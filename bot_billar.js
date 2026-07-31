/* ============================================================
   bot_billar.js — Bot para Billar Local (rework r3)
   ------------------------------------------------------------
   Script clásico SIN Web Worker: funciona también desde file://.
   Todo el contenido vive en una IIFE; la única variable pública
   es `MetaBot`, expuesta sobre globalThis y congelada:

     MetaBot.analyze(state, onProgress, onComplete)
       state:      { mode, currentPlayer, groups, ballInHand,
                     balls:[{id,x,y,pocketed}], difficulty,
                     physics? (constantes reales del juego) }
       onProgress: (pct 0..100) => {}
       onComplete: ({shot, top} | {error, shot:null}) => {}

   El cálculo corre en lotes cooperativos de ~25 ms para no
   bloquear la animación y poder reportar el porcentaje.

   Rework según instrucción (8 secciones):
   §1 física unificada (DT=2.1, constantes inyectables, orden
      idéntico al juego, simulación hasta reposo o 25 s)
   §2 corredores: bolas + mandíbulas + límites, clasificación
   §3 capas L0 validación → L1 geometría → L2 simulación
      nominal → L3 refinamiento → L4 robustez determinista
   §4 presupuesto 15 s con corte cooperativo a 14.7 s
   §5 puntuación por prioridades estrictas + tasas
   §6 bola en mano recalcula todo por colocación
   §7 determinismo en 'hard', contrato de respuesta exacto

   Índice Elo (doc de traspaso billar_indice_elo_traspaso.md):
   v0  shotElo()/potProb() geométricos · D en candidatos directos
       (baseScore sigue conduciendo; D fluye a resultados para
       validar el ordenamiento antes del reemplazo total, §10/§14)
   v1  eje de potencia: pMin forma cerrada + margen + ventana
       [p_lo, p_hi] con piso FIJO de σ_scratch (= σ_exec del bot,
       decisión tomada) · término σ_p en D · recargo +70/banda ·
       carambolas con A_total = Π A_i · powersFor() al centro de
       la ventana (fin de la sobrepotencia 2–10×, §5)
   v2  estorbos y riesgo de blanca: D = máx(boca+potencia+bandas,
       cada estorbo por tramo con su A acumulada, σ_scratch a la
       potencia elegida) · severidad continua 1−erf(σ/(σ_BOT√2))
       reemplaza cuePocketRisk/W.POS_RISK (muere el umbral 70)
   v3  L4 = bisección 2D (§12): 5 finalistas, ventanas [α⁻,α⁺] y
       [p_lo,p_hi] medidas por simulación (fallo = no embocar O
       σ_scratch bajo el piso), dos vueltas 1→2→1, D medido
       sustituye al analítico en finalistas · presupuesto §11
       (30 s / margen 500 ms) + salida temprana (hook D_TARGET
       para el D* por ventaja de v4)
   v3.1 entrada sucia permitida con recargo (decisión §13.2): el
       tramo a tronera puede besar la mandíbula junto a la boca
       (margen ∈ [ELO_DIRTY_MIN, 0), sin estorbo de bolas) — w piso
       + ELO_DIRTY_COST analítico, la bisección mide su D real con
       búsqueda de semilla si el nominal falla
   v4  estimador MAP del jugador por partida (estimateSkill, prior
       N(1500,300²), sin historial) · S_BOT = S_jugador+100 y D* por
       ventaja (fórmula A: S−150 ± diferencia de bolas, §9) · salida
       temprana con |D−D*|<40 · measureShot: bisección del tiro que
       ejecutó el jugador (alimenta el estimador con D medido) ·
       §10: candidatos ordenados por D (baseScore queda de desempate)
   instrumentación §13: (6) corridorClear → holgura mínima + tramo
       vía corridorMeasure · (7) simulateShot expone cueMargin /
       cueMarginAt / cueRun · (8) comboCandidate expone cut1/cut2/dL
       y distTP = solo tramo objetivo→tronera
   ============================================================ */
(function (global) {
"use strict";

/* ========== §1 FÍSICA UNIFICADA ==========
   Valores de respaldo = los actuales de index.html (v18). Si el
   HTML envía state.physics, se reconstruye todo desde ahí. */
const FALLBACK = Object.freeze({
  TABLE_W: 1000, TABLE_H: 500, BALL_R: 12,
  DT: 2.1,                 // igualado al juego (antes 4.2)
  ROLL_FRICTION: 0.99975, CUSHION_REST: 0.8, BALL_REST: 0.9,
  STOP_SPEED: 0.02, MAX_SPEED: 2.5,
  FOLLOW_DECEL: 0.001, FOLLOW_ACCEL: 1, FOLLOW_STOP: 0.05,
  SIDE_DECAY: 0.9997, SIDE_STOP: 0.05,
  CUSH_SPIN_ANGLE: Math.PI / 8,
  CUSH_FA_KEEP: 0.3, CUSH_UA_KEEP: 0.85,
  HIT_FA_KEEP: 0.8, HIT_UA_KEEP: 0.9,
  POCKET_DEPTH_R: 0.91,    // × BALL_R
  CUSHION_R: 2.3333        // × BALL_R
});
const SIM_TIME_CAP_MS = 25000;      // §1: límite amplio de seguridad
const DEADLINE_MS = 30000;          // §11 v3: bisección necesita más presupuesto
const RETURN_MARGIN_MS = 500;

let P = null;        // parámetros físicos activos
let GEO = null;      // límites, troneras y mandíbulas derivados

function configure(physics) {
  P = { ...FALLBACK, ...(physics || {}) };
  const R = P.BALL_R, C = P.BALL_R * P.CUSHION_R;
  const BX0 = C + R, BX1 = P.TABLE_W - C - R;
  const BY0 = C + R, BY1 = P.TABLE_H - C - R;
  const prof = {
    corner: { holeR: R*1.35, rimR: R*2.15, railGap: R*1.3333, jawOut: R*2, captureR: R*2.10 },
    side:   { holeR: R*1.45, rimX: R*2.50, rimY: R*2.15, railGap: R*2.50, jawOut: R*2, captureR: R*2.20 }
  };
  const mk = (id, type, x, y, jaws) => ({ id, type, x, y, jaws,
    holeR: prof[type].holeR, captureR: prof[type].captureR, railGap: prof[type].railGap });
  const pockets = [
    mk("tl","corner", BX0-R, BY0-R, [{x:BX0-prof.corner.jawOut,y:BY0+prof.corner.railGap},{x:BX0+prof.corner.railGap,y:BY0-prof.corner.jawOut}]),
    mk("tc","side", P.TABLE_W/2, BY0-(R+4), [{x:P.TABLE_W/2-prof.side.railGap,y:BY0-prof.side.jawOut},{x:P.TABLE_W/2+prof.side.railGap,y:BY0-prof.side.jawOut}]),
    mk("tr","corner", BX1+R, BY0-R, [{x:BX1+prof.corner.jawOut,y:BY0+prof.corner.railGap},{x:BX1-prof.corner.railGap,y:BY0-prof.corner.jawOut}]),
    mk("bl","corner", BX0-R, BY1+R, [{x:BX0-prof.corner.jawOut,y:BY1-prof.corner.railGap},{x:BX0+prof.corner.railGap,y:BY1+prof.corner.jawOut}]),
    mk("bc","side", P.TABLE_W/2, BY1+(R+4), [{x:P.TABLE_W/2-prof.side.railGap,y:BY1+prof.side.jawOut},{x:P.TABLE_W/2+prof.side.railGap,y:BY1+prof.side.jawOut}]),
    mk("br","corner", BX1+R, BY1+R, [{x:BX1+prof.corner.jawOut,y:BY1-prof.corner.railGap},{x:BX1-prof.corner.railGap,y:BY1+prof.corner.jawOut}])
  ];
  const jaws = [];
  for (const pk of pockets) for (const j of pk.jaws)
    jaws.push({ id: -1, x: j.x, y: j.y, r: R, isJaw: true, pocketed: false });
  GEO = { BX0, BX1, BY0, BY1, pockets, jaws, prof };
}
configure(null);   // arranque con valores de respaldo

class Ball {
  constructor(id, x, y, isJaw = false, pocketed = false) {
    this.id = id; this.x = x; this.y = y;
    this.dir = 0; this.speed = 0; this.fa = 0; this.ua = 0; this.Nm = 0;
    this.pocketed = !!pocketed; this.isJaw = isJaw; this.r = P.BALL_R;
  }
  get vx() { return Math.cos(this.dir) * this.speed; }
  get vy() { return -Math.sin(this.dir) * this.speed; }
  setVel(vx, vy) { this.dir = Math.atan2(-vy, vx); this.speed = Math.hypot(vx, vy); }
  get moving() { return this.speed !== 0 || this.fa !== 0 || this.ua !== 0; }
}

/* --- Simulación: MISMO orden que el juego (stepPhysics):
   1) integrate por bola: fa → mover → banda → tronera → fricción
      → condición de reposo → decaimiento lateral
   2) dos pasadas de colisiones par a par (bolas + mandíbulas) --- */
function simIntegrate(ball, dt, st, phys) {
  if (ball.pocketed || ball.isJaw) return;
  if (ball.speed === 0 && ball.fa === 0) {
    if (ball.ua !== 0) decaySide(ball, dt, phys);
    return;
  }
  if (ball.fa !== 0) {
    let d = phys.FOLLOW_DECEL * dt;
    if (d > Math.abs(ball.fa)) d = Math.abs(ball.fa);
    if (ball.fa < 0) d = -d;
    ball.fa -= d;
    if (Math.abs(ball.fa) < phys.FOLLOW_STOP) ball.fa = 0;
    const e = phys.FOLLOW_ACCEL * d;
    ball.setVel(ball.vx + Math.cos(ball.Nm) * e, ball.vy - Math.sin(ball.Nm) * e);
  }
  ball.x += ball.vx * dt;
  ball.y += ball.vy * dt;
  simCushion(ball, st, phys);
  simCapture(ball, st, phys);
  ball.speed *= Math.pow(phys.ROLL_FRICTION, dt);
  if (ball.fa === 0 && Math.abs(ball.speed) < phys.STOP_SPEED) ball.speed = 0;
  decaySide(ball, dt, phys);
}

function decaySide(ball, dt, phys) {
  if (ball.ua === 0) return;
  ball.ua *= Math.pow(phys.SIDE_DECAY, dt);
  if (Math.abs(ball.ua) < phys.SIDE_STOP) ball.ua = 0;
}

function simCushion(ball, st, phys) {
  const { BX0, BX1, BY0, BY1, prof } = GEO;
  const cg = prof.corner.railGap, sg = prof.side.railGap;
  const inSideGapTop = Math.abs(ball.x - P.TABLE_W / 2) < sg;
  const inLo = ball.x < BX0 + cg, inHi = ball.x > BX1 - cg;
  let hit = false;
  if (ball.x < BX0 && ball.y > BY0 + cg && ball.y < BY1 - cg) {
    ball.x = BX0; ball.dir = Math.PI - ball.dir + ball.ua * phys.CUSH_SPIN_ANGLE; hit = true;
  } else if (ball.x > BX1 && ball.y > BY0 + cg && ball.y < BY1 - cg) {
    ball.x = BX1; ball.dir = Math.PI - ball.dir + ball.ua * phys.CUSH_SPIN_ANGLE; hit = true;
  }
  if (ball.y < BY0 && !inSideGapTop && !inLo && !inHi) {
    ball.y = BY0; ball.dir = -ball.dir + ball.ua * phys.CUSH_SPIN_ANGLE; hit = true;
  } else if (ball.y > BY1 && !inSideGapTop && !inLo && !inHi) {
    ball.y = BY1; ball.dir = -ball.dir + ball.ua * phys.CUSH_SPIN_ANGLE; hit = true;
  }
  if (hit) {
    ball.speed *= phys.CUSHION_REST;
    ball.ua *= phys.CUSH_UA_KEEP;
    ball.fa *= phys.CUSH_FA_KEEP;
    /* T1 (punto 2 backlog): golpes de banda previos al primer contacto
       bola-bola. En la práctica solo la blanca se mueve en esa ventana,
       así que equivale a "bandas de la blanca antes del contacto".
       railAfter NO se toca: su semántica alimenta la lógica de faltas. */
    if (st) {
      if (st.contacted) st.railAfter = true;
      else st.railBefore = (st.railBefore || 0) + 1;
    }
  }
}

function simCapture(ball, st, phys) {
  const { BX0, BX1, BY0, BY1, pockets } = GEO;
  let depth = 0;
  if (ball.x < BX0) depth += BX0 - ball.x;
  if (ball.y < BY0) depth += BY0 - ball.y;
  if (ball.x > BX1) depth += ball.x - BX1;
  if (ball.y > BY1) depth += ball.y - BY1;
  if (depth < P.BALL_R * P.POCKET_DEPTH_R) return false;
  let cap = null, bestD = Infinity;
  for (const pk of pockets) {
    const d = Math.hypot(ball.x - pk.x, ball.y - pk.y);
    if (d <= pk.captureR && d < bestD) { cap = pk; bestD = d; }
  }
  if (!cap) return false;
  ball.pocketed = true; ball.speed = 0; ball.fa = 0; ball.ua = 0;
  if (st) {
    if (ball.id === 0) st.scratch = true;
    else st.pocketed.push(ball.id);
  }
  return true;
}

function simCollide(a, b, st, phys) {
  if (a.pocketed || b.pocketed) return false;
  if (a.isJaw && b.isJaw) return false;
  if (a.speed === 0 && b.speed === 0 && a.fa === 0 && b.fa === 0) return false;
  const dx = b.x - a.x, dy = b.y - a.y;
  const dist2 = dx * dx + dy * dy;
  const minDist = a.r + b.r;
  if (dist2 > minDist * minDist || dist2 === 0) return false;
  const dist = Math.sqrt(dist2);
  const nx = dx / dist, ny = dy / dist;
  const overlap = minDist - dist;
  if (a.isJaw)      { b.x += nx * overlap; b.y += ny * overlap; }
  else if (b.isJaw) { a.x -= nx * overlap; a.y -= ny * overlap; }
  else {
    a.x -= nx * overlap / 2; a.y -= ny * overlap / 2;
    b.x += nx * overlap / 2; b.y += ny * overlap / 2;
  }
  if (st && !st.contacted) {
    if (a.id === 0 && b.id > 0) { st.contacted = true; st.firstHit = b.id; }
    else if (b.id === 0 && a.id > 0) { st.contacted = true; st.firstHit = a.id; }
  }
  let avx = a.vx, avy = a.vy, bvx = b.vx, bvy = b.vy;
  const e = (bvx * nx + bvy * ny) - (avx * nx + avy * ny);
  if (a.isJaw || b.isJaw) {
    const ball = a.isJaw ? b : a;
    const vn = ball.vx * nx + ball.vy * ny;
    const approaching = a.isJaw ? vn < 0 : vn > 0;
    if (!approaching) return false;
    ball.setVel(ball.vx - 2 * vn * nx, ball.vy - 2 * vn * ny);
    ball.speed *= phys.CUSHION_REST;
    if (st) {
      if (st.contacted) st.railAfter = true;
      else st.railBefore = (st.railBefore || 0) + 1;
    }
    return true;
  }
  if (e > 0) return false;
  avx += nx * e; avy += ny * e;
  bvx -= nx * e; bvy -= ny * e;
  a.setVel(avx, avy); b.setVel(bvx, bvy);
  a.speed *= phys.BALL_REST; b.speed *= phys.BALL_REST;
  a.fa *= phys.HIT_FA_KEEP; a.ua *= phys.HIT_UA_KEEP;
  b.fa *= phys.HIT_FA_KEEP; b.ua *= phys.HIT_UA_KEEP;
  return true;
}

function simStep(balls, dt, st, phys) {
  for (const b of balls) simIntegrate(b, dt, st, phys);
  const all = balls.concat(GEO.jaws);
  for (let pass = 0; pass < 2; pass++)
    for (let i = 0; i < all.length; i++)
      for (let j = i + 1; j < all.length; j++)
        simCollide(all[i], all[j], st, phys);
}

/* Simulación completa de un tiro. Devuelve estado final y registro.
   §1: corre hasta el reposo o SIM_TIME_CAP_MS, nunca corta a 6 s. */
function simulateShot(srcBalls, params, phys = P) {
  const balls = srcBalls.map(b => {
    const nb = new Ball(b.id, b.x, b.y, !!b.isJaw, !!b.pocketed);
    return nb;
  });
  let cue = balls.find(b => b.id === 0);
  if (params.cuePos) {
    cue.x = params.cuePos.x; cue.y = params.cuePos.y; cue.pocketed = false;
  }
  cue.dir = -params.angle; cue.Nm = -params.angle;
  cue.speed = params.power * phys.MAX_SPEED;
  cue.fa = params.power * (params.follow || 0);
  cue.ua = params.power * (params.english || 0);
  /* §13.7: cueMargin/cueMarginAt/cueRun alimentan σ_scratch (§7) en v2.
     cueMargin = holgura mínima de la blanca a toda tronera (menos
     captureR) sobre TODA su trayectoria posterior al primer contacto;
     cueMarginAt = recorrido de la blanca hasta ese punto. */
  const st = { contacted: false, firstHit: null, railAfter: false,
               railBefore: 0,      // T1: bandas de la blanca antes del contacto
               pocketed: [], scratch: false,
               cueMargin: Infinity, cueMarginAt: 0, cueRun: 0 };
  const maxSteps = Math.ceil(SIM_TIME_CAP_MS / phys.DT);
  let steps = 0;
  while (steps < maxSteps) {
    let any = false;
    for (const b of balls) if (!b.isJaw && !b.pocketed && b.moving) { any = true; break; }
    if (!any) break;
    simStep(balls, phys.DT, st, phys);
    steps++;
    if (st.contacted && !cue.pocketed) {
      for (const pk of GEO.pockets) {
        const m = Math.hypot(cue.x - pk.x, cue.y - pk.y) - pk.captureR;
        if (m < st.cueMargin) { st.cueMargin = m; st.cueMarginAt = st.cueRun; }
      }
      st.cueRun += cue.speed * phys.DT;
    }
  }
  const stillMoving = balls.filter(b => !b.isJaw && !b.pocketed && b.moving).length;
  return { balls, shotState: st, cueFinal: { x: cue.x, y: cue.y },
           simMs: steps * phys.DT, stillMoving, truncated: steps >= maxSteps };
}

/* ========== §2 GEOMETRÍA DE CORREDORES ========== */
const SAFETY_MARGIN = 0.6;

function segPointDist(ax, ay, bx, by, px, py) {
  const dx = bx - ax, dy = by - ay;
  const len2 = dx * dx + dy * dy;
  let t = len2 > 0 ? ((px - ax) * dx + (py - ay) * dy) / len2 : 0;
  t = Math.max(0, Math.min(1, t));
  return Math.hypot(px - (ax + t * dx), py - (ay + t * dy));
}

/* Distancia punto-segmento con parámetro de proyección (para localizar
   el tramo de mínima holgura, §13.6) */
function segPointDistT(ax, ay, bx, by, px, py) {
  const dx = bx - ax, dy = by - ay;
  const len2 = dx * dx + dy * dy;
  let t = len2 > 0 ? ((px - ax) * dx + (py - ay) * dy) / len2 : 0;
  t = Math.max(0, Math.min(1, t));
  return { d: Math.hypot(px - (ax + t * dx), py - (ay + t * dy)), t };
}

/* ¿El punto está en zona jugable o dentro de la boca de una tronera?
   EPS absorbe el polvo flotante de puntos exactamente sobre la banda
   (p. ej. el punto de rebote de un tiro con banda previa) */
const BOUND_EPS = 0.75;
function pointInPlayOrMouth(x, y) {
  const { BX0, BX1, BY0, BY1, pockets } = GEO;
  if (x >= BX0 - BOUND_EPS && x <= BX1 + BOUND_EPS &&
      y >= BY0 - BOUND_EPS && y <= BY1 + BOUND_EPS) return true;
  for (const pk of pockets)
    if (Math.hypot(x - pk.x, y - pk.y) <= pk.captureR) return true;
  return false;
}

/* §13.6: el corredor ahora MIDE. Devuelve:
     ok          — misma condición de siempre (booleano legacy)
     margin      — holgura mínima sobre TODO el tramo (bolas + mandíbulas
                   + límites); alimenta σ de trayectoria de blanca (v2+)
     marginAt    — distancia desde (x1,y1) donde ocurre esa holgura
     ballMargin  — holgura mínima SOLO respecto de bolas (v2: estorbos).
                   La geometría de mandíbulas se excluye a propósito: ya
                   está en σ_tol vía w(β); incluirla doble-contaría la boca.
     ballMarginAt — tramo donde ocurre ballMargin
   Estorbos: toElo(ballMargin / (ballMarginAt · A_acumulada)) (§3). */
function corridorMeasure(x1, y1, x2, y2, balls, ignoreIds) {
  const R = P.BALL_R;
  const len = Math.hypot(x2 - x1, y2 - y1);
  let ok = true, margin = Infinity, marginAt = 0;
  let bMargin = Infinity, bMarginAt = 0;
  const track = (slack, at) => {
    if (slack < 0) ok = false;
    if (slack < margin) { margin = slack; marginAt = at; }
  };

  /* Bolas activas que invaden el corredor (excluidas las participantes) */
  const clearance = 2 * R + SAFETY_MARGIN;
  for (const b of balls) {
    if (b.pocketed || b.isJaw || ignoreIds.has(b.id)) continue;
    const { d, t } = segPointDistT(x1, y1, x2, y2, b.x, b.y);
    const slack = d - clearance, at = t * len;
    track(slack, at);
    if (slack < bMargin) { bMargin = slack; bMarginAt = at; }
  }

  /* §2: el recorrido no puede atravesar mandíbulas ni salir del paño
     salvo por la boca de una tronera. Muestreo denso del segmento. */
  const steps = Math.max(2, Math.ceil(len / (R * 0.5)));
  for (let i = 0; i <= steps; i++) {
    const x = x1 + (x2 - x1) * i / steps;
    const y = y1 + (y2 - y1) * i / steps;
    const at = len * i / steps;
    if (!pointInPlayOrMouth(x, y)) track(-BOUND_EPS, at);
    for (const j of GEO.jaws) {
      /* contacto real: centro a < 2r de la mandíbula (margen −0.8) */
      track(Math.hypot(x - j.x, y - j.y) - (2 * R - 0.8), at);
    }
  }
  return { ok, margin, marginAt, ballMargin: bMargin, ballMarginAt: bMarginAt };
}

/* Interfaz legacy intacta: todos los llamadores siguen recibiendo
   el mismo booleano de siempre. */
function corridorClear(x1, y1, x2, y2, balls, ignoreIds) {
  return corridorMeasure(x1, y1, x2, y2, balls, ignoreIds).ok;
}

/* ========== Entrada sucia (decisión: permitida con recargo) ==========
   El tramo objetivo→tronera puede rozar la mandíbula cerca de la boca:
   la línea pasa a < 2R−0.8 de la punta pero la bola besa y cae
   (captureR es generoso). Se acepta si:
     · no hay estorbo de bolas (ballMargin > 0)
     · el beso es superficial: margen ≥ ELO_DIRTY_MIN
     · ocurre junto a la boca (≤ ELO_DIRTY_NEAR del final del tramo)
   Analíticamente se evalúa con un w piso + recargo ELO_DIRTY_COST;
   la bisección v3 mide su dificultad real si llega a finalista. */
const ELO_DIRTY_MIN = -8;        // beso máximo permitido (uds)
const ELO_DIRTY_NEAR = 45;       // distancia a la boca para ser "entrada"
const ELO_DIRTY_COST = 200;      // recargo Elo analítico (bench v5: +171…+233)
const W_DIRTY_FLOOR = 0.5;       // w efectivo para entradas sucias

function pocketLegState(x1, y1, pocket, balls, ignoreIds) {
  const leg = corridorMeasure(x1, y1, pocket.x, pocket.y, balls, ignoreIds);
  if (leg.ok) return { ok: true, dirty: false, leg };
  const len = Math.hypot(pocket.x - x1, pocket.y - y1);
  const dirty = leg.ballMargin > 0 &&
                leg.margin >= ELO_DIRTY_MIN &&
                (len - leg.marginAt) <= ELO_DIRTY_NEAR;
  return { ok: dirty, dirty, leg };
}

function normalizeAngle(a) {
  while (a > Math.PI) a -= Math.PI * 2;
  while (a <= -Math.PI) a += Math.PI * 2;
  return a;
}

/* ========== REGLAS (§3 capa 0) ========== */
const groupOf = id => (id >= 1 && id <= 7) ? "solids" : (id >= 9 ? "stripes" : null);

function getLowest(balls) {
  let min = 99;
  for (const b of balls)
    if (!b.pocketed && !b.isJaw && b.id >= 1 && b.id <= 9 && b.id < min) min = b.id;
  return min === 99 ? null : min;
}

function legalTargets(mode, groups, player, balls) {
  const alive = id => balls.find(b => b.id === id && !b.pocketed);
  if (mode === "9ball") {
    const low = getLowest(balls);
    const b = low !== null ? alive(low) : null;
    return b ? [b] : [];
  }
  const g = groups ? groups[player] : null;
  if (!g) return balls.filter(b => !b.pocketed && !b.isJaw && b.id >= 1 && b.id !== 8);
  const own = balls.filter(b => !b.pocketed && groupOf(b.id) === g);
  if (own.length > 0) return own;
  const eight = alive(8);
  return eight ? [eight] : [];
}

/* ¿firstHit sería legal para este jugador? */
function firstHitLegal(firstHit, mode, groups, player, ballsBefore) {
  if (firstHit === null) return false;
  if (mode === "9ball") return firstHit === getLowest(ballsBefore);
  const g = groups ? groups[player] : null;
  if (!g) return firstHit !== 8;
  const rem = ballsBefore.filter(b => !b.pocketed && groupOf(b.id) === g).length;
  return rem === 0 ? firstHit === 8 : groupOf(firstHit) === g;
}

/* ========== §3 CAPA 1: CANDIDATOS GEOMÉTRICOS ==========
   Clasificación §2: "directa" | "combinacion" | "banda" |
   "defensa" | "invalido" (los inválidos no se generan). */
function ghostPoint(ball, pocket) {
  const dx = pocket.x - ball.x, dy = pocket.y - ball.y;
  const d = Math.hypot(dx, dy);
  if (d < P.BALL_R * 2) return null;
  return { x: ball.x - (dx / d) * 2 * P.BALL_R,
           y: ball.y - (dy / d) * 2 * P.BALL_R,
           distPocket: d, ux: dx / d, uy: dy / d };
}

function baseScore(cut, distCT, distTP, pocket) {
  let s = 100;
  s -= (cut / (Math.PI / 2)) * 35;
  s -= (distCT / P.TABLE_W) * 25;
  s -= (distTP / P.TABLE_W) * 15;
  if (pocket.type === "side") s += 4;
  return s;
}

/* ========== ÍNDICE ELO v0 — geométrica pura (traspaso §3/§14) ==========
   D = dificultad del tiro en escala Elo. Anclaje: 1500 = esquina
   recta con distCT=250 y d_jaw=250 (σ_ref ≈ 1.50 mrad). K = 690
   puntos por década de precisión exigida.
   v0 NO reemplaza baseScore: solo lo acompaña para validación.
   Limitación conocida (§14): sin eje de potencia, no ve el caso
   "blanca comprometida" (+431 a +537). Bandas y carambolas quedan
   sin D hasta v1 (recargo +70/banda y A_total = Π A_i). */
const ELO_K       = 690;
const ELO_TWOR    = 24;                          // 2·BALL_R (verificado §1)
const ELO_A_HALF  = { corner: 28.284, side: 30.0 };  // semiseparación mandíbulas
const ELO_JAW     = { corner: -11.31, side: 8.0 };   // offset línea de mandíbulas
const ELO_SIG_REF = 4.2843 / (250 * (1 + 250 / ELO_TWOR));  // 1.5011e-3 rad
const ELO_AXIS    = {   // eje de cada tronera (§2)
  tl: [-0.7071, -0.7071], tr: [0.7071, -0.7071],
  bl: [-0.7071,  0.7071], br: [0.7071,  0.7071],
  tc: [0, -1],            bc: [0,  1]
};
const ELO_CUT_CLAMP = 1.30;                      // θ máximo modelable (rad)

/* Ancho de paso limpio exacto: w(β) = a − 2R/cosβ (§2, NO w₀·cosβ).
   β > β_max ⇒ w ≤ 0 ⇒ no hay entrada limpia: D = Infinity.
   (Decisión §13.2 pendiente: hoy el candidato sobrevive con D=Infinity;
   la bisección v3 medirá el régimen rattle-in.) */
function pocketPassWidth(pocket, target) {
  const dx = pocket.x - target.x, dy = pocket.y - target.y;
  const L = Math.hypot(dx, dy);
  if (L < 1) return { beta: 0, w: -1 };
  const ax = ELO_AXIS[pocket.id] || [0, 0];
  const cosB = Math.abs((dx / L) * ax[0] + (dy / L) * ax[1]);
  const beta = Math.acos(Math.min(1, cosB));
  const w = ELO_A_HALF[pocket.type] - ELO_TWOR / Math.cos(beta);
  return { beta, w };
}

/* ========== ÍNDICE ELO v1 — eje de potencia (§5) ========== */
/* Punto 3 (D2): referencia derivada, no tanteada.
   σ_p = 0.03 es el error absoluto de potencia de §5 (mapeo lineal de
   260 px de arrastre, precisión de puntero constante en px); 0.6745 es
   el semiancho al que P(éxito) = 0.5 en un eje gaussiano — el mismo
   factor del puente Elo↔ejecución de §6. Así ambos ejes son
   conmensurables en su punto de referencia (ambos = P 0.5). La
   referencia anterior, 0.12, equivalía a P ≈ 0.9997 y por eso casi
   todo el eje restaba. */
const ELO_SIG_P_REF = 0.6745 * 0.03;   // = 0.02024
const ELO_BAND_COST = 70;          // recargo por banda (placeholder, §13.14)
const S_BOT = 1500;                // arranque en frío (v4: ctx.S_BOT si hay estimador)
const sigmaExec = S => ELO_SIG_REF * Math.pow(10, (1618 - S) / ELO_K);
const SIG_BOT = sigmaExec(S_BOT);  // ≈ 2.23 mrad a S=1500
/* Piso FIJO de σ_scratch (decisión): el bot no acepta trayectorias
   de blanca más finas que su propia precisión de ejecución.
   v4: ahora dinámico vía sigmaExec(ctx.S_BOT) en la bisección. */

const lamFriction = () => -Math.log(P.ROLL_FRICTION);   // λ ≈ 2.5003e-4

/* Potencia mínima en forma cerrada (§5): cadena hacia atrás desde la
   tronera. La fricción es lineal en la distancia: ds/dv = 1/λ. */
function pMin({ distCT, distTP, cut = 0, bands = 0, stages = [] }) {
  const LAM = lamFriction(), VSTOP = P.STOP_SPEED, VMAX = P.MAX_SPEED;
  const VDROP = VSTOP + LAM * 11;
  let v = LAM * distTP + VDROP;
  for (let i = stages.length - 1; i >= 0; i--)
    v = v / (P.BALL_REST * Math.cos(Math.min(stages[i].cut, ELO_CUT_CLAMP)))
        + LAM * stages[i].dist;
  v = v / (P.BALL_REST * Math.cos(Math.min(cut, ELO_CUT_CLAMP)));
  const seg = distCT / (bands + 1);
  for (let b = 0; b < bands; b++) v = v / P.CUSHION_REST + LAM * seg;
  return (v + LAM * seg) / VMAX;
}

/* Margen por sensibilidad del coseno al error de corte (§5, derivado):
   ×1.00 en rectos, crece con el corte. */
function powerMargin(cut, A) {
  return 1 / Math.max(0.35, 1 - Math.tan(cut) * 3 * (A - 1) * SIG_BOT);
}

/* Piso por regla de banda (§5): si el tiro falla, la objeto debe poder
   llegar a una banda (contacted && !pocketed && !railAfter ⇒ falta).
   v1: distancia mínima de la objetivo a cualquier banda. */
function railFloor(cand, target, cut, bands) {
  const LAM = lamFriction();
  const { BX0, BX1, BY0, BY1 } = GEO;
  const dRail = Math.max(0, Math.min(target.x - BX0, BX1 - target.x,
                                     target.y - BY0, BY1 - target.y));
  let v = (LAM * dRail + P.STOP_SPEED) /
          (P.BALL_REST * Math.cos(Math.min(cut, ELO_CUT_CLAMP)));
  const seg = cand.distCT / (bands + 1);
  for (let b = 0; b < bands; b++) v = v / P.CUSHION_REST + LAM * seg;
  return (v + LAM * seg) / P.MAX_SPEED;
}

/* Seguido nominal del bot (máximo de effectsFor en hard). La blanca
   retenida tras el choque acelera ≈ fa·FOLLOW_ACCEL a lo largo de su
   dirección original; por eso incluso un tiro recto tiene p_hi < 1:
   la blanca corre detrás de la objeto hacia la tronera (§5). */
const NOMINAL_FOLLOW = 0.25;

/* σ_scratch analítico de primer orden (v1). Tras el contacto la blanca
   conserva la componente tangencial (collide() transfiere solo la
   normal) MÁS el empuje del seguido; la resultante recorre
   (v − VSTOP)/λ en línea recta. Las bandas posteriores se ignoran
   (la bisección v3 medirá el valor real). Devuelve Infinity si la
   blanca no llega a moverse. */
function cueScratchSigma(cand, power, A) {
  const LAM = lamFriction(), VMAX = P.MAX_SPEED, VSTOP = P.STOP_SPEED;
  const gx = cand.ghostX, gy = cand.ghostY;
  const v0 = power * VMAX;
  let ux, uy, vImp;
  if (cand.type === "banda" && cand.railX != null) {
    const dx = gx - cand.railX, dy = gy - cand.railY;
    const L = Math.hypot(dx, dy) || 1;
    ux = dx / L; uy = dy / L;
    const seg = cand.distCT / 2;
    vImp = Math.max(0, (v0 - LAM * seg) * P.CUSHION_REST - LAM * seg);
  } else {
    ux = Math.cos(cand.angle); uy = Math.sin(cand.angle);
    vImp = Math.max(0, v0 - LAM * cand.distCT);
  }
  /* dirección de salida de la objeto: fantasma → bola (línea de centros) */
  const ox = (cand.target.x - gx) / ELO_TWOR;
  const oy = (cand.target.y - gy) / ELO_TWOR;
  const cosC = ux * ox + uy * oy;
  const sin2 = Math.max(0, 1 - cosC * cosC);
  const vTan = vImp * Math.sqrt(sin2);
  const fa = power * NOMINAL_FOLLOW;
  let tx = ux - cosC * ox, ty = uy - cosC * oy;
  const Lt = Math.hypot(tx, ty);
  if (Lt > 1e-9) { tx /= Lt; ty /= Lt; } else { tx = 0; ty = 0; }
  /* resultante: tangencial + seguido (primer orden, sin fricción en
     la aceleración: compensa el HIT_FA_KEEP=0.8 que no modelamos) */
  const vx = fa * ux + vTan * tx, vy = fa * uy + vTan * ty;
  const v = Math.hypot(vx, vy);
  const travel = (v - VSTOP) / LAM;
  if (travel <= 0) return Infinity;
  const dx = vx / v, dy = vy / v;
  let margin = Infinity;
  for (const pk of GEO.pockets) {
    const rx = pk.x - gx, ry = pk.y - gy;
    let s = rx * dx + ry * dy;
    s = Math.max(0, Math.min(travel, s));
    const d = Math.hypot(rx - s * dx, ry - s * dy) - pk.captureR;
    if (d < margin) margin = d;
  }
  return margin / (travel * A);
}

/* Ventana de potencia [p_lo, p_hi] (§5):
     p_lo = max(pMin·margin, p_rail)
     p_hi = min(1, p_scratch)   ← el techo lo pone el control de la
     blanca, no el embocar; p_scratch es donde σ_scratch toca el piso.
   La potencia elegida es el CENTRO de la ventana (máxima robustez). */
function powerWindow(cand, target, pocket, A, opts) {
  const lo0 = pMin({ distCT: cand.distCT, distTP: cand.distTP,
                     cut: opts.cut, bands: opts.bands, stages: opts.stages });
  const lo = Math.max(lo0 * powerMargin(opts.cut, A), opts.pRail || 0, 0.02);
  let hi = lo;                     // si ni p_lo cumple el piso, degenerada
  for (let i = 0; i <= 24; i++) {
    const p = lo + (1 - lo) * i / 24;
    if (cueScratchSigma(cand, p, A) >= sigmaExec(S_BOT)) hi = p;
  }
  hi = Math.min(1, Math.max(lo, hi));
  /* Punto 3 (D3): la potencia elegida es la MÍNIMA viable más dos sigmas
     (SP2 = 2·σ_p, margen absoluto porque el error de potencia es
     absoluto). Tirar tan suave como sea seguro: suave emboca más
     (captura por subpaso) y la blanca recorre menos (posición más
     predecible). Ventana más angosta que 2σ_p → centro (lo mejor
     disponible; esa estrechez ya se paga en el índice por D1/D2). */
  const SP2 = 0.06;
  const chosen = (hi - lo >= SP2) ? lo + SP2 : (lo + hi) / 2;
  return { lo, hi, center: (lo + hi) / 2, chosen,
           sigPTol: Math.max(0.005, (hi - lo) / 2) };
}

function shotElo(cand, target, pocket) {
  const { beta, w } = pocketPassWidth(pocket, target);
  /* Entrada sucia (decisión: permitida con recargo): w ≤ 0 ya no mata
     el candidato; se evalúa con w piso + ELO_DIRTY_COST, y la
     bisección v3 mide su dificultad real si llega a finalista. */
  const dirty = cand.dirty === true || w <= 0;
  const wEff = Math.max(w, W_DIRTY_FLOOR);
  const type = cand.type === "bolaEnMano" ? "directa" : cand.type;
  const bands = type === "banda" ? 1 : 0;
  let A, A1 = 1, cut, stages = [];
  if (type === "combinacion") {
    /* §4: cada contacto repite la estructura → A_total = Π A_i.
       La variable dominante es dL (separación entre bolas). */
    const cut1 = Math.min(cand.cut1 || 0, ELO_CUT_CLAMP);
    const cut2 = Math.min(cand.cut2 || 0, ELO_CUT_CLAMP);
    A1 = 1 + cand.distCT / (ELO_TWOR * Math.cos(cut1));
    A = A1 * (1 + (cand.dL || 0) / (ELO_TWOR * Math.cos(cut2)));
    cut = cand.cut1 || 0;
    stages = [{ cut: cand.cut2 || 0, dist: cand.dL || 0 }];
  } else {
    cut = Math.min(cand.cutAngle || 0, ELO_CUT_CLAMP);
    A = 1 + cand.distCT / (ELO_TWOR * Math.cos(cut));
    A1 = A;
  }
  cand.A = A;
  const dJaw = Math.max(20, cand.distTP + ELO_JAW[pocket.type]);
  const sigTol = wEff / (dJaw * A);
  const win = powerWindow(cand, target, pocket, A, {
    cut, bands, stages,
    pRail: railFloor(cand, target, cut, bands)
  });
  cand.pWin = win;
  const toElo = sig => 1500 + ELO_K * Math.log10(ELO_SIG_REF / sig);
  /* Punto 3 (D1): el término de potencia es UNILATERAL — una ventana
     más ancha de lo necesario no hace el tiro más fácil, solo no lo
     hace más difícil. Con D2 queda casi siempre inactivo y solo habla
     cuando la potencia es el cuello de botella (ancho ≲ 0.04). */
  const powCost = Math.max(0, ELO_K * Math.log10(ELO_SIG_P_REF / win.sigPTol));
  /* Restricción base: boca + potencia + recargos de bandas y suciedad */
  let D = 1500 + ELO_K * Math.log10(ELO_SIG_REF / sigTol) + powCost
        + bands * ELO_BAND_COST
        + (dirty ? ELO_DIRTY_COST : 0);
  /* v2 §3: D final = MÁXIMO sobre todas las restricciones, porque
     manda el cuello de botella. Estorbos: holgura de bolas por tramo,
     con la A acumulada hasta ese punto (banda preserva el ángulo por
     el argumento del espejo → A=1 en los tramos previos al contacto). */
  if (cand.legs) {
    const Alegs = type === "combinacion" ? [1, A1, A]
                : type === "banda"       ? [1, 1, A]
                :                          [1, A];
    for (let i = 0; i < cand.legs.length && i < Alegs.length; i++) {
      const lg = cand.legs[i];
      if (!isFinite(lg.margin)) continue;          // corredor libre de bolas
      const sig = lg.margin / (Math.max(lg.marginAt, 1) * Alegs[i]);
      if (sig > 0) D = Math.max(D, toElo(sig));
    }
  }
  /* v2 §7 + punto 3 (D4): riesgo de blanca como exigencia de precisión,
     evaluado a la potencia que se va a JUGAR (chosen), no al centro de
     la ventana — evaluarlo en el centro mide un tiro distinto. */
  const sigS = cueScratchSigma(cand, win.chosen, A);
  if (isFinite(sigS) && sigS > 0) D = Math.max(D, toElo(sigS));
  return D;
}

/* Probabilidad de embocar un tiro de dificultad D para un jugador
   de nivel S (puente Elo ↔ ejecución, §6). */
function potProb(D, S) {
  if (!isFinite(D)) return 0;
  return 1 / (1 + Math.pow(10, (D - S) / 400));
}

/* §6 forma gaussiana con ruido aditivo de puntería (punto 1 backlog):
   q es la cuantización del aim (uniforme en un paso → sd q/√12).
   Con q = 0 reproduce potProb exactamente (D = S ⇒ P = 0.500);
   con q > 0 la probabilidad satura por debajo de 1 aunque S → ∞,
   que es la forma honesta de modelar el suelo del puntero.
   El BOT usa q = 0 (elige su ángulo con precisión de double);
   q > 0 solo aplica al estimador del jugador. */
const sigTolOf = D => 0.6745 * ELO_SIG_REF * Math.pow(10, (1618 - D) / ELO_K);
function potProbQ(D, S, q = 0) {
  if (!isFinite(D)) return 0;
  const se = Math.hypot(sigmaExec(S), q / Math.sqrt(12));
  return erf(sigTolOf(D) / (se * Math.SQRT2));
}

/* erf (Abramowitz–Stegun 7.1.26, |ε| ≤ 1.5e-7): la severidad del
   riesgo de blanca es 1 − erf(σ_scratch/(σ_BOT·√2)) (§7). */
function erf(x) {
  const s = x < 0 ? -1 : 1, ax = Math.abs(x);
  const t = 1 / (1 + 0.3275911 * ax);
  const y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t
              - 0.284496736) * t + 0.254829592) * t * Math.exp(-ax * ax);
  return s * y;
}

function directCandidate(cx, cy, target, pocket, balls, type = "directa", cuePos = null) {
  const g = ghostPoint(target, pocket);
  if (!g) return null;
  const { BX0, BX1, BY0, BY1 } = GEO;
  const m = P.BALL_R * 1.5;
  if (g.x < BX0 - m || g.x > BX1 + m || g.y < BY0 - m || g.y > BY1 + m) return null;
  const distCT = Math.hypot(g.x - cx, g.y - cy);
  if (distCT < 1) return null;
  const cosCut = ((g.x - cx) * g.ux + (g.y - cy) * g.uy) / distCT;
  if (cosCut < 0.087) return null;                     // corte > ~85°
  const cut = Math.acos(Math.max(-1, Math.min(1, cosCut)));
  const ignore = new Set([0, target.id]);
  const leg1 = corridorMeasure(cx, cy, g.x, g.y, balls, ignore);
  if (!leg1.ok) return null;
  const pl2 = pocketLegState(target.x, target.y, pocket, balls, new Set([target.id]));
  if (!pl2.ok) return null;
  const leg2 = pl2.leg;
  const cand = { type, targetId: target.id, pocketId: pocket.id,
           ghostX: g.x, ghostY: g.y,
           angle: Math.atan2(g.y - cy, g.x - cx),
           cutAngle: cut, distCT, distTP: g.distPocket,
           baseScore: baseScore(cut, distCT, g.distPocket, pocket),
           dirty: pl2.dirty,                        // entrada sucia (recargo)
           /* v2: holguras de estorbos por tramo (solo bolas) */
           legs: [ { margin: leg1.ballMargin, marginAt: leg1.ballMarginAt },
                   { margin: leg2.ballMargin, marginAt: leg2.ballMarginAt } ],
           cuePos, pocket, target };
  cand.D = shotElo(cand, target, pocket);        // índice Elo v2
  return cand;
}

/* Combinación: primerContacto → objetivo → tronera (§2/§3 L1) */
function comboCandidate(cx, cy, first, target, pocket, balls) {
  const g2 = ghostPoint(target, pocket);
  if (!g2) return null;
  const dxL = g2.x - first.x, dyL = g2.y - first.y;
  const dL = Math.hypot(dxL, dyL);
  if (dL < 1) return null;
  const g1 = { x: first.x - (dxL / dL) * 2 * P.BALL_R,
               y: first.y - (dyL / dL) * 2 * P.BALL_R };
  const { BX0, BX1, BY0, BY1 } = GEO;
  if (g1.x < BX0 || g1.x > BX1 || g1.y < BY0 || g1.y > BY1) return null;
  const cut1 = Math.abs(normalizeAngle(
    Math.atan2(first.y - cy, first.x - cx) - Math.atan2(g2.y - first.y, g2.x - first.x)));
  const cut2 = Math.abs(normalizeAngle(
    Math.atan2(g2.y - first.y, g2.x - first.x) - Math.atan2(pocket.y - target.y, pocket.x - target.x)));
  if (cut1 > 1.2 || cut2 > 1.2) return null;
  const leg1 = corridorMeasure(cx, cy, g1.x, g1.y, balls, new Set([0, first.id]));
  if (!leg1.ok) return null;
  const leg2 = corridorMeasure(first.x, first.y, g2.x, g2.y, balls, new Set([first.id, target.id]));
  if (!leg2.ok) return null;
  const pl3 = pocketLegState(target.x, target.y, pocket, balls, new Set([target.id]));
  if (!pl3.ok) return null;
  const leg3 = pl3.leg;
  const distCT = Math.hypot(g1.x - cx, g1.y - cy);
  const base = 90 - cut1 * 30 - cut2 * 20 - (distCT / P.TABLE_W) * 20 + 50;
  /* Fix §13.8: cut1, cut2 y dL se exponen por separado; distTP es SOLO
     el tramo objetivo→tronera (antes dL se contaba dos veces).
     cutAngle se conserva como cut1+cut2 para el legado (W.CUT, L4). */
  const cand = { type: "combinacion", targetId: first.id, secondaryId: target.id,
           pocketId: pocket.id, ghostX: g1.x, ghostY: g1.y,
           angle: Math.atan2(g1.y - cy, g1.x - cx),
           cut1, cut2, dL,
           cutAngle: cut1 + cut2, distCT, distTP: g2.distPocket,
           dirty: pl3.dirty,
           legs: [ { margin: leg1.ballMargin, marginAt: leg1.ballMarginAt },
                   { margin: leg2.ballMargin, marginAt: leg2.ballMarginAt },
                   { margin: leg3.ballMargin, marginAt: leg3.ballMarginAt } ],
           baseScore: base, cuePos: null, pocket, target: first };
  cand.D = shotElo(cand, target, pocket);        // índice Elo v2
  return cand;
}

/* Tiro a una banda: blanca rebota una vez antes del contacto.
   Solo si el primer contacto legal está bloqueado en directo. */
function railCandidate(cx, cy, target, pocket, balls) {
  const g = ghostPoint(target, pocket);
  if (!g) return null;
  const { BX0, BX1, BY0, BY1 } = GEO;
  const rails = [
    { ax: BX0, ay: BY0, bx: BX1, by: BY0, fx: 1, fy: -1 },  // superior
    { ax: BX0, ay: BY1, bx: BX1, by: BY1, fx: 1, fy: -1 },  // inferior (espejo y)
    { ax: BX0, ay: BY0, bx: BX0, by: BY1, fx: -1, fy: 1 },  // izquierda
    { ax: BX1, ay: BY0, bx: BX1, by: BY1, fx: -1, fy: 1 }   // derecha
  ];
  let best = null;
  for (const r of rails) {
    /* punto de rebote: reflejar el fantasma sobre la banda y
       cruzar la recta blanca→reflejo con la banda */
    const rx = r.fx < 0 ? 2 * r.ax - g.x : g.x;
    const ry = r.fy < 0 ? 2 * r.ay - g.y : g.y;
    const dx = rx - cx, dy = ry - cy;
    const denom = (r.bx - r.ax) * dy - (r.by - r.ay) * dx;
    if (Math.abs(denom) < 1e-9) continue;
    const t = ((r.ax - cx) * dy - (r.ay - cy) * dx) / ((r.by - r.ay) * dx - (r.bx - r.ax) * dy);
    const hitX = cx + dx * t, hitY = cy + dy * t;
    if (t <= 0.05 || t >= 0.95) continue;
    if (hitX < Math.min(r.ax, r.bx) - 1 || hitX > Math.max(r.ax, r.bx) + 1 ||
        hitY < Math.min(r.ay, r.by) - 1 || hitY > Math.max(r.ay, r.by) + 1) continue;
    const ignore = new Set([0, target.id]);
    const leg1 = corridorMeasure(cx, cy, hitX, hitY, balls, ignore);
    if (!leg1.ok) continue;
    const leg2 = corridorMeasure(hitX, hitY, g.x, g.y, balls, ignore);
    if (!leg2.ok) continue;
    const pl3 = pocketLegState(target.x, target.y, pocket, balls, new Set([target.id]));
    if (!pl3.ok) continue;
    const leg3 = pl3.leg;
    const distCT = Math.hypot(hitX - cx, hitY - cy) + Math.hypot(g.x - hitX, g.y - hitY);
    const cut = Math.abs(normalizeAngle(
      Math.atan2(g.y - hitY, g.x - hitX) - Math.atan2(pocket.y - target.y, pocket.x - target.x)));
    if (cut > 1.35) continue;
    const base = baseScore(cut, distCT, g.distPocket, pocket) - 18;   // banda cuesta
    const cand = { type: "banda", targetId: target.id, pocketId: pocket.id,
      ghostX: g.x, ghostY: g.y, railX: hitX, railY: hitY,
      angle: Math.atan2(hitY - cy, hitX - cx),
      cutAngle: cut, distCT, distTP: g.distPocket, baseScore: base,
      dirty: pl3.dirty,
      legs: [ { margin: leg1.ballMargin, marginAt: leg1.ballMarginAt },
              { margin: leg2.ballMargin, marginAt: leg2.ballMarginAt },
              { margin: leg3.ballMargin, marginAt: leg3.ballMarginAt } ],
      cuePos: null, pocket, target };
    cand.D = shotElo(cand, target, pocket);      // índice Elo v2
    if (!best || cand.baseScore > best.baseScore) best = cand;
  }
  return best;
}

/* Defensa: primer contacto legal suave (§3 L1/§5) */
function safetyCandidate(cx, cy, target, balls) {
  const d = Math.hypot(target.x - cx, target.y - cy);
  if (d < 1) return null;
  return { type: "defensa", targetId: target.id, pocketId: null,
           angle: Math.atan2(target.y - cy, target.x - cx), kick: false,
           cutAngle: 0, distCT: d, distTP: 0,
           baseScore: 5, cuePos: null, pocket: null, target };
}

/* Defensa con toque de banda previo (kick): cuando la línea directa
   a la bola legal está tapada, caminos blanca→banda→bola con ambos
   tramos verificados (bolas, mandíbulas y límites). La simulación
   nominal decidirá si el contacto resulta legal y qué tan bien
   queda escondida la blanca. */
function kickSafetyCandidates(cx, cy, target, balls) {
  const { BX0, BX1, BY0, BY1 } = GEO;
  const rails = [
    { fx:  1, fy: -1, axis: "y", val: BY0 },   // banda superior
    { fx:  1, fy: -1, axis: "y", val: BY1 },   // banda inferior
    { fx: -1, fy:  1, axis: "x", val: BX0 },   // banda izquierda
    { fx: -1, fy:  1, axis: "x", val: BX1 }    // banda derecha
  ];
  const out = [];
  for (const r of rails) {
    /* reflejar el objetivo sobre la banda y hallar el punto de rebote */
    const tx = r.fx < 0 ? 2 * r.val - target.x : target.x;
    const ty = r.fy < 0 ? 2 * r.val - target.y : target.y;
    let tH, hx, hy;
    if (r.axis === "y") {
      if (Math.abs(ty - cy) < 1e-9) continue;
      tH = (r.val - cy) / (ty - cy);
      hx = cx + (tx - cx) * tH; hy = r.val;
    } else {
      if (Math.abs(tx - cx) < 1e-9) continue;
      tH = (r.val - cx) / (tx - cx);
      hx = r.val; hy = cy + (ty - cy) * tH;
    }
    if (tH <= 0.05 || tH >= 0.98) continue;
    /* El punto de rebote vive SOBRE la banda: el margen solo lo
       aleja de esquinas y, en bandas horizontales, de la boca de
       la tronera lateral */
    if (r.axis === "y") {
      if (hx < BX0 + 30 || hx > BX1 - 30) continue;
      if (Math.abs(hx - P.TABLE_W / 2) < GEO.prof.side.railGap + 6) continue;
    } else {
      if (hy < BY0 + 30 || hy > BY1 - 30) continue;
    }
    const ignore = new Set([0, target.id]);
    if (!corridorClear(cx, cy, hx, hy, balls, ignore)) continue;
    if (!corridorClear(hx, hy, target.x, target.y, balls, ignore)) continue;
    const d = Math.hypot(hx - cx, hy - cy) + Math.hypot(target.x - hx, target.y - hy);
    out.push({ type: "defensa", targetId: target.id, pocketId: null,
               angle: Math.atan2(hy - cy, hx - cx), kick: true,
               railX: hx, railY: hy,
               cutAngle: 0, distCT: d, distTP: 0,
               baseScore: 4, cuePos: null, pocket: null, target });
  }
  return out;
}

/* §6 bola en mano: colocación válida espejo del juego */
function placementValid(x, y, balls) {
  const { BX0, BX1, BY0, BY1, pockets } = GEO;
  if (x < BX0 || x > BX1 || y < BY0 || y > BY1) return false;
  for (const b of balls) {
    if (b.pocketed || b.isJaw || b.id === 0) continue;
    if (Math.hypot(b.x - x, b.y - y) < P.BALL_R * 2.1) return false;
  }
  for (const pk of pockets)
    if (Math.hypot(pk.x - x, pk.y - y) < pk.holeR + P.BALL_R * 0.5) return false;
  return true;
}

function generateCandidates(cx, cy, balls, mode, groups, player) {
  const out = [];
  const targets = legalTargets(mode, groups, player, balls);
  for (const t of targets) {
    for (const pk of GEO.pockets) {
      const d = directCandidate(cx, cy, t, pk, balls);
      if (d) out.push(d);
    }
  }
  /* Combinaciones legales (§2): 9-ball L→9; 8-ball propia→propia/8 */
  if (mode === "9ball") {
    const low = targets[0];
    const nine = balls.find(b => b.id === 9 && !b.pocketed);
    if (low && nine && low.id !== 9)
      for (const pk of GEO.pockets) {
        const c = comboCandidate(cx, cy, low, nine, pk, balls);
        if (c) out.push(c);
      }
  } else {
    const g = groups ? groups[player] : null;
    if (g) {
      const rem = balls.filter(b => !b.pocketed && groupOf(b.id) === g);
      const second = rem.length > 0 ? null : balls.find(b => b.id === 8 && !b.pocketed);
      if (second) for (const first of targets)
        for (const pk of GEO.pockets) {
          const c = comboCandidate(cx, cy, first, second, pk, balls);
          if (c) out.push(c);
        }
      else if (rem.length > 1)
        for (const first of targets)
          for (const second2 of rem) {
            if (second2.id === first.id) continue;
            for (const pk of GEO.pockets) {
              const c = comboCandidate(cx, cy, first, second2, pk, balls);
              if (c) out.push(c);
            }
          }
    }
  }
  /* Bandas solo si no hay directas: primer contacto legal vía rebote */
  if (out.filter(c => c.type === "directa").length === 0) {
    for (const t of targets)
      for (const pk of GEO.pockets) {
        const r = railCandidate(cx, cy, t, pk, balls);
        if (r) out.push(r);
      }
  }
  /* Defensas: directa al primer objetivo con corredor libre; con
     toque de banda previo (kick) cuando la bola legal está tapada */
  let safetyAdded = false, kicks = 0;
  for (const t of targets) {
    if (!safetyAdded && corridorClear(cx, cy, t.x, t.y, balls, new Set([0, t.id]))) {
      const s = safetyCandidate(cx, cy, t, balls);
      if (s) { out.push(s); safetyAdded = true; continue; }
    }
    if (kicks < 4)
      for (const k of kickSafetyCandidates(cx, cy, t, balls)) {
        if (kicks >= 4) break;
        out.push(k); kicks++;
      }
  }
  /* §10 (v4): ordenar por D ascendente (más fácil primero);
     baseScore queda como desempate legado. Defensas (D null) al final. */
  const dKey = c => (c.D == null || !isFinite(c.D)) ? Infinity : c.D;
  out.sort((a, b) => dKey(a) - dKey(b) ||
                     b.baseScore - a.baseScore ||
                     a.targetId - b.targetId ||
                     (a.pocketId < b.pocketId ? -1 : 1));
  return out.slice(0, 30);
}

/* ========== §5 PUNTUACIÓN POR PRIORIDADES ESTRICTAS ==========
   1 evitar derrota · 2 victoria legal · 3 evitar falta/suicidio ·
   4 embocar objetivo · 5 mantener turno · 6 tiro visible ·
   7 distancia siguiente · 8 no regalar al rival · 9 robustez.
   Una falta NUNCA se compensa con bolas embocadas. */
/* v2 §7: W.POS_RISK se retira — la severidad del riesgo de blanca es
   continua (1 − erf(σ_scratch/(σ_BOT·√2))) sobre la trayectoria medida,
   no una métrica local con umbral 70. */
const W = { SUCCESS: 300, LEGAL: 400, SCRATCH: 500, CUT: 60 };

function nextTargetsAfter(mode, groups, player, ballsAfter) {
  return legalTargets(mode, groups, player, ballsAfter);
}

function positionScore(cx, cy, targets, balls) {
  let best = 0;
  for (const t of targets)
    for (const pk of GEO.pockets) {
      const c = directCandidate(cx, cy, t, pk, balls);
      if (c && c.baseScore > best) best = c.baseScore;
    }
  return best;   // 0..~104
}

function opponentBest(cx, cy, mode, groups, player, balls) {
  const opp = player === 1 ? 2 : 1;
  return positionScore(cx, cy, legalTargets(mode, groups, opp, balls), balls);
}

/* v2 §7: severidad del riesgo de blanca a partir del cueMargin MEDIDO
   en la simulación (toda la trayectoria post-contacto, no la posición
   final; la escala natural es captureR, sin umbral). σ ≥ 0 recortado:
   un scratch real ya cuenta en scratchRate. */
function scratchSeverity(shotState, A) {
  const st = shotState;
  if (st.cueMargin === Infinity || !isFinite(st.cueMargin)) return 0;
  const sig = Math.max(st.cueMargin, 0) / (Math.max(st.cueMarginAt, 1) * (A || 1));
  return 1 - erf(Math.min(sig, 1) / (SIG_BOT * Math.SQRT2));
}

function scoreSim(sim, cand, mode, groups, player, ballsBefore) {
  const st = sim.shotState;
  const pocketed = st.pocketed;
  const potId = cand.secondaryId || cand.targetId;
  let foul = false, win = false, loss = false;

  if (!st.contacted) foul = true;
  else if (!firstHitLegal(st.firstHit, mode, groups, player, ballsBefore)) foul = true;
  if (st.scratch) foul = true;
  if (st.contacted && pocketed.length === 0 && !st.railAfter) foul = true;

  if (mode === "9ball") {
    if (pocketed.includes(9) && !foul && st.firstHit === getLowest(ballsBefore)) win = true;
    /* la 9 con falta vuelve al pie: es falta, no derrota */
  } else {
    if (pocketed.includes(8)) {
      const g = groups ? groups[player] : null;
      const remBefore = g ? ballsBefore.filter(b => !b.pocketed && groupOf(b.id) === g).length : -1;
      if (g && remBefore === 0 && !foul && st.firstHit === 8) win = true;
      else loss = true;                                  // derrota inmediata
    }
  }

  let score = cand.baseScore;
  if (loss) return { score: -9000 + cand.baseScore * 0.01, foul: true, loss: true,
                     win: false, pocketed, firstHit: st.firstHit, scratch: st.scratch,
                     cueFinal: sim.cueFinal };
  if (win) score += 5000;
  else if (foul) score = Math.min(score, 0) - 1500;      // §5: sin compensación
  else {
    if (potId !== null && pocketed.includes(potId)) score += 800;
    for (const pid of pocketed) {
      if (pid === potId || pid === 8 || pid === 9) continue;
      if (mode === "9ball") score += 100;
      else {
        const g = groups ? groups[player] : null;
        if (!g) score += 150;
        else score += (groupOf(pid) === g) ? 250 : -200;
      }
    }
    const nextT = nextTargetsAfter(mode, groups, player, sim.balls);
    score += positionScore(sim.cueFinal.x, sim.cueFinal.y, nextT, sim.balls) * 0.6;
    if (potId === null || !pocketed.includes(potId)) {   // valor defensivo §5
      const opp = opponentBest(sim.cueFinal.x, sim.cueFinal.y, mode, groups, player, sim.balls);
      score += (opp < 30) ? 300 : -opp * 1.5;
      if (st.railAfter) score += 20;
    }
  }
  return { score, foul, win, loss: false, pocketed,
           firstHit: st.firstHit, scratch: st.scratch, cueFinal: sim.cueFinal };
}

/* ========== ORQUESTACIÓN POR CAPAS (§3/§4) ========== */
/* v1: la potencia nominal sale de la ventana del candidato.
   Punto 3 (D3): se juega la MÍNIMA viable + 2σ_p (pWin.chosen), no el
   centro — antes ~0.52 típico, 5–10× lo necesario, con juego posicional
   arruinado y régimen de ventana angular no plana. */
function powersFor(cand) {
  if (cand.type === "defensa")
    return (cand.distCT || 200) > 250 ? [0.55, 0.72] : [0.42];
  if (cand.pWin)
    return [Math.max(0.08, Math.min(1, cand.pWin.chosen))];
  return [0.5];     // sin ventana (D=Infinity): potencia media de respaldo
}
function effectsFor(difficulty) {
  return difficulty === "hard"
    ? [{ e: 0, f: 0 }, { e: 0, f: 0.25 }, { e: 0, f: -0.2 }, { e: 0.3, f: 0.1 }, { e: -0.3, f: 0.1 }]
    : [{ e: 0, f: 0 }];
}

function createRun(state) {
  configure(state.physics);
  const difficulty = state.difficulty || "hard";
  const balls = state.balls.map(b => new Ball(b.id, b.x, b.y, false, !!b.pocketed));
  let cue = balls.find(b => b.id === 0);
  if ((!cue || cue.pocketed) && state.ballInHand) {
    cue = new Ball(0, P.TABLE_W * 0.25, P.TABLE_H * 0.5, false, false);
    balls.push(cue);
  }
  /* v4: nivel estimado del jugador (state.playerSkill, del estimador
     por partida). El bot juega "justo por encima" (+100).
     T4 §8: compuerta de confianza — si la dispersión del estimador es
     alta (sd ≥ 120), el estimado no es fiable y se queda en el arranque
     en frío (S_BOT = 1500). */
  const ctx = {
    t0: performance.now(), deadline: DEADLINE_MS - RETURN_MARGIN_MS,
    state, difficulty, balls, cue,
    mode: state.mode, groups: state.groups, player: state.currentPlayer,
    ballInHand: !!state.ballInHand,
    S_BOT: state.playerSkill ?? S_BOT,
    phase: "L1", queue: [], results: [], finalists: [],
    simsDone: 0, simsPlanned: 0, pct: 0, expired: false
  };
  return ctx;
}

const elapsed = ctx => performance.now() - ctx.t0;
const expired = ctx => elapsed(ctx) > ctx.deadline;

/* --- L1 (+ §6 bola en mano): construye la cola de simulaciones L2 --- */
function runL1(ctx) {
  let cands;
  if (ctx.ballInHand) {
    /* §6: cuadrícula amplia; por cada colocación se RECALCULA todo */
    const { BX0, BX1, BY0, BY1 } = GEO;
    const spots = [];
    for (let ix = 0; ix < 8; ix++) for (let iy = 0; iy < 5; iy++) {
      const x = BX0 + (BX1 - BX0) * (ix + 0.5) / 8;
      const y = BY0 + (BY1 - BY0) * (iy + 0.5) / 5;
      if (placementValid(x, y, ctx.balls)) spots.push({ x, y });
    }
    const perSpot = [];
    for (const s of spots) {
      const c = generateCandidates(s.x, s.y, ctx.balls, ctx.mode, ctx.groups, ctx.player)
        .filter(k => k.type !== "defensa");
      if (c.length) perSpot.push({ spot: s, best: c[0] });
    }
    perSpot.sort((a, b) => {
      const dK = c => (c.D == null || !isFinite(c.D)) ? Infinity : c.D;
      return dK(a.best) - dK(b.best) || b.best.baseScore - a.best.baseScore;
    });
    /* §6: refinar alrededor de las 3 mejores colocaciones */
    const refined = [];
    for (const ps of perSpot.slice(0, 3))
      for (let dx = -20; dx <= 20; dx += 10)
        for (let dy = -20; dy <= 20; dy += 10) {
          const x = ps.spot.x + dx, y = ps.spot.y + dy;
          if (placementValid(x, y, ctx.balls)) refined.push({ x, y });
        }
    const allSpots = perSpot.map(p => p.spot).concat(refined);
    cands = [];
    for (const s of allSpots) {
      const cs = generateCandidates(s.x, s.y, ctx.balls, ctx.mode, ctx.groups, ctx.player)
        .filter(k => k.type !== "defensa").slice(0, 2);
      for (const k of cs) { k.cuePos = { x: s.x, y: s.y }; k.type = "bolaEnMano"; cands.push(k); }
    }
    cands.sort((a, b) => {
      const dK = c => (c.D == null || !isFinite(c.D)) ? Infinity : c.D;
      return dK(a) - dK(b) || b.baseScore - a.baseScore;
    });
    cands = cands.slice(0, 18);
    if (cands.length === 0) {
      /* sin corredor desde ninguna colocación: defensa desde la mejor */
      const t = legalTargets(ctx.mode, ctx.groups, ctx.player, ctx.balls)[0];
      if (t) cands = [{ ...safetyCandidate(perSpot.length ? perSpot[0].spot.x : P.TABLE_W * 0.25,
                                           perSpot.length ? perSpot[0].spot.y : P.TABLE_H / 2, t, ctx.balls),
                        cuePos: perSpot.length ? perSpot[0].spot : { x: P.TABLE_W * 0.25, y: P.TABLE_H / 2 },
                        type: "bolaEnMano" }];
    }
  } else {
    cands = generateCandidates(ctx.cue.x, ctx.cue.y, ctx.balls, ctx.mode, ctx.groups, ctx.player);
  }
  ctx.candidates = cands;
  /* Cola L2: mejores 18 × potencias × efectos */
  for (const cand of cands.slice(0, 18))
    for (const pwr of powersFor(cand))
      for (const ef of effectsFor(ctx.difficulty))
        ctx.queue.push({ cand, params: {
          angle: cand.angle, power: pwr, english: ef.e, follow: ef.f,
          cuePos: cand.cuePos || null } });
  ctx.simsPlanned += ctx.queue.length;
  ctx.phase = "L2";
  ctx.pct = 8;
}

function runOneSim(ctx) {
  const job = ctx.queue.shift();
  if (!job) return;
  const sim = simulateShot(ctx.balls, job.params);
  ctx.simsDone++;
  const sc = scoreSim(sim, job.cand, ctx.mode, ctx.groups, ctx.player, ctx.balls);
  ctx.results.push({
    ...job.params, targetId: job.cand.targetId, pocketId: job.cand.pocketId,
    secondaryId: job.cand.secondaryId || null, candidateType: job.cand.type,
    kick: job.cand.kick || false,
    baseScore: job.cand.baseScore, cutAngle: job.cand.cutAngle,
    distCT: job.cand.distCT, distTP: job.cand.distTP,
    D: job.cand.D ?? null,                        // índice Elo v2
    A: job.cand.A ?? null,                        // amplificación total
    cueMargin: sim.shotState.cueMargin,           // §13.7 (v2: σ_scratch)
    cueMarginAt: sim.shotState.cueMarginAt,
    score: sc.score, foul: sc.foul, win: sc.win, loss: sc.loss,
    pocketed: sc.pocketed, firstHit: sc.firstHit, scratch: sc.scratch,
    cueFinal: sc.cueFinal, stillMoving: sim.stillMoving, truncated: sim.truncated
  });
  const span = ctx.phase === "L2" ? [10, 70] : ctx.phase === "L3" ? [70, 85] : [85, 98];
  const frac = ctx.simsPlanned ? ctx.simsDone / ctx.simsPlanned : 1;
  ctx.pct = Math.min(span[1], span[0] + (span[1] - span[0]) * frac);
}

/* §3 L2: elimina faltas salvo que no exista alternativa legal */
function legalPool(ctx) {
  const ok = ctx.results.filter(r => !r.foul);
  return ok.length ? ok : ctx.results;
}

function sortResults(arr) {
  arr.sort((a, b) => b.score - a.score || a.angle - b.angle ||
                    a.power - b.power || (a.targetId || 99) - (b.targetId || 99) ||
                    ((a.pocketId || "") < (b.pocketId || "") ? -1 : 1));
  return arr;
}

function runL3(ctx) {
  /* §3: refina solo los 5 mejores; descenso por coordenadas */
  const top = sortResults(legalPool(ctx).slice()).slice(0, 5);
  const angleOffsets = [-0.012, 0.012, -0.006, 0.006, -0.003, 0.003];
  const powerOffsets = [-0.08, 0.08, -0.04, 0.04, -0.02, 0.02];
  for (const r of top) {
    for (const da of angleOffsets)
      ctx.queue.push({ cand: r.candRef, params: { ...r.paramsRef, angle: r.paramsRef.angle + da } });
    for (const dp of powerOffsets)
      ctx.queue.push({ cand: r.candRef, params: { ...r.paramsRef,
        power: Math.max(0.08, Math.min(1, r.paramsRef.power + dp)) } });
  }
  ctx.simsPlanned += ctx.queue.length;
  ctx.phase = "L3";
  ctx.pct = 70;
}

/* ========== v3 §12: BISECCIÓN 2D (reemplaza L4) ==========
   Por finalista (~30-50 sims):
     1) bisección en α a potencia fija → [α⁻, α⁺]: σ_tol medido y
        ángulo óptimo = punto medio (no el geométrico)
     2) bisección en p al ángulo óptimo → [p_lo, p_hi]: fallo =
        no embocar O σ_scratch medido bajo el piso fijo SIG_SCRATCH_MIN
     3) D completo de ambos ejes (medido, misma escala que el analítico)
     4) se itera 1→2→1 una vez (converge en dos vueltas)
   Presupuesto §11: DEADLINE 30 s, margen 500 ms, salida temprana. */
const BISECT = { ANG_STEP: 0.004, ANG_MAX: 0.032, ANG_ITERS: 4,
                 P_MIN: 0.04, P_STEP: 0.05, P_ITERS: 3,
                 EST_SIMS: 45, N_FINAL: 5 };
/* Escala medida: el simulador es más tolerante que el corredor
   analítico (captureR tragona ~13 uds vs a−2R=4.28). Estas referencias
   se calibran con la bisección sobre el tiro ancla §3 para que
   D_meas(ancla) = 1500 exacto; fuera del ancla, las desviaciones
   medida↔analítica son la señal genuina (§13.13). */
const ELO_SIG_MEAS_REF = 3.44e-3;    // σA medido en el ancla (calibrado v3)
const ELO_SIG_P_MEAS_REF = 0.462;    // σP medido en el ancla (calibrado v3)

const B_STAGES = [
  { kind: "probe" },                                            // 0 nominal
  { kind: "edge", axis: "ang", side: -1, pass: 1 },
  { kind: "edge", axis: "ang", side: +1, pass: 1 },
  { kind: "confirm", axis: "ang", pass: 1 },                    // (αOpt1, p0)
  { kind: "edge", axis: "pow", side: -1, pass: 1 },
  { kind: "edge", axis: "pow", side: +1, pass: 1 },
  { kind: "confirm", axis: "pow", pass: 1 },                    // (αOpt1, pOpt1)
  { kind: "edge", axis: "ang", side: -1, pass: 2 },
  { kind: "edge", axis: "ang", side: +1, pass: 2 },
  { kind: "confirm", axis: "ang", pass: 2 },                    // (αOpt2, pOpt1)
  { kind: "edge", axis: "pow", side: -1, pass: 2 },
  { kind: "edge", axis: "pow", side: +1, pass: 2 }
];

/* Buscador de arista: desde lo (éxito conocido) duplica el paso hasta
   el primer fallo y bisecciona. Devuelve el próximo valor a probar,
   o undefined cuando fija e.edge = último éxito (conservador). */
function edgeNext(e, lastOK) {
  if (lastOK !== undefined) { if (lastOK) e.lo = e.probe; else e.hi = e.probe; }
  if (e.hi == null) {
    const rem = e.bound - e.lo;
    if (e.side * rem <= 1e-9) { e.edge = e.bound; return undefined; }
    e.probe = e.side * rem > e.step ? e.lo + e.side * e.step : e.bound;
    e.step *= 2;
    return e.probe;
  }
  if (e.iters-- > 0) { e.probe = (e.lo + e.hi) / 2; return e.probe; }
  e.edge = e.lo;
  return undefined;
}

/* Una sonda: simula y aplica el criterio de fallo §12.
   Efectos secundarios: contadores del job y ctx.simsDone. */
function probeOutcome(ctx, job, angle, power) {
  const sim = simulateShot(ctx.balls, { ...job.paramsRef, angle, power });
  ctx.simsDone++;
  const st = sim.shotState;
  const sc = scoreSim(sim, job.candRef, ctx.mode, ctx.groups, ctx.player, ctx.balls);
  job.sims++;
  if (!sc.foul) job.legal++;
  if (sc.scratch) job.scratch++;
  if (job.sims === 1) job.sev = scratchSeverity(st, job.candRef.A);
  if (job.isDefense) return !sc.foul;
  const potId = job.candRef.secondaryId || job.candRef.targetId;
  const potted = sc.win || (!sc.foul && potId !== null && sc.pocketed.includes(potId));
  if (!potted) return false;
  /* §12: fallo también si σ_scratch medido queda bajo el piso fijo */
  if (isFinite(st.cueMargin)) {
    const sig = Math.max(st.cueMargin, 0) / (Math.max(st.cueMarginAt, 1) * (job.candRef.A || 1));
    if (sig < sigmaExec(ctx.S_BOT)) return false;
  }
  return true;
}

function makeBisectJob(r) {
  return {
    candRef: r.candRef, target: r, paramsRef: r.paramsRef,
    isDefense: r.pocketId == null,
    alpha0: r.paramsRef.angle,
    p0: Math.max(0.08, Math.min(1, r.paramsRef.power)),
    sims: 0, legal: 0, scratch: 0, sev: 0,
    bandsObserved: r.bandsObserved,   // T3: bandas observadas (o supuestas por tipo)
    stage: 0, edge: null, lastOK: undefined,
    aMinus: null, aPlus: null, pLo: null, pHi: null,
    prevAMinus: null, prevAPlus: null,
    failed: false
  };
}

function aOptOf(job) {
  return job.aMinus != null && job.aPlus != null ? (job.aMinus + job.aPlus) / 2 : job.alpha0;
}
function pOptOf(job) {
  return job.pLo != null && job.pHi != null ? (job.pLo + job.pHi) / 2 : job.p0;
}

function stepDefenseJob(ctx, job) {
  const probes = [[0, 0], [0.008, 0], [-0.008, 0], [0, 0.04], [0, -0.04]];
  if (job.idx == null) { job.idx = 0; job.oks = 0; }
  const [da, dp] = probes[job.idx++];
  if (probeOutcome(ctx, job, job.alpha0 + da,
        Math.max(0.08, Math.min(1, job.p0 + dp)))) job.oks++;
  if (job.idx < probes.length) return false;
  job.defenseRate = job.oks / probes.length;
  finishJob(ctx, job);
  return true;
}

/* Avanza el job UNA sonda. Devuelve true cuando terminó. */
function stepJob(ctx, job) {
  if (job.isDefense) return stepDefenseJob(ctx, job);
  const st = B_STAGES[job.stage];
  if (!st) { finishJob(ctx, job); return true; }
  let angle, power;
  if (st.kind === "probe") { angle = job.alpha0; power = job.p0; }
  else if (st.kind === "confirm") { angle = aOptOf(job); power = pOptOf(job); }
  else {
    if (!job.edge) {
      if (st.axis === "ang") {
        const c = aOptOf(job);
        if (st.pass === 2) { job.prevAMinus = job.aMinus; job.prevAPlus = job.aPlus; }
        job.edge = { lo: c, hi: null, side: st.side, step: BISECT.ANG_STEP,
                     bound: c + st.side * BISECT.ANG_MAX, iters: BISECT.ANG_ITERS, probe: c };
      } else {
        const c = pOptOf(job);
        job.edge = { lo: c, hi: null, side: st.side, step: BISECT.P_STEP,
                     bound: st.side < 0 ? BISECT.P_MIN : 1, iters: BISECT.P_ITERS, probe: c };
      }
    }
    const v = edgeNext(job.edge, job.lastOK);
    job.lastOK = undefined;
    if (v === undefined) {                       // arista fijada
      if (st.axis === "ang") { if (st.side < 0) job.aMinus = job.edge.edge; else job.aPlus = job.edge.edge; }
      else { if (st.side < 0) job.pLo = job.edge.edge; else job.pHi = job.edge.edge; }
      job.edge = null;
      job.stage++;
      return false;
    }
    if (st.axis === "ang") { angle = v; power = st.pass === 1 ? job.p0 : pOptOf(job); }
    else { angle = aOptOf(job); power = v; }
  }
  const ok = probeOutcome(ctx, job, angle, power);
  if (st.kind === "edge") { job.lastOK = ok; return false; }
  job.stage++;
  if (ok) return false;
  if (st.kind === "probe") {
    /* Entrada sucia u óptimo descentralizado: antes de declarar el
       fallo, buscar una semilla de éxito cerca del nominal. */
    if (job.seedIdx == null) job.seedIdx = 0;
    const SEEDS = [0.008, -0.008, 0.016, -0.016, 0.024, -0.024];
    while (job.seedIdx < SEEDS.length) {
      const o = SEEDS[job.seedIdx++];
      if (probeOutcome(ctx, job, job.alpha0 + o, job.p0)) {
        job.alpha0 += o;                       // nuevo centro con éxito conocido
        return false;
      }
    }
    job.failed = true; finishJob(ctx, job); return true;
  }
  /* confirmación fallida → revertir el óptimo recién medido */
  if (st.axis === "ang" && st.pass === 1) { job.aMinus = null; job.aPlus = null; }
  else if (st.axis === "pow") { job.pLo = null; job.pHi = null; }
  else { job.aMinus = job.prevAMinus; job.aPlus = job.prevAPlus; }
  return false;
}

function finishJob(ctx, job) {
  const r = job.target;
  r.measured = true;
  r.legalRate = job.legal / Math.max(1, job.sims);
  r.scratchRate = job.scratch / Math.max(1, job.sims);
  if (job.isDefense) {
    r.successRate = job.defenseRate ?? 0;
    r.D_meas = null;
  } else if (job.failed || job.aMinus == null || job.aPlus == null ||
             job.pLo == null || job.pHi == null) {
    r.successRate = 0;
    r.D_meas = Infinity;
  } else {
    const sigA = Math.max(1e-4, (job.aPlus - job.aMinus) / 2);
    const sigP = Math.max(0.005, (job.pHi - job.pLo) / 2);
    r.sigA_meas = sigA; r.sigP_meas = sigP;      // §13 instrumentación
    /* T3 (punto 2 backlog): las bandas que entran a D_meas son las
       OBSERVADAS en la simulación sonda (measureShot) o las del tipo de
       candidato (camino del bot, comportamiento previo). Un tiro de dos
       bandas paga 2 × ELO_BAND_COST. */
    const bands = job.bandsObserved ?? (job.candRef.type === "banda" ? 1 : 0);
    r.D_meas = 1500 + ELO_K * (Math.log10(ELO_SIG_MEAS_REF / sigA) +
                               Math.log10(ELO_SIG_P_MEAS_REF / sigP)) +
               bands * ELO_BAND_COST;
    r.successRate = potProb(r.D_meas, ctx.S_BOT);
    /* adoptar los óptimos medidos como el tiro final */
    r.angle = (job.aPlus + job.aMinus) / 2;
    r.power = (job.pHi + job.pLo) / 2;
    r.D = r.D_meas;          // el medido sustituye al analítico en finalistas
  }
  r.score += r.successRate * W.SUCCESS + r.legalRate * W.LEGAL -
             r.scratchRate * W.SCRATCH - (r.cutAngle || 0) / (Math.PI / 2) * W.CUT -
             job.sev * W.SCRATCH;
  const frac = ctx.simsPlanned ? ctx.simsDone / ctx.simsPlanned : 1;
  ctx.pct = Math.min(98, 85 + 13 * frac);
}

function runL4(ctx) {
  /* §12: 5 finalistas, bisección 2D cooperativa */
  const top = sortResults(legalPool(ctx).slice()).slice(0, BISECT.N_FINAL);
  ctx.finalists = top;
  for (const r of top) ctx.queue.push(makeBisectJob(r));
  ctx.simsPlanned += top.length * BISECT.EST_SIMS;
  ctx.phase = "L4";
  ctx.pct = 85;
}

function runOneBisect(ctx) {
  const job = ctx.queue[0];
  if (!job) return;
  if (stepJob(ctx, job)) {
    ctx.queue.shift();
  }
}

/* Paso cooperativo: procesa ~budgetMs de trabajo. Devuelve true al terminar. */
function stepRun(ctx, budgetMs) {
  const sliceStart = performance.now();
  for (;;) {
    if (ctx.phase === "L1") { runL1(ctx); }
    if (expired(ctx)) { ctx.expired = true; return true; }
    if (ctx.queue.length === 0) {
      if (ctx.phase === "L2") { attachRefs(ctx); runL3(ctx); continue; }
      if (ctx.phase === "L3") { attachRefs(ctx); runL4(ctx); continue; }
      return true;                                   // L4 completa
    }
    if (ctx.phase === "L4") runOneBisect(ctx); else runOneSim(ctx);
    if (performance.now() - sliceStart > budgetMs) return false;
  }
}

/* Los resultados necesitan referencia a su candidato/params para
   L3/L4; se adjuntan a los que aún no las tengan (L3 añade nuevos) */
function attachRefs(ctx) {
  for (const r of ctx.results) {
    if (r.paramsRef) continue;
    r.paramsRef = { angle: r.angle, power: r.power, english: r.english,
                    follow: r.follow, cuePos: r.cuePos || null };
    /* T3: en el camino del bot las bandas se las debe al generador de
       candidatos (comportamiento previo, preservado a propósito) */
    r.bandsObserved = r.candidateType === "banda" ? 1 : 0;
    r.candRef = { targetId: r.targetId, pocketId: r.pocketId,
                  secondaryId: r.secondaryId, kick: r.kick || false,
                  type: r.candidateType, baseScore: r.baseScore,
                  cutAngle: r.cutAngle, distCT: r.distCT, distTP: r.distTP,
                  D: r.D ?? null, A: r.A ?? null };
  }
}

function finalize(ctx) {
  attachRefs(ctx);
  const pool = sortResults(legalPool(ctx).slice());
  let best = pool[0];
  if (!best) {
    /* §4: nada evaluado → mejor defensa legal geométrica */
    const t = legalTargets(ctx.mode, ctx.groups, ctx.player, ctx.balls)[0];
    const s = t ? safetyCandidate(ctx.cue.x, ctx.cue.y, t, ctx.balls) : null;
    if (!s) return { error: "no candidates" };
    best = { angle: s.angle, power: 0.42, english: 0, follow: 0,
             targetId: t.id, pocketId: null, secondaryId: null,
             candidateType: "defensa", score: 0, pocketed: [], cuePos: null,
             successRate: 0, legalRate: 1, scratchRate: 0, cutAngle: 0 };
  }
  let angle = best.angle, power = best.power;
  const calculationTimeMs = Math.round(elapsed(ctx));
  const shot = {
    angle, power,
    english: best.english || 0, follow: best.follow || 0,
    targetId: best.targetId, pocketId: best.pocketId,
    secondaryId: best.secondaryId || null,
    cuePlacement: best.paramsRef ? best.paramsRef.cuePos : (best.cuePos || null),
    candidateType: best.candidateType,
    kick: !!best.kick,
    distCT: best.distCT ?? null,
    D: best.D ?? null,                            // índice Elo (medido en finalistas v3)
    D_meas: best.D_meas ?? null,                  // §12: null si no se midió
    S_bot: ctx.S_BOT,                             // v4: nivel de juego del bot
    sigA: best.sigA_meas ?? null, sigP: best.sigP_meas ?? null,
    score: Math.round(best.score * 10) / 10,
    successRate: best.successRate ?? null,
    legalRate: best.legalRate ?? null,
    scratchRate: best.scratchRate ?? null,
    isSafety: best.candidateType === "defensa" || best.score < 50,
    isWinning: !!best.win,
    pocketedExpected: best.pocketed || [],
    simulationsCompleted: ctx.simsDone,
    calculationTimeMs,
    expired: ctx.expired,
    reasoning: `${best.candidateType} · objetivo ${best.targetId}` +
      (best.secondaryId ? `→${best.secondaryId}` : "") +
      ` a ${best.pocketId || "—"} · corte ${((best.cutAngle || 0) * 180 / Math.PI).toFixed(1)}°` +
      ` · D ${best.D != null && isFinite(best.D) ? Math.round(best.D) : (best.D === Infinity ? "∞" : "—")}` +
      ` · éxito ${best.successRate != null ? (best.successRate * 100).toFixed(0) + "%" : "s/d"}` +
      ` · ${ctx.simsDone} sims · ${calculationTimeMs} ms`
  };
  const top = pool.slice(0, 5).map(r => ({
    angle: r.angle, power: r.power, targetId: r.targetId, pocketId: r.pocketId,
    candidateType: r.candidateType, score: Math.round(r.score),
    D: r.D ?? null, D_meas: r.D_meas ?? null,
    baseScore: r.baseScore ?? null               // par para validación v0
  }));
  return { shot, top };
}

/* ========== BÚSQUEDA PRINCIPAL (interna) ==========
   Lotes cooperativos de ~25 ms: un solo hilo, la UI respira
   entre tajadas y onProgress reporta el porcentaje (0..100). */
function runBotSearch(state, onProgress, onDone) {
  const ctx = createRun(state);
  const report = () => onProgress(Math.round(ctx.pct));
  const slice = () => {
    let done;
    try {
      done = stepRun(ctx, 25);
    } catch (error) {
      onDone({ error: error instanceof Error ? error.message : String(error),
               shot: null });
      return;
    }
    report();
    if (done) {
      try {
        onDone(finalize(ctx));
      } catch (error) {
        onDone({ error: error instanceof Error ? error.message : String(error),
                 shot: null });
      }
      return;
    }
    setTimeout(slice, 0);
  };
  setTimeout(slice, 0);
}

/* ========== INTERFAZ PÚBLICA (contrato con index19.html) ========== */
function analyze(state, onProgress, onComplete) {
  const reportProgress =
    typeof onProgress === "function" ? onProgress : function () {};
  const finish =
    typeof onComplete === "function" ? onComplete : function () {};
  try {
    reportProgress(0);
    runBotSearch(state, reportProgress, function (result) {
      reportProgress(100);
      finish(result);
    });
  } catch (error) {
    finish({
      error: error instanceof Error ? error.message : String(error),
      shot: null
    });
  }
}

/* D analítico de un tiro concreto ya decidido (p. ej. el del jugador,
   para la UI / futuro estimador v4): misma escala que shotElo.
   state: igual que analyze (usa state.physics y state.balls PRE-tiro).
   Devuelve D (finito) o null si falta bola/tronera o no hay geometría. */
function rateShot(state, targetId, pocketId) {
  configure(state && state.physics);
  const balls = (state.balls || []).filter(b => !b.pocketed)
    .map(b => ({ id: b.id, x: b.x, y: b.y, pocketed: false }));
  const cue = balls.find(b => b.id === 0);
  const target = balls.find(b => b.id === targetId);
  const pocket = GEO.pockets.find(p => p.id === pocketId);
  if (!cue || !target || !pocket) return null;
  let cand = directCandidate(cue.x, cue.y, target, pocket, balls);
  if (!cand) {
    /* corredor obstruido por bolas: aproximar con el D geométrico
       del tiro aislado (sin estorbos) */
    cand = directCandidate(cue.x, cue.y, target, pocket, [cue, target]);
  }
  return cand ? cand.D : null;
}

/* ========== v4: estimador MAP del jugador (por partida, sin historial) ==========
   samples: [{D, y}] con y ∈ {0,1} (1 = embocó). MAP con prior N(1500, 300²):
   maximiza  Σ [y·ln p + (1−y)·ln(1−p)] − (S−1500)²/(2·300²),  p = potProb(D,S).
   Rejilla 800..2200 paso 5 + refinamiento parabólico: sobra para ~10 muestras. */
/* §13.10 (punto 1 backlog): la cuantización del puntero (~2.5 mrad;
   puntero ~1 px a distancia típica, flechas de ajuste 8 mrad) NO es
   un techo de S: es una fuente de error independiente que entra en la
   verosimilitud vía potProbQ. El prior queda dentro de la rejilla y el
   posterior se ensancha solo cuando los datos dejan de ser informativos. */
const PLAYER_AIM_QUANT = 0.0025;  // rad

function estimateSkill(samples) {
  if (!samples || samples.length === 0) return null;
  /* PRIOR_SD = 250 (§8; estaba en 300 por error mío: pesaba menos y
     amplificaba movimientos por muestra).
     Notas residuales registradas (no bloqueantes, ver punto 7):
     · Colas logística (bot) vs gaussiana (estimador) divergen lejos del
       centro (×2.4 a D−S=+600), pero coinciden <2% en los offsets de
       uso real (S_BOT = S+100, D* = S−150).
     · Zona muerta explícita: con q=2.5 mrad, p satura para D ≲ 1000 —
       esas muestras no informan (defendible, y el HUD las descuenta).
     · Mala atribución: sensible en D ≈ 1200–1400 (±170…325 pts por
       muestra errada sobre base de 6); inofensiva fuera de ese rango. */
  const PRIOR_MU = 1500, PRIOR_SD = 250;
  const logLik = S => {
    let ll = -((S - PRIOR_MU) ** 2) / (2 * PRIOR_SD * PRIOR_SD);
    for (const s of samples) {
      if (s.D == null || !isFinite(s.D)) continue;
      /* q = cuantización del puntero: los aciertos dejan de ser
         informativos cuando σ_exec ≪ q/√12 — sin truncar la rejilla */
      const p = Math.min(0.9999, Math.max(1e-4, potProbQ(s.D, S, PLAYER_AIM_QUANT)));
      ll += s.y ? Math.log(p) : Math.log(1 - p);
    }
    return ll;
  };
  /* T4 (punto 2 backlog): la verosimilitud es BIMODAL en casos ambiguos
     (medido: 4×1500✓ + 2×1600✓ + 1×1000✗ → dos máximos a ~475 Elo de
     distancia, Δll = 0.1–0.2 nats; el argmax salta con ruido mínimo).
     Mitigación: devolver la MEDIA POSTERIOR (estable) y la DISPERSIÓN
     (que expresa la ambigüedad en vez de esconderla). La solución de
     fondo son residuos continuos — punto 7, fuera de alcance. */
  const grid = [];
  let bestS = 1500, bestL = -Infinity;
  for (let S = 800; S <= 2200; S += 5) {
    const l = logLik(S);
    grid.push([S, l]);
    if (l > bestL) { bestL = l; bestS = S; }
  }
  let Z = 0, m = 0, m2 = 0;
  for (const [S, l] of grid) {
    const w = Math.exp(l - bestL);
    Z += w; m += w * S; m2 += w * S * S;
  }
  const mean = m / Z;
  const sd = Math.sqrt(Math.max(0, m2 / Z - mean * mean));
  return { S: Math.round(mean), sd: Math.round(sd), mode: bestS, n: samples.length };
}

/* T2 (punto 2 backlog): A "a mano" cuando el constructor específico no
   puede reconstruir la geometría (corredor obstruido por bolas). Misma
   fórmula que shotElo. Jamás se cae silenciosamente al directo: si ni
   así se puede, measureShot devuelve null (mejor no medir que medir mal:
   el HTML cae entonces al rateShot analítico, camino ya previsto). */
function manualAmp(type, cx, cy, first, target, pocket) {
  const g2 = ghostPoint(target, pocket);
  if (!g2) return null;
  if (type === "combinacion" && first) {
    /* A = A1 · (1 + dL / (2R·cos θ2)) — como shotElo */
    const dxL = g2.x - first.x, dyL = g2.y - first.y;
    const dL = Math.hypot(dxL, dyL);
    if (dL < 1) return null;
    const g1x = first.x - (dxL / dL) * 2 * P.BALL_R;
    const g1y = first.y - (dyL / dL) * 2 * P.BALL_R;
    const distCT = Math.hypot(g1x - cx, g1y - cy);
    if (distCT < 1) return null;
    const cut1 = Math.abs(normalizeAngle(
      Math.atan2(first.y - cy, first.x - cx) - Math.atan2(g2.y - first.y, g2.x - first.x)));
    const cut2 = Math.abs(normalizeAngle(
      Math.atan2(g2.y - first.y, g2.x - first.x) - Math.atan2(pocket.y - target.y, pocket.x - target.x)));
    const c1 = Math.cos(Math.min(cut1, ELO_CUT_CLAMP));
    const c2 = Math.cos(Math.min(cut2, ELO_CUT_CLAMP));
    if (c1 <= 0 || c2 <= 0) return null;
    const A1 = 1 + distCT / (ELO_TWOR * c1);
    return A1 * (1 + dL / (ELO_TWOR * c2));
  }
  let distCT, cut;
  if (type === "banda") {
    /* geometría de espejo EXACTA (no la aproximación de railCandidate:
       su fórmula de intersección desvía el punto de rebote varias uds
       y con la tolerancia ±1 rechaza geometrías válidas — defecto
       latente reportado, fuera de alcance corregirlo ahí) */
    const { BX0, BX1, BY0, BY1 } = GEO;
    const rails = [
      { horiz: true, v: BY0 }, { horiz: true, v: BY1 },
      { horiz: false, v: BX0 }, { horiz: false, v: BX1 }
    ];
    let found = null;
    for (const r of rails) {
      const rx = r.horiz ? g2.x : 2 * r.v - g2.x;
      const ry = r.horiz ? 2 * r.v - g2.y : g2.y;
      const dx = rx - cx, dy = ry - cy;
      const s = r.horiz
        ? (Math.abs(dy) < 1e-9 ? NaN : (r.v - cy) / dy)
        : (Math.abs(dx) < 1e-9 ? NaN : (r.v - cx) / dx);
      if (!(s > 0.05 && s < 0.95)) continue;
      const hitX = cx + dx * s, hitY = cy + dy * s;
      if (hitX < BX0 - 1 || hitX > BX1 + 1 || hitY < BY0 - 1 || hitY > BY1 + 1) continue;
      const d = Math.hypot(hitX - cx, hitY - cy) + Math.hypot(g2.x - hitX, g2.y - hitY);
      const c = Math.abs(normalizeAngle(
        Math.atan2(g2.y - hitY, g2.x - hitX) - Math.atan2(pocket.y - target.y, pocket.x - target.x)));
      if (c > 1.35) continue;
      found = { distCT: d, cut: c };
      break;
    }
    if (!found) return null;
    distCT = found.distCT; cut = found.cut;
  } else {
    /* directa: A = 1 + distCT / (2R·cos θ) — como shotElo */
    distCT = Math.hypot(g2.x - cx, g2.y - cy);
    if (distCT < 1) return null;
    const cosCut = ((g2.x - cx) * g2.ux + (g2.y - cy) * g2.uy) / distCT;
    if (cosCut <= 0) return null;
    cut = Math.acos(Math.max(-1, Math.min(1, cosCut)));
  }
  const cosc = Math.cos(Math.min(cut, ELO_CUT_CLAMP));
  if (cosc <= 0) return null;
  return 1 + distCT / (ELO_TWOR * cosc);
}

/* ========== v4: medición del tiro del jugador (bisección §12) ==========
   Mide la ventana real del tiro que el jugador ACABA de ejecutar
   (ángulo/potencia registrados en el juego). Cooperativo (~25 ms por
   tajada); onDone({D_meas, sigA, sigP, sims} | null).
   T2: el tipo de tiro NO se recibe ni se supone directo — se INFIERE de
   una simulación sonda sobre el estado pre-tiro:
     · railBefore > 0            → "banda"       (bands = railBefore)
     · firstHit ≠ bola embocada  → "combinacion" (secondaryId = embocada)
     · resto                     → "directa"
   El candRef resultante alimenta scratchSeverity, σ_scratch y el recargo
   de bandas de finishJob con la geometría que EFECTIVAMENTE ocurrió. */
function measureShot(state, params, targetId, pocketId, onDone) {
  try {
    configure(state && state.physics);
    const balls = (state.balls || []).map(b => new Ball(b.id, b.x, b.y, false, !!b.pocketed));
    const cue = balls.find(b => b.id === 0);
    const target = balls.find(b => b.id === targetId);
    const pocket = GEO.pockets.find(p => p.id === pocketId);
    if (!cue || !target || !pocket || !params) { onDone(null); return; }
    const paramsRef = { angle: params.angle, power: Math.max(0.08, Math.min(1, params.power)),
                        english: params.english || 0, follow: params.follow || 0,
                        cuePos: params.cuePos || null };
    /* V3: la sonda B_STAGES[0] corre con estos mismos paramsRef, pero su
       shotState queda enterrado en el bucle de bisección; una simulación
       aparte antes de crear el trabajo es más simple y cuesta ~1/45. */
    const probe = simulateShot(balls, paramsRef);
    const pst = probe.shotState;
    let type, bands, first = null, secondaryId = null;
    if (pst.railBefore > 0) {
      type = "banda"; bands = pst.railBefore;
    } else if (pst.firstHit != null && pst.firstHit !== targetId) {
      type = "combinacion"; bands = 0;
      first = balls.find(b => b.id === pst.firstHit) || null;
      secondaryId = targetId;              // la embocada es la "secundaria"
      if (!first) { onDone(null); return; }
    } else {
      type = "directa"; bands = 0;
    }
    let cand = null;
    if (type === "banda") {
      cand = railCandidate(cue.x, cue.y, target, pocket, balls);
    } else if (type === "combinacion") {
      cand = comboCandidate(cue.x, cue.y, first, target, pocket, balls);
    } else {
      cand = directCandidate(cue.x, cue.y, target, pocket, balls) ||
             directCandidate(cue.x, cue.y, target, pocket, [cue, target]);
    }
    let A = cand ? (cand.A ?? null) : null;
    if (A == null || !isFinite(A)) {
      /* constructor no reconstruyó la geometría: A a mano (misma fórmula
         que shotElo) con el tipo OBSERVADO; si tampoco, no medir */
      A = manualAmp(type, cue.x, cue.y, first, target, pocket);
      if (A == null || !isFinite(A)) { onDone(null); return; }
    }
    const r = {
      candRef: { targetId: first ? first.id : targetId, pocketId,
                 secondaryId, type, A, distCT: cand ? cand.distCT : null },
      bandsObserved: bands,                // T3: recargo según lo observado
      paramsRef,
      targetId, pocketId, cutAngle: cand ? (cand.cutAngle || 0) : 0, score: 0
    };
    const ctx = { balls, mode: state.mode, groups: state.groups,
                  player: state.currentPlayer, simsDone: 0, simsPlanned: BISECT.EST_SIMS,
                  S_BOT: S_BOT, pct: 0 };
    const job = makeBisectJob(r);
    const slice = () => {
      const t0 = performance.now();
      let done = false;
      try {
        while (!done && performance.now() - t0 < 25) done = stepJob(ctx, job);
      } catch (e) { onDone(null); return; }
      if (done) onDone({ D_meas: r.D_meas ?? null, sigA: r.sigA_meas ?? null,
                         sigP: r.sigP_meas ?? null, sims: ctx.simsDone,
                         alphaOpt: r.angle ?? null, distCT: r.candRef ? r.candRef.distCT : null,
                         pOpt: r.power ?? null });
      else setTimeout(slice, 0);
    };
    setTimeout(slice, 0);
  } catch (e) { onDone(null); }
}

/* Única variable pública del archivo */
global.MetaBot = Object.freeze({
  analyze: analyze,
  rateShot: rateShot,
  estimateSkill: estimateSkill,
  measureShot: measureShot,
  potProbQ: potProbQ,          // HUD: conteo de muestras informativas
  AIM_QUANT: PLAYER_AIM_QUANT
});
})(globalThis);
