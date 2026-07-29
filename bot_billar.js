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
const DEADLINE_MS = 15000;          // §4
const RETURN_MARGIN_MS = 300;

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
    if (st && st.contacted) st.railAfter = true;
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
    if (st && st.contacted) st.railAfter = true;
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
  const st = { contacted: false, firstHit: null, railAfter: false,
               pocketed: [], scratch: false };
  const maxSteps = Math.ceil(SIM_TIME_CAP_MS / phys.DT);
  let steps = 0;
  while (steps < maxSteps) {
    let any = false;
    for (const b of balls) if (!b.isJaw && !b.pocketed && b.moving) { any = true; break; }
    if (!any) break;
    simStep(balls, phys.DT, st, phys);
    steps++;
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

/* Bolas activas que invaden el corredor (excluidas las participantes) */
function corridorBlockedByBall(x1, y1, x2, y2, balls, ignoreIds) {
  const clearance = 2 * P.BALL_R + SAFETY_MARGIN;
  for (const b of balls) {
    if (b.pocketed || b.isJaw || ignoreIds.has(b.id)) continue;
    if (segPointDist(x1, y1, x2, y2, b.x, b.y) < clearance) return b;
  }
  return null;
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

/* §2: el recorrido no puede atravesar mandíbulas ni salir del paño
   salvo por la boca de una tronera. Muestreo denso del segmento. */
function corridorRespectsGeometry(x1, y1, x2, y2) {
  const R = P.BALL_R;
  const len = Math.hypot(x2 - x1, y2 - y1);
  const steps = Math.max(2, Math.ceil(len / (R * 0.5)));
  for (let i = 0; i <= steps; i++) {
    const x = x1 + (x2 - x1) * i / steps;
    const y = y1 + (y2 - y1) * i / steps;
    if (!pointInPlayOrMouth(x, y)) return false;
    for (const j of GEO.jaws) {
      /* contacto real: centro a < 2r de la mandíbula (margen −0.8) */
      if (Math.hypot(x - j.x, y - j.y) < 2 * R - 0.8) return false;
    }
  }
  return true;
}

function corridorClear(x1, y1, x2, y2, balls, ignoreIds) {
  if (corridorBlockedByBall(x1, y1, x2, y2, balls, ignoreIds)) return false;
  return corridorRespectsGeometry(x1, y1, x2, y2);
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
  if (!corridorClear(cx, cy, g.x, g.y, balls, ignore)) return null;
  if (!corridorClear(target.x, target.y, pocket.x, pocket.y, balls, new Set([target.id]))) return null;
  return { type, targetId: target.id, pocketId: pocket.id,
           ghostX: g.x, ghostY: g.y,
           angle: Math.atan2(g.y - cy, g.x - cx),
           cutAngle: cut, distCT, distTP: g.distPocket,
           baseScore: baseScore(cut, distCT, g.distPocket, pocket),
           cuePos, pocket, target };
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
  if (!corridorClear(cx, cy, g1.x, g1.y, balls, new Set([0, first.id]))) return null;
  if (!corridorClear(first.x, first.y, g2.x, g2.y, balls, new Set([first.id, target.id]))) return null;
  if (!corridorClear(target.x, target.y, pocket.x, pocket.y, balls, new Set([target.id]))) return null;
  const distCT = Math.hypot(g1.x - cx, g1.y - cy);
  const base = 90 - cut1 * 30 - cut2 * 20 - (distCT / P.TABLE_W) * 20 + 50;
  return { type: "combinacion", targetId: first.id, secondaryId: target.id,
           pocketId: pocket.id, ghostX: g1.x, ghostY: g1.y,
           angle: Math.atan2(g1.y - cy, g1.x - cx),
           cutAngle: cut1 + cut2, distCT, distTP: dL + g2.distPocket,
           baseScore: base, cuePos: null, pocket, target: first };
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
    if (!corridorClear(cx, cy, hitX, hitY, balls, ignore)) continue;
    if (!corridorClear(hitX, hitY, g.x, g.y, balls, ignore)) continue;
    if (!corridorClear(target.x, target.y, pocket.x, pocket.y, balls, new Set([target.id]))) continue;
    const distCT = Math.hypot(hitX - cx, hitY - cy) + Math.hypot(g.x - hitX, g.y - hitY);
    const cut = Math.abs(normalizeAngle(
      Math.atan2(g.y - hitY, g.x - hitX) - Math.atan2(pocket.y - target.y, pocket.x - target.x)));
    if (cut > 1.35) continue;
    const base = baseScore(cut, distCT, g.distPocket, pocket) - 18;   // banda cuesta
    const cand = { type: "banda", targetId: target.id, pocketId: pocket.id,
      ghostX: g.x, ghostY: g.y, railX: hitX, railY: hitY,
      angle: Math.atan2(hitY - cy, hitX - cx),
      cutAngle: cut, distCT, distTP: g.distPocket, baseScore: base,
      cuePos: null, pocket, target };
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
  out.sort((a, b) => b.baseScore - a.baseScore ||
                     a.targetId - b.targetId ||
                     (a.pocketId < b.pocketId ? -1 : 1));
  return out.slice(0, 30);
}

/* ========== §5 PUNTUACIÓN POR PRIORIDADES ESTRICTAS ==========
   1 evitar derrota · 2 victoria legal · 3 evitar falta/suicidio ·
   4 embocar objetivo · 5 mantener turno · 6 tiro visible ·
   7 distancia siguiente · 8 no regalar al rival · 9 robustez.
   Una falta NUNCA se compensa con bolas embocadas. */
const W = { SUCCESS: 300, LEGAL: 400, SCRATCH: 500, CUT: 60, POS_RISK: 80 };

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

function cuePocketRisk(cx, cy) {
  let d = Infinity;
  for (const pk of GEO.pockets) d = Math.min(d, Math.hypot(cx - pk.x, cy - pk.y));
  return d < 70 ? (70 - d) / 70 : 0;
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
function powersFor(distCT, type) {
  if (type === "defensa") return distCT > 250 ? [0.55, 0.72] : [0.42];
  if (distCT < 150) return [0.35, 0.55];
  if (distCT < 350) return [0.5, 0.7];
  return [0.65, 0.85];
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
  const ctx = {
    t0: performance.now(), deadline: DEADLINE_MS - RETURN_MARGIN_MS,
    state, difficulty, balls, cue,
    mode: state.mode, groups: state.groups, player: state.currentPlayer,
    ballInHand: !!state.ballInHand,
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
    perSpot.sort((a, b) => b.best.baseScore - a.best.baseScore);
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
    cands.sort((a, b) => b.baseScore - a.baseScore);
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
    for (const pwr of powersFor(cand.distCT || 200, cand.type))
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

function runL4(ctx) {
  /* §4 robustez: 3 finalistas × perturbaciones deterministas fijas */
  const top = sortResults(legalPool(ctx).slice()).slice(0, 3);
  const pert = [
    { da: 0.008 }, { da: -0.008 }, { da: 0.004 }, { da: -0.004 },
    { dp: 0.04 }, { dp: -0.04 }, { dp: 0.02 }, { dp: -0.02 },
    { fr: 1.005 }, { fr: 0.995 }, { re: 1.02 }, { re: 0.98 }
  ];
  for (const r of top) {
    const samples = [];
    for (const p of pert) {
      const phys = (p.fr || p.re) ? { ...P,
        ROLL_FRICTION: Math.min(0.9999, P.ROLL_FRICTION * (p.fr || 1)),
        CUSHION_REST: P.CUSHION_REST * (p.re || 1),
        BALL_REST: P.BALL_REST * (p.re || 1) } : P;
      samples.push({ params: { ...r.paramsRef,
          angle: r.paramsRef.angle + (p.da || 0),
          power: Math.max(0.08, Math.min(1, r.paramsRef.power + (p.dp || 0))) },
        phys, candRef: r.candRef });
    }
    ctx.queue.push({ robustFor: r, samples });
  }
  ctx.simsPlanned += top.length * 12;
  ctx.phase = "L4";
  ctx.pct = 85;
}

function runOneRobust(ctx) {
  const job = ctx.queue.shift();
  if (!job) return;
  const r = job.robustFor;
  let success = 0, legal = 0, scratch = 0;
  const potId = r.secondaryId || r.targetId;
  for (const s of job.samples) {
    if (expired(ctx)) break;
    const sim = simulateShot(ctx.balls, s.params, s.phys);
    ctx.simsDone++;
    const sc = scoreSim(sim, s.candRef, ctx.mode, ctx.groups, ctx.player, ctx.balls);
    if (!sc.foul) legal++;
    if (sc.scratch) scratch++;
    if (!sc.foul && potId !== null && sc.pocketed.includes(potId)) success++;
    if (sc.win) { success++; legal++; }
  }
  const n = job.samples.length;
  r.successRate = success / n;
  r.legalRate = legal / n;
  r.scratchRate = scratch / n;
  /* §5: robustez dentro de la misma categoría */
  r.score += r.successRate * W.SUCCESS + r.legalRate * W.LEGAL -
             r.scratchRate * W.SCRATCH - (r.cutAngle || 0) / (Math.PI / 2) * W.CUT -
             cuePocketRisk(r.cueFinal.x, r.cueFinal.y) * W.POS_RISK;
  const frac = ctx.simsPlanned ? ctx.simsDone / ctx.simsPlanned : 1;
  ctx.pct = Math.min(98, 85 + 13 * frac);
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
    if (ctx.phase === "L4") runOneRobust(ctx); else runOneSim(ctx);
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
    r.candRef = { targetId: r.targetId, pocketId: r.pocketId,
                  secondaryId: r.secondaryId, kick: r.kick || false,
                  type: r.candidateType, baseScore: r.baseScore,
                  cutAngle: r.cutAngle, distCT: r.distCT, distTP: r.distTP };
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
  /* Ruido por dificultad: NUNCA en hard (§7 determinismo) */
  let angle = best.angle, power = best.power;
  if (ctx.difficulty === "easy") {
    angle += (Math.random() - 0.5) * 0.06;
    power = Math.max(0.15, Math.min(1, power + (Math.random() - 0.5) * 0.2));
  } else if (ctx.difficulty === "medium") {
    angle += (Math.random() - 0.5) * 0.02;
  }
  const calculationTimeMs = Math.round(elapsed(ctx));
  const shot = {
    angle, power,
    english: best.english || 0, follow: best.follow || 0,
    targetId: best.targetId, pocketId: best.pocketId,
    secondaryId: best.secondaryId || null,
    cuePlacement: best.paramsRef ? best.paramsRef.cuePos : (best.cuePos || null),
    candidateType: best.candidateType,
    kick: !!best.kick,
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
      ` · éxito ${best.successRate != null ? (best.successRate * 100).toFixed(0) + "%" : "s/d"}` +
      ` · ${ctx.simsDone} sims · ${calculationTimeMs} ms`
  };
  const top = pool.slice(0, 5).map(r => ({
    angle: r.angle, power: r.power, targetId: r.targetId, pocketId: r.pocketId,
    candidateType: r.candidateType, score: Math.round(r.score)
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

/* Única variable pública del archivo */
global.MetaBot = Object.freeze({
  analyze: analyze
});
})(globalThis);
