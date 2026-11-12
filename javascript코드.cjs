#!/usr/bin/env node

'use strict';

let _s = 1;
function setSeed(seed){ _s = (seed >>> 0) || 1; }
function rnd(){
  _s = (_s + 0x6D2B79F5) | 0;
  let t = Math.imul(_s ^ (_s >>> 15), 1 | _s);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
}
function randn(){
  let u = 0, v = 0;
  while(u === 0) u = rnd();
  while(v === 0) v = rnd();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
}
function shuffle(a){
  for(let i = a.length - 1; i > 0; i--){
    const j = (rnd() * (i + 1)) | 0;
    const t = a[i]; a[i] = a[j]; a[j] = t;
  }
  return a;
}
function clamp(v, lo, hi){ return Math.max(lo, Math.min(hi, v)); }

const OVL_EPS   = 1e-9;
const AREA_TOL  = 1e-12;
const H_INFLATE = 1e-9;

function squareCorners(sq){
  const c = Math.cos(sq.theta), s = Math.sin(sq.theta);
  return [
    {x: sq.x - 0.5*c + 0.5*s, y: sq.y - 0.5*s - 0.5*c},
    {x: sq.x + 0.5*c + 0.5*s, y: sq.y + 0.5*s - 0.5*c},
    {x: sq.x + 0.5*c - 0.5*s, y: sq.y + 0.5*s + 0.5*c},
    {x: sq.x - 0.5*c - 0.5*s, y: sq.y - 0.5*s + 0.5*c}
  ];
}

function overlapPenetration(sqA, sqB){

  const dx = sqA.x - sqB.x, dy = sqA.y - sqB.y;
  if(dx*dx + dy*dy > 2.0000001) return 0;
  const A = squareCorners(sqA), B = squareCorners(sqB);
  const axes = [
    {x: Math.cos(sqA.theta), y: Math.sin(sqA.theta)},
    {x:-Math.sin(sqA.theta), y: Math.cos(sqA.theta)},
    {x: Math.cos(sqB.theta), y: Math.sin(sqB.theta)},
    {x:-Math.sin(sqB.theta), y: Math.cos(sqB.theta)}
  ];
  let minOverlap = Infinity;
  for(let k = 0; k < 4; k++){
    const ax = axes[k];
    let aMin = Infinity, aMax = -Infinity, bMin = Infinity, bMax = -Infinity;
    for(let i = 0; i < 4; i++){
      let d = A[i].x*ax.x + A[i].y*ax.y;
      if(d < aMin) aMin = d; if(d > aMax) aMax = d;
      d = B[i].x*ax.x + B[i].y*ax.y;
      if(d < bMin) bMin = d; if(d > bMax) bMax = d;
    }
    const ov = Math.min(aMax, bMax) - Math.max(aMin, bMin);
    if(ov <= 0) return 0;
    if(ov < minOverlap) minOverlap = ov;
  }
  return minOverlap;
}

function containViolation(tri, sq){
  const bx = tri.bx, cx = tri.cx, cy = tri.cy;
  const sgn = (bx*cy) >= 0 ? 1 : -1;
  const corners = squareCorners(sq);
  const ex = [bx, cx-bx, -cx], ey = [0, cy, -cy];
  const ax = [0, bx, cx],      ay = [0, 0, cy];
  let viol = 0;
  for(let p = 0; p < 4; p++){
    const px = corners[p].x, py = corners[p].y;
    for(let i = 0; i < 3; i++){
      const cross = ex[i]*(py-ay[i]) - ey[i]*(px-ax[i]);
      const len = Math.hypot(ex[i], ey[i]) || 1e-9;
      const dist = (cross/len)*sgn;
      if(dist < 0) viol += -dist;
    }
  }
  return viol;
}

function overlapTotal(squares){
  let s = 0;
  for(let i = 0; i < squares.length; i++)
    for(let j = i+1; j < squares.length; j++)
      s += overlapPenetration(squares[i], squares[j]);
  return s;
}
function overlapOf(squares, idx){
  let s = 0;
  for(let j = 0; j < squares.length; j++){
    if(j === idx) continue;
    s += overlapPenetration(squares[idx], squares[j]);
  }
  return s;
}

function collectCorners(squares, out){
  out.length = 0;
  for(let i = 0; i < squares.length; i++){
    const cs = squareCorners(squares[i]);
    out.push(cs[0], cs[1], cs[2], cs[3]);
  }
  return out;
}

function supportTri(pts, phi, inflate){
  const inf = inflate || 0;
  const nx = [Math.cos(phi[0]), Math.cos(phi[1]), Math.cos(phi[2])];
  const ny = [Math.sin(phi[0]), Math.sin(phi[1]), Math.sin(phi[2])];
  const h = [-Infinity, -Infinity, -Infinity];
  for(let p = 0; p < pts.length; p++){
    const x = pts[p].x, y = pts[p].y;
    for(let i = 0; i < 3; i++){
      const d = x*nx[i] + y*ny[i];
      if(d > h[i]) h[i] = d;
    }
  }
  h[0] += inf; h[1] += inf; h[2] += inf;
  const verts = new Array(3);
  for(let i = 0; i < 3; i++){
    const j = (i+1) % 3;
    const det = nx[i]*ny[j] - ny[i]*nx[j];
    if(Math.abs(det) < 1e-12) return null;
    verts[i] = {
      x: (h[i]*ny[j] - h[j]*ny[i]) / det,
      y: (nx[i]*h[j] - nx[j]*h[i]) / det
    };
  }

  for(let i = 0; i < 3; i++){
    const k = (i+2) % 3;
    const v = verts[i];
    if(v.x*nx[k] + v.y*ny[k] > h[k] + 1e-7) return null;
  }
  const area = 0.5*Math.abs(
    (verts[1].x-verts[0].x)*(verts[2].y-verts[0].y) -
    (verts[1].y-verts[0].y)*(verts[2].x-verts[0].x)
  );
  if(!(area > 1e-9) || !isFinite(area)) return null;
  return { area, verts };
}

function phiFromTri(tri){
  const A = {x:0,y:0}, B = {x:tri.bx,y:0}, C = {x:tri.cx,y:tri.cy};
  const edges = [[A,B,C],[B,C,A],[C,A,B]];
  const phi = [];
  for(const [P,Q,R] of edges){
    let nxv = Q.y-P.y, nyv = -(Q.x-P.x);
    if(nxv*(R.x-P.x) + nyv*(R.y-P.y) > 0){ nxv = -nxv; nyv = -nyv; }
    phi.push(Math.atan2(nyv, nxv));
  }
  return phi;
}

function angleDescent(pts, phi, maxSweeps){
  let st = supportTri(pts, phi);
  if(!st) return Infinity;
  let bestArea = st.area;
  let step = 0.2, sweeps = 0;
  const cap = maxSweeps || 120;
  while(step > 2e-7 && sweeps < cap){
    let improved = false;
    for(let i = 0; i < 3; i++){
      const orig = phi[i];
      for(const cand of [orig+step, orig-step]){
        phi[i] = cand;
        const t = supportTri(pts, phi);
        if(t && t.area < bestArea - AREA_TOL){
          bestArea = t.area; improved = true;
          break;
        }
        phi[i] = orig;
      }
    }
    if(!improved) step *= 0.5;
    sweeps++;
  }
  return bestArea;
}

function canonicalRecord(squares, phi){
  const pts = collectCorners(squares, []);
  const st = supportTri(pts, phi, H_INFLATE);
  if(!st) return null;
  let [v0, v1, v2] = st.verts;
  const cross = (v1.x-v0.x)*(v2.y-v0.y) - (v1.y-v0.y)*(v2.x-v0.x);
  if(cross < 0){ const t = v1; v1 = v2; v2 = t; }
  const alpha = Math.atan2(v1.y-v0.y, v1.x-v0.x);
  const ca = Math.cos(alpha), sa = Math.sin(alpha);
  const map = (p)=>({
    x:  (p.x-v0.x)*ca + (p.y-v0.y)*sa,
    y: -(p.x-v0.x)*sa + (p.y-v0.y)*ca
  });
  const B = map(v1), C = map(v2);
  const tri = { bx: B.x, cx: C.x, cy: C.y };
  const sqs = squares.map(s=>{
    const m = map({x: s.x, y: s.y});
    return { x: m.x, y: m.y, theta: s.theta - alpha };
  });
  return { area: 0.5*Math.abs(tri.bx*tri.cy), tri, squares: sqs };
}

function makeEngine(n){
  const contain = new Float64Array(n);
  const ovl = new Float64Array(n*n);
  const uContain = new Float64Array(n);
  const uOvlRow  = new Float64Array(n);
  const uOvlAll  = new Float64Array(n*n);
  const uX = new Float64Array(n), uY = new Float64Array(n);

  const eng = {
    st: null, containSum: 0, overlapSum: 0, area: 0,

    attach(st){ this.st = st; this.recomputeAll(); },
    recomputeAll(){
      const st = this.st, sqs = st.squares;
      let cs = 0, os = 0;
      for(let i = 0; i < n; i++){
        contain[i] = containViolation(st.tri, sqs[i]);
        cs += contain[i];
      }
      ovl.fill(0);
      for(let i = 0; i < n; i++)
        for(let j = i+1; j < n; j++){
          const v = overlapPenetration(sqs[i], sqs[j]);
          ovl[i*n+j] = ovl[j*n+i] = v;
          os += v;
        }
      this.containSum = cs;
      this.overlapSum = os;
      this.area = 0.5*Math.abs(st.tri.bx*st.tri.cy);
    },

    saStep(T, T0){
      const st = this.st, sqs = st.squares;
      const frac = clamp(T/T0, 0, 1);
      const K = 30 + 600*(1-frac);
      const before = this.area + K*(this.containSum + this.overlapSum);
      const posSigma = 0.03 + 0.5*frac;
      const rotSigma = 0.03 + 0.7*frac;
      const triSigma = 0.03 + 0.6*frac;
      const moveType = rnd();
      let kind, idx = -1, sx=0, sy=0, sth=0, sbx=0, scx=0, scy=0;
      const savedCS = this.containSum, savedOS = this.overlapSum, savedArea = this.area;

      if(moveType < 0.55 && n > 0){
        kind = 0;
        idx = (rnd()*n) | 0;
        const sq = sqs[idx];
        sx = sq.x; sy = sq.y; sth = sq.theta;
        uContain[0] = contain[idx];
        for(let j = 0; j < n; j++) uOvlRow[j] = ovl[idx*n+j];
        sq.x += randn()*posSigma;
        sq.y += randn()*posSigma;
        sq.theta += randn()*rotSigma;
        const nc = containViolation(st.tri, sq);
        this.containSum += nc - contain[idx];
        contain[idx] = nc;
        for(let j = 0; j < n; j++){
          if(j === idx) continue;
          const v = overlapPenetration(sq, sqs[j]);
          this.overlapSum += v - ovl[idx*n+j];
          ovl[idx*n+j] = ovl[j*n+idx] = v;
        }
      } else if(moveType < 0.82){
        kind = 1;
        sbx = st.tri.bx; scx = st.tri.cx; scy = st.tri.cy;
        for(let i = 0; i < n; i++) uContain[i] = contain[i];
        const which = (rnd()*3) | 0;
        if(which === 0) st.tri.bx += randn()*triSigma;
        else if(which === 1) st.tri.cx += randn()*triSigma;
        else st.tri.cy += randn()*triSigma;
        st.tri.bx = Math.max(st.tri.bx, 0.2);
        st.tri.cy = Math.max(st.tri.cy, 0.2);
        let cs = 0;
        for(let i = 0; i < n; i++){
          contain[i] = containViolation(st.tri, sqs[i]);
          cs += contain[i];
        }
        this.containSum = cs;
        this.area = 0.5*Math.abs(st.tri.bx*st.tri.cy);
      } else {
        kind = 2;
        sbx = st.tri.bx; scx = st.tri.cx; scy = st.tri.cy;
        for(let i = 0; i < n; i++){ uX[i] = sqs[i].x; uY[i] = sqs[i].y; uContain[i] = contain[i]; }
        uOvlAll.set(ovl);
        const factor = 1 - (0.005 + 0.03*rnd())*(0.2+frac);
        st.tri.bx *= factor; st.tri.cx *= factor; st.tri.cy *= factor;
        for(let i = 0; i < n; i++){ sqs[i].x *= factor; sqs[i].y *= factor; }
        this.recomputeAll();
      }

      const after = this.area + K*(this.containSum + this.overlapSum);
      const delta = after - before;
      const Teff = Math.max(T, 0.0015);
      if(delta <= 0 || rnd() < Math.exp(-delta/Teff)) return;

      this.containSum = savedCS; this.overlapSum = savedOS; this.area = savedArea;
      if(kind === 0){
        const sq = sqs[idx];
        sq.x = sx; sq.y = sy; sq.theta = sth;
        contain[idx] = uContain[0];
        for(let j = 0; j < n; j++){ ovl[idx*n+j] = uOvlRow[j]; ovl[j*n+idx] = uOvlRow[j]; }
      } else if(kind === 1){
        st.tri.bx = sbx; st.tri.cx = scx; st.tri.cy = scy;
        for(let i = 0; i < n; i++) contain[i] = uContain[i];
      } else {
        st.tri.bx = sbx; st.tri.cx = scx; st.tri.cy = scy;
        for(let i = 0; i < n; i++){ sqs[i].x = uX[i]; sqs[i].y = uY[i]; contain[i] = uContain[i]; }
        ovl.set(uOvlAll);
      }
    }
  };
  return eng;
}

function initState(n, variant){

  const k = Math.ceil(Math.sqrt(n));
  const squares = [];
  if(variant === 1){

    const m = Math.ceil((Math.sqrt(8*n+1)-1)/2);
    let placed = 0, row = 0;
    while(placed < n){
      const rowLen = Math.max(1, m - row);
      for(let col = 0; col < rowLen && placed < n; col++){
        squares.push({x: 0.5 + col*1.001, y: 0.5 + row*1.001, theta: 0});
        placed++;
      }
      row++;
    }
    return { tri: {bx: (k+2)*2, cx: 0.2, cy: (k+2)*2}, squares };
  }
  if(variant === 2){
    for(let i = 0; i < n; i++) squares.push({x: 0.5 + i*1.001, y: 0.5, theta: 0});
    return { tri: {bx: (n+2)*1.6, cx: (n+2)*0.8, cy: 3.2}, squares };
  }
  const jitterScale = variant === 0 ? 0 : 0.45;
  const aspect = variant === 0 ? 1 : (0.5 + rnd()*1.6);
  const baseSize = (k+1.6);
  const bx = baseSize*1.5*Math.sqrt(aspect);
  const cy = baseSize*1.5/Math.sqrt(aspect);
  const cx = bx/2 + (variant === 0 ? 0 : (rnd()-0.5)*baseSize*0.7);
  const globalRot = variant === 0 ? 0 : (rnd()-0.5)*1.0;
  let placed = 0;
  for(let row = 0; row < k && placed < n; row++){
    for(let col = 0; col < k && placed < n; col++){
      const x = 0.8 + col*1.15 + (rnd()-0.5)*jitterScale;
      const y = 0.8 + row*1.15 + (rnd()-0.5)*jitterScale;
      squares.push({x, y, theta: globalRot + (rnd()-0.5)*jitterScale*0.5});
      placed++;
    }
  }
  return { tri: {bx, cx, cy}, squares };
}

function kickFrom(최고){
  const st = { tri: {bx: best.tri.bx, cx: best.tri.cx, cy: best.tri.cy},
               squares: best.squares.map(s=>({x: s.x, y: s.y, theta: s.theta})) };
  const n = st.squares.length;
  const kickCount = Math.max(1, Math.round(n*(0.2+0.5*rnd())));
  const idxs = shuffle([...Array(n).keys()]).slice(0, kickCount);
  for(const idx of idxs){
    st.squares[idx].x += randn()*0.35;
    st.squares[idx].y += randn()*0.35;
    st.squares[idx].theta += randn()*0.5;
  }
  if(rnd() < 0.5){
    st.tri.bx *= (1+randn()*0.04);
    st.tri.cx += randn()*0.15;
    st.tri.cy *= (1+randn()*0.04);
    st.tri.bx = Math.max(st.tri.bx, 0.2);
    st.tri.cy = Math.max(st.tri.cy, 0.2);
  }
  return st;
}

function repairSweep(squares, step){
  let improved = false;
  const n = squares.length;
  for(let i = 0; i < n; i++){
    const sq = squares[i];
    let cur = overlapOf(squares, i);
    if(cur <= 0) continue;
    for(const v of ['x','y','theta']){
      const orig = sq[v];
      let bestVal = orig, bestOvl = cur;
      const s = (v === 'theta') ? step*1.4 : step;
      for(const cand of [orig+s, orig-s]){
        sq[v] = cand;
        const o = overlapOf(squares, i);
        if(o < bestOvl - 1e-13){ bestOvl = o; bestVal = cand; }
      }
      sq[v] = bestVal;
      if(bestOvl < cur - 1e-13){ improved = true; cur = bestOvl; }
    }
  }
  return improved;
}
function repair(squares, maxSweeps){
  let step = 0.06;
  for(let s = 0; s < maxSweeps; s++){
    if(overlapTotal(squares) <= OVL_EPS) return true;
    const improved = repairSweep(squares, step);
    if(!improved) step *= 0.6;
    if(step < 1e-6) break;
  }
  return overlapTotal(squares) <= OVL_EPS;
}

function tightenState(squares, phiSeed){
  const pts = collectCorners(squares, []);
  const phi = phiSeed.slice();
  angleDescent(pts, phi, 60);
  return { squares, phi, ptsBuf: pts };
}
function tightenArea(ts){
  collectCorners(ts.squares, ts.ptsBuf);
  const t = supportTri(ts.ptsBuf, ts.phi);
  return t ? t.area : Infinity;
}
function tightenSweep(ts, step){
  let improved = false;
  let curArea = tightenArea(ts);
  const n = ts.squares.length;

  for(let i = 0; i < 3; i++){
    const orig = ts.phi[i];
    let bestVal = orig, bestArea = curArea;
    for(const cand of [orig+step, orig-step]){
      ts.phi[i] = cand;
      const a = tightenArea(ts);
      if(a < bestArea - AREA_TOL){ bestArea = a; bestVal = cand; }
    }
    ts.phi[i] = bestVal;
    if(bestArea < curArea - AREA_TOL){ improved = true; curArea = bestArea; }
  }

  for(let i = 0; i < n; i++){
    const sq = ts.squares[i];
    for(const v of ['x','y','theta']){
      const orig = sq[v];
      let bestVal = orig, bestArea = curArea;
      const s = (v === 'theta') ? step*1.3 : step;
      for(const cand of [orig+s, orig-s]){
        sq[v] = cand;
        if(overlapOf(ts.squares, i) <= OVL_EPS){
          const a = tightenArea(ts);
          if(a < bestArea - AREA_TOL){ bestArea = a; bestVal = cand; }
        }
      }
      sq[v] = bestVal;
      if(bestArea < curArea - AREA_TOL){ improved = true; curArea = bestArea; }
    }
  }

  if(n >= 2){
    let cx0 = 0, cy0 = 0;
    for(const sq of ts.squares){ cx0 += sq.x; cy0 += sq.y; }
    cx0 /= n; cy0 /= n;
    for(const [mx, my] of [[1,1],[1,0],[0,1]]){
      for(const f of [1-step*0.5, 1+step*0.5]){
        const sx = new Array(n), sy = new Array(n);
        for(let i = 0; i < n; i++){
          sx[i] = ts.squares[i].x; sy[i] = ts.squares[i].y;
          if(mx) ts.squares[i].x = cx0 + f*(sx[i]-cx0);
          if(my) ts.squares[i].y = cy0 + f*(sy[i]-cy0);
        }
        const ok = overlapTotal(ts.squares) <= OVL_EPS;
        const a = ok ? tightenArea(ts) : Infinity;
        if(ok && a < curArea - AREA_TOL){
          improved = true; curArea = a;
        } else {
          for(let i = 0; i < n; i++){ ts.squares[i].x = sx[i]; ts.squares[i].y = sy[i]; }
        }
      }
    }
  }

  {
    const nv = 3 + 3*n;
    const dir = new Array(nv), saved = new Array(nv);
    const getV = (i)=> i < 3 ? ts.phi[i]
                 : ((i-3)%3 === 0 ? ts.squares[(i-3)/3|0].x
                 :  (i-3)%3 === 1 ? ts.squares[(i-3)/3|0].y
                 :  ts.squares[(i-3)/3|0].theta);
    const setV = (i,v)=>{ if(i < 3) ts.phi[i] = v;
      else { const s = ts.squares[(i-3)/3|0], k = (i-3)%3;
             if(k === 0) s.x = v; else if(k === 1) s.y = v; else s.theta = v; } };
    for(let probe = 0; probe < 4; probe++){
      let norm = 0;
      for(let i = 0; i < nv; i++){ dir[i] = randn(); norm += dir[i]*dir[i]; }
      norm = Math.sqrt(norm) || 1;
      for(let i = 0; i < nv; i++){ dir[i] /= norm; saved[i] = getV(i); }
      for(const sgn of [1,-1]){
        for(let i = 0; i < nv; i++) setV(i, saved[i] + sgn*step*dir[i]);
        if(overlapTotal(ts.squares) <= OVL_EPS){
          const a = tightenArea(ts);
          if(a < curArea - AREA_TOL){ improved = true; curArea = a; break; }
        }
        for(let i = 0; i < nv; i++) setV(i, saved[i]);
      }
    }
  }
  return improved;
}

function currentTemperature(saIter, curIters, curCycles, curT0){
  const cycleLen = curIters / curCycles;
  const cycleIdx = Math.floor(saIter / cycleLen);
  const withinCycle = (saIter % cycleLen) / cycleLen;
  const Tend = 0.0006;
  const peak = curT0 * Math.pow(0.55, cycleIdx);
  return Math.max(peak * Math.pow(Tend/curT0, withinCycle), Tend);
}

function searchMinTriangle(n, opts){
  opts = opts || {};
  const scale = opts.scale || 1;
  const log = opts.log || (()=>{});
  const diversifyRestarts = opts.diversifyRestarts ?? (n<=3?14 : n<=6?9 : n<=12?6 : 8);
  const itersPerDiversify = Math.round(clamp(Math.round(2000000/Math.max(n,1)), 45000, 900000)*scale);
  const intensifyKicks   = opts.intensifyKicks ?? (n<=3?20 : n<=6?14 : n<=12?10 : 14);
  const itersPerKick     = Math.round(clamp(Math.round(600000/Math.max(n,1)), 25000, 300000)*scale);
  const maxTightenSweeps = opts.maxTightenSweeps ?? 260;

  const eng = makeEngine(n);
  let globalBest = opts.seedBest ? {
    area: opts.seedBest.area,
    tri: {...opts.seedBest.tri},
    squares: opts.seedBest.squares.map(s=>({...s}))
  } : null;

  function tryRecord(squares, phiSeed){

    if(overlapTotal(squares) > OVL_EPS) return false;
    const pts = collectCorners(squares, []);
    const phi = phiSeed.slice();
    const area = angleDescent(pts, phi, 90);
    if(!isFinite(area)) return false;
    if(!globalBest || area < globalBest.area - AREA_TOL){
      const rec = canonicalRecord(squares, phi);
      if(rec && (!globalBest || rec.area < globalBest.area)){
        globalBest = rec;
        return true;
      }
    }
    return false;
  }

  function runStage(st, curT0, curCycles, curIters, finalStage){
    if(!finalStage) tryRecord(st.squares, phiFromTri(st.tri));
    eng.attach(st);
    for(let it = 0; it < curIters; it++){
      eng.saStep(currentTemperature(it, curIters, curCycles, curT0), curT0);
      if((it+1) % 700 === 0 && eng.overlapSum <= OVL_EPS)
        tryRecord(st.squares, phiFromTri(st.tri));
    }

    let ok = overlapTotal(st.squares) <= OVL_EPS;
    for(let c = 0; c < 8 && !ok; c++) ok = repair(st.squares, 12);
    if(!ok) return;
    const ts = tightenState(st.squares, phiFromTri(st.tri));
    let step = 0.08, sweeps = 0;
    const minStep = finalStage ? 2e-8 : 1e-7;
    const maxSw   = finalStage ? maxTightenSweeps*2 : maxTightenSweeps;
    while(step >= minStep && sweeps < maxSw){
      if(!tightenSweep(ts, step)) step *= 0.55;
      sweeps++;
      if(sweeps % 40 === 0) tryRecord(ts.squares, ts.phi);
    }
    tryRecord(ts.squares, ts.phi);
  }

  for(let k = 0; k < diversifyRestarts; k++){
    const st = (k === 0 && globalBest)
      ? { tri: {...globalBest.tri}, squares: globalBest.squares.map(s=>({...s})) }
      : initState(n, k);
    runStage(st, 0.5, 4, itersPerDiversify, false);
    log(`다양화 ${k+1}/${diversifyRestarts}` + (globalBest ? ` — 현재 최고 ${globalBest.area.toFixed(6)}` : ' — 유효 배치 없음'));
  }

  for(let k = 0; k < intensifyKicks; k++){
    const st = globalBest ? kickFrom(globalBest) : initState(n, k);
    runStage(st, 0.18, 2, itersPerKick, false);
    log(`집중화 ${k+1}/${intensifyKicks}` + (globalBest ? ` — 현재 최고 ${globalBest.area.toFixed(6)}` : ' — 유효 배치 없음'));
  }

  if(globalBest){
    const st = { tri: {...globalBest.tri}, squares: globalBest.squares.map(s=>({...s})) };
    runStage(st, 0, 1, 0, true);
    log(`최종 정밀화 — 최종 ${globalBest.area.toFixed(9)}`);
  }
  return globalBest;
}

function validate(rec){
  let maxPen = 0;
  for(let i = 0; i < rec.squares.length; i++)
    for(let j = i+1; j < rec.squares.length; j++)
      maxPen = Math.max(maxPen, overlapPenetration(rec.squares[i], rec.squares[j]));
  let maxViol = 0;
  for(const sq of rec.squares)
    maxViol = Math.max(maxViol, containViolation(rec.tri, sq));
  const areaErr = Math.abs(rec.area - 0.5*Math.abs(rec.tri.bx*rec.tri.cy));
  return { maxPen, maxViol, areaErr };
}

function toSVG(rec, sizePx){
  const S = sizePx || 480, pad = 24;
  const tri = rec.tri;
  const V = [{x:0,y:0},{x:tri.bx,y:0},{x:tri.cx,y:tri.cy}];
  let minX = Math.min(0, tri.bx, tri.cx), maxX = Math.max(0, tri.bx, tri.cx);
  let minY = Math.min(0, tri.cy),         maxY = Math.max(0, tri.cy);
  for(const sq of rec.squares)
    for(const c of squareCorners(sq)){
      minX = Math.min(minX, c.x); maxX = Math.max(maxX, c.x);
      minY = Math.min(minY, c.y); maxY = Math.max(maxY, c.y);
    }
  const spanX = maxX-minX, spanY = maxY-minY;
  const sc = Math.min((S-2*pad)/spanX, (S-2*pad)/spanY);
  const tx = (p)=> (pad + (p.x-minX)*sc).toFixed(2);
  const ty = (p)=> (S - pad - (p.y-minY)*sc).toFixed(2);
  const poly = (pts)=> pts.map(p=>`${tx(p)},${ty(p)}`).join(' ');
  let out = `<svg xmlns="http://www.w3.org/2000/svg" width="${S}" height="${S}" viewBox="0 0 ${S} ${S}">\n`;
  out += `<rect width="${S}" height="${S}" fill="white"/>\n`;
  out += `<polygon points="${poly(V)}" fill="none" stroke="black" stroke-width="1.6"/>\n`;
  for(const sq of rec.squares)
    out += `<polygon points="${poly(squareCorners(sq))}" fill="#e5e5e5" stroke="#333" stroke-width="1"/>\n`;
  out += `</svg>\n`;
  return out;
}

function main(){
  const fs = require('fs');
  const args = process.argv.slice(2);
  const n = parseInt(args[0]);
  if(!(n >= 1)){
    console.error('사용법: node min_triangle.js <n> [--seed S] [--scale F] [--svg 파일] [--json 파일] [--resume 파일] [--quiet]');
    process.exit(1);
  }
  const getOpt = (name, def)=>{
    const i = args.indexOf(name);
    return (i >= 0 && i+1 < args.length) ? args[i+1] : def;
  };
  const seed  = parseInt(getOpt('--seed', '1')) || 1;
  const scale = parseFloat(getOpt('--scale', '1')) || 1;
  const svgPath  = getOpt('--svg', null);
  const jsonPath = getOpt('--json', null);
  const resumePath = getOpt('--resume', null);
  const quiet = args.includes('--quiet');

  setSeed(seed);
  let seedBest = null;
  if(resumePath){
    seedBest = JSON.parse(fs.readFileSync(resumePath, 'utf8'));
    if(!quiet) console.error(`이전 기록에서 재개: 넓이 ${seedBest.area}`);
  }

  const t0 = Date.now();
  const best = searchMinTriangle(n, {
    scale, seedBest,
    log: quiet ? ()=>{} : (msg)=>console.error(msg)
  });
  const elapsed = ((Date.now()-t0)/1000).toFixed(1);

  if(!best){
    console.log(`n=${n}: 유효한 배치를 찾지 못함 (seed=${seed}, scale=${scale})`);
    process.exit(2);
  }
  const chk = validate(최고);
  console.log(`n = ${n}  (seed=${seed}, scale=${scale}, ${elapsed}s)`);
  console.log(`최소 넓이 A      = ${best.area.toFixed(9)}`);
  console.log(`밀도 n/A         = ${(n/best.area).toFixed(6)}`);
  console.log(`삼각형 꼭짓점    : (0, 0), (${best.tri.bx.toFixed(6)}, 0), (${best.tri.cx.toFixed(6)}, ${best.tri.cy.toFixed(6)})`);
  console.log(`정사각형 (중심 x, 중심 y, 회전각 rad):`);
  best.squares.forEach((s, i)=>
    console.log(`  ${String(i+1).padStart(2)}: (${s.x.toFixed(6)}, ${s.y.toFixed(6)}, ${s.theta.toFixed(6)})`));
  console.log(`검증: 최대 겹침 침투 = ${chk.maxPen.toExponential(2)} (허용 ${OVL_EPS}), ` +
              `최대 담김 위반 = ${chk.maxViol.toExponential(2)}, 넓이 재계산 오차 = ${chk.areaErr.toExponential(2)}`);

  if(jsonPath){ require('fs').writeFileSync(jsonPath, JSON.stringify(best, null, 1)); console.error(`JSON 저장: ${jsonPath}`); }
  if(svgPath){ require('fs').writeFileSync(svgPath, toSVG(최고)); console.error(`SVG 저장: ${svgPath}`); }
}

if(require.main === module) main();
module.exports = { searchMinTriangle, validate, toSVG, setSeed,
                   supportTri, angleDescent, canonicalRecord,
                   overlapPenetration, overlapTotal, containViolation };
