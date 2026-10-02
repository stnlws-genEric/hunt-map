"use strict";
/* Hunt Map — offline field map and editor. All data stays on this device. */

const BUILD = 21;
const R = 6378137;
const COARSE = matchMedia("(pointer: coarse)").matches;
const GRAB = COARSE ? 22 : 15;          // finger vs mouse
const LINEGRAB = COARSE ? 16 : 10;

/* ---------- tiny IndexedDB key/value ---------- */
const DB = (() => {
  let p = null;
  const open = () => p || (p = new Promise((res, rej) => {
    const r = indexedDB.open("huntmap", 1);
    r.onupgradeneeded = () => r.result.createObjectStore("kv");
    r.onsuccess = () => res(r.result);
    r.onerror = () => rej(r.error);
  }));
  const tx = async (mode, fn) => {
    const db = await open();
    return new Promise((res, rej) => {
      const t = db.transaction("kv", mode), s = t.objectStore("kv");
      const q = fn(s);
      t.oncomplete = () => res(q && q.result);
      t.onerror = () => rej(t.error);
    });
  };
  return {
    get: k => tx("readonly", s => s.get(k)),
    set: (k, v) => tx("readwrite", s => s.put(v, k)),
    del: k => tx("readwrite", s => s.delete(k))
  };
})();

/* ---------- vocabulary ---------- */
const KINDS = {
  trail: {label:"Trail",         dash:[],      w:2.6, col:null},
  road:  {label:"Road",          dash:[],      w:4.0, col:null},
  atv:   {label:"ATV / buggy",   dash:[10,4],  w:3.0, col:null},
  foot:  {label:"Foot path",     dash:[3,4],   w:2.2, col:null},
  creek: {label:"Creek / drain", dash:[8,5],   w:2.4, col:"#3f9fc4"},
  edge:  {label:"Field edge",    dash:[2,6],   w:2.0, col:"#d9c23a"},
  route: {label:"Access route",   dash:[1,5],   w:2.8, col:"#b06bd6"}
};
/* Pin colours are FIXED, never theme-dependent: they sit on aerial photography,
   and the aerial does not get darker when the phone switches to dark mode. */
const PINS = {
  stand:  {label:"Stand",          color:"#E2672A", glyph:"stand"},
  blind:  {label:"Blind",          color:"#E2672A", glyph:"blind"},
  cam:    {label:"Trail camera",   color:"#B98B4F", glyph:"cam"},
  camdeer:{label:"Deer on camera", color:"#B98B4F", glyph:"oncam"},
  track:  {label:"Tracks",         color:"#6C8A58", glyph:"track"},
  scrape: {label:"Scrape",         color:"#6C8A58", glyph:"scrape"},
  rub:    {label:"Rub",            color:"#6C8A58", glyph:"rub"},
  drop:   {label:"Droppings",      color:"#6C8A58", glyph:"drop"},
  urine:  {label:"Urine / sign",   color:"#6C8A58", glyph:"urine"},
  bed:    {label:"Bedding",        color:"#6C8A58", glyph:"bed"},
  feeder: {label:"Feeder",         color:"#C9A33A", glyph:"feeder"},
  food:   {label:"Food plot",      color:"#C9A33A", glyph:"food"},
  water:  {label:"Water",          color:"#5A8C9E", glyph:"water"},
  sight:  {label:"Deer sighting",  color:"#90A379", glyph:"sight"},
  kill:   {label:"Kill",           color:"#AD4531", glyph:"kill"},
  move:   {label:"Movement",       color:"#E2672A", glyph:"move"},
  terrain:{label:"Terrain feature",color:"#7FA8B5", glyph:"terrain"},
  note:   {label:"Note",           color:"#8c8c8c", glyph:"note"}
};
const CHIP_BONE = "#E8E3D6", CHIP_INK = "#14170F";
const DIRECTIONAL = new Set(["sight","camdeer","track","move"]);
const WINDS = ["N","NE","E","SE","S","SW","W","NW"];
const NAME_IDEAS = ["Main road","Camp road","Ridge road","Bottom road","Food plot road",
  "Creek crossing","Power line","Property line walk","North loop","South loop","Bedding edge"];

/* ---------- state ---------- */
let D = null;                       // the loaded map pack
let trails = [], pins = [], sits = [];
let seedDone = [];                  // seed ids already merged, so a deletion stays deleted
let sitOpen = null;          // the sit in progress, if any
let selT = new Set(), primary = null, selPin = null, anchors = [];
let tool = "pan", editMode = "move", arrowPushed = false;
/* What the crosshair is currently aiming at. {what:"pin"} drops a new pin of the
   selected type; {what:"recovery", ...} marks where a deer was shot from, hit or
   found. Before this existed the recovery buttons silently snapshotted the centre
   of the canvas with no crosshair shown and no chance to aim — and the toast
   claimed "at the crosshair" when none had been drawn. */
let placing = null;
let layers = {aerial:true, cont:true, parcel:true, trail:true, labels:true, pins:true};
let nudge = {dx:0, dy:0, rot:0, scl:1};
let draft = null, eraseBox = null, pending = null;
let undoStack = [], redoStack = [];
let uid = 0;
const newId = pre => pre + Date.now().toString(36) + (uid++).toString(36);

const view = {k:1, tx:0, ty:0};
let W = 0, H = 0, DPR = 1;
const cv = document.getElementById("map");
const ctx = cv.getContext("2d");
let aerialImg = null;

/* GPS */
let gpsOn = false, watchId = null, fix = null, recording = null, averaging = null;

/* ---------- geo helpers ---------- */
function worldToLL(x, y){
  const X = D.bbox3857[0] + (x / D.w) * (D.bbox3857[2] - D.bbox3857[0]);
  const Y = D.bbox3857[3] - (y / D.h) * (D.bbox3857[3] - D.bbox3857[1]);
  return [X / R * 180 / Math.PI, (2 * Math.atan(Math.exp(Y / R)) - Math.PI / 2) * 180 / Math.PI];
}
function llToWorld(lon, lat){
  const X = lon * Math.PI / 180 * R;
  const Y = R * Math.log(Math.tan(Math.PI / 4 + lat * Math.PI / 360));
  return [(X - D.bbox3857[0]) / (D.bbox3857[2] - D.bbox3857[0]) * D.w,
          (D.bbox3857[3] - Y) / (D.bbox3857[3] - D.bbox3857[1]) * D.h];
}
const fmtLL = (lon, lat) => lat.toFixed(5) + "°N  " + Math.abs(lon).toFixed(5) + "°W";
const MPP = () => D.mpp;

const sx = x => x * view.k + view.tx;
const sy = y => y * view.k + view.ty;
const wx = px => (px - view.tx) / view.k;
const wy = py => (py - view.ty) / view.k;

const idNudge = () => !nudge.dx && !nudge.dy && !nudge.rot && nudge.scl === 1;
function nudged(p){
  if(idNudge()) return p;
  const c = [D.w/2, D.h/2], a = nudge.rot * Math.PI/180, ca = Math.cos(a), sa = Math.sin(a);
  const x = (p[0]-c[0]) * nudge.scl, y = (p[1]-c[1]) * nudge.scl;
  return [c[0] + x*ca - y*sa + nudge.dx, c[1] + x*sa + y*ca + nudge.dy];
}
function unnudged(p){
  if(idNudge()) return p;
  const c = [D.w/2, D.h/2], a = -nudge.rot * Math.PI/180, ca = Math.cos(a), sa = Math.sin(a);
  const X = p[0]-nudge.dx-c[0], Y = p[1]-nudge.dy-c[1];
  return [c[0] + (X*ca - Y*sa)/nudge.scl, c[1] + (X*sa + Y*ca)/nudge.scl];
}
function evXY(e){ const r = cv.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; }
const atScreen = (px, py) => unnudged([wx(px), wy(py)]);

function distSeg(px, py, a, b){
  const vx = b[0]-a[0], vy = b[1]-a[1], L2 = vx*vx + vy*vy;
  let t = L2 ? ((px-a[0])*vx + (py-a[1])*vy) / L2 : 0;
  t = Math.max(0, Math.min(1, t));
  return {d:Math.hypot(px-(a[0]+vx*t), py-(a[1]+vy*t)), t};
}
function lenOf(p){
  let L = 0;
  for(let i = 0; i < p.length-1; i++) L += Math.hypot(p[i+1][0]-p[i][0], p[i+1][1]-p[i][1]);
  return L * MPP();
}
function rdp(pts, eps){
  if(pts.length < 3) return pts.slice();
  let idx = 0, dmax = 0;
  for(let i = 1; i < pts.length-1; i++){
    const d = distSeg(pts[i][0], pts[i][1], pts[0], pts[pts.length-1]).d;
    if(d > dmax){dmax = d; idx = i;}
  }
  if(dmax > eps) return rdp(pts.slice(0, idx+1), eps).slice(0,-1).concat(rdp(pts.slice(idx), eps));
  return [pts[0], pts[pts.length-1]];
}
/* distances: stored metric, shown in yards. Yards under half a mile, miles above. */
const M2YD = 1.09361;
function fmtDist(m){
  const yd = m * M2YD;
  if(yd < 880) return Math.round(yd) + " yd";
  return (yd/1760).toFixed(2) + " mi";
}
const fmtAcc = m => "\u00b1" + Math.round(m * M2YD) + " yd";

const getT = id => trails.find(t => t.id === id);
const css = v => getComputedStyle(document.documentElement).getPropertyValue(v).trim();

/* ---------- sun & moon, computed locally (no network) ---------- */
function moonInfo(date){
  const synodic = 29.530588853;
  const known = Date.UTC(2000, 0, 6, 18, 14) / 86400000;      // a known new moon
  const days = date.getTime() / 86400000 - known;
  let age = days % synodic; if(age < 0) age += synodic;
  const phase = age / synodic;
  const illum = (1 - Math.cos(2 * Math.PI * phase)) / 2;
  const names = ["New","Waxing crescent","First quarter","Waxing gibbous","Full",
                 "Waning gibbous","Last quarter","Waning crescent"];
  const i = Math.floor(((phase + 1/16) % 1) * 8) % 8;
  return {age:age, illum:illum, phase:phase, name:names[i]};
}
function sunTimes(date, lat, lon){
  const rad = Math.PI/180, dayMs = 86400000, J1970 = 2440588, J2000 = 2451545;
  const toJulian = d => d.valueOf()/dayMs - 0.5 + J1970;
  const fromJulian = j => new Date((j + 0.5 - J1970) * dayMs);
  const d = toJulian(date) - J2000;
  const n = Math.round(d - 0.0009 + lon*rad/(2*Math.PI));
  const Js = 0.0009 - lon*rad/(2*Math.PI) + n;
  const M = rad * (357.5291 + 0.98560028 * Js);
  const C = rad * (1.9148*Math.sin(M) + 0.02*Math.sin(2*M) + 0.0003*Math.sin(3*M));
  const P = rad * 102.9372;
  const Ls = M + C + P + Math.PI;
  const Jtransit = J2000 + Js + 0.0053*Math.sin(M) - 0.0069*Math.sin(2*Ls);
  const dec = Math.asin(Math.sin(Ls) * Math.sin(rad*23.4397));
  const out = {};
  for(const [key, h] of [["sunrise",-0.833],["sunset",-0.833],["dawn",-6],["dusk",-6]]){
    const h0 = h * rad;
    const cosw = (Math.sin(h0) - Math.sin(rad*lat)*Math.sin(dec)) / (Math.cos(rad*lat)*Math.cos(dec));
    if(cosw < -1 || cosw > 1){ out[key] = null; continue; }
    const w = Math.acos(cosw);
    const Jset = J2000 + (0.0009 - lon*rad/(2*Math.PI) + w/(2*Math.PI) + n)
                 + 0.0053*Math.sin(M) - 0.0069*Math.sin(2*Ls);
    out[key] = (key === "sunset" || key === "dusk") ? fromJulian(Jset)
                                                    : fromJulian(Jtransit - (Jset - Jtransit));
  }
  return out;
}
const hhmm = d => d ? d.toLocaleTimeString([], {hour:"numeric", minute:"2-digit"}) : "—";
const degToCompass = d => WINDS.concat(WINDS)[Math.round(((d % 360) + 360) % 360 / 45) % 8];

/* ---------- rendering ---------- */
function resize(){
  DPR = Math.min(window.devicePixelRatio || 1, 2);
  const r = cv.parentElement.getBoundingClientRect();
  W = r.width; H = r.height;
  cv.width = Math.round(W*DPR); cv.height = Math.round(H*DPR);
  cv.style.width = W+"px"; cv.style.height = H+"px";
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
}
function fit(){
  if(!D) return;
  const pad = 16;
  view.k = Math.min((W-pad*2)/D.w, (H-pad*2)/D.h);
  view.tx = (W - D.w*view.k)/2; view.ty = (H - D.h*view.k)/2;
}
function labelRun(pts, textW){
  const S = pts.map(p => [sx(p[0]), sy(p[1])]);
  if(S.length < 2) return null;
  const seg = [], cum = [0];
  for(let i = 0; i < S.length-1; i++){
    const d = Math.hypot(S[i+1][0]-S[i][0], S[i+1][1]-S[i][1]);
    seg.push(d); cum.push(cum[i]+d);
  }
  const total = cum[cum.length-1];
  if(total < 14) return null;
  const at = dd => {
    if(dd <= 0) return S[0];
    for(let i = 0; i < seg.length; i++) if(cum[i+1] >= dd){
      const f = seg[i] ? (dd-cum[i])/seg[i] : 0;
      return [S[i][0]+(S[i+1][0]-S[i][0])*f, S[i][1]+(S[i+1][1]-S[i][1])*f];
    }
    return S[S.length-1];
  };
  const mid = total/2, half = Math.min(textW/2, total/2);
  const a = at(mid-half), b = at(mid+half), c = at(mid);
  let ang = Math.atan2(b[1]-a[1], b[0]-a[0]);
  if(ang > Math.PI/2) ang -= Math.PI;
  if(ang < -Math.PI/2) ang += Math.PI;
  return {x:c[0], y:c[1], ang};
}
function vertexGap(t){
  const pts = t.p.map(nudged), gaps = [];
  for(let i = 0; i < pts.length-1; i++)
    gaps.push(Math.hypot(sx(pts[i+1][0])-sx(pts[i][0]), sy(pts[i+1][1])-sy(pts[i][1])));
  if(!gaps.length) return Infinity;
  gaps.sort((a,b) => a-b);
  return gaps[Math.floor(gaps.length/2)];
}

function draw(){
  if(!D) return;
  ctx.clearRect(0,0,W,H);
  ctx.fillStyle = css("--ground"); ctx.fillRect(0,0,W,H);
  ctx.imageSmoothingQuality = "high";
  const dx = sx(0), dy = sy(0), dw = D.w*view.k, dh = D.h*view.k;
  if(layers.aerial && aerialImg && aerialImg.naturalWidth) ctx.drawImage(aerialImg, dx, dy, dw, dh);
  if(layers.cont && D.contours){
    /* Over imagery a contour needs a dark casing under a light core, or it vanishes
       on bright sand and on dark timber alike. With the aerial off there is nothing
       to fight, so plain ink reads better and a casing just looks like a mistake. */
    const overImagery = layers.aerial && aerialImg && aerialImg.naturalWidth;
    const trace = c => {
      ctx.beginPath();
      for(let i = 0; i < c.p.length; i++){
        const X = sx(c.p[i][0]), Y = sy(c.p[i][1]);
        i ? ctx.lineTo(X,Y) : ctx.moveTo(X,Y);
      }
      ctx.closePath();
    };
    ctx.lineJoin = "round"; ctx.lineCap = "round";
    if(overImagery){
      // pass 1: every casing first, so no line's halo covers its neighbour's core
      ctx.strokeStyle = "rgba(10,12,8,.72)";
      for(const c of D.contours){
        trace(c);
        ctx.lineWidth = (c.index ? 2.0 : 1.2) + 2.0;
        ctx.stroke();
      }
      ctx.strokeStyle = "#f2ead8";
      for(const c of D.contours){ trace(c); ctx.lineWidth = c.index ? 2.0 : 1.2; ctx.stroke(); }
    }else{
      const clay = css("--clay");
      ctx.strokeStyle = clay;
      for(const c of D.contours){
        trace(c);
        ctx.globalAlpha = c.index ? 1 : .75;
        ctx.lineWidth = c.index ? 2.0 : 1.1;
        ctx.stroke();
      }
    }
    ctx.globalAlpha = 1;
    if(view.k > .55){
      ctx.font = "600 10px 'IBM Plex Mono',monospace";
      ctx.textAlign = "center"; ctx.textBaseline = "middle";
      for(const c of D.contours){
        if(!c.index || c.p.length < 14) continue;
        const m = c.p[Math.floor(c.p.length/2)], X = sx(m[0]), Y = sy(m[1]);
        if(X<0||X>W||Y<0||Y>H) continue;
        const txt = c.ft + "'", wd = ctx.measureText(txt).width + 5;
        ctx.fillStyle = overImagery ? "rgba(10,12,8,.8)" : css("--ground");
        ctx.globalAlpha = overImagery ? 1 : .8;
        ctx.fillRect(X-wd/2, Y-7, wd, 13);
        ctx.globalAlpha = 1;
        ctx.fillStyle = overImagery ? "#f2ead8" : css("--clay");
        ctx.fillText(txt, X, Y);
      }
    }
  }
  if(layers.parcel && D.parcels){
    ctx.lineJoin = "round";
    for(const p of D.parcels){
      ctx.beginPath();
      p.p.forEach((q,i) => i ? ctx.lineTo(sx(q[0]), sy(q[1])) : ctx.moveTo(sx(q[0]), sy(q[1])));
      ctx.closePath();
      ctx.strokeStyle = "rgba(0,0,0,.45)"; ctx.lineWidth = 4.5; ctx.stroke();
      ctx.strokeStyle = "#e8c53a"; ctx.lineWidth = 2; ctx.setLineDash([9,5]); ctx.stroke();
      ctx.setLineDash([]);
    }
  }
  if(layers.trail){
    const blaze = css("--blaze");
    ctx.lineCap = "round"; ctx.lineJoin = "round";
    for(const t of trails){
      const ks = KINDS[t.kind] || KINDS.trail, pts = t.p.map(nudged);
      ctx.beginPath();
      pts.forEach((q,i) => i ? ctx.lineTo(sx(q[0]), sy(q[1])) : ctx.moveTo(sx(q[0]), sy(q[1])));
      ctx.setLineDash([]); ctx.strokeStyle = "rgba(0,0,0,.5)"; ctx.lineWidth = ks.w+2.4; ctx.stroke();
      const on = selT.has(t.id);
      ctx.setLineDash(on ? [] : ks.dash);
      ctx.strokeStyle = on ? "#fff" : (ks.col || blaze);
      ctx.lineWidth = on ? ks.w+.8 : ks.w; ctx.stroke(); ctx.setLineDash([]);
    }
    if(layers.labels && view.k > .42){
      ctx.font = "600 12px 'Barlow Condensed',sans-serif";
      ctx.textAlign = "center"; ctx.textBaseline = "middle";
      const placed = [];
      for(const {t} of trails.filter(t => t.name).map(t => ({t, L:lenOf(t.p)})).sort((a,b) => b.L-a.L)){
        const wd = ctx.measureText(t.name).width + 9;
        const pl = labelRun(t.p.map(nudged), wd);
        if(!pl || pl.x < -60 || pl.x > W+60 || pl.y < -30 || pl.y > H+30) continue;
        const ex = Math.abs(Math.cos(pl.ang))*wd/2 + Math.abs(Math.sin(pl.ang))*9;
        const ey = Math.abs(Math.sin(pl.ang))*wd/2 + Math.abs(Math.cos(pl.ang))*9;
        const bb = {x0:pl.x-ex, x1:pl.x+ex, y0:pl.y-ey-11, y1:pl.y+ey-11};
        if(placed.some(o => bb.x0<o.x1 && bb.x1>o.x0 && bb.y0<o.y1 && bb.y1>o.y0)) continue;
        placed.push(bb);
        ctx.save(); ctx.translate(pl.x, pl.y); ctx.rotate(pl.ang); ctx.translate(0,-11);
        const h = 15, rr = 3, x0 = -wd/2, y0 = -h/2;
        ctx.beginPath(); ctx.moveTo(x0+rr,y0);
        ctx.arcTo(x0+wd,y0,x0+wd,y0+h,rr); ctx.arcTo(x0+wd,y0+h,x0,y0+h,rr);
        ctx.arcTo(x0,y0+h,x0,y0,rr); ctx.arcTo(x0,y0,x0+wd,y0,rr); ctx.closePath();
        ctx.fillStyle = "rgba(0,0,0,.66)"; ctx.fill();
        ctx.fillStyle = "#fff"; ctx.fillText(t.name, 0, .5);
        ctx.restore();
      }
    }
    if(tool === "draw" || tool === "edit"){
      ctx.fillStyle = "rgba(255,255,255,.85)";
      for(const t of trails) for(const q of [t.p[0], t.p[t.p.length-1]]){
        const n = nudged(q);
        ctx.beginPath(); ctx.arc(sx(n[0]), sy(n[1]), 2.6, 0, 7); ctx.fill();
      }
      for(const t of trails){
        if(!selT.has(t.id) || t.id === primary) continue;
        for(const q of t.p.map(nudged)){
          ctx.beginPath(); ctx.arc(sx(q[0]), sy(q[1]), 3.6, 0, 7);
          ctx.fillStyle = blaze; ctx.fill();
          ctx.strokeStyle = "#fff"; ctx.lineWidth = 1.3; ctx.stroke();
        }
      }
    }
    const pt = primary && getT(primary);
    if(pt && tool === "edit"){
      const pts = pt.p.map(nudged);
      if(anchors.length === 2){
        const [i,j] = [Math.min(...anchors), Math.max(...anchors)];
        ctx.beginPath();
        for(let k = i; k <= j; k++){
          const X = sx(pts[k][0]), Y = sy(pts[k][1]);
          k === i ? ctx.moveTo(X,Y) : ctx.lineTo(X,Y);
        }
        ctx.strokeStyle = css("--sky"); ctx.lineWidth = 6; ctx.globalAlpha = .75; ctx.stroke(); ctx.globalAlpha = 1;
      }
      for(let k = 0; k < pts.length; k++){
        const X = sx(pts[k][0]), Y = sy(pts[k][1]), isA = anchors.includes(k);
        ctx.beginPath(); ctx.arc(X, Y, isA ? (COARSE?8:6) : (COARSE?6:4.5), 0, 7);
        ctx.fillStyle = isA ? css("--sky") : blaze; ctx.fill();
        ctx.strokeStyle = "#fff"; ctx.lineWidth = 1.6; ctx.stroke();
      }
    }
    if(draft && draft.pts.length){
      ctx.beginPath();
      draft.pts.forEach((q,i) => {const n = nudged(q); i ? ctx.lineTo(sx(n[0]), sy(n[1])) : ctx.moveTo(sx(n[0]), sy(n[1]));});
      ctx.strokeStyle = css("--sky"); ctx.lineWidth = 2.6; ctx.setLineDash([7,4]); ctx.stroke(); ctx.setLineDash([]);
      for(const q of draft.pts){
        const n = nudged(q);
        ctx.beginPath(); ctx.arc(sx(n[0]), sy(n[1]), 3.5, 0, 7); ctx.fillStyle = css("--sky"); ctx.fill();
      }
    }
    if(recording && recording.pts.length > 1){
      ctx.beginPath();
      recording.pts.forEach((q,i) => i ? ctx.lineTo(sx(q[0]), sy(q[1])) : ctx.moveTo(sx(q[0]), sy(q[1])));
      ctx.strokeStyle = css("--danger"); ctx.lineWidth = 3.4; ctx.stroke();
    }
  }
  if(layers.pins) for(const p of pins) drawPin(p);
  if(fix) drawFix();
  if(tool === "mark"){ drawCrosshair(); syncPlacing(); }
  if(eraseBox){
    const {x0,y0,x1,y1} = eraseBox;
    ctx.save(); ctx.setLineDash([6,4]); ctx.strokeStyle = "#ff4d4d"; ctx.lineWidth = 1.6;
    ctx.fillStyle = "rgba(255,77,77,.16)";
    ctx.fillRect(x0,y0,x1-x0,y1-y0); ctx.strokeRect(x0,y0,x1-x0,y1-y0); ctx.restore();
  }
  updateScale();
}

function roundRect(x, y, w, h, r){
  ctx.beginPath();
  ctx.moveTo(x+r, y);
  ctx.arcTo(x+w, y,   x+w, y+h, r);
  ctx.arcTo(x+w, y+h, x,   y+h, r);
  ctx.arcTo(x,   y+h, x,   y,   r);
  ctx.arcTo(x,   y,   x+w, y,   r);
  ctx.closePath();
}
function drawPin(p){
  const X = sx(p.x), Y = sy(p.y);
  if(X < -48 || X > W+48 || Y < -48 || Y > H+48) return;
  const spec = PINS[p.t] || PINS.note, on = selPin === p.id;
  const S = on ? 27 : 22;                       // 22 px is the floor: below it the rack goes

  if(DIRECTIONAL.has(p.t) && typeof p.dir === "number"){
    const a = (p.dir-90)*Math.PI/180, L = 34;
    const hx = X+Math.cos(a)*L, hy = Y+Math.sin(a)*L;
    ctx.beginPath(); ctx.moveTo(X,Y); ctx.lineTo(hx,hy);
    ctx.strokeStyle = "rgba(0,0,0,.55)"; ctx.lineWidth = 5; ctx.stroke();
    ctx.strokeStyle = spec.color; ctx.lineWidth = 2.4; ctx.stroke();
    ctx.beginPath(); ctx.moveTo(hx,hy);
    ctx.lineTo(hx+Math.cos(a+2.5)*9, hy+Math.sin(a+2.5)*9);
    ctx.lineTo(hx+Math.cos(a-2.5)*9, hy+Math.sin(a-2.5)*9);
    ctx.closePath(); ctx.fillStyle = spec.color; ctx.fill();
    ctx.strokeStyle = "rgba(0,0,0,.45)"; ctx.lineWidth = 1; ctx.stroke();
  }

  const x0 = X - S/2, y0 = Y - S/2;
  ctx.save();
  ctx.shadowColor = "rgba(0,0,0,.5)"; ctx.shadowBlur = 3; ctx.shadowOffsetY = 1;
  roundRect(x0, y0, S, S, S*.28);
  ctx.fillStyle = CHIP_BONE; ctx.fill();
  ctx.restore();
  roundRect(x0, y0, S, S, S*.28);
  ctx.lineWidth = on ? 3 : 2.2; ctx.strokeStyle = on ? "#fff" : spec.color; ctx.stroke();

  let g = GLYPH[spec.glyph] || GLYPH.note;
  ctx.save(); ctx.translate(x0, y0);
  paintGlyph(g, S, CHIP_INK);
  // a buck carries the rack; a doe does not, and the count rides on the badge
  if(p.t === "kill" && p.sex !== "doe")
    paintGlyph({s:RACK, sw:1.25}, S, CHIP_INK);
  ctx.restore();

  if(p.t === "kill" && p.sex !== "doe" && p.points){
    const bs = Math.max(S*.46, 11), bx = X + S/2 - bs*.36, by = Y + S/2 - bs*.36;
    ctx.beginPath(); ctx.arc(bx, by, bs/2, 0, 7);
    ctx.fillStyle = spec.color; ctx.fill();
    ctx.lineWidth = Math.max(1.4, S*.075); ctx.strokeStyle = css("--panel") || "#1b2016"; ctx.stroke();
    ctx.fillStyle = CHIP_BONE;
    ctx.font = "700 " + Math.round(bs*.66) + "px 'Barlow Condensed',sans-serif";
    ctx.textAlign = "center"; ctx.textBaseline = "middle";
    ctx.fillText(String(p.points), bx, by + bs*.04);
  }

  if(p.name && view.k > .5){
    ctx.font = "600 11px 'Barlow Condensed',sans-serif";
    ctx.textAlign = "left"; ctx.textBaseline = "middle";
    const tw = ctx.measureText(p.name).width;
    ctx.fillStyle = "rgba(0,0,0,.6)"; ctx.fillRect(X+S/2+3, Y-7, tw+6, 14);
    ctx.fillStyle = "#fff"; ctx.fillText(p.name, X+S/2+6, Y);
  }
}
function drawFix(){
  const w = llToWorld(fix.lon, fix.lat), X = sx(w[0]), Y = sy(w[1]);
  const rad = (fix.acc / MPP()) * view.k;
  if(rad > 3){
    ctx.beginPath(); ctx.arc(X, Y, rad, 0, 7);
    ctx.fillStyle = "rgba(57,208,255,.16)"; ctx.fill();
    ctx.strokeStyle = "rgba(57,208,255,.6)"; ctx.lineWidth = 1; ctx.stroke();
  }
  ctx.beginPath(); ctx.arc(X, Y, 7, 0, 7);
  ctx.fillStyle = "#1e90ff"; ctx.fill();
  ctx.strokeStyle = "#fff"; ctx.lineWidth = 2.5; ctx.stroke();
}
/* The crosshair has to sit in the middle of the map you can SEE, which is not the
   middle of the canvas. The canvas runs full-bleed underneath the panel, so on a
   laptop the panel covers the left ~230 px and the raw centre lands well left of
   where your eye puts the middle — about 116 px out on a 1280 px window, which is
   a real distance on the ground. On a phone the sheet covers the bottom instead,
   and the error runs the other way. */
function mapCentre(){
  const cr = cv.getBoundingClientRect();
  let left = 0, right = 0, bottom = 0;
  /* Both floating panels eat into the map: the tool rail on the left, the
     inspector on the right, and on a phone each of them spans the width and sits
     along the bottom instead. Measure whichever are actually on screen. */
  for(const [id, side] of [["rail", "left"], ["insp", "right"]]){
    const el = document.getElementById(id);
    if(!el || el.hidden || !el.getClientRects().length) continue;
    const b = el.getBoundingClientRect();
    if(b.width > cr.width * 0.6){ bottom = Math.max(bottom, cr.bottom - b.top); continue; }
    if(side === "left") left  = Math.max(left,  b.right - cr.left);
    else                right = Math.max(right, cr.right - b.left);
  }
  left = Math.max(0, left); right = Math.max(0, right); bottom = Math.max(0, bottom);
  /* If the panels between them leave no room, fall back to the whole canvas
     rather than returning a centre outside it. */
  if(left + right >= W - 40){ left = right = 0; }
  if(bottom >= H - 40) bottom = 0;
  return [(left + (W - right)) / 2, (H - bottom) / 2];
}

function drawCrosshair(){
  /* Locked at the centre of the visible map: you pan under it instead of stabbing
     at the glass, which is the only way to be accurate one-handed in the woods.
     Same casing trick as the contours so it reads over sand and over timber. */
  const c = mapCentre();
  const X = Math.round(c[0]), Y = Math.round(c[1]), R1 = 16, GAP = 5;
  const arm = (dx, dy) => {
    ctx.beginPath();
    ctx.moveTo(X+dx*GAP, Y+dy*GAP); ctx.lineTo(X+dx*R1, Y+dy*R1);
  };
  for(const pass of [{c:"rgba(10,12,8,.75)", w:5}, {c:"#f2ead8", w:1.8}]){
    ctx.strokeStyle = pass.c; ctx.lineWidth = pass.w; ctx.lineCap = "round";
    arm(1,0); ctx.stroke(); arm(-1,0); ctx.stroke();
    arm(0,1); ctx.stroke(); arm(0,-1); ctx.stroke();
    ctx.beginPath(); ctx.arc(X, Y, R1-4.5, 0, 7); ctx.stroke();
  }
  ctx.beginPath(); ctx.arc(X, Y, 1.4, 0, 7);
  ctx.fillStyle = "#E2672A"; ctx.fill();
}
function updateScale(){
  /* round YARD steps, not converted metres: a bar labelled "109 yd" is worse than one labelled "100 yd" */
  const yards = [10,25,50,100,200,300,440,880,1760,3520];
  const pxPerYd = () => view.k / (MPP() * M2YD);
  let best = yards[0];
  for(const y of yards) if(y * pxPerYd() <= 110) best = y;
  document.getElementById("scalerule").style.width = (best * pxPerYd()).toFixed(0)+"px";
  document.getElementById("scaletext").textContent =
    best >= 880 ? (best/1760 % 1 ? (best/1760).toFixed(2) : best/1760) + " mi" : best + " yd";
}


/* ---------- pin glyphs ----------
   Set D, the bone chip: an ink glyph on a bone rounded square with a kind-coloured
   border. Geometry is on a 24x24 grid, drawn through Path2D with the same SVG path
   data the icon sheet was designed with, so the map and the sheet never drift apart.
   `sw` overrides the stroke width: filled shapes need a hair stroke or they blob and
   fine detail (the hoof cleft, the skull sockets) closes up.                        */
const HOOF_L = "M11.1 3.4C9.3 5.3 6.2 8.7 5.1 12.1c-1 3.2.7 5.6 3.2 5.6 1.9 0 2.9-1 2.95-2.8.05-3.8.05-8.2-.15-11.5z";
const HOOF_R = "M12.9 3.4c1.8 1.9 4.9 5.3 6 8.7 1 3.2-.7 5.6-3.2 5.6-1.9 0-2.9-1-2.95-2.8-.05-3.8-.05-8.2.15-11.5z";
const hoofAt = (tx, ty, k) => ({f:[HOOF_L, HOOF_R], sw:.5, tf:[tx, ty, k]});

const GLYPH = {
  stand:  {s:["M8.6 21.2 9.9 4","M15.4 21.2 14.1 4","M9.55 7.6h4.9","M9.1 13h5.8","M8.75 18.4h6.5"]},
  blind:  {s:["M6.2 7.8h11.6v6.4H6.2z","M4.2 7.8 12 3.4l7.8 4.4","M9 10.9h6",
              "M7.8 14.2 6 21.6M16.2 14.2l1.8 7.4"]},
  cam:    {s:["M5.2 8h13.6v11.4H5.2z","M8.4 8V5.2h7.2V8","M8.4 11h-1.4"],
           c:[[12,13.7,3.2]]},
  oncam:  {s:["M4.4 8.8V4.4h4.4M19.6 8.8V4.4h-4.4M4.4 15.2v4.4h4.4M19.6 15.2v4.4h-4.4"],
           g:[hoofAt(12,12,.5)]},
  track:  {f:[HOOF_L,HOOF_R], sw:.5,
           e:[[7.8,20.9,1.45,2.05,20],[16.2,20.9,1.45,2.05,-20]]},
  scrape: {g:[hoofAt(12,9.2,.62)],
           s:["M7.2 17.6 9.5 19.4M10.8 16.8l2.5 1.8M14.8 17.8l2.2 1.6M8.9 21l2.3 1.4M13.3 20.8l2.3 1.4"]},
  rub:    {s:["M10.3 3.2c-1 5.7-1.4 11.7-1.3 18.2h6c.1-6.5-.3-12.5-1.3-18.2z","M6.4 21.4h11.2"],
           f:["M11.9 8.4c-1.3 1.5-1.5 5.8-.4 8 1-2.4 1.1-5.6.4-8z"], sw:.5},
  drop:   {g:[hoofAt(12,9,.6)], sw:.5,
           e:[[7.9,19.4,1.6,1.15,-20],[12.1,21.6,1.6,1.15,8],[16.1,19.2,1.6,1.15,22]]},
  urine:  {g:[hoofAt(12,8.8,.6)], sw:.5,
           f:["M12 16.2c-1.1 1.6-1.5 2.7-.9 3.5.5.6 1.3.6 1.8 0 .6-.8.2-1.9-.9-3.5z"]},
  bed:    {s:["M7.2 13c2-1.4 4.8-1.4 6.8 0M9 16.4c1.8-1.2 4.2-1.2 6 0"],
           eo:[[12,13.8,7.8,5,0]]},
  feeder: {s:["M7.9 3.8h8.2v8.4H7.9z","M7.9 12.2 12 17.4l4.1-5.2","M10 18.6 7.6 22.2M14 18.6l2.4 3.6"]},
  food:   {s:["M4.4 6.6h15.2v10.8H4.4z","M7.6 9.6v4.8M12 9.6v4.8M16.4 9.6v4.8"]},
  water:  {s:["M3.6 8.6c2.8-2.7 5.6-2.7 8.4 0s5.6 2.7 8.4 0","M3.6 14c2.8-2.7 5.6-2.7 8.4 0s5.6 2.7 8.4 0",
              "M3.6 19.4c2.8-2.7 5.6-2.7 8.4 0s5.6 2.7 8.4 0"]},
  sight:  {s:["M10.3 12.4h3.4","M6 11.4V7.7h4.3v3.7M18 11.4V7.7h-4.3v3.7"],
           c:[[7.8,15.2,4.4],[16.2,15.2,4.4]]},
  kill:   {s:["M12 5.4c-2.4 0-4.2 1.8-4.35 4.4-.15 2 .2 3.4 1.2 4.5.9 1 1.35 2.2 1.45 3.9l.15 2.2c.05.9.45 1.45 1.55 1.45s1.5-.55 1.55-1.45l.15-2.2c.1-1.7.55-2.9 1.45-3.9 1-1.1 1.35-2.5 1.2-4.5C16.2 7.2 14.4 5.4 12 5.4z"],
           sw:1.25,
           e:[[10,11.4,1.35,1.05,-25],[14,11.4,1.35,1.05,25]],
           f:["M12 17.2c-.55 1.3-.7 2.6-.35 3.2.3.5.8.5 1.1 0 .35-.6.2-1.9-.35-3.2z"]},
  note:   {s:["M12 4.4v12.4","M8.6 13.4 12 16.8l3.4-3.4"], c:[[12,20.4,1.1]]},
  move:   {s:["M12 21.4V4.6","M7.2 9.4 12 4.4l4.8 5"]},
  terrain:{s:["M2.8 16.4c3.4-4 6.2-4 9.2 0s5.8 4 9.2 0",
              "M5.4 20.2c2.4-2.8 4.4-2.8 6.6 0s4.2 2.8 6.6 0",
              "M12 11.6 9.2 7.2h5.6z"]}
};
/* one rack, drawn once — the point count rides on a badge where it stays readable */
const RACK = ["M10.4 7.4C9 4.8 6.6 3.2 4 3 2.9 2.95 2.2 2.3 2.3 1.2",
              "M13.6 7.4c1.4-2.6 3.8-4.2 6.4-4.4 1.1-.05 1.8-.7 1.7-1.8",
              "M8.9 5.2 8.6 2.4","M15.1 5.2 15.4 2.4",
              "M7 3.9 6.7 1.1","M17 3.9 17.3 1.1",
              "M5.2 3.2 4.9 .9","M18.8 3.2 19.1 .9"];
const PATHC = new Map();
const pathOf = d => { let p = PATHC.get(d); if(!p){ p = new Path2D(d); PATHC.set(d, p); } return p; };

function paintGlyph(spec, size, ink){
  const k = size/24;
  ctx.save(); ctx.scale(k, k);
  ctx.lineCap = "round"; ctx.lineJoin = "round";
  ctx.strokeStyle = ink; ctx.fillStyle = ink;
  const base = spec.sw || 1.7;
  const run = (sp, tf) => {
    ctx.save();
    if(tf){ ctx.translate(tf[0], tf[1]); ctx.scale(tf[2], tf[2]); ctx.translate(-12, -12); }
    ctx.lineWidth = sp.sw || base;
    for(const d of sp.f || []){ const p = pathOf(d); ctx.fill(p); ctx.stroke(p); }
    for(const d of sp.s || []) ctx.stroke(pathOf(d));
    for(const c of sp.c || []){ ctx.beginPath(); ctx.arc(c[0], c[1], c[2], 0, 7); ctx.stroke(); }
    for(const e of sp.e || []){           // filled: dewclaws, pellets, eye sockets
      ctx.beginPath(); ctx.ellipse(e[0], e[1], e[2], e[3], (e[4]||0)*Math.PI/180, 0, 7);
      ctx.fill(); ctx.stroke();
    }
    for(const e of sp.eo || []){          // outline: the bed hollow, lens barrels
      ctx.beginPath(); ctx.ellipse(e[0], e[1], e[2], e[3], (e[4]||0)*Math.PI/180, 0, 7);
      ctx.stroke();
    }
    ctx.restore();
  };
  run(spec, spec.tf);
  for(const g of spec.g || []) run(g, g.tf);
  ctx.restore();
}

function syncPlacing(){
  const bar = document.getElementById("placebar");
  if(!bar) return;
  const on = tool === "mark";
  bar.hidden = !on;
  document.body.classList.toggle("placing", on);
  if(!on) return;
  const c = mapCentre();
  const w = atScreen(c[0], c[1]), ll = worldToLL(w[0], w[1]);
  let txt = fmtLL(ll[0], ll[1]);
  if(fix){
    const fw = llToWorld(fix.lon, fix.lat);
    txt += "  ·  " + fmtDist(Math.hypot(w[0]-fw[0], w[1]-fw[1]) * MPP()) + " from you";
  }
  document.getElementById("placecoord").textContent = txt;
  const rec = placing && placing.what === "recovery";
  /* "Placing" is a static word in the markup, so a recovery label was reading
     "Placing Marking shot from". Swap the lead word instead of stacking verbs. */
  const lead = document.getElementById("placelead");
  lead.firstChild.nodeValue = rec ? "Marking " : "Placing ";
  document.getElementById("placewhat").textContent =
    rec ? placing.label.toLowerCase()
        : (PINS[document.getElementById("pintype").value] || PINS.note).label;
  document.getElementById("placego").textContent = rec ? "Mark here" : "Place here";
}

/* ---------- hit tests ---------- */
function hitPin(px, py){
  for(let i = pins.length-1; i >= 0; i--)
    if(Math.hypot(sx(pins[i].x)-px, sy(pins[i].y)-py) < GRAB) return pins[i];
  return null;
}
function hitTrail(px, py){
  let best = null, bd = LINEGRAB, bi = -1;
  for(const t of trails){
    const pts = t.p.map(nudged);
    for(let i = 0; i < pts.length-1; i++){
      const r = distSeg(px, py, [sx(pts[i][0]), sy(pts[i][1])], [sx(pts[i+1][0]), sy(pts[i+1][1])]);
      if(r.d < bd){bd = r.d; best = t; bi = i;}
    }
  }
  return best ? {t:best, i:bi} : null;
}
function hitVertex(t, px, py){
  const pts = t.p.map(nudged);
  let bi = -1, bd = GRAB;
  for(let i = 0; i < pts.length; i++){
    const d = Math.hypot(sx(pts[i][0])-px, sy(pts[i][1])-py);
    if(d < bd){bd = d; bi = i;}
  }
  return bi;
}
function hitAnyVertex(px, py){
  let best = null, bd = GRAB;
  for(const t of trails){
    const pts = t.p.map(nudged);
    for(let i = 0; i < pts.length; i++){
      const d = Math.hypot(sx(pts[i][0])-px, sy(pts[i][1])-py);
      if(d < bd){bd = d; best = {t, i};}
    }
  }
  return best;
}
function hitLooseEnd(px, py){
  for(const t of trails) for(const end of [0,1]){
    const q = nudged(end ? t.p[t.p.length-1] : t.p[0]);
    if(Math.hypot(sx(q[0])-px, sy(q[1])-py) < GRAB) return {id:t.id, end};
  }
  return null;
}

/* ---------- history ---------- */
const snap = () => JSON.stringify({trails, pins, sits});
function push(){ undoStack.push(snap()); if(undoStack.length > 60) undoStack.shift(); redoStack.length = 0; }
function restore(s){
  const o = JSON.parse(s);
  trails = o.trails; pins = o.pins; if(o.sits) sits = o.sits;
  selT = new Set([...selT].filter(id => getT(id)));
  if(primary && !getT(primary)) primary = null;
  if(selPin && !pins.find(p => p.id === selPin)) selPin = null;
  anchors = [];
  after(null);
}
function after(msg){ saveState(); syncList(); renderInsp(); renderSits(); draw(); if(msg) toast(msg); }

/* ---------- selection ---------- */
function selectTrail(id, additive){
  if(!additive) selT.clear();
  if(additive && selT.has(id)) selT.delete(id); else selT.add(id);
  primary = selT.has(id) ? id : ([...selT].pop() || null);
  selPin = null; anchors = [];
  syncList(); renderInsp(); draw();
}
function clearSel(){ selT.clear(); primary = null; selPin = null; anchors = []; syncList(); renderInsp(); draw(); }

/* ---------- edit operations ---------- */
function span(){
  if(!primary || anchors.length !== 2) return null;
  const t = getT(primary); if(!t) return null;
  return {t, i:Math.min(...anchors), j:Math.max(...anchors)};
}
function replaceTrail(t, arrays){
  const idx = trails.indexOf(t);
  const made = arrays.filter(a => a.length >= 2)
    .map((a, n) => ({id:n ? newId("s") : t.id, p:a, name:t.name, kind:t.kind}));
  trails.splice(idx, 1, ...made);
  return made;
}
function opStraighten(){
  const s = span(); if(!s) return;
  push(); s.t.p = s.t.p.slice(0, s.i+1).concat(s.t.p.slice(s.j));
  anchors = [s.i, s.i+1]; after("Stretch straightened.");
}
function opCut(){
  const s = span(); if(!s) return;
  push();
  const made = replaceTrail(s.t, [s.t.p.slice(0, s.i+1), s.t.p.slice(s.j)]);
  primary = made[0] ? made[0].id : null;
  selT = new Set(made.map(m => m.id)); anchors = [];
  after(made.length === 2 ? "Cut out — line split in two." : made.length ? "Trimmed." : "Line removed.");
}
function opKeepSpan(){
  const s = span(); if(!s) return;
  push(); s.t.p = s.t.p.slice(s.i, s.j+1); anchors = []; after("Kept just that stretch.");
}
function opRedraw(){
  const s = span(); if(!s) return;
  draft = {pts:[], extend:null, redraw:{id:s.t.id, i:s.i, j:s.j}};
  setTool("draw", true); toast("Tap the real route, then double-tap or Enter.");
}
function opSplit(){
  if(!primary || anchors.length !== 1) return;
  const t = getT(primary), i = anchors[0];
  if(i <= 0 || i >= t.p.length-1) return toast("Pick a point in the middle of the line.");
  push();
  const made = replaceTrail(t, [t.p.slice(0, i+1), t.p.slice(i)]);
  selT = new Set(made.map(m => m.id)); primary = made[0].id; anchors = [];
  after("Split into two lines.");
}
function opTrim(dir){
  if(!primary || anchors.length !== 1) return;
  const t = getT(primary), i = anchors[0];
  push();
  t.p = dir === "start" ? t.p.slice(i) : t.p.slice(0, i+1);
  if(t.p.length < 2) trails = trails.filter(x => x !== t);
  anchors = []; after("Trimmed.");
}
function opSimplify(strong){
  const ids = selT.size ? [...selT] : (primary ? [primary] : []);
  if(!ids.length) return;
  push();
  const eps = (strong ? 9 : 2.6) / MPP();
  for(const id of ids){ const t = getT(id); if(t) t.p = rdp(t.p, eps); }
  anchors = []; after(strong ? "Straightened." : "Smoothed.");
}
function opDeleteSel(){
  if(!selT.size && !selPin) return;
  push();
  if(selPin){ pins = pins.filter(p => p.id !== selPin); selPin = null; }
  if(selT.size){ trails = trails.filter(t => !selT.has(t.id)); selT.clear(); primary = null; anchors = []; }
  after("Deleted.");
}
function opJoin(){
  if(!primary) return;
  const t = getT(primary); if(!t) return;
  let best = null;
  for(const o of trails){
    if(o === t) continue;
    for(const te of [0,1]) for(const oe of [0,1]){
      const a = te ? t.p[t.p.length-1] : t.p[0], b = oe ? o.p[o.p.length-1] : o.p[0];
      const d = Math.hypot(a[0]-b[0], a[1]-b[1]) * MPP();
      if(!best || d < best.d) best = {d, o, te, oe};
    }
  }
  if(!best || best.d > 60) return toast("No loose end within 65 yd to join to.");
  push();
  const A = best.te ? t.p.slice() : t.p.slice().reverse();
  const B = best.oe ? best.o.p.slice().reverse() : best.o.p.slice();
  t.p = A.concat(B);
  trails = trails.filter(x => x !== best.o);
  selT = new Set([t.id]); primary = t.id; anchors = [];
  after("Joined — gap was " + fmtDist(best.d) + ".");
}
function removePoint(t, i){
  if(!t || i < 0) return;
  if(t.p.length <= 2) return toast("A line needs two points — delete the line instead.");
  push(); t.p.splice(i, 1);
  anchors = anchors.filter(a => a !== i).map(a => a > i ? a-1 : a);
  after("Point removed — " + t.p.length + " left.");
}
function removeMarkedPoint(){ if(primary && anchors.length === 1) removePoint(getT(primary), anchors[0]); }
function setEditMode(m){
  editMode = m;
  if(m !== "move" && tool !== "edit") setTool("edit");
  cv.classList.toggle("cross", tool === "draw" || tool === "mark" || tool === "erase" || m !== "move");
  renderInsp(); draw();
}
function applyErase(box, wholeLines){
  const inBox = q => {
    const n = nudged(q), X = sx(n[0]), Y = sy(n[1]);
    return X >= box.x0 && X <= box.x1 && Y >= box.y0 && Y <= box.y1;
  };
  push();
  if(wholeLines){
    const before = trails.length;
    trails = trails.filter(t => !t.p.some(inBox));
    return after(before - trails.length ? (before - trails.length) + " line(s) deleted." : "Nothing in the box.");
  }
  const out = []; let touched = 0;
  for(const t of trails){
    if(!t.p.some(inBox)){ out.push(t); continue; }
    touched++;
    let run = [], first = true;
    for(const q of t.p){
      if(inBox(q)){
        if(run.length >= 2){ out.push({id:first ? t.id : newId("e"), p:run, name:t.name, kind:t.kind}); first = false; }
        run = [];
      } else run.push(q);
    }
    if(run.length >= 2) out.push({id:first ? t.id : newId("e"), p:run, name:t.name, kind:t.kind});
  }
  trails = out;
  selT = new Set([...selT].filter(id => getT(id)));
  if(primary && !getT(primary)) primary = null;
  anchors = [];
  after(touched ? "Erased inside the box." : "Nothing in the box.");
}

/* ---------- pointer ---------- */
let drag = null, pinch = null;
const ptrs = new Map();

cv.addEventListener("pointerdown", e => {
  if(!D) return;
  try{ cv.setPointerCapture(e.pointerId); }catch(_){}
  const d0 = evXY(e);
  ptrs.set(e.pointerId, d0);
  if(ptrs.size === 2){
    const [a,b] = [...ptrs.values()];
    pinch = {d:Math.hypot(a[0]-b[0], a[1]-b[1]), k:view.k, cx:(a[0]+b[0])/2, cy:(a[1]+b[1])/2, tx:view.tx, ty:view.ty};
    drag = null; return;
  }
  const px = d0[0], py = d0[1];

  if(tool === "draw"){
    if(!draft) draft = {pts:[], extend:null, redraw:null};
    if(!draft.pts.length && !draft.redraw){
      const le = hitLooseEnd(px, py);
      if(le){
        draft.extend = le;
        const t = getT(le.id);
        draft.pts.push((le.end ? t.p[t.p.length-1] : t.p[0]).slice());
        toast("Extending that line."); draw(); return;
      }
    }
    draft.pts.push(atScreen(px, py)); draw(); return;
  }
  if(tool === "erase"){ eraseBox = {x0:px, y0:py, x1:px, y1:py, shift:e.shiftKey}; drag = {mode:"erase"}; return; }
  /* Placing a pin is pan-only. Tapping to drop used to be allowed as well, but on a
     phone your first touch to move the map IS a tap, so the pin landed under your
     finger before you could scroll. The crosshair plus Place here is the single way in. */
  if(tool === "mark"){
    drag = {mode:"pan", px, py, tx:view.tx, ty:view.ty, moved:false, click:null};
    return;
  }

  const hp = hitPin(px, py);
  if(hp){
    selPin = hp.id; selT.clear(); primary = null; anchors = [];
    drag = {mode:"pin", id:hp.id, ox:wx(px)-hp.x, oy:wy(py)-hp.y, moved:false};
    syncList(); renderInsp(); draw(); return;
  }
  if(tool === "edit"){
    const hv = hitAnyVertex(px, py);
    const t = hv ? hv.t : (primary && getT(primary));
    const vi = hv ? hv.i : -1;
    if(hv && hv.t.id !== primary){
      if(!selT.has(hv.t.id)) selT = new Set([hv.t.id]);
      primary = hv.t.id; anchors = []; syncList();
    }
    if(editMode === "del"){
      if(vi >= 0) return removePoint(t, vi);
      const any = hitTrail(px, py);
      if(any && any.t.id !== primary){ selectTrail(any.t.id, false); return; }
      return toast("Tap a point on the line.");
    }
    if(editMode === "add"){
      const ht2 = hitTrail(px, py);
      if(ht2){
        if(ht2.t.id !== primary) selectTrail(ht2.t.id, false);
        const tt = getT(ht2.t.id);
        push(); tt.p.splice(ht2.i+1, 0, atScreen(px, py));
        anchors = [ht2.i+1];
        drag = {mode:"vertex", id:tt.id, i:ht2.i+1, moved:false, pushed:true};
        return after("Point added — drag to place it.");
      }
      return toast("Tap on a line where the point should go.");
    }
    if(t && vi >= 0){
      if(e.altKey || e.ctrlKey || e.metaKey) return removePoint(t, vi);
      drag = {mode:"vertex", id:t.id, i:vi, moved:false, pushed:false};
      return;
    }
  }
  const ht = hitTrail(px, py);
  drag = {mode:"pan", px, py, tx:view.tx, ty:view.ty, moved:false,
          click:{hit:ht, shift:e.shiftKey, fromPan:tool === "pan"}};
});

function onMove(e){
  if(!D) return;
  const [px, py] = evXY(e);
  if(ptrs.has(e.pointerId)) ptrs.set(e.pointerId, [px, py]);
  const ll = worldToLL(wx(px), wy(py));
  document.getElementById("coord").textContent = fmtLL(ll[0], ll[1]);
  if(ptrs.size === 2 && pinch){
    const [a,b] = [...ptrs.values()];
    const d = Math.hypot(a[0]-b[0], a[1]-b[1]);
    const nk = Math.max(.12, Math.min(16, pinch.k * d / pinch.d)), f = nk / pinch.k;
    view.k = nk;
    view.tx = pinch.cx - (pinch.cx - pinch.tx)*f;
    view.ty = pinch.cy - (pinch.cy - pinch.ty)*f;
    draw(); return;
  }
  if(!drag) return;
  if(drag.mode === "pan"){
    if(Math.abs(px-drag.px) > 3 || Math.abs(py-drag.py) > 3) drag.moved = true;
    view.tx = drag.tx + (px-drag.px); view.ty = drag.ty + (py-drag.py); draw();
  }else if(drag.mode === "erase"){ eraseBox.x1 = px; eraseBox.y1 = py; draw(); }
  else if(drag.mode === "pin"){
    const p = pins.find(x => x.id === drag.id);
    if(p){ p.x = wx(px)-drag.ox; p.y = wy(py)-drag.oy; drag.moved = true; draw(); }
  }else if(drag.mode === "vertex"){
    const t = getT(drag.id); if(!t) return;
    if(!drag.pushed){ push(); drag.pushed = true; }
    t.p[drag.i] = atScreen(px, py); drag.moved = true; draw();
  }
}
window.addEventListener("pointermove", onMove, {passive:true});
window.addEventListener("mousemove", e => { if(drag && e.buttons) onMove(e); });

function endPtr(e){
  ptrs.delete(e.pointerId);
  if(ptrs.size < 2) pinch = null;
  if(drag){
    if(drag.mode === "erase" && eraseBox){
      const b = {x0:Math.min(eraseBox.x0, eraseBox.x1), x1:Math.max(eraseBox.x0, eraseBox.x1),
                 y0:Math.min(eraseBox.y0, eraseBox.y1), y1:Math.max(eraseBox.y0, eraseBox.y1)};
      const shift = eraseBox.shift; eraseBox = null;
      if(b.x1-b.x0 > 6 && b.y1-b.y0 > 6) applyErase(b, shift); else draw();
    }else if(drag.mode === "pan" && !drag.moved && drag.click){
      const c = drag.click;
      if(c.hit){ selectTrail(c.hit.t.id, c.shift); if(c.fromPan) setTool("edit"); }
      else if(!c.shift) clearSel();
    }else if(drag.mode === "vertex" && !drag.moved){
      const i = drag.i;
      if(anchors.length >= 2) anchors = [i];
      else if(anchors.includes(i)) anchors = anchors.filter(a => a !== i);
      else anchors.push(i);
      renderInsp(); draw();
    }else if(drag.moved){ saveState(); renderInsp(); }
  }
  drag = null;
}
window.addEventListener("pointerup", endPtr);
window.addEventListener("pointercancel", endPtr);
window.addEventListener("mouseup", e => { if(drag) endPtr(e); });

cv.addEventListener("dblclick", e => {
  if(!D) return;
  if(tool === "draw") return finishDraw();
  if(tool === "edit" && primary){
    const t = getT(primary), [dx2, dy2] = evXY(e), ht = hitTrail(dx2, dy2);
    if(t && ht && ht.t.id === t.id){
      push(); t.p.splice(ht.i+1, 0, atScreen(dx2, dy2)); anchors = [ht.i+1];
      after("Point added.");
    }
  }
});
cv.addEventListener("wheel", e => {
  if(!D) return;
  e.preventDefault();
  const f = Math.exp(-e.deltaY * .0016);
  const nk = Math.max(.12, Math.min(16, view.k*f)), r = nk/view.k;
  const [wxp, wyp] = evXY(e);
  view.tx = wxp - (wxp-view.tx)*r; view.ty = wyp - (wyp-view.ty)*r;
  view.k = nk; draw();
}, {passive:false});

function finishDraw(){
  if(!draft) return;
  const pts = draft.pts;
  if(pts.length < 2){ draft = null; setTool("pan"); return draw(); }
  push();
  if(draft.redraw){
    const t = getT(draft.redraw.id);
    if(t) t.p = t.p.slice(0, draft.redraw.i+1).concat(pts, t.p.slice(draft.redraw.j));
    draft = null; anchors = []; setTool("edit"); return after("Stretch redrawn.");
  }
  if(draft.extend){
    const t = getT(draft.extend.id);
    if(t){
      t.p = draft.extend.end ? t.p.concat(pts.slice(1)) : pts.slice(1).reverse().concat(t.p);
      selT = new Set([t.id]); primary = t.id;
    }
    draft = null; setTool("edit"); return after("Line extended.");
  }
  const t = {id:newId("n"), p:pts.slice(), name:"", kind:"trail"};
  trails.push(t); selT = new Set([t.id]); primary = t.id;
  draft = null; setTool("edit"); after("Trail added.");
}

window.addEventListener("keydown", e => {
  const tag = (e.target.tagName || "").toLowerCase();
  if(tag === "input" || tag === "textarea" || tag === "select" || !D) return;
  const k = e.key.toLowerCase();
  if((e.ctrlKey || e.metaKey) && k === "z"){
    e.preventDefault();
    document.getElementById(e.shiftKey ? "redo" : "undo").click(); return;
  }
  if(e.key === "Escape"){
    if(draft){ draft = null; setTool("edit"); } else if(anchors.length) anchors = []; else clearSel();
    return draw();
  }
  if(e.key === "Enter" && tool === "draw") return finishDraw();
  if(e.key === "Delete" || e.key === "Backspace"){ e.preventDefault(); return opDeleteSel(); }
  if(e.key.startsWith("Arrow") && tool === "edit" && primary){
    const t = getT(primary); if(!t) return;
    const step = (e.shiftKey ? 10 : 1) / view.k;
    const d = {ArrowLeft:[-step,0], ArrowRight:[step,0], ArrowUp:[0,-step], ArrowDown:[0,step]}[e.key];
    if(!d) return;
    e.preventDefault();
    if(!arrowPushed){ push(); arrowPushed = true; setTimeout(() => {arrowPushed = false;}, 900); }
    if(anchors.length === 1){
      const p = t.p[anchors[0]];
      t.p[anchors[0]] = [p[0]+d[0], p[1]+d[1]];
    } else t.p = t.p.map(p => [p[0]+d[0], p[1]+d[1]]);
    saveState(); return draw();
  }
  if(k === "v") setTool("pan");
  if(k === "e") setTool("edit");
  if(k === "d") setTool("draw");
  if(k === "x") setTool("erase");
  if(k === "s" && span()) opStraighten();
  if(k === "a") setEditMode(editMode === "add" ? "move" : "add");
  if(k === "r") setEditMode(editMode === "del" ? "move" : "del");
});

/* ---------- tools ---------- */
const HINTS = {
  pan:"Drag to pan, pinch or scroll to zoom. Tap a trail to start editing it.",
  edit:"Tap a line to pick it up. Drag its points; tap two points to mark a stretch.",
  draw:"Tap along the route. Double-tap to finish. Start on a loose end to extend that line.",
  erase:"Drag a box over what isn't trail. Shift deletes whole lines.",
  mark:"Move the map so the crosshair sits where the pin goes, then press Place here. Mark here drops one at your GPS fix instead."
};
function setTool(t, keepDraft){
  tool = t;
  if(t !== "mark") placing = null;
  else if(!placing) placing = {what:"pin"};
  document.querySelectorAll("#tools .btn, #tools2 .btn").forEach(b => b.setAttribute("aria-pressed", String(b.dataset.tool === t)));
  document.getElementById("toolhint").textContent = HINTS[t];
  if(t !== "edit") editMode = "move";
  cv.classList.toggle("cross", t === "draw" || t === "mark" || t === "erase" || (t === "edit" && editMode !== "move"));
  if(t !== "draw" && !keepDraft) draft = null;
  syncPlacing(); renderInsp(); draw();
}

/* ---------- pins ---------- */
function dropPin(world, type, extra){
  push();
  const p = Object.assign({id:newId("p"), t:type, x:world[0], y:world[1], name:"", note:"",
                           when:new Date().toISOString().slice(0,10)}, extra || {});
  if(DIRECTIONAL.has(type)){ p.dir = 0; p.count = 1; p.sexage = "unknown"; p.tod = todNow(); }
  if(type === "stand") p.winds = [];
  pins.push(p); selPin = p.id; selT.clear(); primary = null;
  after(null);
  return p;
}
function todNow(){
  const h = new Date().getHours();
  return h < 7 ? "first light" : h < 11 ? "morning" : h < 15 ? "midday"
       : h < 17 ? "afternoon" : h < 19 ? "last light" : "after dark";
}

/* ---------- GPS ---------- */
function setGPS(on){
  gpsOn = on;
  document.getElementById("gpsbtn").setAttribute("aria-pressed", String(on));
  const en = id => document.getElementById(id).disabled = !on;
  en("markhere"); en("avgbtn"); en("recbtn");
  if(!on){
    if(watchId != null) navigator.geolocation.clearWatch(watchId);
    watchId = null; fix = null;
    if(recording) stopRecording();
    return draw();
  }
  if(!navigator.geolocation){ toast("This browser has no location access."); return setGPS(false); }
  watchId = navigator.geolocation.watchPosition(onFix, err => {
    toast(err.code === 1 ? "Location permission denied." : "No GPS fix yet.");
  }, {enableHighAccuracy:true, maximumAge:2000, timeout:20000});
}
function onFix(pos){
  fix = {lat:pos.coords.latitude, lon:pos.coords.longitude,
         acc:pos.coords.accuracy || 99, t:pos.timestamp};
  if(averaging) averaging.samples.push(fix);
  if(recording && fix.acc <= 25){
    const w = llToWorld(fix.lon, fix.lat);
    const last = recording.pts[recording.pts.length-1];
    if(!last || Math.hypot(w[0]-last[0], w[1]-last[1]) * MPP() > 2) recording.pts.push(w);
  }
  document.getElementById("coord").textContent =
    fmtLL(fix.lon, fix.lat) + "  " + fmtAcc(fix.acc);
  draw();
}
function needFix(){
  if(!fix){ toast("Waiting on a GPS fix."); return false; }
  return true;
}
document.getElementById("gpsbtn").onclick = () => setGPS(!gpsOn);
document.getElementById("markhere").onclick = () => {
  if(!needFix()) return;
  const p = dropPin(llToWorld(fix.lon, fix.lat), document.getElementById("pintype").value,
                    {acc:Math.round(fix.acc)});
  toast("Dropped at " + fmtAcc(fix.acc) + ". Fill in the details.");
  centerOn(p.x, p.y);
};
document.getElementById("avgbtn").onclick = function(){
  if(averaging){ finishAverage(); return; }
  if(!needFix()) return;
  averaging = {samples:[], until:Date.now()+30000};
  const btn = this;
  const tick = () => {
    if(!averaging) return;
    const left = Math.ceil((averaging.until - Date.now())/1000);
    if(left <= 0) return finishAverage();
    btn.textContent = "Hold " + left + "s";
    setTimeout(tick, 250);
  };
  toast("Stand still. Averaging fixes for 30 seconds.");
  tick();
};
function finishAverage(){
  const s = averaging ? averaging.samples : [];
  averaging = null;
  document.getElementById("avgbtn").textContent = "Hold 30s";
  if(!s.length) return toast("No fixes collected.");
  const good = s.filter(f => f.acc <= 30).length ? s.filter(f => f.acc <= 30) : s;
  const lat = good.reduce((a,f) => a+f.lat, 0)/good.length;
  const lon = good.reduce((a,f) => a+f.lon, 0)/good.length;
  const acc = good.reduce((a,f) => a+f.acc, 0)/good.length / Math.sqrt(good.length);
  const p = dropPin(llToWorld(lon, lat), document.getElementById("pintype").value,
                    {acc:Math.round(acc*10)/10, averaged:good.length});
  toast("Averaged " + good.length + " fixes — about " + fmtAcc(acc) + ".");
  centerOn(p.x, p.y);
}
document.getElementById("recbtn").onclick = function(){
  if(recording) return stopRecording();
  if(!needFix()) return;
  recording = {pts:[], start:Date.now()};
  this.setAttribute("aria-pressed", "true"); this.textContent = "Stop";
  toast("Recording. Keep the screen on while you walk.");
};
function stopRecording(){
  const btn = document.getElementById("recbtn");
  btn.setAttribute("aria-pressed", "false"); btn.textContent = "Record";
  const pts = recording ? recording.pts : [];
  recording = null;
  if(pts.length < 3){ walkSpan = null; draw(); return toast("Too few fixes to keep."); }
  if(walkSpan) return walkReplace(pts);
  push();
  const line = rdp(pts, 3 / MPP());
  const t = {id:newId("w"), p:line.map(unnudged), name:"", kind:"trail"};
  trails.push(t); selT = new Set([t.id]); primary = t.id;
  after("Walked line saved — " + fmtDist(lenOf(t.p)) + ". Name it, or use it to replace an old line.");
}
function centerOn(x, y){
  /* Centre on the visible map, not the canvas, so a point you centre on lands
     under the crosshair rather than behind the panel. */
  const c = mapCentre();
  view.tx = c[0] - x*view.k; view.ty = c[1] - y*view.k; draw();
}

/* ---------- weather (National Weather Service, free, no key) ----------
   Worth being honest about what these numbers are. "Now" is the first hour of
   the gridded hourly forecast, not a measurement: a ~2.5 km square smoothed by
   a model. Only the pressure below is a real instrument reading, and the nearest
   station is likely 20-odd miles off at Dothan. Good enough for trend and
   direction; not good enough to tell you what the wind is doing in your timber.

   WXV is a shape version. Build 19 cached 12 hourly rows, which is not enough to
   reach tomorrow morning, so a cache written by an older build has to be thrown
   away rather than quietly producing a short forecast. */
const WXV = 2;
async function getWeather(){
  const cached = await DB.get("wx");
  if(cached && cached.now) LASTWX = {deg:WINDDEG[cached.now.dir] ?? null, dir:cached.now.dir || ""};
  const fresh = cached && cached.v === WXV && (Date.now() - cached.at < 45*60*1000);
  if(fresh) return cached;
  const c = D.center || worldToLL(D.w/2, D.h/2);
  try{
    const pr = await fetch("https://api.weather.gov/points/" + c[1].toFixed(4) + "," + c[0].toFixed(4));
    if(!pr.ok) throw 0;
    const pj = await pr.json();
    const hr = await fetch(pj.properties.forecastHourly);
    if(!hr.ok) throw 0;
    const hj = await hr.json();
    const now = hj.properties.periods[0];
    /* 48 hours, not 12: the forecast mode has to be able to reach tomorrow
       morning from late tonight, and the extra rows cost a few KB. */
    const next = hj.properties.periods.slice(0, 48).map(p => ({
      t:p.startTime, temp:p.temperature, unit:p.temperatureUnit,
      wind:p.windSpeed, dir:p.windDirection, sky:p.shortForecast
    }));
    let press = null;
    try{
      const st = await fetch(pj.properties.observationStations);
      const sj = await st.json();
      const ob = await fetch(sj.features[0].id + "/observations/latest");
      const oj = await ob.json();
      const pa = oj.properties.barometricPressure;
      if(pa && pa.value) press = +(pa.value/3386.39).toFixed(2);   // Pa -> inHg
    }catch(_){}
    /* Keep a short rolling history of pressure readings. A single number tells
       you nothing; the direction it is moving is one of the few weather signals
       that actually predicts deer movement, and nobody else is going to store it
       for us offline. 24 readings at 45 min apart covers about 18 hours. */
    let hist = (cached && cached.hist) || [];
    if(press !== null){
      hist = hist.concat([{at:Date.now(), p:press}]).slice(-24);
    }
    const wx = {v:WXV, at:Date.now(), press, hist,
                now:{temp:now.temperature, unit:now.temperatureUnit,
                     wind:now.windSpeed, dir:now.windDirection, sky:now.shortForecast}, next};
    await DB.set("wx", wx);
    LASTWX = {deg:WINDDEG[wx.now.dir] ?? null, dir:wx.now.dir || ""};
    return wx;
  }catch(_){ return cached || null; }
}

/* Needs two readings at least 90 min apart before it will claim a direction.
   Below 0.02 inHg it says steady rather than inventing a trend out of noise. */
function pressureTrend(wx){
  const h = (wx && wx.hist) || [];
  if(h.length < 2) return null;
  const last = h[h.length - 1];
  let first = null;
  for(let i = h.length - 2; i >= 0; i--){
    if(last.at - h[i].at >= 90*60000){ first = h[i]; break; }
  }
  if(!first) return null;
  const d = last.p - first.p, hrs = (last.at - first.at) / 36e5;
  const over = " over " + (hrs < 1.5 ? "90 min" : Math.round(hrs) + "h");
  if(Math.abs(d) < 0.02) return "steady" + over;
  const word = d < 0 ? "falling" : "rising";
  const read = d < -0.06 ? " — a drop like that is the best thing on this page"
             : d >  0.06 ? " — a sharp rise usually means they moved before you got there"
             : "";
  return word + " " + Math.abs(d).toFixed(2) + " inHg" + over + read;
}

/* ---------- season, rut and the legal calendar ----------
   Centerfire rifle only. Archery, muzzleloader and youth dates are deliberately
   absent because Steven hunts his own land with a rifle, and showing him a
   season he does not hunt is how an app teaches you to stop reading its banner.

   Henry County is Zone A. The either-sex / bucks-only splits ADCNR publishes
   apply to PUBLIC land and to dog hunting. On privately owned or leased land,
   stalk hunting, the season is either sex the whole way through. Getting that
   backwards would tell him "bucks only" on a day he can legally take a doe,
   which is the expensive direction to be wrong in.

   Dates are republished every licence year and this app has to work with no
   signal, so they are baked in with a stamp rather than fetched. Check them
   against the current digest each summer. */
const SEASON = {
  stamp: "2026–27 licence year",
  zone:  "Zone A (Henry Co.) · gun, stalk hunting, privately owned or leased land",
  open:  "2026-11-21",
  close: "2027-02-10",
  eitherSex: true
};

/* ADCNR's 2022 rut map: a spatial analysis of conception dates collected by WFF
   biologists at herd health checks, 1995–2019. Real measured data, not folklore.
   Breeding is photoperiod-locked, so the window holds year to year — it is
   daylight that starts it, not a cold front. ADCNR also puts nearly all breeding
   in a well-managed herd inside a 14–20 day span, which is what this is.

   Henry County carries no sample marker of its own on that map. Its window is
   read off the shading of the counties around it, so treat the edges as soft. */
const RUT = {
  from: "01-09", to: "01-24",
  source: "ADCNR 2022 rut map, from 1995–2019 conception data",
  caveat: "interpolated from neighbouring counties — Henry has no sample of its own, so give it a few days either side"
};

const MON = ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"];
const ymdOf = d => d.getFullYear() + "-" + String(d.getMonth()+1).padStart(2,"0") +
                   "-" + String(d.getDate()).padStart(2,"0");
const dayDiff = (a, b) => Math.round((Date.parse(b + "T00:00:00Z") - Date.parse(a + "T00:00:00Z")) / 864e5);
const fmtMD = s => { const p = s.split("-"); return +p[2] + " " + MON[+p[1]-1]; };
const plural = (n, w) => n + " " + w + (n === 1 ? "" : "s");

function seasonState(now){
  const t = ymdOf(now);
  if(t < SEASON.open)  return {open:false, phase:"before", days:dayDiff(t, SEASON.open)};
  if(t > SEASON.close) return {open:false, phase:"after",  days:dayDiff(SEASON.close, t)};
  return {open:true, phase:"in", day:dayDiff(SEASON.open, t) + 1,
          total:dayDiff(SEASON.open, SEASON.close) + 1, left:dayDiff(t, SEASON.close)};
}

/* The rut falls in January, which is the back half of a season that starts in
   November. Anchor it to the year the season closes in, not the year it opens. */
function rutWindow(){
  const y = SEASON.close.slice(0, 4);
  return {from:y + "-" + RUT.from, to:y + "-" + RUT.to};
}
function rutState(now){
  const w = rutWindow(), t = ymdOf(now);
  if(t < w.from) return {phase:"before", days:dayDiff(t, w.from), from:w.from, to:w.to};
  if(t > w.to)   return {phase:"after",  days:dayDiff(w.to, t),   from:w.from, to:w.to};
  return {phase:"in", day:dayDiff(w.from, t) + 1, from:w.from, to:w.to};
}

function seasonLines(now){
  const s = seasonState(now), r = rutState(now), L = [];
  if(s.open){
    L.push("SEASON OPEN — centerfire rifle, day " + s.day + " of " + s.total +
           ", closes " + fmtMD(SEASON.close) + " (" + plural(s.left, "day") + " left). Either sex throughout.");
  }else if(s.phase === "before"){
    L.push("!! SEASON CLOSED — centerfire rifle opens " + fmtMD(SEASON.open) +
           ", " + plural(s.days, "day") + " away. Everything below is scouting, not a licence to shoot.");
  }else{
    L.push("!! SEASON CLOSED — centerfire rifle closed " + fmtMD(SEASON.close) +
           ", " + plural(s.days, "day") + " ago. Next year's dates land in the summer digest.");
  }
  L.push("   " + SEASON.zone);
  L.push("   Dates as of the " + SEASON.stamp + " — confirm against the current digest.");
  if(r.phase === "in")
    L.push("   RUT: day " + r.day + " of the expected window (" + fmtMD(r.from) + "–" + fmtMD(r.to) + "). This is the slice to burn vacation on.");
  else if(r.phase === "before")
    L.push("   RUT: expected " + fmtMD(r.from) + "–" + fmtMD(r.to) + ", " + plural(r.days, "day") + " out.");
  else
    L.push("   RUT: expected window " + fmtMD(r.from) + "–" + fmtMD(r.to) + " has passed (" + plural(r.days, "day") + " ago).");
  L.push("   Rut source: " + RUT.source + "; " + RUT.caveat + ".");
  return L;
}

/* ---------- the next huntable window ----------
   The report should always point at the next time you can legally be in a tree,
   never at the one you just missed.

     midnight   → 11:00        this morning, through 11:00
     11:00      → last light    this evening, through last light
     last light → midnight      tomorrow morning, through 11:00

   The evening boundary rides on legal light rather than a fixed clock hour, so
   it walks forward through the season the way the deer do. */
function legalLight(sun){
  return {on:  sun.sunrise ? new Date(sun.sunrise.getTime() - 30*60000) : null,
          off: sun.sunset  ? new Date(sun.sunset.getTime()  + 30*60000) : null};
}
function nextWindow(now, lat, lon){
  const sunToday = sunTimes(now, lat, lon);
  const ll = legalLight(sunToday);
  const eleven = new Date(now); eleven.setHours(11, 0, 0, 0);

  if(now < eleven){
    const from = ll.on && ll.on > now ? ll.on : now;
    return {label:"this morning", from, to:eleven, sun:sunToday, day:new Date(now), kind:"am"};
  }
  if(ll.off && now < ll.off)
    return {label:"this evening", from:now, to:ll.off, sun:sunToday, day:new Date(now), kind:"pm"};

  const tm = new Date(now.getTime() + 24*36e5);
  const sun2 = sunTimes(tm, lat, lon), ll2 = legalLight(sun2);
  const e2 = new Date(tm); e2.setHours(11, 0, 0, 0);
  return {label:"tomorrow morning", from:ll2.on || new Date(tm.setHours(6,0,0,0)),
          to:e2, sun:sun2, day:tm, kind:"am"};
}

/* ---------- scoring an hour ----------
   Deliberately transparent: every point added or taken away comes back out as a
   phrase, so the report can show its work instead of handing down a number.
   Nothing here is a model. It is a checklist written down. */
function parseMph(s){
  const m = /(\d+)\s*(?:to\s*(\d+))?\s*mph/i.exec(s || "");
  if(!m) return null;
  return m[2] ? Math.round((+m[1] + +m[2]) / 2) : +m[1];
}
const to8 = d => (d && WINDDEG[d] !== undefined) ? degToCompass(WINDDEG[d]) : "";

/* which stands each 8-point wind opens up */
function standWindIndex(){
  const idx = {};
  for(const p of pins.filter(x => x.t === "stand" || x.t === "blind"))
    for(const w of (p.winds || []))
      (idx[w] = idx[w] || []).push(p.name || "unnamed");
  return idx;
}

function scoreHour(p, win, idx){
  const t = new Date(p.t), temp = p.temp, mph = parseMph(p.wind);
  const d8 = to8(p.dir), sky = (p.sky || "").toLowerCase();
  let s = 50;
  /* Two lists, not one. A single "why" array reads as a list of reasons the hour
     is good, so "dead calm" landed in it looking like a selling point. Anything
     that costs points belongs in the second list, behind a "but". */
  const plus = [], minus = [];

  const mins = x => x ? Math.abs(t - x) / 60000 : 1e9;
  const nr = mins(win.sun.sunrise), ns = mins(win.sun.sunset);
  if(nr <= 90)                { s += 22; plus.push("first light"); }
  else if(ns <= 90)           { s += 22; plus.push("last light"); }
  else if(nr <= 150 || ns <= 150) s += 8;
  else                        { s -= 12; minus.push("mid-morning lull"); }

  if(temp <= 35)      { s += 14; plus.push(temp + "°"); }
  else if(temp <= 50) { s += 8; }
  else if(temp >= 70) { s -= 14; minus.push(temp + "°, too warm to move"); }

  if(mph === null){}
  else if(mph <= 1)  { s -= 10; minus.push("dead calm — your scent sits and they hear every step"); }
  else if(mph <= 10) { s += 10; plus.push(mph + " mph steady"); }
  else if(mph <= 15) { s -= 2;  minus.push(mph + " mph, getting busy"); }
  else               { s -= 16; minus.push(mph + " mph — too much, they bed"); }

  const suits = d8 && idx[d8] ? idx[d8] : null;
  if(suits){ s += 16; plus.push(d8 + " suits " + suits.join(" and ")); }
  else if(d8){ s -= 8; minus.push(d8 + " fits none of your stands"); }

  if(/thunder|heavy rain/.test(sky))      { s -= 25; minus.push("storm"); }
  else if(/rain|shower/.test(sky))        { s -= 6;  minus.push("wet"); }
  else if(/cloud|overcast/.test(sky))     { s += 6;  plus.push("overcast"); }

  return {score:Math.max(0, Math.min(100, Math.round(s))), plus, minus, t, mph, d8};
}

/* ---------- briefing / forecast for Claude ---------- */
async function buildBriefing(mode){
  mode = mode === "forecast" ? "forecast" : "current";
  const c = D.center || worldToLL(D.w/2, D.h/2);
  const now = new Date();
  const wx = await getWeather();
  const L = [];
  const calm = p => (!p.dir || /^0\s*mph/.test(p.wind || "")) ? "calm" : p.dir + " " + p.wind;

  L.push("HUNT " + (mode === "forecast" ? "FORECAST" : "BRIEFING") + " — " + (D.name || "property"));
  L.push("Pulled: " + now.toLocaleDateString() + " " + hhmm(now));
  L.push("Location: " + fmtLL(c[0], c[1]) +
         (D.relief_ft ? "  |  relief " + D.relief_ft[0] + "–" + D.relief_ft[1] + " ft" : ""));
  L.push("");
  for(const s of seasonLines(now)) L.push(s);
  L.push("");

  if(mode === "forecast"){
    const win = nextWindow(now, c[1], c[0]);
    const ll = legalLight(win.sun);
    const mn = moonInfo(win.day);
    L.push("FORECAST — " + win.label.toUpperCase() + ", " +
           win.day.toLocaleDateString(undefined, {weekday:"long", month:"short", day:"numeric"}));
    L.push("Sitting window: " + hhmm(win.from) + " to " + hhmm(win.to));
    L.push("Legal light that day: " + hhmm(ll.on) + " to " + hhmm(ll.off) +
           " (30 min either side of the sun — confirm against this year's regs)");
    L.push("Moon: " + mn.name + ", " + Math.round(mn.illum*100) + "% lit, day " + mn.age.toFixed(1) + " of cycle");

    if(!wx){
      L.push("");
      L.push("Weather: unavailable — no signal and nothing cached. Everything above is still good; fill the weather in yourself.");
    }else{
      const age = Math.round((Date.now() - wx.at) / 60000);
      L.push("Forecast age: " + (age < 2 ? "just fetched" : age + " min old") + " (NWS gridpoint)");
      if(wx.press){
        const tr = pressureTrend(wx);
        L.push("Pressure: " + wx.press + " inHg" + (tr ? ", " + tr : ", no trend yet — needs a second reading hours apart") +
               ". Station reading, not a grid value, so this one is measured.");
      }
      const idx = standWindIndex();
      const slack = 36e5;
      const rows = (wx.next || []).filter(p => {
        const t = new Date(p.t).getTime();
        return t >= win.from.getTime() - slack && t <= win.to.getTime();
      });
      if(!rows.length){
        L.push("");
        L.push("No hourly rows cover that window yet — the cached forecast does not reach it. Pull again closer to the day.");
      }else{
        const scored = rows.map(p => ({p, s:scoreHour(p, win, idx)}));
        const best = scored.slice().sort((a, b) => b.s.score - a.s.score).slice(0, 3);
        L.push("");
        L.push("BEST HOURS IN THAT WINDOW");
        let rank = 1;
        for(const b of best){
          const good = b.s.plus.length ? b.s.plus.join(", ") : "nothing much going for it";
          const bad  = b.s.minus.length ? "   but: " + b.s.minus.join(", ") : "";
          L.push("  " + rank++ + ". " + hhmm(b.s.t) + "  — " + b.s.score + "/100 — " + good + bad);
        }
        L.push("");
        L.push("FULL HOURLY");
        for(const {p, s} of scored)
          L.push("  " + hhmm(s.t).padStart(8) + "  " + (p.temp + "°").padStart(5) + "  " +
                 calm(p).padEnd(14) + "  " + (p.sky || "") + "   [" + s.score + "]");
        const t0 = rows[0].temp, t1 = rows[rows.length-1].temp;
        L.push("");
        L.push("Temp across the window: " + t0 + "° → " + t1 + "° (" +
               (t1 - t0 >= 0 ? "+" : "") + (t1 - t0) + "°). " +
               (t1 - t0 <= -6 ? "A drop like that is what moves them."
                              : t1 - t0 >= 3 ? "Rising — expect them late or not at all."
                                             : "Flat, which is the least helpful kind of sit."));
        L.push("Reminder on the wind: these are gridpoint numbers, roughly 2.5 km square. " +
               "On 120 acres of timber the wind at your stand will swirl off this. Trust it for direction, not for gospel.");
      }
    }
  }else{
    const sun = sunTimes(now, c[1], c[0]);
    const ll = legalLight(sun);
    const mn = moonInfo(now);
    L.push("RIGHT NOW");
    L.push("Light: dawn " + hhmm(sun.dawn) + ", sunrise " + hhmm(sun.sunrise) +
           ", sunset " + hhmm(sun.sunset) + ", dusk " + hhmm(sun.dusk));
    L.push("Moon: " + mn.name + ", " + Math.round(mn.illum*100) + "% lit, day " + mn.age.toFixed(1) + " of cycle");
    if(ll.on && ll.off)
      L.push("Legal light (AL: 30 min either side of the sun): " + hhmm(ll.on) + " to " + hhmm(ll.off) +
             " — confirm against this year's regs.");
    if(wx){
      const age = Math.round((Date.now() - wx.at) / 60000);
      L.push("Weather (NWS, " + (age < 2 ? "just now" : age + " min old") + "): " +
             wx.now.temp + "°" + wx.now.unit + ", wind " + calm(wx.now) + ", " + wx.now.sky +
             (wx.press ? ", pressure " + wx.press + " inHg" : ""));
      if(wx.press){
        const tr = pressureTrend(wx);
        if(tr) L.push("Pressure trend: " + tr + ".");
      }
      const endMs = (sun.sunset ? sun.sunset.getTime() : now.getTime()) + 30*60000;
      const rows = (wx.next || []).filter(p => {
        const t = new Date(p.t).getTime();
        return t >= now.getTime() - 36e5 && t <= endMs + 36e5;
      }).slice(0, 8);
      if(rows.length){
        L.push("Through last light: " +
          rows.map(p => new Date(p.t).getHours() + "h " + calm(p) + " " + p.temp + "°").join("; "));
        const t0 = rows[0].temp, t1 = rows[rows.length-1].temp;
        L.push("Temp trend over the sit: " + t0 + "° → " + t1 + "° (" +
               (t1 - t0 >= 0 ? "+" : "") + (t1 - t0) + "°). " +
               (t1 - t0 <= -6 ? "A falling temp like that is what moves them."
                              : t1 - t0 >= 3 ? "Rising — expect them late."
                                             : "Flat, which is the least helpful kind of evening."));
      }
    }else L.push("Weather: unavailable offline — add it yourself if you have it.");
  }

  L.push("");
  L.push("STANDS AND BLINDS");
  const stands = pins.filter(p => p.t === "stand" || p.t === "blind");
  if(!stands.length) L.push("  (none marked yet)");
  for(const p of stands)
    L.push("  • " + (p.name || "unnamed") + " @ " + fmtLL(...worldToLL(p.x, p.y)) +
           (p.winds && p.winds.length ? "  huntable on: " + p.winds.join(",") : "  (no wind notes)") +
           (p.note ? "  — " + p.note : ""));
  /* Terrain features are permanent facts about the ground, not things you saw on
     a date. Mixed into the sightings list they sorted to the top on an empty date
     and buried the actual sign, which is the opposite of useful. */
  const terrain = pins.filter(p => p.t === "terrain");
  if(terrain.length){
    L.push("");
    L.push("TERRAIN (standing features of the land, not sightings)");
    for(const p of terrain)
      L.push("  • " + (p.name || "unnamed") + " @ " + fmtLL(...worldToLL(p.x, p.y)) +
             (p.note ? " — " + p.note : ""));
  }
  L.push("");
  L.push("SIGN AND SIGHTINGS (newest first)");
  const obs = pins.filter(p => p.t !== "stand" && p.t !== "blind" && p.t !== "terrain")
    .sort((a, b) => (b.when || "").localeCompare(a.when || "")).slice(0, 60);
  if(!obs.length) L.push("  (none marked yet)");
  for(const p of obs){
    const bits = [(PINS[p.t] || PINS.note).label];
    if(p.name) bits.push('"' + p.name + '"');
    if(p.when) bits.push(p.when);
    if(p.tod) bits.push(p.tod);
    if(p.count > 1) bits.push(p.count + " deer");
    if(p.sexage && p.sexage !== "unknown") bits.push(p.sexage);
    if(typeof p.dir === "number") bits.push("moving " + degToCompass(p.dir) + " (" + p.dir + "°)");
    bits.push("@ " + fmtLL(...worldToLL(p.x, p.y)));
    if(p.acc) bits.push(fmtAcc(p.acc));
    L.push("  • " + bits.join(", ") + (p.note ? " — " + p.note : ""));
  }
  L.push("");
  L.push("TRAILS AND LINES (" + trails.length + " lines, " +
         fmtDist(trails.reduce((s, t) => s + lenOf(t.p), 0)) + " total)");
  const ranked = trails.map(t => ({t, L:lenOf(t.p)})).sort((a, b) => b.L - a.L);
  for(const o of ranked.slice(0, 14))
    L.push("  • " + (o.t.name || "unnamed") + " (" + (KINDS[o.t.kind] || KINDS.trail).label +
           ", " + fmtDist(o.L) + ")" +
           (o.t.kind === "route" && (o.t.stands || []).length
             ? "  [approach to " + o.t.stands.map(id => {
                 const p = pins.find(x => x.id === id); return p ? (p.name || "a stand") : "?";
               }).join(", ") + "]" : ""));
  if(ranked.length > 14) L.push("  • …and " + (ranked.length - 14) + " shorter lines");
  L.push("");
  L.push("SIT LOG (what each stand has actually produced this season)");
  const season = inSeason(sits);
  if(!season.length) L.push("  (no sits logged yet — so stand rankings below are guesswork)");
  const byStand = [...new Set(season.map(s => s.stand).filter(Boolean))]
    .map(id => ({id, p:pins.find(x => x.id === id), st:standStats(id)}))
    .sort((a, b) => b.st.per - a.st.per);
  for(const o of byStand)
    L.push("  • " + (o.p ? (o.p.name || "unnamed stand") : "deleted stand") + ": " +
           o.st.sits + (o.st.sits === 1 ? " sit" : " sits") + ", " + o.st.deer + " deer, " +
           o.st.per.toFixed(1) + " per sit, last sat " + o.st.days + "d ago" +
           (o.st.hot ? "  [PRESSURED — sat " + o.st.sits + "x recently]" : ""));
  for(const s of season.slice(0, 10))
    L.push("    - " + s.date + " " + (s.standName || "?") + " " + (s.in || "") + "-" + (s.out || "") +
           ", " + (s.seen || 0) + " deer" + (s.wind ? ", wind " + s.wind + " " + s.windSpeed : "") +
           (s.temp !== null && s.temp !== undefined ? ", " + s.temp + "°" : "") +
           (s.note ? " — " + s.note : ""));
  if(sitOpen) L.push("  (a sit is open right now at " + (sitOpen.standName || "an unset stand") + ")");

  L.push("");
  L.push(mode === "forecast"
    ? "Question: for that window, which stand, which hours, and how do I get in without blowing it out? " +
      "Weigh the sit log against the wind — a stand that has produced is worth less on a wind it cannot hold."
    : "Question: given the wind, light and what I've been seeing, where should I sit " +
      "this evening and in the morning, and how should I get in without blowing it out?");
  return L.join("\n");
}

/* ---------- import ---------- */
function parseGPX(text){
  const doc = new DOMParser().parseFromString(text, "application/xml");
  if(doc.querySelector("parsererror")) throw new Error("not valid GPX");
  const lines = [], pts = []; let dropped = 0;
  const good = el2 => {
    const h = el2.querySelector("hdop"), acc = h ? parseFloat(h.textContent)*5 : null;
    return acc === null || !isFinite(acc) || acc <= 20;
  };
  for(const seg of doc.querySelectorAll("trkseg")){
    const run = [];
    for(const p of seg.querySelectorAll("trkpt")){
      if(!good(p)){ dropped++; continue; }
      const la = parseFloat(p.getAttribute("lat")), lo = parseFloat(p.getAttribute("lon"));
      if(isFinite(la) && isFinite(lo)) run.push(llToWorld(lo, la));
    }
    if(run.length >= 2) lines.push(run);
  }
  for(const r of doc.querySelectorAll("rte")){
    const run = [];
    for(const p of r.querySelectorAll("rtept")){
      const la = parseFloat(p.getAttribute("lat")), lo = parseFloat(p.getAttribute("lon"));
      if(isFinite(la) && isFinite(lo)) run.push(llToWorld(lo, la));
    }
    if(run.length >= 2) lines.push(run);
  }
  for(const w of doc.querySelectorAll("gpx > wpt")){
    const la = parseFloat(w.getAttribute("lat")), lo = parseFloat(w.getAttribute("lon"));
    if(!isFinite(la) || !isFinite(lo)) continue;
    const n = w.querySelector("name"), xy = llToWorld(lo, la);
    pts.push({x:xy[0], y:xy[1], name:n ? n.textContent.trim() : ""});
  }
  return {lines, pts, dropped};
}
function parseGeoJSON(text){
  const g = JSON.parse(text), lines = [], pts = [];
  for(const f of (g.type === "FeatureCollection" ? g.features : [g])){
    const gm = f.geometry || f; if(!gm) continue;
    const pr = f.properties || {};
    const nm = pr.name || pr.Name || "";
    if(gm.type === "LineString")
      lines.push(Object.assign(gm.coordinates.map(c => llToWorld(c[0], c[1])), {meta:{name:nm, kind:pr.type}}));
    else if(gm.type === "MultiLineString")
      for(const l of gm.coordinates) lines.push(l.map(c => llToWorld(c[0], c[1])));
    else if(gm.type === "Point"){
      if(pr.kind === "parcel") continue;
      const xy = llToWorld(gm.coordinates[0], gm.coordinates[1]);
      pts.push({x:xy[0], y:xy[1], name:nm, props:pr});
    }
  }
  return {lines:lines.filter(l => l.length >= 2), pts, dropped:0};
}
// Rebuild a full pin from exported GeoJSON properties, so phone -> Mac keeps everything.
function pinFromProps(x, y, pr){
  pr = pr || {};
  const t = PINS[pr.kind] ? pr.kind : "note";
  const p = {id:newId("p"), t, x, y, name:pr.name || "", note:pr.note || "",
             when:pr.date || "", acc:pr.accuracy_m || undefined};
  if(DIRECTIONAL.has(t)){
    p.dir = typeof pr.heading_deg === "number" ? pr.heading_deg : 0;
    p.count = pr.count || 1;
    p.sexage = pr.what || "unknown";
    p.tod = pr.time_of_day || "";
  }
  if(t === "stand") p.winds = Array.isArray(pr.winds) ? pr.winds : [];
  return p;
}
const idlg = document.getElementById("importdlg");
document.getElementById("importbtn").onclick = () => document.getElementById("filein").click();
document.getElementById("filein").onchange = async e => {
  const files = [...e.target.files]; e.target.value = "";
  if(!files.length) return;
  let lines = [], pts = [], dropped = 0;
  for(const f of files){
    try{
      const text = await f.text();
      if(/"huntmap-state\/1"/.test(text)){        // a backup: replace everything
        const b = JSON.parse(text);
        push();
        trails = (b.trails || []).map((t,i) => ({id:t.id || ("b"+i), p:t.p,
                  name:t.name || "", kind:KINDS[t.kind] ? t.kind : "trail"}));
        pins = b.pins || [];
        sits = b.sits || [];
        sitOpen = b.sitOpen || null;
        nudge = b.nudge || {dx:0, dy:0, rot:0, scl:1};
        selT.clear(); primary = null; selPin = null; anchors = [];
        nudgeStat(); after("Backup restored \u2014 " + trails.length + " lines, " + pins.length + " pins.");
        return;
      }
      const r = /^\s*[[{]/.test(text) ? parseGeoJSON(text) : parseGPX(text);
      lines = lines.concat(r.lines); pts = pts.concat(r.pts); dropped += r.dropped;
    }catch(err){ toast(f.name + ": " + err.message); }
  }
  if(!lines.length && !pts.length) return toast("Nothing readable in that file.");
  const inMap = p => p[0] > -400 && p[0] < D.w+400 && p[1] > -400 && p[1] < D.h+400;
  let offmap = 0;
  lines = lines.map(l => {
    const thinned = rdp(l, 3 / MPP());
    thinned.meta = l.meta;                 // rdp builds a new array; carry the name and type over
    return thinned;
  }).filter(l => {
    if(l.filter(inMap).length / l.length < .3){ offmap++; return false; }
    return true;
  });
  pts = pts.filter(p => { const ok = inMap([p.x, p.y]); if(!ok) offmap++; return ok; });
  pending = {lines, pts};
  const total = lines.reduce((s,l) => s+lenOf(l), 0);
  const bits = [lines.length + " track" + (lines.length === 1 ? "" : "s") +
                (total ? " · " + fmtDist(total) : "")];
  if(pts.length) bits.push(pts.length + " waypoint" + (pts.length === 1 ? "" : "s"));
  const named = lines.filter(l => l.meta && l.meta.name).length;
  const typed = pts.filter(p => p.props && PINS[p.props.kind]).length;
  if(named) bits.push(named + " with names");
  if(typed) bits.push(typed + " typed pins");
  if(dropped) bits.push(dropped + " poor fixes dropped");
  if(offmap) bits.push(offmap + " off this map, ignored");
  document.getElementById("importsummary").textContent = bits.join(" · ");
  document.getElementById("imp-replace").disabled = !primary || lines.length !== 1;
  document.getElementById("imp-pins").disabled = !pts.length;
  document.getElementById("imp-add").disabled = !lines.length;
  idlg.showModal();
};
document.getElementById("imp-add").onclick = () => {
  if(!pending) return;
  push();
  for(const l of pending.lines){
    const m = l.meta || {};
    trails.push({id:newId("g"), p:l.slice(), name:m.name || "",
                 kind:KINDS[m.kind] ? m.kind : "trail"});
  }
  const n = pending.lines.length; idlg.close(); pending = null;
  after(n + " track" + (n === 1 ? "" : "s") + " added.");
};
document.getElementById("imp-replace").onclick = () => {
  if(!pending || !primary) return;
  const t = getT(primary); if(!t) return;
  push(); t.p = pending.lines[0]; anchors = []; idlg.close(); pending = null;
  after("“" + (t.name || "That line") + "” replaced with the walked track.");
};
document.getElementById("imp-pins").onclick = () => {
  if(!pending) return;
  push();
  for(const p of pending.pts)
    pins.push(p.props ? pinFromProps(p.x, p.y, p.props)
                      : {id:newId("p"), t:"note", x:p.x, y:p.y, name:p.name || "", note:"Imported waypoint"});
  const n = pending.pts.length; idlg.close(); pending = null;
  after(n + " waypoint" + (n === 1 ? "" : "s") + " added as pins.");
};

/* ---------- export ---------- */
function geojson(){
  const fs = [];
  for(const t of trails) fs.push({type:"Feature",
    properties:{kind:"trail", type:t.kind || "trail", name:t.name || null, length_m:Math.round(lenOf(t.p))},
    geometry:{type:"LineString", coordinates:t.p.map(nudged).map(q => worldToLL(q[0], q[1]).map(v => +v.toFixed(6)))}});
  for(const p of pins){
    const pr = {kind:p.t, label:(PINS[p.t] || PINS.note).label, name:p.name || null, note:p.note || null,
                date:p.when || null, accuracy_m:p.acc || null};
    if(DIRECTIONAL.has(p.t)) Object.assign(pr, {heading_deg:p.dir, count:p.count, what:p.sexage, time_of_day:p.tod || null});
    if(p.t === "stand") pr.winds = p.winds || [];
    fs.push({type:"Feature", properties:pr,
      geometry:{type:"Point", coordinates:worldToLL(p.x, p.y).map(v => +v.toFixed(6))}});
  }
  for(const pc of (D.parcels || [])) fs.push({type:"Feature",
    properties:{kind:"parcel", parcel_id:pc.id, acres:pc.acres, address:pc.addr},
    geometry:{type:"Polygon", coordinates:[pc.p.map(q => worldToLL(q[0], q[1]).map(v => +v.toFixed(6)))]}});
  return {type:"FeatureCollection", features:fs};
}
const edlg = document.getElementById("exportdlg");
let exportName = "hunt-map.geojson";
function showExport(title, hint, text, filename){
  document.getElementById("exporttitle").textContent = title;
  document.getElementById("exporthint").textContent = hint;
  const ta = document.getElementById("exporttext");
  ta.value = text;
  /* Always open at the top. The season banner is the first thing on a report
     and the browser otherwise keeps the scroll position from the last one. */
  ta.scrollTop = 0;
  exportName = filename;
  document.getElementById("sharefile").hidden = !(navigator.canShare && navigator.canShare({files:[new File(["x"], "a.txt", {type:"text/plain"})]}));
  /* Only the hunt report shows the Now / Next sit switch. Everything else that
     borrows this dialog — backup, GeoJSON — gets it hidden again. */
  document.getElementById("reportmode").hidden = true;
  /* Re-rendering the report in place must not call showModal on an open dialog;
     that throws. */
  if(!edlg.open) edlg.showModal();
}
function backupBlob(){
  return {format:"huntmap-state/1", savedAt:new Date().toISOString(),
          map:(D && D.name) || "", trails, pins, sits, sitOpen, nudge, seedDone};
}
document.getElementById("backupbtn").onclick = () =>
  showExport("Backup", "Everything exactly as it is here. Send it to your other device and use Import to restore it.",
             JSON.stringify(backupBlob()), "hunt-backup.json");
document.getElementById("exportbtn").onclick = () =>
  showExport("Export GeoJSON", "Everything on the map as lat/long. Opens in onX, HuntStand, BaseCamp or QGIS.",
             JSON.stringify(geojson(), null, 1), "hunt-map.geojson");
/* The report has two modes and you can flip between them without leaving the
   dialog, which beats a chooser you have to answer before you have seen anything. */
let reportMode = "current";
async function showReport(mode){
  reportMode = mode === "forecast" ? "forecast" : "current";
  const fc = reportMode === "forecast";
  const txt = await buildBriefing(reportMode);
  showExport("Hunt report",
    fc ? "Conditions for your next sit. Copy this and paste it to Claude."
       : "Conditions right now. Copy this and paste it to Claude.",
    txt, fc ? "hunt-forecast.txt" : "hunt-briefing.txt");
  const row = document.getElementById("reportmode");
  row.hidden = false;
  document.getElementById("rm-now").setAttribute("aria-pressed", String(!fc));
  document.getElementById("rm-next").setAttribute("aria-pressed", String(fc));
}
document.getElementById("briefbtn").onclick = () => showReport("current");
document.getElementById("rm-now").onclick  = () => showReport("current");
document.getElementById("rm-next").onclick = () => showReport("forecast");
document.getElementById("copytext").onclick = async () => {
  const ta = document.getElementById("exporttext");
  try{ await navigator.clipboard.writeText(ta.value); toast("Copied."); }
  catch(_){ ta.focus(); ta.select(); toast("Press Ctrl/Cmd+C."); }
};
document.getElementById("savefile").onclick = () => {
  const blob = new Blob([document.getElementById("exporttext").value], {type:"application/json"});
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob); a.download = exportName;
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 5000);
};
document.getElementById("sharefile").onclick = async () => {
  const txt = document.getElementById("exporttext").value;
  try{ await navigator.share({files:[new File([txt], exportName, {type:"text/plain"})], title:exportName}); }
  catch(_){}
};
document.querySelectorAll("[data-close]").forEach(b => b.onclick = () => b.closest("dialog").close());
document.getElementById("keysbtn").onclick = () => document.getElementById("keysdlg").showModal();

/* ---------- inspector ---------- */
function el(tag, attrs, kids){
  const n = document.createElement(tag);
  for(const k in (attrs || {})){
    if(k === "class") n.className = attrs[k];
    else if(k === "disabled"){ if(attrs[k]) n.disabled = true; }
    else if(k.startsWith("on")) n.addEventListener(k.slice(2), attrs[k]);
    else n.setAttribute(k, attrs[k]);
  }
  for(const c of (kids || [])) n.appendChild(typeof c === "string" ? document.createTextNode(c) : c);
  return n;
}
const field = (label, input) => el("label", {class:"field"}, [el("span", {}, [label]), input]);

function renderInsp(){
  if((selPin || primary || selT.size) && typeof SHEET !== "undefined") SHEET.atLeast(1);
  const box = document.getElementById("insp"), body = document.getElementById("insp-body");
  body.textContent = "";
  if(selPin) return renderPin(box, body);
  if(!selT.size){ box.hidden = true; return; }
  box.hidden = false;
  if(selT.size > 1){
    document.getElementById("insp-title").textContent = selT.size + " lines picked";
    const tot = [...selT].reduce((s,id) => s + lenOf(getT(id).p), 0);
    body.append(
      el("div", {class:"stat"}, [fmtDist(tot)]),
      el("div", {class:"row g2"}, [
        el("button", {class:"btn sm", onclick:() => opSimplify(false)}, ["Smooth"]),
        el("button", {class:"btn sm", onclick:() => opSimplify(true)}, ["Straighten"]),
        el("button", {class:"btn sm danger", onclick:opDeleteSel, style:"grid-column:1/-1"}, ["Delete all " + selT.size])
      ]));
    return;
  }
  const t = getT(primary || [...selT][0]);
  if(!t){ box.hidden = true; return; }
  document.getElementById("insp-title").textContent = "Trail";
  const L = lenOf(t.p);
  const nameIn = el("input", {type:"text", value:t.name || "", placeholder:"e.g. Ridge road", list:"nameideas"});
  nameIn.addEventListener("input", () => { t.name = nameIn.value; saveState(); syncList(); draw(); });
  const kindSel = el("select", {});
  for(const k in KINDS){
    const o = el("option", {value:k}, [KINDS[k].label]);
    if(k === (t.kind || "trail")) o.selected = true;
    kindSel.appendChild(o);
  }
  kindSel.addEventListener("change", () => { t.kind = kindSel.value; saveState(); syncList(); draw(); });
  const hasSpan = anchors.length === 2, hasOne = anchors.length === 1;
  body.append(
    field("Name", nameIn),
    field("What it is", kindSel),
    el("div", {class:"stat"}, [fmtDist(L) + " · " + t.p.length + " points"]),
    el("div", {class:"sep"}),
    el("div", {class:"grp"}, ["Points"]),
    el("div", {class:"row g2"}, [
      el("button", {class:"btn sm", "aria-pressed":String(editMode === "move"), onclick:() => setEditMode("move")}, ["Move"]),
      el("button", {class:"btn sm", "aria-pressed":String(editMode === "add"), onclick:() => setEditMode("add")}, ["Add point"]),
      el("button", {class:"btn sm", "aria-pressed":String(editMode === "del"), onclick:() => setEditMode("del")}, ["Remove point"]),
      el("button", {class:"btn sm danger", disabled:!hasOne, onclick:removeMarkedPoint}, ["Drop marked"])
    ]),
    el("div", {class:"hint"}, [
      vertexGap(t) < 9 ? "Points are stacked at this zoom — pinch in before dragging one."
      : editMode === "add" ? "Tap the line to drop a point in, then drag it."
      : editMode === "del" ? "Tap any point to remove it."
      : "Drag points to move them."
    ]),
    el("div", {class:"sep"}),
    el("div", {class:"grp"}, ["Marked stretch"]),
    el("div", {class:"row g2"}, [
      el("button", {class:"btn sm", disabled:!hasSpan, onclick:opStraighten}, ["Straighten"]),
      el("button", {class:"btn sm", disabled:!hasSpan, onclick:opRedraw}, ["Redraw"]),
      el("button", {class:"btn sm danger", disabled:!hasSpan, onclick:opCut}, ["Cut out"]),
      el("button", {class:"btn sm", disabled:!hasSpan, onclick:opKeepSpan}, ["Keep only"])
    ]),
    el("div", {class:"row g2"}, [
      el("button", {class:"btn sm", disabled:!hasOne, onclick:opSplit}, ["Split here"]),
      el("button", {class:"btn sm", disabled:!hasOne, onclick:() => opTrim("start")}, ["Cut back"]),
      el("button", {class:"btn sm", disabled:!hasOne, onclick:() => opTrim("end")}, ["Cut forward"]),
      el("button", {class:"btn sm", disabled:!anchors.length, onclick:() => {anchors = []; renderInsp(); draw();}}, ["Clear marks"])
    ]),
    el("div", {class:"sep"}),
    el("div", {class:"grp"}, ["Whole line"]),
    el("div", {class:"row g2"}, [
      el("button", {class:"btn sm", onclick:() => opSimplify(false)}, ["Smooth"]),
      el("button", {class:"btn sm", onclick:() => opSimplify(true)}, ["Straighten"]),
      el("button", {class:"btn sm", onclick:opJoin}, ["Join nearest"]),
      el("button", {class:"btn sm danger", onclick:opDeleteSel}, ["Delete line"])
    ]));
}

function renderPin(box, body){
  const p = pins.find(x => x.id === selPin);
  if(!p){ selPin = null; box.hidden = true; return; }
  box.hidden = false;
  const spec = PINS[p.t] || PINS.note;
  document.getElementById("insp-title").textContent = spec.label;
  const nameIn = el("input", {type:"text", value:p.name || "", placeholder:spec.label});
  nameIn.addEventListener("input", () => { p.name = nameIn.value; saveState(); draw(); });
  body.append(field("Label", nameIn));
  const typeSel = el("select", {});
  for(const k in PINS){
    const o = el("option", {value:k}, [PINS[k].label]);
    if(k === p.t) o.selected = true;
    typeSel.appendChild(o);
  }
  typeSel.addEventListener("change", () => {
    p.t = typeSel.value;
    if(DIRECTIONAL.has(p.t) && typeof p.dir !== "number")
      Object.assign(p, {dir:0, count:1, sexage:"unknown", tod:p.tod || ""});
    if(p.t === "stand" && !p.winds) p.winds = [];
    saveState(); renderInsp(); draw();
  });
  body.append(field("Type", typeSel));

  if(DIRECTIONAL.has(p.t)){
    const dial = el("div", {class:"dial"});
    const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
    svg.setAttribute("width", "64"); svg.setAttribute("height", "64"); svg.setAttribute("viewBox", "0 0 62 62");
    svg.innerHTML =
      '<circle cx="31" cy="31" r="27" fill="none" stroke="var(--line)" stroke-width="1.5"></circle>' +
      '<text x="31" y="11" text-anchor="middle" font-size="9" font-family="Barlow Condensed,sans-serif" fill="var(--ink-2)">N</text>' +
      '<text x="31" y="58" text-anchor="middle" font-size="9" font-family="Barlow Condensed,sans-serif" fill="var(--ink-2)">S</text>' +
      '<text x="55" y="34" text-anchor="middle" font-size="9" font-family="Barlow Condensed,sans-serif" fill="var(--ink-2)">E</text>' +
      '<text x="7" y="34" text-anchor="middle" font-size="9" font-family="Barlow Condensed,sans-serif" fill="var(--ink-2)">W</text>' +
      '<line id="dl" x1="31" y1="31" x2="31" y2="10" stroke="var(--blaze)" stroke-width="3" stroke-linecap="round"></line>' +
      '<circle cx="31" cy="31" r="3" fill="var(--blaze)"></circle>';
    const num = el("input", {type:"number", min:"0", max:"359", step:"1", value:String(p.dir || 0)});
    const lbl = el("div", {class:"stat"}, [""]);
    function setDir(d){
      p.dir = ((Math.round(d) % 360) + 360) % 360;
      const a = (p.dir-90)*Math.PI/180, ln = svg.querySelector("#dl");
      ln.setAttribute("x2", (31+Math.cos(a)*21).toFixed(1));
      ln.setAttribute("y2", (31+Math.sin(a)*21).toFixed(1));
      num.value = p.dir; lbl.textContent = "heading " + degToCompass(p.dir);
      saveState(); draw();
    }
    const fromEvt = ev => {
      const r = svg.getBoundingClientRect();
      setDir(Math.atan2(ev.clientY-r.top-31, ev.clientX-r.left-31)*180/Math.PI + 90);
    };
    svg.addEventListener("pointerdown", ev => { svg.setPointerCapture(ev.pointerId); fromEvt(ev); });
    svg.addEventListener("pointermove", ev => { if(ev.buttons) fromEvt(ev); });
    num.addEventListener("input", () => setDir(Number(num.value) || 0));
    dial.append(svg, el("div", {style:"flex:1"}, [field("Which way they moved", num), lbl]));
    body.append(dial); setDir(p.dir || 0);

    const cnt = el("input", {type:"number", min:"1", step:"1", value:String(p.count || 1)});
    cnt.addEventListener("input", () => { p.count = Number(cnt.value) || 1; saveState(); });
    const sa = el("select", {});
    for(const v of ["unknown","doe","fawn","doe + fawns","young buck","mature buck","group"]){
      const o = el("option", {value:v}, [v]);
      if(v === (p.sexage || "unknown")) o.selected = true;
      sa.appendChild(o);
    }
    sa.addEventListener("change", () => { p.sexage = sa.value; saveState(); });
    const tod = el("select", {});
    for(const v of ["","first light","morning","midday","afternoon","last light","after dark"]){
      const o = el("option", {value:v}, [v || "—"]);
      if(v === (p.tod || "")) o.selected = true;
      tod.appendChild(o);
    }
    tod.addEventListener("change", () => { p.tod = tod.value; saveState(); });
    body.append(field("How many", cnt), field("What", sa), field("Time of day", tod));
  }
  if(p.t === "stand"){
    const grid = el("div", {class:"wind"});
    p.winds = p.winds || [];
    for(const w of WINDS){
      const b = el("button", {class:"btn sm", "aria-pressed":String(p.winds.includes(w))}, [w]);
      b.addEventListener("click", () => {
        const i = p.winds.indexOf(w);
        i < 0 ? p.winds.push(w) : p.winds.splice(i, 1);
        b.setAttribute("aria-pressed", String(i < 0)); saveState();
      });
      grid.appendChild(b);
    }
    body.append(field("Huntable on these winds", grid));
  }

  if(p.t === "stand" || p.t === "blind"){
    const st = standStats(p.id);
    body.append(el("div", {class:"stat"}, [
      st.sits ? st.sits + (st.sits === 1 ? " sit" : " sits") + " this season \u00b7 " + st.deer +
                " deer \u00b7 " + st.per.toFixed(1) + " per sit" +
                (st.days !== null ? " \u00b7 last sat " + st.days + "d ago" : "")
              : "No sits logged here yet."]));
    if(st.hot) body.append(el("div", {class:"risk"},
      ["Sat " + st.sits + " times and you were here " + st.days + " days ago. " +
       "Deer pattern you faster than you pattern them \u2014 this one wants resting."]));
    if(LASTWX && LASTWX.deg !== null){
      const risk = approachRisk(p, LASTWX.deg);
      if(risk) body.append(el("div", {class:"risk"}, [risk.text]));
    }
    const chk = el("input", {type:"date", value:p.lastCheck || ""});
    chk.addEventListener("input", () => { p.lastCheck = chk.value; saveState(); });
    body.append(field("Last inspected (ladders rot)", chk));

    const linked = trails.filter(t => t.kind === "route" && (t.stands || []).includes(p.id));
    const rrow = el("div", {class:"row"});
    rrow.append(el("button", {class:"btn sm", onclick:() => linkRoute(p)},
                   [linked.length ? "Link another route" : "Link an access route"]));
    for(const r of linked){
      const b = el("button", {class:"btn sm"}, [(r.name || "route") + " \u00d7"]);
      b.onclick = () => { r.stands = (r.stands || []).filter(x => x !== p.id); after("Route unlinked."); };
      rrow.append(b);
    }
    body.append(field("Access routes \u2014 the walk in", rrow));
  }

  if(p.t === "cam" || p.t === "camdeer"){
    const card = el("input", {type:"date", value:p.lastCard || ""});
    card.addEventListener("input", () => { p.lastCard = card.value; saveState(); });
    const batt = el("input", {type:"date", value:p.lastBatt || ""});
    batt.addEventListener("input", () => { p.lastBatt = batt.value; saveState(); });
    body.append(field("Card pulled", card), field("Battery changed", batt));
  }

  if(p.t === "kill"){
    const sex = el("select", {});
    for(const v of ["buck","doe"]){
      const o = el("option", {value:v}, [v]);
      if(v === (p.sex || "buck")) o.selected = true;
      sex.appendChild(o);
    }
    const pts = el("input", {type:"number", min:"0", max:"40", step:"1",
                             value:p.points === undefined ? "" : String(p.points),
                             placeholder:"any number"});
    const ptsField = field("Points", pts);
    const syncSex = () => {
      p.sex = sex.value;
      ptsField.hidden = p.sex === "doe";       // a doe carries no rack and no badge
      saveState(); draw();
    };
    sex.addEventListener("change", syncSex);
    pts.addEventListener("input", () => {
      p.points = pts.value === "" ? undefined : Math.max(0, Number(pts.value) || 0);
      saveState(); draw();
    });
    body.append(field("Sex", sex), ptsField); syncSex();

    /* where it stood, where it ran, where you found it. Useful once for the
       track; useful every year after for learning the exits. */
    const mark = (key, label) => {
      const has = Array.isArray(p[key]);
      const b = el("button", {class:"btn sm"},
                   [has ? label + " \u2713" : "Mark " + label.toLowerCase()]);
      b.onclick = () => {
        /* Arm the crosshair rather than grabbing a point behind your back. If GPS
           has a fix we centre on it first, so standing where it happened is still
           one tap — but you can pan off it, which matters when you are marking the
           hit site from fifty yards away with a rifle still in your hands. */
        if(fix) centerOn(...llToWorld(fix.lon, fix.lat));
        placing = {what:"recovery", pinId:p.id, key, label};
        setTool("mark");
      };
      return b;
    };
    const row = el("div", {class:"row"}, [mark("shotFrom","Shot from"), mark("hitAt","Hit"), mark("foundAt","Found")]);
    body.append(field("Shot and recovery", row));
    if(Array.isArray(p.shotFrom) && Array.isArray(p.hitAt))
      body.append(el("div", {class:"stat"}, ["Shot distance " +
        fmtDist(Math.hypot(p.shotFrom[0]-p.hitAt[0], p.shotFrom[1]-p.hitAt[1]) * MPP())]));
    if(Array.isArray(p.hitAt) && Array.isArray(p.foundAt))
      body.append(el("div", {class:"stat"}, ["Ran " +
        fmtDist(Math.hypot(p.hitAt[0]-p.foundAt[0], p.hitAt[1]-p.foundAt[1]) * MPP()) +
        " to " + degToCompass(Math.atan2(p.foundAt[0]-p.hitAt[0], -(p.foundAt[1]-p.hitAt[1]))*180/Math.PI)]));
  }
  const when = el("input", {type:"date", value:p.when || ""});
  when.addEventListener("input", () => { p.when = when.value; saveState(); });
  body.append(field("Date", when));
  const note = el("textarea", {placeholder:"What you saw, how you get in, anything worth remembering."});
  note.value = p.note || "";
  note.addEventListener("input", () => { p.note = note.value; saveState(); });
  body.append(field("Notes", note));
  const ll = worldToLL(p.x, p.y);
  body.append(el("div", {class:"stat"}, [fmtLL(ll[0], ll[1]) + (p.acc ? "  " + fmtAcc(p.acc) : "") +
      (p.averaged ? "  (" + p.averaged + " fixes averaged)" : "")]),
    el("div", {class:"row"}, [el("button", {class:"btn sm danger", onclick:opDeleteSel}, ["Delete pin"])]));
}


/* ================= sit log =================
   The thing that was missing. Pins record deer SEEN; without a record of sits
   there is no denominator, and the blank sits are where the information is.
   A sit with nothing seen has to cost one tap, or it never gets logged.        */
let LASTWX = {deg:null, dir:""};     // most recent NWS wind, for the approach check
const WINDDEG = {N:0, NNE:22, NE:45, ENE:68, E:90, ESE:113, SE:135, SSE:158,
                 S:180, SSW:203, SW:225, WSW:248, W:270, WNW:293, NW:315, NNW:338};
const SEASON_START = () => {            // Alabama season spans the new year
  const n = new Date(), y = n.getMonth() >= 6 ? n.getFullYear() : n.getFullYear()-1;
  return y + "-07-01";
};
const sitsFor = id => sits.filter(s => s.stand === id);
const inSeason = a => a.filter(s => (s.date || "") >= SEASON_START());

function standStats(id){
  const all = inSeason(sitsFor(id));
  const deer = all.reduce((n, s) => n + (s.seen || 0), 0);
  const last = all.map(s => s.date).sort().pop();
  const days = last ? Math.round((Date.now() - new Date(last+"T12:00").getTime())/86400000) : null;
  return {sits:all.length, deer, last, days,
          per: all.length ? deer/all.length : null,
          hot: all.length >= 3 && days !== null && days <= 7};   // sat out
}
function nearestStand(w){
  let best = null, bd = Infinity;
  for(const p of pins) if(p.t === "stand" || p.t === "blind"){
    const d = Math.hypot(p.x-w[0], p.y-w[1]);
    if(d < bd){ bd = d; best = p; }
  }
  return best;
}
async function startSit(){
  const w = fix ? llToWorld(fix.lon, fix.lat) : atScreen(...mapCentre());
  const st = nearestStand(w);
  const wx = await getWeather().catch(() => null);
  const now = new Date(), mn = moonInfo(now);
  sitOpen = {
    id:newId("s"), stand:st ? st.id : null, standName:st ? (st.name || "unnamed") : "",
    date:now.toISOString().slice(0,10), in:hhmm(now), out:"",
    wind:wx ? wx.now.dir : "", windSpeed:wx ? wx.now.wind : "",
    temp:wx ? wx.now.temp : null, sky:wx ? wx.now.sky : "",
    moon:Math.round(mn.illum*100), seen:0, note:""
  };
  saveState(); renderSits();
  toast(st ? "Sit started at " + (st.name || "the nearest stand") + "."
           : "Sit started. No stand nearby — pick one in the log.");
}
function endSit(){
  if(!sitOpen) return;
  sitOpen.out = hhmm(new Date());
  sits.unshift(sitOpen);
  const n = sitOpen.seen || 0;
  sitOpen = null;
  push(); saveState(); renderSits(); renderInsp();
  toast("Sit logged" + (n ? " — " + n + " deer." : " — nothing seen. That counts."));
}




/* ================= walk-and-replace a span =================
   Mark two points on a line, walk that stretch, and swap the walked track in.
   A raw GPS walk arrives with hundreds of points against a hand-drawn line's
   dozen, so it is simplified and the counts are shown BEFORE anything commits. */
let walkSpan = null;         // {tid, i, j} armed before recording starts

function armWalk(){
  const sp = span();
  if(!sp) return toast("Pick a line, then tap two points on it to mark the stretch.");
  walkSpan = {tid:sp.t.id, i:sp.i, j:sp.j};
  toast("Walk the stretch between those two points, then press Record again to stop.");
  if(!gpsOn) document.getElementById("gpsbtn").click();
  const rec = document.getElementById("recbtn");
  if(rec.getAttribute("aria-pressed") !== "true") rec.click();
}
function orientToAnchors(track, a, b){
  /* a track walked the other way round would fold the line back on itself */
  const d0 = Math.hypot(track[0][0]-a[0], track[0][1]-a[1]) +
             Math.hypot(track[track.length-1][0]-b[0], track[track.length-1][1]-b[1]);
  const d1 = Math.hypot(track[0][0]-b[0], track[0][1]-b[1]) +
             Math.hypot(track[track.length-1][0]-a[0], track[track.length-1][1]-a[1]);
  return d1 < d0 ? track.slice().reverse() : track;
}
function walkReplace(rawPts){
  const t = getT(walkSpan.tid);
  const {i, j} = walkSpan;
  walkSpan = null;
  if(!t || j >= t.p.length) return toast("That line changed while you were walking — nothing replaced.");

  const a = t.p[i], b = t.p[j];
  const raw = rawPts.map(unnudged);
  const eps = 3 / MPP();
  const thin = rdp(raw, eps);
  const span2 = orientToAnchors(thin, a, b);
  // stitch to the anchors: GPS will not land exactly on them
  const mid = span2.slice(1, -1);
  const next = t.p.slice(0, i+1).concat(mid, t.p.slice(j));

  const before = j - i + 1, after2 = mid.length + 2;
  const dlg = document.getElementById("walkdlg");
  document.getElementById("walkstat").innerHTML =
    "<b>" + raw.length + "</b> fixes walked, thinned to <b>" + after2 + "</b> points.<br>" +
    "Replacing <b>" + before + "</b> points covering " +
    fmtDist(lenOf(t.p.slice(i, j+1))) + " with " + fmtDist(lenOf(span2)) + ".";
  dlg.returnValue = "";
  const commit = () => {
    push();
    t.p = next; anchors = [];
    after("Span replaced from your walk — line is now " + fmtDist(lenOf(t.p)) + ".");
  };
  dlg.onclose = () => { if(dlg.returnValue === "ok") commit(); };
  dlg.showModal();
}

/* ---------- access routes ---------- */
function linkRoute(stand){
  const cands = trails.filter(t => t.kind === "route");
  if(!cands.length){
    toast("Draw or walk a line first, set its type to Access route, then link it.");
    return;
  }
  if(primary && getT(primary) && getT(primary).kind === "route"){
    const r = getT(primary);
    r.stands = [...new Set([...(r.stands || []), stand.id])];
    after("Linked " + (r.name || "that route") + " to " + (stand.name || "this stand") + ".");
    return;
  }
  const last = cands[cands.length-1];
  last.stands = [...new Set([...(last.stands || []), stand.id])];
  after("Linked " + (last.name || "the newest route") + ". Pick a different route first to link that one instead.");
}

/* ---------- sit log panel ---------- */
function renderSits(){
  const box = document.getElementById("sitbody");
  if(!box) return;
  const cnt = document.getElementById("sitcount");
  if(cnt) cnt.textContent = sitOpen ? "sitting now" : (inSeason(sits).length + " this season");
  box.textContent = "";
  const btn = document.getElementById("sitbtn");
  btn.textContent = sitOpen ? "End sit" : "Start sit";
  btn.classList.toggle("go", !sitOpen);
  btn.classList.toggle("rec", !!sitOpen);
  btn.setAttribute("aria-pressed", String(!!sitOpen));

  if(sitOpen){
    const sel = el("select", {});
    sel.appendChild(el("option", {value:""}, ["— pick a stand —"]));
    for(const p of pins) if(p.t === "stand" || p.t === "blind"){
      const o = el("option", {value:p.id}, [p.name || PINS[p.t].label]);
      if(p.id === sitOpen.stand) o.selected = true;
      sel.appendChild(o);
    }
    sel.addEventListener("change", () => {
      sitOpen.stand = sel.value || null;
      const p = pins.find(x => x.id === sel.value);
      sitOpen.standName = p ? (p.name || "unnamed") : "";
      saveState();
    });
    box.append(field("Stand", sel));
    const seen = el("input", {type:"number", min:"0", step:"1", value:String(sitOpen.seen || 0)});
    seen.addEventListener("input", () => { sitOpen.seen = Math.max(0, Number(seen.value) || 0); saveState(); });
    box.append(field("Deer seen so far", seen));
    const note = el("textarea", {placeholder:"Anything worth remembering"});
    note.value = sitOpen.note || "";
    note.addEventListener("input", () => { sitOpen.note = note.value; saveState(); });
    box.append(field("Note", note));
    const bits = ["in " + sitOpen.in];
    if(sitOpen.wind) bits.push("wind " + sitOpen.wind + " " + sitOpen.windSpeed);
    if(sitOpen.temp !== null && sitOpen.temp !== undefined) bits.push(sitOpen.temp + "°");
    box.append(el("div", {class:"stat"}, [bits.join(" · ") + " — captured automatically"]));
  }else{
    const season = inSeason(sits);
    const deer = season.reduce((n, s) => n + (s.seen || 0), 0);
    box.append(el("div", {class:"stat"}, [
      season.length ? season.length + " sits this season · " + deer + " deer · " +
        (deer/season.length).toFixed(1) + " per sit"
                    : "No sits logged yet. The blank ones matter most."]));
    const ids = [...new Set(season.map(s => s.stand).filter(Boolean))];
    ids.sort((a,b) => standStats(b).per - standStats(a).per);
    for(const id of ids){
      const p = pins.find(x => x.id === id), st = standStats(id);
      const row = el("div", {class:"sitrow"}, [
        el("b", {}, [p ? (p.name || PINS[p.t].label) : "gone"]),
        el("span", {}, [st.sits + (st.sits === 1 ? " sit · " : " sits · ") + st.deer + " deer · " +
                        (st.per !== null ? st.per.toFixed(1) + "/sit" : "—")]),
        el("span", {class:st.hot ? "warn" : ""},
           [st.days === null ? "" : st.hot ? "sat " + st.sits + "×, last " + st.days + "d ago — resting it"
                                           : "last " + st.days + "d ago"])
      ]);
      row.onclick = () => { if(p){ selPin = p.id; selT.clear(); primary = null; centerOn(p.x, p.y); renderInsp(); draw(); } };
      box.append(row);
    }
    for(const s of sits.slice(0, 6)){
      box.append(el("div", {class:"stat dim"}, [
        s.date + "  " + (s.standName || "—") + "  " + (s.in || "") + "–" + (s.out || "") +
        "  " + (s.seen || 0) + " deer" + (s.wind ? "  " + s.wind + " " + s.windSpeed : "")]));
    }
  }
}

/* ---------- approach-wind check ----------
   A stand can play the wind perfectly while the walk in blows it out. This looks
   at the route, not just the stand, which is the failure you cannot otherwise see. */
function approachRisk(stand, windFromDeg){
  const rs = trails.filter(t => t.kind === "route" && (t.stands || []).includes(stand.id));
  if(!rs.length || windFromDeg === null) return null;
  const toward = (windFromDeg + 180) % 360;    // the way your scent travels
  let worst = 0, hits = 0, total = 0;
  for(const r of rs) for(const q of r.p){
    const dx = stand.x - q[0], dy = stand.y - q[1];
    const d = Math.hypot(dx, dy) * MPP();
    total++;
    if(d > 230 || d < 8) continue;             // 250 yd of relevance
    let brg = (Math.atan2(dx, -dy) * 180/Math.PI + 360) % 360;
    let off = Math.abs(((brg - toward + 540) % 360) - 180);
    if(off < 50){ hits++; worst = Math.max(worst, 50 - off); }
  }
  if(!total) return null;
  const frac = hits / total;
  if(frac < .08) return null;
  return {frac, text:"Your approach runs upwind of this stand on a " +
          degToCompass(windFromDeg) + " wind — " + Math.round(frac*100) +
          "% of the route carries scent into it."};
}

/* ---------- trail list ---------- */
function syncList(){
  const box = document.getElementById("tlist");
  box.textContent = "";
  document.getElementById("tcount").textContent =
    trails.length + " lines · " + fmtDist(trails.reduce((s,t) => s+lenOf(t.p), 0));
  for(const {t, L} of trails.map(t => ({t, L:lenOf(t.p)})).sort((a,b) => b.L-a.L)){
    const row = el("div", {class:"trow", "aria-selected":String(selT.has(t.id))});
    const nm = el("span", {class:"nm", title:"Double-tap to rename"},
      [t.name || ("Unnamed · " + (KINDS[t.kind] || KINDS.trail).label.toLowerCase())]);
    if(!t.name) nm.style.opacity = ".6";
    const ln = el("span", {class:"ln"}, [fmtDist(L)]);
    const x = el("button", {class:"x", type:"button", title:"Delete this line"}, ["×"]);
    x.onclick = ev => {
      ev.stopPropagation(); push();
      trails = trails.filter(q => q.id !== t.id); selT.delete(t.id);
      if(primary === t.id){ primary = null; anchors = []; }
      after("Line deleted.");
    };
    nm.ondblclick = ev => {
      ev.stopPropagation();
      const inp = el("input", {type:"text", value:t.name || "", placeholder:"Name this line"});
      inp.style.cssText = "flex:1;min-width:0;font-size:16px;padding:0 .2rem;background:var(--panel-2);color:var(--ink);border:1px solid var(--blaze);border-radius:2px";
      inp.onclick = e2 => e2.stopPropagation();
      const commit = () => { t.name = inp.value.trim(); saveState(); syncList(); renderInsp(); draw(); };
      inp.onkeydown = e2 => {
        e2.stopPropagation();
        if(e2.key === "Enter"){ e2.preventDefault(); commit(); }
        if(e2.key === "Escape"){ e2.preventDefault(); syncList(); }
      };
      inp.onblur = commit;
      row.replaceChild(inp, nm); inp.focus(); inp.select();
    };
    row.onclick = ev => {
      selectTrail(t.id, ev.shiftKey);
      if(!ev.shiftKey){
        const xs = t.p.map(q => nudged(q)[0]), ys = t.p.map(q => nudged(q)[1]);
        centerOn((Math.min(...xs)+Math.max(...xs))/2, (Math.min(...ys)+Math.max(...ys))/2);
        setTool("edit");
      }
    };
    row.append(nm, ln, x);
    box.appendChild(row);
  }
}

/* ---------- chrome wiring ---------- */
let toastT;
function toast(m){
  const t = document.getElementById("toast");
  t.textContent = m; t.classList.add("on");
  clearTimeout(toastT); toastT = setTimeout(() => t.classList.remove("on"), 2600);
}
function nudgeStat(){
  document.getElementById("nudgestat").textContent =
    fmtDist(Math.hypot(nudge.dx, nudge.dy) * (D ? MPP() : 1)) + " · " +
    nudge.rot.toFixed(1) + "° · " + Math.round(nudge.scl*100) + "%";
}
for(const box of ["tools","tools2"]) document.getElementById(box).addEventListener("click", e => {
  const b = e.target.closest("[data-tool]");
  /* Pressing Drop pin always means a new pin, even if a recovery mark was armed. */
  if(b){ if(b.dataset.tool === "mark") placing = {what:"pin"}; setTool(b.dataset.tool); }
});
document.querySelectorAll("[data-toggle]").forEach(h => h.addEventListener("click", () => {
  const b = document.getElementById(h.dataset.toggle); b.hidden = !b.hidden;
}));
for(const key of Object.keys(layers)){
  const elx = document.getElementById("L-" + key);
  elx.checked = layers[key];
  elx.addEventListener("change", () => { layers[key] = elx.checked; draw(); });
}
document.getElementById("fit").onclick = () => { fit(); draw(); };
document.getElementById("selall").onclick = () => {
  selT = new Set(trails.map(t => t.id)); primary = trails.length ? trails[0].id : null;
  anchors = []; syncList(); renderInsp(); draw();
};
document.getElementById("selnone").onclick = clearSel;
document.getElementById("delsel").onclick = opDeleteSel;
document.getElementById("undo").onclick = () => {
  const s = undoStack.pop(); if(!s) return toast("Nothing to undo.");
  redoStack.push(snap()); restore(s);
};
document.getElementById("redo").onclick = () => {
  const s = redoStack.pop(); if(!s) return toast("Nothing to redo.");
  undoStack.push(snap()); restore(s);
};
const railEl = document.getElementById("rail"), railShow = document.getElementById("railshow");
document.getElementById("railhide").onclick = e => { e.stopPropagation(); railEl.hidden = true; railShow.hidden = false; };
railShow.onclick = () => { railEl.hidden = false; railShow.hidden = true; };
document.getElementById("nudgebody").parentElement.addEventListener("click", e => {
  const b = e.target.closest("button"); if(!b) return;
  if(b.dataset.nudge){
    const [ax, ay] = b.dataset.nudge.split(",").map(Number), step = 5 / MPP();
    nudge.dx += ax*step; nudge.dy += ay*step;
  }else if(b.dataset.rot) nudge.rot += Number(b.dataset.rot);
  else if(b.dataset.scl) nudge.scl *= Number(b.dataset.scl);
  else if(b.id === "nudgereset") nudge = {dx:0, dy:0, rot:0, scl:1};
  else if(b.id === "nudgeapply"){
    push();
    for(const t of trails) t.p = t.p.map(nudged);
    nudge = {dx:0, dy:0, rot:0, scl:1};
    saveState(); toast("Shift baked in.");
  } else return;
  nudgeStat(); draw();
});

/* ---------- mobile bottom sheet ----------
   Three stops. Peek keeps the four actions you actually use in a stand within
   thumb reach; half and full are for everything else. The map is visible above
   it at every stop, which the old full-height panel could not manage. */
const SHEET = (() => {
  const rail = document.getElementById("rail");
  const grab = document.getElementById("sheetgrab");
  const isPhone = () => matchMedia("(max-width:760px)").matches;
  const stops = () => {
    const h = document.getElementById("stage").getBoundingClientRect().height;
    return [108, Math.round(h*.46), Math.round(h*.86)];
  };
  let at = 0;
  try{ const v = +localStorage.getItem("sheetStop"); if(v >= 0 && v <= 2) at = v; }catch(_){}
  function apply(px){ rail.style.setProperty("--sheet-h", Math.round(px) + "px"); }
  function go(i, remember){
    at = Math.max(0, Math.min(2, i));
    apply(stops()[at]);
    if(remember !== false){ try{ localStorage.setItem("sheetStop", at); }catch(_){} }
  }
  function nearest(px){
    const s = stops();
    let best = 0, bd = Infinity;
    s.forEach((v, i) => { const d = Math.abs(v-px); if(d < bd){ bd = d; best = i; } });
    return best;
  }
  let drag = null;
  grab.addEventListener("pointerdown", e => {
    if(!isPhone()) return;
    grab.setPointerCapture(e.pointerId);
    drag = {y:e.clientY, h:rail.getBoundingClientRect().height, moved:false};
    rail.dataset.dragging = "1";
  });
  grab.addEventListener("pointermove", e => {
    if(!drag) return;
    const dy = drag.y - e.clientY;
    if(Math.abs(dy) > 4) drag.moved = true;
    const max = stops()[2];
    apply(Math.max(60, Math.min(max, drag.h + dy)));
    e.preventDefault();
  });
  const release = () => {
    if(!drag) return;
    delete rail.dataset.dragging;
    if(drag.moved) go(nearest(rail.getBoundingClientRect().height));
    else go((at+1) % 3);               // a tap cycles, so it works without a drag
    drag = null;
  };
  grab.addEventListener("pointerup", release);
  grab.addEventListener("pointercancel", release);
  grab.addEventListener("keydown", e => {
    if(e.key === "ArrowUp"){ go(at+1); e.preventDefault(); }
    if(e.key === "ArrowDown"){ go(at-1); e.preventDefault(); }
    if(e.key === "Enter" || e.key === " "){ go((at+1)%3); e.preventDefault(); }
  });
  addEventListener("resize", () => { if(isPhone()) apply(stops()[at]); });
  return {
    go, isPhone,
    atLeast(i){ if(isPhone() && at < i) go(i, false); },
    init(){ if(isPhone()) apply(stops()[at]); }
  };
})();

/* the peek row drives the same handlers as the desktop GPS bar */
const mirror = (from, to) => {
  const a = document.getElementById(from), b = document.getElementById(to);
  b.onclick = () => a.click();
  new MutationObserver(() => { b.disabled = a.disabled; })
    .observe(a, {attributes:true, attributeFilter:["disabled"]});
  b.disabled = a.disabled;
};
mirror("gpsbtn", "sp-locate");
mirror("markhere", "sp-mark");
mirror("briefbtn", "sp-brief");
document.getElementById("sp-pin").onclick = () => { setTool("mark"); SHEET.go(0); };

/* ---------- persistence ---------- */
let saveT = null, saving = false, dirty = false;
function setSave(s, txt){ const n = document.getElementById("savestate"); n.dataset.s = s; n.textContent = txt; }
function saveState(){
  dirty = true; setSave("saving", "Saving…");
  clearTimeout(saveT); saveT = setTimeout(doSave, 700);
}
async function doSave(){
  if(saving) return;
  saving = true;
  try{
    await DB.set("state", {v:3, trails, pins, sits, sitOpen, nudge, seedDone, at:new Date().toISOString()});
    dirty = false; setSave("saved", "Saved");
  }catch(_){ setSave("local", "Save failed"); }
  finally{
    saving = false;
    if(dirty){ clearTimeout(saveT); saveT = setTimeout(doSave, 700); }
  }
}

/* ---------- seed data ----------
   Creeks and terrain features belong to the land, not to a device. They used to
   ship as side files you imported by hand, which meant importing again on every
   phone and losing them on a reinstall. Now they ride in with the app, get
   cached by the service worker, and merge themselves on boot.

   Merging is keyed on a stable id recorded in seedDone, not on whether the
   feature is currently present. That is the difference between "add what is
   missing" and "add what you have never been given": if you delete a seed pin it
   stays deleted, and if you walk a creek and replace a stretch your version is
   never overwritten. New seed features added in a later build still come in,
   because their ids are not in the list yet. */
const SEED_URL = "seed.geojson";
async function mergeSeed(){
  if(!D) return;
  let g;
  try{
    const r = await fetch(SEED_URL, {cache:"no-cache"});
    if(!r.ok) return;
    g = await r.json();
  }catch(_){ return; }                     // offline on a first run: try again next boot
  const done = new Set(seedDone);
  let nt = 0, np = 0;
  for(const f of (g.features || [])){
    const pr = f.properties || {}, gm = f.geometry;
    if(!gm || !pr.id || done.has(pr.id)) continue;
    if(gm.type === "LineString" && gm.coordinates.length >= 2){
      trails.push({id:pr.id, p:gm.coordinates.map(c => llToWorld(c[0], c[1])),
                   name:pr.name || "", kind:KINDS[pr.type] ? pr.type : "trail", seed:true});
      nt++;
    }else if(gm.type === "Point"){
      const xy = llToWorld(gm.coordinates[0], gm.coordinates[1]);
      const pin = pinFromProps(xy[0], xy[1], pr);
      pin.id = pr.id; pin.seed = true;
      pins.push(pin); np++;
    }else continue;
    done.add(pr.id);
  }
  if(!nt && !np) return;
  seedDone = [...done];
  saveState(); syncList(); renderSits(); draw();
  const bits = [];
  if(nt) bits.push(nt + (nt === 1 ? " line" : " lines"));
  if(np) bits.push(np + (np === 1 ? " pin" : " pins"));
  toast("Added " + bits.join(" and ") + " that ship with the map.");
}

/* ---------- boot ---------- */
function startMap(pack, state){
  D = pack;
  D.center = worldToLL(D.w/2, D.h/2);
  trails = (state && state.trails) || (pack.trails || []).map((t,i) =>
    ({id:t.id || ("t"+i), p:t.p, name:t.name || "", kind:KINDS[t.kind] ? t.kind : "trail"}));
  pins = (state && state.pins) || pack.pins || [];
  sits = (state && state.sits) || [];
  seedDone = (state && state.seedDone) || [];
  sitOpen = (state && state.sitOpen) || null;
  nudge = (state && state.nudge) || {dx:0, dy:0, rot:0, scl:1};
  document.getElementById("title").textContent = pack.name || "Hunt Map";
  document.getElementById("subline").innerHTML =
    (pack.relief_ft ? "RELIEF <b>" + pack.relief_ft[0] + "–" + pack.relief_ft[1] + " ft</b> · " : "") +
    "CONTOURS <b>10 ft</b> · BUILD <b>" + BUILD + "</b>";
  if(pack.aerial){ aerialImg = new Image(); aerialImg.onload = draw; aerialImg.src = pack.aerial; }
  document.getElementById("welcome").hidden = true;
  SHEET.init();
  resize(); fit(); nudgeStat(); syncList(); renderSits(); setTool("pan"); draw();
  setSave("saved", state ? "Saved" : "Ready");
}
async function loadPackFile(file){
  try{
    const pack = JSON.parse(await file.text());
    if(!pack.w || !pack.h || !pack.bbox3857) throw new Error("that isn't a map pack");
    /* This used to call DB.del("state") unconditionally, which meant handing you
       an updated basemap also quietly deleted every pin, sit and trail edit on
       the device. The pack is the ground; state is your work. If the new pack
       covers the same ground, the work still lines up, so keep it. */
    const old = await DB.get("pack");
    const prev = await DB.get("state");
    const sameGround = !!(old && old.bbox3857 && pack.bbox3857 &&
      old.bbox3857.every((v, i) => Math.abs(v - pack.bbox3857[i]) < 1));
    if(!sameGround && prev){
      const n = (prev.trails || []).length + (prev.pins || []).length;
      if(n && !confirm("That map covers different ground, so your " + n +
          " lines and pins would not line up on it and will be cleared.\n\n" +
          "Back up first if you have not. Carry on?")){
        toast("Left exactly as it was.");
        return;
      }
    }
    await DB.set("pack", pack);
    if(!sameGround) await DB.del("state");
    startMap(pack, sameGround ? prev : null);
    await mergeSeed();
    toast(sameGround ? "Map updated \u2014 your pins and lines are untouched."
                     : "Map loaded. It stays on this device.");
  }catch(err){ toast("Couldn't read that file: " + err.message); }
}
document.getElementById("loadpack").onclick = () => document.getElementById("packin").click();
document.getElementById("packin").onchange = e => {
  const f = e.target.files[0]; e.target.value = "";
  if(f) loadPackFile(f);
};
/* ---------- pin placement ---------- */
document.getElementById("walkbtn").onclick = armWalk;
document.getElementById("sitbtn").onclick = () => { sitOpen ? endSit() : startSit(); };

document.getElementById("placego").onclick = () => {
  const at = atScreen(...mapCentre());
  if(placing && placing.what === "recovery"){
    const p = pins.find(x => x.id === placing.pinId);
    if(!p){ toast("That pin is gone."); setTool("pan"); return; }
    push();
    p[placing.key] = at;
    const label = placing.label;
    setTool("pan");
    after(label + " marked at the crosshair.");
    selPin = p.id; renderInsp();
    return;
  }
  const t = document.getElementById("pintype").value;
  dropPin(at, t);
  toast((PINS[t] || PINS.note).label + " dropped at the crosshair.");
  setTool("pan");
};
document.getElementById("placecancel").onclick = () => setTool("pan");

document.getElementById("startblank").onclick = async () => {
  const blank = {name:"Blank map", mpp:1, w:2000, h:2000,
    bbox3857:[-9486681.73, 3697560.80, -9484218.69, 3700023.85],
    parcels:[], contours:[], trails:[], pins:[]};
  await DB.set("pack", blank);
  startMap(blank, null);
  toast("Blank map. Import a GPX or map pack when you have one.");
};

const dl = document.getElementById("nameideas") || (() => {
  const d = document.createElement("datalist"); d.id = "nameideas";
  document.body.appendChild(d); return d;
})();
for(const n of NAME_IDEAS){ const o = document.createElement("option"); o.value = n; dl.appendChild(o); }
const ptsel = document.getElementById("pintype");
for(const k in PINS){ const o = document.createElement("option"); o.value = k; o.textContent = PINS[k].label; ptsel.appendChild(o); }
ptsel.value = "stand";

window.addEventListener("resize", () => { resize(); draw(); });
window.addEventListener("orientationchange", () => setTimeout(() => { resize(); fit(); draw(); }, 250));

(async function boot(){
  resize();
  try{
    const pack = await DB.get("pack");
    if(pack){ startMap(pack, await DB.get("state")); await mergeSeed(); }
  }catch(_){}
  if("serviceWorker" in navigator && location.protocol.startsWith("http")){
    try{ await navigator.serviceWorker.register("sw.js"); }catch(_){}
  }
})();
