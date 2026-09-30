"use strict";
/* Hunt Map — offline field map and editor. All data stays on this device. */

const BUILD = 16;
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
  edge:  {label:"Field edge",    dash:[2,6],   w:2.0, col:"#d9c23a"}
};
const PINS = {
  stand:  {label:"Stand / blind",  color:"#d9541a", glyph:"stand"},
  sight:  {label:"Deer sighting",  color:"#e8c53a", glyph:"deer"},
  cam:    {label:"Trail camera",   color:"#b0409a", glyph:"cam"},
  camdeer:{label:"Deer on camera", color:"#e0902a", glyph:"deer"},
  scrape: {label:"Scrape",         color:"#8a5a2a", glyph:"ring"},
  rub:    {label:"Rub",            color:"#c98a3a", glyph:"dot"},
  drop:   {label:"Droppings",      color:"#6b5a3a", glyph:"dot"},
  urine:  {label:"Urine / sign",   color:"#a8a03a", glyph:"dot"},
  track:  {label:"Tracks",         color:"#7d8a94", glyph:"dot"},
  bed:    {label:"Bedding",        color:"#7a5cc4", glyph:"bed"},
  food:   {label:"Food plot",      color:"#5f9e3f", glyph:"square"},
  feeder: {label:"Feeder",         color:"#4a8f2f", glyph:"square"},
  water:  {label:"Water",          color:"#2f8fb0", glyph:"drop"},
  note:   {label:"Note",           color:"#8c8c8c", glyph:"dot"}
};
const DIRECTIONAL = new Set(["sight","camdeer","track"]);
const WINDS = ["N","NE","E","SE","S","SW","W","NW"];
const NAME_IDEAS = ["Main road","Camp road","Ridge road","Bottom road","Food plot road",
  "Creek crossing","Power line","Property line walk","North loop","South loop","Bedding edge"];

/* ---------- state ---------- */
let D = null;                       // the loaded map pack
let trails = [], pins = [];
let selT = new Set(), primary = null, selPin = null, anchors = [];
let tool = "pan", editMode = "move", arrowPushed = false;
let layers = {aerial:true, hill:false, cont:true, parcel:true, trail:true, labels:true, pins:true};
let nudge = {dx:0, dy:0, rot:0, scl:1};
let draft = null, eraseBox = null, pending = null;
let undoStack = [], redoStack = [];
let uid = 0;
const newId = pre => pre + Date.now().toString(36) + (uid++).toString(36);

const view = {k:1, tx:0, ty:0};
let W = 0, H = 0, DPR = 1;
const cv = document.getElementById("map");
const ctx = cv.getContext("2d");
let aerialImg = null, hillImg = null;

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
  if(layers.hill && hillImg && hillImg.naturalWidth){
    ctx.globalAlpha = .55; ctx.globalCompositeOperation = "multiply";
    ctx.drawImage(hillImg, dx, dy, dw, dh);
    ctx.globalCompositeOperation = "source-over"; ctx.globalAlpha = 1;
  }
  if(layers.cont && D.contours){
    const clay = css("--clay");
    for(const c of D.contours){
      ctx.beginPath();
      for(let i = 0; i < c.p.length; i++){
        const X = sx(c.p[i][0]), Y = sy(c.p[i][1]);
        i ? ctx.lineTo(X,Y) : ctx.moveTo(X,Y);
      }
      ctx.closePath(); ctx.strokeStyle = clay;
      ctx.globalAlpha = c.index ? .95 : .6; ctx.lineWidth = c.index ? 1.6 : .9; ctx.stroke();
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
        ctx.fillStyle = css("--ground"); ctx.globalAlpha = .8;
        ctx.fillRect(X-wd/2, Y-7, wd, 13);
        ctx.globalAlpha = 1; ctx.fillStyle = clay; ctx.fillText(txt, X, Y);
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
  if(eraseBox){
    const {x0,y0,x1,y1} = eraseBox;
    ctx.save(); ctx.setLineDash([6,4]); ctx.strokeStyle = "#ff4d4d"; ctx.lineWidth = 1.6;
    ctx.fillStyle = "rgba(255,77,77,.16)";
    ctx.fillRect(x0,y0,x1-x0,y1-y0); ctx.strokeRect(x0,y0,x1-x0,y1-y0); ctx.restore();
  }
  updateScale();
}

function drawPin(p){
  const X = sx(p.x), Y = sy(p.y);
  if(X < -44 || X > W+44 || Y < -44 || Y > H+44) return;
  const spec = PINS[p.t] || PINS.note, on = selPin === p.id, r = on ? 9 : 7;
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
  ctx.beginPath();
  if(spec.glyph === "square") ctx.rect(X-r, Y-r, r*2, r*2);
  else if(spec.glyph === "stand"){ctx.moveTo(X,Y-r-2); ctx.lineTo(X+r,Y+r); ctx.lineTo(X-r,Y+r); ctx.closePath();}
  else if(spec.glyph === "drop"){ctx.moveTo(X,Y-r-2); ctx.bezierCurveTo(X+r,Y-r,X+r,Y+r,X,Y+r); ctx.bezierCurveTo(X-r,Y+r,X-r,Y-r,X,Y-r-2);}
  else ctx.arc(X,Y,r,0,7);
  ctx.fillStyle = spec.color; ctx.fill();
  ctx.lineWidth = on ? 3 : 2; ctx.strokeStyle = on ? "#fff" : "rgba(0,0,0,.6)"; ctx.stroke();
  if(spec.glyph === "ring"){ctx.beginPath(); ctx.arc(X,Y,r-3.5,0,7); ctx.strokeStyle = "rgba(0,0,0,.6)"; ctx.lineWidth = 2; ctx.stroke();}
  if(spec.glyph === "cam"){ctx.beginPath(); ctx.arc(X,Y,2.4,0,7); ctx.fillStyle = "#fff"; ctx.fill();}
  if(spec.glyph === "bed"){ctx.beginPath(); ctx.moveTo(X-4,Y+1); ctx.lineTo(X+4,Y+1); ctx.strokeStyle = "#fff"; ctx.lineWidth = 2; ctx.stroke();}
  if(p.name && view.k > .5){
    ctx.font = "600 11px 'Barlow Condensed',sans-serif";
    ctx.textAlign = "left"; ctx.textBaseline = "middle";
    const tw = ctx.measureText(p.name).width;
    ctx.fillStyle = "rgba(0,0,0,.6)"; ctx.fillRect(X+r+3, Y-7, tw+6, 14);
    ctx.fillStyle = "#fff"; ctx.fillText(p.name, X+r+6, Y);
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
function updateScale(){
  const targets = [10,20,25,50,100,200,250,500,1000];
  let best = targets[0];
  for(const t of targets) if(t / MPP() * view.k <= 110) best = t;
  document.getElementById("scalerule").style.width = (best / MPP() * view.k).toFixed(0)+"px";
  document.getElementById("scaletext").textContent = best >= 1000 ? (best/1000)+" km" : best+" m";
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
const snap = () => JSON.stringify({trails, pins});
function push(){ undoStack.push(snap()); if(undoStack.length > 60) undoStack.shift(); redoStack.length = 0; }
function restore(s){
  const o = JSON.parse(s);
  trails = o.trails; pins = o.pins;
  selT = new Set([...selT].filter(id => getT(id)));
  if(primary && !getT(primary)) primary = null;
  if(selPin && !pins.find(p => p.id === selPin)) selPin = null;
  anchors = [];
  after(null);
}
function after(msg){ saveState(); syncList(); renderInsp(); draw(); if(msg) toast(msg); }

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
  if(!best || best.d > 60) return toast("No loose end within 60 m to join to.");
  push();
  const A = best.te ? t.p.slice() : t.p.slice().reverse();
  const B = best.oe ? best.o.p.slice().reverse() : best.o.p.slice();
  t.p = A.concat(B);
  trails = trails.filter(x => x !== best.o);
  selT = new Set([t.id]); primary = t.id; anchors = [];
  after("Joined — gap was " + Math.round(best.d) + " m.");
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
  if(tool === "mark"){ dropPin(atScreen(px, py), document.getElementById("pintype").value); setTool("pan"); return; }

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
  mark:"Pick a type, then tap where it goes. Or use Mark here to drop one at your GPS position."
};
function setTool(t, keepDraft){
  tool = t;
  document.querySelectorAll("#tools .btn").forEach(b => b.setAttribute("aria-pressed", String(b.dataset.tool === t)));
  document.getElementById("toolhint").textContent = HINTS[t];
  if(t !== "edit") editMode = "move";
  cv.classList.toggle("cross", t === "draw" || t === "mark" || t === "erase" || (t === "edit" && editMode !== "move"));
  if(t !== "draw" && !keepDraft) draft = null;
  renderInsp(); draw();
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
    fmtLL(fix.lon, fix.lat) + "  ±" + Math.round(fix.acc) + "m";
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
  toast("Dropped at ±" + Math.round(fix.acc) + " m. Fill in the details.");
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
  toast("Averaged " + good.length + " fixes — about ±" + acc.toFixed(1) + " m.");
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
  if(pts.length < 3){ draw(); return toast("Too few fixes to keep."); }
  push();
  const line = rdp(pts, 3 / MPP());
  const t = {id:newId("w"), p:line.map(unnudged), name:"", kind:"trail"};
  trails.push(t); selT = new Set([t.id]); primary = t.id;
  after("Walked line saved — " + Math.round(lenOf(t.p)) + " m. Name it, or use it to replace an old line.");
}
function centerOn(x, y){
  view.tx = W/2 - x*view.k; view.ty = H/2 - y*view.k; draw();
}

/* ---------- weather (National Weather Service, free, no key) ---------- */
async function getWeather(){
  const cached = await DB.get("wx");
  const fresh = cached && (Date.now() - cached.at < 45*60*1000);
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
    const next = hj.properties.periods.slice(0, 12).map(p => ({
      t:p.startTime, temp:p.temperature, unit:p.temperatureUnit,
      wind:p.windSpeed, dir:p.windDirection, sky:p.shortForecast
    }));
    const wx = {at:Date.now(), now:{temp:now.temperature, unit:now.temperatureUnit,
                wind:now.windSpeed, dir:now.windDirection, sky:now.shortForecast}, next};
    await DB.set("wx", wx);
    return wx;
  }catch(_){ return cached || null; }
}

/* ---------- briefing for Claude ---------- */
async function buildBriefing(){
  const c = D.center || worldToLL(D.w/2, D.h/2);
  const now = new Date();
  const sun = sunTimes(now, c[1], c[0]);
  const mn = moonInfo(now);
  const wx = await getWeather();
  const L = [];
  L.push("HUNT BRIEFING — " + (D.name || "property"));
  L.push("Date: " + now.toLocaleDateString() + " " + hhmm(now));
  L.push("Location: " + fmtLL(c[0], c[1]) + (D.relief_ft ? "  |  relief " + D.relief_ft[0] + "–" + D.relief_ft[1] + " ft" : ""));
  L.push("Light: dawn " + hhmm(sun.dawn) + ", sunrise " + hhmm(sun.sunrise) +
         ", sunset " + hhmm(sun.sunset) + ", dusk " + hhmm(sun.dusk));
  L.push("Moon: " + mn.name + ", " + Math.round(mn.illum*100) + "% lit, day " + mn.age.toFixed(1) + " of cycle");
  if(wx){
    const age = Math.round((Date.now()-wx.at)/60000);
    L.push("Weather (NWS, " + (age < 2 ? "just now" : age + " min old") + "): " +
           wx.now.temp + "°" + wx.now.unit + ", wind " + wx.now.dir + " " + wx.now.wind + ", " + wx.now.sky);
    const w6 = wx.next.slice(1, 7).map(p => new Date(p.t).getHours() + "h " + p.dir + " " + p.wind).join("; ");
    L.push("Next 6 h wind: " + w6);
  } else L.push("Weather: unavailable offline — add it yourself if you have it.");
  L.push("");
  L.push("STANDS AND BLINDS");
  const stands = pins.filter(p => p.t === "stand");
  if(!stands.length) L.push("  (none marked yet)");
  for(const p of stands)
    L.push("  • " + (p.name || "unnamed") + " @ " + fmtLL(...worldToLL(p.x, p.y)) +
           (p.winds && p.winds.length ? "  huntable on: " + p.winds.join(",") : "  (no wind notes)") +
           (p.note ? "  — " + p.note : ""));
  L.push("");
  L.push("SIGN AND SIGHTINGS (newest first)");
  const obs = pins.filter(p => p.t !== "stand")
    .sort((a,b) => (b.when || "").localeCompare(a.when || "")).slice(0, 60);
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
    if(p.acc) bits.push("±" + p.acc + "m");
    if(p.note) bits.push("— " + p.note);
    L.push("  • " + bits.join(", "));
  }
  L.push("");
  L.push("TRAILS (" + trails.length + " lines, " +
         (trails.reduce((s,t) => s+lenOf(t.p), 0)/1609.34).toFixed(2) + " mi)");
  for(const t of trails.filter(t => t.name))
    L.push("  • " + t.name + " (" + (KINDS[t.kind] || KINDS.trail).label + ", " + Math.round(lenOf(t.p)) + " m)");
  L.push("");
  L.push("Question: given the wind, light and what I've been seeing, where should I sit " +
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
                (total ? " · " + Math.round(total) + " m (" + (total/1609.34).toFixed(2) + " mi)" : "")];
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
  document.getElementById("exporttext").value = text;
  exportName = filename;
  document.getElementById("sharefile").hidden = !(navigator.canShare && navigator.canShare({files:[new File(["x"], "a.txt", {type:"text/plain"})]}));
  edlg.showModal();
}
function backupBlob(){
  return {format:"huntmap-state/1", savedAt:new Date().toISOString(),
          map:(D && D.name) || "", trails, pins, nudge};
}
document.getElementById("backupbtn").onclick = () =>
  showExport("Backup", "Everything exactly as it is here. Send it to your other device and use Import to restore it.",
             JSON.stringify(backupBlob()), "hunt-backup.json");
document.getElementById("exportbtn").onclick = () =>
  showExport("Export GeoJSON", "Everything on the map as lat/long. Opens in onX, HuntStand, BaseCamp or QGIS.",
             JSON.stringify(geojson(), null, 1), "hunt-map.geojson");
document.getElementById("briefbtn").onclick = async () => {
  const txt = await buildBriefing();
  showExport("Hunt briefing", "Copy this and paste it to Claude on your phone.", txt, "hunt-briefing.txt");
};
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
  const box = document.getElementById("insp"), body = document.getElementById("insp-body");
  body.textContent = "";
  if(selPin) return renderPin(box, body);
  if(!selT.size){ box.hidden = true; return; }
  box.hidden = false;
  if(selT.size > 1){
    document.getElementById("insp-title").textContent = selT.size + " lines picked";
    const tot = [...selT].reduce((s,id) => s + lenOf(getT(id).p), 0);
    body.append(
      el("div", {class:"stat"}, [Math.round(tot) + " m · " + (tot/1609.34).toFixed(2) + " mi"]),
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
    el("div", {class:"stat"}, [Math.round(L) + " m · " + (L/1609.34).toFixed(2) + " mi · " + t.p.length + " points"]),
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
  const when = el("input", {type:"date", value:p.when || ""});
  when.addEventListener("input", () => { p.when = when.value; saveState(); });
  body.append(field("Date", when));
  const note = el("textarea", {placeholder:"What you saw, how you get in, anything worth remembering."});
  note.value = p.note || "";
  note.addEventListener("input", () => { p.note = note.value; saveState(); });
  body.append(field("Notes", note));
  const ll = worldToLL(p.x, p.y);
  body.append(el("div", {class:"stat"}, [fmtLL(ll[0], ll[1]) + (p.acc ? "  ±" + p.acc + "m" : "") +
      (p.averaged ? "  (" + p.averaged + " fixes averaged)" : "")]),
    el("div", {class:"row"}, [el("button", {class:"btn sm danger", onclick:opDeleteSel}, ["Delete pin"])]));
}

/* ---------- trail list ---------- */
function syncList(){
  const box = document.getElementById("tlist");
  box.textContent = "";
  document.getElementById("tcount").textContent =
    trails.length + " lines · " + (trails.reduce((s,t) => s+lenOf(t.p), 0)/1609.34).toFixed(2) + " mi";
  for(const {t, L} of trails.map(t => ({t, L:lenOf(t.p)})).sort((a,b) => b.L-a.L)){
    const row = el("div", {class:"trow", "aria-selected":String(selT.has(t.id))});
    const nm = el("span", {class:"nm", title:"Double-tap to rename"},
      [t.name || ("Unnamed · " + (KINDS[t.kind] || KINDS.trail).label.toLowerCase())]);
    if(!t.name) nm.style.opacity = ".6";
    const ln = el("span", {class:"ln"}, [Math.round(L) + "m"]);
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
    Math.round(Math.hypot(nudge.dx, nudge.dy) * (D ? MPP() : 1)) + " m · " +
    nudge.rot.toFixed(1) + "° · " + Math.round(nudge.scl*100) + "%";
}
document.getElementById("tools").addEventListener("click", e => {
  const b = e.target.closest("[data-tool]"); if(b) setTool(b.dataset.tool);
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
    await DB.set("state", {v:1, trails, pins, nudge, at:new Date().toISOString()});
    dirty = false; setSave("saved", "Saved");
  }catch(_){ setSave("local", "Save failed"); }
  finally{
    saving = false;
    if(dirty){ clearTimeout(saveT); saveT = setTimeout(doSave, 700); }
  }
}

/* ---------- boot ---------- */
function startMap(pack, state){
  D = pack;
  D.center = worldToLL(D.w/2, D.h/2);
  trails = (state && state.trails) || (pack.trails || []).map((t,i) =>
    ({id:t.id || ("t"+i), p:t.p, name:t.name || "", kind:KINDS[t.kind] ? t.kind : "trail"}));
  pins = (state && state.pins) || pack.pins || [];
  nudge = (state && state.nudge) || {dx:0, dy:0, rot:0, scl:1};
  document.getElementById("title").textContent = pack.name || "Hunt Map";
  document.getElementById("subline").innerHTML =
    (pack.relief_ft ? "RELIEF <b>" + pack.relief_ft[0] + "–" + pack.relief_ft[1] + " ft</b> · " : "") +
    "CONTOURS <b>10 ft</b> · BUILD <b>" + BUILD + "</b>";
  if(pack.aerial){ aerialImg = new Image(); aerialImg.onload = draw; aerialImg.src = pack.aerial; }
  if(pack.hillshade){ hillImg = new Image(); hillImg.onload = draw; hillImg.src = pack.hillshade; }
  document.getElementById("welcome").hidden = true;
  if(innerWidth < 760){          // on a phone the panel would cover the map
    document.getElementById("rail").hidden = true;
    document.getElementById("railshow").hidden = false;
  }
  resize(); fit(); nudgeStat(); syncList(); setTool("pan"); draw();
  setSave("saved", state ? "Saved" : "Ready");
}
async function loadPackFile(file){
  try{
    const pack = JSON.parse(await file.text());
    if(!pack.w || !pack.h || !pack.bbox3857) throw new Error("that isn't a map pack");
    await DB.set("pack", pack);
    await DB.del("state");
    startMap(pack, null);
    toast("Map loaded. It stays on this device.");
  }catch(err){ toast("Couldn't read that file: " + err.message); }
}
document.getElementById("loadpack").onclick = () => document.getElementById("packin").click();
document.getElementById("packin").onchange = e => {
  const f = e.target.files[0]; e.target.value = "";
  if(f) loadPackFile(f);
};
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
    if(pack) startMap(pack, await DB.get("state"));
  }catch(_){}
  if("serviceWorker" in navigator && location.protocol.startsWith("http")){
    try{ await navigator.serviceWorker.register("sw.js"); }catch(_){}
  }
})();
