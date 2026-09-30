/* Cache the app shell so it opens with no signal. Data lives in IndexedDB, never here. */
const CACHE = "huntmap-v10";
const SHELL = ["./", "./index.html", "./app.js", "./manifest.webmanifest",
               "./icon-192.png", "./icon-512.png"];

self.addEventListener("install", e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll(SHELL)).then(() => self.skipWaiting()));
});
self.addEventListener("activate", e => {
  e.waitUntil(caches.keys()
    .then(ks => Promise.all(ks.filter(k => k !== CACHE).map(k => caches.delete(k))))
    .then(() => self.clients.claim()));
});
self.addEventListener("fetch", e => {
  const url = new URL(e.request.url);
  if(e.request.method !== "GET") return;
  // Never cache weather; it must be fresh or absent.
  if(url.hostname.endsWith("weather.gov")) return;
  // App shell: serve from cache first so it works offline, refresh in the background.
  if(url.origin === location.origin){
    e.respondWith(caches.match(e.request).then(hit => {
      const net = fetch(e.request).then(res => {
        if(res && res.ok) caches.open(CACHE).then(c => c.put(e.request, res.clone()));
        return res;
      }).catch(() => hit);
      return hit || net;
    }));
    return;
  }
  // Fonts and anything else: cache opportunistically, fall back to cache offline.
  e.respondWith(caches.match(e.request).then(hit => hit || fetch(e.request).then(res => {
    if(res && (res.ok || res.type === "opaque")) caches.open(CACHE).then(c => c.put(e.request, res.clone()));
    return res;
  }).catch(() => hit)));
});
