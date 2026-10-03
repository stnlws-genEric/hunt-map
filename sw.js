/* Offline shell cache.
   The app's own code is fetched network-first so an update reaches you on the
   next load rather than the one after; the cache is the fallback when there is
   no signal. Icons and fonts stay cache-first since they never change. */
const CACHE = "huntmap-v40";
const SHELL = ["./", "./index.html", "./app.js", "./seed.geojson", "./version.json", "./manifest.webmanifest",
               "./icon-180-v16.png", "./icon-192-v16.png", "./icon-512-v16.png"];

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
  if(url.hostname.endsWith("weather.gov")) return;      // never cache weather

  /* seed.geojson is network-first with the code, not cache-first with the
     icons. It changes when the map data changes, and a cache-first copy would
     mean new creeks or terrain never reaching a device that already has the
     app installed. */
  const isCode = url.origin === location.origin &&
                 /(\.html|\.js|\.geojson|\.json|\.webmanifest|\/)$/.test(url.pathname);
  if(isCode){
    e.respondWith(
      fetch(e.request).then(res => {
        if(res && res.ok) caches.open(CACHE).then(c => c.put(e.request, res.clone()));
        return res;
      }).catch(() => caches.match(e.request).then(hit => hit || caches.match("./index.html")))
    );
    return;
  }
  e.respondWith(caches.match(e.request).then(hit => hit || fetch(e.request).then(res => {
    if(res && (res.ok || res.type === "opaque")) caches.open(CACHE).then(c => c.put(e.request, res.clone()));
    return res;
  }).catch(() => hit)));
});
