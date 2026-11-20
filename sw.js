/* ARCADE service worker (Wave 5, BN-179) — GitHub Pages only.
   Strategy: network-first for everything same-origin, falling
   back to the runtime cache, so a fresh sync is picked up
   immediately when online and the last good copy still opens
   offline. The cache name carries a version: bump it whenever
   this file's behaviour changes so old caches are dropped on
   activate. This file is a standalone repo file (never baked
   into the single-file build); module 77 registers it only on
   *.github.io hosts. */
var CACHE = "arcade-pwa-v1";
var CORE = ["./space-6.html", "./manifest.webmanifest", "./icon-192.png", "./icon-512.png"];

self.addEventListener("install", function (ev) {
  ev.waitUntil(
    caches.open(CACHE).then(function (c) { return c.addAll(CORE); }).then(function () { return self.skipWaiting(); })
  );
});

self.addEventListener("activate", function (ev) {
  ev.waitUntil(
    caches.keys().then(function (keys) {
      return Promise.all(keys.map(function (k) { return k === CACHE ? null : caches.delete(k); }));
    }).then(function () { return self.clients.claim(); })
  );
});

self.addEventListener("fetch", function (ev) {
  var req = ev.request;
  if (req.method !== "GET") return;
  var url = new URL(req.url);
  if (url.origin !== self.location.origin) return; /* Firebase etc. pass through */
  ev.respondWith(
    fetch(req).then(function (res) {
      if (res && res.ok) {
        var copy = res.clone();
        caches.open(CACHE).then(function (c) { c.put(req, copy); });
      }
      return res;
    }).catch(function () {
      return caches.match(req, { ignoreSearch: true }).then(function (hit) {
        if (hit) return hit;
        if (req.mode === "navigate") return caches.match("./space-6.html", { ignoreSearch: true });
        return Response.error();
      });
    })
  );
});
