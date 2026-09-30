# Hunt Map

A single-page offline field map for marking trails, stands and deer sign, and for
editing GPS tracks by hand.

No map data ships with this code. On first run it asks for a "map pack" file —
aerial imagery, contours, property lines and trails — which is stored in the
browser's IndexedDB on that device and never leaves it. Nothing is uploaded
anywhere; there is no server side.

## Use

1. Publish these files on any static host (GitHub Pages, Cloudflare Pages).
2. Open the URL, import your map pack.
3. iPhone: Share -> Add to Home Screen. It then opens full screen and works
   with no signal.

## Files

- `index.html` — markup and styles
- `app.js` — the whole application
- `sw.js` — service worker, caches the shell for offline use
- `manifest.webmanifest` — home-screen install metadata
- `icon-192.png`, `icon-512.png`

Weather comes from the US National Weather Service API when a connection is
available, and is skipped when it isn't. Sun, dusk and moon phase are computed
on the device with no network at all.
