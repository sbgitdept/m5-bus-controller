# Device cloud config (optional HTTP poll)

M5 polls:

`https://sbgitdept.github.io/m5-bus-controller/devices/<DEVICE_ID>.json`

Primary live path is MQTT retained `m5bus/<DEVICE_ID>/config`.
Place a JSON file here (same shape the WebApp publishes) only if you want
HTTP as a secondary config source after deploy to GitHub Pages.
