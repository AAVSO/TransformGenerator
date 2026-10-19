# TG Web — Transformation Generator

Browser-based conversion of the supplied TG 6.11 Tkinter application. A Python/Flask server provides scientific calculations; a responsive browser interface provides the workspace. No JavaScript build tools or external frontend services are required.

## Start locally

Requires Python 3.10 or later.

Windows:

    py -m venv .venv
    .venv\Scripts\activate
    python -m pip install -r requirements.txt
    python app.py

macOS / Linux:

    python3 -m venv .venv
    source .venv/bin/activate
    python -m pip install -r requirements.txt
    python app.py

Open http://127.0.0.1:5000 in your browser. Keep the terminal running. Use Ctrl+C to stop. Click **Load example** to explore without input files. The example is synthetic, not a calibration dataset.

## Included workflows

- All 20 UBVRI coefficients and the original reciprocal-error convention.
- AAVSO standard-field catalog retrieval for M67, NGC7790, or coordinates, with uploaded JSON/CSV catalogs as an offline alternative.
- TG/AIP4WIN, MaxIm, VPhot and normalized CSV measurement imports.
- Star ID aliases from the original M67 and NGC7790 mappings.
- Interactive regression plots, per-coefficient exclusions, one-pass 3σ clipping, residual tables, a coordinate map, and SVG downloads.
- Telescope names, Julian dates, saved snapshots, reopening, deletion, and averaging sets from the same telescope.
- CSV and legacy-compatible INI coefficient exports; JSON backup/restore.
- Original telescope configuration and sequential transform_values.ptgp history imports. History archives contain coefficients only; their measurements cannot be reconstructed.

## File formats

Reference CSV: `id,label,ra,dec,U,B,V,R,I`. Use degrees for coordinates, uppercase magnitude columns, and blank cells for unavailable bands. VSP API JSON with a `photometry` array is also accepted.

Normalized measurement CSV: `id,u,b,v,r,i,jd`. Lowercase instrumental magnitudes; repeated rows are averaged. At least three matched stars and sufficient standard-color spread are required for a fit. Standard colors may use reference bands not measured instrumentally.

See the in-app Field guide for legacy format details, uncertainty definitions, and import behavior. VPhot includes only active stars with SNR strictly greater than the selected threshold. Zero/−1000 measurement sentinels are ignored as in the original program.

## Saved data

Observations are processed in server memory; the server does not write uploaded files. Saved sets use browser local storage at the current origin. Browser data clearing, a different browser, or a different host/port will change which sets are available. Export JSON backups for durable storage. There are no user accounts or shared database.

## Hosting

The default server binds to localhost. For a managed Linux host, install the requirements and use:

    gunicorn --bind 0.0.0.0:8000 --workers 2 --timeout 90 app:app

A Dockerfile is included:

    docker build -t tg-web .
    docker run --rm -p 127.0.0.1:8000:8000 tg-web

The included deployment has no authentication or access control. Add HTTPS, access control, rate limits and resource limits before exposing a multiuser service. Each upload request is limited to 20 MB. AAVSO retrieval requires internet access and is subject to upstream availability. This package has not been deployed to a public URL.

## Verification and scientific limits

Install pytest in the virtual environment and run `python -m pytest -q`. Five automated tests exercise all 20 equations, reciprocal uncertainties, excluded-star refits, averaging, importer fixtures, API exports, and restricted legacy archive loading. Browser checks exercised the 20-coefficient synthetic example, point exclusion, saved-set reopen, averaging, and a 390-pixel mobile viewport with no JavaScript errors.

The supplied material contained the Python source only, with no real measurement exports or expected calibration results. Importers were tested with constructed fixtures; validate them against your own TG/AIP4WIN, MaxIm, and VPhot exports. Compare a known calibration with the desktop original before production scientific use. Live AAVSO catalog retrieval has not been end-to-end verified in this environment; catalog upload remains available.

For reciprocal coefficients, errors preserve TG 6.11's formula `abs(stderr / (slope * (slope - stderr)))`, rather than first-order propagation. The plot shading is ±3 residual standard deviations, not a confidence interval. Fitting is unweighted ordinary least squares, matching the source; catalog and measurement errors are not fitted weights. Sets are averaged with the original arithmetic mean and combined scatter/error formula. Invalid/insufficient fits show an explicit error.

## Source layout

- app.py: HTTP endpoints and exports
- engine.py: parsers and coefficient math
- legacy.py: restricted legacy history reader
- aliases.json: field-specific ID mappings extracted from your source
- templates/index.html, static/: browser application
- test_app.py: automated checks

The original source is included under original/ as a reference, not as a runtime dependency. No ownership or licensing of your supplied source is asserted by this conversion.
