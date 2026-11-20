# RH

This repository contains the Lean project extracted from the archive accompanying Levent Alpöge’s Riemann Hypothesis note. [Original note (PDF)](https://alpo.ge/remark.pdf)

The Lean project is in [`extracted/lean/`](extracted/lean/). A summary is available in [`remark.md`](remark.md).

<details>
<summary>Verso</summary>

The [Verso proof archive](https://tomasortega.net/RH/) shows natural-language proof notes alongside the original Lean statements and proofs in [`verso/src/`](verso/src/). CI publishes the site from `verso` without elaborating the extracted proofs. A single AI drafting pass over all 823,417 detected claims would use about **445 million input tokens and 82–165 million written output tokens**, or roughly **$860–$1,270 USD** at GPT‑6.2 Sol Batch rates on November 20, 2026. This estimate uses a token count extrapolated from 3,200 Lean files sampled by size, 300 prompt tokens per file, and 100–200 output tokens per claim, informed by a sample of 115 written proofs. The cost covers that drafting pass. Model reasoning tokens, extra dependency context, retries, and editorial review can raise it. [Build and annotation details](verso/README.md) · [API pricing](https://developers.openai.com/api/docs/pricing)

</details>
