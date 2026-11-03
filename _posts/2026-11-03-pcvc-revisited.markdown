---
layout: post
title:  "Provably Correct vibe Coding, Revisited"
title_html: "Provably Correct <code>vibe</code> Coding, Revisited"
date:   2026-11-03 07:30:00 +0000
categories: AI
---

About a year ago, I made a demo called [Provably-Correct Vibe Coding]({% post_url 2025-07-29-pcvc %}) ([GitHub](https://github.com/GasStationManager/ProvablyCorrectVibeCoding)). It is a Streamlit app that lets the user give a formal specification of a Lean function they want implemented. It then calls out to an LLM, armed with my primitive Lean coding harness [LeanTool](https://github.com/GasStationManager/LeanTool), to provide the implementation and its correctness proof.

Since then, the field has progressed greatly. Frontier models have become much better at writing code and proofs in Lean, and coding harnesses like Claude Code and Codex have matured, with excellent support for feeding Lean compilation results back to the model.

However, there is one aspect of my original demo that is perhaps missing from the Claude Code or Codex experience. In Claude Code, there is no direct support for the user to look at the formal spec: to read it, understand it, edit it, and take ownership of it before sending it to the LLM. I think that part is important. It is what separates provably correct vibe coding from just vibe coding.
