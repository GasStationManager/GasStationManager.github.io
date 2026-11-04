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

So I tried to vibe code a successor to my demo, adapted to today's coding agent landscape. It is a Lean tactic called [`vibe`](https://github.com/GasStationManager/vibe). Given a Lean function signature with a formal spec attached, either as a subtype of the return type or as spec lemmas in the `vcgen` framework, the user can write `by vibe`, and the tactic will call out to an LLM coding agent (which can be configured). The agent takes in the task and tries to provide the implementation and its correctness proof.

With the spec as a subtype, the precondition is a parameter and the postcondition is the subtype:

```lean
def listMax (xs : List Int) (h : xs ≠ []) : {m : Int // m ∈ xs ∧ ∀ x ∈ xs, x ≤ m} := by
  vibe
```

With the spec as a `vcgen` spec lemma, the definition carries no spec in its type, and the `@[spec]` theorem about it does. Both get `by vibe`, and one job fills in both, the implementation and the proof:

```lean
def bump (k : Nat) : StateM Nat Nat := by
  vibe

/-- `bump k` adds `k` to the state and returns the old value. -/
@[spec] theorem bump_spec (k n : Nat) :
    ⦃ fun s => s = n ⦄ bump k ⦃ fun r s' => r = n ∧ s' = n + k ⦄ := by
  vibe
```

Since `vibe` is a tactic, it lives in your editor through Lean's language server, with no separate app. By default it runs in the background: on a new spec, it starts the agent, leaves a `sorry` in place, and lets you keep working, and when the agent finishes, the result shows up in the editor on its own. You apply it from the `Try this` link in the infoview, or from the quick-fix lightbulb, which is plain LSP and so should work in any editor that runs Lean's language server. Either way, Lean re-checks the code once it is in your file. Results are cached, so re-elaborating does not call the model again, and once you accept a suggestion, `vibe` is gone from the file, so `lake build` and CI never call a model.

There have been similar tactics that call out to LLMs, including [llmstep](https://github.com/wellecks/llmstep) and [Lean Copilot](https://github.com/lean-dojo/LeanCopilot) from the LeanDojo project. I think what is unique about this tactic is its focus on verified code generation: it requires both an implementation and a correctness proof.

`vibe` will also help you check the validity of your spec, again by calling out to the LLM: before implementing, the agent checks whether the spec is vacuous (the preconditions never hold, or every implementation satisfies the postcondition) or unsatisfiable (no implementation can meet it). A defect is reported only with a certificate, a theorem stating the defect that Lean checks. For example, this spec cannot be met:

```lean
def between (lo hi : Nat) : {m : Nat // lo ≤ m ∧ m < hi ∧ hi ≤ lo + 0} := by
  vibe
```

and `vibe` reports:

```
vibe: SPEC DEFECT (unsat): The postcondition requires lo ≤ m < hi and hi ≤ lo,
which is contradictory for every input, e.g. lo = 0, hi = 0.
Lean-checked certificate (check that it states the defect of THIS spec):
theorem between_unsat : ¬ ∃ f : Nat → Nat → Nat, ∀ lo hi : Nat,
    lo ≤ f lo hi ∧ f lo hi < hi ∧ hi ≤ lo + 0 := by
  rintro ⟨f, h⟩
  have := h 0 0
  omega
```

Feel free to adapt the LLM agent call to your own development workflow: the agent command is a setting (`set_option vibe.llm`), and its instructions are a plain prompt file in the repo. This is a natural site for inserting property-based testing and test-driven development, such as the [Code-Test-Prove]({% post_url 2025-06-08-proving-alphabeta %}) scheme I suggested earlier.

[Try it out](https://github.com/GasStationManager/vibe); comments welcome! This is a prototype, but I hope it can become part of something useful. One of my goals is to support workflows where the user works closely with the formal spec in the editor, while dispatching implementation and proof jobs via `vibe`. I would be very curious to hear about user experiences: how effective it is, and any pain points.
