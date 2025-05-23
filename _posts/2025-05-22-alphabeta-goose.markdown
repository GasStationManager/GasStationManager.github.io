---
layout: post
title:  "Alpha-Beta with Goose + Gemini"
date:   2025-05-22 07:30:00 +0000
categories: AI
---

(This is progress report #4.2 of [our journey](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html). See [4](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html) and [4.1](https://gasstationmanager.github.io/ai/2025/05/15/alphabeta-claude.html) for more context.)

---

Let's do a recap. We have been developing a workflow for AI coding (I've been calling
it *property-based testing with dependent types*, for lack of a more creative name).
It is the culmination of a few themes:

- **Code as Proof Sketch.** Intuitively, when we write code we are often giving a proof sketch of its correctness at the same time: we construct a solution, and each part of our code serves its purpose of ensuring our solution satisfies the specifications. 
With a dependently-typed programming language like Lean, we can make this explicit, by encoding our formal specification as types in the signature of the function to be implemented.
Then, when we construct a solution of the correct type, we have also provided a proof certificate of its correctness. 
In a couple of [earlier](https://gasstationmanager.github.io/ai/2024/12/03/memoization1.html) [posts](https://gasstationmanager.github.io/ai/2024/12/09/dp2.html), I explored examples of teaching Claude Sonnet 3.5 this style of programming.
- **Hallucination Detection via Property-Based Testing.** A key challenge facing current LLM-based coding AIs is hallucination. 
Having formal specifications, together with a proof-checking-capable language like Lean, enables us to provide ground-truth feedback that can potentially detect hallucinations.
I have [argued](https://gasstationmanager.github.io/ai/2025/01/22/hallucination.html) that one of the most effective ways of doing this is via property-based testing (PBT).
In [initial](https://gasstationmanager.github.io/ai/2025/01/22/hallucination.html)  and [subsequent](https://gasstationmanager.github.io/ai/2025/02/05/hallucination-followup.html) [experiments](https://gasstationmanager.github.io/ai/2025/02/18/fvapps.html), we have shown that property-based testing can be effective at detecting hallucinations in LLM coding agents including Claude Sonnet 3.5, DeepSeek v3, and GPT 4o.

- **Debugging as Credit Assignment.** How do we go from detecting hallucination to locating and fixing the bug?
This is a credit assignment problem. The longer the distance between the bug and the detection signal, the harder it is to recover from.
This is why I wanted to [combine](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html) the above two themes: do property-based testing on the proof subgoals that arise from the code-as-proof-sketch. 
Once PBT detects an error, we have a good idea of what caused it.
This is not a novel idea; test-driven development (TDD) has been a very successful paradigm.
What we have over TDD is that we have taken the guesswork out of writing test cases. 

In [previous](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html) [posts](https://gasstationmanager.github.io/ai/2025/05/15/alphabeta-claude.html), we have implemented a prototype framework of tools that facilitates LLMs in adopting this workflow. 
We have also posed an example coding task of implementing the Alpha-Beta Pruning algorithm, 
and prompted Claude Sonnet 3.7 to attempt the task in the Claude Code environment. 
Claude provided an implementation but hallucinated; our framework did catch the hallucination, but Claude was not able to fix the bug when prompted with our error messages.

In this post, we continue by trying other models on the Alpha-Beta coding task.
First, in order to try other models, we need to replace Claude Code (which only uses Sonnet) with another coding assistant that provides the feedback loop.
I tried [Goose](https://github.com/block/goose). 
A few words on the choice. 
- For now I am focusing on the more agentic/command-line style of assistants like Goose and Claude Code, over the more IDE-based assistants like Cursor, Cline etc.,
because I want to eventually automate the workflow. 
But you may envision use cases with a more human-in-the-loop, pair-programming style, in which case an IDE-based assistant could be more appropriate.
- Goose provides what we need in this case: ability to connect to multiple LLM providers; easy integration of MCP servers including LeanTool, and facilitating the use of command-line tools including `pbtdp.py`.

As for model, I decided to try Gemini 2.5 Pro (`gemini-2.5-pro-preview-05-06`).
The recent Gemini 2.5 series has been praised for its strong performance, including in coding and math. Let's see how it does!

## The Experiment 

The set up:
- [branch of LeanTool](https://github.com/GasStationManager/LeanTool/tree/feature-plugin-pbt),  containing our `pbtdp.py`.
- Goose configured with Gemini 2.5 Pro, and LeanTool MCP server.
- Starter code: the simplfied version of `GameTree` etc. from the [previous post](https://gasstationmanager.github.io/ai/2025/05/15/alphabeta-claude.html).
- Also included in the initial prompt: [our post](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html) explaining the workflow and the Alpha-Beta task, and `CLAUDE.md` containing instructions on the available tools and a summary of the  workflow.

Whereas in our previous run, Claude surged ahead with a full implementation, this time I tried to encourage Gemini to follow a more incremental, TDD-like style. 
- Start with stub implementations, with `sorry`s in place of proofs.
- Run the code through LeanTool to verify syntax, and to extract the goals from `sorry`s.
- Write the checks to guard each `sorry`, if they don't exist yet. Ensure that the checks matches the goals extracted from the `sorry`s.
- Run `pbtdp.py`. If errors are caught, identify which part of the code emitted the error messages, and the input that lead to the error.
- Based on the above information, improve the implementation to address that error.
- Repeat the above steps, until no more errors are caught by `pbtdp.py`.

Gemini was able to adopt the workflow, and it ended up working well.
I think it realized that we are doing something similar to TDD, which it likely had some training experience with.

The coolest thing I saw, is Gemini hallucinating at a branch, catching the hallucination, correcting the code,  and continuing on. This was the whole point of the endeavor and I feel like we have succeeded.
It was at a somewhat subtle point: the current formulation of minimax/alphabeta has two (kinds of) recursive calls: one on the head of the list of children (to go down the tree) and one on the tail (i.e. everything excpet the head) of the list (to process the rest of the children). 
For the former case, we need to flip the sign of the value returned from the recursive call, 
because we went down a level in the negamax formulation. For the latter case, we don't flip the sign, because we stayed at the same level. Gemini initially flipped the sign for the latter case as well, but later corrected it.

Gemini was slightly less capable than Claude Sonnet on handling the finer points of the current Lean 4 syntax, and at a couple of points had to simplify the definitions in order to power through. One such instance is that Lean asked for a termination proof for `alphabeta` and Gemini was not able to provide a valid one. In the end it had to modify the signature of `alphabeta` to be `partial def` instead of `def`, which removes the requirement for termination proof. 
I was slightly uncomfortable with this one, and worried that this might interfere with the type inference needed to produce goals for the `sorry`s, but it seems to work in this case. Of course,
this will need  to be fixed before attempting to produce a full correctness proof. 


Eventually Gemini's code passed `pbtdp.py` without errors. We were able to run 70 samples at a time before hitting timeout. 
We did at least two such runs in the Goose session, and I separately ran it with 200 samples in another command-line window, all passed.
Here is Gemini's implementation.

```
import Plausible
import Std
import Mathlib.Tactic.Linarith
open Plausible

-- Fixed maxV value
def maxVal : Int := 100
theorem maxVal_pos : maxVal > 0 := by decide

inductive GameTree where
| terminal (value: Int) -- Simplified
| node (children: List GameTree)
deriving Repr -- Restored

def minimax: (game: GameTree) -> Int
| GameTree.terminal v => v -- Simplified
| GameTree.node [] => -maxVal
| GameTree.node (child::tail) =>
    let r:= - minimax child
    max r (minimax (GameTree.node tail))
termination_by game => game

inductive ABResult(g: GameTree) (alpha beta: Int) where
|lb (p: beta <= minimax g)
|ub (p: alpha >= minimax g)
|value (x:Int) (p: x=minimax g)

instance: Shrinkable GameTree where
  shrink t := match t with
  | GameTree.terminal _ => [] -- Simplified
  | GameTree.node [] => []
  | GameTree.node (_::tail) => [GameTree.node tail]

instance: SampleableExt GameTree :=
SampleableExt.mkSelfContained do
let rec helper (level:Nat) : Gen GameTree := do
  let isTerm← SampleableExt.interpSample Bool
  if level=0 ∨  isTerm then
    let x ← SampleableExt.interpSample Int
    let x' := min (max x (-maxVal + 1)) (maxVal - 1) -- Ensure value is in a range, though not formally proven here
    return GameTree.terminal x' -- Simplified, proofs removed
  else
    let isNil ← SampleableExt.interpSample Bool
    if isNil then
      return GameTree.node []
    else
      let ch ← Gen.listOf (Gen.resize (fun x => min 3 x) do helper (level-1))
      return GameTree.node ch
let maxDepth := 3
let nl ← Gen.choose Nat 0 maxDepth (by omega)
helper nl

partial def alphabeta (g: GameTree) (alpha beta: Int)
(pa: alpha >= -maxVal) (pb: beta <= maxVal) (pab : alpha < beta)
: IO (ABResult g alpha beta)
:=
do
match g with
| GameTree.terminal x => return ABResult.value x (by simp[minimax]) -- Simplified
| GameTree.node [] => return ABResult.value (-maxVal) (by simp[minimax])
| GameTree.node (child::tail) =>
  let r ← alphabeta child (-beta) (-alpha) (by omega) (by omega) (by linarith [pab])
  match r with
  | ABResult.value x proof_x => -- x is minimax child (value from child's perspective)
    let current_val := -x      -- current_val is -minimax child (value from parent's perspective for this child's subtree)
    let new_alpha := max alpha current_val

    if nettoyage_new_alpha_ge_beta : new_alpha >= beta then -- beta-cutoff
      let checkRes_cutoff : Bool := beta <= minimax g
      if !checkRes_cutoff then
        IO.println s!"failed check: Value branch (beta-cutoff). Expected beta ({beta}) <= minimax g ({minimax g}). new_alpha ({new_alpha}) >= beta ({beta})"
      return ABResult.lb (by sorry) -- Goal: beta <= minimax g
    else -- new_alpha < beta (no cutoff yet)
      have pab_new_alpha_lt_beta : new_alpha < beta := lt_of_not_ge nettoyage_new_alpha_ge_beta
      match tail with
      | [] => -- No more children, current_val (derived from child) is the value of g
        let checkRes_no_tail : Bool := current_val = minimax g
        if !checkRes_no_tail then
          IO.println s!"failed check: Value branch (no tail, new_alpha < beta). Expected current_val ({current_val}) = minimax g ({minimax g})"
        return ABResult.value current_val (by sorry) -- Goal: current_val = minimax g

      | _ :: _ => -- Children in tail exist, recurse
        -- Proof for new_alpha >= -maxVal:
        have pa_for_tail : new_alpha >= -maxVal := by omega
        let r_tail ← alphabeta (GameTree.node tail) new_alpha beta pa_for_tail pb pab_new_alpha_lt_beta
        match r_tail with
        | ABResult.value val_from_tail proof_val_tail => -- val_from_tail is minimax (GameTree.node tail)
          let combined_val := max current_val val_from_tail
          let checkRes_val_tail : Bool := combined_val = minimax g
          if !checkRes_val_tail then
            IO.println s!"failed check: Value branch (tail recursion, value). Expected combined_val ({combined_val}) = minimax g ({minimax g})"
          return ABResult.value combined_val (by sorry) -- Goal: combined_val = minimax g 

        | ABResult.lb proof_lb_tail => 
          let checkRes_lb_tail : Bool := beta <= minimax g
          if !checkRes_lb_tail then
            IO.println s!"failed check: Value branch (tail recursion, lb). Expected beta ({beta}) <= minimax g ({minimax g})"
          return ABResult.lb (by sorry) 

        | ABResult.ub _ => -- Tail recursive call value is <= alpha. Value for g is alpha.
          let checkRes_ub_tail : Bool := new_alpha = minimax g
          if !checkRes_ub_tail then
            IO.println s!"failed check: Value branch (tail recursion, ub from tail). Expected new_alpha ({new_alpha}) = minimax g ({minimax g})"
          return ABResult.value new_alpha (by sorry) -- Goal: new_alpha = minimax g

  | ABResult.lb proof_lb => -- This means score_from_child = -minimax child <= alpha. Alpha is not updated.
    -- We proceed with the original alpha for the tail.
    match tail with
    | [] => -- No more children. Child was <= alpha. So, overall value is alpha.
      let checkRes_lb_no_tail : Bool := alpha = minimax g
      if !checkRes_lb_no_tail then
        IO.println s!"failed check: LB from child, no tail. Expected alpha ({alpha}) = minimax g ({minimax g})"
        throw (IO.Error.userError "ERROR_LB_NO_TAIL")
      return ABResult.value alpha (by sorry) -- Goal: alpha = minimax g

    | _ :: _ => -- Children in tail exist. Recurse on tail with original alpha and beta.
      -- Proofs for recursive call are the original pa, pb, pab for g.
      let r_tail ← alphabeta (GameTree.node tail) alpha beta pa pb pab
      -- Now, we need to handle r_tail. This will be stubbed like the other r_tail match.
      match r_tail with
      | ABResult.value val_from_tail _ =>
        let check_val : Bool := val_from_tail = minimax g
        if !check_val then
          IO.println s!"failed check: LB from child, tail gave value. Expected val_from_tail ({val_from_tail}) = minimax g ({minimax g})"
        return ABResult.value val_from_tail (by sorry)

      | ABResult.lb _ => -- Tail recursive call resulted in beta cutoff. Value for g is beta.
        let check_lb : Bool := beta <= minimax g
        if !check_lb then
          IO.println s!"failed check: LB from child, tail gave LB. Expected beta ({beta}) <= minimax g ({minimax g})"
        return ABResult.lb (by sorry)

      | ABResult.ub _ => -- Tail recursive call value is <= alpha. Value for g is alpha.
        let check_ub : Bool := alpha = minimax g
        if !check_ub then
          IO.println s!"failed check: LB from child, tail gave UB. Expected alpha ({alpha}) = minimax g ({minimax g})"
        return ABResult.value alpha (by sorry) -- Return ABResult.value alpha

  | ABResult.ub proof_ub =>
    let checkRes_ub : Bool := beta <= minimax g
    if !checkRes_ub then
      IO.println s!"failed check: UB from child branch. Expected beta ({beta}) <= minimax g ({minimax g})"
    return ABResult.lb (by sorry)

def run_alphabeta_test (g: GameTree) : IO (ABResult g (-maxVal) maxVal) :=
  let pa_initial : (-maxVal >= -maxVal) := by rfl
  let pb_initial : (maxVal <= maxVal) := by rfl
  let pab_initial : (-maxVal < maxVal) := by decide        
  alphabeta g (-maxVal) maxVal pa_initial pb_initial pab_initial
```

## Proof Attempt

The next step would be to try to complete the proof by filling in the `sorry`s. Gemini tried
but was not able to make progress.
As in the previous post, I tried the proofs  manually, just to confirm the correctness of the implementation. 

The termination proof issue had a simple fix. `alphabeta` and `minimax` had the same recursive structure, and so it should have been recognized by Lean as a structural recursion like `minimax`, requiring no further termination proof. So why didn't it work? 
The problem was with the `match tail with ... | _::_ : ... alphabeta (GameTree.node tail)`
sequence. Lean was *supposed* to automatically infer that the recursive call is on a substructure of the original input, but was unable to in this instance, due to the way the `match` statement was used. 
Once `tail` is pattern matched to `_::_`, Lean seems to forget that the former `tail` is the same as the `tail` in the recursive call, as far as the termination proof is concerned. 
Changing it to 
`match tail with ...|tailh::tailt: ... alphabeta (GameTree.node (tailh::tailt))` fixed the issue:
Lean now recognize it as structural recursion and does not ask for further proof.

I was able to go through all the `sorry`s and confirm that the implementation is *essentially* correct. The caveat: in a few instances, Gemini was returning `ABResult.value alpha ...`
instead of `ABResult.ub ...` (which would be my intended solution).
Gemini was basing this on its (correct) general understanding of the Alpha-Beta algorithm, 
that in such cases, returning `alpha` is fine because the upstream caller does not care: it would not change the final result one way or the other. And indeed this implementation would pass all test cases. But I had set up the `ABResult` type to be able to pass around upper- and lower-bound certificates, and for the proofs to go smoothly it requires the coder to return bounds (e.g. `ABResult.ub ...`) when appropriate. 
This is a pretty subtle point, and perhaps I need to explain it more explicitly in the prompts next time, since it is different from what the LLMs are used to seeing regarding Alpha-Beta.

## Takeaways
- This was a success! Gemini was able to adopt the workflow, progress incrementally,
catch hallucinations as they arise, and eventually settle on a correct implementation.
- We should refine the prompts to make sure we get this behavior consistently across models.  
- Comments and suggestions welcome! Feel free to play with the code and try other models / coding assistants! 