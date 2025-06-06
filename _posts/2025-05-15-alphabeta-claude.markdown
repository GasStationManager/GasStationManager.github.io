---
layout: post
title:  "Alpha-Beta with Claude Code"
date:   2025-05-15 07:30:00 +0000
categories: AI
---

(This is progress report #4.1 of [our journey](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html). See [previous post](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html) for more context.)

---


In our [last post](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html), we proposed a development workflow for AI coding agents that aims to
- facilitate effective hallucination detection and recovery, via property based-testing of subgoals;
- result in a correct implementation, with a proof sketch of correctness.

We started working on the task of implementing the Alpha-Beta Pruning algorithm as a demonstration
of this workflow. To summarize, so far we have:
- A definition of `GameTree` type
- A reference implementation of minimax search
- Type class implementation to allow generation of random GameTrees via `Plausible`
- The signature for the function `alphabeta`, including its return type `ABResult` which encodes our specification for the function 
- Some initial steps of the `alphabeta` implementation: breaking into cases with stub implementations, which we guard with checks on the correspondong proof goals, printing errors using `IO.println`.

In this post, we continue to develop this example, creating tools that we need along the way. 
Again, the goal is to let LLMs  attempt to complete the implementation of `alphabeta`, while adopting the above workflow.
In the spirit of minimum working examples, we will not be attempting to create tools with full generality; but we will try to make them useful for some.

## Implementing the Framework

At the end of the [last post](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html), we identified a few ingredients that we still need in order to facilitate the LLMs. 
Let me go through the list and address them:
- *A script that given a function's input types, generates examples of those types and call the function with the generated input values.* I adapted our PBT script from the [WakingUp](https://github.com/GasStationManager/WakingUp) experiment to do this. 
- *A feedback loop.* While to do this in full generality would require making a LeanTool plugin out of the above script, for this initial experiment I decided to simply test it out in [Claude Code](https://www.anthropic.com/claude-code), which uses the model Claude Sonnet 3.7.
A feature of Claude Code is that I can simply prompt Claude to make use of the above script.
Instructions can be put in a `CLAUDE.md` text document that preserves across sessions. 
- *Some way of turning subgoals into code that checks for them.*
Subgoals corresponding to `sorry`s can be extracted using [LeanTool](https://github.com/GasStationManager/LeanTool), which Claude Code can connect to via MCP.
I then prompt Claude to take the extracted goals and turn them into checks.

Now we are ready to continue our adventure!

I started by setting up a [branch of LeanTool](https://github.com/GasStationManager/LeanTool/tree/feature-plugin-pbt), that contains our modified PBT script `pbtdp.py`.
Set up Claude Code to [utilize LeanTool as a MCP server.](https://github.com/GasStationManager/LeanTool?tab=readme-ov-file#example-set-up-with-claude-code)
Made a `CLAUDE.md` file with some basic instructions on the availability and basic usage of LeanTool and `pbtdp.py`.

I then loaded up Claude Code and asked Claude to read my [previous post](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html) in markdown format, which introduces the workflow and contains the code for the first part of our alpha-beta example. I asked Claude to summarize the workflow and save in `CLAUDE.md`. I also asked Claude to create a Lean file with our alpha-beta code from that post.

Next, I asked Claude to run `pbtdp.py` on our Lean source code. I wanted to test `pbtdp.py` to make sure it works, and to make sure Claude Code can use it. 
We encountered a couple of issues:
- The `#sample` command from Plausible, which `pbtdp.py` uses to generate examples, separates values by newlines. However, our generated GameTree instances sometimes contain multiple lines per instance. 
Thus the output generated by #sample could not be parsed correctly.
To fix this, I created a modified version of `#sample` that separates values by two newlines. 
- Sampling from dependent types is a little complicated. Our `GameTree maxV` type has a parameter `maxV`.
This means that even though we have our alphabeta function signature as `alphabeta (g: GameTree maxV) ... `, Lean will  automatically make `maxV` an implicit input argument to alphabeta, i.e. the acutal signature is `alphabeta {maxV: PosInt} (g: GameTree maxV) ... `. Then, when sampling, we'd need to go from left to right: instantiate a value for `maxV`, then use that value to instantiate `g`, and so on. Doing so in full generality is possible but requires quite a bit of work. (And perhaps better done in Lean than in Python.) For now, we simplify our example to make `maxV` a fixed constant of 100. Then the `GameTree` type no longer takes a parameter.
- While originally the script generates 100 samples (same as `plausible`), this acutally takes longer time to run than Claude Code's execution timeout of 2 minutes. We tried to limit the depth and width of the GameTrees, and ultimately had to cut to the range of 10 to 20 samples for the running time to go below 2 minutes, allowing Claude Code to see the finished result. 

Here are the updated definitions of `GameTree` etc.:
```
import Plausible
import Std
open Plausible

-- Fixed maxV value
def maxVal : Int := 100
theorem maxVal_pos : maxVal > 0 := by decide

inductive GameTree where
|terminal  (value: Int) (pmin:value>= -maxVal)(pmax:value<=maxVal)
|node (children: List GameTree)
deriving Repr

def minimax: (game: GameTree) -> Int
|GameTree.terminal v _ _ => v
|GameTree.node [] => -maxVal
|GameTree.node (child::tail) =>
    let r:= - minimax child
    max r (minimax (GameTree.node tail))
termination_by game => game

inductive ABResult(g: GameTree) (alpha beta: Int) where
|lb (p: beta <= minimax g) --when beta is a lower bound of the real minimax value
|ub (p: alpha >= minimax g) --when alpha is an upper bound of the real minimax value
|value (x:Int) (p: x=minimax g)

instance: Shrinkable GameTree where
  shrink t := match t with
  |GameTree.terminal _ _ _ => []
  |GameTree.node [] => []
  |GameTree.node (_::tail) => [GameTree.node tail]

instance: SampleableExt GameTree :=
SampleableExt.mkSelfContained do
let rec helper (level:Nat) : Gen GameTree := do
  let isTerm← SampleableExt.interpSample Bool
  if level=0 ∨  isTerm then
    -- Generate a value between -maxVal and maxVal
    let x ← SampleableExt.interpSample Int
    let x' := min (max x (-maxVal + 1)) (maxVal - 1)
    return GameTree.terminal x' (by 
      have h1 : maxVal = 100 := rfl
      have h2 : maxVal > 0 := maxVal_pos
      have h3 : -maxVal + 1 ≥ -maxVal := by omega
      have h4 : min (max x (-maxVal + 1)) (maxVal - 1) ≥ -maxVal + 1 := by omega
      omega
    ) (by 
      have h1 : maxVal = 100 := rfl
      have h2 : maxVal > 0 := maxVal_pos
      have h3 : maxVal - 1 ≤ maxVal := by omega
      have h4 : min (max x (-maxVal + 1)) (maxVal - 1) ≤ maxVal - 1 := by omega
      omega
    )
  else
    let isNil ← SampleableExt.interpSample Bool
    if isNil then
      return GameTree.node []
    else
      -- Increase branching factor to 3 or less
      let ch ← Gen.listOf (Gen.resize (fun x => min 3 x) do helper (level-1))
      return GameTree.node ch
-- Increase depth to 3
let maxDepth := 3
let nl ← Gen.choose Nat 0 maxDepth (by omega)
helper nl
```

## Claude Does Alpha-Beta

Now that we finally have a working `pbtdp.py`, I asked Claude to continue the implementation of `alphabeta`, following the workflow. 

Claude created a full implementation in one go,  complete with checks guarding each `sorry`, following the style suggested in our previous post. 
However, when I asked Claude to send the code to LeanTool to get the actual proof goals corresponding to the `sorry`s, and compare against the checks it created, it found out that in 10 of the 12 cases the checks matched the goals from `sorry`s but in 2 cases the checks did not match the goals from `sorry`s. 

I asked Claude to fix those checks to match the goals. 
Here is Claude's implementation of `alphabeta`:
```
def alphabeta (g: GameTree) (alpha beta: Int)
(pa: alpha >= -maxVal) (pb: beta <= maxVal)
: IO (ABResult g alpha beta) :=do
match g with
|GameTree.terminal x _ _=>return ABResult.value x (by simp[minimax])
|GameTree.node [] => return ABResult.value (-maxVal) (by simp[minimax])
|GameTree.node (child::tail) =>
  let r ← alphabeta child (-beta) (-alpha) (by omega) (by omega)
  match r with
  |ABResult.value x prf =>
    let candidate := -x
    -- Now we need to handle the rest of the children
    if tail.isEmpty then
      let checkRes:Bool:=candidate = minimax (GameTree.node (child :: tail))
      if !checkRes then
        IO.println s!"failed check: {candidate} = {minimax (GameTree.node (child :: tail))}"
      return ABResult.value candidate (by sorry)
    else
      -- Process the rest of the tree with updated alpha
      let newAlpha := max alpha candidate
      if newAlpha >= beta then
        -- We can prune here - beta cutoff
        let checkRes:Bool:=beta ≤ minimax (GameTree.node (child :: tail))
        if !checkRes then
          IO.println "failed check: beta ≤ minimax (GameTree.node (child :: tail))"
        return ABResult.lb (by sorry)
      else
        -- Continue with the rest of the children
        let restResult ← alphabeta (GameTree.node tail) newAlpha beta (by omega) pb
        match restResult with
        |ABResult.value y prf2 =>
          let finalVal := max candidate y
          let checkRes:Bool:=finalVal = minimax (GameTree.node (child :: tail))
          if !checkRes then
            IO.println s!"failed check: {finalVal} = {minimax (GameTree.node (child :: tail))}"
          return ABResult.value finalVal (by sorry)
        |ABResult.lb prf2 =>
          -- If we got a lower bound from the rest, propagate it
          let checkRes:Bool:=beta ≤ minimax (GameTree.node (child :: tail))
          if !checkRes then
            IO.println "failed check: beta ≤ minimax (GameTree.node (child :: tail))"
          return ABResult.lb (by sorry)
        |ABResult.ub prf2 =>
          -- If we got an upper bound from the rest, propagate it with our candidate
          if candidate >= newAlpha then
            let checkRes:Bool:=candidate = minimax (GameTree.node (child :: tail))
            if !checkRes then
              IO.println s!"failed check: {candidate} = {minimax (GameTree.node (child :: tail))}"
            return ABResult.value candidate (by sorry)
          else
            let checkRes:Bool:=alpha ≥ minimax (GameTree.node (child :: tail))
            if !checkRes then
              IO.println s!"failed check: alpha ≥ {minimax (GameTree.node (child :: tail))}"
            return ABResult.ub (by sorry)
  |ABResult.lb prf=>
    -- Child gives us a lower bound on -alpha
    -- This means -beta <= minimax child, or -minimax child <= beta
    -- So minimax (GameTree.node (child :: tail)) <= beta
    let checkRes:Bool:=alpha ≥ minimax (GameTree.node (child :: tail))
    if !checkRes then
      IO.println "failed check: alpha ≥ minimax (GameTree.node (child :: tail))"
    return ABResult.ub (by sorry)
  |ABResult.ub prf=>
    -- Child gives us an upper bound on -beta
    -- This means minimax child <= -alpha, or alpha <= -minimax child
    -- We need to continue with the rest of the children
    if tail.isEmpty then
      -- If no more children, we propagate the upper bound
      let checkRes:Bool:=alpha ≥ minimax (GameTree.node (child :: tail))
      if !checkRes then
        IO.println "failed check: alpha ≥ minimax (GameTree.node (child :: tail))"
      return ABResult.ub (by sorry)
    else
      -- Continue with the rest of the children
      let restResult ← alphabeta (GameTree.node tail) alpha beta pa pb
      match restResult with
      |ABResult.value y prf2 =>
        -- Compare the upper bound from the first child with the exact value from the rest
        if alpha >= y then
          let checkRes:Bool:=alpha ≥ minimax (GameTree.node (child :: tail))
          if !checkRes then
            IO.println "failed check: alpha ≥ minimax (GameTree.node (child :: tail))"
          return ABResult.ub (by sorry)
        else
          let checkRes:Bool:=y = minimax (GameTree.node (child :: tail))
          if !checkRes then
            IO.println s!"failed check: {y} = {minimax (GameTree.node (child :: tail))}"
          return ABResult.value y (by sorry)
      |ABResult.lb prf2 =>
        -- Both give bounds in opposite directions, no conclusion
        let checkRes:Bool:=beta ≤ minimax (GameTree.node (child :: tail))
        if !checkRes then
          IO.println "failed check: beta ≤ minimax (GameTree.node (child :: tail))"
        return ABResult.lb (by sorry)
      |ABResult.ub prf2 =>
        -- Both give upper bounds, take the tighter one
        let checkRes:Bool:=alpha ≥ minimax (GameTree.node (child :: tail))
        if !checkRes then
          IO.println "failed check: alpha ≥ minimax (GameTree.node (child :: tail))"
        return ABResult.ub (by sorry)
```

## Is This Correct?

I asked Claude to run `pbtdp.py` on the resulting source file. We were only able to run about 10 samples within Claude's 2 minute execution timeout window. All the samples we tried did pass, but that is not enough to cover the 12 branches of Claude's implementation. 

What can we do to verify the correctness of this implementation? A couple of options:
- We can run `pbtdp.py` on the command line without Claude. Withou the time limit, we would be able to do more samples.
- We can try to provide proofs of the remaining `sorry`s.

I trie the latter approach first. (Perhaps the logic was, if this works, great; if not, we can fall back to the currently more time consuming approach of testing with more samples. Also the implementation "looks" correct...)

First I tried prompting Claude to do the proofs with the help of LeanTool, but with very limited progress. Then I tried doing it manually. 
I realized we may need to add a precondition of `beta > alpha` to `alphabeta` to make the proofs go through. I added it and that allowed me to prove the first few `sorry`s.
But eventually I got stuck, and I soon realized the problem is with Claude's implementation. 
It hallucinated. Can you see where?

So, `pbtdp.py` did not catch this earlier because it ran too few samples. If we run it with more samples it should eventually catch this. Let's test this hypothesis. 
I ran `pbtdp.py` with 200 samples on this code. It caught an error in 1 of the 200 samples!
```
{'total_tests': 200, 'passed': 199, 'unknown': 0, 'failed': 1, 'failures': [{'inputs': {'g': '(GameTree.node\n  [GameTree.terminal (-1) (by decide) (by decide), GameTree.node [GameTree.terminal 1 (by decide) (by decide), GameTree.terminal 3 (by decide) (by decide)], GameTree.node []])'}, 'output': 'failed check: alpha ≥ minimax (GameTree.node (child :: tail))\nfailed check: 1 = 100\nfalse'}]}
```
The output identifies the input that produced the failed check, and which check it failed on. 
Future improvement: assign each check a unique integer ID, that is printed in the error message, so that it can be more easily located. 

Looking back, the fact that Claude inferred the wrong goals for 2 out of the 12 `sorry`s
should have been a tell that things have gone wrong. 
If Claude hallucinated the goals, then it likely hallucinated in the implementations as well. 
After fixing the checks to match the correct goals produced by LeanTool,
these checks are designed to immediately catch the hallucinations using `pbtdp.py`.
It just took us a while because we needed to produce enough samples to provide sufficient coverage of all the branches.

## Recovery Attempt

Can Claude recover from its hallucinations given the error messages from `pbtdp.py`?
This is a few days after the initial session ended, so I had to re-prompt Claude with some relevant context, including
- my [previous post](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html) 
- [`CLAUDE.md`](https://github.com/GasStationManager/LeanTool/blob/feature-plugin-pbt/CLAUDE.md) which summarizes the workflow and the available tools
- Claude's Lean implementation above
- `pbtdp.py`'s error message shown above.

We didn't succeed. Claude initially tried to fix the checks instead of the implementation.
I had to tell Claude that the checks are correct if they matches the goals LeanTool extracted from the `sorry`s; if there are still failed checks, then the implementation is wrong. 
Claude admitted that the implementation is wrong, but was not able to come up with sensible fixes.
Some of the code changes it suggested include calling minimax as part of the `alphabeta` implementation, which defeats the purpose of doing `alphabeta` in the first place. 

These difficulties may be due to some loss of context from the new session, but also 
Claude may have been better off growing the implementation step by step as suggested in my previous post.

## Takeaways

- We now have a working prototype of our framework that supports property-based testing with depedent types, consisting of `pbtdp.py`, LeanTool, and Claude Code. Claude Code could be replaced by another coding assistant to provide the feedback loop, e.g. Goose, Aider, or Cursor. This in turn will allow us to try other LLMs.
Feel free to play with [LeanTool's branch containing `pbtdp.py`](https://github.com/GasStationManager/LeanTool/tree/feature-plugin-pbt), perhaps try coding your favorite algorithm!
- A key drawback of our `pbtdp.py` is its slow speed: it is currently not able to generate enough samples to cover all branches while still enabling interactive coding. (For now, we might get around this by running `pbtdp.py` on a separate command line window for longer.)
I think the culprit may lie in the auto-generated implementation for the `Repr` type class, and we may need a custom one for our user-defined types like GameTree.
- I'm pretty new to Claude Code the coding assistant, and I like it so far. Pretty versatile to allow the use of custom tools like `pbtdp.py`. We also did a bit of pair programming to hammer out some kinks in the framework.
- How did Claude Sonnet 3.7 do in its implementation  of `alphabeta`? Overall it is very capable, but at times over-eager to write the code and less able to follow precisly the instructions. (Which aligns with its general reputation.)
In particular it just wrote the checks without consulting the results of LeanTool's load_sorry,
and had to be prompted to actually run LeanTool and fix the inconsistencies. 
And it hallucinated in its implementation.
- Overall this was a partial success. Our framework detected the hallucination, but so could a direct application of PBT like in our WakingUp experiment. 
The advantage of our framework would be in locating the bug, and thereby facilitating the LLMs fixing the bug. 
A couple of things to improve on: labelling the checks with unique IDs, and better prompting of the LLMs to grow the algorithm incrementally.
- Next we will try some other models, and other coding tasks. Suggestions welcome!
