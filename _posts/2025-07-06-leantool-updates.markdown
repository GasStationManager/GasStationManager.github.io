---
layout: post
title:  "Proving Alpha-Beta (Episode 2), Sorry Hammer and More"
date:   2025-07-06 07:30:00 +0000
categories: AI
---

(This is progress report #4.3 of [our journey](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html).)


---

This post is a progress report on a few different topics, all revolving around [LeanTool](https://github.com/GasStationManager/LeanTool)'s functionalities.


## Proving Alpha-Beta, Episode 2: Claude Code Revisited

A quick recap: in the last few posts, we have been developing a workflow for AI coding, that aims to 
- facilitate hallucination detection and recovery via property-based testing, and 
- produce correct code with proof of correctness.

And we have been testing it with various LLM coding models on the [Alpha-Beta challenge](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html).

This time, I am revisiting Claude Code. What changed since [the last time we tried Claude Code](https://gasstationmanager.github.io/ai/2025/05/15/alphabeta-claude.html)?
- I am trying the latest iteration of our workflow, [Code-Test-Prove](https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html). As the name suggests, it interleaves proving steps with the coding and property-based-testing steps. 
- Last time Claude Code was using the model Sonnet 3.7. Since then, Anthropic has released their newest series of models Sonnet 4 and Opus 4. So I will be using these new models.


The set up:
- Claude Code configured with [LeanTool MCP](https://github.com/GasStationManager/LeanTool).
- `pbtdp.py`, our property-based testing script. This is available in the LeanTool package as both a command-line script and as a MCP tool `run_tests`. Claude Code supports both modes.  This time I'm going with the command-line version. Our experience in the [previous episode](https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html) suggests that the command-line version is lighter on the token usage since it doesn't need to pass the content of the entire source file as a string. Besides cost, this would hopefully help preserve the context window.
- `CLAUDE.md` already has instructions about usage of the above tools, and instructions about the workflow from the previous Claude Code episode. I updated the instructions to summarize the Code-Test-Prove workflow. Explicitly mentioned similarity to test-driven development to get Claude into that mindset.


Let's start the session!
- Same starter code and initial prompts as previous episodes.
- Claude Code's default model is Sonnet 4; the user can switch to the more expensive Opus 4.
- Ever since the time [Sonnet 3.7 tried to output a complete implementation in one go](https://gasstationmanager.github.io/ai/2025/05/15/alphabeta-claude.html), I have tried to make the models go slow initially; making sure they are able to use the tools, and to follow the workflow: start with a stub implementation, run LeanTool to check syntax and extract goals, make sure the run-time checks matches the goals, then test by running `pbtdp.py`.
- Sonnet 4 was eager to start coding, but after some prompting was able to get a good grasp of the tools and the workflow.
- Sonnet does not know when to switch to proving mode. I ended up asking it to start trying to prove the `sorry`s at "random" points in the session, but it was not very systematic. 
- So what should be the right timing to switch to proving? This is actually non-obvious:
at any point in the middle of the workflow, after `pbtdp.py` finished running, we will have:
some branches of the implementation failing the tests, and some branches of the implementation passing the tests. Should we start trying to prove a sorry associated with the branch that passed the tests, or try to fix the branch that is failing the tests?
- I think the following is the answer that makes most sense, and aligned with the intention of the workflow:
if a branch's implementation is intentionally a stub implementation, we know it will fail the tests; we will need to fix this branch but not necessarily right away. 
If besides these stub failures, all other tests pass: this likely happens right after we finished implementing (or fixing) a branch, and it is passing the tests. This is when we can switch to attempting a proof for the branch.
On the other hand, if there are other test failures besides the stubs, this is when the tests have discovered a bug in an attempted implementation of a branch, and we should focus on fixing that branch right away.  
- And that is in the ideal situation when the tests always detect a bug. In reality,
`pbtdp.py` was only able to run about 25 to 30 samples before it hits Claude Code's 2-minute timeout limit.
We could run `pbtdp.py` multiple times, and Claude does that sometimes.
Ultimately, `pbtdp.py` was very frequently helpful at detecting hallucinations, but passing it could not serve as conclusive evidence that the implementation was correct, due to the limited sample size.


- Sonnet 4 got stuck at a proof attempt at some point. Meanwhile the tests were passing but we didn't get enough samples to be sure. At this point I switched to Opus 4. This perhaps wasn't strictly necessary; I could have tried to ask Sonnet to run `pbtdp.py` more times.
But I was curious how Opus would do at the proof tasks.
Opus made some very nice progress (more on that below), but I was very soon hitting its usage limit and had to wait to use it again. I continued with Sonnet to finish up the episode.

- Opus 4 seems to have stronger reasoning abilities, which allowed it to make more progress on proving the `sorry`s than Sonnet did. The most impressive thing I saw Opus did though, is it actually was able to **detect a bug in the implementation via its proof attempt**. 
This was one of the things I wished for when I proposed [Code-Test-Prove](https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html), but I wrote at the time that I thought it would require a model that is a very strong Lean prover to be able to get much useful information out of a failed Lean proof attempt. And that I thought such a model is not here yet.
- Here's how Opus did it. Recall that the main challenge with trying to detect bugs via failed proof attempt, is that when a proof attempt fails, how do we know whether it is due to our lack of Lean proving ability, or due to a bug in the implementation?
Opus, when it failed at proving a `sorry`, switched back to *informal, proof-sketch level reasoning.* It can get the goal statement and the premises corresponding to the `sorry` from calling LeanTool. It then tries to formulate an informal proof sketch. As long as it believes that the proof sketch works, it is worth keep trying to formalize the argument into Lean, possibly involving multiple rounds of calling LeanTool and iteratively fixing the proof attempt. 
On the other hand, if it senses that the proof sketch doesn't work, it will investigate the possibility that the implementation is wrong. 
- How generalizable is this method? It requires the model to be at least decent in Lean to be able to make progress, but also a very strong informal reasoner. 
I think this is very much within reach of the current state-of-the-art reasoning models, like Gemini-2.5-Pro, or o3 strapped with another agent that does the coding and tool-calling (I should try this with Aider architect mode someday). 
As we get models with stronger and stronger Lean proving ability, they will be able to get more information out of the failed attempt to feed into the subsequent informal reasoning, 
but the overall structure still makes sense: you still need some transition from formal to informal.

- After I had to switch back to Sonnet, I just let it run with auto-approved file editing and tool-calling. Each individual action of Sonnet might not be the best move, but now that it got a good grasp of the workflow, it was able to get good feedback from the tools and keep making progress. It finished with a complete implementation with proof of correctness:

```
import Mathlib.Tactic.Linarith

/- Rest of the starting definitions omitted; they are the same as in the previous post -/

def alphabeta (g: GameTree) (alpha beta: Int)
(pa: alpha >= -maxVal) (pb: beta <= maxVal) (pab : alpha < beta)
: IO (ABResult g alpha beta) := do
match g with
| GameTree.terminal x => return ABResult.value x (by simp[minimax]) 
| GameTree.node [] => return ABResult.value (-maxVal) (by simp[minimax])
| GameTree.node (child::tail) =>
    let r ← alphabeta child (-beta) (-alpha) (by linarith) (by linarith) (by linarith)
    match r with
    | ABResult.value x prf =>
      let candidate := -x
      if h_cand_beta: candidate >= beta then
        return ABResult.lb (by simp [minimax, candidate, prf] at *; omega)
      else
        let newAlpha := max alpha candidate
        let tailResult ← alphabeta (GameTree.node tail) newAlpha beta (by omega) (by assumption) (by omega)
        match h_tail: tailResult with
        | ABResult.value y _ =>
          let finalCandidate := max candidate y
          return ABResult.value finalCandidate (by simp [minimax]; omega)
        | ABResult.lb p_tail =>
          -- Tail value >= beta, so overall value >= beta
          return ABResult.lb (by simp [minimax]; right; exact p_tail)
        | ABResult.ub p_tail =>
          -- p_tail: newAlpha >= minimax (GameTree.node tail)
          -- Case analysis on whether alpha >= candidate
          if h_alpha_cand: alpha >= candidate then
            -- If alpha >= candidate, then newAlpha = alpha
            -- We can prove alpha >= minimax (GameTree.node (child :: tail))
            return ABResult.ub (by 
              simp [minimax] at *
              -- newAlpha = alpha since alpha >= candidate
              have h_newAlpha : newAlpha = alpha := by simp [newAlpha, max_eq_left h_alpha_cand]
              rw [h_newAlpha] at p_tail
              constructor
              · -- alpha >= -minimax child since alpha >= candidate = -minimax child
                rw [← prf]; exact h_alpha_cand
              · exact p_tail  -- alpha >= minimax (GameTree.node tail)
            )
          else
            -- If alpha < candidate, then newAlpha = candidate  
            -- Since candidate >= minimax tail, the overall value is candidate
            -- Since alpha < candidate, we should return the exact value candidate
            return ABResult.value candidate (by
              simp [minimax]
              -- Goal: candidate = max (-minimax child) (minimax (GameTree.node tail))
              -- We have: candidate = -x and x = minimax child and candidate >= minimax (GameTree.node tail)
              have h_newAlpha : newAlpha = candidate := by simp [newAlpha, max_eq_right (le_of_not_ge h_alpha_cand)]
              rw [h_newAlpha] at p_tail
              -- candidate = -x = -minimax child, so candidate >= minimax tail means -minimax child >= minimax tail
              have h_equiv : candidate = -minimax child := by simp [candidate]; rw [← prf]
              rw [h_equiv] at p_tail
              rw [h_equiv]
              exact (max_eq_left p_tail).symm
            )
    | ABResult.lb prf =>
      -- prf: -alpha <= minimax child (the second argument to the recursive call)
      -- This doesn't give us enough info about the parent, so continue with tail
      let tailResult ← alphabeta (GameTree.node tail) alpha beta (by assumption) (by assumption) (by assumption)
      match tailResult with
      | ABResult.value y p_tail_val =>
        -- We know -minimax child <= alpha (from prf)
        -- The overall value is max(-minimax child, y)
        -- But we don't know -minimax child exactly, just that it's <= alpha
        -- If y >= alpha, then max(-minimax child, y) = y
        -- If y < alpha, then we can't determine the exact value
        if h_y_alpha: y >= alpha then
          return ABResult.value y (by 
            simp [minimax, p_tail_val]
            -- Need to show: y = max (-minimax child) y
            -- Since -minimax child <= alpha <= y, we have max(-minimax child, y) = y
            have h1: -minimax child <= alpha := by linarith [prf]
            have h2: -minimax child <= y := by linarith [h1, h_y_alpha]
            omega
          )
        else
          -- y < alpha, and -minimax child <= alpha
          -- The max could be anywhere from y to alpha
          return ABResult.ub (by
            simp [minimax]
            -- Goal: alpha >= max (-minimax child) (minimax (GameTree.node tail))
            -- We have: -alpha <= minimax child, so -minimax child <= alpha
            -- We have: y = minimax (GameTree.node tail) and y < alpha from h_y_alpha
            have h1: -minimax child ≤ alpha := by linarith [prf]
            have h2: minimax (GameTree.node tail) < alpha := by rw [← p_tail_val]; linarith [h_y_alpha]
            constructor
            · exact h1  -- alpha >= -minimax child  
            · linarith [h2]  -- alpha >= minimax (GameTree.node tail)
          )
      | ABResult.lb p_tail2 =>
        return ABResult.lb (by simp [minimax]; right; exact p_tail2)
      | ABResult.ub p_tail3 =>
        return ABResult.ub (by
          simp [minimax]
          -- Goal: alpha >= max (-minimax child) (minimax (GameTree.node tail))
          -- We have: -alpha <= minimax child, so -minimax child <= alpha
          -- We have: alpha >= minimax (GameTree.node tail) from p_tail3
          have h1: -minimax child ≤ alpha := by linarith [prf]
          constructor
          · exact h1  -- alpha >= -minimax child
          · exact p_tail3  -- alpha >= minimax (GameTree.node tail)
        )
    | ABResult.ub prf =>
      -- prf: -beta >= minimax child
      -- This means -minimax child >= beta, so we should prune (beta cutoff)
      return ABResult.lb (by simp [minimax]; left; linarith)
```

- Looking at the proofs, we see that it has a more varied style than the 
[output from o3/GPT 4.1](https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html).
This time, I did also suggest `omega` as a tactic to try, but Opus/Sonnet got to do some of their own exploration as well. Sometimes `omega` didn't work because there was a bug in the implementation, as mentioned above. In the end, Opus/Sonnet was able to make it work.

- Overall, this was a much more pleasant outing than the [previous episode](https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html).
Sure, Sonnet hallucinates sometimes, but hallucination detection and recovery is exactly what this workflow was designed to do.  On the other hand, o3's lying was kind of harder to deal with; in this framework it just ends up lying to itself and fail to get benefits from the tools.
Opus/Sonnet was also able to be more agentic, capable of going long stretches without needing human intervention. 

- To-dos on the tooling side: better reporting of statistics for the PBT script, on which branch was covered, by how many samples. 
Codifying some of the stuff we learned into `CLAUDE.md` and/or system prompts, including
timing of switching to proof mode; and
the failed-proof-to-debugging route that Opus showed.



## Sorry Hammer

I have always been a fan of the [Draft-Sketch-Prove](https://arxiv.org/abs/2210.12283) approach; I think it is a great way to set up the division of labor between LLM-based informal reasoning
and informal-to-formal translation, and automated theorem proving tools.  [LeanTool](https://github.com/GasStationManager/LeanTool)'s system messages and features generally encourage the LLMs to decompose the proof task by starting with a proof sketch, and getting the goals from the sorrys (thanks to Pantograph's load_sorry). What had been missing was a good hammer tactic that can help solve some of the smaller goals. 
That has changed lately with the recent release of [LeanHammer](https://github.com/JOSHCLUNE/LeanHammer), and other tools including Canonical, egg, grind etc coming along. 

To help facilitate the use of hammers by LLMs, I have added the following (very experimental) "Sorry Hammer" feature to LeanTool: if the LLM passes a Lean source code with `sorry`s to the tool, and choose to activate the `sorry_hammer` option of the tool call, then the tool will try to replace the first `sorry` with a hammer tactic. By default it is `hammer` from LeanHammer, but this is configurable, and can even be a list of tactics to try one by one (the list is converted to `first | tac_1 | tac_2 | ..`).

(Alternatively, you could directly prompt the LLM to use the `hammer` tactic. And that is fine too.
I think the sorry_hammer can be a useful way to explore different configurations and combinations of tactics; and also potential further automations, see below.)

LeanTool allows the LLM to iteratively refine its proof attempt: if the hammer fails, it can go back to the drawing board and try replacing the sorry with a more fine-grained proof sketch. (Right now you might need to prompt the LLMs; but if you find a prompt that works well, let me know and I can add it to the system prompt!)

Actually, if the hammer fails, the other possibility is that the `have` statement we are trying to prove is false, i.e. the proof sketch (or in the coding case, the implementation as well)
is wrong. 

Knowing which is the case is actually extremely valuable. 
This shouldn't be a surprise coming from me; I have been focusing on hallucination detection for the past several posts, including earlier in this post. 
So, what to do? We could try property-based testing tools, including `plausible` and the `pbtdp.py` script I've been working on. Here, since we already have access to the hammer, I thought it would be natural to try the hammer on the negation of the goal. If the hammer succeeds in proving the negation, we know the `have` statement is false. This can serve as a complement to the property-based testing approach. So:
- I have implemented a Lean tactic `check_false` that applies a hammer to the negation of the goal. This ended up requiring a bit of metaprogramming. (Thanks Chase Norman for suggestions on the implementation.) `check_false` has a similar user interface as `plausible`: raises an error if the negation is proven; otherwise acts like `sorry`.
- Sorry Hammer will now try `check_false` if the hammer fails to prove the goal at first. 


This is now available in the latest version of [LeanTool](https://github.com/GasStationManager/LeanTool), including its MCP mode.  Or you can try out its API server (by pointing your coding assistant to http://www.codeproofarena.com:8800/v1 as the base URL.)

Let me know how it goes! Feature requests welcome. 
- what combination of tactics tend to work best as hammer for your use case? 
- rewriting with the proof from the `Try this` suggestion: for now you can prompt the LLM to do it. One could try to automate this...


## LeanTool + LeanExplore

When I observe some of the proof attempts by the models, they often have a good grasp of the mathematical arguments required for the proof, but stuggle to translate them into Lean. 
LeanTool helps in allowing the models to iteratively fix the syntax issues. 
But another difficulty, especially for more mathematical proofs, is that we often want to 
make use of known results instead of proving everything from scratch. These known results are often available as Lemmas in Mathlib, but the models often do not know the exact name or the type of the lemma. (They were likely trained on an older version of Mathlib.)
This is where search engines can help, and I had put in LeanTool's system prompt some instructions
on using the built-in `#moogle` and `#leansearch` commands provided by the LeanSearchClient package. They help sometimes, but it seems Moogle's database lags behind the current Mathlib version, whereas LeanSearch's server is often down. 
 

[LeanExplore](https://www.leanexplore.com) is a recently-released search engine for Lean libraries including current versions of Mathlib. It provides an [MCP option](https://www.leanexplore.com/docs/mcp).
I wanted to try composing the functionalies of both LeanExplore and LeanTool, 
and see if that improves the models' proving ability. 
MCP makes it easy to do such compositions: just add both MCP servers to your app of choice.
This time, I tried Claude Desktop
and configured it to connect to the [LeanTool](https://github.com/GasStationManager/LeanTool) and LeanExplore MCP servers.

A note on the set up. I have been serving LeanTool MCP from a Linux machine, 
while my Claude Desktop was running in Windows and does not support remote MCP servers. 
What to do? It turns out we can use tools like Supergateway to serve as proxies to translate remote MCP to local `stdio` ones and vice versa. My Claude Desktop config file ended up looking like
```
{
    "mcpServers": {
        "LeanTool": {
            "command": "npx",
            "args": [
                "-y",
                "supergateway",
                "--sse",
                "<my remote leantool mcp server address>/sse"
            ]
        },
        "LeanExplore": {
          "command": "leanexplore",
          "args": [
            "mcp",
            "serve",
            "--backend",
            "api",
            "--api-key",
            "<leanexplore-api-key>"
          ]
        }
    }
}
```


As an exercise, I asked Claude Sonnet / Opus to prove the theorems and lemmas from [Morph Labs/Trinity's recent autoformalization result](https://github.com/morph-labs/lean-abc-true-almost-always/tree/main). 
For each theorem/lemma, I prompted with the Lean theorem statement, and which lemma it depends on according to the published blueprint. They were able to prove the first dozen or so lemmas before I hit my usage limit for the day. 
(I start with Sonnet which is cheaper, and switch to Opus if it gets stuck, which happened for a couple of those lemmas.)

Overall they are able to effectively use multiple calls to LeanExplore's search tool and LeanTool's code interpreter to iteratively refine their proof attempts.

Here is a [file](https://github.com/GasStationManager/LeanTool/blob/main/examples/pabc_claude.lean.txt) that contains the proofs so far. 
One example: here is the first lemma.
```
import Mathlib

lemma two_rpow_ge_add_one (x : ℝ) (hx : x ≥ 1) : 2 ^ x ≥ x + 1 := by
  -- Apply Bernoulli's inequality: 1 + p * s ≤ (1 + s) ^ p with s = 1, p = x
  have h : 1 + x * 1 ≤ (1 + 1) ^ x := 
    one_add_mul_self_le_rpow_one_add (by norm_num : (-1 : ℝ) ≤ 1) hx
  -- Simplify and rearrange
  simp only [mul_one] at h
  have : (1 + 1 : ℝ) ^ x = 2 ^ x := by norm_num
  rw [this] at h
  rwa [add_comm]
```
I actually tried this with another model in a setting without LeanExplore. The model knew that the lemma can be proved by utilizing Bernoulli's Inequality, but did not know what that lemma is called in Mathlib. Trying to prove the result from scratch using Calculus ended up being too difficult. Here, with the help of LeanExplore, Sonnet could use Bernoulli's inequality provided by Mathlib, and the rest of the proof was relatively easy.

I think these tools, combined with capable models like Sonnet & Opus, can already be helpful to people working on formalization of mathematics.

I do want to say that I don't mean to make Morph lab's [autoformalization result](https://github.com/morph-labs/lean-abc-true-almost-always/tree/main) sound less impressive than it is; the work is very impressive and I am a fan of it. 
Part of the work was a human-and-AI-combined effort to break the task into a blueprint of smaller lemmas, that is the part we are not re-doing here. Our excercise was just taking the lemma statements as the starting point. 





