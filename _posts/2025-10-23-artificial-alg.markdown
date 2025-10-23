---
layout: post
title:  "Artificial Algorithms"
date:   2025-10-23 07:30:00 +0000
categories: AI
---

Work on this blog post is generously supported by [Axiom Math](https://axiommath.ai/).

---

I have recently started a Github repository [Artificial Algorithms](https://github.com/GasStationManager/ArtificialAlgorithms), a collection of verified algorithms in Lean, implemented and proved by AIs. Primary goal of the repo is to serve as a place for sharing examples, recipes, and experiences on AI-assisted coding and verification of code. Secondary goal is to be potentially useful as a library of verified algorithms, that can be used to build more complex projects with provable guarantees.

Included in the collection are some algorithms that have been documented in earlier posts of this blog: [Memoization](https://gasstationmanager.github.io/ai/2024/12/03/memoization1.html), [Dynamic programming with the Rod-cutting example](https://gasstationmanager.github.io/ai/2024/12/09/dp2.html), and [Alpha-Beta Pruning](https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html).

Also included is a [contribution](https://github.com/GasStationManager/ArtificialAlgorithms/blob/main/ArtificialAlgorithms/DynamicProgramming/Knapsack.lean) by Huỳnh Trần Khanh of a solution to the Knapsack problem, and proof of optimality. It was translated from his [Coq/Rocq proof](https://github.com/huynhtrankhanh/CoqCP/blob/main/theories/Knapsack.v)
using Claude Code, with LeanTool and LeanExplore.

More contributions are welcome and appreciated!

In the rest of this post, I will highlight a few other algorithms that has been included in the repository, and comment on the experience.

## Insertion Sort and Selection Sort

[InsertionSort.lean](https://github.com/GasStationManager/ArtificialAlgorithms/blob/main/ArtificialAlgorithms/Sorting/InsertionSort.lean)
and [SelectionSort.lean](https://github.com/GasStationManager/ArtificialAlgorithms/blob/main/ArtificialAlgorithms/Sorting/SelectionSort.lean)
are implementations and proofs of the two classic sorting algorithms. 
They are done by Opus 4/Sonnet 4 on Claude Desktop with LeanTool and LeanExplore installed as MCP servers.

The AIs initially had trouble completing the proofs. What helped was promptinng the AIs to adopt the style where the proofs are interleaved in the implementations. This is accomplished by prompting with starter code with complete implementations of the sorting function and helper functions (adopted from earlier iterations), with postconditions encoded in return types.


## Divide and Conquer

Three classic divide-and-conquer solutions, [max subarray sum](https://github.com/GasStationManager/ArtificialAlgorithms/blob/main/ArtificialAlgorithms/DivideConquer/MaxSubarraySum.lean), [binary search](https://github.com/GasStationManager/ArtificialAlgorithms/blob/main/ArtificialAlgorithms/DivideConquer/BinarySearch.lean), and [quickselect](https://github.com/GasStationManager/ArtificialAlgorithms/blob/main/ArtificialAlgorithms/DivideConquer/QuickSelect.lean).

In general, divide-and-conquer algorithms are a bit tougher to formally verify. Intuitively, 
we needed to leverage some additional mathematical structure about the problem to make the algorithm work (and to show that it is correct). In binary search and quickselect, it is the total ordering of the numbers, and in particular the transitive property.
In max subarray sum, it is (among other things) the associativity of addition and how addition preserves ordering.

As a result, the proofs were getting long, and Claude Desktop 
was having trouble with keeping track of the proof, and will reach the limit of the context window
(on Claude Desktop this would mean hitting the maximum length of a conversation).

So I had to continue the work in a coding assistant environment, like Claude Code and Cursor,
which keep the current snapshot of the proof attempt in a file, and allow the model to make edits to it. One technique I found useful was to let the AI factor out certain technical subtasks as lemmas, then send the lemma to a separate environment (like Claude Desktop) to be proved. 


## Value Iteration: Adventure with the Noncomputable

Reinforcement learning is one of my favorite topics, and is becoming more and more relevant in AI today. I thought it'd be fun to do some algorithms and proofs in RL.

This was my original motivation. I have done some more thinking since then, and now believe that there might be more to this beyond having fun. If you read [AI 2027](https://ai-2027.com/), along their predicted route of self-improving AI towards AGI, there is AIs writing code, and also AIs doing AI research. I think that is quite plausible, and not an uncommon belief. And as AIs are getting stronger, I am sure people will start trying that, if not already.

Letting AIs do AI research has the same kind of safety risks as [AI coding](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html): how do you trust the output produced by AIs? 
And I think formal methods can play an important role in the solution. Although much of modern AI research is empirical, there are important theoretical foundations. And perhaps with the help of AIs, more of AI research could become mathematically proven. And when GPT-6 produces the next breakthrough AI algorithm, we would feel safer if it comes with a machine-checkable proof.
And even better if the algorithm is implemented in a proof-capable programming language like Lean, 
so that you can directly run the code and be confident that it has the claimed properties.


Let's start with the classic value iteration algorithm.
So the task is to define the value iteration algorithm, and prove that it converges.

I wanted the code to be runnable, while still possible to prove properties about, so chose to do the implementation in rational numbers (`Rat`). (Background: in Lean, operations with `Real` are not computable; while `Float`s are computable but currently there is no library support for proving any properties of `Float` operations. That may change in the future; there is some ongoing work porting Coq/Rocq's Flocq libray to Lean.)

Working with Claude Code, we were able to prove that the Bellman operator is a contraction map; but to prove convergence, traditionally the proof will need the Banach fixed point theorem, which would only work for Real numbers (and hence noncomputable). We ended up going with the following plan: prove convergence using a (noncomputable) definition of the value iteration algorithm with Reals, then have a computable definition of the algorithm with rationals, then prove that the rational version and the Real version give equal results, when given a rational input.

[Here's the proof](https://github.com/GasStationManager/ArtificialAlgorithms/blob/main/ArtificialAlgorithms/AI/ValueIterationComplete.lean). Now that we are in the regime of longer proofs, much of this was done in Claude Code. Some individual lemmas were sent to Claude Desktop with Opus 4.1 and Cursor with GPT 5. 

## Towards Efficient Computation of Value Iteration via Rounding

A drawback of the exact value iteration implementation with rationals above is that computation cost (in time and space) could blow up: each exact rational operation (e.g. multiplying things by the discount factor) will increase the represenation size of the rationals involved. 

In [this file](https://github.com/GasStationManager/ArtificialAlgorithms/blob/main/ArtificialAlgorithms/AI/ApproxValueIterationInt.lean), I asked Codex CLI to formalize an approximate variant of value iteration with the simplest rounding scheme: do the Bellman operator computation in exact Rational arithmetic, then round to the nearest integer. Then repeat. This ends up working sufficiently well for value iteration (and other contraction maps): the rounding errors accumulate but gets squashed by the discount factor, so we end up with a constant error bound that depends on the discount factor. In practice you would pre- scale up the reward function by an appropriate amount so that this constant error bound is acceptable. (Or equivalently, instead of round to integers, round to the nearest integer multiple of some h.)

This was done mainly in Codex CLI by GPT-5 (med and high), with two lemmas solved separately by Sonnet 4. My first time trying Codex CLI on a larger Lean proof, and I must say I liked the experience. OpenAI's models have always been strong at informal reasoning, now their Lean ability seems to be catching up to Claude.

This proof is fairly reusable, e.g. if instead of rounding to integers we use dyadic rationals, or a future float library, as long as one can prove a constant error bound for one step of the Bellman iteration implementation, the rest of the proof can be reused to show a constant error bound on value iteration.

## Takeaways

The main observation is that as we tackle more complex, longer proofs, this goes beyond the ability of chat apps like Claude Desktop; the model will struggle to keep all of the Lean proof in the context window, let alone the back and forth with tool calls. This is where coding assistants like Claude Code and Codex CLI come in, which helps by managing Lean proofs as files. 

In this regime, LeanTool becomes less helpful; Claude Code is able to compile the proof with `lake build` etc and get feedback directly. I'm doing a bit of rethinking, and will hopefully adapt LeanTool to be more useful in a file-based environment. 
Ultimately, I think the main bottleneck for LLMs to do longer Lean proofs will be context management. I am exploring some ideas. Anyways, thanks for reading! Until next time...