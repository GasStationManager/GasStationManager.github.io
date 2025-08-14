---
layout: post
title:  "Thoughts on Informal and Formal Reasoning"
date:   2025-08-11 07:30:00 +0000
categories: AI
---

(Sam Altman in a recent interview said that (paraphrasing) writing can be a helpful tool to clarify the ideas.  I'm following his advise and doing a thinking-out-loud post.)

---

Recently, multiple labs have claimed to have achieved gold-medal level performance at IMO. 
Some used informal reasoning (OpenAI, Google Deepmind); some did formal proofs with Lean (Bytedance Seed, Harmonic).

Which approach is better? What will future  mathematical-reasoning AIs look like?

I have [previously expressed](https://gasstationmanager.github.io/ai/2025/02/13/leantool.html) my opinion that we ultimately need both. And I have developed coding/reasoning workflows like [Code-Test-Prove](https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html) accordingly, leveraging both the formal and the informal.

I think it is worth diving into the interplay between various forms of informal and formal reasoning. Ultimately we would like to develop reasoning patterns that get the best of both worlds: the speed and the freedom from informal reasoning, and the rigorousness and safety of formal reasoning. 

## The Levels

There was the traditional dichotomy of System 1 vs System 2, "Thinking, fast and slow".
System 1 is what a single forward pass of a neural network (or an autoregressive genration of a transformer) produces. System 2 is about (leveraging system-1 outputs, but) spending more compute at inference time to get a higher-quality output. E.g. search, chain-of-thought reasoning.
Later popularized by AlphaZero, a feedback loop that uses system-2 search procedure to generate higher-quality data to train better and better system-1 neural networks for value and policy functions.


Then, we realize that even within System 2, there are different kinds of reasoning.
Let's talk about informal vs formal. For purpose of this post, let's define informal reasoning 
as reasoning without access to a formal verifier (like Lean compiler or REPL); and formal reasoning as reasoning that 
can access  feedback from a formal verifier.

I think it is useful to be a bit more fine-grained, and define these four phases:

- **Informal, non-rigorous.**
Non-rigorous is not meant to be perjorative. In fact this is where the magic happens; stuff that does not (yet) have a formal counterpart. Perhaps what people call research *taste*.
Exploration; experimenting with examples to identify patterns. 
Forming a conjecture, with informal justification. Perhaps outline of a plan for a rigorous proof.

- **Informal, rigorous.**
We have a conjecture we want to try to prove, and our task is to provide a mathematically rigorous proof of the conjecture. Intuition developed in the non-rigorous phase will help guide us.

- **Formal reasoning as programming.**
Mathematical objects and proofs are now objects and functions in a programming language like Lean.
The reasoner trying to prove `P -> Q` is writing a function `f: P -> Q` that satisfies the syntax rules and type-system rules of the language. 
The resulting formal proof is verified by the Lean proof checker, and any outputs and error messages is fed back to the reasoner, allowing it to repair the proof if needed.

Our strategy here is going to be heavily informed by the non-rigorous and rigorous informal phases. Another mode is the *autoformalization* task: we are given a rogorous math proof from a paper or textbook, and need to turn it into a Lean proof.

- **Formal reasoning as search.** 
A proof task is cast as a search problem. E.g. in tactic mode, the states are goal states, actions are possible tactics, and our task is to find a sequence of tactics that transforms from the initial goal state a successful terminal state where no unproved goal remain.

Examples include AlphaProof, and similar approaches. These are often specialized transformers trained via RL; perhaps a system-1 neural networks combined with a system-2 search like MCTS.

This is also where automated theorem proving (ATP) tools can be applicable, stuff that we sometimes don't think of as AI, including SAT and SMT solvers, linear and integer programming, and hammer tactics that package them together.


## How to Combine Them

As the ordering suggests, a natural flow is to go top-down: start with informal non-rigorous reasoning, then make it rigorous, then translate the argument to Lean, 
and use ATP tools like hammers to close some of the simpler subgoals.

Draf-Sketch-Prove (DSP) is an influential approach that captures this intuition. A key step is producing a formal proof sketch: a sequence of assertions (with placeholders for proofs) that represents the structure of the underlying mathematical argument. Then each proof subgoal is passed to a hammer.

**Formal Feedback.** Perhaps also important is feedback from the formal side to the informal side. 
Feedback from Lean in the formal-programming  and/or formal-search phase could 
update the reasoner's belief about whether the current proof sketch is promising (or even correct).
Counterexample-finding can be extremely useful. 
This can include tools for property-based testing like Plausible (and my ad-hoc scripts);
as well as SMT or other ATP based approaches.

In the context of coding tasks, this relates to the [hallucination detection](https://gasstationmanager.github.io/ai/2025/01/22/hallucination.html) work that I've been focusing on in the past few months.

**Denser and more immediate feedback.**
After getting feedback from Lean, the reasoner could spend a long chain of thought deliberating,
before sending another formal proof to be verified. E.g. this is what Kimina Prover does.
But then the feeback will be very sparse and very delayed.
So while long chain-of-thought could be optimal when you are not expecting to get Lean prover feedback,
the optimal length of chain-of-thought when the model has access to Lean feedback could be shorter.
It may even make sense to do a heirarchical / recursive DSP, where you start with a high-level formal proof sketch, then replace each sorry with a more refined proof sketch, and so on, and get feedback from the prove each step of the way.

On the coding side, this desire to tighten the feedback loop underlies my [exploration](https://gasstationmanager.github.io/ai/2025/03/28/alphabeta.html) of interleaving coding and the property-based tests for hallucination detection,
and later the [Code-Test-Prove](https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html) workflow where we interleave the three. 


**Sorry -> Formal Goal -> Informal Sketch -> Formal Sketch.**
In the middle of a recursive DSP proof attempt, we will have some subtasks (`sorry`s) 
that could not be immediately resolved by hammers. 
We can get Lean to output the goal state corresponding to the `sorry` (via Pantograph/LeanTool or some other tool). Then try to prove that goal. 
Often the most effective approach is to lift back up to the informal level, produce a (rigorous) informal proof sketch, then translate to a formal Lean sketch.
E.g. Opus 4 used this effectively in its [attempt](https://gasstationmanager.github.io/ai/2025/07/06/leantool-updates.html) of the Alpha-Beta challenge.

**Sorry -> Examples -> Identify Patterns/Generalize.**
(This has not been instantiated / tried, but I think could be pretty useful.)
Again, with a sorry that could not be immediately proved by hammer, we can go back to the non-rigorours informal level:
generate examples (perhaps as part of a property-based testing process);
identify patterns in the examples that could poentially be generalized into a proof.

Potentially related: the autogeneralize tool from this [recent talk](https://www.newton.ac.uk/seminar/46714/).

## Open Problems

What is the optimal reasoning pattern? Just as CoT reasoning emerges when training LLMs in RL, 
perhaps it is worth RL-training an LLM with access to the abovementioned tools for formal feedback, and see what emerges.

What would it look like to have an AlphaZero  that can take advantage of this more complicated terrain of formal and informal reasoning?

