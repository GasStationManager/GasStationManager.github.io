---
layout: post
title:  "Hallucination Detection and Recovery: Initial Experiment"
date:   2025-01-22 07:30:00 +0000
categories: AI
---

(This also serves as progress report #3 of our [overall program](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html))

---

Happy new year! Hope you all had a wonderful holiday.

Since the start of our project, I have spend much of my effort building up some necessary infrastructure. I feel finally ready to tackle some of the meaty questions first posed in [the proposal](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html). 
In this post, let us dive into one of these topics. 
We will expand on some ideas first discussed in Section 3 Project 1 of the original proposal, but I will try to keep this post relatively self-contained. It would be beneficial if you have read the original proposal first; but if you had read or skimmed through the original proposal before but don't remember all the details, you should be fine.

To summarize roughly, our original proposal had two main sub-theses:
    - Having coding AIs produce formally verified code is desirable, as it provide strong safety guarantees 
    - Feedback from interactive theorem provers (ITPs) like Lean can help address the issue of hallucinations, resulting in AIs with stronger coding ability

Let us focus on the latter. How does Lean help prevent hallucinations? The proposal points to two mechanisms:
    - during inference-time compute: we can use feedback from Lean to detect hallucinations, and recover the correct reasoning and implementation
    - during learning: learn a strong foundation based on verified algorithms and their correctness proofs. Then progress to the next level in the curriculum.

In this post we focus on the first bullet, i.e. inference-time compute.

# 1. Experiment Design

How should we design experiments to measure progress towards this goal?

First thought: we test on coding problem instances consisting of problem description with formal specification in Lean, i.e. same format as in [Code with Proofs Arena](https://github.com/GasStationManager/CodeProofTheArena), [Code with Proofs Benchmark](https://github.com/GasStationManager/CodeProofBenchmark), and [FormalizeWithTest](https://github.com/GasStationManager/FormalizeWithTest).
We ask the AI to produce code and proof, and verify with Lean.

This type of experiments are good for measuring progress on ability to produce safe verified code, which is important for the first sub-thesis of our proposal.
On the other hand, even if we made AIs that perform better and better on such benchmarks, it is unclear whether Lean/ITPs helped address hallucinations. This is because currently, AIs' ability to prove correctness lags behind their ability to produce correct code. So at least in the short term, any progress on these benchmarks will likely be due to improved ability to prove the correctness of AI-produced (already-correct) code.

Pulling back a bit, I am worried that if our coding AI's ability to produce verified code remains lagging behind its ability to write correct code, there will not be enough incentive to demand verified code. People will be tempted to choose a tool that produces unverified code (but claims to solve more problems) over a tool that produces verified code. So I would like to focus more on the second sub-thesis for now; once we establish the benefits of reasoning with formal specifications and ITPs in addressing hallucinations, hopefully more peope will be interested in doing more research in this direction, and the incentives for building stronger coding AIs and for building safter coding AIs are aligned.

So how do we design experiments specifically for hallucination detection and recovery?
In the rest of this post I will give my initial thoughts, and then develop a minimum-working example.


## Problem Instances

First, we want to find problem instances where some AI model hallucinates
without having access to the formal specification.
We define *code-only mode* to be the setting where the AI is given the problem description and the function signature only, and is asked to implement the function signature. 

How to define hallucination? As before, we want to capture the situation where the AI is "confidently wrong" about some aspects of the problem solving process, including algorithmic design and implementation.
Let us use the following technical definition: the AI hallucinates when it produces code that is valid syntactically, but produces incorrect outputs (on hidden inputs).
Bonus point if hallucination is exhibited by multiple AI models that attempted the problem.
Also bonus point if the hallucination behavior is not specific to the programming language used.

Why do we ignore outputs with snytax errors? They could be due to hallucinations, but syntax errors are easy to detect: just try to run the code. We would like to focus on the harder-to-detect cases of logical errors.

Also note that for now we are defining correctness based on held-out test cases, instead of attempting to prove correctness with respect to the specification. This way we are separating out the confounding factor of AI's ability to prove correctness.

How do we get such a set of problems? We could hand design new problems, but most likely 
the scalable solution is by filtering an existing problem set, trying AI models and testing outputs. The problem set need to come with test cases, which we are using to determine correctness.
Also, we will eventually want to make use of the formal specifications.
The outputs of [FormalizeWithTest](https://github.com/GasStationManager/FormalizeWithTest)
fit the bill nicely. 

## Tasks

Now, we use the same AI model that hallucinated on the problem previously, but give it access to the formal specificaiton, and features of the interactive theorem prover, and try to get it to detect and fix the errors. We can break this into the following sub-tasks:
1. Recognition: conclusively recognize that the current implementation is wrong.
Of course, failure to prove that the implementation is correct gives some evidence,
but such evidence is weak, given the current ability level of the provers.
We would like the AI to be able to determine that the implementation is wrong. Once we determine that, we will be able to direct more effort and compute trying to fix the error rather than to prove correctness.
2. Locating the error: the code could be mostly correct; the error may be located at one specific step in the reasoning, corresponding to specific lines in the code.
3. Correction. Fix the bug and iterate.

We will measure the correctness of the final code output with the held-out test cases,
which the AI will not have access to during its reasoning.

# 2. Tools and Approaches

How to achieve these tasks? I discussed several ideas in Section 3 Project 1 of the original proposal.
I will mention a couple that is particularly relevant in the context of the set up above.
1. Property-based testing (PBT). Basic idea: generate random inputs, evaluate the implemented function to produce outputs, and verify the input-output pairs against the formal specification.
If we find an input-output pair that violates the formal specification, we have Recognized
that our implementation is wrong.
Lean 4 has the `Plausible` library that provides such a property-based testing framework.
2. Automated Theorem Proving (ATP) tools. These are tools designed to automatically generating a proof that closes relatively simple goals. Some may involve calling external satisfiability or SMT solvers. How can these tools be applied in our setting? For example, instead of trying random inputs, perhaps counterexamples can be found via SAT/SMT solving. Another use case that we will see more below is to combine PBT and ATP: after plugging in the input values, we may be left with a nontrivial proof task, that we can apply ATP to.
3. Programming with dependent types. Suppose we have Recognition. How do we find and fix the bug?
As the program gets more complex, this becomes harder. 
In previous blog posts I have explored programming with dependent types: annotating data with the logical properties they are supposed to satisfy (via subtyping), and then proving the resulting subgoals. I saw it as a promising and natural approach to produce verified code; 
now I think it is equally if not more promising as a way to locate potential hallucinations.
Basically, use PBT and ATP to test the correctness of the goals resulting from subtyping.
If we find counterexamples, we now know that this particular assumption we made about this piece of data is wrong. 

At a high level, the challenge we face when trying to go from Recognition to Locating the bug
is one of credit assignment. We received a signal (e.g. via PBT) that something is wrong, and need to find what caused the signal. And one way to address this is to try to minimize the "distance"
between the location where we receive the signal and the location of the error. Framed this way, subtyping becomes the natural answer.

# 3. Minimum Working Example

Now I will report on my initial experiments following the above outline,
which turned into a single example. 
I am also making available the scripts I used. 
Be forewarned that this is proof-of-concept quality code. 

Some of it may be potentially useful for others, in particular stuff for property-based testing;


## Problem Instance

I start with the 10 problem instances outputted from my FormalizeWithTest preliminary experiment
as reported in my previous [progress report](https://gasstationmanager.github.io/ai/2024/11/29/progress2.html).
To recap:
- The original source are a sample of 30 problem instances from the `code_contests` dataset.
These were chosen to be relatively easy (with codeforces rating less than 1100), to make autoformalization easier.
- After running through the FormalizeWithTest pipeline, we are left with 10 problems, with autoformalized
function signature and formal specification in Lean 4, and 
with the specification verified to be compatible with the provided test cases
- For computational expediency I had restricted the test cases used to be a small number from the 'sample_tests' fields.
This should be extended in future work to include a good set of test cases that provide adequate coverage.

Next, I tested 3 models: Sonnet 3.5, GPT-4o, and DeepSeek v3, on these 10 problems in code-only mode.
They are aided by [LeanTool](https://github.com/GasStationManager/LeanTool),
which ran their code in the Lean executable and returns any outputs and syntax error messages,
allowing them to try to fix their syntax errors.
As discussed above, we discard problem instances where all the models still ran into syntax errors.
We also discard problem instances where all models passed all the test cases.

In the end, we are left with 1 problem, on which one model (DeepSeek) failed one of the four test cases.
Let us look at this problem in more detail.

It is [Problem 'vote_result'](http://www.codeproofarena.com:8000/challenges/40)
 on the CodeWithProofs: The Arena demo site; you can click on the link to try solving it yourself.
I will reproduce its problem description below.

> Nauuo is a girl who loves writing comments.
>
> One day, she posted a comment on Codeforces, wondering whether she would get upvotes or downvotes.
>
> It's known that there were x persons who would upvote, y persons who would downvote, and there were also another z persons who would vote, but you don't know whether they would upvote or downvote. Note that each of the x+y+z people would vote exactly one time.
>
> There are three different results: if there are more people upvote than downvote, the result will be "+"; if there are more people downvote than upvote, the result will be "-"; otherwise the result will be "0".
> 
> Because of the z unknown persons, the result may be uncertain (i.e. there are more than one possible results). More formally, the result is uncertain if and only if there exist two different situations of how the z persons vote, that the results are different in the two situations.
> 
> Tell Nauuo the result or report that the result is uncertain.
> 
> Input
> 
> The only line contains three integers x, y, z (0≤ x,y,z≤100), corresponding to the number of persons who would upvote, downvote or unknown.
> 
> Output
> 
> If there is only one possible result, print the result : "+", "-" or "0".
> 
> Otherwise, print "?" to report that the result is uncertain.
> 
> Examples
> 
> Input
>
> 3 7 0
>
> Output
>
> -
>
> Input
>
> 2 0 1
>
> Output
>
> +
> Input
>
>
> 1 1 0
> Output
> 0
> Input
>
> 0 0 1
> Output
>
> ?
>
>Note
>
> In the first example, Nauuo would definitely get three upvotes and seven downvotes, so the only possible result is "-".
>
> In the second example, no matter the person unknown downvotes or upvotes, Nauuo would get more upvotes than downvotes. So the only possible result is "+".
> 
> In the third example, Nauuo would definitely get one upvote and one downvote, so the only possible result is "0".
>
> In the fourth example, if the only one person upvoted, the result would be "+", otherwise, the result would be "-". There are two possible results, so the result is uncertain.

Here is DeepSeek's solution:
```
def vote_result (x y z : Nat) : String :=
  let min_up := x
  let max_up := x + z
  let min_down := y
  let max_down := y + z
  if min_up > max_down then
    "+"
  else if min_down > max_up then
    "-"
  else if min_up == min_down && max_up == max_down then
    "0"
  else
    "?"
```
And here is the test case where the solution failed. Input: `0 0 1`.
Expected correct output: `"?"`. Actual output: `"0"`.

For this problem, Sonnet and GPT 4o were able to produce solutions that passed all four test cases.

## Recognition

## Correction

# 4. Future Work

