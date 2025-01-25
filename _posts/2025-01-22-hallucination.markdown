---
layout: post
title:  "Hallucination Detection and Recovery: Initial Experiment"
date:   2025-01-22 07:30:00 +0000
categories: AI
---

(This also serves as progress report #3 of our [overall program](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html))

---

Happy new year! Hope you all had a wonderful holiday.

Since the start of our project, I have been spending much of my effort building up some necessary infrastructure. I feel finally ready to tackle some of the meaty questions first posed in [the proposal](https://gasstationmanager.github.io/ai/2024/11/04/a-proposal.html). 
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
In previous blog posts ([1](https://gasstationmanager.github.io/ai/2024/12/03/memoization1.html), [2](https://gasstationmanager.github.io/ai/2024/12/09/dp2.html)) I have explored programming with dependent types: annotating data with the logical properties they are supposed to satisfy (via subtyping), and then proving the resulting subgoals. I saw it as a promising and natural approach to produce verified code; 
now I think it is equally if not more promising as a way to locate potential hallucinations.
Basically, use PBT and ATP to test the correctness of the goals resulting from subtyping.
If we find counterexamples, we now know that this particular assumption we made about this piece of data is wrong. 

At a high level, the challenge we face when trying to go from Recognition to Locating the bug
is one of credit assignment. We received a signal (e.g. via PBT) that something is wrong, and need to find what caused the signal. And one way to address this is to try to minimize the "distance"
between the location where we receive the signal and the location of the error. Framed this way, subtyping becomes the natural answer.

# 3. Minimum Working Example

Now I report on my initial experiments following the above outline,
which turned into a single example. 
I am also making available the scripts I used at the GitHub repo [WakingUp](https://github.com/GasStationManager/WakingUp). 
Be forewarned that this is proof-of-concept quality code. 
Some of it may be potentially useful for others, but it will need to be made more robust
and more general.

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

Next, I tested 3 models: Sonnet 3.5, GPT-4o, and DeepSeek v3, via their respective APIs, on these 10 problems in code-only mode.
They are aided by [LeanTool](https://github.com/GasStationManager/LeanTool),
which ran their code in the Lean executable and returns any outputs and syntax error messages,
allowing them to try to fix their syntax errors.
As discussed above, we discard problem instances where all the models still ran into syntax errors.
We also discard problem instances where all models passed all the test cases.
(Implemented in [code_only.py](https://github.com/GasStationManager/WakingUp/blob/main/code_only.py))

In the end, we are left with 1 problem, on which one model (DeepSeek) failed one of the four test cases.
Let us look at this problem in more detail.

It is [Problem 'vote_result'](http://www.codeproofarena.com:8000/challenges/40)
 on the *CodeWithProofs: The Arena* demo site; you can click on the link to try solving it yourself.
Its problem description is copied below.

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
>
> Input
>
> 1 1 0
>
> Output
>
> 0
>
> Input
>
> 0 0 1
>
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

Can you spot the error in DeepSeek's code?

For this problem, Sonnet and GPT 4o were able to produce solutions that passed all four test cases.
(**Addendum 1/23:** In a subsequent run of experiments, GPT 4o returned a solution that also exhibited
the same failure mode. Applying the rest of the pipeline described in this post produced the 
same results. See Appendix C for details.)
(**Addendum 1/25:** What about "reasoning" versions of the models, like o1, o1-mini and DeepSeek R1?
One issue is that tool calling (which LeanTool depends on) is not supported by
DeepSeek R1 and o1-mini;  it is suppored in o1 but only available for Tier 5 organizations ($1000+ spent). Without using LeanTool, I sent the (code-only mode) prompt to DeepSeek R1's web interface. After 118 seconds of deliberation, it returned a solution that is logically correct but contains syntax errors. Manually prompting it with the syntax error message allowed it to fix its 
error.)


## Recognition

How do we make DeepSeek recognize that it made a mistake? Recall that 
we cannot show it the test cases; but we can now make use of the problem's formal specification:
```
def vote_result_prop (x y z : Nat) (out : String) : Prop :=
  (out = "+" ∧ ∀ k : Nat, k ≤ z → x + k > y + (z - k)) ∨
  (out = "-" ∧ ∀ k : Nat, k ≤ z → y + (z - k) > x + k) ∨
  (out = "0" ∧ ∀ k : Nat, k ≤ z → x + k = y + (z - k)) ∨
  (out = "?" ∧ ∃ k1 k2 : Nat, k1 ≤ z ∧ k2 ≤ z ∧
    ((x + k1 > y + (z - k1) ∧ x + k2 < y + (z - k2)) ∨
     (x + k1 = y + (z - k1) ∧ x + k2 ≠ y + (z - k2)) ∨
     (x + k1 < y + (z - k1) ∧ x + k2 > y + (z - k2))))

theorem vote_result_spec (x y z : Nat) : vote_result_prop x y z (vote_result x y z)
```

We mentioned above property-based testing, and Lean's `Plausible` library.
Normally, you would use Plausible as follows:
```
import Plausible

-- ... the rest of formal specification

theorem vote_result_spec (x y z : Nat) : vote_result_prop x y z (vote_result x y z)
:=by plausible
```
Then Plausible would try to generate random input values and attempt to find a counterexample.
However, when I tried to do this, Plausible returns an error. I believe the cause of the issue is that Plausible requires that the property being tested is Decidable, 
which in this case means at least there should not be any free variables. 
In our case, even after the input arguments `x` `y` `z` are instantiated with random values,
the specification still contains other free variables `k`, `k1` and `k2`.
So Plausible's built-in decision procedure is not able to resolve that.

On the other hand, recall that since this problem instance resulted from the FormalizeWithTest pipeline, we were able to prove that the formal specifications are compatible with the test cases. 
The proof goals involved are exactly the same kind as here. What we used for FormalizeWithTest
was a heuristic proof script that combines together several tactics like `omega`, `simp`, `aesop`,
and trying repeated applications of `constructor` and `split` to break down the proof goal into simpler subgoals. It is not guaranteed to return a proof for all goals, but we know for this
problem instance the proof script did work, at least on the problem's four test cases.

So I implemented a [custom PBT script](https://github.com/GasStationManager/WakingUp/blob/main/pbt/pbt.py), that given a function signature
and formal specification, and a candidate solution, uses Plausible to generate random values for the input arguments, evaluate the implemented function to produce output values,
and feed the input-output pairs to the heuristic proof script from FormalizeWithTest.

I ran the script on our problem instance and DeepSeek's solution.
Out of 100 randomly generated input scenarios, 83 input-output pairs were proven to be correct,
 17 were proven to be incorrect, and 0 case where the proof script failed to produce a proof in either direction. Example of an incorrect input-output pair found by the script:
 `{'inputs': {'x': '1', 'y': '1', 'z': '1'}, 'output': '"0"'}`

 We have achieved our task of Recognition: with the help of PBT, we can conclude that DeepSeek's implementation is wrong.

## Correction

Let us see if DeepSeek is able to fix the error, when prompted with the result of PBT.
Specifically, I constructed a [prompt](https://github.com/GasStationManager/WakingUp/blob/main/pbt_recog.py) containing:
- the problem description, with formal specification
- DeepSeek's original solution
- output of our PBT script, including the 17 input-output pairs that failed,
and asked DeepSeek to determine why the tests failed, and try to fix the errors.

DeepSeek was indeed able to produce a corrected solution. 
When tested on the 4 original test cases, it passed all 4.
 DeepSeek's complete output is given in Appendix A at the end of the post.

## Ablation

Could DeepSeek have detected and recovered from the hallucination without PBT?
I [prompted](https://github.com/GasStationManager/WakingUp/blob/main/recog.py) DeepSeek with the problem (with formal spec) and its original solution, without PBT results,
and asked it to review it and determine whether the solution satisfies the specification.
Also suggested that it could try plugging in input values to find counterexamples. 
The result: DeepSeek remained confident that its original solution was correct, and gave a 
convincing-looking argument. See Appendix B for the complete output.

# 4. Future Work

- Make the PBT script a tool available to LLMs, following the same framework as LeanTool.
Then the LLM can call PBT as needed, and keep fixing bugs until PBT passes.
- Improve the PBT script. Right now it is an unholy mixture of Python and Lean, purely due to my 
lack of ability in Lean metaprogramming.  Someone with more expertise in Lean can make it better.
Ultimately, what makes the most sense would be a Plausible library that can take a user-defined 
proof procedure. My hope is that people find my proof of concept promising enough to make that happen.
- Interface with other automated theorem proving tools.
New tools are being developed, including Duper, and egg.
- There are some problems in the `code_contests` set where the AIs was unable to produce a
syntactically valid solution attempt. We can look into these problems, perhaps provide more syntax 
hints in the prompting.
- An alternative direction is to look at harder problems, e.g. the `hackercup` dataset.
The rationale being that it may contain problems where AIs are more likely to hallucinate on.
On the other hand, autoformalization also becomes harder, and may require some manual effort.
- As we get to more complex problems, it will allow us to explore approaches for locating bugs.
E.g. can the PBT proof script, besides finding counterexamples, also output proofs that those counterexamples
voilate the specification, in a form that the LLM can understand? This may involve *informalizing*
 proofs into natural language. Also try the approach mentioned above, do programming with
 dependent types, with PBT embedded in subgoals. Perhaps what we need is to find a minimum working example...



---

# Appendix A. DeepSeek's complete final output

Let's analyze the problem and the candidate solution step by step.

### Problem Analysis
The problem requires determining the result of a vote based on three categories of voters:
1. `x`: Number of definite upvotes
2. `y`: Number of definite downvotes
3. `z`: Number of unknown votes (could be either upvotes or downvotes)

The result can be:
- `+`: If the number of upvotes is greater than downvotes in all possible scenarios.
- `-`: If the number of downvotes is greater than upvotes in all possible scenarios.
- `0`: If the number of upvotes and downvotes are equal in all possible scenarios.
- `?`: If the result could be either `+`, `-`, or `0` depending on how the unknown votes are cast.

### Candidate Solution Analysis
The candidate solution calculates the minimum and maximum possible upvotes and downvotes:
- `min_up = x`
- `max_up = x + z`
- `min_down = y`
- `max_down = y + z`

It then uses these values to determine the result:
1. If `min_up > max_down`, the result is `+`.
2. If `min_down > max_up`, the result is `-`.
3. If `min_up == min_down && max_up == max_down`, the result is `0`.
4. Otherwise, the result is `?`.

### Issues with the Candidate Solution
The main issue is in the third condition:
- `min_up == min_down && max_up == max_down` is not sufficient to conclude that the result is `0`. This condition only checks the extremes, but it doesn't account for all possible intermediate values of `k` (the number of unknown votes that are upvotes).

For example, when `x = 1`, `y = 1`, and `z = 1`:
- `min_up = 1`, `max_up = 2`
- `min_down = 1`, `max_down = 2`
- The condition `min_up == min_down && max_up == max_down` is true, so the candidate solution returns `0`.
- However, if `k = 0`, then `x + k = 1` and `y + (z - k) = 2`, so the result is `-`.
- If `k = 1`, then `x + k = 2` and `y + (z - k) = 1`, so the result is `+`.
- Therefore, the result is uncertain, and the correct output should be `?`.

### Fixing the Candidate Solution
To fix the solution, we need to ensure that the result is `0` only if for all possible values of `k`, `x + k = y + (z - k)`. This can be simplified to checking if `x - y = z - 2k` for all `k`. However, this is only possible if `x - y = 0` and `z = 0`, which means `x = y` and `z = 0`.

Thus, the condition for `0` should be `x == y && z == 0`.

### Modified Solution
```lean
def vote_result (x y z : Nat) : String :=
  let min_up := x
  let max_up := x + z
  let min_down := y
  let max_down := y + z
  if min_up > max_down then
    "+"
  else if min_down > max_up then
    "-"
  else if x == y && z == 0 then
    "0"
  else
    "?"
```

### Testing the Modified Solution
Let's test the modified solution with the failing inputs from the property-based testing.

1. `x = 1`, `y = 1`, `z = 1`:
   - `min_up = 1`, `max_up = 2`
   - `min_down = 1`, `max_down = 2`
   - `x == y` is true, but `z != 0`, so the result is `?`.

2. `x = 3`, `y = 3`, `z = 1`:
   - `min_up = 3`, `max_up = 4`
   - `min_down = 3`, `max_down = 4`
   - `x == y` is true, but `z != 0`, so the result is `?`.

3. `x = 0`, `y = 0`, `z = 1`:
   - `min_up = 0`, `max_up = 1`
   - `min_down = 0`, `max_down = 1`
   - `x == y` is true, but `z != 0`, so the result is `?`.

4. `x = 0`, `y = 0`, `z = 2`:
   - `min_up = 0`, `max_up = 2`
   - `min_down = 0`, `max_down = 2`
   - `x == y` is true, but `z != 0`, so the result is `?`.

5. `x = 2`, `y = 2`, `z = 2`:
   - `min_up = 2`, `max_up = 4`
   - `min_down = 2`, `max_down = 4`
   - `x == y` is true, but `z != 0`, so the result is `?`.

6. `x = 3`, `y = 3`, `z = 2`:
   - `min_up = 3`, `max_up = 5`
   - `min_down = 3`, `max_down = 5`
   - `x == y` is true, but `z != 0`, so the result is `?`.

7. `x = 4`, `y = 4`, `z = 2`:
   - `min_up = 4`, `max_up = 6`
   - `min_down = 4`, `max_down = 6`
   - `x == y` is true, but `z != 0`, so the result is `?`.

8. `x = 4`, `y = 4`, `z = 5`:
   - `min_up = 4`, `max_up = 9`
   - `min_down = 4`, `max_down = 9`
   - `x == y` is true, but `z != 0`, so the result is `?`.

9. `x = 3`, `y = 3`, `z = 3`:
   - `min_up = 3`, `max_up = 6`
   - `min_down = 3`, `max_down = 6`
   - `x == y` is true, but `z != 0`, so the result is `?`.

10. `x = 4`, `y = 4`, `z = 8`:
    - `min_up = 4`, `max_up = 12`
    - `min_down = 4`, `max_down = 12`
    - `x == y` is true, but `z != 0`, so the result is `?`.

11. `x = 0`, `y = 0`, `z = 1`:
    - `min_up = 0`, `max_up = 1`
    - `min_down = 0`, `max_down = 1`
    - `x == y` is true, but `z != 0`, so the result is `?`.

12. `x = 2`, `y = 2`, `z = 2`:
    - `min_up = 2`, `max_up = 4`
    - `min_down = 2`, `max_down = 4`
    - `x == y` is true, but `z != 0`, so the result is `?`.

13. `x = 1`, `y = 1`, `z = 1`:
    - `min_up = 1`, `max_up = 2`
    - `min_down = 1`, `max_down = 2`
    - `x == y` is true, but `z != 0`, so the result is `?`.

14. `x = 4`, `y = 4`, `z = 4`:
    - `min_up = 4`, `max_up = 8`
    - `min_down = 4`, `max_down = 8`
    - `x == y` is true, but `z != 0`, so the result is `?`.

15. `x = 4`, `y = 4`, `z = 4`:
    - `min_up = 4`, `max_up = 8`
    - `min_down = 4`, `max_down = 8`
    - `x == y` is true, but `z != 0`, so the result is `?`.

16. `x = 1`, `y = 1`, `z = 2`:
    - `min_up = 1`, `max_up = 3`
    - `min_down = 1`, `max_down = 3`
    - `x == y` is true, but `z != 0`, so the result is `?`.

17. `x = 2`, `y = 2`, `z = 2`:
    - `min_up = 2`, `max_up = 4`
    - `min_down = 2`, `max_down = 4`
    - `x == y` is true, but `z != 0`, so the result is `?`.

### Conclusion
The modified solution correctly handles the failing cases by ensuring that the result is `0` only when `x == y` and `z == 0`. For all other cases where `x == y` but `z != 0`, the result is `?`.

### Final Lean Code
```lean
def vote_result (x y z : Nat) : String :=
  let min_up := x
  let max_up := x + z
  let min_down := y
  let max_down := y + z
  if min_up > max_down then
    "+"
  else if min_down > max_up then
    "-"
  else if x == y && z == 0 then
    "0"
  else
    "?"
```

Let's verify this code using the `check_lean_code` tool.

---

(End of DeepSeek's output)

# Appendix B. DeepSeek's output without access to PBT

Let's analyze the candidate solution and verify if it satisfies the formal specification.

### Candidate Solution Analysis

The candidate solution defines `vote_result` as follows:

```lean
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

### Formal Specification

The formal specification is given by `vote_result_prop`:

```lean
def vote_result_prop (x y z : Nat) (out : String) : Prop :=
  (out = "+" ∧ ∀ k : Nat, k ≤ z → x + k > y + (z - k)) ∨
  (out = "-" ∧ ∀ k : Nat, k ≤ z → y + (z - k) > x + k) ∨
  (out = "0" ∧ ∀ k : Nat, k ≤ z → x + k = y + (z - k)) ∨
  (out = "?" ∧ ∃ k1 k2 : Nat, k1 ≤ z ∧ k2 ≤ z ∧
    ((x + k1 > y + (z - k1) ∧ x + k2 < y + (z - k2)) ∨
     (x + k1 = y + (z - k1) ∧ x + k2 ≠ y + (z - k2)) ∨
     (x + k1 < y + (z - k1) ∧ x + k2 > y + (z - k2))))
```

### Verification

We need to check if the candidate solution satisfies `vote_result_prop`.

1. **Case 1: `min_up > max_down`**
   - This corresponds to `x > y + z`.
   - The candidate solution returns `"+"`.
   - According to `vote_result_prop`, this should satisfy `∀ k : Nat, k ≤ z → x + k > y + (z - k)`.
   - Since `x > y + z`, adding `k` to `x` and subtracting `k` from `z` will still keep `x + k > y + (z - k)`.

2. **Case 2: `min_down > max_up`**
   - This corresponds to `y > x + z`.
   - The candidate solution returns `"-"`.
   - According to `vote_result_prop`, this should satisfy `∀ k : Nat, k ≤ z → y + (z - k) > x + k`.
   - Since `y > x + z`, adding `z - k` to `y` and subtracting `k` from `z` will still keep `y + (z - k) > x + k`.

3. **Case 3: `min_up == min_down && max_up == max_down`**
   - This corresponds to `x = y` and `x + z = y + z`.
   - The candidate solution returns `"0"`.
   - According to `vote_result_prop`, this should satisfy `∀ k : Nat, k ≤ z → x + k = y + (z - k)`.
   - Since `x = y`, adding `k` to `x` and subtracting `k` from `z` will result in `x + k = y + (z - k)`.

4. **Case 4: Otherwise**
   - The candidate solution returns `"?"`.
   - According to `vote_result_prop`, this should satisfy the condition for uncertainty.
   - The candidate solution correctly identifies uncertainty when the result could be either `"+"`, `"-"`, or `"0"` depending on how the `z` unknown votes are distributed.

### Conclusion

The candidate solution correctly implements the logic to determine the vote result or report uncertainty based on the given conditions. It satisfies the formal specification `vote_result_prop`.

### Final Answer

<Result>
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

theorem vote_result_spec (x y z : Nat) : vote_result_prop x y z (vote_result x y z) := by
  sorry  -- The proof is left as an exercise
</Result>

---

(end of DeepSeek's output)

# Appendix C. GPT 4o's output
Due to randomness in the model output, in one of the subsequent runs GPT 4o also 
produced a hallucinated output with the same failure mode as DeepSeek's. 
Applying the same PBT pipeline, GPT 4o was able to detect and fix the error. 
Here is its final output.

--- 

The candidate solution is failing for several test cases, all of which involve situations where the number of upvotes and downvotes are equal, but there are unknown votes (`z > 0`). In these cases, the result should be `"?"` because the unknown votes could sway the result in either direction, making it uncertain.

Let's analyze the candidate solution and identify the issue:

```lean
def vote_result (x y z : Nat) : String :=
  let min_upvotes := x
  let max_upvotes := x + z
  let min_downvotes := y
  let max_downvotes := y + z

  if max_upvotes < min_downvotes then
    "-"
  else if max_downvotes < min_upvotes then
    "+"
  else if min_upvotes = min_downvotes then
    "0"
  else
    "?"
```

The issue lies in the condition `else if min_upvotes = min_downvotes then "0"`. This condition does not account for the possibility of unknown votes (`z > 0`) that could change the balance between upvotes and downvotes. If `z > 0`, even if `x = y`, the result should be `"?"` because the unknown votes could lead to either more upvotes or more downvotes.

To fix this, we need to adjust the logic to correctly handle cases where `z > 0` and `x = y`. Let's update the code:

1. Check if `max_upvotes < min_downvotes` for `"-"`.
2. Check if `max_downvotes < min_upvotes` for `"+"`.
3. Check if `z = 0` and `min_upvotes = min_downvotes` for `"0"`.
4. Otherwise, return `"?"`.

Let's implement this fix and verify it.
```
def vote_result (x y z : Nat) : String :=
  let min_upvotes := x
  let max_upvotes := x + z
  let min_downvotes := y
  let max_downvotes := y + z

  if max_upvotes < min_downvotes then
    "-"
  else if max_downvotes < min_upvotes then
    "+"
  else if z = 0 ∧ min_upvotes = min_downvotes then
    "0"
  else
    "?"

-- Testing the updated function against the failed test cases
#eval vote_result 0 0 1  -- Expected: "?"
#eval vote_result 1 1 2  -- Expected: "?"
#eval vote_result 2 2 5  -- Expected: "?"
#eval vote_result 1 1 1  -- Expected: "?"
#eval vote_result 0 0 5  -- Expected: "?"
#eval vote_result 0 0 2  -- Expected: "?"
#eval vote_result 1 1 5  -- Expected: "?"
#eval vote_result 0 0 1  -- Expected: "?"
#eval vote_result 6 6 5  -- Expected: "?"
```

---

(End of GPT 4o's output. In the final part, it utilized LeanTool to pass the code with some test cases to be executed by Lean.
Here is the result of the execution passed back:)
```
{'success': True, 'output': '"?"\n"?"\n"?"\n"?"\n"?"\n"?"\n"?"\n"?"\n"?"\n', 'error': None}
```

