---
layout: post
title:  "A Proposal for Safe and Hallucination-free Coding AI"
date:   2024-11-04 07:30:00 +0000
categories: AI
---

**Update 11/10:** Added GitHub Repo [FormalizeWithTest](https://github.com/GasStationManager/FormalizeWithTest) for Project 3.

**Quick Links to GitHub Repos:** [Arena](https://github.com/GasStationManager/CodeProofTheArena) / [Benchmark](https://github.com/GasStationManager/CodeProofBenchmark) / [Formalize](https://github.com/GasStationManager/FormalizeWithTest)

---

# Preface

In this essay, I propose a research agenda that I believe will eventually lead to coding AIs that have superhuman-level ability, are hallucination-free, and safe. To achieve our goal will require a lot of further innovation, experimentation, and hard work. But I fully believe this is the most promising direction.

I am writing this mainly to the open source community. Why? The insights and ideas in my essay might be new to some, and might not to others. In fact, publicly-available information has led me to believe that at least some of the commercial labs are actively working on similar ideas/directions.  One message that I hope to convince you in this essay is that, whoever ends up achieving this, it will be a Big Deal. And right now, most likely it will be the frontier labs, because they have the most resources, including compute. And when they do, it is unlikely that they will open source it. The open source community will be playing catch up then, and it will be hard to catch up this time, because such a superhuman-level coding AI will be able to recursively self-improve in an accelerating manner. I realized that, even though it is tempting to continue working on this by myself, I, an independent researcher with limited time and compute, will simply not be fast enough.

By publishing this essay, and [open-sourcing what I have done so far](https://github.com/GasStationManager), I am calling on the open source community to start thinking about these ideas, if you haven't already. If you are already working in this direction, it may be beneficial to coordinate resources. Even then, we will be playing catch up. But hopefully it will be a more level playing field.

Why do I want to help the open source community? I do subscribe to the stance that a single company (no matter which one) having all the power in the world is perhaps undesirable. 
Furthermore, as the title suggests, what I'm proposing below has an important AI Safety component. Indeed, if we are going to be able to produce coding AIs with superhuman ability, AI Safety has to be taken seriously. And for that to work requires buy-in from everyone. I want the open source community to have a seat at the table for that discussion. 

# 1. The Question 

Consider the task of code generation. I will assume the readers already appreciate the importance
of code generation, and will not further belabor the point. 

The following is a common workflow. 
Some version of this is already happening with current AI coding assistants,
from plain chat interfaces like ChatGPT and Claude Sonnet to integrated tools like Github Copilot, Aider, and Cursor.
1. We provide a description of the task. 
2. The AI returns code and explanation. 
3. Rounds of feedback/questions/revisions/sandbox testing as needed, 
4. we decide whether to depoly the code.
 
Imagine that we are in a future where the AIs keep getting stronger at coding,
able to solve more and more complex tasks.
One day, our AI assistant presents a solution to our task. Claims to satisfy exactly our specifications. Provides a high level description of the solution that seems plausible. Passed all tests in sandbox. Only problem: the code is 100,000 lines long and we are not able to check it line by line.

Current AIs might be not strong enough yet; but as we improve them (which is our goal), we will eventually hit this point.[^1]


### Question: Do we run this code in the real world?

*What's the worry? Didn’t it pass all the tests?*

(The answer won't be a surprise to many of you, but let's spell this out so we are on the same page.)
We could be facing an superintellgent, deceptive AI, that has secretly planted a piece of code in its submission that fulfills its own purpose when executed. A virus. A backdoor.
This is a scenario often imagined in science fiction ("Skynet"), but is becoming less and less fictional. 



One answer to the Question (this was roughly my position until a few months ago). *If we don't understand the code, we don't run it. We, the elite programmers, have to take on the responsibility of the last line of defense. Even if that limits the amount of automation benefits the AIs can provide. Safety is more important.*

This may be a reasonable position to take, but: what if I thought I understood every detail of the code, but I make a mistake?

*Can I use another AI to help me make this decision?* For that to work, I'll need an AI that (a) I completely trust, and also (b) is strong enough to not make any mistakes.

(We could also seek help from other branches of alignment research. E.g.,
mechanistic interpretability: we can open up the AI's brain, probe the neurons etc to understand what it's doing. Totally worthwhile research direction, but at its current state, not powerful enough to provide a satisfying answer the question.)


### The Question, but in Current Year

Let us imagine the same scenario, but in the current year. Put in whichever current model you think is strongest at producing code, be it o1 or Sonnet.
Do we trust the produced code enough to run it without being able to check it line by line?

The worry here is more mundane but still extremely important. How do we know that the AI hasn't made a mistake? That it hasn't hallucinated at some point?

*But didn't it pass the tests?* My response is: who do you think wrote the test cases?

Indeed, the issue of halluciation appears to be the main obstacle currently preventing AIs to 
solve larger-scale coding tasks. These more complex tasks typically require solving a sequence of subtasks; and hallucination in an earlier task will quickly lead the AI astray; the mistakes compound and it is hard to recover.

This is of course an active area of research. The most promising current approaches focus on scaling up 
inference-time compute (a.k.a. "System 2", reasoning), either via some external scaffolding or by training the behavior
into the model via reinforcement learning. 
The intuition is that by spending more tokens to think, the AI can produe a better quality output.
The extra tokens are used to reason step by step (chain-of-thought), to check over the output for mistakes (reflection), and/or to systematically examine candidate options (search, tree-of-thought).
So even if the base model could occasionally produce hallucinated output, 
it could be caught and corrected at inference time.

I believe although inference-time compute is a powerful paradigm, it is necessary but not sufficient by itself: it cannot guarantee being able to recover from hallucinations, because of its lack of access to the ground truth. Indeed,  the current state of the art, OpenAI's o1, is very impressive at utilizing inference time compute to solve complex tasks, but it still hallucinates.

# 2. The Protocol

Let us first focus on the first version of the Question, the one from the future. 
We will come back to the second version a bit later.

Here is an attempt to answer the Question: *Let us ask the AI to prove a theorem about the correctness of its code.* 
But the proof could be also very long and hard to understand.

*Revised attempt: I know! I've just read about [AlphaProof](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/), which was able to produce 
rigorous, machine-checkable proofs of mathematical statements in the language Lean; solving highly-nontrivial International Math Olympiad problems at a silver-medal level. So, let's ask the AI to provide a machine-checkable proof of correctness of its code, written in a formal language like Lean. If the proof passed the proof checker, we know it is correct.*

But how do we trust that the theorem proved matches what the code is doing?
E.g., suppose we asked the AI to write a Python program that computes shortest path in a graph,
and the AI returns a Python implementation of [Dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra's_algorithm), with a proof in
Lean that Dijkstra's Algorithm correctly computes the shortest path. How do we know that the AI's Python code is a faithful implementation of Dijkstra's algorithm, without checking it line by line?


A key observation: some of these proof systems (Lean, Coq, Isabell, Idris etc) are also general-purpose (functional) programming languages.

So: ask AI to write the function in (say) Lean, and also write the proof of correctness of the submitted function in Lean. 
Specifically, we provide:
1. a function signature to be implemented, and
2. the formal specification of what the function should satisfy, as a theorem statement
that references the function by name.

And ask the AI to implement the function and provide a proof of the theorem, in Lean.
If the proof passes the proof checker, we know the function satisfies the theorem statement. 
We humans do not have to understand the code or the proof. We just have to understand the theorem statement, which is the software specification formalized in Lean.

In the rest of this essay I will focus on Lean, because of my relative familiarity with it.
(And I chose to study it first because the the current state of the art in AI theorem proving
has focused on Lean.)
My points stand if you replace Lean with a similar programming language/proof assistant, e.g.
Coq, Issabelle, Idris, Agda etc.
I will not attempt to give a comprehensive tutorial on Lean here; 
for a full introduction see [Functional Programming in Lean.](https://lean-lang.org/functional_programming_in_lean/)
If you are familiar with functional programming the examples in this essay will be easy to follow.

Let us look at the simplest example. We ask for a function solveAdd that takes two integers a and b, and returns an integer x such that a + x = b. The function signature in Lean is:

{% highlight lean %}
def solveAdd(a b: Int): Int
{% endhighlight %}

And the specification as theorem statement is:
{% highlight lean %}
theorem solveAdd_spec(a b: Int): a + (solveAdd a b) = b
{% endhighlight %}
These are valid Lean code except that the body of the function and the body of the theorem (the proof) are missing. 
Given these to the AI, we would expect the solution back in the form of the completions of both the function and the theorem:
{% highlight lean %}
def solveAdd(a b: Int): Int := b-a

theorem solveAdd_spec(a b: Int): a + (solveAdd a b) = b := by simp[solveAdd]; omega
{% endhighlight %}
Lean is an interactive theorem prover. To understand what is going on in a Lean proof, it is often 
helpful to look at it in an Lean environment; 
e.g. you can paste this code to the official Lean web playground at https://live.lean-lang.org/,
or install the Lean extension of VS Code. As you step through the proof steps with the cursor,
Lean displays the current *proof state*, which shows what has been proven (or assumed), and what tasks remain.

The proof is straightforward as expected. At the beginning of the proof, the goal, i.e. statement to be proved, is `a + (solveAdd a b) = b`. The tactic `simp[solveAdd]` rewrites the goal by plugging in the definition of `solveAdd`. So the goal becomes `a+(b-a)=b`. The tactic `omega` proves the remaining goal by applying rules of arithmetic for integers. 
This is a toy example, but we can already see that the theorem is proving a property of the actual function `solveAdd`. If we had made a mistake in implementing `solveAdd`, e.g. by writing `a-b` instead of `b-a`, the proof would have failed to pass the proof checker, and indeed the theorem statement would be false.

What about more complex tasks? Suppose we are given a list of integers and an integer x, and we want to check whether x is in the list. 
A function signature for this task would be 
`def isIn (x:Int) (xs: List Int): Bool`,
and a reasonable specification would be that we want `isIn x xs` to be true if and only if x is a member of xs.
Here is an implementation in Lean.
{% highlight lean %}
def isIn (x:Int) (xs: List Int): Bool
  := match xs with
  |[] => false
  |h::t => x==h || isIn x t
{% endhighlight %}
This solution using recursion is very similar to what you would do in other functional programming languages like Haskell.
The pattern matching works because the type `List Int` is defined inductively as either the empty list `[]` or
the cons (`::`) of a head (an `Int`) and a tail (a `List Int`).
How do we prove the correctness of such a recursive function?
{% highlight lean %}
theorem isIn_correct (x:Int) (xs:List Int):
  isIn x xs = true ↔ x ∈ xs := by{
    induction xs with
    |nil=> simp[isIn]
    |cons h t ih=> simp[isIn,ih]
  }
{% endhighlight %}
The `induction` tactic initiates a proof by induction. It follows the structure of the List `xs` to break into 
the base case (when `xs` is empty) and the inductive case (when `xs` is the cons of `h` and `t`). 
For the inductive case it also helpfully constructs the induction hypothesis in `ih` for us to use.
In the Lean environment you will see `ih` among the list of assumptions,
assigned to the proposition `isIn x t = true ↔ x ∈ t`, i.e. the theorem statement applied to `t`.
All that is left for us to do is to plug in the `isIn` definition (which in the case of nonempty list, narrows down to the expression `x==h || isIn x t`),
and the induction hypothesis `ih`. 
The `simp` tactic also tries to simpify the goal by applying built-in theorems, and in this case 
that is sufficient to prove our goal.
We see that this kind of induction proofs are naturally suited to prove correctness of recursive functions.


This possibility of providing code with machine-checkable correctness proof is not new. 
This is what the field of formal verification studies, which developed languages like Coq and Lean,
 designed to do exactly this.
If machine-verifiable code is so good, why don’t we see it more often?
While machine-verifiable code is nice, it might be too much to ask human programmers to provide it, except in certain safety critical scenarios, because the proofs required would be extremely tedious.  

But, it is not too much to require this from the AIs.


### Objections

Q. *what if the AI still tries to include some secret code in the submission, which does not change the return value but does some side effects?*

A. In a functional programming language like Lean, pure functions do not have side effects. Side effects has to be done via monads, and that will be indicated on the function signature. So if you do not want side effects it is easy to enforce that.



Q. *Isn't the restriction to these particular functional languages limiting?*

A. You can have procedural style programming inside a functional language like Lean,
with the use of monads...

Q. *No seriously. What if I have a task that requires direct mutation of computer hardware resources? What about all the Python libraries that I can't live without?*

A. This is a starting point. Once we get this working, we can try to extend to procedural languages.
Proving correctness of code written in procedural languages is 
a very common topic in formal verification. 
To prove some property about some piece of code in Python or C, 
in a proof system like Lean, the first step
is to build a mathematical model of the language's intepreter (or compiler).
This allows us to translate the Python/C code into a mathematical statement of what the code does.
There has been quite a bit of research from formal verification on proving correctness of procedural 
style code, 
 e.g. Hoare logic, and separation logic.

Another direction is to compile Lean into other languages. Right now the Lean compiler compiles
into C.


Q. *What about guarantees of the program's run time, or other resource usage?*

A. Right now, Lean can only reason about the function's return value.
 We will need additional instrumentation to measure resource usage.  At a high level, 
 within Lean this is doable with the use of monads and possibly metaprogramming.
 If we are reasoning across languages as in the previous answer, 
 instrumentation can be introduced during translation. 
 I will expand on this in a future post.


Q. *What if I am still uncomfortable with executing code I don’t understand? It is not that I have personally read and understood every line of code I have executed, but in this case I would like to be more careful because (a) the code is going to be executed in a more critical domain, and/or (b) the code is written by an AI.*

A. You can still maintain the policy that only human-understood code is to be executed, for the set of domains you define. Still, the proofs give you an additional layer of verification and protection.



# 3. A Way Forward

Suppose you agree that this is a worthy goal. What then?

One answer: *With this safety guardrail in place, it allows us to aim for stronger and stronger coding AIs, and to trust the AI's output as long as the required proof is provided.
So we do nothing really different for now. People are already trying to make stronger code generating AIs, whether by scaling up the current architectures or via some different method. People are already making AIs that can formally prove theorems in Lean (e.g. AlphaProof). Perhaps we can make more investments towards this to make stronger and stronger theorem provers geared towards proving properties of code. Once we reach the point in future when we are faced with the Question, we  "LangChain together" the code generation AI and the theorem proving AI, to produce the code and its proof. We reject the code unless it passes the proof checker.*  

But more concretely how do we get there? 
Let us revisit the second version of the Question, from the current year. I.e. do I trust a large piece of code produced by a current AI?  Recall that the issue is that the current models suffer from hallucinations, and are generally not reliably correct. These mistakes compound as the task become more complex. 

I would argue that the protocol we proposed in Section 2 is also very relevant in addressing the issue of hallucination.
First of all, what is hallucination? Different kinds of AI halluciation have been
identified and studied; some are regarding factual knowledge, here we are mainly
concerned with ability to reason correctly. 
Here's a working definition of hallucination for the code generation domain:
1. The AI is making mistakes as if it has the wrong world model (about how code works, and/or how the relevant logic and math works); and
2. The AI is confident about the answer even though it is wrong.

Now consider an AI that is able to produce code and a machine-checked proof of its correctness. Then the AI is behaving as if it has a good world model of what its code does.
On the other hand, if the AI produced code but is not able to produce correct reasoning of why their code works, then it is likely that AI doesn't "understand" what the code is doing. 

**An AI that is able to produce code and proof solves both versions of the Question.**
It does not hallucinate. It also provides the safety guarantee we need to trust the code.

This next part is a bit speculative but I would argue is very plausible: getting rid of hallucinations will enable the AIs to solve more and more complex tasks by building
on verified components. This will allow the AIs to reach superhuman ability in coding.
(Here by "superhuman" I don't mean the AI necessarily becomes a general superintelligence,
but in the narrower sense of ability to complete the specific task of code generation given
human-provided specifications, as measured by accuracy and speed.)

I still haven't said anything about how to achieve it. But this is at least a more 
concrete goal than just "avoid hallucination".

So how to achieve this? So far what I'm proposing is totally agnostic regarding 
architecture. Any approach could potentially succeed, from the purely symbolic to the purely connectionist. And I encourage the community to try a diverse set of ideas.
If you are already working on a coding AI, why not add this as a benchmark target.

For me personally, I believe a good direction will likely involve a combination of
search and learning. Not really a radical take. But allow me to elaborate. 
1. Search. Coding and proving are tasks that natually benefit from more inference-time compute.
Earlier I said that the current inference-time compute approaches are insufficient, because of a lack of access to ground truth.
Feedback from the interactive proof system provide strong ground truth signals to guide the search.

2. Learning.  If hallucination is due to the lack of a good world model of how code works, then 
feedback from the proof system can be a strong grounding signal to help the AI learn such a good world model.

3. Combining Search and Learning. This access to the ground truth allows us to be confident that search produces improved results than the base model's output.
We train our model to imitate the output of the search; then use the improved model to 
guide the search toward better solutions. Repeat the feedback loop.
This is basically the [AlphaZero](https://storage.googleapis.com/deepmind-media/DeepMind.com/Blog/alphazero-shedding-new-light-on-chess-shogi-and-go/alphazero_preprint.pdf) algorithm.

The AlphaZero algorithm, from its earlier success in games like Go, chess, shogi,  and starcraft,
to powering [AlphaProof's recent breakthrough in mathematical problem solving](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/), 
has shown us a reliable recipe to get to superhuman performance in reasoning-heavy domains. 
A key ingredient in these other successes was that the domain has a source of ground truth.
I believe that by formulating the code generation task as a code-and-proof problem,
and with (e.g.) the Lean proof checker system as source of ground truth, 
We will be able to adapt the AlphaZero training loop to achieve superhuman performance in coding.

### On Competing Against Scale

Q: *Even if you are right about the technical direction, logistically this is a daunting task!
The amount of data you'd have to construct. The amount of compute needed for training.[^2] 
All the technical challenges that you have glossed over. If as you guessed the frontier labs are already attempting this, how do we have any hope of catching up?*

A: I admit that the frontier labs are well-suited to tackle a project of this scale.
They have the capital to spend to acquire or construct data sets as needed.
They have the compute, so that their teams can quickly experiment and iterate on ideas.
On the other hand, I believe that an open source collaborative effort can also be
successful, by leveraging the advantages of open source. 
Specifically, I propose below a community effort to construct and curate an open source data set,
aiming to be exclusivly used to train open-source models.
Also, I believe we have an advantange in the sheer number of brilliant minds and the diversity of expertise. By trying diverse approaches in parallel, and sharing results, we can make quick progress
even though individually we have less resources available to us.

To that end, I suggest below a few relatively self-contained sub-projects that 
people can choose to contribute to according to their interest and expertise. 
I am also open sourcing my preliminary efforts on GitHub. 
I fully acknowledge the primitive states they are in; they are meant to serve as starting points,
and I wholly encourage someone with more expertise to fork the repositories and take over.

### Project 1. Search / Scaling Inference-Time Compute

It would be interesting to see how much milage we can get out of scaling inference-time compute,
using current models.[^3]

A baseline would be the simple composition of a code generating model and a theorem prover model
mentioned at the beginning of this section. If the prover fails to generate a proof that passes the checker,
the system outputs "I am not sure about the correctness of my code."
This system is at least not confidently wrong.

We can get a stronger baseline by utilizing the simple inference-time scaling technique Best-of-N: sample N solutions from the coder model
and pass them to the prover. If the prover is able to successfully prove the correctness of one of the 
solutions, we succeed.

But we can certainly hope to do better.
I point out below a few directions.


**1. Utilizing feedback from the Lean proof checker.**
When the prover model fails the proof checker, we have two possibilities.
One is that the code is correct but the prover was not strong enough at producing a proof.
The other possibility is that the code contains a mistake. 
We really want to be able to identify the latter; this is how we detect hallucinations and recover.
Of course, the stronger the prover
is, the better we are able to do that. For now, suppose the prover is fixed;
how do we make use of the feedback from the proof checker?

Here is a first attempt. Run the prover with a fixed time budget. If it fails, ask the coder AI to go over the code again
to check for bugs. One drawback is that, without additional information from the proving run,
repeatedly checking over the code may have diminishing returns. 
Sometimes when the theorem statement contains conjunction of multiple components,
which parts  failed 
could provide hints to which part of code to check.
If we get stuck, an option is to resample another candidate solution from the coder AI.

Additionally,   we can try to prove that the code is *incorrect*, i.e. prove the negation of the theorem statement. A theorem statement for the correctness of function f generally take the form "for all input values `x`, the return value `f x` satisfy some property `P`".
So the negation is of the form "there exists some input value `x'` such that 
the return value `f x'` violates property `P`". So a natural way to prove the negation is to construct such a counterexample.
In other words,  testing.
Sometimes the problem description contains a few sample test cases, but they generally
do not provide sufficient coverage. 

A benefit of having formal specification is that, we can do *property based testing*. 
That is, generate random input values according to the input types. Then plug them into
the negation theorem statement and try to prove it. In other words, we do
not need to know the correct output value. With fixed input values, 
 the proof task becomes much easier, and can often be done automatically (e.g. using Lean's `decide` tactic). For example, for `solveAdd` we can generate random integer input values for `a` and `b`, say 1 and 3, and then try to prove the proposition `Not (1 + (solveAdd 1 3) = 3)`.
 If our solveAdd implementation was incorrect (e.g. `a-b` instead of `b-a`), this proposition 
 can be easily proved, establishing the incorrectness of the implementation.

 There may be other ways to prove the incorrectness of a function implementation besides testing.
 E.g. if the task is to implement a comparison-sorting algorithm, and the 
 submitted function makes a linear number of comparisons, then we may conclude that the function
 is incorrect because it violates the well-known `O(n logn)` lower-bound on [the number of comparisons required for comparison sorting](https://en.wikipedia.org/wiki/Comparison_sort#Number_of_comparisons_required_to_sort_a_list).

A simple flow that combines these components together would be:
after the coder outputs the function implementation, it is passed to 
the negation prover which tries to prove the negation via property-based testing.
If the function passes all the test cases, we finally pass it to the prove to try proving its
correctness.

**2. Explore approaches for proving.**
The current state of the art in AI theorem proving
has focused on search guided by LLM policy. See e.g. AlphaProof, DeepSeek Prover 1.5.
This is natural, as the iteractive theorem prover environment of Lean provides
the current proof state, which contains rich feedback; and a natural choice for 
action set is the set of possible tactics to try. 
Other research on theorem proving, including retrieval-augmented generation (ReProver),
can also be adapted to our setting.

I will mention a couple of ideas that may be particularly relevant
in the context of proving correctness of code.
One observation is that the coder AI often is able to articulate a justification of the 
correctness of its code in natural language. 
So one idea is to adapt the [Draft-Sketch-Prove](https://arxiv.org/abs/2210.12283) approach:
Ask the coding AI to produce (in addition to code)
a proof sketch in natural language, then the coding AI (or another agent) translates this into a formal 
proof sketch consisting of a sequence of intermediate statements (but without proofs),
and finally the prover agent provide proofs of each of the intermediate statements.
The rationale is that with a good proof sketch, each of the intermediate statements would be easy to prove. (And again automated theorem proving techniques can become relevant, 
including use of SAT and Satisfiability modulo theory (SMT) solvers.) 
Applying to our toy example `solveAdd_spec`, a formal proof sketch that breaks the proof task into even smaller
logical steps would be:

{% highlight lean %}
theorem solveAdd_spec(a b: Int): a + (solveAdd a b) = b := by{
  have hsub: solveAdd a b= b-a :=by{
    sorry
  }
  have haba: a+(b-a)=b :=by{
    sorry
  }
  have hfinal: a + (solveAdd a b) = b :=by{
    sorry
  }
  exact hfinal
}
{% endhighlight %}
Here each intermediate statement is in the form of a `have` command, which
poses a statement and proves it on the right hand side of `:=`, but in this case
the proofs are missing. `sorry` is a special placeholder in Lean that makes the proofs
go through, except that the Lean proof checker will emit a warning when `sorry` is encountered.

And if the prover fails, which subgoal it fails on provides useful information
to the coder, to either refine the proof sketch to break the step down into even smaller substeps,
or to re-examine the relevant part of code to check for mistakes. 

Overall, the success of this approach will depend crucially on the ability to come up with good
proof sketches.

**3. Integrating code and proof.**
I have been practicing the task of coding up a function in Lean and proving its correctness.
Lean provides a lot of features that helps with proving, e.g. tactics like simp and omega
that are able to automatically prove simple goals, but it can still be quite
tedious to prove the correctness of seemingly simple functions. 
Lately, I have been gravitating towards a particular style.
First, a brief background: in Lean and other dependent typed languages, propositions are types.
A proof that proposition `P` implies proposition `Q` is a function from type `P` to type `Q`.
And proof checking is just type checking. 

Many of us are fans of strongly typed programming languages, because the type system
can help enforce and verify certain kinds of logical consistency on our code, if they are 
expressible as type restrictions on data. With dependent-typed languages like Lean we
can take this to the next level: we can put in the type definitions of data
arbitrary propositions that express the logical properties of the data.
The type system then does its work: this type information follows the data as
they are passed around the code, and checked when required. 
When I am ready to return a value in a function whose return type requires a certain property to be satisfied, and that property is not yet present, I am then obligated
to provide a proof that the return value satisfies the property, and pass it along with
the return value. Thus much of the proving is done inside the body of the function 
definition, interleaved with code.[^4]

For example, our `isIn` function can be implemented and proved in this style:

{% highlight lean %}
def isInTyped(x:Int)(xs:List Int)
:{b:Bool // b=true ↔ x∈ xs} :=
  match xs with
  |[] => ⟨false, by simp⟩
  |h::t =>
    let rest := isInTyped x t
    ⟨x==h || rest, by simp[rest.2]⟩
{% endhighlight %}
The return type `{b:Bool // b=true ↔ x∈ xs}` defines a *subtype* of Bool,
meaning Booleans `b` that satisfies `b=true ↔ x∈ xs`.
So this is logically equivalent to the theorem statement `isIn_correct`.
In the body we are essentially doing the same work as the function body of `isIn` plus
the proof body of `isIn_correct`. When returning in the base case and recursive case,
I am passing the value as well as the proof that the value satisfies the return type.
(The brackets `⟨ ⟩` syntax just means "pass to the constructor of the appropriate type".)
Can you spot the induction hypothesis? 

Comparing this with our earlier code and proof. For this example, both styles provide pretty
short proofs. One difference is that, now I no longer have to explicitly plug in the definition
of the function `isIn` in my proof. This difference can become significant for functions with more complex bodies.

Beyond specializing the return type, we can also attach propositions to the types
of internal data structures used by the algorithm, even individual pieces of data stored
by the data structures. This is especially natural when we are to maintain certain invariances
on the data. I will give a more illustrative example a future blog post.


Overall, I find it easier to prove in this style. It feels like coding in a very strongly-typed
language, where you sometimes need to prove a proposition in order to construct a piece of data 
with the right type. Often, there is *intention* behind how we choose to write code a certain
way; e.g. we believe this line of code is needed because it establishes a certain property of the data, which ultimately leads to the correctness of our final output. So in a way when we write code we are already doing coding and (implicit) proving at the same time. Now we are just making the proving part explicit. 

To adapt this style for our AIs, we would ask the coding AI to create
the function as in `isInTyped`, except for the proof obligations; in their places
put either `sorry`s or proof sketches that further break them down into smaller tasks with `sorry`s.

This creates a very natural proof sketch, that breaks down the proof task along the 
structure of the program.

**4.Scaling Up.**
What is the most efficient way to scale up inference-time compute to increase performance?
This is an active research area; the answer very  likely depends on the domain.
The current state of the art is o1, but I think for our purposes it is not necessary to imitate what o1 is doing.
o1's algorithm is secret, and whatever it is, it's unlikely to be the only way to achieve 
scale up. 
A recent talk I came across that looked very promising was
[Using recurrence to achieve weak to strong generalization.](https://www.youtube.com/watch?v=M7Kq0ooFFco)
More generally, I think any approach that strongly benefits from access to ground truth is worth
exploring. A few ideas to explore:

- Small, fast models for efficient search, including State Space Models (SSMs) and/or hybrids.
- Experts that specialize on subtasks.
- Retrieval augmentation.
- Prompt engineering, including few-shot prompting.
- "agent" framework to combine them together.

I will publish some of my initial explorations on GitHub in a few days; and will update
this article with the link.

### Project 2. Creating and Sharing Data

Let us consider the task of training a model to produce code and its proof.
One challenge is that the learning goal seems to be harder than producing proof only
or code only. 

I believe an essential part of the solution is Curriculum Learning. 
By progressing through a curriculum of easier to harder problems, earlier topics provide strong foundations so the student (AI) is ready for the subsequent topics.
The curriculum would be literally a curriculum of undergraduate computer science education (with proofs):

- Basics. How do write a function. Prove statements about a function. 
- Write recursive functions. Prove statements about recursive functions via induction
- Data structure and algorithms. Proofs of both correctness and efficiency
- Depending on need, go into other areas of computer science that has a rigorous foundation. E.g.,  AI topics like constraint satisfaction, Markov Decision Processes, learning theory. Linear algebra, linear programming, convex optimization. Parallel algorithms, cryptography...

Why I think curriculum learning is a good fit:
- The harder learning goal becomes a feature. This is analogous to when you are trying to prove a theorem by induction, sometimes it is better to try to prove a stronger statement, because that makes your induction hypothesis stronger. In our case, when the AI suceeds in solving and proving
(e.g.) basic recursion problems, the AI will have gained a deeper understanding / world model
than an AI that only learned the coding side.
In other words, the harder learning goal makes it easier to progress to more difficult problems.
- Curriculum learning is well suited for AlphaZero. For two-player game domains like Go and chess,
AlphaZero utilizes self-play which natually provides a curriculum as the AI player's strength 
improves. In domains like ours where self-play is not readily available, 
AlphaZero still works well as long as a curriculum of problems is provided, as in 
the case of AlphaProof for mathematical theorem proving.

Now we face the largest obstacle of the whole program: the lack of existing data.
 A standard recipe is to get data from the internet/textbooks. There are some 
 textbooks containing code with proofs, the [Software Foundations](https://softwarefoundations.cis.upenn.edu/) series, and 
 [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/), although those are written for Coq.

On GitHub / Hugginface there are a few relatively smaller scale repositories
containing Lean specifications, code, and/or proofs of code:
- [MiniCodeProps](https://huggingface.co/datasets/elohn/miniCodeProps). A benchmark for proving properties of existing code. [Paper Link.](https://arxiv.org/abs/2406.11915)  
- [LeanSpec](https://github.com/paulch42/lean-spec/tree/main) A tutorial containing examples of formal specifications of problems in Lean.
- [Algorithm](https://github.com/FR-vdash-bot/Algorithm): a collection of verified efficient algorithms.

These are all very nice, but the problem is that they are several orders of magnitude
short of the amount of data needed to train large language models. 
To compare, [AlphaProof was trained on millions of problems](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/).

Let's go back to the drawing board. Exactly what types of data do we need?
If we are planning to do AlphaZero, the curriculum need only consist of problem statements (including function signatures and formal specifications)
without solutions. 
In fact this is an important advantage of AlphaZero, compared to supervised learning approaches.
A relatively smaller number of labeled data (i.e. problem statements with solutions)
can also be useful, to train a good initial model via supervised fine tuning.


To create a large collection of formal problem statements, a promising 
direction is automated formalization of natural language source material.
Autoformalization is an active research area for AI theorem proving, and was used by AlphaProof.
I will share below in Project 3 some ideas for autoformalization in the context of coding tasks.

To create data that has solutions to problems, a couple of ideas come to mind.
One is synthetic data creation: use large models, combined with large amount of inference-time 
compute, to create solutions to problems; which can then be utilized to train smaller, faster models. Another is to create human-written solutions by crowd sourcing.

### Code with Proofs: the Arena

With that in mind, I am open-sourcing the repository [Code with Proofs: the Arena](https://github.com/GasStationManager/CodeProofTheArena) on GitHub. 
This is a website with functionalities similar to online coding challenge sites like LeetCode, HackerRank and CodeForces, where users can submit solutions to coding challenges and be judged on test cases;
except here the problems have function signatures with formal theorem statements, users submit code with proofs, and will be judged by the proof checker. 
Right now the only supported language is Lean, but I hope someone can extend it to other 
similar languages such as Coq, Idris, Dafny.

The purpose of this website is to serve as a platform to crowdsource efforts to create data on 
code-with-proof problems and solutions, 
including problem-only data as well as problem-with-solution data, 
both human-created and machine-created.
And as a platform to share this data with the open-source community, for the purpose of training
open-source models.

With this purpose in mind, I would like to set the data license of the site to benefit the open-source community. In particular, that if you train a model using
the data from this site, and you would like to release/distribute/productize the model,
you are obligated to at least make the weights of the model freely available (i.e. open-weights model). I am not an expert in data licensing; I am not aware of whether an existing license matches what we need. Perhaps a [Creative Commons](https://en.wikipedia.org/wiki/Creative_Commons_license) license like CC-BY-SA or CC-BY-NC-SA, if the Share-Alike (SA) clause also covers models trained on the data. Suggestions are welcome.

On the other hand, if you would like to contribute data to the website, and your data is generated base on some existing data source and/or LLM model output, you want to make sure the license
of the existing data source / LLM model is compatible with you open-sourcing your data this way. 

The GitHub repository contains the source code but the website is not yet officially hosted anywhere. *(Update 11/13: A [Demo site](http://5.78.72.236:8000) is up.)* My hope is for someone from the open source community to fork the repo and host the website. Whoever hosts the website can decide on the data license for the site (and be prepared to enforce it). Given the license, people can decide whether to contribute data to the site.

### Code with Proofs Benchmark

I am also open-sourcing [Code with Proofs Benchmark](https://github.com/GasStationManager/CodeProofBenchmark) on GitHub. This is an initial effort at constructing a benchmark
of code-with-proof problems, so that folks working on the inference-time scaling
or learning aspects (or both) can measure progress.

The benchmark consists of 24 problems with solutions.
Each problem statement consists of a natural language description, a function signature,
and the formal specification consisting of up to two theorem statements. Currently in Lean only; translation to
other languages is welcome.
In the spirit of curriculum learning, for this initial benchmark I focused on selecting
simple (but not trivial) problems involving non-recursive functions and basic recursive functions
on natural numbers and lists.
Future releases will add medium-level hardness problems including recursion on arrays and trees,
reasoning about computational efficiency/resource usage, sorting, etc.
And progressing to more advanced problems involving dynamic programming, 
greedy methods, divide-and-conquer, advanced data structures and graph algorithms.

Contributions are welcome. 
One issue is the need to make sure the benchmarks and training data are not cross contaminated.
If the Code with Proofs: the Arena website 
become more popular, one approach would be to do what [LiveBench](https://livebench.ai/) does: select from the recently created
problems as benchmarks, and evaluate models trained on problems created before the cutoff date.

### Project 3. Autoformalization

We have an abundance of natural-lanuage descriptions of coding tasks available on the Internet.
So a natural approach is to use a large language model to translate them into formal problem
statements. A challenge is that the models' translation might not be faithful;
manually checking the model's outputs would be costly, and does not scale up.

[AlphaProof](https://www.youtube.com/watch?v=pkpJMNjvgXw) had an ingenious solution to this: as long as the translation model's output is
syntactically valid, it represents some formal problem statement (even if it may not match the natural language version). Just use the formal problem statements (without the natural language description) as training data for AlphaZero.

This approach can be adapted to our code-with-proofs domain, and is certainly worth trying.
A drawback is that all the natural language descriptions has to be thrown away. 
In the following I am going to explore a variation of this approach
that can hopefully produce formal problem statements matching the natural language description.
Why do I want that? One reason is that existing coding models are already very good at 
taking natural language problem description and outputing code. 
Another reason is that models that can accruately translate from natural language to formal problem specification will become very useful in the future (though we will still want humans to be in the loop; see discussion in Section 4). 

Given a model-translated formal problem specification, how do we verify its faithfulness?
Many coding problem data sets come with test cases with inputs and expected outputs.
If the translation is faithful, these input-output pairs should be compatible with the 
formal specification. Whereas normally we would plug our implemented function into the 
theorem statement, here we do not yet have an implemented function but the input-output pairs serve as surrogates. 

Consider our earlier example with `solveAdd`. Let us rewrite the theorem statement 
into the following logically equivalent formulation:
{% highlight lean%}
def solveAdd_prop(inp_a inp_b output : Nat):= inp_a + output = inp_b

theorem solveAdd_correct (a b:Nat) : solveAdd_prop a b (solvdadd a b) :=
{% endhighlight %}
We have now factored out a function `solveAdd_prop` that takes input and output values,
and returns a proposition that specifies the relationship the input and output values should
satisfy. In particular `solveAdd_prop` does not refer to the function `solveAdd`, so we do not need to have an implemented solveAdd function.
Given a test case with input 3, 7 and output 4, we can plug these values into `solveAdd_prop`, and 
try to prove 
`theorem prop_true: solveAdd_prop 3 7 4`
or its negation 
`theorem prop_false: Not (solveAdd_prop 3 7 4)`.
Similar to the property-based testing scenario, these can often be easy to prove, and automated
methods can be applied.

If the `solveAdd_prop` passes all the test cases, we have a relatively high confidence that
it faithfully captures the original problem description, and can attach the problem description
with the formal specification together as training data.
Furthermore, the pass/fail results can be used as ground truth to train better translation models.

For datasets of problems without test cases, if the dataset also comes with correct code solutions in some language
(e.g. Python), we can use the solution code together with randomly generated input values (as in property-based testing)
to generate the expected output values, which forms the test cases we need for the above approach.

I am open-sourcing [FormalizeWithTest](https://github.com/GasStationManager/FormalizeWithTest), a simple proof-of-concept of this process.

### Project 4. AlphaZero
If we are able to make good progress on Projects 1, 2 and 3, we will have all the key ingredients
we need to attempt an AlphaZero training loop. 
I think we will likely need a couple of additional things:
1. sufficient compute, and
2. some expertise in deep reinforcement learning. 
 
I say this as an non-expert in reinforcement learning. If this is your first reinforcement learning project, you might have a hard time. Is it a coincidence that it was again David Silver and DeepMind
that achieved the AlphaProof result, even though in theory anyone could have applied AlphaZero to the problem of mathematical theorem proving? I think part of it was that they strongly believed in their approach; but another big part of it is that their expertise and experience in reinforcement learning allows them to actually carry it out, overcoming any obstacles that arise on the way.

Nevertheless, I believe some in the open source community are well-equipped to attempt this.
For example an academic lab with some experience in reinforcement learning and access to some compute.


# 4. Some Final Remarks

### 4.1 Related Work

I will not attempt to give a comprehensive literature review. 
Instead I will recommend a few works that influenced my thinking and I think the readers will enjoy.

- [David Silver's talk at Reinforcement Learning Conference 2024](https://www.youtube.com/watch?v=pkpJMNjvgXw) goes into the AlphaProof work.
- [Towards Guaranteed Safe AI: A Framework for Ensuring Robust and Reliable AI Systems](https://arxiv.org/abs/2405.06624) 
- [Clover](https://arxiv.org/abs/2310.17807)

My background is in AI; I am relatively unfamiliar with the Formal Verification literature, but am trying to learn as much as I can. I think with the recent advances of LLMs, there will be many opportunities to combine ideas from AI and formal verification. E.g. tools from formal verification that are useful but thought to be hard to scale up because they sometimes require humans to manually finish the proof: now they can be revisited, to see whether LLMs can help automate the 
remaining proof tasks.

### 4.2 On Timing

Open-sourcing the project at this preliminary statge may seem unusual. 
Indeed when many academic labs and industry labs open source their code, it is at a 
finished state.
This stems from different goals. 
E.g. at an academic lab, the plan is for the students and professor to do the research and
then publish. Open sourcing too early would risk someone else taking the idea and publish first.
My goal is to invite collaboration, and 
the timing is chosen accordingly. There is some similarity to Polymath type projects in mathematics.
Within AI/machine learning, examples of collaborative open source projects include the Leela Zero and Leela Chess Zero projects
that replicated the AlphaZero algorithm for Go and chess respectively.

As mentioned in the preface, it would not surprise me if one or more labs are already working along similar directions.
If you are an academic lab in this situation, my message is:
I am in no way trying to compete for publication credits. In fact I am not planning 
to write any paper based on what I am open sourcing today.
On the other hand,  I hope you realize that, you are not going to be faster than the frontier labs if you work on this by yourselves. Joining forces in a open-source collaboration is our best bet.
If you are an industry lab, my message is similar: unless you are a frontier lab, 
you may be better off joining with the open source effort.
 Imagine you are in the final table a poker tournament. Only the winner takes the prize and 
everyone else gets nothing. You are currently second place in chips but far behind the chip leader.
What would be your best strategy?


### 4.3 Why This Will Work
Let me summarize a few key reasons I believe our  proposed research agenda is likely to work.
- By formulating the code generation task as code-with-proof, we can utilize the interactive proof system's feedback as ground truth, which then grounds both search and learning efforts.
- Our formulation aligns the AI Safety objective with the ability improvement objective: 
in our framework,
a strong, hallucination-free coding AI will also be safe.

Once our research agenda shows promise in improved coding performance within the Lean language,
hopefully this will attract efforts to build bridges between Lean and other languages, 
to either translate Lean code to other languages, or allow proof of correctness of code from other languages in Lean.

Q. *Isn't the situation even better than what you describe?
Once the AI is able to internalize the better world model that it learned from interacting with Lean, it should be able to apply this to improved coding ability in other languages like Python.
So it may already be able to write hallucination-free code in Python, without needing a verifier specifically for Python.*

A. Well that may be true, but please read on...

### 4.4 Don't forget about Safety

I started this essay talking about safety. I would like to end the essay 
coming back to discuss safety.
What happens if our proposal for superhuman level coding AI, outlined in the 
middle portion of this essay, suceeds?
As with any technology that aims to produce superhuman performance in coding,
this carries risks (as outlined in Section 1).
The protocol we proposed in Section 2 is an effective guardrail against such risks,
but **only if used correctly.**

Generally, as we argued in Section 3, having the proof checker at inference time also helps boost accuracy, so the safety and performance objectives are often aligned. But I see a couple of potential risks for misuse, which I outline below.

- There are situations where people would be tempted to go without
proof checking at inference time, E.g. to produce code in a popular language (say Python)
that does not yet have infrastructure set up for formal verification.
This is exactly the failure mode we outlined in Section 1: a superhuman level AI
producing code that is not checked. We may be lured into a false sense of security
because proof checking is done during training. 
I would like to emphasize that **proof checking during training helps improve ability but does not guarantee security at deploy time. Only proof checking during inference time can guarantee security.**

- Another risk is that people may be tempted to leave the task of creating formal specifications
completely to the AIs. *"In an ideal world, we should only have to specify what we want in natural language,
and these language models should be able to do the rest."*
But that is not safe, at least under the current framework outlined in this essay.
Automating formalization
can be useful during traning; and we can make use of tools (AI based or otherwise) that helps us
in the process of translating requirements into formal specification; 
but **our protocol works only if we humans understand the formal specification and are able to verify that it matches what we want.**[^5]

I believe the safety protocol proposed in Section 2 warrants consideration
independent from the merits of our subsequent proposal of building 
an AI that will pass the protocol. Specifically:
- Even if some other approach achieves superhuman performance in coding first,
our safety protocol can and should still be applied.
- In the somewhat likely event that a frontier lab first develops a superhuman-level coding AI, 
that claims to be hallucination-free due to the use of a formal verifier,
we should be ready to keep them honest and demand them to 
provide enough so that we can verify the output ourselves:
if the model outputs in a language like Python, demand a machine-verifiable proof of correctness. 
If they offer a service to automatically turn natural language specification into
code, demand the formal specification to be provided as well, so that we can make sure that the
formal specification macthes our goals.

Finally, comments and suggestions are welcome. I can be reached at the email in the [About](/about/) page. 
And please check out [my GitHub](https://github.com/GasStationManager) which contains the repositories mentioned in this essay. 

---
# Footnotes
[^1]: As I am writing this, OpenAI's o1 "strawberry" was released. Very impressive improvement in reasoning and coding ability; which makes it even more important to have this conversation. Another recent news headline: 25% of code at Google is being written by AI.

[^2]: And are you prepared to invest in your own nuclear reactor?

[^3]: A brief survey of current coding and proving models. On the coding side, unfortunately not many models are fluent in Lean 4 (the current version). The transition from Lean 3 to 4 only happened recently, and the new syntax and old syntax are not compatible. As a result many models' training data consists of Lean 3 code and therefore still uses Lean 3 syntax. Open-weights Models I tried that are reasonably fluent in Lean 4 include DeepSeek Coder V2, Jamba 1.5, and Qwen 2.5 Coder. Among closed models, Anthropic's Sonnet 3.5 is scarily good. On the proving side, the state of the art is AlphaProof, but it is not available as weights nor API. Open models that can operate in Lean 4 include DeepSeek Prover 1.5, InternLM 2 Step Prover, and LeanDojo/ReProver, although they are trained to prove mathematical theorems.

[^4]: I of course did not invent this; this is known as programming with dependent types. For more details, see [this chapter](https://lean-lang.org/functional_programming_in_lean/dependent-types.html) in the Functional Programming in Lean book, or the book [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) (in Coq).

[^5]: This may feel unsatisfying to some. Philosophically, I believe that the ability to communicate in code, a language that both human and computers understand, is a feature. We humans  moving from raw coding to creating formal specifications is like moving to a higher-level programming language. We will be able to make creation of formal specifications more and more user-friendly; the formal language may look more and more like English, but will remain formal, in that it follows formal rules and can be machine-verified. In this future, software engineers will focus on the higher-level design and then the creation and communication of the specification to the coding AI.
