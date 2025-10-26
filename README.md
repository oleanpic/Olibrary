# Number Theory Lean4 library for the Mathematics Olympiads
In this project, we plan to gather all (even if "some", or even "one" would be good enough!) useful lemmata used to help in the resolution of Mathematical Olympiad problems in the domain of Number Theory, formalizing them in Lean4 using the Mathilb library https://github.com/leanprover-community/mathlib4.

## Why this project
The goal, together with the libraries for the other domains, is to demonstrate that an LLM trained on an enhanced library, designed for a specific purpose, can perform better than one which uses plain Mathilb when dealing with Mathematical Olympiads problems. Here "better" means that it takes less time, and produces better-quality proofs (shorter, more human readable etc...). In particular, a fair amount of human judgement is required to consider a proof "better", although a specific LLM assessing "proof clarity" can be used as a benchmark.

## Lemmata to include
Various lemmata can be deemed useful, including:
- Results from local or global syllabi, preparatory courses, classes etc... related to Mathematical Olympiads or similar competitions.
- Intermediate lemmata used in the solution of one of the problems in the past editions. Even entire statements or generalizations of them can be considered.
- Results from mathematical folklore, forums, communities, or in general statements that are simple and generic enough for common sense to consider them useful for the competition.

## Lemmata not to include
We do not want to specifically exclude any particular lemma, since we are aware that machine proving is conceptually different from human proving. However, willing to keep the solver "as human as possible", we should avoid:
- University-grade theories or research topics.
- Highly specialized lemmata requiring complex, long proofs that would be impossible to present for a human candidate during the competition.
- The general criterion is "would it be realistic that a candidate could use a lemma during the competition, including its proof in case such lemma is not well-known or in the syllabi?" If the answer is no, then such lemma should be avoided.

