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

## Available sources
A lot of work is available on the internet, here I gather some of it:
- https://github.com/dwrensha/compfiles lists various problems and solutions in Lean4 for IMO, USAMO and other mathematical competitions.
- https://imo-grand-challenge.github.io/ the classical well-known challenge to build an AI that can win a gold medal in the competition. Of course, this project is part of this challenge.
- https://github.com/leanprover-community/mathlib4/tree/master/Archive/Imo archive of a few problems.
- https://github.com/jsm28/IMOLean/tree/main
- https://github.com/roozbeh-yz/IMO-Steps the closest to ours, it covers some "building blocks" of IMO problems.
- https://arxiv.org/html/2508.14644v1 paper about formalizing Geometry problems in Lean4.
- https://www.youtube.com/playlist?list=PLCX7V9VYd16cpuYoH_affUDbusZMGN05p set of videos regarding formalization.
- https://warwick.ac.uk/fac/cross_fac/eduport/edufund/projects/yang/projects/a-lean-dataset-for-international-math-olympiad-small-steps-towards-writing-math-proofs-for-36b83d/ dataset for IMO for AI training.
- https://arxiv.org/html/2507.15225v1 a way to solve IMO problems via decomposition.
- https://deepmind.google/ main Google page, recall that AlphaProof is a benchmark for the AI solver.