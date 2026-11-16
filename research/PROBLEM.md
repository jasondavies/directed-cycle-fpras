# Directed-cycle probability

Given a finite directed graph G=(V,E), retain each edge e independently with
rational probability p_e in [0,1]. Let Z be the probability that the retained
subgraph contains a directed cycle. Can Z be approximated with relative error
epsilon in time polynomial in the binary input length and 1/epsilon, with
success probability at least 3/4? A fully polynomial randomized approximation
scheme (FPRAS) must work even when Z is exponentially small. When Z=0 it
must return zero with the required success probability; the written algorithm
handles this case exactly.

The model permits distinct parallel arcs and self-loops. In the Lean model,
cyclicity is expressed as the existence of a nonempty closed directed walk.
For ordinary directed graphs this expresses the same existence property as
a directed cycle. Edge identities are separate from endpoint pairs.

Sources:

- [Antoine Amarilli's problem entry](https://a3nm.net/work/research/questions/#fpras-for-the-probability-of-obtaining-a-cyclic-subgraph-of-a-directed-graph).
- [Original TCS Stack Exchange question](https://cstheory.stackexchange.com/questions/53359/fpras-to-estimate-the-probability-to-get-a-cyclic-subgraph-of-a-directed-graph).
- [Amarilli, van Bremen, Gaspard, and Meel, Approximating Queries on Probabilistic Graphs](https://lmcs.episciences.org/17113).

On 2026-11-12 the problem remained in the source's main list, and the live
Stack Exchange API reported zero answers and zero comments. Targeted searches
found no separate public cycle-probability solution. This is a record of a
search, not proof that no prior solution exists.

The proposed answer is positive via an approximation-preserving oracle
reduction to general directed two-terminal reliability. See
[the manuscript](../paper/directed-cycle-fpras.pdf) and the precise [Lean scope](../validation/FORMALIZATION.md).

## Novelty check, 2026-11-16

The publication case rests on the cycle-probability consequence, not on new
general approximation machinery. Karp–Luby–Madras supplies union estimation;
[Jerrum–Valiant–Vazirani](https://ics.uci.edu/~vazirani/JVV.pdf), proofs of
Theorems 3.3 and 6.3, supplies rejection correction and the accurate-oracle
comparison. The manuscript attributes these methods explicitly.

Targeted searches for “directed-cycle probability” with FPRAS, “cyclic
subgraph” with FPRAS, and directed acyclicity probability/counting with
approximation found the original question and related work, but did not
establish whether the consequence or the complementary hardness result was
already known. Search results are incomplete and may predate the reliability
preprint. No novelty conclusion follows from this check.

Before submission, ask the question's author and a reliability/counting
specialist whether the consequence was recognized after Feng–Fu–Guo and
whether the witness reduction merits a short standalone note. The
[feedback drafts](feedback-drafts.txt) remain unsent. The current
[manuscript](../paper/directed-cycle-fpras.pdf) contains the weighted analysis
and explicit conservative bit bounds; independent checking remains pending.
