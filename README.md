# Written on the Wall II, Conjecture 61: a Lean 4 proof

**Theorem.** For every finite connected simple graph $G$ on at least two vertices,

$$f(G) \ge \mathrm{residue}(G) + \lceil \mathrm{diam}(G)/3 \rceil,$$

where $f(G)$ is the number of vertices of a largest induced forest, $\mathrm{residue}(G)$ is the
Havel–Hakimi residue of the degree sequence, and $\mathrm{diam}(G)$ is the diameter.

This is Conjecture 61 of E. DeLaViña's *Written on the Wall II* (conjectures of Graffiti.pc). The
formal statement is the one in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean)
(`conjecture61`, tagged `research open` there on 26 November 2026), copied verbatim with its
definitions. Two proofs inside the copied definitions differ from the source (the helper
lemma `havelHakimiStep_length_cons` uses `rw` instead of `grind`, and a redundant `omega` is
removed from the termination proof of `residueAux`); no definition or statement is changed.

## Layout

| File | Contents |
|---|---|
| `Challenge.lean` | The statement with `sorry`, and the definitions it uses. |
| `Solution.lean` | The same statement, proved. |
| `Wowii61/Defs.lean` | The definitions, copied from formal-conjectures. |
| `Wowii61/Main.lean` | The proof (about 1,290 lines). |
| `PROOF.md` | The mathematical argument in about two pages. |
| `comparator.json`, `formalization.yaml` | Metadata for the Palomar registry. |

## Checking it

```sh
lake exe cache get
lake build
```

Lean 4.35.0, Mathlib v4.35.0. The theorem `WrittenOnTheWallII.GraphConjecture61.conjecture61` in
`Solution.lean` depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. There
is no `sorry` outside `Challenge.lean` and no `native_decide`.

## Idea of the proof

Let $m = \lceil \mathrm{diam}(G)/3 \rceil$. On a diametral geodesic, mark the adjacent pairs at
positions $(0,1), (3,4), \dots$. The $2m$ marked vertices $U$ induce a perfect matching, and every
vertex outside $U$ has at most two marked neighbours, which are consecutive along the path.

**Lemma.** If $U$ induces a perfect matching in $G$, there is an independent set $S$ outside $U$
with $\mathrm{residue}(G) \le |S| + \lceil |U \setminus N(S)|/2 \rceil$.

The lemma is proved by a maximum-degree deletion argument: the matching on $U$ is re-paired in
deletion order, which keeps the degree sequence, and deleting a maximum-degree vertex never
decreases the residue (Favaron, Mahéo and Saclé 1991; Griggs and Kleitman 1994). Dropping the
smaller parity class of $U \cap N(S)$ then leaves $S$ together with the remaining marked vertices
as an induced forest with at least $\mathrm{residue}(G) + m$ vertices. Details are in `PROOF.md`.

## How this was produced, and what has and has not been checked

- The proof was found and formalised by an AI system, OpenAI GPT-6.2 Astra, running as a coding
  agent, on 25–26 November 2026. No human wrote proof code.
- A second AI system, Anthropic Claude (Claude Code), supervised the run and independently rebuilt
  the proof against formal-conjectures, checking that the proved statement is identical to the
  original and that only the three standard axioms are used. It also did the packaging in this
  repository.
- The written argument in `PROOF.md` has not been checked by hand by a human and has not been peer
  reviewed. The Lean check is the evidence.
- Prior work: searches of the formal-conjectures issues and pull requests, the Palomar registry,
  ProofXiv, arXiv, Zenodo and the web on 26 November 2026 found no earlier complete proof. The
  closest result found is H. Chen, *Partial Results on the WOWII-61 Graffiti Conjecture* (August
  2026, <https://doi.org/10.5281/zenodo.22069069>), which leaves the general case open. If you
  know of an earlier proof, please open an issue so it can be credited.

## Licence

Apache-2.0. The formal statement and the definitions of `havelHakimiStep`, `residueAux`,
`residue` and `largestInducedForestSize` are from google-deepmind/formal-conjectures (Apache-2.0).
