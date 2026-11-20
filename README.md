# Finite-hole and lower-ray classifications of Meyer Fourier pairs

## Finite-comb and finite-hole classification for relatively separated carriers

Let Λ be a locally finite subset of the real line with a uniform bound on the number of points in each integer unit cell. The whole complex Meyer space of tempered distributions T with value-only atomic physical and Fourier records on Λ has finite dimension. Its dimension equals the attained maximum of nullities over finite unions L of translated positive-step full lattices for which L ∖ Λ is finite. For each L, the original physical and Fourier coefficients must both vanish at every missing site. In finite lattice residue coordinates, subtracting the joint rank of these rows from the sum of the cyclotomic block nullities gives the envelope nullity. One such envelope realizes the whole space. With separate relatively separated carriers both members of the Fourier pair are finite sums of translated and modulated lattice Dirac combs. The separately stated one-record H6 theorem only bounds the physical carrier. The active spectral module is finitely generated, and a single nonzero exponential polynomial with frequencies in that module annihilates every member of the fixed-carrier space.

[Lean statement](WholeSpace/Challenge.lean) · [Proof imports](WholeSpace/Solution.lean) · [Compared declarations](WholeSpace/comparator.json) · [Formalization metadata](WholeSpace/formalization.yaml)

## Annihilation and finite-comb classification from finite lower density on one ray

Let T be a tempered distribution on the real line with value-only atomic records for T and its Fourier transform on locally finite carriers. If the point count on either ray of the physical carrier is bounded by C times the radius along arbitrarily large radii, a nonzero finite real-frequency exponential polynomial annihilates T. The opposite carrier only needs to be locally finite for this implication. When the counted carrier is the actual support and the centred count of the opposite carrier has zero quadratic lower density, both records are finite sums of translated and modulated lattice Dirac combs. The latter conclusion also holds with the Fourier record as the counted actual support. The radii witnessing lower density may be sparse.

[Lean statement](LowerRay/Challenge.lean) · [Proof imports](LowerRay/Solution.lean) · [Compared declarations](LowerRay/comparator.json) · [Formalization metadata](LowerRay/formalization.yaml)

## Reading the statements

Value-only atomicity means that the distribution vanishes on every Schwartz test function whose values vanish at all carrier sites. This excludes derivatives of point masses. A carrier may include inactive sites. In the comb implication with a one-ray count, each site on the entire counted carrier must have a nonzero coefficient. The opposite carrier may contain inactive sites. All frequencies are real, the comb steps are positive and Fourier transformation uses the negative exponential sign.

Each Challenge imports Mathlib directly. The named definition holes are specified by compared theorems giving the value of an isolating test on the carrier, the action of a modulated comb on every Schwartz test, and pointwise multiplication by the annihilating polynomial. The whole-space Challenge also characterizes the lattice union by its exact membership test. These specifications fix the coefficient evaluations and spaces used by the statements.

## Building and verifying

Install the toolchain named in `lean-toolchain`. From the repository root run the following commands.

```sh
lake exe cache get
lake build
lake comparator --config WholeSpace/comparator.json
lake comparator --config LowerRay/comparator.json
```

Each entry uses the repository root as its Lake project. Select the matching Comparator and metadata paths above. The manual GitHub workflow runs Palomar’s full reusable preflight against a specified public commit. The present claims concern the stated carrier and counting hypotheses. The unrestricted Meyer problem remains open.

## Mathematical and formal sources

The public source tree contains the selected Lean modules and their recursive project imports. The pinned public dependencies are recorded in `lake-manifest.json`. The upstream project remains private. See the [provenance and review record](docs/PROVENANCE.md) and the [per-module source digests](docs/sources.json).
