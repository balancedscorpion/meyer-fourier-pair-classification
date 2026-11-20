module

public import MeyerGeneralProblem.Sampling.KNSGraphRepresentative
public import MeyerGeneralProblem.Sampling.CanonicalGraphInterpolator

@[expose] public section

/-!
# Actual point identification on the canonical graph interpolator range

The chosen graph representative equals the existing smooth interpolating
function everywhere. Original signed-square prefixes and decoded on-carrier
values then agree exactly. This is a range-identification theorem, not a
bounded full sampler on arbitrary graph elements.
-/

namespace MeyerGeneralProblem
namespace KNSGraphSpace

noncomputable section

open MeasureTheory
open scoped FourierTransform ContDiff

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
  (ho : BoundedClusterOrder S.signedSquareImage d q)
  (N k : ℕ) (hk : 2 ≤ k) {B : ℝ} (hB : 1 ≤ B)
  (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) (b₀ : ℤ)
  (hpositive : ∀ j : ℤ, b₀ ≤ j →
    (orientedBlockPoints S.signedSquareImage B 1 j).ncard ≤ N)
  (hnegative : ∀ j : ℤ, b₀ ≤ j →
    (orientedBlockPoints S.signedSquareImage B (-1) j).ncard ≤ N)
  (start : ℕ) (hstart : 3 ≤ start) (hstart₀ : b₀ + 1 ≤ (start : ℤ))
  (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) → Fin (ho.clusterSize C))

/-- The actual reflected-Fourier representative of the existing graph
interpolator equals its named smooth function at every real point. Continuity
of both functions upgrades their actual AE equality; no samples are inferred
from AE equality alone. -/
theorem representative_canonicalGraphInterpolator
    (y : ho.CanonicalGraphData) :
    representative k (S.canonicalGraphInterpolator ho N k hk hB hd hdiam b₀
      hpositive hnegative start hstart hstart₀ anchor y) =
      S.canonicalGraphFunction ho k hd hB start anchor y := by
  have h := S.canonicalGraphInterpolator_represents_prefixes ho N k hk hB hd hdiam b₀
    hpositive hnegative start hstart hstart₀ anchor y
  apply ((representative_contDiff_pair hk _).1.continuous.ae_eq_iff_eq volume
    h.1.continuous).mp
  exact (representative_ae (by omega : 1 ≤ k) _).trans h.2.1

/-- Every original signed-square prefix of the actual representative equals
the decoded canonical datum, including central clusters and the negative ray. -/
theorem representative_canonicalGraphInterpolator_prefix
    (y : ho.CanonicalGraphData) :
    ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap
      (representative k (S.canonicalGraphInterpolator ho N k hk hB hd hdiam b₀
        hpositive hnegative start hstart hstart₀ anchor y))) =
      ho.canonicalGraphDecode k anchor y := by
  rw [representative_canonicalGraphInterpolator S ho N k hk hB hd hdiam b₀
    hpositive hnegative start hstart hstart₀ anchor y]
  exact S.canonicalGraphFunction_prefix ho k hd hB start hstart anchor y

/-- At each actual signed-square carrier node, finite Newton decoding gives
the representative's value at its unique physical preimage. This uses the
proved on-carrier pullback restriction, not off-carrier smoothness. -/
theorem representative_canonicalGraphInterpolator_node
    (y : ho.CanonicalGraphData) (s : S.signedSquareImage.subtype) :
    ho.canonicalDataValueMap (ho.canonicalGraphDecode k anchor y) s =
      representative k (S.canonicalGraphInterpolator ho N k hk hB hd hdiam b₀
        hpositive hnegative start hstart hstart₀ anchor y)
        (S.signedSquareSubtypeEquiv.symm s) := by
  rw [← representative_canonicalGraphInterpolator_prefix S ho N k hk hB hd hdiam b₀
    hpositive hnegative start hstart hstart₀ anchor y,
    ho.canonicalDataValueMap_canonicalPrefixData,
    S.physicalSignedSquarePullbackMap_on_carrier]

end
end KNSGraphSpace
end MeyerGeneralProblem
