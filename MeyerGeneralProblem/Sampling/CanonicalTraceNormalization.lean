module

public import MeyerGeneralProblem.Sampling.CanonicalJointSampler
public import MeyerGeneralProblem.Gram.CanonicalGroupedPositivity
public import MeyerGeneralProblem.Endpoint.CanonicalGroupedCompactModel
public import MeyerGeneralProblem.Trace.SamplingCokernel
public import Mathlib.Analysis.Normed.Lp.lpHolder

@[expose] public section

/-!
# Canonical graph-to-trace normalization

This module identifies the canonical graph-sampler normalization with the
normalization of the actual grouped Hermite trace atoms. The comparison is
an explicit bounded diagonal equivalence, uniformly bounded above and away
from zero. Its final pairing identity holds for every coefficient vector,
not merely for finitely supported coordinates.

The final synthesis theorem retains the genuine
`groupedHermiteDifferentiationOrder (q + 1) ≤ m` premise of the existing
grouped Bessel analysis. In particular it is not used as a vacuous order-one
bridge, and it asserts neither joint-sampler closed range nor coercivity.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal FourierTransform

namespace BoundedClusterOrder

/-- The dimensionless comparison between the canonical signed-square graph
weight and the actual Hermite diagonal scale. -/
def signedSquareGraphHermiteRatio (x : ℝ) : ℝ :=
  (1 + |x|) ^ 2 / (1 + x ^ 2)

/-- The graph/Hermite comparison ratio always lies between one and two. -/
theorem signedSquareGraphHermiteRatio_mem_Icc (x : ℝ) :
    signedSquareGraphHermiteRatio x ∈ Set.Icc 1 2 := by
  have hden : 0 < 1 + x ^ 2 := by positivity
  constructor
  · rw [signedSquareGraphHermiteRatio, le_div_iff₀ hden]
    nlinarith [sq_abs x, abs_nonneg x]
  · rw [signedSquareGraphHermiteRatio, div_le_iff₀ hden]
    nlinarith [sq_abs x, sq_nonneg (|x| - 1), abs_nonneg x]

/-- At graph order `2 * m`, the graph weight and Hermite decay combine
exactly into a power of the dimensionless comparison ratio. -/
theorem signedSquareGraphHermite_balance
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (1 + |x|) ^ (4 * m - 1) *
        ((1 + x ^ 2)⁻¹) ^ hermiteResolventHalfShape m =
      (signedSquareGraphHermiteRatio x) ^ hermiteResolventHalfShape m := by
  have hb : 0 ≤ 1 + |x| := by positivity
  have ht : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  have hexp : ((4 * m - 1 : ℕ) : ℝ) =
      2 * hermiteResolventHalfShape m := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * m)]
    unfold hermiteResolventHalfShape
    push_cast
    ring
  rw [← Real.rpow_natCast, hexp, Real.rpow_mul hb, Real.rpow_two,
    ← Real.mul_rpow (sq_nonneg _) ht]
  rfl

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
  (ho : BoundedClusterOrder S.signedSquareImage d q)

/-- The actual minimum-modulus physical anchor, cast to the definitionally
equal canonical cluster-size presentation expected by graph data. -/
def canonicalActualAnchor
    (C : CanonicalClusterIndex S.signedSquareImage d) : Fin (ho.clusterSize C) :=
  ho.signedGrouping.anchor C

/-- The exact diagonal factor converting canonical graph sampling coordinates
to the normalization of the actual grouped Hermite atoms. -/
def canonicalToActualTraceFactor
    (m k : ℕ) (hm : 1 ≤ m)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (C : CanonicalClusterIndex S.signedSquareImage d) : ℝ :=
  ho.canonicalGraphWeight k anchor C * ho.signedGrouping.weight m hm C

/-- For the actual minimum-modulus anchor, the square of the canonical graph
weight is the required signed-square polynomial weight. -/
theorem canonicalGraphWeight_actualAnchor_sq
    (m : ℕ) (hm : 1 ≤ m)
    (C : CanonicalClusterIndex S.signedSquareImage d) :
    ho.canonicalGraphWeight (2 * m) (ho.canonicalActualAnchor S) C ^ 2 =
      (1 + |(ho.signedGrouping.point C (ho.signedGrouping.anchor C) : ℝ)|) ^
        (4 * m - 1) := by
  rw [ho.canonicalGraphWeight_sq]
  simp only [canonicalActualAnchor]
  rw [← ho.signedGrouping_realNodes C (ho.signedGrouping.anchor C)]
  unfold OrderedCarrierGrouping.realNodes
  rw [abs_signedSquare, Real.sqrt_sq_eq_abs, abs_abs]
  congr 1
  omega

/-- The squared diagonal trace factor has uniform positive lower and finite
upper bounds independent of the canonical cluster. -/
theorem canonicalToActualTraceFactor_sq_bounds
    (m : ℕ) (hm : 1 ≤ m)
    (C : CanonicalClusterIndex S.signedSquareImage d) :
    hermiteDiagonalFloorConstant m ≤
        ho.canonicalToActualTraceFactor S m (2 * m) hm
            (ho.canonicalActualAnchor S) C ^ 2 ∧
      ho.canonicalToActualTraceFactor S m (2 * m) hm
            (ho.canonicalActualAnchor S) C ^ 2 ≤
        hermiteRawNormalizationConstant m *
          (2 : ℝ) ^ hermiteResolventHalfShape m := by
  let x : ℝ := ho.signedGrouping.point C (ho.signedGrouping.anchor C)
  let g : ℝ :=
    ho.canonicalGraphWeight (2 * m) (ho.canonicalActualAnchor S) C
  let w : ℝ := ho.signedGrouping.weight m hm C
  have hgpos : 0 < g := ho.canonicalGraphWeight_pos (2 * m)
    (ho.canonicalActualAnchor S) C
  have hwpos : 0 < w := ho.signedGrouping.weight_pos m hm C
  have hgsq : g ^ 2 = (1 + |x|) ^ (4 * m - 1) := by
    exact ho.canonicalGraphWeight_actualAnchor_sq S m hm C
  have hwupper : w ^ 2 ≤
      hermiteRawNormalizationConstant m *
        ((1 + x ^ 2)⁻¹) ^ hermiteResolventHalfShape m := by
    exact grouped_norm_hermitePointMass_sq_le_scale m hm x
  have hwlower : hermiteDiagonalFloorConstant m *
        ((1 + x ^ 2)⁻¹) ^ hermiteResolventHalfShape m ≤ w ^ 2 := by
    have h := hermitePointMassDiagonalFloor_le_norm_sq m hm x
    rw [hermitePointMassDiagonalFloor_eq_rpow m hm x] at h
    simpa only [w, OrderedCarrierGrouping.weight, x, hermiteDiagonalScale] using h
  have hq : 0 ≤ hermiteResolventHalfShape m :=
    (hermiteResolventHalfShape_pos hm).le
  have hratio := signedSquareGraphHermiteRatio_mem_Icc x
  have hbalance := signedSquareGraphHermite_balance m hm x
  constructor
  · change hermiteDiagonalFloorConstant m ≤ (g * w) ^ 2
    calc
      hermiteDiagonalFloorConstant m =
          hermiteDiagonalFloorConstant m * 1 := by ring
      _ ≤ hermiteDiagonalFloorConstant m *
          (signedSquareGraphHermiteRatio x) ^ hermiteResolventHalfShape m := by
        apply mul_le_mul_of_nonneg_left _ (hermiteDiagonalFloorConstant_pos m).le
        simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
          hratio.1 hq
      _ = g ^ 2 * (hermiteDiagonalFloorConstant m *
          ((1 + x ^ 2)⁻¹) ^ hermiteResolventHalfShape m) := by
        rw [← hbalance, hgsq]
        ring
      _ ≤ g ^ 2 * w ^ 2 := by gcongr
      _ = (g * w) ^ 2 := by ring
  · change (g * w) ^ 2 ≤ _
    calc
      (g * w) ^ 2 = g ^ 2 * w ^ 2 := by ring
      _ ≤ g ^ 2 * (hermiteRawNormalizationConstant m *
          ((1 + x ^ 2)⁻¹) ^ hermiteResolventHalfShape m) := by gcongr
      _ = hermiteRawNormalizationConstant m *
          (signedSquareGraphHermiteRatio x) ^ hermiteResolventHalfShape m := by
        rw [← hbalance, hgsq]
        ring
      _ ≤ hermiteRawNormalizationConstant m *
          (2 : ℝ) ^ hermiteResolventHalfShape m := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (le_trans (by norm_num) hratio.1) hratio.2 hq)
          (hermiteRawNormalizationConstant_pos hm).le

/-- A uniform upper bound for the graph-to-actual trace diagonal factor. -/
def canonicalToActualTraceUpper (m : ℕ) : ℝ :=
  Real.sqrt (hermiteRawNormalizationConstant m *
    (2 : ℝ) ^ hermiteResolventHalfShape m)

/-- A strictly positive uniform lower bound for the graph-to-actual trace
diagonal factor. -/
def canonicalToActualTraceLower (m : ℕ) : ℝ :=
  Real.sqrt (hermiteDiagonalFloorConstant m)

/-- Every actual graph-to-trace diagonal factor is strictly positive. -/
theorem canonicalToActualTraceFactor_pos
    (m : ℕ) (hm : 1 ≤ m)
    (C : CanonicalClusterIndex S.signedSquareImage d) :
    0 < ho.canonicalToActualTraceFactor S m (2 * m) hm
      (ho.canonicalActualAnchor S) C :=
  mul_pos (ho.canonicalGraphWeight_pos (2 * m) (ho.canonicalActualAnchor S) C)
    (ho.signedGrouping.weight_pos m hm C)

/-- The explicit upper constant bounds every actual diagonal factor. -/
theorem canonicalToActualTraceFactor_le_upper
    (m : ℕ) (hm : 1 ≤ m)
    (C : CanonicalClusterIndex S.signedSquareImage d) :
    ho.canonicalToActualTraceFactor S m (2 * m) hm
        (ho.canonicalActualAnchor S) C ≤ canonicalToActualTraceUpper m := by
  rw [canonicalToActualTraceUpper]
  apply (Real.le_sqrt
    (ho.canonicalToActualTraceFactor_pos S m hm C).le
    (mul_nonneg (hermiteRawNormalizationConstant_pos hm).le
      (Real.rpow_nonneg (by norm_num) _))).2
  exact (ho.canonicalToActualTraceFactor_sq_bounds S m hm C).2

/-- The explicit positive lower constant bounds every actual diagonal factor
from below. -/
theorem canonicalToActualTraceLower_le_factor
    (m : ℕ) (hm : 1 ≤ m)
    (C : CanonicalClusterIndex S.signedSquareImage d) :
    canonicalToActualTraceLower m ≤
      ho.canonicalToActualTraceFactor S m (2 * m) hm
        (ho.canonicalActualAnchor S) C := by
  rw [canonicalToActualTraceLower, Real.sqrt_le_iff]
  exact ⟨(ho.canonicalToActualTraceFactor_pos S m hm C).le,
    (ho.canonicalToActualTraceFactor_sq_bounds S m hm C).1⟩

/-- The explicit trace upper constant is nonnegative. -/
theorem canonicalToActualTraceUpper_nonneg (m : ℕ) :
    0 ≤ canonicalToActualTraceUpper m := Real.sqrt_nonneg _

/-- The explicit trace lower constant is strictly positive. -/
theorem canonicalToActualTraceLower_pos (m : ℕ) :
    0 < canonicalToActualTraceLower m :=
  Real.sqrt_pos.2 (hermiteDiagonalFloorConstant_pos m)

def canonicalToActualTraceCoordinateCLM
    (m : ℕ) (hm : 1 ≤ m) (i : ho.signedGrouping.Index) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
    (ho.canonicalToActualTraceFactor S m (2 * m) hm
      (ho.canonicalActualAnchor S) i.1 : ℂ)

def canonicalToActualTraceForward
    (m : ℕ) (hm : 1 ≤ m) :
    CoefficientSpace ho.signedGrouping.Index →L[ℂ]
      CoefficientSpace ho.signedGrouping.Index :=
  lp.mapCLM 2 (ho.canonicalToActualTraceCoordinateCLM S m hm)
    (canonicalToActualTraceUpper_nonneg m) (fun i => by
      rw [canonicalToActualTraceCoordinateCLM,
        ContinuousLinearMap.norm_smulRight_apply]
      simp only [norm_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (ho.canonicalToActualTraceFactor_pos S m hm i.1)]
      exact ho.canonicalToActualTraceFactor_le_upper S m hm i.1)

def canonicalToActualTraceInverse
    (m : ℕ) (hm : 1 ≤ m) :
    CoefficientSpace ho.signedGrouping.Index →L[ℂ]
      CoefficientSpace ho.signedGrouping.Index :=
  lp.mapCLM 2
    (fun i : ho.signedGrouping.Index =>
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((ho.canonicalToActualTraceFactor S m (2 * m) hm
          (ho.canonicalActualAnchor S) i.1 : ℂ)⁻¹))
    (inv_nonneg.mpr (canonicalToActualTraceLower_pos m).le) (fun i => by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      simp only [norm_one, one_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (ho.canonicalToActualTraceFactor_pos S m hm i.1)]
      exact (inv_le_inv₀ (ho.canonicalToActualTraceFactor_pos S m hm i.1)
        (canonicalToActualTraceLower_pos m)).2
          (ho.canonicalToActualTraceLower_le_factor S m hm i.1))

@[simp] theorem canonicalToActualTraceForward_apply
    (m : ℕ) (hm : 1 ≤ m)
    (c : CoefficientSpace ho.signedGrouping.Index)
    (i : ho.signedGrouping.Index) :
    ho.canonicalToActualTraceForward S m hm c i =
      (ho.canonicalToActualTraceFactor S m (2 * m) hm
        (ho.canonicalActualAnchor S) i.1 : ℂ) * c i := by
  change c i * (ho.canonicalToActualTraceFactor S m (2 * m) hm
    (ho.canonicalActualAnchor S) i.1 : ℂ) = _
  ring

@[simp] theorem canonicalToActualTraceInverse_apply
    (m : ℕ) (hm : 1 ≤ m)
    (c : CoefficientSpace ho.signedGrouping.Index)
    (i : ho.signedGrouping.Index) :
    ho.canonicalToActualTraceInverse S m hm c i =
      (ho.canonicalToActualTraceFactor S m (2 * m) hm
        (ho.canonicalActualAnchor S) i.1 : ℂ)⁻¹ * c i := by
  change c i * (ho.canonicalToActualTraceFactor S m (2 * m) hm
    (ho.canonicalActualAnchor S) i.1 : ℂ)⁻¹ = _
  ring

/-- The exact bounded diagonal automorphism from graph-normalized samples
to the normalization of the actual grouped Hermite atoms. -/
def canonicalToActualTraceEquiv
    (m : ℕ) (hm : 1 ≤ m) :
    CoefficientSpace ho.signedGrouping.Index ≃L[ℂ]
      CoefficientSpace ho.signedGrouping.Index :=
  ContinuousLinearEquiv.equivOfInverse
    (ho.canonicalToActualTraceForward S m hm)
    (ho.canonicalToActualTraceInverse S m hm)
    (fun c => by
      apply Subtype.ext
      funext i
      simp only [canonicalToActualTraceForward_apply,
        canonicalToActualTraceInverse_apply]
      let r : ℂ := (ho.canonicalToActualTraceFactor S m (2 * m) hm
        (ho.canonicalActualAnchor S) i.1 : ℂ)
      change r⁻¹ * (r * c i) = c i
      exact inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr
        (ho.canonicalToActualTraceFactor_pos S m hm i.1).ne') _)
    (fun c => by
      apply Subtype.ext
      funext i
      simp only [canonicalToActualTraceForward_apply,
        canonicalToActualTraceInverse_apply]
      let r : ℂ := (ho.canonicalToActualTraceFactor S m (2 * m) hm
        (ho.canonicalActualAnchor S) i.1 : ℂ)
      change r * (r⁻¹ * c i) = c i
      exact mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr
        (ho.canonicalToActualTraceFactor_pos S m hm i.1).ne') _)

/-- Coordinate formula for the bounded diagonal trace equivalence. -/
@[simp] theorem canonicalToActualTraceEquiv_apply
    (m : ℕ) (hm : 1 ≤ m)
    (c : CoefficientSpace ho.signedGrouping.Index)
    (i : ho.signedGrouping.Index) :
    ho.canonicalToActualTraceEquiv S m hm c i =
      (ho.canonicalToActualTraceFactor S m (2 * m) hm
        (ho.canonicalActualAnchor S) i.1 : ℂ) * c i := by
  exact ho.canonicalToActualTraceForward_apply S m hm c i

private theorem coefficientAtom_apply {iota : Type*} [DecidableEq iota]
    (i j : iota) :
    (coefficientAtom i : CoefficientSpace iota) j = if j = i then 1 else 0 := by
  change (coefficientHilbertBasis iota).repr (coefficientAtom i) j = _
  rw [(coefficientHilbertBasis iota).repr_apply_apply]
  unfold coefficientAtom
  exact orthonormal_iff_ite.mp (coefficientHilbertBasis iota).orthonormal j i

/-- The diagonal trace equivalence scales each canonical coefficient atom by
its exact graph-to-actual trace factor. -/
theorem canonicalToActualTraceEquiv_coefficientAtom
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (i : ho.signedGrouping.Index) :
    ho.canonicalToActualTraceEquiv S m hm (coefficientAtom i) =
      (ho.canonicalToActualTraceFactor S m (2 * m) hm
        (ho.canonicalActualAnchor S) i.1 : ℂ) • coefficientAtom i := by
  apply Subtype.ext
  funext j
  rw [ho.canonicalToActualTraceEquiv_apply S m hm]
  change (ho.canonicalToActualTraceFactor S m (2 * m) hm
      (ho.canonicalActualAnchor S) j.1 : ℂ) * (coefficientAtom i) j =
    (ho.canonicalToActualTraceFactor S m (2 * m) hm
      (ho.canonicalActualAnchor S) i.1 : ℂ) * (coefficientAtom i) j
  by_cases hji : j = i
  · subst j
    rfl
  · rw [coefficientAtom_apply i j]
    simp [hji]

private def hermiteScaleDistributionEvalCLM
    (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    HermiteScale (-(m : ℤ)) →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ f).comp
    (hermiteScaleDistributionCLM m)

private def actualGroupedSynthesisPairingCLM
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (f : SchwartzMap ℝ ℂ) :
    CoefficientSpace ho.signedGrouping.Index →L[ℂ] ℂ :=
  (hermiteScaleDistributionEvalCLM m f).comp
    ((ho.actualGroupedBesselAnalysis hd m hmB).synthesis.comp
      (ho.canonicalToActualTraceEquiv S m hm).toContinuousLinearMap)

private theorem inner_star_coefficientAtom_eq_apply
    {iota : Type*} [DecidableEq iota]
    (x : CoefficientSpace iota) (i : iota) :
    inner ℂ (star x) (coefficientAtom i) = x i := by
  have hrepr := (coefficientHilbertBasis iota).repr_apply_apply (star x) i
  calc
    inner ℂ (star x) (coefficientAtom i) =
        star (inner ℂ (coefficientAtom i) (star x)) := by
          exact (inner_conj_symm (star x) (coefficientAtom i)).symm
    _ = star ((star x) i) := congrArg star hrepr.symm
    _ = x i := by
      change star (star (x i)) = x i
      rw [star_star]

/-- A canonical scalar sample on an embedded Schwartz test is exactly the
actual grouped atom action after the explicit diagonal normalization. -/
theorem canonicalPhysicalSampler_schwartzEmbedding_eq_actualAtom
    (m k : ℕ) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k (by omega) anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k (by omega) anchor v ≤ A * ‖v‖ ^ 2)
    (C : CanonicalClusterIndex S.signedSquareImage d)
    (j : Fin (ho.clusterSize C)) (f : SchwartzMap ℝ ℂ) :
    ho.canonicalGraphDataCoefficientEquiv
        (ho.canonicalPhysicalSampler S k (by omega) anchor A hA hsummable hbound
          (KNSGraphSpace.schwartzEmbedding k f)) ⟨C, j⟩ =
      (ho.canonicalToActualTraceFactor S m k hm anchor C : ℂ) *
        hermiteScaleDistribution m (ho.signedGrouping.atom m hm
          ⟨C, Fin.cast (show ho.signedGrouping.size C = ho.clusterSize C from rfl) j⟩) f := by
  rw [ho.canonicalGraphDataCoefficientEquiv_apply]
  rw [ho.canonicalPhysicalSampler_apply_coord]
  rw [KNSGraphSpace.representative_schwartzEmbedding hk]
  rw [ho.signedGrouping.atom_distribution_apply]
  unfold canonicalToActualTraceFactor
  have hweight : ho.signedGrouping.weight m hm C ≠ 0 :=
    ne_of_gt (ho.signedGrouping.weight_pos m hm C)
  have hweightC : ((ho.signedGrouping.weight m hm C : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hweight
  have hpref :
      ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap (f : ℝ → ℂ)) C j =
        dividedDifferences (ho.signedGrouping.nodes C)
          (ho.signedGrouping.nodes_injective C)
          (fun i => f (ho.signedGrouping.point C i))
          (Fin.cast (show ho.signedGrouping.size C = ho.clusterSize C from rfl) j) := by
    rw [BoundedClusterOrder.canonicalPrefixData,
      analyticDividedDifference_eq_dividedDifferences
        (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective]
    congr 1
    · funext i
      change (ho.realClusterNode C i : ℂ) =
        (ho.signedGrouping.realNodes C i : ℂ)
      exact_mod_cast (ho.signedGrouping_realNodes C i).symm
    · funext i
      exact S.physicalSignedSquarePullbackMap_on_carrier
        (f : ℝ → ℂ) (ho.orderedClusterNode C i)
  rw [hpref]
  push_cast
  field_simp [hweightC]

/-- The same exact coordinate adapter for the unconditional sampler. -/
theorem canonicalPhysicalSamplerBounded_schwartzEmbedding_eq_actualAtom
    (m k : ℕ) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (C : CanonicalClusterIndex S.signedSquareImage d)
    (j : Fin (ho.clusterSize C)) (f : SchwartzMap ℝ ℂ) :
    ho.canonicalGraphDataCoefficientEquiv
        (ho.canonicalPhysicalSamplerBounded S hd hq anchor
          (KNSGraphSpace.schwartzEmbedding k f)) ⟨C, j⟩ =
      (ho.canonicalToActualTraceFactor S m k hm anchor C : ℂ) *
        hermiteScaleDistribution m (ho.signedGrouping.atom m hm
          ⟨C, Fin.cast (show ho.signedGrouping.size C = ho.clusterSize C from rfl) j⟩) f := by
  rw [ho.canonicalGraphDataCoefficientEquiv_apply]
  rw [ho.canonicalPhysicalSamplerBounded_apply_coord]
  rw [KNSGraphSpace.representative_schwartzEmbedding hk]
  rw [ho.signedGrouping.atom_distribution_apply]
  unfold canonicalToActualTraceFactor
  have hweight : ho.signedGrouping.weight m hm C ≠ 0 :=
    ne_of_gt (ho.signedGrouping.weight_pos m hm C)
  have hweightC : ((ho.signedGrouping.weight m hm C : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hweight
  have hpref :
      ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap (f : ℝ → ℂ)) C j =
        dividedDifferences (ho.signedGrouping.nodes C)
          (ho.signedGrouping.nodes_injective C)
          (fun i => f (ho.signedGrouping.point C i))
          (Fin.cast (show ho.signedGrouping.size C = ho.clusterSize C from rfl) j) := by
    rw [BoundedClusterOrder.canonicalPrefixData,
      analyticDividedDifference_eq_dividedDifferences
        (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective]
    congr 1
    · funext i
      change (ho.realClusterNode C i : ℂ) =
        (ho.signedGrouping.realNodes C i : ℂ)
      exact_mod_cast (ho.signedGrouping_realNodes C i).symm
    · funext i
      exact S.physicalSignedSquarePullbackMap_on_carrier
        (f : ℝ → ℂ) (ho.orderedClusterNode C i)
  rw [hpref]
  push_cast
  field_simp [hweightC]

private def canonicalSamplerPairingCLM
    (m : ℕ) (hd : 0 < d) (hq : q + 1 ≤ 2 * m)
    (f : SchwartzMap ℝ ℂ) :
    CoefficientSpace ho.signedGrouping.Index →L[ℂ] ℂ :=
  (innerSL ℂ) (star
    (ho.canonicalPhysicalScalarSamplerBounded hd hq
      (ho.canonicalActualAnchor S)
      (KNSGraphSpace.schwartzEmbedding (2 * m) f)))

private theorem actualGroupedSynthesisPairingCLM_eq_canonicalSamplerPairingCLM
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (hq : q + 1 ≤ 2 * m) (f : SchwartzMap ℝ ℂ) :
    ho.actualGroupedSynthesisPairingCLM S m hm hd hmB f =
      ho.canonicalSamplerPairingCLM S m hd hq f := by
  apply ContinuousLinearMap.ext_on
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact coefficientAtom_dense_span
  · rintro _ ⟨i, rfl⟩
    change hermiteScaleDistribution m
        ((ho.actualGroupedBesselAnalysis hd m hmB).synthesis
          (ho.canonicalToActualTraceEquiv S m hm (coefficientAtom i))) f =
      inner ℂ
        (star (ho.canonicalPhysicalScalarSamplerBounded hd hq
          (ho.canonicalActualAnchor S)
          (KNSGraphSpace.schwartzEmbedding (2 * m) f))) (coefficientAtom i)
    rw [ho.canonicalToActualTraceEquiv_coefficientAtom S m hm i,
      map_smul, BesselAnalysis.synthesis_coefficientAtom]
    rw [← hermiteScaleDistributionCLM_apply]
    simp only [map_smul, hermiteScaleDistributionCLM_apply, smul_apply,
      smul_eq_mul]
    rw [inner_star_coefficientAtom_eq_apply]
    rcases i with ⟨C, j⟩
    symm
    exact ho.canonicalPhysicalSamplerBounded_schwartzEmbedding_eq_actualAtom
      S m (2 * m) hm (by omega) hd hq (ho.canonicalActualAnchor S) C j f

/-- All-coefficient synthesis pairing for the actual grouped Bessel family,
after the exact diagonal normalization of canonical graph samples. -/
theorem actualGroupedSynthesis_canonicalToActualTraceEquiv_pairing
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (hq : q + 1 ≤ 2 * m)
    (c : CoefficientSpace ho.signedGrouping.Index) (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution m
        ((ho.actualGroupedBesselAnalysis hd m hmB).synthesis
          (ho.canonicalToActualTraceEquiv S m hm c)) f =
      inner ℂ
        (star (ho.canonicalPhysicalScalarSamplerBounded hd hq
          (ho.canonicalActualAnchor S)
          (KNSGraphSpace.schwartzEmbedding (2 * m) f))) c := by
  have h := congrArg (fun T :
      CoefficientSpace ho.signedGrouping.Index →L[ℂ] ℂ => T c)
    (ho.actualGroupedSynthesisPairingCLM_eq_canonicalSamplerPairingCLM
      S m hm hd hmB hq f)
  exact h

/-- The block sampler expressed on the exact scalar coordinate space used by
the actual grouped Hermite synthesis. -/
def canonicalPhysicalScalarSampler
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2) :
    KNSGraphSpace k →L[ℂ] CoefficientSpace ho.signedGrouping.Index :=
  ho.canonicalGraphDataCoefficientEquiv.toLinearIsometry.toContinuousLinearMap.comp
    (ho.canonicalPhysicalSampler S k hk anchor A hA hsummable hbound)

/-- The conditional scalar sampler is exactly graph sampling followed by the
canonical graph-data coefficient equivalence. -/
@[simp] theorem canonicalPhysicalScalarSampler_apply
    (k : ℕ) (hk : 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (A : ℝ) (hA : 0 ≤ A)
    (hsummable : ∀ v : KNSGraphSpace k,
      Summable (ho.canonicalPhysicalPrefixBlockEnergy S k hk anchor v))
    (hbound : ∀ v : KNSGraphSpace k,
      ho.canonicalPhysicalPrefixRealEnergy S k hk anchor v ≤ A * ‖v‖ ^ 2)
    (v : KNSGraphSpace k) :
    ho.canonicalPhysicalScalarSampler S k hk anchor A hA hsummable hbound v =
      ho.canonicalGraphDataCoefficientEquiv
        (ho.canonicalPhysicalSampler S k hk anchor A hA hsummable hbound v) := rfl

end BoundedClusterOrder

end

end MeyerGeneralProblem
