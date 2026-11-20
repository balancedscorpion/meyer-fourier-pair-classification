module

public import MeyerGeneralProblem.Interpolation.CanonicalBlockSelection
public import MeyerGeneralProblem.Interpolation.PhysicalBlockGluing

@[expose] public section

/-!
# Actual weighted exterior interpolation from canonical grouped data

Uniform source block counts construct the local polynomial family. Its
genuine derivative estimates, the locally finite physical ray sum, and the
exact five-window weighted reindexing give a global exterior energy bound.
No interpolation or energy certificate is supplied as an assumption.
The source-dependent tail start remains explicit; central gluing is separate.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

attribute [local instance] Classical.propDecidable

/-- The actual nonnegative weighted value plus derivative energy of a
physical function. Infinite energies are retained rather than defaulted to zero. -/
def physicalInterpolationEnergy (k : ℕ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 * k)) * ENNReal.ofReal (‖f x‖ ^ 2)) +
    ∫⁻ x : ℝ, ENNReal.ofReal (‖iteratedDeriv k f x‖ ^ 2)

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (horder : BoundedClusterOrder S d q)

/-- The canonical weighted grouped coefficient energy at physical order k.
Each anchor is an actual node, and every original prefix is counted once. -/
def canonicalWeightedDataEnergy (k : ℕ)
    (anchor : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C))
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) : ℝ≥0∞ :=
  ∑' C : CanonicalClusterIndex S d,
    ENNReal.ofReal ((1 + Real.sqrt |horder.realClusterNode C (anchor C)|) ^ (2 * k - 1)) *
      ENNReal.ofReal (∑ j, ‖data C j‖ ^ 2)

/-- Actual original-prefix data of an arbitrary function at the distinct
canonical nodes. No regularity is needed for these finite value coordinates. -/
def canonicalPrefixData (g : ℝ → ℂ) (C : CanonicalClusterIndex S d)
    (j : Fin (horder.clusterSize C)) : ℂ :=
  analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j g

/-- Squaring the genuine local derivative bound preserves exactly the
local coefficient energy; its common constant factors out of the global sum. -/
theorem tsum_canonicalBlock_sqrtEnergy_sq (B : ℝ) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (k : ℕ) (A : ℝ)
    (data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ) :
    (∑' b : ℕ, if 3 ≤ b then
      ENNReal.ofReal ((((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
        (A * Real.sqrt (horder.canonicalBlockDataEnergy B hε b data)) ^ 2) else 0) =
      ENNReal.ofReal (A ^ 2) * ∑' b : ℕ, if 3 ≤ b then
        ENNReal.ofReal (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
          ENNReal.ofReal (horder.canonicalBlockDataEnergy B hε b data) else 0 := by
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  by_cases hb : 3 ≤ b
  · simp only [hb, ite_true]
    rw [mul_pow, Real.sq_sqrt (horder.canonicalBlockDataEnergy_nonneg B hε b data)]
    have heq : (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
        (A ^ 2 * horder.canonicalBlockDataEnergy B hε b data) =
        A ^ 2 * ((((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
          horder.canonicalBlockDataEnergy B hε b data) := by ring
    rw [heq, ENNReal.ofReal_mul (sq_nonneg A),
      ENNReal.ofReal_mul' (horder.canonicalBlockDataEnergy_nonneg B hε b data)]
  · simp [hb]

end BoundedClusterOrder

/-- Every active local cutoff lies strictly inside its actual triple
window, including the two enlarged cutoff endpoints. -/
theorem blockCutoff_ne_zero_mem_tripleBlock {B : ℝ} (hB : 0 < B)
    (b : ℕ) {s : ℝ} (hs : blockCutoff B b s ≠ 0) : s ∈ tripleBlockWindow B b := by
  have h := support_blockCutoff_subset hB b hs
  change ((b : ℝ) - 1) * B ≤ s ∧ s < ((b : ℝ) + 2) * B
  constructor <;> nlinarith [h.1, h.2]

/-- The actual source-dependent tail transition equals one on its precise
plateau. This is the exterior region, not the central transition strip. -/
theorem blockTransition_eq_one_of_plateau {B : ℝ} (hB : 0 < B)
    (start : ℕ) {s : ℝ} (hs : ((start : ℝ) + 1 / 8) * B ≤ s) :
    blockTransition B start s = 1 := by
  apply unitBlockTransition_one
  have hd : (start : ℝ) + 1 / 8 ≤ s / B := (le_div_iff₀ hB).mpr hs
  linarith

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (horder : BoundedClusterOrder S d q)

/-- Actual canonical prefix matching yields physical carrier-point
interpolation with the exact tail transition still visible. -/
theorem physicalRayBlockTail_eq_on_carrier {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (g : ℝ → ℂ) (h : ℕ → ℝ → ℂ)
    (hprefix : ∀ b : ℕ, start ≤ b → ∀ C : CanonicalClusterIndex S d,
      groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b →
      ∀ i : Fin (horder.clusterSize C),
        analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
          (fun s => h b (ε * s)) = horder.canonicalPrefixData g C i)
    (x : ℝ) (hx : 0 < ε * x) (hmem : ε * x ^ 2 ∈ S.carrier) :
    physicalRayBlockTail B start ε h x = blockTransition B start (x ^ 2) • g (ε * x ^ 2) := by
  have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hdouble : ε * (ε * x ^ 2) = x ^ 2 := by
    calc
      _ = ε ^ 2 * x ^ 2 := by ring
      _ = _ := by rw [hεsq, one_mul]
  rw [physicalRayBlockTail_eq_of_active_values B start hstart ε h x (g (ε * x ^ 2))]
  · rw [smul_smul, unitBlockTransition_mul_squareTransition hB hstart hεsq hx]
  · intro b hb hcut
    have ht : (⟨ε * x ^ 2, hmem⟩ : S.subtype) ∈ orientedTripleBlockPoints S B ε b := by
      change ε * (ε * x ^ 2) ∈ tripleBlockWindow B b
      rw [hdouble]
      exact blockCutoff_ne_zero_mem_tripleBlock (by linarith) b hcut
    have hv := horder.allTouching_values_of_prefix_eq B ε b g (h b)
      (hprefix b hb) ⟨ε * x ^ 2, hmem⟩ ht
    simpa only [hdouble] using hv

/-- On the plateau of the actual tail, the physical pullback agrees with
the original carrier function at every canonical node. -/
theorem physicalRayBlockTail_pullback_value {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (g : ℝ → ℂ) (h : ℕ → ℝ → ℂ)
    (hprefix : ∀ b : ℕ, start ≤ b → ∀ C : CanonicalClusterIndex S d,
      groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b →
      ∀ i : Fin (horder.clusterSize C),
        analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
          (fun s => h b (ε * s)) = horder.canonicalPrefixData g C i)
    {s : ℝ} (hs : s ∈ S.carrier) (hfar : ((start : ℝ) + 1 / 8) * B ≤ ε * s) :
    physicalRayBlockTail B start ε h (ε * Real.sqrt (ε * s)) = g s := by
  have hBpos : 0 < B := by linarith
  have hpos : 0 < ε * s := lt_of_lt_of_le (by positivity) hfar
  have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hdouble (t : ℝ) : ε * (ε * t) = t := by
    calc
      _ = ε ^ 2 * t := by ring
      _ = _ := by rw [hεsq, one_mul]
  have hxsq : (ε * Real.sqrt (ε * s)) ^ 2 = ε * s := by
    rw [mul_pow, hεsq, one_mul, Real.sq_sqrt hpos.le]
  have he := horder.physicalRayBlockTail_eq_on_carrier hB start hstart hε g h hprefix
    (ε * Real.sqrt (ε * s)) (by rw [hdouble]; exact Real.sqrt_pos.mpr hpos)
    (by rw [hxsq, hdouble]; exact hs)
  rw [hxsq, hdouble, blockTransition_eq_one_of_plateau hBpos start hfar, one_smul] at he
  exact he

/-- Full canonical prefixes are preserved by the actual physical
interpolant on every cluster wholly beyond the tail plateau. This is proved
from point values using the genuine finite values-to-Newton equivalence. -/
theorem physicalRayBlockTail_pullback_prefix {B : ℝ} (hB : 1 ≤ B)
    (start : ℕ) (hstart : 3 ≤ start) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (g : ℝ → ℂ) (h : ℕ → ℝ → ℂ)
    (hprefix : ∀ b : ℕ, start ≤ b → ∀ C : CanonicalClusterIndex S d,
      groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b →
      ∀ i : Fin (horder.clusterSize C),
        analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
          (fun s => h b (ε * s)) = horder.canonicalPrefixData g C i)
    (C : CanonicalClusterIndex S d)
    (hfar : ∀ i, ((start : ℝ) + 1 / 8) * B ≤ ε * horder.realClusterNode C i)
    (j : Fin (horder.clusterSize C)) :
    analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j
      (fun s => physicalRayBlockTail B start ε h (ε * Real.sqrt (ε * s))) =
        horder.canonicalPrefixData g C j := by
  have hv : (fun i => physicalRayBlockTail B start ε h
      (ε * Real.sqrt (ε * horder.realClusterNode C i))) =
      (fun i => g (horder.realClusterNode C i)) := by
    funext i
    exact horder.physicalRayBlockTail_pullback_value hB start hstart hε g h hprefix
      (horder.realClusterNode_mem C i) (hfar i)
  simp only [canonicalPrefixData, analyticDividedDifference_eq_dividedDifferences
    (horder.realClusterNode C) (horder.realClusterNode_strictMono C).injective]
  rw [hv]

end BoundedClusterOrder

/-- Actual canonical data construct a smooth one-ray exterior function
with global weighted energy. Constants precede the carrier, source threshold,
tail start, ray, anchor choices, and data. No global summability is assumed. -/
theorem exists_uniform_canonicalExterior_interpolant (N q k : ℕ) (hk : 1 ≤ k)
    {B d : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ S : LocallyFiniteCarrier,
      ∀ horder : BoundedClusterOrder S d q, ∀ ε : ℝ, ∀ _hε : ε = 1 ∨ ε = -1,
      ∀ b₀ : ℤ,
      (∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S B ε j).ncard ≤ N) →
      ∀ start : ℕ, 3 ≤ start → b₀ + 1 ≤ (start : ℤ) →
      ∀ anchor : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C),
      ∀ data : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C) → ℂ,
        ∃ h : ℕ → ℝ → ℂ, (∀ b, ContDiff ℝ ∞ (h b)) ∧
          (∀ b : ℕ, start ≤ b → ∀ C : CanonicalClusterIndex S d,
            groupTouchesTripleBlock B (range (fun i => ε * horder.realClusterNode C i)) b →
            ∀ i : Fin (horder.clusterSize C),
              analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) i
                (fun s => h b (ε * s)) = data C i) ∧
          let f := physicalRayBlockTail B start ε h
          ContDiff ℝ ∞ f ∧ (∀ x : ℝ, ε * x ≤ 0 → f x = 0) ∧
            physicalInterpolationEnergy k f ≤
              ENNReal.ofReal K * horder.canonicalWeightedDataEnergy k anchor data := by
  have hBpos : 0 < B := by linarith
  obtain ⟨A, hA, hfamily⟩ := exists_uniform_allTouching_interpolation_family N q k hB hd hdiam
  obtain ⟨R, hR, hray⟩ := exists_uniform_exteriorRayBlockSum_lintegral_bound k
  let K : ℝ := (3 * R * B) * (A ^ 2 * (5 * (3 : ℝ) ^ ((k : ℝ) - 1 / 2)))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro S horder ε hε b₀ hcount start hstart hstart₀ anchor data
  obtain ⟨h, hsmooth, _hzero, hproperties⟩ := hfamily S horder ε hε b₀ hcount data
  have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hactive (b : ℕ) (hb : start ≤ b) : b₀ + 1 ≤ (b : ℤ) ∧ 2 ≤ b := by
    have hb' : (start : ℤ) ≤ b := by exact_mod_cast hb
    exact ⟨hstart₀.trans hb', by omega⟩
  have hlocal : ∀ b : ℕ, 3 ≤ b →
      ∀ x ∈ Icc ((b : ℝ) * B - B / 8) (((b : ℝ) + 1) * B + B / 8),
        ∀ j ≤ k, ‖iteratedDeriv j (tailBlockFunctions start h b) x‖ ≤
          A * Real.sqrt (horder.canonicalBlockDataEnergy B hε b data) := by
    intro b _hb3 x hx j hj
    by_cases hb : start ≤ b
    · simpa only [tailBlockFunctions, hb, ite_true] using
        (hproperties b (hactive b hb).1 (hactive b hb).2).2.1 x hx j hj
    · simpa only [tailBlockFunctions, hb, ite_false, iteratedDeriv_const, ite_self, norm_zero] using
        (mul_nonneg hA.le (Real.sqrt_nonneg (horder.canonicalBlockDataEnergy B hε b data)))
  have he := hray B hB ε hεsq (tailBlockFunctions start h)
    (fun b => contDiff_tailBlockFunctions start b h (hsmooth b))
    (fun b => A * Real.sqrt (horder.canonicalBlockDataEnergy B hε b data))
    (fun b => mul_nonneg hA.le (Real.sqrt_nonneg _)) hlocal
  refine ⟨h, hsmooth, ?_, contDiff_physicalRayBlockTail hBpos start ε h hsmooth, ?_, ?_⟩
  · intro b hb
    exact (hproperties b (hactive b hb).1 (hactive b hb).2).1
  · intro x hx
    exact physicalRayBlockTail_eq_zero_of_nonpos hB start hεsq h hx
  · have hweight := horder.tsum_canonicalBlockDataEnergy_weighted_le hBpos hd hdiam hε k hk anchor data
    have hKcast : ENNReal.ofReal K = ENNReal.ofReal (3 * R * B) *
        (ENNReal.ofReal (A ^ 2) * (5 * ENNReal.ofReal ((3 : ℝ) ^ ((k : ℝ) - 1 / 2)))) := by
      dsimp [K]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 3 * R * B),
        ENNReal.ofReal_mul (sq_nonneg A), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    calc
      _ ≤ ENNReal.ofReal (3 * R * B) *
          (ENNReal.ofReal (A ^ 2) * ∑' b : ℕ, if 3 ≤ b then
            ENNReal.ofReal (((b : ℝ) * B) ^ ((k : ℝ) - 1 / 2)) *
              ENNReal.ofReal (horder.canonicalBlockDataEnergy B hε b data) else 0) := by
        simpa only [physicalInterpolationEnergy, physicalRayBlockTail,
          horder.tsum_canonicalBlock_sqrtEnergy_sq B hε k A data] using he
      _ ≤ ENNReal.ofReal (3 * R * B) *
          (ENNReal.ofReal (A ^ 2) * (5 * ENNReal.ofReal ((3 : ℝ) ^ ((k : ℝ) - 1 / 2)) *
            horder.canonicalWeightedDataEnergy k anchor data)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hweight)
      _ = _ := by rw [hKcast]; simp only [mul_assoc]

/-- A finite bound for the genuine nonnegative physical energy proves
ordinary integrability and the corresponding real integral inequality.
Neither integrability nor a desired Sobolev estimate is an input. -/
theorem integrable_and_real_energy_le_of_physicalInterpolationEnergy_le
    (k : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) {A : ℝ} (hA : 0 ≤ A)
    {E : ℝ≥0∞} (hE : E ≠ ⊤)
    (hbound : physicalInterpolationEnergy k f ≤ ENNReal.ofReal A * E) :
    Integrable (fun x : ℝ => |x| ^ (2 * k) * ‖f x‖ ^ 2) ∧
    Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2) ∧
    (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) +
        (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤ A * E.toReal := by
  have hu : ENNReal.ofReal A * E < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hE)
  have hfinite := lt_of_le_of_lt hbound hu
  have hvalue : (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 * k) * ‖f x‖ ^ 2)) =
      ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 * k)) * ENNReal.ofReal (‖f x‖ ^ 2) := by
    apply lintegral_congr
    intro x
    exact ENNReal.ofReal_mul (by positivity)
  change (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 * k)) * ENNReal.ofReal (‖f x‖ ^ 2)) +
    (∫⁻ x : ℝ, ENNReal.ofReal (‖iteratedDeriv k f x‖ ^ 2)) < ⊤ at hfinite
  rw [← hvalue] at hfinite
  obtain ⟨hvfinite, hdfinite⟩ := ENNReal.add_lt_top.mp hfinite
  have hvcont : Continuous (fun x : ℝ => |x| ^ (2 * k) * ‖f x‖ ^ 2) :=
    (continuous_abs.pow _).mul (hf.continuous.norm.pow _)
  have hdcont : Continuous (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2) :=
    ((hf.of_le (by simp)).continuous_iteratedDeriv' k).norm.pow _
  have hvnonneg : ∀ x : ℝ, 0 ≤ |x| ^ (2 * k) * ‖f x‖ ^ 2 := fun x => by positivity
  have hdnonneg : ∀ x : ℝ, 0 ≤ ‖iteratedDeriv k f x‖ ^ 2 := fun x => sq_nonneg _
  refine ⟨⟨hvcont.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hvnonneg)).mpr hvfinite⟩,
    ⟨hdcont.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hdnonneg)).mpr hdfinite⟩, ?_⟩
  have hleft : (physicalInterpolationEnergy k f).toReal =
      (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) +
        (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) := by
    rw [physicalInterpolationEnergy, ← hvalue, ENNReal.toReal_add hvfinite.ne hdfinite.ne,
      ← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hvnonneg) hvcont.aestronglyMeasurable,
      ← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hdnonneg) hdcont.aestronglyMeasurable]
  have hm := ENNReal.toReal_mono hu.ne hbound
  simpa only [hleft, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] using hm

/-- Function-derived canonical data give an actual smooth exterior
interpolant with the global weighted energy bound, exact physical carrier
values on the plateau, and every original prefix on full exterior clusters.
Finite data energy additionally gives real integrability and the real bound. -/
theorem exists_uniform_canonicalExterior_function (N q k : ℕ) (hk : 1 ≤ k)
    {B d : ℝ} (hB : 1 ≤ B) (hd : 0 < d) (hdiam : (q : ℝ) * d ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ S : LocallyFiniteCarrier,
      ∀ horder : BoundedClusterOrder S d q, ∀ ε : ℝ, ∀ _hε : ε = 1 ∨ ε = -1,
      ∀ b₀ : ℤ,
      (∀ j : ℤ, b₀ ≤ j → (orientedBlockPoints S B ε j).ncard ≤ N) →
      ∀ start : ℕ, 3 ≤ start → b₀ + 1 ≤ (start : ℤ) →
      ∀ anchor : (C : CanonicalClusterIndex S d) → Fin (horder.clusterSize C),
      ∀ g : ℝ → ℂ,
        ∃ h : ℕ → ℝ → ℂ, (∀ b, ContDiff ℝ ∞ (h b)) ∧
          let f := physicalRayBlockTail B start ε h
          let E := horder.canonicalWeightedDataEnergy k anchor (horder.canonicalPrefixData g)
          ContDiff ℝ ∞ f ∧ (∀ x : ℝ, ε * x ≤ 0 → f x = 0) ∧
          physicalInterpolationEnergy k f ≤ ENNReal.ofReal K * E ∧
          (∀ x : ℝ, 0 < ε * x → ε * x ^ 2 ∈ S.carrier →
            f x = blockTransition B start (x ^ 2) • g (ε * x ^ 2)) ∧
          (∀ s ∈ S.carrier, ((start : ℝ) + 1 / 8) * B ≤ ε * s →
            f (ε * Real.sqrt (ε * s)) = g s) ∧
          (∀ C : CanonicalClusterIndex S d,
            (∀ i, ((start : ℝ) + 1 / 8) * B ≤ ε * horder.realClusterNode C i) →
            ∀ j : Fin (horder.clusterSize C),
              analyticDividedDifference (finiteNodeSequence (horder.realClusterNode C)) j
                (fun s => f (ε * Real.sqrt (ε * s))) = horder.canonicalPrefixData g C j) ∧
          (E ≠ ⊤ →
            Integrable (fun x : ℝ => |x| ^ (2 * k) * ‖f x‖ ^ 2) ∧
            Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2) ∧
            (∫ x : ℝ, |x| ^ (2 * k) * ‖f x‖ ^ 2) +
                (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤ K * E.toReal) := by
  obtain ⟨K, hK, hbuild⟩ := exists_uniform_canonicalExterior_interpolant N q k hk hB hd hdiam
  refine ⟨K, hK, ?_⟩
  intro S horder ε hε b₀ hcount start hstart hstart₀ anchor g
  obtain ⟨h, hs, hp, hf, hz, he⟩ := hbuild S horder ε hε b₀ hcount start hstart hstart₀
    anchor (horder.canonicalPrefixData g)
  refine ⟨h, hs, hf, hz, he, ?_, ?_, ?_, ?_⟩
  · exact horder.physicalRayBlockTail_eq_on_carrier hB start hstart hε g h hp
  · exact fun s hs hfar => horder.physicalRayBlockTail_pullback_value hB start hstart hε g h hp hs hfar
  · exact horder.physicalRayBlockTail_pullback_prefix hB start hstart hε g h hp
  · intro hE
    exact integrable_and_real_energy_le_of_physicalInterpolationEnergy_le k _ hf hK.le hE he

end

end MeyerGeneralProblem
