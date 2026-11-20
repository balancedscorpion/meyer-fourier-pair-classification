module

public import MeyerGeneralProblem.Gram.UniversalOperator
public import MeyerGeneralProblem.Gram.UniversalDecay
public import MeyerGeneralProblem.Carrier.HermiteSynthesis
public import MeyerGeneralProblem.Sampling.CarrierIngham
public import MeyerGeneralProblem.Sampling.SeparatedDecay
public import MeyerGeneralProblem.Cross.CompactRemainder

@[expose] public section

/-!
# Strict-subcritical carrier universal tail model

Strict subcriticality selects a finite deletion, a separated signed-square
tail, and a cosine-window parameter.  The universal operator on that infinite
tail is bounded, has the expected kernel entries, and has a positive Loewner
floor.
-/

namespace MeyerGeneralProblem

open ComplexConjugate
open Filter

noncomputable section

/-- Concrete strict-subcritical tail data used by the universal Gram model. -/
structure CarrierUniversalTailData (Λ : TwoSidedCarrier) where
  /-- Signed-square separation constant on the tail. -/
  d : ℝ
  hd : 1 < d
  /-- Finite set deleted to obtain signed-square separation. -/
  F : Finset ℤ
  separated : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
    d ≤ |signedSquare (Λ i) - signedSquare (Λ j)|
  /-- Tail points lie outside the fixed physical central interval. -/
  outside : ∀ i, i ∉ F → 1 < (Λ i) ^ 2
  /-- Cosine-window half-width used for the lower Gram estimate. -/
  a : ℝ
  ha : 0 < a
  had : 1 < 2 * a * d
  ha_lt_half : a < 1 / 2

/-- Strict subcriticality supplies all parameters of the infinite universal
tail Gram model. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_universalTailData
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    Nonempty (CarrierUniversalTailData Λ) := by
  rcases strictSubcritical_exists_separated_ingham_window hΛ with
    ⟨d, hd, F₀, hsep₀, a, ha, hleft, halt, hfloor⟩
  have had : 1 < 2 * a * d := by
    have hden : 0 < 2 * d := by positivity
    have hmul := (div_lt_iff₀ hden).mp hleft
    nlinarith
  let F : Finset ℤ :=
    F₀ ∪ (Λ.finite_indices_in_Icc (-1) 1).toFinset
  have hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      d ≤ |signedSquare (Λ i) - signedSquare (Λ j)| := by
    intro i j hi hj hij
    apply hsep₀ i j
    · exact fun hiF₀ ↦ hi (Finset.mem_union_left _ hiF₀)
    · exact fun hjF₀ ↦ hj (Finset.mem_union_left _ hjF₀)
    · exact hij
  have houtside : ∀ i, i ∉ F → 1 < (Λ i) ^ 2 := by
    intro i hi
    have hiInterval : Λ i ∉ Set.Icc (-1 : ℝ) 1 := by
      intro hiIcc
      apply hi
      apply Finset.mem_union_right F₀
      exact (Λ.finite_indices_in_Icc (-1) 1).mem_toFinset.mpr hiIcc
    have habs : 1 < |Λ i| := by
      apply lt_of_not_ge
      intro hle
      exact hiInterval (abs_le.mp hle)
    nlinarith [sq_abs (Λ i)]
  exact ⟨⟨d, hd, F, hsep, houtside, a, ha, had, halt⟩⟩

/-- A chosen concrete set of universal tail parameters. -/
noncomputable def TwoSidedCarrier.StrictSubcritical.universalTailData
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    CarrierUniversalTailData Λ :=
  Classical.choice hΛ.exists_universalTailData

namespace CarrierUniversalTailData

variable {Λ : TwoSidedCarrier} (D : CarrierUniversalTailData Λ)

/-- Signed-square frequencies on the separated carrier tail. -/
def frequency (j : {j : ℤ // j ∉ D.F}) : ℝ :=
  signedSquare (Λ j)

theorem frequency_separated (i j : {j : ℤ // j ∉ D.F}) (hij : i ≠ j) :
    D.d ≤ |D.frequency i - D.frequency j| := by
  apply D.separated
  · exact i.property
  · exact j.property
  · exact Subtype.coe_injective.ne hij

/-- Every row of the universal tail kernel is absolutely summable, by its
quadratic Fourier decay and the separated signed-square geometry. -/
theorem summable_norm_universalGramKernel_row
    (m : ℕ) (hm : 1 ≤ m)
    (i : {j : ℤ // j ∉ D.F}) :
    Summable (fun j : {j : ℤ // j ∉ D.F} =>
      ‖universalGramKernel m (D.frequency j - D.frequency i)‖) := by
  have henv := summable_inverseSquareDistance_of_separated
    D.frequency D.hd D.frequency_separated (D.frequency i)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => norm_universalGramKernel_le_inv_sq hm
      (D.frequency j - D.frequency i))
  simpa only [div_eq_mul_inv, one_div, one_mul] using
    henv.mul_left (universalGramDecayConstant m)

/-- The universal tail kernel has uniformly small finite row sums beyond one
signed-square distance cutoff. -/
theorem exists_uniform_sum_norm_universalGramKernel_tail
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ ε > 0, ∃ L ≥ 0,
      ∀ (i : {j : ℤ // j ∉ D.F})
        (U : Finset {j : ℤ // j ∉ D.F}),
        ∑ j ∈ U with L < |D.frequency j - D.frequency i|,
          ‖universalGramKernel m (D.frequency j - D.frequency i)‖ ≤ ε := by
  intro ε hε
  let C := universalGramDecayConstant m
  have hC : 0 ≤ C := universalGramDecayConstant_nonneg hm
  have hsmall : 0 < ε / (C + 1) := by positivity
  rcases exists_uniform_sum_inverseSquareDistance_tail_of_separated
      D.frequency D.hd D.frequency_separated (ε / (C + 1)) hsmall with
    ⟨L, hL, htail⟩
  refine ⟨L, hL, ?_⟩
  intro i U
  calc
    (∑ j ∈ U with L < |D.frequency j - D.frequency i|,
        ‖universalGramKernel m (D.frequency j - D.frequency i)‖) ≤
        ∑ j ∈ U with L < |D.frequency j - D.frequency i|,
          C / (1 + |D.frequency j - D.frequency i|) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_universalGramKernel_le_inv_sq hm
        (D.frequency j - D.frequency i)
    _ = C * ∑ j ∈ U with L < |D.frequency j - D.frequency i|,
          1 / (1 + |D.frequency j - D.frequency i|) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ C * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left (htail (D.frequency i) U) hC
    _ ≤ ε := by
      have hden : 0 < C + 1 := by positivity
      have hfrac : C / (C + 1) ≤ 1 :=
        (div_le_one hden).2 (by linarith)
      calc
        C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hfrac hε.le
        _ = ε := mul_one ε

/-- The genuine normalized Hermite kernel has uniformly small finite row sums
beyond one signed-square distance cutoff. -/
theorem exists_uniform_sum_norm_normalizedHermiteGramKernel_tail
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ ε > 0, ∃ L ≥ 0,
      ∀ (i : {j : ℤ // j ∉ D.F})
        (U : Finset {j : ℤ // j ∉ D.F}),
        ∑ j ∈ U with L < |D.frequency j - D.frequency i|,
          ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j)‖ ≤ ε := by
  intro ε hε
  let A := hermiteNormalizedGramGaussianConstant m
  have hA : 0 ≤ A := (hermiteNormalizedGramGaussianConstant_pos hm).le
  have hc : 0 < Real.pi / 2 := by positivity
  have hsmall : 0 < ε / (A + 1) := by positivity
  rcases exists_uniform_sum_exp_neg_abs_tail_of_separated
      D.frequency D.hd hc D.frequency_separated (ε / (A + 1)) hsmall with
    ⟨L, hL, htail⟩
  refine ⟨L, hL, ?_⟩
  intro i U
  calc
    (∑ j ∈ U with L < |D.frequency j - D.frequency i|,
        ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j)‖) ≤
        ∑ j ∈ U with L < |D.frequency j - D.frequency i|,
          A * Real.exp (-(Real.pi / 2) *
            |D.frequency j - D.frequency i|) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [A, frequency] using
        norm_normalizedHermiteGramKernel_le_signedSquare m hm (Λ i) (Λ j)
    _ = A * ∑ j ∈ U with L < |D.frequency j - D.frequency i|,
          Real.exp (-(Real.pi / 2) *
            |D.frequency j - D.frequency i|) := by
      rw [Finset.mul_sum]
    _ ≤ A * (ε / (A + 1)) :=
      mul_le_mul_of_nonneg_left (htail (D.frequency i) U) hA
    _ ≤ ε := by
      have hden : 0 < A + 1 := by positivity
      have hfrac : A / (A + 1) ≤ 1 :=
        (div_le_one hden).2 (by linarith)
      calc
        A * (ε / (A + 1)) = ε * (A / (A + 1)) := by ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hfrac hε.le
        _ = ε := mul_one ε

/-- Far from the signed-square diagonal, the finite row sums of the genuine
minus universal kernel are uniformly small.  This combines the actual
Gaussian tail with the universal inverse-square tail; only the local metric
band remains for the compact comparison. -/
theorem exists_uniform_sum_norm_carrier_sub_universal_far_tail
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ ε > 0, ∃ L ≥ 0,
      ∀ (i : {j : ℤ // j ∉ D.F})
        (U : Finset {j : ℤ // j ∉ D.F}),
        ∑ j ∈ U with L < |D.frequency j - D.frequency i|,
          ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
            universalGramKernel m (D.frequency j - D.frequency i)‖ ≤ ε := by
  intro ε hε
  rcases D.exists_uniform_sum_norm_normalizedHermiteGramKernel_tail
      m hm (ε / 2) (by positivity) with ⟨LA, hLA, hactual⟩
  rcases D.exists_uniform_sum_norm_universalGramKernel_tail
      m hm (ε / 2) (by positivity) with ⟨LU, hLU, huniversal⟩
  let L := max LA LU
  have hL : 0 ≤ L := by
    exact le_trans hLA (le_max_left _ _)
  refine ⟨L, hL, ?_⟩
  intro i U
  let far := U.filter (fun j => L < |D.frequency j - D.frequency i|)
  let farA := U.filter (fun j => LA < |D.frequency j - D.frequency i|)
  let farU := U.filter (fun j => LU < |D.frequency j - D.frequency i|)
  have hsubsetA : far ⊆ farA := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    exact ⟨hj'.1, lt_of_le_of_lt (le_max_left LA LU) hj'.2⟩
  have hsubsetU : far ⊆ farU := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    exact ⟨hj'.1, lt_of_le_of_lt (le_max_right LA LU) hj'.2⟩
  have hactualFar :
      (∑ j ∈ far, ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j)‖) ≤
        ε / 2 := by
    calc
      (∑ j ∈ far, ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j)‖) ≤
          ∑ j ∈ farA,
            ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubsetA
          (fun _ _ _ => norm_nonneg _)
      _ ≤ ε / 2 := by
        simpa only [farA] using hactual i U
  have huniversalFar :
      (∑ j ∈ far,
          ‖universalGramKernel m (D.frequency j - D.frequency i)‖) ≤
        ε / 2 := by
    calc
      (∑ j ∈ far,
          ‖universalGramKernel m (D.frequency j - D.frequency i)‖) ≤
          ∑ j ∈ farU,
            ‖universalGramKernel m (D.frequency j - D.frequency i)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubsetU
          (fun _ _ _ => norm_nonneg _)
      _ ≤ ε / 2 := by
        simpa only [farU] using huniversal i U
  calc
    (∑ j ∈ U with L < |D.frequency j - D.frequency i|,
        ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
          universalGramKernel m (D.frequency j - D.frequency i)‖) =
        ∑ j ∈ far,
          ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
            universalGramKernel m (D.frequency j - D.frequency i)‖ := by rfl
    _ ≤ ∑ j ∈ far,
        (‖normalizedHermiteGramKernel m hm (Λ i) (Λ j)‖ +
          ‖universalGramKernel m (D.frequency j - D.frequency i)‖) := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_sub_le _ _
    _ = (∑ j ∈ far,
          ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j)‖) +
        ∑ j ∈ far,
          ‖universalGramKernel m (D.frequency j - D.frequency i)‖ := by
      rw [Finset.sum_add_distrib]
    _ ≤ ε / 2 + ε / 2 := add_le_add hactualFar huniversalFar
    _ = ε := by ring

/-- The bounded universal Gram operator on the infinite separated carrier
tail selected by strict subcriticality. -/
def gramOperator (m : ℕ) (hm : 1 ≤ m) :
    CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
      CoefficientSpace {j : ℤ // j ∉ D.F} :=
  universalGramOperator hm D.hd D.frequency D.frequency_separated

/-- Exact matrix entries of the concrete carrier-tail universal model. -/
theorem gramOperator_entry (m : ℕ) (hm : 1 ≤ m)
    (i j : {j : ℤ // j ∉ D.F}) :
    inner ℂ (coefficientAtom i) (D.gramOperator m hm (coefficientAtom j)) =
      universalGramKernel m
        (signedSquare (Λ j) - signedSquare (Λ i)) := by
  exact universalGramOperator_entry hm D.hd D.frequency
    D.frequency_separated i j

/-- The concrete infinite carrier-tail model has the positive uniform floor
needed for Gram inversion. -/
theorem gramOperator_lowerBound (m : ℕ) (hm : 1 ≤ m) :
    universalGramLowerConstant m D.a D.d •
        (1 : CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
          CoefficientSpace {j : ℤ // j ∉ D.F}) ≤
      D.gramOperator m hm := by
  exact universalGramOperator_lowerBound D.ha D.had D.hd hm
    D.frequency D.frequency_separated

/-- Inclusion of the separated tail into the original carrier index set. -/
def tailEmbedding : {j : ℤ // j ∉ D.F} ↪ ℤ :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The actual normalized carrier atoms restricted to the same tail as the
universal model. -/
def carrierBesselAnalysis (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    BesselAnalysis (fun j : {j : ℤ // j ∉ D.F} =>
      carrierHermitePointMass m hm Λ j) :=
  B.reindex D.tailEmbedding

/-- Synthesis of the actual normalized carrier atoms on the selected tail. -/
def carrierSynthesis (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
      HermiteScale (-(m : ℤ)) :=
  (D.carrierBesselAnalysis m hm B).synthesis

/-- The genuine normalized carrier Gram restricted to the selected tail. -/
def carrierGramOperator (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
      CoefficientSpace {j : ℤ // j ∉ D.F} :=
  coefficientGram (D.carrierSynthesis m hm B)

/-- Matrix entries of the actual carrier tail Gram are the normalized Hermite
kernel at the original carrier nodes. -/
theorem carrierGramOperator_entry (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (i j : {j : ℤ // j ∉ D.F}) :
    inner ℂ (coefficientAtom i)
        (D.carrierGramOperator m hm B (coefficientAtom j)) =
      normalizedHermiteGramKernel m hm (Λ i) (Λ j) := by
  rw [carrierGramOperator, coefficientGram,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    carrierSynthesis,
    BesselAnalysis.synthesis_coefficientAtom,
    BesselAnalysis.synthesis_coefficientAtom]
  exact inner_carrierHermitePointMass_eq_kernel m hm Λ i j

/-- Difference between the genuine carrier tail Gram and its universal model. -/
def carrierGramDifference (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
      CoefficientSpace {j : ℤ // j ∉ D.F} :=
  D.carrierGramOperator m hm B - D.gramOperator m hm

/-- Exact entrywise reduction of the compact-comparison problem. -/
theorem carrierGramDifference_entry (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (i j : {j : ℤ // j ∉ D.F}) :
    inner ℂ (coefficientAtom i)
        (D.carrierGramDifference m hm B (coefficientAtom j)) =
      normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
        universalGramKernel m
          (signedSquare (Λ j) - signedSquare (Λ i)) := by
  rw [carrierGramDifference, sub_apply, inner_sub_right,
    D.carrierGramOperator_entry, D.gramOperator_entry]

/-- The universal tail Gram is self-adjoint. -/
theorem gramOperator_isSelfAdjoint (m : ℕ) (hm : 1 ≤ m) :
    IsSelfAdjoint (D.gramOperator m hm) := by
  rw [gramOperator, universalGramOperator, coefficientGram]
  exact (ContinuousLinearMap.isPositive_adjoint_comp_self _).isSelfAdjoint

/-- The genuine carrier tail Gram is self-adjoint. -/
theorem carrierGramOperator_isSelfAdjoint (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    IsSelfAdjoint (D.carrierGramOperator m hm B) := by
  rw [carrierGramOperator, coefficientGram]
  exact (ContinuousLinearMap.isPositive_adjoint_comp_self _).isSelfAdjoint

/-- The genuine-minus-universal tail Gram difference is self-adjoint. -/
theorem carrierGramDifference_isSelfAdjoint (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    IsSelfAdjoint (D.carrierGramDifference m hm B) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  rw [carrierGramDifference, map_sub, (D.carrierGramOperator_isSelfAdjoint m hm B).adjoint_eq,
    (D.gramOperator_isSelfAdjoint m hm).adjoint_eq]

/-- Matrix entry left after deleting a finite two-sided coordinate block from
the carrier Gram difference.  This is the exact scalar expression that the
local Mehler comparison and separated Schur tails must control. -/
theorem carrierGramDifference_sub_compression_entry
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (E : Finset {j : ℤ // j ∉ D.F})
    (i j : {j : ℤ // j ∉ D.F}) :
    inner ℂ (coefficientAtom i)
        ((D.carrierGramDifference m hm B -
          finiteCoordinateCompression (D.carrierGramDifference m hm B) E)
          (coefficientAtom j)) =
      if i ∈ E ∧ j ∈ E then 0 else
        normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
          universalGramKernel m
            (signedSquare (Λ j) - signedSquare (Λ i)) := by
  rw [sub_apply, inner_sub_right,
    finiteCoordinateCompression_entry,
    D.carrierGramDifference_entry]
  by_cases h : i ∈ E ∧ j ∈ E <;> simp [h]

/-- Concrete compactness handoff for the carrier Gram difference.  Once
finite central blocks leave kernel-difference Schur rows with a uniform bound
tending to zero, the operator is compact. -/
theorem carrierGramDifference_isCompact_of_finite_compression_schur
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (E : ℕ → Finset {j : ℤ // j ∉ D.F}) (R : ℕ → ℝ)
    (hR : ∀ n, 0 ≤ R n) (hR0 : Tendsto R atTop (nhds 0))
    (hrow : ∀ n (s : Finset {j : ℤ // j ∉ D.F})
      (i : {j : ℤ // j ∉ D.F}), i ∈ s →
      ∑ j ∈ s, ‖if i ∈ E n ∧ j ∈ E n then 0 else
        normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
          universalGramKernel m
            (signedSquare (Λ j) - signedSquare (Λ i))‖ ≤ R n) :
    IsCompactOperator (D.carrierGramDifference m hm B) := by
  apply isCompactOperator_of_finite_compression_schur
    (D.carrierGramDifference m hm B)
    (D.carrierGramDifference_isSelfAdjoint m hm B) E R hR hR0
  intro n s i hi
  simpa only [D.carrierGramDifference_sub_compression_entry m hm B] using
    hrow n s i hi

end CarrierUniversalTailData

end

end MeyerGeneralProblem
