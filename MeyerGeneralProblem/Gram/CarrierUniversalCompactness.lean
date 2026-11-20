module

public import MeyerGeneralProblem.Gram.CarrierUniversalModel
public import MeyerGeneralProblem.Gram.HermiteUniversalUniform

@[expose] public section

/-!
# Carrier/universal compact comparison assembly

This module assembles the finite central block, uniform separated far tails,
and bounded-geometry near rows.  Its single analytic input is the local
bounded-band convergence of the normalized Hermite Gram kernel to the
universal kernel.
-/

namespace MeyerGeneralProblem

open Filter

noncomputable section

namespace CarrierUniversalTailData

variable {Λ : TwoSidedCarrier} (D : CarrierUniversalTailData Λ)

/-- Only finitely many tail indices have bounded signed-square frequency. -/
theorem finite_frequency_abs_le (R : ℝ) :
    {j : {j : ℤ // j ∉ D.F} | |D.frequency j| ≤ R}.Finite := by
  let physicalBand : Set ℤ :=
    {j : ℤ | Λ j ∈ Set.Icc (-(R + 1)) (R + 1)}
  have hphysical : physicalBand.Finite := by
    simpa only [physicalBand] using
      Λ.finite_indices_in_Icc (-(R + 1)) (R + 1)
  apply (hphysical.preimage Subtype.val_injective.injOn).subset
  intro j hj
  change |signedSquare (Λ (j : ℤ))| ≤ R at hj
  have hsq : |Λ (j : ℤ)| ^ 2 ≤ R := by
    simpa only [abs_signedSquare] using hj
  have habsSelf : |Λ (j : ℤ)| ≤ |Λ (j : ℤ)| ^ 2 + 1 := by
    nlinarith [sq_nonneg (|Λ (j : ℤ)| - 1 / 2)]
  have habs : |Λ (j : ℤ)| ≤ R + 1 :=
    habsSelf.trans (by linarith)
  change -(R + 1) ≤ Λ (j : ℤ) ∧ Λ (j : ℤ) ≤ R + 1
  exact (abs_le.mp habs)

/-- Finite central block cut out by a signed-square frequency threshold. -/
def centralFrequencyFinset (R : ℝ) : Finset {j : ℤ // j ∉ D.F} :=
  (D.finite_frequency_abs_le R).toFinset

@[simp]
theorem mem_centralFrequencyFinset (R : ℝ)
    (j : {j : ℤ // j ∉ D.F}) :
    j ∈ D.centralFrequencyFinset R ↔ |D.frequency j| ≤ R := by
  exact Set.Finite.mem_toFinset _

/-- If two frequencies lie in an `L`-band and are not both in the central
`T+L` block, then each frequency has magnitude at least `T`. -/
theorem frequency_large_of_band_of_not_both_central
    {u v T L : ℝ} (hL : 0 ≤ L)
    (hband : |v - u| ≤ L)
    (hout : ¬ (|u| ≤ T + L ∧ |v| ≤ T + L)) :
    T ≤ |u| ∧ T ≤ |v| := by
  have huv : |u - v| ≤ L := by simpa only [abs_sub_comm] using hband
  rcases not_and_or.mp hout with hu | hv
  · have huLarge : T + L < |u| := lt_of_not_ge hu
    have htri : |u| ≤ |v| + |u - v| := by
      calc
        |u| = |(u - v) + v| := by ring_nf
        _ ≤ |u - v| + |v| := abs_add_le _ _
        _ = |v| + |u - v| := by ring
    exact ⟨by linarith, by linarith⟩
  · have hvLarge : T + L < |v| := lt_of_not_ge hv
    have htri : |v| ≤ |u| + |v - u| := by
      calc
        |v| = |(v - u) + u| := by ring_nf
        _ ≤ |v - u| + |u| := abs_add_le _ _
        _ = |u| + |v - u| := by ring
    exact ⟨by linarith, by linarith⟩

/-- Assuming the local bounded-band comparison, one finite central block
makes every finite masked kernel-difference row uniformly small. -/
theorem exists_maskedGramKernelDifference_row_bound
    (m : ℕ) (hm : 1 ≤ m)
    (hlocal : HermiteUniversalUniformOnBand m hm) :
    ∀ ε > 0, ∃ E : Finset {j : ℤ // j ∉ D.F},
      ∀ (U : Finset {j : ℤ // j ∉ D.F})
        (i : {j : ℤ // j ∉ D.F}), i ∈ U →
        ∑ j ∈ U, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
          normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
            universalGramKernel m (D.frequency j - D.frequency i)‖ ≤ ε := by
  intro ε hε
  rcases D.exists_uniform_sum_norm_carrier_sub_universal_far_tail
      m hm (ε / 2) (by positivity) with ⟨L, hL, hfar⟩
  let N : ℕ := (Finset.Icc ⌊-L⌋ ⌊L⌋).card
  let δ : ℝ := ε / (2 * ((N : ℝ) + 1))
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  rcases hlocal L hL δ hδ with ⟨T, hT, happrox⟩
  let E := D.centralFrequencyFinset (T + L)
  refine ⟨E, ?_⟩
  intro U i hiU
  let near := U.filter (fun j => |D.frequency j - D.frequency i| ≤ L)
  let far := U.filter (fun j => ¬ |D.frequency j - D.frequency i| ≤ L)
  have hnearCard : near.card ≤ N := by
    dsimp only [near, N]
    exact card_metricBand_le_integerFloorBand_of_separated
      D.frequency D.hd D.frequency_separated L (D.frequency i) U
  have hnearPoint (j : {j : ℤ // j ∉ D.F}) (hj : j ∈ near) :
      ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
        normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
          universalGramKernel m (D.frequency j - D.frequency i)‖ ≤ δ := by
    have hjBand : |D.frequency j - D.frequency i| ≤ L := by
      have hj' := hj
      dsimp only [near] at hj'
      exact (Finset.mem_filter.mp hj').2
    by_cases hcentral : i ∈ E ∧ j ∈ E
    · simpa [hcentral] using hδ.le
    ·
      have hout : ¬
          (|D.frequency i| ≤ T + L ∧ |D.frequency j| ≤ T + L) := by
        simpa only [E, mem_centralFrequencyFinset] using hcentral
      rcases frequency_large_of_band_of_not_both_central
          hL hjBand hout with ⟨hiLarge, hjLarge⟩
      simpa [hcentral, frequency] using
        happrox (Λ i) (Λ j) hiLarge hjLarge hjBand
  have hnearSum :
      (∑ j ∈ near, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
        normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
          universalGramKernel m (D.frequency j - D.frequency i)‖) ≤ ε / 2 := by
    have hcardReal : (near.card : ℝ) ≤ N := by exact_mod_cast hnearCard
    have hfrac : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < (N : ℝ) + 1)]
      linarith
    calc
      (∑ j ∈ near, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
          normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
            universalGramKernel m (D.frequency j - D.frequency i)‖) ≤
          ∑ _j ∈ near, δ := by
        apply Finset.sum_le_sum
        intro j hj
        exact hnearPoint j hj
      _ = (near.card : ℝ) * δ := by simp
      _ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right hcardReal hδ.le
      _ = (ε / 2) * ((N : ℝ) / ((N : ℝ) + 1)) := by
        dsimp only [δ]
        field_simp
      _ ≤ (ε / 2) * 1 :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = ε / 2 := mul_one _
  have hfarSum :
      (∑ j ∈ far, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
        normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
          universalGramKernel m (D.frequency j - D.frequency i)‖) ≤ ε / 2 := by
    calc
      (∑ j ∈ far, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
          normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
            universalGramKernel m (D.frequency j - D.frequency i)‖) ≤
          ∑ j ∈ far, ‖normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
            universalGramKernel m (D.frequency j - D.frequency i)‖ := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hcentral : i ∈ E ∧ j ∈ E
        · simp [hcentral]
        · simp [hcentral]
      _ ≤ ε / 2 := by
        simpa only [far, not_le] using hfar i U
  calc
    (∑ j ∈ U, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
        normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
          universalGramKernel m (D.frequency j - D.frequency i)‖) =
        (∑ j ∈ near, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
          normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
            universalGramKernel m (D.frequency j - D.frequency i)‖) +
        ∑ j ∈ far, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
          normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
            universalGramKernel m (D.frequency j - D.frequency i)‖ := by
      simpa only [near, far] using
        (Finset.sum_filter_add_sum_filter_not U
          (fun j => |D.frequency j - D.frequency i| ≤ L)
          (fun j => ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
            normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
              universalGramKernel m (D.frequency j - D.frequency i)‖)).symm
    _ ≤ ε / 2 + ε / 2 := add_le_add hnearSum hfarSum
    _ = ε := by ring

/-- The local bounded-band Hermite-to-universal comparison implies compactness
of the genuine carrier Gram difference.  All far-field and bounded-geometry
estimates are discharged inside this theorem. -/
theorem carrierGramDifference_isCompact_of_uniformOnBand
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hlocal : HermiteUniversalUniformOnBand m hm) :
    IsCompactOperator (D.carrierGramDifference m hm B) := by
  let R : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hR : ∀ n, 0 ≤ R n := by
    intro n
    dsimp only [R]
    positivity
  have hR0 : Tendsto R atTop (nhds 0) := by
    simpa only [R] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hblocks : ∀ n, ∃ E : Finset {j : ℤ // j ∉ D.F},
      ∀ (U : Finset {j : ℤ // j ∉ D.F})
        (i : {j : ℤ // j ∉ D.F}), i ∈ U →
        ∑ j ∈ U, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else
          normalizedHermiteGramKernel m hm (Λ i) (Λ j) -
            universalGramKernel m (D.frequency j - D.frequency i)‖ ≤ R n := by
    intro n
    exact D.exists_maskedGramKernelDifference_row_bound
      m hm hlocal (R n) (by dsimp only [R]; positivity)
  choose E hE using hblocks
  apply D.carrierGramDifference_isCompact_of_finite_compression_schur
    m hm B E R hR hR0
  intro n U i hi
  simpa only [frequency] using hE n U i hi

/-- Unconditional compactness of the genuine-minus-universal carrier Gram
difference.  The local bounded-band comparison is now a proved theorem. -/
theorem carrierGramDifference_isCompact
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    IsCompactOperator (D.carrierGramDifference m hm B) := by
  exact D.carrierGramDifference_isCompact_of_uniformOnBand
    m hm B (hermiteUniversalUniformOnBand m hm)

end CarrierUniversalTailData

end

end MeyerGeneralProblem
