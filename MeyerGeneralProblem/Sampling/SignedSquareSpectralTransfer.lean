module

public import MeyerGeneralProblem.Sampling.SignedSquareSobolevDomain

@[expose] public section

/-!
# Actual spectral weighted transfer for smooth physical functions

The localized chart's Sobolev domain is derived from physical mass,
top derivative and weighted mass. The actual grouped spectral theorem is
then applied to actual carrier zeros. No spectral or transfer estimate is
accepted as an input certificate. Extension to a completed KNS graph and
compact-remainder/path arguments are not asserted here.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology

/-- The two disjoint physical rays give the actual symmetric weighted
tail integral. This identity counts each physical point exactly once. -/
theorem signedSquare_twoRay_weighted_mass (k : ℕ) (h : ℝ → ℂ)
    (hW : Integrable (fun x : ℝ => x ^ (2 * k) * ‖h x‖ ^ 2))
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in Ioi R, x ^ (2 * k) * ‖h x‖ ^ 2) +
      (∫ x in Ioi R, x ^ (2 * k) * ‖h (-x)‖ ^ 2) =
        ∫ x in {x : ℝ | R < |x|}, |x| ^ (2 * k) * ‖h x‖ ^ 2 := by
  have href : (∫ x in Ioi R, x ^ (2 * k) * ‖h (-x)‖ ^ 2) =
      ∫ x in Iio (-R), x ^ (2 * k) * ‖h x‖ ^ 2 := by
    simpa only [(even_two_mul k).neg_pow] using
      integral_reflected_positive_tail (fun x : ℝ => x ^ (2 * k) * ‖h x‖ ^ 2) R
  have hset : {x : ℝ | R < |x|} = Ioi R ∪ Iio (-R) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio, lt_abs]
    constructor <;> intro hx
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by linarith)
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by linarith)
  have hd : Disjoint (Ioi R) (Iio (-R)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change R < x at hx
    change x < -R at hy
    linarith
  rw [href, hset]
  simp only [(even_two_mul k).pow_abs]
  exact (setIntegral_union hd measurableSet_Iio hW.integrableOn hW.integrableOn).symm

/-- Actual grouped spectral geometry implies smooth weighted transfer.
The spectral constant precedes the order, carriers and physical input;
the shell constant precedes the carriers and input. The inner principal
coefficient remains exactly (1+η)4^(-k), and the local remainder contains
only derivatives strictly below k on the paired compact physical shells. -/
theorem signedSquare_weighted_transfer_of_groupedZeros
    {q N : ℕ} {d B₀ Ω Ω' : ℝ} (hd : 0 < d) (hΩ : 1 ≤ Ω)
    (hΩΩ' : Ω < Ω') (hgap : Ω' / Real.pi < (N : ℝ) / B₀) :
    ∃ A > 0, ∀ k : ℕ, q + 1 ≤ k → ∀ η : ℝ, 0 < η →
      ∀ R : ℝ, 2 ≤ R → ∃ C > 0,
      ∀ (ΓPos ΓNeg : TwoSidedCarrier),
        BoundedClusterOrder ΓPos.toLocallyFinite d q →
        BoundedClusterOrder ΓNeg.toLocallyFinite d q →
        (∀ t r, 0 < r → (N : ℝ) * ((⌊2 * r / B₀⌋ : ℝ) - 2) ≤
          ((ΓPos.toLocallyFinite.carrier ∩ Ioo (t - r) (t + r)).ncard : ℝ)) →
        (∀ t r, 0 < r → (N : ℝ) * ((⌊2 * r / B₀⌋ : ℝ) - 2) ≤
          ((ΓNeg.toLocallyFinite.carrier ∩ Ioo (t - r) (t + r)).ncard : ℝ)) →
      ∀ (Λ : Set ℝ) (h : ℝ → ℂ), ContDiff ℝ ∞ h → MemLp h 2 →
        MemLp (iteratedDeriv k h) 2 →
        Integrable (fun x : ℝ => x ^ (2 * k) * ‖h x‖ ^ 2) →
        (∀ x ∈ Λ, h x = 0) →
        (∀ σ ∈ ΓPos.toLocallyFinite.carrier, R ^ 2 - 1 < σ → Real.sqrt σ ∈ Λ) →
        (∀ σ ∈ ΓNeg.toLocallyFinite.carrier, R ^ 2 - 1 < σ → -Real.sqrt σ ∈ Λ) →
        (∫ x in {x : ℝ | R < |x|}, |x| ^ (2 * k) * ‖h x‖ ^ 2) ≤
          (A * (Ω ^ (2 * k))⁻¹) *
            (((1 + η) / (4 : ℝ) ^ k) * (∫ x : ℝ, ‖iteratedDeriv k h x‖ ^ 2) +
              (8 * signedSquareChartErrorConstant k η / R ^ 2) *
                (∫ x : ℝ, ∑ j ∈ Finset.range k, ‖iteratedDeriv j h x‖ ^ 2) +
              C * (∫ x in Icc (R / 2) R, ∑ j ∈ Finset.range k,
                (‖iteratedDeriv j h x‖ ^ 2 + ‖iteratedDeriv j h (-x)‖ ^ 2))) := by
  obtain ⟨A, hA, hspectral⟩ := spectralGap_of_groupedZeros_classicalSobolev
    (q := q) hd hΩ hΩΩ' hgap
  refine ⟨A, hA, ?_⟩
  intro k hk η hη R hR
  obtain ⟨C, hC, henergy⟩ := exists_integral_signedSquareCutoffChart_twoRay_le k hη hR
  refine ⟨C, hC, ?_⟩
  intro ΓPos ΓNeg hcPos hcNeg hbPos hbNeg Λ h hh hF hD hW hz hΓPos hΓNeg
  obtain ⟨hGPos, hGDPos⟩ := signedSquareCutoffChart_memLp_derivatives k hR
    (by norm_num : (1 : ℝ) ^ 2 = 1) hh hF hD hW
  obtain ⟨hGNeg, hGDNeg⟩ := signedSquareCutoffChart_memLp_derivatives k hR
    (by norm_num : (-1 : ℝ) ^ 2 = 1) hh hF hD hW
  have hzeroPos : ∀ σ ∈ ΓPos.toLocallyFinite.carrier,
      signedSquareCutoffChart k R 1 h σ = 0 :=
    signedSquareCutoffChart_zero_on_carrier k R 1 h Λ _ hz (by simpa only [one_mul] using hΓPos)
  have hzeroNeg : ∀ σ ∈ ΓNeg.toLocallyFinite.carrier,
      signedSquareCutoffChart k R (-1) h σ = 0 :=
    signedSquareCutoffChart_zero_on_carrier k R (-1) h Λ _ hz (by simpa only [neg_one_mul] using hΓNeg)
  have hgPos := hspectral ΓPos hcPos hbPos _ k hk
    ((contDiff_signedSquareCutoffChart k (R := R) (by linarith) 1 hh).of_le (by simp))
    hGPos hGDPos hzeroPos
  have hgNeg := hspectral ΓNeg hcNeg hbNeg _ k hk
    ((contDiff_signedSquareCutoffChart k (R := R) (by linarith) (-1) hh).of_le (by simp))
    hGNeg hGDNeg hzeroNeg
  have hmPos := (integrable_signedSquareCutoffChart_mass_and_tail_le k hR 1 hh
    (by simpa only [one_mul] using hW)).2
  have hWNeg : Integrable (fun x : ℝ => x ^ (2 * k) * ‖h (-x)‖ ^ 2) := by
    simpa only [(even_two_mul k).neg_pow] using hW.comp_neg
  have hmNeg := (integrable_signedSquareCutoffChart_mass_and_tail_le k hR (-1) hh
    (by simpa only [neg_one_mul] using hWNeg)).2
  simp only [one_mul] at hmPos
  simp only [neg_one_mul] at hmNeg
  have htower := memLp_iteratedDeriv_of_top_classical_derivative k hh hF hD
  have hen := henergy h hh (fun j hj =>
    (memLp_two_iff_integrable_sq_norm (htower j hj).aestronglyMeasurable).mp (htower j hj))
  have hγ : 0 ≤ A * (Ω ^ (2 * k))⁻¹ := by
    have hΩpos : 0 < Ω := lt_of_lt_of_le zero_lt_one hΩ
    positivity
  have hen' := mul_le_mul_of_nonneg_left hen hγ
  rw [← signedSquare_twoRay_weighted_mass k h hW (by linarith : 0 ≤ R)]
  nlinarith

/-- The exact chart coefficient and the actual 2π Fourier derivative
normalization combine to π^(2k), not twice that value. -/
theorem signedSquare_principal_fourier_normalization (k : ℕ) :
    ((2 * Real.pi) ^ (2 * k)) / (4 : ℝ) ^ k = Real.pi ^ (2 * k) := by
  rw [mul_pow, pow_mul 2 2 k]
  norm_num

/-- With Ω>π the actual spectral/chart/Fourier leading factor is below
one half for every sufficiently large order. The threshold precedes
carriers, cutoff radius and physical input. -/
theorem eventually_signedSquare_principal_transfer_factor_le_half (A : ℝ)
    {Ω : ℝ} (hΩ : Real.pi < Ω) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (A * (Ω ^ (2 * k))⁻¹) * (((2 * Real.pi) ^ (2 * k)) / (4 : ℝ) ^ k) ≤ 1 / 2 := by
  have hΩpos : 0 < Ω := Real.pi_pos.trans hΩ
  have hr : 0 ≤ Real.pi / Ω := div_nonneg Real.pi_pos.le hΩpos.le
  have hr1 : Real.pi / Ω < 1 := (div_lt_one hΩpos).mpr hΩ
  have hr2 : (Real.pi / Ω) ^ 2 < 1 := by nlinarith
  have ht : Tendsto (fun k : ℕ => A * ((Real.pi / Ω) ^ 2) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) hr2)
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨K, ?_⟩
  intro k hk
  calc
    _ = A * ((Real.pi / Ω) ^ 2) ^ k := by
      rw [signedSquare_principal_fourier_normalization, ← pow_mul, div_pow]
      ring
    _ ≤ 1 / 2 := (hK k hk).le

end

end MeyerGeneralProblem
