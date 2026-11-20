module

public import MeyerGeneralProblem.Gram.CanonicalGroupedPositivity
public import MeyerGeneralProblem.Sampling.BeurlingWindow

@[expose] public section

/-!
# One grouped window constant before every Hermite order

The actual divided-difference exponential lower bound is chosen once from
the carrier and Fourier window. Spectral weighting then yields the exact
universal Gram floor at every admissible order, with the common Gamma factor
left visible for cancellation against the leading cross ceiling.
-/

namespace MeyerGeneralProblem

noncomputable section

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
  (horder : BoundedClusterOrder S.signedSquareImage d q)

/-- One genuine window constant works in the actual universal grouped
synthesis lower bound at every admissible physical Hermite order. -/
theorem exists_uniform_universalGrouped_synthesis_lower (hd : 0 < d)
    {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m),
      ∀ c : CoefficientSpace horder.signedGrouping.Index,
        beurlingWindowGramFloor m W A*‖c‖^2 ≤
          ‖(horder.universalGroupedBesselAnalysis hd m hm).synthesis c‖^2 := by
  classical
  obtain ⟨A, hA, hwindow⟩ :=
    canonicalGrouping_groupedExponential_finsupp_lower S.signedSquareImage horder hd hW hS
  refine ⟨A, hA, ?_⟩
  intro m hm
  have hm1 : 1 ≤ m := by have := (le_max_left _ _).trans hm; omega
  apply (horder.universalGroupedBesselAnalysis hd m hm).synthesis_norm_sq_lower_of_finsuppGram
  intro c
  rw [← BesselAnalysis.norm_sq_finsupp_linearCombination_eq_gramForm_re]
  have hnodes (C : CanonicalClusterIndex S.signedSquareImage d) :
      horder.signedGrouping.realNodes C = horder.realClusterNode C :=
    funext (horder.signedGrouping_realNodes C)
  have htransfer := horder.signedGrouping.universalAtom_finsupp_ge_window m hm1 c W
  simp_rw [hnodes] at htransfer
  let b := 2*gramNormalization m*(1+4*W^2)⁻¹^(2*m)
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (mul_nonneg (by norm_num) (gramNormalization_pos hm1).le) (by positivity)
  calc
    beurlingWindowGramFloor m W A*(c.sum fun _ z => ‖z‖^2) =
        b*(A*(c.sum fun _ z => ‖z‖^2)) := by unfold beurlingWindowGramFloor b; ring
    _ ≤ b*(_root_.MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (-W) W))
          (fun t : ℝ =>
          ‖c.sum (fun x z => z*groupedExponentialInitial (horder.realClusterNode x.1) x.2 t)‖^2)) :=
      mul_le_mul_of_nonneg_left (hwindow c) hb
    _ ≤ _ := htransfer

/-- The actual canonical universal Gram has one source constant before all
orders, with exactly `2*g_m*A*(1+4*W^2)^(-2m)` as its Loewner floor. -/
theorem exists_uniform_universalGroupedGramFloor (hd : 0 < d)
    {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m),
      beurlingWindowGramFloor m W A •
        (1 : CoefficientSpace horder.signedGrouping.Index →L[ℂ]
          CoefficientSpace horder.signedGrouping.Index) ≤
            horder.universalGroupedGramOperator hd m hm := by
  obtain ⟨A, hA, hlower⟩ := horder.exists_uniform_universalGrouped_synthesis_lower hd hW hS
  refine ⟨A, hA, ?_⟩
  intro m hm
  rw [ContinuousLinearMap.le_def]
  apply ContinuousLinearMap.isPositive_def'.mpr
  constructor
  · apply IsSelfAdjoint.sub
    · exact (ContinuousLinearMap.isPositive_adjoint_comp_self
        (horder.universalGroupedBesselAnalysis hd m hm).synthesis).isSelfAdjoint
    · rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      apply IsSelfAdjoint.smul
      · rw [isSelfAdjoint_iff]; simp
      · exact ContinuousLinearMap.isPositive_one.isSelfAdjoint
  · intro c
    change 0 ≤ RCLike.re (inner ℂ
      ((horder.universalGroupedGramOperator hd m hm-beurlingWindowGramFloor m W A • 1) c) c)
    rw [sub_apply, inner_sub_left, map_sub]
    simp only [universalGroupedGramOperator, coefficientGram, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self, smul_apply]
    rw [← norm_sq_eq_re_inner, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_real_left, RCLike.smul_re, ← norm_sq_eq_re_inner]
    linarith [hlower m hm c]

end BoundedClusterOrder

end

end MeyerGeneralProblem
