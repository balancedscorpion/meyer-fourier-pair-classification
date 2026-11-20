module

public import MeyerGeneralProblem.Interpolation.CompactInterpolationBounds
public import MeyerGeneralProblem.Interpolation.GroupedConfluentUnisolvence

@[expose] public section

/-!
# Uniform actual grouped interpolation on compact node configurations

All nodes lie in a fixed interval, and different groups have a fixed positive
separation. Nodes within a group may collide arbitrarily. This closed parameter
set is compact, and the actual grouped divided-difference coefficient map is
continuous and injective on it. Consequently its inverse estimate is uniform
over the entire configuration set, including all confluent limits. No inverse
minimum intra-group gap appears. Global weighted interpolation remains separate.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

variable {ι : Type*} [Fintype ι]

/-- Bounded finite grouped node configurations with separation only between
different groups. Internal order and distinctness are not required. -/
def GroupedNodeConfigurations (size : ι → ℕ) (R d : ℝ) :
    Set ((g : ι) → Fin (size g) → ℝ) :=
  {positions | (∀ g i, |positions g i| ≤ R) ∧
    ∀ g h, g ≠ h → ∀ i j, d ≤ |positions g i - positions h j|}

omit [Fintype ι] in
/-- The parameter domain includes all confluent boundary configurations
and is closed in the actual finite node-coordinate space. -/
theorem isClosed_groupedNodeConfigurations (size : ι → ℕ) (R d : ℝ) :
    IsClosed (GroupedNodeConfigurations size R d) := by
  have hbounded : IsClosed {p : (g : ι) → Fin (size g) → ℝ |
      ∀ g i, |p g i| ≤ R} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun g => isClosed_iInter (fun i =>
      isClosed_le (by fun_prop) continuous_const))
  have hseparated : IsClosed {p : (g : ι) → Fin (size g) → ℝ |
      ∀ g h, g ≠ h → ∀ i j, d ≤ |p g i - p h j|} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun g => isClosed_iInter (fun h =>
      isClosed_iInter (fun _ => isClosed_iInter (fun i => isClosed_iInter (fun j =>
        isClosed_le continuous_const (by fun_prop))))))
  exact hbounded.inter hseparated

/-- Boundedness and closedness prove compactness of the actual grouped
node domain, without a lower bound on any internal gap. -/
theorem isCompact_groupedNodeConfigurations (size : ι → ℕ) {R : ℝ}
    (hR : 0 ≤ R) (d : ℝ) : IsCompact (GroupedNodeConfigurations size R d) := by
  apply (isCompact_closedBall (0 : (g : ι) → Fin (size g) → ℝ) R).of_isClosed_subset
    (isClosed_groupedNodeConfigurations size R d)
  intro p hp
  simp only [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  intro g i
  exact (Real.norm_eq_abs (p g i)).trans_le (hp.1 g i)

omit [Fintype ι] in
/-- Positive inter-group separation supplies exactly the disjointness
consumed by the proved confluent polynomial unisolvence theorem. -/
theorem groupedNodeDisjoint_of_mem_groupedNodeConfigurations (size : ι → ℕ)
    {R d : ℝ} (hd : 0 < d) {p : (g : ι) → Fin (size g) → ℝ}
    (hp : p ∈ GroupedNodeConfigurations size R d) :
    GroupedNodeDisjoint size (fun g => finiteNodeSequence (p g)) := by
  apply (groupedNodeDisjoint_finiteNodeSequence_iff size p).mpr
  intro g h hgh i j heq
  have hgap := hp.2 g h hgh i j
  rw [heq, sub_self, abs_zero] at hgap
  exact (not_le_of_gt hd) hgap

/-- The actual grouped coefficient map has one strictly positive lower
bound over every bounded, inter-group-separated node configuration. -/
theorem exists_uniform_groupedCoefficient_lowerBound (size : ι → ℕ)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ p ∈ GroupedNodeConfigurations size R d,
      ∀ c : Fin (∑ g, size g) → ℂ,
        A * ‖c‖ ≤ ‖groupedCoefficientData size p c‖ := by
  exact exists_uniform_lowerBound_of_compact_injective_family
    (GroupedNodeConfigurations size R d) (isCompact_groupedNodeConfigurations size hR d)
    (groupedCoefficientData size) (continuous_groupedCoefficientData_joint size)
    (fun p hp => groupedCoefficientData_injective size p
      (groupedNodeDisjoint_of_mem_groupedNodeConfigurations size hd hp))

/-- Actual monomial coefficients are uniformly controlled by their grouped
prefix divided differences, including arbitrary intra-group collisions. -/
theorem exists_uniform_groupedCoefficient_normBound (size : ι → ℕ)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ GroupedNodeConfigurations size R d,
      ∀ c : Fin (∑ g, size g) → ℂ,
        ‖c‖ ≤ C * ‖groupedCoefficientData size p c‖ := by
  exact exists_uniform_preimageNormBound_of_compact_injective_family
    (GroupedNodeConfigurations size R d) (isCompact_groupedNodeConfigurations size hR d)
    (groupedCoefficientData size) (continuous_groupedCoefficientData_joint size)
    (fun p hp => groupedCoefficientData_injective size p
      (groupedNodeDisjoint_of_mem_groupedNodeConfigurations size hd hp))

/-- Prescribed actual grouped prefix data have a unique interpolating
coefficient vector with a single configuration-independent bound. -/
theorem exists_uniform_groupedCoefficient_interpolant (size : ι → ℕ)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ GroupedNodeConfigurations size R d,
      ∀ data : (g : ι) → Fin (size g) → ℂ,
        ∃! c : Fin (∑ g, size g) → ℂ,
          groupedCoefficientData size p c = data ∧ ‖c‖ ≤ C * ‖data‖ := by
  exact exists_uniform_interpolant_of_compact_bijective_family
    (GroupedNodeConfigurations size R d) (isCompact_groupedNodeConfigurations size hR d)
    (groupedCoefficientData size) (continuous_groupedCoefficientData_joint size)
    (fun p hp => groupedCoefficientData_bijective size p
      (groupedNodeDisjoint_of_mem_groupedNodeConfigurations size hd hp))

omit [Fintype ι] in
/-- Monomial-coordinate norm controls genuine derivatives of a polynomial
on a fixed real interval, with an explicit degree/order/radius constant. -/
theorem norm_iteratedDeriv_degreeLT_eval_le_coefficientNorm {n : ℕ}
    (p : Polynomial.degreeLT ℂ n) (order : ℕ) {R x : ℝ}
    (hR : 0 ≤ R) (hx : |x| ≤ R) :
    ‖iteratedDeriv order (fun t : ℝ => p.1.eval (t : ℂ)) x‖ ≤
      ‖Polynomial.degreeLTEquiv ℂ n p‖ * polynomialDerivativeBound n order R := by
  rw [iteratedDeriv_polynomial_eval_ofReal]
  apply norm_eval_iterate_derivative_le_of_coeff_bound _ n order
    (Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLT.mp p.property).le)
    hR (norm_nonneg _) _ (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx)
  intro i
  by_cases hi : i < n
  · exact norm_le_pi_norm (Polynomial.degreeLTEquiv ℂ n p) ⟨i, hi⟩
  · rw [Polynomial.coeff_eq_zero_of_degree_lt
      ((Polynomial.mem_degreeLT.mp p.property).trans_le
        (WithBot.coe_le_coe.mpr (Nat.le_of_not_lt hi))), norm_zero]
    exact norm_nonneg _

/-- Uniform actual polynomial derivative control by grouped prefix data.
The only geometric gap is between groups, not within them. The common
constant is chosen before the configuration, polynomial, point, and order. -/
theorem exists_uniform_groupedPolynomial_derivativeBound (size : ι → ℕ)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ positions ∈ GroupedNodeConfigurations size R d,
      ∀ p : Polynomial.degreeLT ℂ (∑ g, size g), ∀ order : ℕ, ∀ x : ℝ, |x| ≤ R →
        ‖iteratedDeriv order (fun t : ℝ => p.1.eval (t : ℂ)) x‖ ≤
          C * polynomialDerivativeBound (∑ g, size g) order R *
            ‖groupedConfluentData size
              (fun g j => (finiteNodeSequence (positions g) j : ℂ)) p‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_groupedCoefficient_normBound size hR hd
  refine ⟨C, hC, ?_⟩
  intro positions hpositions p order x hx
  have hc := hbound positions hpositions (Polynomial.degreeLTEquiv ℂ (∑ g, size g) p)
  simp only [groupedCoefficientData, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply] at hc
  calc
    _ ≤ ‖Polynomial.degreeLTEquiv ℂ (∑ g, size g) p‖ *
        polynomialDerivativeBound (∑ g, size g) order R :=
      norm_iteratedDeriv_degreeLT_eval_le_coefficientNorm p order hR hx
    _ ≤ (C * ‖groupedConfluentData size
          (fun g j => (finiteNodeSequence (positions g) j : ℂ)) p‖) *
        polynomialDerivativeBound (∑ g, size g) order R :=
      mul_le_mul_of_nonneg_right hc (polynomialDerivativeBound_nonneg _ _ hR)
    _ = _ := by ring

end

end MeyerGeneralProblem
