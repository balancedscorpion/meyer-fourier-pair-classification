module

public import MeyerGeneralProblem.Interpolation.GroupedCompactBounds
public import MeyerGeneralProblem.Interpolation.GroupedSubdata

@[expose] public section

/-!
# One actual interpolation bound for all bounded finite group patterns

A bounded number of groups, each of bounded size, has only finitely many
size patterns. Taking a finite upper bound of the proved compact-configuration
estimates gives a single coefficient and derivative bound for every pattern.
The interpolant is the actual polynomial with the prescribed confluent
divided-difference data. Internal nodes may coincide; only different groups
have a positive separation. No inverse estimate is supplied as a hypothesis.

These are local finite-polynomial estimates. The global cutoff construction
and weighted Sobolev summation remain separate.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset Polynomial

/-- The finite catalogue of at most `N` groups, each with at most `q` nodes.
Empty groups are permitted and do not create any interpolation constraints. -/
abbrev BoundedGroupedPattern (N q : ℕ) :=
  Σ n : Fin (N + 1), Fin n.val → Fin (q + 1)

/-- The natural-number group sizes of a bounded finite pattern. -/
def boundedGroupedPatternSize {N q : ℕ} (pattern : BoundedGroupedPattern N q) :
    Fin pattern.1.val → ℕ := fun g => (pattern.2 g).val

/-- One coefficient inverse bound works simultaneously for every bounded
size pattern and every actual inter-group-separated configuration. -/
theorem exists_uniform_groupedPattern_coefficientNormBound (N q : ℕ)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ N → ∀ size : Fin n → ℕ,
      (∀ g, size g ≤ q) → ∀ positions ∈ GroupedNodeConfigurations size R d,
        ∀ coefficients : Fin (∑ g, size g) → ℂ,
          ‖coefficients‖ ≤ C * ‖groupedCoefficientData size positions coefficients‖ := by
  classical
  have hlocal (pattern : BoundedGroupedPattern N q) :=
    exists_uniform_groupedCoefficient_normBound (boundedGroupedPatternSize pattern) hR hd
  choose C hC hbound using hlocal
  let common : ℝ := 1 + ∑ pattern : BoundedGroupedPattern N q, C pattern
  have hsum : 0 ≤ ∑ pattern : BoundedGroupedPattern N q, C pattern :=
    sum_nonneg (fun pattern _ => (hC pattern).le)
  have hcommon : 0 < common := by dsimp [common]; linarith
  refine ⟨common, hcommon, ?_⟩
  intro n hn size hsize positions hpositions coefficients
  let pattern : BoundedGroupedPattern N q :=
    ⟨⟨n, Nat.lt_succ_iff.mpr hn⟩, fun g => ⟨size g, Nat.lt_succ_iff.mpr (hsize g)⟩⟩
  have hle : C pattern ≤ common := by
    have hs := single_le_sum (fun pattern _ => (hC pattern).le)
      (mem_univ pattern)
    dsimp [common]
    linarith
  exact (hbound pattern positions hpositions coefficients).trans
    (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

/-- The same finite-pattern argument yields a strictly positive lower
bound for the actual grouped coefficient map, uniformly over all patterns. -/
theorem exists_uniform_groupedPattern_coefficientLowerBound (N q : ℕ)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, n ≤ N → ∀ size : Fin n → ℕ,
      (∀ g, size g ≤ q) → ∀ positions ∈ GroupedNodeConfigurations size R d,
        ∀ coefficients : Fin (∑ g, size g) → ℂ,
          A * ‖coefficients‖ ≤ ‖groupedCoefficientData size positions coefficients‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_groupedPattern_coefficientNormBound N q hR hd
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro n hn size hsize positions hpositions coefficients
  have h := hbound n hn size hsize positions hpositions coefficients
  have hdiv : ‖coefficients‖ / C ≤
      ‖groupedCoefficientData size positions coefficients‖ :=
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using h)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- A finite explicit envelope for all polynomial derivative bounds up to
order `k` and all total node counts allowed by `N` groups of size at most `q`. -/
def groupedPatternDerivativeEnvelope (N q k : ℕ) (R : ℝ) : ℝ :=
  ∑ n : Fin (N * q + 1), ∑ order : Fin (k + 1), polynomialDerivativeBound n order R

/-- The finite derivative envelope is nonnegative on a nonnegative radius. -/
theorem groupedPatternDerivativeEnvelope_nonneg (N q k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ groupedPatternDerivativeEnvelope N q k R := by
  exact sum_nonneg (fun n _ => sum_nonneg (fun order _ =>
    polynomialDerivativeBound_nonneg n order hR))

/-- Every allowed degree/order bound occurs in the finite derivative
envelope, independently of the actual size pattern. -/
theorem polynomialDerivativeBound_le_groupedPatternDerivativeEnvelope
    {N q k n order : ℕ} (hn : n ≤ N * q) (horder : order ≤ k)
    {R : ℝ} (hR : 0 ≤ R) :
    polynomialDerivativeBound n order R ≤ groupedPatternDerivativeEnvelope N q k R := by
  classical
  let ni : Fin (N * q + 1) := ⟨n, Nat.lt_succ_iff.mpr hn⟩
  let oi : Fin (k + 1) := ⟨order, Nat.lt_succ_iff.mpr horder⟩
  calc
    _ ≤ ∑ r : Fin (k + 1), polynomialDerivativeBound ni r R :=
      single_le_sum (f := fun r : Fin (k + 1) => polynomialDerivativeBound ni r R)
        (fun r _ => polynomialDerivativeBound_nonneg ni r hR) (mem_univ oi)
    _ ≤ groupedPatternDerivativeEnvelope N q k R :=
      show (∑ r : Fin (k + 1), polynomialDerivativeBound ni r R) ≤
          ∑ degree : Fin (N * q + 1),
            ∑ r : Fin (k + 1), polynomialDerivativeBound degree r R from
        single_le_sum (f := fun degree : Fin (N * q + 1) =>
          ∑ r : Fin (k + 1), polynomialDerivativeBound degree r R)
          (fun degree _ => sum_nonneg (fun r _ =>
          polynomialDerivativeBound_nonneg degree r hR)) (mem_univ ni)

/-- A bounded pattern has at most `N * q` nodes, counting every repeated
node with its multiplicity. -/
theorem sum_groupedPatternSize_le {N q n : ℕ} (hn : n ≤ N)
    (size : Fin n → ℕ) (hsize : ∀ g, size g ≤ q) :
    ∑ g, size g ≤ N * q := by
  calc
    ∑ g, size g ≤ ∑ _ : Fin n, q := sum_le_sum (fun g _ => hsize g)
    _ = n * q := by simp
    _ ≤ N * q := Nat.mul_le_mul_right q hn

/-- One constant controls both actual monomial coefficients and all real
derivatives through order `k`, simultaneously over all permitted patterns.
The only separation parameter is the gap between different groups. -/
theorem exists_uniform_groupedPattern_polynomialBounds (N q k : ℕ)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ N → ∀ size : Fin n → ℕ,
      (∀ g, size g ≤ q) → ∀ positions ∈ GroupedNodeConfigurations size R d,
        ∀ p : Polynomial.degreeLT ℂ (∑ g, size g),
          ‖Polynomial.degreeLTEquiv ℂ (∑ g, size g) p‖ ≤
            C * ‖groupedConfluentData size
              (fun g j => (finiteNodeSequence (positions g) j : ℂ)) p‖ ∧
          ∀ order ≤ k, ∀ x : ℝ, |x| ≤ R →
            ‖iteratedDeriv order (fun t : ℝ => p.1.eval (t : ℂ)) x‖ ≤
              C * ‖groupedConfluentData size
                (fun g j => (finiteNodeSequence (positions g) j : ℂ)) p‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_groupedPattern_coefficientNormBound N q hR hd
  let envelope := groupedPatternDerivativeEnvelope N q k R
  have henv : 0 ≤ envelope := groupedPatternDerivativeEnvelope_nonneg N q k hR
  have hCen : C ≤ C * (1 + envelope) := by nlinarith
  refine ⟨C * (1 + envelope), mul_pos hC (by linarith), ?_⟩
  intro n hn size hsize positions hpositions p
  have hc := hbound n hn size hsize positions hpositions
    (Polynomial.degreeLTEquiv ℂ (∑ g, size g) p)
  simp only [groupedCoefficientData, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply] at hc
  refine ⟨hc.trans (mul_le_mul_of_nonneg_right hCen (norm_nonneg _)), ?_⟩
  intro order horder x hx
  have hderiv := norm_iteratedDeriv_degreeLT_eval_le_coefficientNorm p order hR hx
  have hdegree := sum_groupedPatternSize_le hn size hsize
  have hsmall := polynomialDerivativeBound_le_groupedPatternDerivativeEnvelope
    hdegree horder hR
  calc
    _ ≤ ‖Polynomial.degreeLTEquiv ℂ (∑ g, size g) p‖ *
        polynomialDerivativeBound (∑ g, size g) order R := hderiv
    _ ≤ (C * ‖groupedConfluentData size
          (fun g j => (finiteNodeSequence (positions g) j : ℂ)) p‖) *
        polynomialDerivativeBound (∑ g, size g) order R :=
      mul_le_mul_of_nonneg_right hc (polynomialDerivativeBound_nonneg _ _ hR)
    _ ≤ (C * ‖groupedConfluentData size
          (fun g j => (finiteNodeSequence (positions g) j : ℂ)) p‖) * (1 + envelope) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC.le (norm_nonneg _))
    _ = _ := by ring

/-- Arbitrary grouped confluent data have a unique actual interpolating
polynomial, with coefficient and derivative bounds using one constant for
every allowed pattern. No inverse or interpolation bound is assumed. -/
theorem exists_uniform_groupedPattern_polynomialInterpolant (N q k : ℕ)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ N → ∀ size : Fin n → ℕ,
      (∀ g, size g ≤ q) → ∀ positions ∈ GroupedNodeConfigurations size R d,
        ∀ data : (g : Fin n) → Fin (size g) → ℂ,
          ∃! p : Polynomial.degreeLT ℂ (∑ g, size g),
            groupedConfluentData size
              (fun g j => (finiteNodeSequence (positions g) j : ℂ)) p = data ∧
            ‖Polynomial.degreeLTEquiv ℂ (∑ g, size g) p‖ ≤ C * ‖data‖ ∧
            ∀ order ≤ k, ∀ x : ℝ, |x| ≤ R →
              ‖iteratedDeriv order (fun t : ℝ => p.1.eval (t : ℂ)) x‖ ≤ C * ‖data‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_groupedPattern_polynomialBounds N q k hR hd
  refine ⟨C, hC, ?_⟩
  intro n hn size hsize positions hpositions data
  have hdisjoint := groupedNodeDisjoint_of_mem_groupedNodeConfigurations size hd hpositions
  have hcdisjoint : GroupedNodeDisjoint size
      (fun g j => (finiteNodeSequence (positions g) j : ℂ)) := by
    intro g h hgh i hi j hj heq
    exact hdisjoint g h hgh i hi j hj (Complex.ofReal_injective heq)
  let p := groupedConfluentInterpolant size _ hcdisjoint data
  have hdata : groupedConfluentData size
      (fun g j => (finiteNodeSequence (positions g) j : ℂ)) p = data := by
    funext g i
    exact polynomialDividedDifference_groupedConfluentInterpolant size _ hcdisjoint data g i
  have hb := hbound n hn size hsize positions hpositions p
  rw [hdata] at hb
  refine ⟨p, ⟨hdata, hb⟩, ?_⟩
  intro other hother
  exact groupedConfluentData_injective size _ hcdisjoint (hother.1.trans hdata.symm)

/-- Divided differences of a polynomial written in the local coordinate
`x - centre` are exactly the synthetic polynomial data at the centred nodes.
The identity includes every confluent prefix. -/
theorem analyticDividedDifference_finite_shiftedPolynomial {n : ℕ}
    (positions : Fin n → ℝ) (j : Fin n) (p : ℂ[X]) (centre : ℝ) :
    analyticDividedDifference (finiteNodeSequence positions) j
        (fun t : ℝ => p.eval ((t - centre : ℝ) : ℂ)) =
      polynomialDividedDifference
        (fun i => (finiteNodeSequence (fun a => positions a - centre) i : ℂ)) j p := by
  have h := analyticDividedDifference_finite_recenter positions j
    (fun t : ℝ => p.eval ((t - centre : ℝ) : ℂ)) centre
  simp only [add_sub_cancel_right] at h
  rw [← h, analyticDividedDifference_polynomial_eval]

/-- The same single interpolation constant works around every centre.
The polynomial coefficients are measured in the local coordinate `x - centre`,
while its prescribed analytic data and derivative bounds are at the actual
untranslated nodes and real points. Internal collisions remain permitted. -/
theorem exists_uniform_groupedPattern_centeredPolynomialInterpolant (N q k : ℕ)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ N → ∀ size : Fin n → ℕ,
      (∀ g, size g ≤ q) → ∀ centre : ℝ,
        ∀ positions : (g : Fin n) → Fin (size g) → ℝ,
          (fun g i => positions g i - centre) ∈ GroupedNodeConfigurations size R d →
          ∀ data : (g : Fin n) → Fin (size g) → ℂ,
            ∃! p : Polynomial.degreeLT ℂ (∑ g, size g),
              (∀ g, ∀ i : Fin (size g),
                analyticDividedDifference (finiteNodeSequence (positions g)) i
                  (fun t : ℝ => p.1.eval ((t - centre : ℝ) : ℂ)) = data g i) ∧
              ‖Polynomial.degreeLTEquiv ℂ (∑ g, size g) p‖ ≤ C * ‖data‖ ∧
              ∀ order ≤ k, ∀ x : ℝ, |x - centre| ≤ R →
                ‖iteratedDeriv order
                  (fun t : ℝ => p.1.eval ((t - centre : ℝ) : ℂ)) x‖ ≤ C * ‖data‖ := by
  obtain ⟨C, hC, hinterp⟩ :=
    exists_uniform_groupedPattern_polynomialInterpolant N q k hR hd
  refine ⟨C, hC, ?_⟩
  intro n hn size hsize centre positions hpositions data
  obtain ⟨p, hp, hunique⟩ := hinterp n hn size hsize
    (fun g i => positions g i - centre) hpositions data
  refine ⟨p, ⟨?_, hp.2.1, ?_⟩, ?_⟩
  · intro g i
    rw [analyticDividedDifference_finite_shiftedPolynomial]
    exact congrFun (congrFun hp.1 g) i
  · intro order horder x hx
    rw [iteratedDeriv_comp_sub_const order (fun t : ℝ => p.1.eval (t : ℂ)) centre]
    exact hp.2.2 order horder (x - centre) hx
  · intro other hother
    have hdisjoint :=
      groupedNodeDisjoint_of_mem_groupedNodeConfigurations size hd hpositions
    have hcdisjoint : GroupedNodeDisjoint size
        (fun g j => (finiteNodeSequence (fun i => positions g i - centre) j : ℂ)) := by
      intro g h hgh i hi j hj heq
      exact hdisjoint g h hgh i hi j hj (Complex.ofReal_injective heq)
    apply groupedConfluentData_injective size _ hcdisjoint
    rw [hp.1]
    funext g i
    exact (analyticDividedDifference_finite_shiftedPolynomial
      (positions g) i other.1 centre).symm.trans (hother.1 g i)

end

end MeyerGeneralProblem
