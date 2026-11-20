module

public import MeyerGeneralProblem.Distribution.PolynomialLocalContainment

@[expose] public section

/-!
# Selecting a zero-free polynomial factor

Local divisibility removes an irreducible factor with a zero in the
chosen set. The reduced quotient has the same local continuous factor,
so iteration removes that irreducible as many times as it occurs.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MvPolynomial

/-- The actual numerator can be written as the denominator times a
continuous function in an open neighborhood of each point of the set. -/
def PolynomialQuotientRegularOn {ι : Type*} (S : Set (ι → ℂ))
    (p q : MvPolynomial ι ℂ) : Prop :=
  ∀ v ∈ S, ∃ W : Set (ι → ℂ), IsOpen W ∧ v ∈ W ∧ ∃ H : (ι → ℂ) → ℂ,
    ContinuousOn H W ∧ ∀ w ∈ W, MvPolynomial.eval w q = MvPolynomial.eval w p * H w

private theorem polynomialQuotientRegularOn_cancel {ι : Type*} [Fintype ι]
    (S : Set (ι → ℂ)) (d p q : MvPolynomial ι ℂ) (hd : d ≠ 0)
    (h : PolynomialQuotientRegularOn S (d * p) (d * q)) :
    PolynomialQuotientRegularOn S p q := by
  intro v hv
  obtain ⟨W, hW, hvW, H, hH, hEq⟩ := h v hv
  refine ⟨W, hW, hvW, H, hH, fun w hw => ?_⟩
  by_contra he
  let f (z : ι → ℂ) : ℂ := MvPolynomial.eval z q - MvPolynomial.eval z p * H z
  have hf : ContinuousOn f W :=
    (MvPolynomial.continuous_eval (p := q)).continuousOn.sub
      ((MvPolynomial.continuous_eval (p := p)).continuousOn.mul hH)
  let V := W ∩ f ⁻¹' {c : ℂ | c ≠ 0}
  have hV : IsOpen V := hf.isOpen_inter_preimage hW isOpen_ne
  have hWV : w ∈ V := ⟨hw, sub_ne_zero.mpr he⟩
  apply hd (mvPolynomial_eq_zero_of_eval_eq_zero_on_open d V hV w hWV (fun z hz => ?_))
  by_contra hn
  have heq := hEq z hz.1
  rw [map_mul, map_mul, mul_assoc] at heq
  exact hz.2 (sub_eq_zero.mpr (mul_left_cancel₀ hn heq))

/-- Given any set of evaluation points, split off all irreducible factors
of the denominator that have a zero there, including their full
multiplicities. The resulting denominator is zero-free on the set.
The selected product divides every numerator whose quotient has a
continuous extension in an open neighborhood of each point. -/
theorem exists_zeroFree_factor_for_local_polynomial_quotients
    {ι : Type*} [Fintype ι] (S : Set (ι → ℂ)) (p : MvPolynomial ι ℂ) :
    p ≠ 0 →
    ∃ bad : Multiset (MvPolynomial ι ℂ), ∃ good : MvPolynomial ι ℂ,
      p = bad.prod * good ∧
      (∀ d ∈ bad, Irreducible d ∧ ∃ v ∈ S, MvPolynomial.eval v d = 0) ∧
      (∀ v ∈ S, MvPolynomial.eval v good ≠ 0) ∧
      ∀ q, PolynomialQuotientRegularOn S p q → bad.prod ∣ q := by
  classical
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit u hu =>
    intro _
    refine ⟨0, u, by simp, by simp, fun v _ => (hu.map (MvPolynomial.eval v)).ne_zero, ?_⟩
    intro q _
    simp
  | mul a d ha hd ih =>
    intro _
    obtain ⟨bad, good, haeq, hbad, hgood, hdivide⟩ := ih ha
    by_cases hroot : ∃ v ∈ S, MvPolynomial.eval v d = 0
    · refine ⟨d ::ₘ bad, good, ?_, ?_, hgood, ?_⟩
      · rw [Multiset.prod_cons, mul_assoc, ← haeq]
      · intro r hr
        rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact ⟨hd, hroot⟩
        · exact hbad r hr
      · intro q hq
        obtain ⟨v, hv, hvd⟩ := hroot
        obtain ⟨W, hW, hvW, H, _, hEq⟩ := hq v hv
        have hdq : d ∣ q := irreducible_dvd_of_mvPolynomial_local_zeroSet_containment
          d q hd v hvd W hW hvW (fun w hw hzero => by
            rw [hEq w hw, map_mul, hzero, zero_mul, zero_mul])
        obtain ⟨q', rfl⟩ := hdq
        obtain ⟨k, hk⟩ := hdivide q' (polynomialQuotientRegularOn_cancel S d a q' hd.ne_zero hq)
        refine ⟨k, ?_⟩
        rw [Multiset.prod_cons, mul_assoc, ← hk]
    · push Not at hroot
      refine ⟨bad, d * good, ?_, hbad, ?_, ?_⟩
      · rw [haeq, mul_left_comm]
      · intro v hv
        rw [map_mul]
        exact mul_ne_zero (hroot v hv) (hgood v hv)
      · intro q hq
        apply hdivide q
        intro v hv
        obtain ⟨W, hW, hvW, H, hH, hEq⟩ := hq v hv
        refine ⟨W, hW, hvW, fun w => MvPolynomial.eval w d * H w,
          (MvPolynomial.continuous_eval (p := d)).continuousOn.mul hH, fun w hw => ?_⟩
        rw [hEq w hw, map_mul]
        ring

end

end MeyerGeneralProblem
