module

public import MeyerGeneralProblem.Distribution.PolynomialLocalDivisibility
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section

/-!
# Local zero sets and irreducible complex polynomials

An affine line through the root and a nonzero point supplies a nontrivial
polynomial fiber. A shear places that line along one distinguished variable
without changing irreducibility or the local containment of zero sets.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MvPolynomial

private def coordinateShearHom {ι : Type*} (d : ι → ℂ) :
    MvPolynomial (Option ι) ℂ →ₐ[ℂ] MvPolynomial (Option ι) ℂ :=
  MvPolynomial.aeval (fun j =>
    j.elim (X none) (fun i => X (some i) + C (d i) * X none))

private theorem coordinateShearHom_comp_neg {ι : Type*} (d : ι → ℂ) :
    (coordinateShearHom d).comp (coordinateShearHom (-d)) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro j
  cases j with
  | none => simp [coordinateShearHom]
  | some i =>
    simp [coordinateShearHom, MvPolynomial.algebraMap_eq]

private def coordinateShear {ι : Type*} (d : ι → ℂ) :
    MvPolynomial (Option ι) ℂ ≃ₐ[ℂ] MvPolynomial (Option ι) ℂ :=
  AlgEquiv.ofAlgHom (coordinateShearHom d) (coordinateShearHom (-d))
    (coordinateShearHom_comp_neg d) (by simpa only [neg_neg] using coordinateShearHom_comp_neg (-d))

private theorem eval_coordinateShear {ι : Type*} (d x : ι → ℂ) (z : ℂ)
    (p : MvPolynomial (Option ι) ℂ) :
    MvPolynomial.eval (fun j => j.elim z x) (coordinateShear d p) =
      MvPolynomial.eval (fun j => j.elim z (fun i => x i + d i * z)) p := by
  let v (j : Option ι) : ℂ := j.elim z x
  let w (j : Option ι) : ℂ := j.elim z (fun i => x i + d i * z)
  change ((MvPolynomial.aeval v).comp (coordinateShearHom d)) p = MvPolynomial.aeval w p
  congr 1
  apply MvPolynomial.algHom_ext
  intro j
  cases j <;> simp [coordinateShearHom, v, w]

/-- If a complex multivariate irreducible polynomial has a zero and all
its nearby zeros are zeros of a second polynomial, then it divides the
second polynomial. The chosen fiber need only be nontrivial at the
base point, even when the base root is singular. -/
theorem irreducible_dvd_of_mvPolynomial_local_zeroSet_containment
    {ι : Type*} [Fintype ι] (p q : MvPolynomial ι ℂ) (hp : Irreducible p)
    (v₀ : ι → ℂ) (hzero : MvPolynomial.eval v₀ p = 0)
    (W : Set (ι → ℂ)) (hW : IsOpen W) (h₀ : v₀ ∈ W)
    (hcontained : ∀ v ∈ W, MvPolynomial.eval v p = 0 → MvPolynomial.eval v q = 0) :
    p ∣ q := by
  classical
  obtain ⟨v₁, hv₁⟩ : ∃ v, MvPolynomial.eval v p ≠ 0 := by
    by_contra hv
    push Not at hv
    exact hp.ne_zero
      (mvPolynomial_eq_zero_of_eval_eq_zero_on_open p univ isOpen_univ v₀ (mem_univ _) fun v _ => hv v)
  obtain ⟨j, hj⟩ : ∃ i, v₁ i ≠ v₀ i := by
    by_contra hh
    push Not at hh
    exact hv₁ ((funext hh : v₁ = v₀) ▸ hzero)
  let τ := {i : ι // i ≠ j}
  let e : Option τ ≃ ι := Equiv.optionSubtypeNe j
  let d (i : τ) : ℂ := (v₁ i - v₀ i) / (v₁ j - v₀ j)
  let x (i : τ) : ℂ := v₀ i - d i * v₀ j
  let E : MvPolynomial ι ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial τ ℂ) :=
    (MvPolynomial.renameEquiv ℂ e.symm).trans
      ((coordinateShear d).trans (MvPolynomial.optionEquivLeft ℂ τ))
  let point (w : (τ → ℂ) × ℂ) (i : ι) : ℂ :=
    (e.symm i).elim w.2 (fun k => w.1 k + d k * w.2)
  have heval (r : MvPolynomial ι ℂ) (y : τ → ℂ) (z : ℂ) :
      polynomialCoordinateFiber (E r) y z = MvPolynomial.eval (point (y, z)) r := by
    change ((MvPolynomial.optionEquivLeft ℂ τ)
      (coordinateShear d (MvPolynomial.rename e.symm r))).eval₂ (MvPolynomial.eval y) z = _
    rw [← Polynomial.eval_map, ← MvPolynomial.optionEquivLeft_elim_eval,
      eval_coordinateShear, MvPolynomial.eval_rename]
    rfl
  have hpoint₀ : point (x, v₀ j) = v₀ := by
    funext i
    obtain ⟨k, rfl⟩ := e.surjective i
    dsimp only [point, Prod.fst, Prod.snd]
    rw [e.symm_apply_apply]
    cases k with
    | none => rfl
    | some k =>
      change v₀ k - d k * v₀ j + d k * v₀ j = v₀ k
      exact sub_add_cancel _ _
  have hpoint₁ : point (x, v₁ j) = v₁ := by
    funext i
    obtain ⟨k, rfl⟩ := e.surjective i
    dsimp only [point, Prod.fst, Prod.snd]
    rw [e.symm_apply_apply]
    cases k with
    | none => rfl
    | some k =>
      have hd : d k * (v₁ j - v₀ j) = v₁ k - v₀ k :=
        div_mul_cancel₀ _ (sub_ne_zero.mpr hj)
      change v₀ k - d k * v₀ j + d k * v₁ j = v₁ k
      calc
        _ = v₀ k + d k * (v₁ j - v₀ j) := by ring
        _ = _ := by rw [hd, add_sub_cancel]
  have hpoint : Continuous point := by
    apply continuous_pi
    intro i
    cases h : e.symm i with
    | none =>
      simpa [point, h] using
        (continuous_snd : Continuous (Prod.snd : ((τ → ℂ) × ℂ) → ℂ))
    | some k =>
      have hx : Continuous (fun w : (τ → ℂ) × ℂ => w.1 k) :=
        (continuous_apply k).comp continuous_fst
      have hz : Continuous (fun w : (τ → ℂ) × ℂ => d k * w.2) :=
        continuous_const.mul continuous_snd
      simp only [point, h, Option.elim_some]
      exact hx.add hz
  have hdiv : E p ∣ E q := by
    refine irreducible_dvd_of_local_polynomialFiber_zeroSet_containment
      (E p) (E q) ((MulEquiv.irreducible_iff E.toMulEquiv).mpr hp) x (v₀ j) ?_ ?_
      (point ⁻¹' W) (hW.preimage hpoint) ?_ ?_
    · rw [heval, hpoint₀]
      exact hzero
    · refine ⟨v₁ j, ?_⟩
      rw [heval, hpoint₁]
      exact hv₁
    · change point (x, v₀ j) ∈ W
      rwa [hpoint₀]
    · intro y z hyz hz
      rw [heval] at hz ⊢
      exact hcontained (point (y, z)) hyz hz
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨E.symm r, E.injective ?_⟩
  rw [map_mul, E.apply_symm_apply]
  exact hr

end

end MeyerGeneralProblem
