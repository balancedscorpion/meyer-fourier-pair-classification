module

public import MeyerGeneralProblem.Distribution.FourierGapRealPrimitive
public import MeyerGeneralProblem.Distribution.CompactSchwartzAntiderivative
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Local polynomials from a vanishing weak higher derivative

The action on compact tests in an interval factors through the finite
vector of moments when the weak derivative vanishes. Continuous
integral representatives then agree with the resulting polynomial.
-/

namespace MeyerGeneralProblem

noncomputable section

open LineDeriv MeasureTheory Set
open scoped ContDiff Topology

private def compactSchwartzIntervalSubmodule (l r : ℝ) : Submodule ℂ (SchwartzMap ℝ ℂ) where
  carrier := {φ | tsupport (φ : ℝ → ℂ) ⊆ Ioo l r}
  zero_mem' := by
    change tsupport (fun _ : ℝ => (0 : ℂ)) ⊆ Ioo l r
    simp
  add_mem' := by
    intro φ ψ hφ hψ
    change tsupport ((φ : ℝ → ℂ) + (ψ : ℝ → ℂ)) ⊆ Ioo l r
    exact (tsupport_add (φ : ℝ → ℂ) ψ).trans (union_subset hφ hψ)
  smul_mem' := by
    intro a φ hφ
    change tsupport (a • (φ : ℝ → ℂ)) ⊆ Ioo l r
    exact (tsupport_smul_subset_right (fun _ : ℝ => a) (φ : ℝ → ℂ)).trans hφ

private theorem compactSchwartzInterval_hasCompactSupport {l r : ℝ}
    (φ : compactSchwartzIntervalSubmodule l r) : HasCompactSupport φ.val :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (φ.property.trans Ioo_subset_Icc_self)

private def compactSchwartzIntervalIntegral {l r : ℝ} (f : ℝ → ℂ)
    (hf : Continuous f) : compactSchwartzIntervalSubmodule l r →ₗ[ℂ] ℂ where
  toFun φ := ∫ x : ℝ, φ.val x * f x
  map_add' φ ψ := by
    change (∫ x : ℝ, (φ.val x + ψ.val x) * f x) = _
    simp_rw [add_mul]
    exact integral_add
      ((φ.val.continuous.mul hf).integrable_of_hasCompactSupport
        (compactSchwartzInterval_hasCompactSupport φ).mul_right)
      ((ψ.val.continuous.mul hf).integrable_of_hasCompactSupport
        (compactSchwartzInterval_hasCompactSupport ψ).mul_right)
  map_smul' a φ := by
    change (∫ x : ℝ, (a * φ.val x) * f x) = a * ∫ x : ℝ, φ.val x * f x
    simp_rw [mul_assoc, integral_const_mul]

/-- Equality on compact Schwartz tests inside an open interval implies
pointwise equality there for two continuous densities. -/
theorem continuous_eqOn_Ioo_of_schwartz_integral_eq
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) (l r : ℝ)
    (h : ∀ φ : SchwartzMap ℝ ℂ, HasCompactSupport φ →
      tsupport (φ : ℝ → ℂ) ⊆ Ioo l r →
      (∫ x : ℝ, φ x * f x) = ∫ x : ℝ, φ x * g x) :
    EqOn f g (Ioo l r) := by
  have hAE : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo l r → f x - g x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.sub hg).locallyIntegrable.locallyIntegrableOn (Ioo l r))
    intro u hu huc hUs
    let f₀ : ℝ → ℂ := Complex.ofRealCLM ∘ u
    have hf₀ : HasCompactSupport f₀ := huc.comp_left (show ((0 : ℝ) : ℂ) = 0 by norm_num)
    let φ := hf₀.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hu)
    have hφ : tsupport (φ : ℝ → ℂ) ⊆ Ioo l r :=
      (tsupport_comp_subset (show ((0 : ℝ) : ℂ) = 0 by norm_num) u).trans hUs
    have hfc : Integrable (fun x : ℝ => φ x * f x) :=
      (φ.continuous.mul hf).integrable_of_hasCompactSupport hf₀.mul_right
    have hgc : Integrable (fun x : ℝ => φ x * g x) :=
      (φ.continuous.mul hg).integrable_of_hasCompactSupport hf₀.mul_right
    change (∫ x : ℝ, φ x * (f x - g x)) = 0
    simp_rw [mul_sub]
    rw [integral_sub hfc hgc, h φ hf₀ hφ, sub_self]
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ isOpen_Ioo hf.continuousOn hg.continuousOn
  change ∀ᵐ x : ℝ ∂(volume.restrict (Ioo l r)), f x = g x
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact hAE.mono fun x hx hxs => sub_eq_zero.mp (hx hxs)

/-- If the weak derivative of order m of a continuous function vanishes on
an open interval, the function agrees there with a polynomial supported
on degrees strictly below m. -/
theorem exists_local_polynomial_of_weak_iteratedDeriv_zero
    (f : ℝ → ℂ) (hf : Continuous f) (l r : ℝ) (m : ℕ)
    (hWeak : ∀ ψ : SchwartzMap ℝ ℂ, HasCompactSupport ψ →
      tsupport (ψ : ℝ → ℂ) ⊆ Ioo l r →
      (∫ x : ℝ, iteratedDeriv m ψ x * f x) = 0) :
    ∃ c : Fin m → ℂ, EqOn f (fun x : ℝ => ∑ i, c i * (x : ℂ) ^ (i : ℕ)) (Ioo l r) := by
  classical
  let X := compactSchwartzIntervalSubmodule l r
  let T := compactSchwartzIntervalIntegral (l := l) (r := r) f hf
  let p (i : Fin m) (x : ℝ) : ℂ := (x : ℂ) ^ (i : ℕ)
  have hp (i : Fin m) : Continuous (p i) := Complex.ofRealCLM.continuous.pow _
  let M : X →ₗ[ℂ] (Fin m → ℂ) :=
    LinearMap.pi (fun i => compactSchwartzIntervalIntegral (p i) (hp i))
  have hK : LinearMap.ker M ≤ LinearMap.ker T := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    have hMom (k : ℕ) (hk : k < m) :
        (∫ x : ℝ, (x : ℂ) ^ k * φ.val x) = 0 := by
      have h := congrFun hφ (⟨k, hk⟩ : Fin m)
      change (∫ x : ℝ, φ.val x * (x : ℂ) ^ k) = 0 at h
      simpa only [mul_comm] using h
    obtain ⟨ψ, hψC, hψS, hD⟩ :=
      exists_schwartz_iterated_antiderivative_of_zero_moments_on_Ioo l r m _
        (compactSchwartzInterval_hasCompactSupport φ) φ.property hMom
    change (∫ x : ℝ, φ.val x * f x) = 0
    rw [← hD]
    simp_rw [schwartz_iterate_lineDeriv_one_apply]
    exact hWeak ψ hψC hψS
  let TQ := (LinearMap.ker M).liftQ T hK
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range M)
  let F : (Fin m → ℂ) →ₗ[ℂ] ℂ :=
    TQ.comp (M.quotKerEquivRange.symm.toLinearMap.comp ((LinearMap.range M).projectionOnto W hW))
  have hF (φ : X) : F (M φ) = T φ := by
    let v : LinearMap.range M := ⟨M φ, LinearMap.mem_range_self M φ⟩
    change TQ (M.quotKerEquivRange.symm ((LinearMap.range M).projectionOnto W hW (v : Fin m → ℂ))) = _
    rw [Submodule.projectionOnto_apply_left, M.quotKerEquivRange_symm_apply_image]
    rfl
  let c (i : Fin m) := F (Pi.basisFun ℂ (Fin m) i)
  have hLinear (v : Fin m → ℂ) : F v = ∑ i, c i * v i := by
    have hv := congrArg F ((Pi.basisFun ℂ (Fin m)).sum_repr v)
    simpa only [map_sum, map_smul, Pi.basisFun_repr, smul_eq_mul, mul_comm, c] using hv.symm
  refine ⟨c, continuous_eqOn_Ioo_of_schwartz_integral_eq _ _ hf
    (continuous_finsetSum _ fun i _ => continuous_const.mul (hp i)) l r ?_⟩
  intro φ hφC hφ
  let φ₀ : X := ⟨φ, hφ⟩
  calc
    (∫ x : ℝ, φ x * f x) = ∑ i, c i * (∫ x : ℝ, φ x * p i x) := by
      exact (hF φ₀).symm.trans (hLinear (M φ₀))
    _ = ∫ x : ℝ, φ x * ∑ i, c i * (x : ℂ) ^ (i : ℕ) := by
      simp_rw [Finset.mul_sum, mul_left_comm (φ _)]
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul, p]
      · intro i _
        exact ((φ.continuous.mul (hp i)).integrable_of_hasCompactSupport hφC.mul_right).const_mul _

end
end MeyerGeneralProblem
