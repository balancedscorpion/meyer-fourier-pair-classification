module

public import MeyerGeneralProblem.Distribution.ExponentialPhaseClosure
public import MeyerGeneralProblem.Cardinal.Adaptive.TorusFlowDensity
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section

/-!
# Phase nonvanishing on the full original frequency torus

An integral basis of the spectral module identifies its full phase
torus. The real frequency flow is dense because the frequency map
is injective. Real-rootedness thus gives the nonvanishing of every
torus phase at each off-real height.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open Adaptive

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

theorem frequencyMap_eq_basis_sum (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (m : G) :
    L m = ∑ i, (b.repr m i : ℝ) * L (b i) := by
  have h := congrArg L (b.sum_repr m)
  rw [map_sum] at h
  simpa only [map_zsmul, zsmul_eq_mul] using h.symm

/-- The continuous torus character associated to a label in the original module. -/
def basisTorusCharacter (b : Module.Basis ι ℤ G) (m : G) : C(UnitAddTorus ι, ℂ) :=
  UnitAddTorus.mFourier fun i => b.repr m i

theorem basisTorusCharacter_flow (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (m : G) (x : ℝ) :
    basisTorusCharacter b m (torusLinearFlow (fun i => L (b i)) x) = combModulationCharacter (L m) x := by
  unfold basisTorusCharacter
  rw [mFourier_torusLinearFlow, ← frequencyMap_eq_basis_sum b L m,
    fourier_coe_apply, combModulationCharacter_eq_exp]
  simp only [Int.cast_one, Complex.ofReal_one, mul_one, div_one, Complex.ofReal_mul]
  congr 1
  ring

theorem basisTorusCharacter_add_phase (b : Module.Basis ι ℤ G) (m : G)
    (θ φ : UnitAddTorus ι) :
    basisTorusCharacter b m (θ + φ) = basisTorusCharacter b m θ * basisTorusCharacter b m φ :=
  mFourier_point_add _ _ _

/-- The real flow on a finite basis is dense whenever its frequency map is injective. -/
theorem basis_frequencyFlow_denseRange
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L) :
    DenseRange (torusLinearFlow (fun i => L (b i))) := by
  apply torusLinearFlow_denseRange
  intro k hk
  let m := b.equivFun.symm k
  have hm (i : ι) : b.repr m i = k i := by
    have he := congrFun (b.equivFun.apply_symm_apply k) i
    simpa only [Module.Basis.equivFun_apply] using he
  have hx : L m = 0 := by
    rw [frequencyMap_eq_basis_sum b L m]
    simpa only [hm] using hk
  have hz : m = 0 := hL (hx.trans (map_zero L).symm)
  funext i
  simp [← hm i, hz]

/-- Every torus coefficient vector of the original labels is in the closure of the translation vectors. -/
theorem basisTorusCoefficients_mem_translationClosure
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (p : G →₀ ℂ) (θ : UnitAddTorus ι) :
    (fun m : p.support => p m * basisTorusCharacter b m θ) ∈
      closure (range fun x : ℝ => fun m : p.support => p m * combModulationCharacter (L m) x) := by
  let f (φ : UnitAddTorus ι) (m : p.support) := p m * basisTorusCharacter b m φ
  have hf : Continuous f := continuous_pi fun m =>
    continuous_const.mul (basisTorusCharacter b m).continuous
  let orbit := torusLinearFlow (fun i => L (b i))
  have hθ : θ ∈ closure (range orbit) := basis_frequencyFlow_denseRange b L hL θ
  have h := image_closure_subset_closure_image hf ⟨θ, hθ, rfl⟩
  rw [← range_comp] at h
  change f θ ∈ closure (range (f ∘ orbit)) at h
  have heq (x : ℝ) : f (orbit x) = fun m : p.support => p m * combModulationCharacter (L m) x := by
    funext m
    change p m * basisTorusCharacter b m (orbit x) = _
    rw [basisTorusCharacter_flow]
  simpa only [Function.comp_def, heq] using h

/-- A real-rooted finite exponential polynomial has no off-real zero at any
phase of the full torus of the original spectral module. -/
theorem realRooted_exponentialSum_basisTorus_ne_zero
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (p : G →₀ ℂ) (hp : p ≠ 0)
    (hroot : ∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L p z ≠ 0)
    (θ : UnitAddTorus ι) (z : ℂ) (hz : z.im ≠ 0) :
    (∑ m ∈ p.support, p m * basisTorusCharacter b m θ *
        Complex.exp (2 * Real.pi * Complex.I * (L m : ℂ) * z)) ≠ 0 := by
  have hne : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  obtain ⟨m, hm⟩ := hne
  have h := phaseClosure_exponentialSum_ne_zero_of_im_ne_zero
    (fun m : p.support => L m) (hL.comp Subtype.coe_injective) (fun m => p m)
    (fun m : p.support => p m * basisTorusCharacter b m θ)
    ⟨⟨m, hm⟩, Finsupp.mem_support_iff.mp hm⟩
    (fun z h => by rw [finiteEntireExponentialSum_original_support]; exact hroot z h)
    (basisTorusCoefficients_mem_translationClosure b L hL p θ) z hz
  unfold finiteEntireExponentialSum at h
  rwa [p.support.sum_coe_sort (fun m : G => p m * basisTorusCharacter b m θ *
    Complex.exp (2 * Real.pi * Complex.I * (L m : ℂ) * z))] at h

end

end MeyerGeneralProblem
