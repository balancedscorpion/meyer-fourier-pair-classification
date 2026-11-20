module

public import MeyerGeneralProblem.Distribution.BroadCauchyKernel
public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity

@[expose] public section

/-!
# Compact Cauchy tests away from their support

The pole may be real wherever the compact multiplier vanishes locally.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

/-- The pole domain for the action of a fixed compact Schwartz multiplier. -/
def compactCauchyPoleDomain (χ : SchwartzMap ℝ ℂ) : Set ℂ :=
  (Complex.ofReal '' tsupport (χ : ℝ → ℂ))ᶜ

theorem isOpen_compactCauchyPoleDomain (χ : SchwartzMap ℝ ℂ)
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) : IsOpen (compactCauchyPoleDomain χ) :=
  (hχ.image Complex.continuous_ofReal).isClosed.isOpen_compl

private theorem sub_ne_zero_of_compactCauchyPoleDomain {χ : SchwartzMap ℝ ℂ} {z : ℂ}
    (hz : z ∈ compactCauchyPoleDomain χ) {x : ℝ} (hx : x ∈ tsupport (χ : ℝ → ℂ)) :
    (x : ℂ) - z ≠ 0 := fun h => hz ⟨x, hx, sub_eq_zero.mp h⟩

private theorem eventuallyEq_zero_of_notMem_tsupport {χ : SchwartzMap ℝ ℂ} {x : ℝ}
    (hx : x ∉ tsupport (χ : ℝ → ℂ)) : (χ : ℝ → ℂ) =ᶠ[𝓝 x] 0 := by
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
  by_contra hy'
  exact hy (subset_closure hy')

/-- On the pole domain this is the literal compact product, including at
real poles outside the support of the multiplier. -/
def compactCauchySchwartzTest (χ : SchwartzMap ℝ ℂ)
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (m : ℕ) (z : ℂ) : SchwartzMap ℝ ℂ := by
  classical
  exact if hz : z ∈ compactCauchyPoleDomain χ then
    (hχ.mul_right (f' := broadCauchyKernel m z)).toSchwartzMap <| contDiff_iff_contDiffAt.mpr <| by
      intro x
      by_cases hx : x ∈ tsupport (χ : ℝ → ℂ)
      · exact (χ.smooth ⊤).contDiffAt.mul
          (contDiffAt_broadCauchyKernel_test_of_sub_ne_zero m z x (sub_ne_zero_of_compactCauchyPoleDomain hz hx) ⊤)
      · have he : ((χ : ℝ → ℂ) * broadCauchyKernel m z) =ᶠ[𝓝 x] (fun _ => 0) := by
          filter_upwards [eventuallyEq_zero_of_notMem_tsupport hx] with y hy
          simp only [Pi.mul_apply, show χ y = 0 from hy, zero_mul]
        exact contDiffAt_const.congr_of_eventuallyEq he
  else 0

theorem compactCauchySchwartzTest_apply {χ : SchwartzMap ℝ ℂ}
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (m : ℕ) {z : ℂ}
    (hz : z ∈ compactCauchyPoleDomain χ) (x : ℝ) :
    compactCauchySchwartzTest χ hχ m z x = χ x * broadCauchyKernel m z x := by
  rw [compactCauchySchwartzTest, dite_eq_left hz]
  rfl

theorem iteratedDeriv_compactCauchySchwartzTest_eq_zero {χ : SchwartzMap ℝ ℂ}
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (m j : ℕ) {z : ℂ}
    (hz : z ∈ compactCauchyPoleDomain χ) {x : ℝ} (hx : x ∉ tsupport (χ : ℝ → ℂ)) :
    iteratedDeriv j (compactCauchySchwartzTest χ hχ m z) x = 0 := by
  have he : (compactCauchySchwartzTest χ hχ m z : ℝ → ℂ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [eventuallyEq_zero_of_notMem_tsupport hx] with y hy
    simp [compactCauchySchwartzTest_apply hχ m hz, show χ y = 0 from hy]
  rw [he.iteratedDeriv_eq j]
  simp

theorem iteratedDeriv_compactCauchySchwartzTest {χ : SchwartzMap ℝ ℂ}
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) (m j : ℕ) {z : ℂ}
    (hz : z ∈ compactCauchyPoleDomain χ) {x : ℝ} (hx : x ∈ tsupport (χ : ℝ → ℂ)) :
    iteratedDeriv j (compactCauchySchwartzTest χ hχ m z) x =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i χ x *
        ((-1 : ℂ) ^ (j - i) * (m.ascFactorial (j - i) : ℂ) * broadCauchyKernel (m + (j - i)) z x) := by
  have hfun : (compactCauchySchwartzTest χ hχ m z : ℝ → ℂ) =
      (χ : ℝ → ℂ) * broadCauchyKernel m z := funext (compactCauchySchwartzTest_apply hχ m hz)
  have hlocal := sub_ne_zero_of_compactCauchyPoleDomain hz hx
  rw [hfun, iteratedDeriv_mul (χ.smooth j).contDiffAt
    (contDiffAt_broadCauchyKernel_test_of_sub_ne_zero m z x hlocal j)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [iteratedDeriv_broadCauchyKernel_test_of_sub_ne_zero _ _ _ _ hlocal]

end

end MeyerGeneralProblem
