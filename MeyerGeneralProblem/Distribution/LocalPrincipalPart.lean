module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Finite principal parts of local analytic quotients

Analytic vanishing-order factorization extracts the local unit from the
denominator. Repeated analytic division by the coordinate gives the
actual finite principal part and an analytic remainder.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

private theorem analyticAt_exists_linearTaylorTail (f : ℂ → ℂ) (a : ℂ) (hf : AnalyticAt ℂ f a) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      f =ᶠ[𝓝 a] fun z => f a + (z - a) * g z := by
  let u (z : ℂ) := f z - f a
  have hu : AnalyticAt ℂ u a := hf.sub analyticAt_const
  by_cases h : analyticOrderAt u a = ⊤
  · refine ⟨0, analyticAt_const, ?_⟩
    filter_upwards [analyticOrderAt_eq_top.mp h] with z hz
    change f z - f a = 0 at hz
    simpa using sub_eq_zero.mp hz
  obtain ⟨g, hg, _, he⟩ := hu.analyticOrderAt_ne_top.mp h
  let m := analyticOrderNatAt u a
  have hm : 0 < m := ENat.toNat_pos (hu.analyticOrderAt_ne_zero.mpr (sub_self _)) h
  let D (z : ℂ) := (z - a) ^ (m - 1) * g z
  have hlin : AnalyticAt ℂ (fun z => z - a) a := by fun_prop
  refine ⟨D, (hlin.pow _).mul hg, ?_⟩
  filter_upwards [he] with z hz
  change f z - f a = (z - a) ^ m * g z at hz
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [← hm', pow_succ'] at hz
  dsimp [D]
  linear_combination hz

private theorem analyticAt_exists_principalPart_invPower (f : ℂ → ℂ) (a : ℂ)
    (hf : AnalyticAt ℂ f a) (m : ℕ) :
    ∃ (r : ℕ → ℂ) (H : ℂ → ℂ), AnalyticAt ℂ H a ∧
      (fun z => f z * ((z - a)⁻¹) ^ m) =ᶠ[𝓝[≠] a]
        fun z => (∑ j ∈ Finset.range m, r j * ((z - a)⁻¹) ^ (j + 1)) + H z := by
  classical
  induction m generalizing f with
  | zero =>
    exact ⟨0, f, hf, Eventually.of_forall fun z => by simp⟩
  | succ m ih =>
    obtain ⟨D, hD, he⟩ := analyticAt_exists_linearTaylorTail f a hf
    obtain ⟨r, H, hH, hr⟩ := ih D hD
    refine ⟨fun j => if j = m then f a else r j, H, hH, ?_⟩
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, hr,
      self_mem_nhdsWithin (s := ({a} : Set ℂ)ᶜ)] with z hz htail hn
    have hne : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hn)
    have hstep : f z * ((z - a)⁻¹) ^ (m + 1) =
        D z * ((z - a)⁻¹) ^ m + f a * ((z - a)⁻¹) ^ (m + 1) := by
      rw [hz, add_mul]
      have hc : (z - a) * D z * ((z - a)⁻¹) ^ (m + 1) =
          D z * ((z - a)⁻¹) ^ m := by
        rw [pow_succ]
        calc
          _ = ((z - a) * (z - a)⁻¹) * (D z * ((z - a)⁻¹) ^ m) := by ac_rfl
          _ = _ := by rw [mul_inv_cancel₀ hne, one_mul]
      rw [hc, add_comm]
    simp only [hstep, htail, Finset.sum_range_succ]
    rw [show (∑ j ∈ Finset.range m, (if j = m then f a else r j) * ((z - a)⁻¹) ^ (j + 1)) =
      ∑ j ∈ Finset.range m, r j * ((z - a)⁻¹) ^ (j + 1) by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ite_eq_right (Nat.ne_of_lt (Finset.mem_range.mp hj))]]
    abel

/-- The quotient of two analytic functions has its actual finite principal
part, bounded by the denominator's analytic multiplicity. -/
theorem analyticAt_quotient_exists_local_principalPart
    (f p : ℂ → ℂ) (a : ℂ) (hf : AnalyticAt ℂ f a) (hp : AnalyticAt ℂ p a)
    (hp' : analyticOrderAt p a ≠ ⊤) :
    ∃ (r : ℕ → ℂ) (H : ℂ → ℂ), AnalyticAt ℂ H a ∧
      (fun z => f z / p z) =ᶠ[𝓝[≠] a]
        fun z => (∑ j ∈ Finset.range (analyticOrderNatAt p a),
          r j * ((z - a)⁻¹) ^ (j + 1)) + H z := by
  obtain ⟨u, hu, hnu, hfactor⟩ := hp.analyticOrderAt_ne_top.mp hp'
  have ha : AnalyticAt ℂ (fun z => f z / u z) a := hf.div hu hnu
  obtain ⟨r, H, hH, he⟩ := analyticAt_exists_principalPart_invPower
    (fun z => f z / u z) a ha (analyticOrderNatAt p a)
  refine ⟨r, H, hH, ?_⟩
  filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds, he] with z hs hr
  change p z = (z - a) ^ analyticOrderNatAt p a * u z at hs
  rw [hs, ← hr, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, inv_pow, mul_assoc]

end

end MeyerGeneralProblem
