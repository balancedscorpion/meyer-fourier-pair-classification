module

public import MeyerGeneralProblem.Distribution.LocalPrincipalPart

@[expose] public section

/-!
# Exact analytic equations for principal-part rows

Clearing a denominator of order `m` converts its Laurent principal part to
the first `m` Taylor coefficients after dividing the numerator by the
analytic unit of the denominator.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

private theorem iteratedDeriv_centered_power_complex (a : ℂ) (j d : ℕ) :
    iteratedDeriv j (fun z : ℂ => (z - a) ^ d) a =
      if j = d then (d.factorial : ℂ) else 0 := by
  have h := congrFun (iteratedDeriv_comp_sub_const j (fun z : ℂ => z ^ d) a) a
  rw [sub_self, iteratedDeriv_fun_pow_zero] at h
  by_cases hEq : j = d <;> simpa [hEq] using h

/-- For the actual principal part of a quotient, the rows excluding
poles of order greater than `m - q` are the first `q` numerator
derivative equations. Here `m` is the analytic order of the denominator. -/
theorem quotientPrincipalPart_rows_iff_numeratorDerivatives
    (f p : ℂ → ℂ) (a : ℂ) (hf : AnalyticAt ℂ f a) (hp : AnalyticAt ℂ p a)
    (hp' : analyticOrderAt p a ≠ ⊤)
    (r : ℕ → ℂ) (H : ℂ → ℂ) (hH : AnalyticAt ℂ H a)
    (he : (fun z => f z / p z) =ᶠ[𝓝[≠] a]
      fun z => (∑ k ∈ Finset.range (analyticOrderNatAt p a),
        r k * ((z - a)⁻¹) ^ (k + 1)) + H z)
    (q : ℕ) (hq : q ≤ analyticOrderNatAt p a) :
    (∀ k < analyticOrderNatAt p a, analyticOrderNatAt p a - (k + 1) < q → r k = 0) ↔
      ∀ j < q, iteratedDeriv j f a = 0 := by
  classical
  let m := analyticOrderNatAt p a
  obtain ⟨u, hu, hnu, hfactor⟩ := hp.analyticOrderAt_ne_top.mp hp'
  let P (z : ℂ) := ∑ k ∈ Finset.range m, r k * (z - a) ^ (m - (k + 1))
  let W (z : ℂ) := (z - a) ^ m * H z
  let g (z : ℂ) := P z + W z
  have hterm (k : ℕ) : AnalyticAt ℂ (fun z : ℂ => r k * (z - a) ^ (m - (k + 1))) a :=
    by fun_prop
  have hP : AnalyticAt ℂ P a := by
    exact Finset.analyticAt_fun_sum _ (fun k _ => hterm k)
  have hW : AnalyticAt ℂ W a := by
    exact (show AnalyticAt ℂ (fun z : ℂ => (z - a) ^ m) a by fun_prop).mul hH
  have hg : AnalyticAt ℂ g a := hP.add hW
  have hu' : ∀ᶠ z in 𝓝 a, u z ≠ 0 := hu.continuousAt.eventually_ne hnu
  have heq : f =ᶠ[𝓝[≠] a] fun z => u z * g z := by
    filter_upwards [he, hfactor.filter_mono nhdsWithin_le_nhds,
      hu'.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin (s := ({a} : Set ℂ)ᶜ)] with z hez hpz huz hz
    have hz' : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
    change p z = (z - a) ^ m * u z at hpz
    have hpne : p z ≠ 0 := by rw [hpz]; exact mul_ne_zero (pow_ne_zero _ hz') huz
    have hcoeff (k : ℕ) (hk : k ∈ Finset.range m) :
        (r k * ((z - a)⁻¹) ^ (k + 1)) * (z - a) ^ m =
          r k * (z - a) ^ (m - (k + 1)) := by
      have hm : k + 1 ≤ m := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      have hpow : (z - a) ^ m * ((z - a)⁻¹) ^ (k + 1) = (z - a) ^ (m - (k + 1)) := by
        calc
          _ = (z - a) ^ (m - (k + 1)) * ((z - a) ^ (k + 1) * ((z - a)⁻¹) ^ (k + 1)) := by
            rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
          _ = _ := by rw [← mul_pow, mul_inv_cancel₀ hz', one_pow, mul_one]
      calc
        _ = r k * ((z - a) ^ m * ((z - a)⁻¹) ^ (k + 1)) := by ac_rfl
        _ = _ := by rw [hpow]
    calc
      f z = (f z / p z) * p z := (div_mul_cancel₀ _ hpne).symm
      _ = (∑ k ∈ Finset.range m, r k * ((z - a)⁻¹) ^ (k + 1) + H z) *
          ((z - a) ^ m * u z) := by rw [hez, hpz]
      _ = u z * ((∑ k ∈ Finset.range m, r k * (z - a) ^ (m - (k + 1))) + W z) := by
        rw [← mul_assoc, add_mul, Finset.sum_mul,
          Finset.sum_congr rfl hcoeff]
        dsimp [W]
        ring
      _ = _ := rfl
  have hat : f a = u a * g a :=
    tendsto_nhds_unique_of_eventuallyEq hf.continuousAt.continuousWithinAt
      (hu.mul hg).continuousAt.continuousWithinAt heq
  have heq' : f =ᶠ[𝓝 a] fun z => u z * g z := by
    filter_upwards [eventually_nhdsWithin_iff.mp heq] with z hz
    by_cases hza : z = a
    · simpa [hza] using hat
    · exact hz (by simpa using hza)
  have horder : analyticOrderAt f a = analyticOrderAt g a := by
    rw [analyticOrderAt_congr heq']
    change analyticOrderAt (u * g) a = _
    rw [analyticOrderAt_mul hu hg, hu.analyticOrderAt_eq_zero.mpr hnu, zero_add]
  have hWorder : (m : ℕ∞) ≤ analyticOrderAt W a := by
    apply (natCast_le_analyticOrderAt hW).mpr
    exact ⟨H, hH, Eventually.of_forall fun _ => rfl⟩
  have hder (j : ℕ) (hj : j < m) :
      iteratedDeriv j g a = r (m - (j + 1)) * (j.factorial : ℂ) := by
    change iteratedDeriv j (P + W) a = _
    have hw := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hW).mp hWorder j hj
    rw [iteratedDeriv_add hP.contDiffAt hW.contDiffAt, hw, add_zero]
    dsimp [P]
    rw [iteratedDeriv_fun_sum (fun k _ => (hterm k).contDiffAt)]
    simp only [iteratedDeriv_const_mul_field, iteratedDeriv_centered_power_complex]
    rw [Finset.sum_eq_single (m - (j + 1))]
    · rw [show m - (m - (j + 1) + 1) = j by omega, ite_eq_left rfl]
    · intro k hk hne
      rw [Finset.mem_range] at hk
      rw [ite_eq_right (show j ≠ m - (k + 1) by omega), mul_zero]
    · intro hk
      exact False.elim (hk (Finset.mem_range.mpr (by omega)))
  rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf, horder,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
  change (∀ k < m, m - (k + 1) < q → r k = 0) ↔ _
  change q ≤ m at hq
  constructor
  · intro hr j hj
    rw [hder j (by omega), hr _ (by omega) (by omega), zero_mul]
  · intro hd k hk hq'
    have h := hd (m - (k + 1)) hq'
    rw [hder _ (by omega), show m - (m - (k + 1) + 1) = k by omega] at h
    exact (mul_eq_zero.mp h).resolve_right (by exact_mod_cast Nat.factorial_ne_zero _)

end

end MeyerGeneralProblem
