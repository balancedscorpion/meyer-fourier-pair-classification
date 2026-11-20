module

public import MeyerGeneralProblem.Carrier.EntireRealZeroCounts
public import MeyerGeneralProblem.Cardinal.Strong.OriginalPairNumerator

@[expose] public section

/-!
# Relatively separated real zeros of a finite exponential sum

After division by the lowest-frequency character, the constant
coefficient dominates on a sufficiently high horizontal line. Jensen
then gives the required uniform unit-window bound without a lower
bound on gaps between the real zeros.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

variable {G : Type*} [AddCommGroup G]

/-- The complex extension of the literal exponential symbol. -/
def complexExponentialSum (a : G → ℝ) (p : G →₀ ℂ) (z : ℂ) : ℂ :=
  ∑ m ∈ p.support, p m * Complex.exp (2 * Real.pi * Complex.I * (a m : ℂ) * z)

private theorem norm_complexExponentialTerm (a : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * z)‖ =
      Real.exp (-(2 * Real.pi * a) * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- Real evaluation agrees with the original action's sign convention. -/
theorem complexExponentialSum_ofReal (L : G →+ ℝ) (p : G →₀ ℂ) (x : ℝ) :
    complexExponentialSum L p (x : ℂ) = annihilatorExponentialSymbol L p x := by
  simp only [complexExponentialSum, annihilatorExponentialSymbol, combModulationCharacter_eq_exp]

omit [AddCommGroup G] in
theorem complexExponentialSum_entire (a : G → ℝ) (p : G →₀ ℂ) :
    AnalyticOnNhd ℂ (complexExponentialSum a p) univ := by
  intro z _
  unfold complexExponentialSum
  fun_prop

private theorem complexExponentialSum_shift (L : G →+ ℝ) (p : G →₀ ℂ)
    (b : ℝ) (z : ℂ) :
    complexExponentialSum L p z =
      Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) * z) *
        complexExponentialSum (fun m => L m - b) p z := by
  unfold complexExponentialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem complexExponentialSum_analyticOrderAt_shift
    (L : G →+ ℝ) (p : G →₀ ℂ) (b : ℝ) (z : ℂ) :
    analyticOrderAt (complexExponentialSum L p) z =
      analyticOrderAt (complexExponentialSum (fun m => L m - b) p) z := by
  let E (w : ℂ) := Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) * w)
  have hE : AnalyticAt ℂ E z := by dsimp [E]; fun_prop
  have hf := complexExponentialSum_entire (fun m => L m - b) p z (mem_univ z)
  rw [show complexExponentialSum L p =
      E * complexExponentialSum (fun m => L m - b) p from
    funext (complexExponentialSum_shift L p b),
    analyticOrderAt_mul hE hf,
    hE.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _), zero_add]

private theorem normalizedExponentialSum_horizontal_dominance
    (L : G →+ ℝ) (p : G →₀ ℂ) (m₀ : G) (h₀ : p m₀ ≠ 0)
    (hmin : ∀ m ∈ p.support, m ≠ m₀ → L m₀ < L m) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ x : ℝ,
      ‖p m₀‖ / 2 ≤ ‖complexExponentialSum (fun m => L m - L m₀) p
        ((x : ℂ) + (Y : ℂ) * Complex.I)‖ := by
  classical
  let E := p.support.erase m₀
  let F (y : ℝ) := ∑ m ∈ E, ‖p m‖ * Real.exp (-(2 * Real.pi * (L m - L m₀)) * y)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hterm (m : G) (hm : m ∈ E) :
        Tendsto (fun y : ℝ => ‖p m‖ * Real.exp (-(2 * Real.pi * (L m - L m₀)) * y)) atTop (𝓝 0) := by
      have hm' := Finset.mem_erase.mp hm
      have hδ : 0 < L m - L m₀ := sub_pos.mpr (hmin m hm'.2 hm'.1)
      have hneg : -(2 * Real.pi * (L m - L m₀)) < 0 := neg_lt_zero.mpr (by positivity)
      have ht := Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_neg hneg).mpr tendsto_id)
      simpa only [Function.comp_apply, id_eq, mul_zero] using
        (tendsto_const_nhds (x := ‖p m‖)).mul ht
    simpa only [F, Finset.sum_const_zero] using tendsto_finsetSum E hterm
  have hc : 0 < ‖p m₀‖ / 2 := by
    exact div_pos (norm_pos_iff.mpr h₀) (by norm_num)
  obtain ⟨Y, hY, hFY⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (hlim.eventually (gt_mem_nhds hc))).exists
  refine ⟨Y, hY, fun x => ?_⟩
  let z : ℂ := (x : ℂ) + (Y : ℂ) * Complex.I
  let u : G → ℂ := fun m => p m * Complex.exp
    (2 * Real.pi * Complex.I * ((L m - L m₀ : ℝ) : ℂ) * z)
  let t : ℂ := ∑ m ∈ E, u m
  have hsplit : complexExponentialSum (fun m => L m - L m₀) p z = t + p m₀ := by
    change ∑ m ∈ p.support, u m = t + p m₀
    have hs := Finset.sum_erase_add p.support u (Finsupp.mem_support_iff.mpr h₀)
    simpa [t, E, u] using hs.symm
  have hsmall : ‖t‖ ≤ F Y := by
    apply (norm_sum_le E u).trans
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro m _
    simp only [u, norm_mul, norm_complexExponentialTerm]
    have hz : z.im = Y := by simp [z, Complex.mul_im]
    rw [hz]
  have h := norm_sub_le (complexExponentialSum (fun m => L m - L m₀) p z) t
  rw [hsplit, add_sub_cancel_left, ← hsplit] at h
  change ‖p m₀‖ / 2 ≤ ‖complexExponentialSum (fun m => L m - L m₀) p z‖
  linarith

/-- The real zero carrier of a nonzero finite pure exponential symbol
has a uniform window bound that counts the original analytic multiplicities. -/
theorem exists_exponentialSymbol_realZeroCarrier_multiplicity_bound
    (L : G →+ ℝ) (hL : Function.Injective L) (p : G →₀ ℂ) (hp : p ≠ 0) :
    ∃ S : LocallyFiniteCarrier,
      S.carrier = {x : ℝ | annihilatorExponentialSymbol L p x = 0} ∧
      ∃ K, UnitCellBound S K ∧ ∀ a : ℝ,
        ∑ x ∈ (S.finite_window a 1).toFinset,
          analyticOrderNatAt (complexExponentialSum L p) (x : ℂ) ≤ K := by
  classical
  obtain ⟨m₀, _, h₀, _, _, hmin, _⟩ := finiteAnnihilator_extrema L hL p hp
  let a (m : G) := L m - L m₀
  let f := complexExponentialSum a p
  let κ := ‖p m₀‖ / 2
  have hκ : 0 < κ := div_pos (norm_pos_iff.mpr h₀) (by norm_num)
  obtain ⟨Y, hY, hlo⟩ := normalizedExponentialSum_horizontal_dominance L p m₀ h₀ hmin
  have hne : ∃ c, f c ≠ 0 :=
    ⟨(Y : ℂ) * Complex.I, by
      have h := hlo 0
      rw [Complex.ofReal_zero, zero_add] at h
      exact norm_ne_zero_iff.mp (ne_of_gt (hκ.trans_le h))⟩
  let S := entireRealZeroCarrier f (complexExponentialSum_entire a p) hne
  refine ⟨S, ?_, ?_⟩
  · ext x
    change f (x : ℂ) = 0 ↔ annihilatorExponentialSymbol L p x = 0
    rw [← complexExponentialSum_ofReal]
    rw [complexExponentialSum_shift L p (L m₀) (x : ℂ)]
    exact ⟨fun h => mul_eq_zero.mpr (Or.inr h),
      fun h => (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)⟩
  · let M := 1 + ∑ m ∈ p.support, ‖p m‖ * Real.exp (2 * Real.pi * |a m| * (5 * Y))
    have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
    have hupper (z : ℂ) (hz : |z.im| ≤ 5 * Y) : ‖f z‖ ≤ M := by
      change ‖∑ m ∈ p.support, p m * Complex.exp (2 * Real.pi * Complex.I * (a m : ℂ) * z)‖ ≤ M
      calc
        _ ≤ ∑ m ∈ p.support, ‖p m * Complex.exp (2 * Real.pi * Complex.I * (a m : ℂ) * z)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ m ∈ p.support, ‖p m‖ * Real.exp (2 * Real.pi * |a m| * (5 * Y)) := by
          apply Finset.sum_le_sum
          intro m _
          rw [norm_mul, norm_complexExponentialTerm]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply Real.exp_le_exp.mpr
          have hm : -(a m * z.im) ≤ |a m| * (5 * Y) :=
            (show -(a m * z.im) ≤ |a m| * |z.im| by
              rw [← abs_mul]
              exact neg_le_abs _).trans
                (mul_le_mul_of_nonneg_left hz (abs_nonneg _))
          calc
            _ = (2 * Real.pi) * (-(a m * z.im)) := by ring
            _ ≤ (2 * Real.pi) * (|a m| * (5 * Y)) :=
              mul_le_mul_of_nonneg_left hm (by positivity)
            _ = _ := by ring
        _ ≤ M := le_add_of_nonneg_left zero_le_one
    obtain ⟨K, hK⟩ := exists_entireRealZeroCarrier_multiplicity_bound f
      (complexExponentialSum_entire a p) hne Y M κ hY hM hκ hupper hlo
    refine ⟨K, ?_, ?_⟩
    · intro n
      rw [LocallyFiniteCarrier.windowCount_eq_toFinset_card]
      refine (le_trans ?_ (hK n))
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro x hx
      have hz : f (x : ℂ) = 0 := ((S.finite_window n 1).mem_toFinset.mp hx).1
      apply ENat.toNat_pos
      · exact ((complexExponentialSum_entire a p) _ (mem_univ _)).analyticOrderAt_ne_zero.mpr hz
      · exact entire_analyticOrderAt_ne_top_of_exists_ne_zero f (complexExponentialSum_entire a p) hne x
    · intro x
      simp only [analyticOrderNatAt, complexExponentialSum_analyticOrderAt_shift L p (L m₀)]
      exact hK x

/-- The literal real zero carrier also has bounded counts of distinct sites. -/
theorem exists_exponentialSymbol_realZeroCarrier_unitCellBound
    (L : G →+ ℝ) (hL : Function.Injective L) (p : G →₀ ℂ) (hp : p ≠ 0) :
    ∃ S : LocallyFiniteCarrier,
      S.carrier = {x : ℝ | annihilatorExponentialSymbol L p x = 0} ∧
      ∃ K, UnitCellBound S K := by
  obtain ⟨S, hS, K, hK, _⟩ := exists_exponentialSymbol_realZeroCarrier_multiplicity_bound L hL p hp
  exact ⟨S, hS, K, hK⟩

/-- Any locally finite carrier on which a nonzero exponential symbol
vanishes has bounded local counts. -/
theorem exists_unitCellBound_of_exponentialSymbol_vanishes
    (L : G →+ ℝ) (hL : Function.Injective L) (p : G →₀ ℂ) (hp : p ≠ 0)
    (A : LocallyFiniteCarrier) (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) :
    ∃ K, UnitCellBound A K := by
  obtain ⟨S, hS, K, hK⟩ := exists_exponentialSymbol_realZeroCarrier_unitCellBound L hL p hp
  have hsub : A.carrier ⊆ S.carrier := by
    rw [hS]
    exact hA
  exact ⟨K, fun n => (LocallyFiniteCarrier.windowCount_mono_carrier hsub n 1).trans (hK n)⟩

end

end MeyerGeneralProblem
