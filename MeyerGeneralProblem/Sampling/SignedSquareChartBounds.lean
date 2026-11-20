module

public import MeyerGeneralProblem.Sampling.PureDerivativeEnergy
public import MeyerGeneralProblem.Sampling.KNSGraphSpaceSmooth

@[expose] public section

/-!
# Uniform same-order smooth cutoff-chart energy

At each fixed order and radius, one positive constant is chosen before the
smooth input, sign and derivative index. The actual cutoff chart and its pure
derivatives are bounded using only the genuine same-order endpoint energies.
The exact smooth KNS graph norm conversion retains its Fourier factor.
-/

namespace MeyerGeneralProblem.SignedSquareSmoothBounds

noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators

/-- Reflections preserve the actual whole-line derivative energy. -/
theorem integral_norm_ray (u : ℝ → ℂ) {ε : ℝ} (hε : ε^2 = 1) :
    (∫ x : ℝ, ‖u (ε*x)‖^2) = ∫ x : ℝ, ‖u x‖^2 := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp only [one_mul]
  · simpa only [neg_one_mul] using integral_neg_eq_self (fun x : ℝ => ‖u x‖^2) volume

/-- Reflections preserve the actual even physical-moment energy. -/
theorem integral_weight_ray (k : ℕ) (u : ℝ → ℂ) {ε : ℝ} (hε : ε^2 = 1) :
    (∫ x : ℝ, x^(2*k) * ‖u (ε*x)‖^2) =
      ∫ x : ℝ, x^(2*k) * ‖u x‖^2 := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp only [one_mul]
  · simpa only [neg_one_mul, (even_two_mul k).neg_pow] using
      integral_neg_eq_self (fun x : ℝ => x^(2*k) * ‖u x‖^2) volume

/-- Square-integrability of a physical function gives integrable ray energy. -/
theorem integrable_norm_ray {u : ℝ → ℂ} (hu : MemLp u 2)
    {ε : ℝ} (hε : ε^2 = 1) : Integrable (fun x : ℝ => ‖u (ε*x)‖^2) := by
  have hi := integrable_norm_sq_of_memLp_complex hu
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simpa only [one_mul] using hi
  · simpa only [neg_one_mul] using hi.comp_neg

/-- The actual localized chart mass is controlled by the pure physical moment. -/
theorem chart_mass_le (k : ℕ) {R ε : ℝ} (hR : 2 ≤ R) (hε : ε^2 = 1)
    {f : ℝ → ℂ}
    (hW : Integrable (fun x : ℝ => x^(2*k) * ‖f x‖^2)) :
    (∫ s : ℝ, ‖signedSquareCutoffChart k R ε f s‖^2) ≤
      2 * ∫ x : ℝ, x^(2*k) * ‖f x‖^2 := by
  have hw : Integrable (fun x : ℝ => x^(2*k) * ‖f (ε*x)‖^2) := by
    rcases sq_eq_one_iff.mp hε with rfl | rfl
    · simpa only [one_mul] using hW
    · simpa only [neg_one_mul, (even_two_mul k).neg_pow] using hW.comp_neg
  have hw0 (x : ℝ) : 0 ≤ x^(2*k) * ‖f (ε*x)‖^2 := by
    rw [pow_mul]; positivity
  have hm := integral_signedSquareCutoffChart_mass k hR ε f
  have hle : (∫ x in Ioi (R/2), (signedSquareTailCutoff R (x^2))^2 *
      (x^(2*k) * ‖f (ε*x)‖^2)) ≤
        ∫ x in Ioi (R/2), x^(2*k) * ‖f (ε*x)‖^2 := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hw0 x)))
      hw.integrableOn
    apply Filter.Eventually.of_forall
    intro x
    have hc := signedSquareTailCutoff_mem_Icc R (x^2)
    have hc2 : (signedSquareTailCutoff R (x^2))^2 ≤ 1 := by nlinarith [hc.1, hc.2]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc2 (hw0 x)
  have hglobal := setIntegral_le_integral (s := Ioi (R/2)) hw
    (Filter.Eventually.of_forall hw0)
  rw [integral_weight_ray k f hε] at hglobal
  linarith

/-- The actual energy of any lower pure derivative is uniformly controlled
on either ray, without mixed regularity. -/
private theorem integral_deriv_ray_le (k : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2) (hD : MemLp (iteratedDeriv k f) 2)
    {ε : ℝ} (hε : ε^2 = 1) (j : ℕ) (hj : j ≤ k) :
    (∫ x : ℝ, ‖iteratedDeriv j f (ε*x)‖^2) ≤ ‖(MemLp.toLp (p := 2) _ hF)‖^2 + ‖(MemLp.toLp (p := 2) _ hD)‖^2 := by
  obtain ⟨hJ, hnJ⟩ := PureDerivativeEnergy.exists_lower_derivative_norm_sq_le k hf hF hD j hj
  rw [integral_norm_ray _ hε, integral_norm_sq_eq_toLp_norm_sq_complex hJ]
  exact hnJ

/-- The finite lower-jet sum has a uniform bound proportional to its actual number of terms. -/
private theorem integral_jet_sum_le (k : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2) (hD : MemLp (iteratedDeriv k f) 2)
    {ε : ℝ} (hε : ε^2 = 1) :
    (∫ x : ℝ, ∑ j ∈ Finset.range k, ‖iteratedDeriv j f (ε*x)‖^2) ≤
      (k : ℝ) * (‖(MemLp.toLp (p := 2) _ hF)‖^2 + ‖(MemLp.toLp (p := 2) _ hD)‖^2) := by
  have ht := memLp_iteratedDeriv_of_top_classical_derivative k hf hF hD
  rw [integral_finsetSum (Finset.range k) (fun j hj =>
    integrable_norm_ray (ht j (by have := Finset.mem_range.mp hj; omega)) hε)]
  calc
    _ ≤ ∑ j ∈ Finset.range k, (‖(MemLp.toLp (p := 2) _ hF)‖^2 + ‖(MemLp.toLp (p := 2) _ hD)‖^2) :=
      Finset.sum_le_sum (fun j hj =>
        integral_deriv_ray_le k hf hF hD hε j (by have := Finset.mem_range.mp hj; omega))
    _ = _ := by simp [mul_add]

set_option maxHeartbeats 2400000
/-- Every smooth cutoff-chart derivative through its graph order is bounded
by only the zeroth and two pure endpoint energies. The positive constant is
fixed before the sign, input and lower derivative index; the radius is fixed. -/
theorem exists_smooth_chart_bound (k : ℕ) {R : ℝ} (hR : 2 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), ε^2 = 1 → ∀ (f : ℝ → ℂ),
      ∀ (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2)
        (hD : MemLp (iteratedDeriv k f) 2),
      Integrable (fun x : ℝ => x^(2*k) * ‖f x‖^2) →
      ∀ j ≤ k, ∃ hJ : MemLp (iteratedDeriv j (signedSquareCutoffChart k R ε f)) 2,
        ‖(MemLp.toLp (p := 2) _ hJ)‖^2 ≤ C *
          (‖(MemLp.toLp (p := 2) _ hF)‖^2 + (∫ x : ℝ, x^(2*k) * ‖f x‖^2) + ‖(MemLp.toLp (p := 2) _ hD)‖^2) := by
  obtain ⟨Cs, hCs, htop⟩ := exists_integral_signedSquareCutoffChart_deriv_le k
    (by norm_num : (0 : ℝ) < 1) hR
  let a : ℝ := (1+1) / (4 : ℝ)^k
  let b : ℝ := 8 * signedSquareChartErrorConstant k 1 / R^2
  let A : ℝ := a + (b+Cs)*(k : ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg (mul_nonneg (by norm_num)
      (signedSquareChartErrorConstant_nonneg k (by norm_num))) (sq_nonneg R)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨2+2*A, by positivity, ?_⟩
  intro ε hε f hf hF hD hW
  let E : ℝ := ‖(MemLp.toLp (p := 2) _ hF)‖^2 + ‖(MemLp.toLp (p := 2) _ hD)‖^2
  let W : ℝ := ∫ x : ℝ, x^(2*k)*‖f x‖^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hW0 : 0 ≤ W := by
    apply integral_nonneg
    intro x
    change 0 ≤ x^(2*k) * ‖f x‖^2
    rw [pow_mul]
    positivity
  have ht := memLp_iteratedDeriv_of_top_classical_derivative k hf hF hD
  have hray : ∀ j ≤ k, Integrable (fun x : ℝ => ‖iteratedDeriv j f (ε*x)‖^2) :=
    fun j hj => integrable_norm_ray (ht j hj) hε
  let J : ℝ → ℝ := fun x => ∑ j ∈ Finset.range k, ‖iteratedDeriv j f (ε*x)‖^2
  have hJint : Integrable J := by
    apply integrable_finsetSum
    intro j hj
    exact hray j (by have := Finset.mem_range.mp hj; omega)
  have hJ0 (x : ℝ) : 0 ≤ J x :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∫ x : ℝ, J x) ≤ (k : ℝ)*E :=
    integral_jet_sum_le k hf hF hD hε
  have htoptail : (∫ x in Ioi (R/2), ‖iteratedDeriv k f (ε*x)‖^2) ≤ E :=
    (setIntegral_le_integral (hray k le_rfl)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).trans
      (integral_deriv_ray_le k hf hF hD hε k le_rfl)
  have hjettail : (∫ x in Ioi (R/2), J x) ≤ (k : ℝ)*E :=
    (setIntegral_le_integral hJint (Filter.Eventually.of_forall hJ0)).trans hsum
  have hjetshell : (∫ x in Icc (R/2) R, J x) ≤ (k : ℝ)*E :=
    (setIntegral_le_integral hJint (Filter.Eventually.of_forall hJ0)).trans hsum
  obtain ⟨hG, hGD⟩ := signedSquareCutoffChart_memLp_derivatives k hR hε hf hF hD hW
  have htG := (htop ε hε f hf hray).2
  have hmajor :
      a*(∫ x in Ioi (R/2), ‖iteratedDeriv k f (ε*x)‖^2) +
        b*(∫ x in Ioi (R/2), J x) + Cs*(∫ x in Icc (R/2) R, J x) ≤ A*E := by
    calc
      _ ≤ a*E + b*((k : ℝ)*E) + Cs*((k : ℝ)*E) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left htoptail ha)
          (mul_le_mul_of_nonneg_left hjettail hb))
          (mul_le_mul_of_nonneg_left hjetshell hCs.le)
      _ = _ := by dsimp [A]; ring
  have hnormtop : ‖(hGD k le_rfl).toLp‖^2 ≤ 2*A*E := by
    rw [← integral_norm_sq_eq_toLp_norm_sq_complex (hGD k le_rfl)]
    change (1/2 : ℝ) * _ ≤
      a*(∫ x in Ioi (R/2), ‖iteratedDeriv k f (ε*x)‖^2) +
        b*(∫ x in Ioi (R/2), J x) + Cs*(∫ x in Icc (R/2) R, J x) at htG
    linarith
  have hnormmass : ‖hG.toLp‖^2 ≤ 2*W := by
    rw [← integral_norm_sq_eq_toLp_norm_sq_complex hG]
    exact chart_mass_le k hR hε hW
  intro j hj
  obtain ⟨hLj, hnLj⟩ := PureDerivativeEnergy.exists_lower_derivative_norm_sq_le k
    (contDiff_signedSquareCutoffChart k (by linarith) ε hf) hG (hGD k le_rfl) j hj
  refine ⟨hLj, ?_⟩
  have hAW : 0 ≤ A*W := mul_nonneg hA hW0
  change _ ≤ (2+2*A) * (‖(MemLp.toLp (p := 2) _ hF)‖^2 + W + ‖(MemLp.toLp (p := 2) _ hD)‖^2)
  have heq : ‖(MemLp.toLp (p := 2) _ hF)‖^2 + W + ‖(MemLp.toLp (p := 2) _ hD)‖^2 = E+W := by dsimp [E]; ring
  rw [heq]
  nlinarith


end
end MeyerGeneralProblem.SignedSquareSmoothBounds

namespace MeyerGeneralProblem.SignedSquareSmoothGraphBounds

set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory
open scoped ContDiff

/-- The physical power coordinate has exactly the actual even-moment integral. -/
theorem power_integral_norm (k : ℕ) {f : ℝ → ℂ}
    (hW : MemLp (fun x : ℝ => (x : ℂ)^k * f x) 2) :
    Integrable (fun x : ℝ => x^(2*k)*‖f x‖^2) ∧
      (∫ x : ℝ, x^(2*k)*‖f x‖^2) = ‖(MemLp.toLp (p := 2) _ hW)‖^2 := by
  have he (x : ℝ) : x^(2*k)*‖f x‖^2 = ‖(x : ℂ)^k * f x‖^2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      ← pow_mul, Nat.mul_comm k 2, (even_two_mul k).pow_abs]
  constructor
  · simpa only [he] using integrable_norm_sq_of_memLp_complex hW
  · simp only [he]
    exact integral_norm_sq_eq_toLp_norm_sq_complex hW

/-- Pure smooth endpoint energy is bounded by the genuine same-order graph norm,
with the Fourier normalization retained in the order-dependent constant. -/
theorem energy_le_graph (k : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hF : MemLp f 2) (hW : MemLp (fun x : ℝ => (x : ℂ)^k*f x) 2)
    (hD : MemLp (iteratedDeriv k f) 2) :
    ‖(MemLp.toLp (p := 2) _ hF)‖^2 + ‖(MemLp.toLp (p := 2) _ hW)‖^2 + ‖(MemLp.toLp (p := 2) _ hD)‖^2 ≤
      (1 + ((2*Real.pi)^k)^2) * ‖KNSGraphSpace.ofSmooth k (f := f) hf hF hW hD‖^2 := by
  let p : ℝ := (2*Real.pi)^k
  have hp : p ≠ 0 := by dsimp [p]; positivity
  have hN := KNSGraphSpace.norm_ofSmooth_sq k hf hF hW hD
  have hlow : ‖(MemLp.toLp (p := 2) _ hF)‖^2 + ‖(MemLp.toLp (p := 2) _ hW)‖^2 ≤
      ‖KNSGraphSpace.ofSmooth k (f := f) hf hF hW hD‖^2 := by
    rw [hN]
    nlinarith [sq_nonneg ‖(MemLp.toLp (p := 2) _ hF)‖, sq_nonneg (p⁻¹*‖(MemLp.toLp (p := 2) _ hD)‖)]
  have htop : (p⁻¹*‖(MemLp.toLp (p := 2) _ hD)‖)^2 ≤ ‖KNSGraphSpace.ofSmooth k (f := f) hf hF hW hD‖^2 := by
    rw [hN]
    dsimp [p]
    nlinarith [sq_nonneg ‖(MemLp.toLp (p := 2) _ hF)‖, sq_nonneg ‖(MemLp.toLp (p := 2) _ hW)‖]
  have htop' : ‖(MemLp.toLp (p := 2) _ hD)‖^2 ≤ p^2 * ‖KNSGraphSpace.ofSmooth k (f := f) hf hF hW hD‖^2 := by
    calc
      _ = p^2 * (p⁻¹*‖(MemLp.toLp (p := 2) _ hD)‖)^2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left htop (sq_nonneg p)
  change _ ≤ (1+p^2) * _
  nlinarith

/-- A fixed positive bound for every actual smooth chart derivative through k
in terms of its genuine same-order graph input. -/
theorem exists_smooth_chart_graph_bound (k : ℕ) {R : ℝ} (hR : 2 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε^2=1 → ∀ (f : ℝ → ℂ)
      (hf : ContDiff ℝ ∞ f) (hF : MemLp f 2)
      (hW : MemLp (fun x : ℝ => (x : ℂ)^k*f x) 2)
      (hD : MemLp (iteratedDeriv k f) 2),
      ∀ j ≤ k, ∃ hJ : MemLp (iteratedDeriv j (signedSquareCutoffChart k R ε f)) 2,
        ‖(MemLp.toLp (p := 2) _ hJ)‖^2 ≤ C * ‖KNSGraphSpace.ofSmooth k (f := f) hf hF hW hD‖^2 := by
  obtain ⟨C, hC, hc⟩ := SignedSquareSmoothBounds.exists_smooth_chart_bound k hR
  refine ⟨C * (1+((2*Real.pi)^k)^2), by positivity, ?_⟩
  intro ε hε f hf hF hW hD j hj
  obtain ⟨hJ, hJb⟩ := hc ε hε f hf hF hD (power_integral_norm k hW).1 j hj
  rw [(power_integral_norm k hW).2] at hJb
  refine ⟨hJ, hJb.trans ?_⟩
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (energy_le_graph k hf hF hW hD) hC.le

end
end MeyerGeneralProblem.SignedSquareSmoothGraphBounds
