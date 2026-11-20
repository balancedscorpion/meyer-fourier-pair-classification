module

public import MeyerGeneralProblem.Sampling.SignedSquareCutoffTransfer
public import MeyerGeneralProblem.Gram.GroupedNormalizerBounds
public import MeyerGeneralProblem.Sampling.GroupedExponential

@[expose] public section

/-!
# Actual anchored reciprocal multiplier

This constructs the globally smooth normalized reciprocal used on fixed-diameter
signed-square cluster hulls. It proves the multiplier estimates themselves, not
the later tail-sampling assembly.
-/

namespace MeyerGeneralProblem.SignedSquareNormalizedReciprocal
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators

/-- The physical-order signed-square exponent. -/
def exponent (k : ℕ) : ℝ := (2 * (k : ℝ) - 1) / 4

/-- The exact natural-exponent anchor normalization. -/
def anchorWeight (k : ℕ) (c : ℝ) : ℝ :=
  Real.sqrt ((1 + Real.sqrt c) ^ (2*k-1))

/-- A fixed cutoff removes the reciprocal power singularity. No hull parameter occurs. -/
def reciprocalScalar (k : ℕ) (c t : ℝ) : ℝ :=
  anchorWeight k c * signedSquareTailCutoff (3/2) t * t ^ (-exponent k)

/-- The actual reflected complex-valued multiplier. -/
def multiplier (k : ℕ) (c ε s : ℝ) : ℂ :=
  reciprocalScalar k c (ε*s) • (1 : ℂ)

/-- Positive physical orders have a positive reciprocal exponent. -/
theorem exponent_pos {k : ℕ} (hk : 1≤k) : 0<exponent k := by
  have : (1:ℝ)≤k := by exact_mod_cast hk
  unfold exponent
  linarith

/-- The natural weight has exactly twice the real chart exponent. -/
theorem anchorWeight_eq_rpow {k : ℕ} (hk : 1≤k) (c : ℝ) :
    anchorWeight k c = (1+Real.sqrt c)^(2*exponent k) := by
  have hb : 0≤1+Real.sqrt c := by positivity
  have hn : (1:ℕ)≤2*k := by omega
  rw [anchorWeight, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hb]
  congr 1
  simp only [Nat.cast_sub hn, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, exponent]
  ring

/-- The multiplier is identically zero on the exact cutoff prefix. -/
theorem reciprocalScalar_zero (k : ℕ) (c : ℝ) {t : ℝ} (ht : t≤5/4) :
    reciprocalScalar k c t=0 := by
  rw [reciprocalScalar, signedSquareTailCutoff_zero (3/2) (by linarith), mul_zero, zero_mul]

/-- Beyond the exact cutoff endpoint, the multiplier is the raw reciprocal factor. -/
theorem reciprocalScalar_raw (k : ℕ) (c : ℝ) {t : ℝ} (ht : 9/4≤t) :
    reciprocalScalar k c t = anchorWeight k c * t^(-exponent k) := by
  rw [reciprocalScalar, signedSquareTailCutoff_one (3/2) (by linarith), mul_one]

/-- The actual total scalar definition is globally smooth. -/
theorem reciprocalScalar_contDiff (k : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (reciprocalScalar k c) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0<t
  · exact (contDiffAt_const.mul (contDiff_signedSquareTailCutoff (3/2)).contDiffAt).mul
      (Real.contDiffAt_rpow_const_of_ne ht.ne')
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show t<5/4 by linarith)] with u hu
    exact reciprocalScalar_zero k c hu.le

/-- The reflected complex multiplier is smooth for every real reflection parameter. -/
theorem multiplier_contDiff (k : ℕ) (c ε : ℝ) :
    ContDiff ℝ ∞ (multiplier k c ε) :=
  ((reciprocalScalar_contDiff k c).comp (by fun_prop)).smul contDiff_const

/-- Every point strictly beyond the plateau endpoint has an actual raw neighborhood. -/
theorem reciprocalScalar_eventually_raw (k : ℕ) (c : ℝ) {t : ℝ} (ht : 9/4<t) :
    reciprocalScalar k c =ᶠ[𝓝 t] (fun u => anchorWeight k c * u^(-exponent k)) := by
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact reciprocalScalar_raw k c hu.le

/-- All derivatives on the raw neighborhood have the exact descending-Pochhammer formula. -/
theorem reciprocalScalar_iteratedDeriv (k j : ℕ) (c : ℝ) {t : ℝ} (ht : 9/4<t) :
    iteratedDeriv j (reciprocalScalar k c) t =
      anchorWeight k c * ((descPochhammer ℝ j).eval (-exponent k) *
        t^(-exponent k-(j:ℝ))) := by
  rw [(reciprocalScalar_eventually_raw k c ht).iteratedDeriv_eq j,
    iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

/-- The exact complex reflected derivative retains the power of the actual ray sign. -/
theorem multiplier_iteratedDeriv (k j : ℕ) (c ε s : ℝ) (hs : 9/4<ε*s) :
    iteratedDeriv j (multiplier k c ε) s =
      (ε^j * (anchorWeight k c * ((descPochhammer ℝ j).eval (-exponent k) *
        (ε*s)^(-exponent k-(j:ℝ))))) • (1:ℂ) := by
  change iteratedDeriv j (fun u => reciprocalScalar k c (ε*u) • (1:ℂ)) s = _
  calc
    _ = iteratedDeriv j (fun u => reciprocalScalar k c (ε*u)) s • (1:ℂ) :=
      iteratedDeriv_smul_const
        (((reciprocalScalar_contDiff k c).comp (by fun_prop)).of_le (by simp)).contDiffAt _
    _ = _ := by
      rw [iteratedDeriv_comp_const_mul ((reciprocalScalar_contDiff k c).of_le (by simp))]
      change (ε^j * iteratedDeriv j (reciprocalScalar k c) (ε*s)) • (1:ℂ) = _
      rw [reciprocalScalar_iteratedDeriv k j c hs]

/-- The exact anchored natural weight has the required scale-free real-power bound. -/
theorem anchorWeight_le {k : ℕ} (hk : 1≤k) {c : ℝ} (hc : 1≤c) :
    anchorWeight k c ≤ (2:ℝ)^(2*exponent k)*c^(exponent k) := by
  have ha := (exponent_pos hk).le
  have hc0 : 0≤c := by linarith
  have hs : 1≤Real.sqrt c := (Real.le_sqrt (by norm_num) hc0).mpr (by simpa using hc)
  rw [anchorWeight_eq_rpow hk]
  calc
    _ ≤ (2*Real.sqrt c)^(2*exponent k) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg c), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hc0]
      congr 2
      ring

/-- Anchor divided by any point in the same fixed-diameter hull has a uniform bound. -/
theorem anchor_ratio_le {A c t D : ℝ} (hA : 4≤A) (hD : 0≤D)
    (hc : c∈Icc A (A+D)) (ht : t∈Icc A (A+D)) : c/t≤1+D/4 := by
  apply (div_le_iff₀ (show 0<t by linarith [ht.1])).mpr
  have h := mul_nonneg hD (show 0≤t-4 by linarith [ht.1])
  nlinarith [hc.2, ht.1]

/-- Every raw derivative power is uniformly normalized on the whole actual hull. -/
theorem weighted_power_le {k : ℕ} (hk : 1≤k) (j : ℕ) {A c t D : ℝ}
    (hA : 4≤A) (hD : 0≤D) (hc : c∈Icc A (A+D)) (ht : t∈Icc A (A+D)) :
    anchorWeight k c * t^(-exponent k-(j:ℝ)) ≤
      (2:ℝ)^(2*exponent k)*(1+D/4)^(exponent k) := by
  have ht0 : 0<t := by linarith [ht.1]
  have hc0 : 0≤c := by linarith [hc.1]
  have ha := (exponent_pos hk).le
  have hp : t^(-exponent k-(j:ℝ))≤t^(-exponent k) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) (by
      have hj0 : (0:ℝ)≤(j:ℝ) := Nat.cast_nonneg j
      linarith)
  calc
    _ ≤ ((2:ℝ)^(2*exponent k)*c^(exponent k))*t^(-exponent k) :=
      mul_le_mul (anchorWeight_le hk (by linarith [hc.1])) hp
        (Real.rpow_nonneg ht0.le _) (by positivity)
    _ = (2:ℝ)^(2*exponent k)*(c/t)^(exponent k) := by
      rw [Real.div_rpow hc0 ht0.le, Real.rpow_neg ht0.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (anchor_ratio_le hA hD hc ht) ha) (by positivity)

/-- The norm of every reflected derivative has the scale-free hull bound. -/
theorem norm_multiplier_iteratedDeriv_le {k : ℕ} (hk : 1≤k) (j : ℕ)
    {A c s D ε : ℝ} (hA : 4≤A) (hD : 0≤D) (hc : c∈Icc A (A+D))
    (hs : ε*s∈Icc A (A+D)) (hε : ε^2=1) :
    ‖iteratedDeriv j (multiplier k c ε) s‖ ≤
      (2:ℝ)^(2*exponent k)*(1+D/4)^(exponent k)*
        |(descPochhammer ℝ j).eval (-exponent k)| := by
  have htail : 9/4<ε*s := by linarith [hs.1]
  have hw : 0≤anchorWeight k c := Real.sqrt_nonneg _
  have hp : 0≤(ε*s)^(-exponent k-(j:ℝ)) := Real.rpow_nonneg (by linarith [hs.1]) _
  have he : |ε|=1 := by
    rcases sq_eq_one_iff.mp hε with rfl | rfl <;> norm_num
  rw [multiplier_iteratedDeriv k j c ε s htail, norm_smul, norm_one, mul_one,
    Real.norm_eq_abs, abs_mul, abs_pow, he, one_pow, abs_mul, abs_mul,
    abs_of_nonneg hw, abs_of_nonneg hp]
  simp only [one_mul]
  have hb := weighted_power_le hk j hA hD hc hs
  calc
    anchorWeight k c * (|(descPochhammer ℝ j).eval (-exponent k)| *
        (ε*s)^(-exponent k-(j:ℝ))) =
      (anchorWeight k c * (ε*s)^(-exponent k-(j:ℝ))) *
        |(descPochhammer ℝ j).eval (-exponent k)| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb
      (abs_nonneg ((descPochhammer ℝ j).eval (-exponent k)))

/-- One fixed constant controls the actual multiplier on every translated hull
of fixed diameter. The same explicit function is used at every location. -/
theorem exists_normalized_reciprocal_multiplier_bound
    (k p : ℕ) (hk : 1≤k) (D : ℝ) (hD : 0≤D) :
    ∃ M>0, ∀ A c ε : ℝ, 4≤A → c∈Icc A (A+D) → ε^2=1 →
      ContDiff ℝ ∞ (multiplier k c ε) ∧
      ∀ s : ℝ, ε*s∈Icc A (A+D) →
        multiplier k c ε s =
            (anchorWeight k c*(ε*s)^(-exponent k)) • (1:ℂ) ∧
          ∀ j≤p, ‖iteratedDeriv j (multiplier k c ε) s‖≤M := by
  let B : ℝ := (2:ℝ)^(2*exponent k)*(1+D/4)^(exponent k)
  let P : ℝ := ∑ j ∈ Finset.range (p+1), |(descPochhammer ℝ j).eval (-exponent k)|
  refine ⟨1+B*P, by positivity, ?_⟩
  intro A c ε hA hc hε
  refine ⟨multiplier_contDiff k c ε, ?_⟩
  intro s hs
  have ht : 9/4≤ε*s := by linarith [hs.1]
  constructor
  · rw [multiplier, reciprocalScalar_raw k c ht]
  · intro j hj
    have hbase : ‖iteratedDeriv j (multiplier k c ε) s‖ ≤
        B*|(descPochhammer ℝ j).eval (-exponent k)| := by
      simpa only [B] using norm_multiplier_iteratedDeriv_le hk j hA hD hc hs hε
    have hterm : B*|(descPochhammer ℝ j).eval (-exponent k)|≤B*P := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.single_le_sum (fun i _ => abs_nonneg ((descPochhammer ℝ i).eval (-exponent k)))
        (by simp only [Finset.mem_range]; omega)
    exact (hbase.trans hterm).trans (by linarith)

/-- Concrete negative-ray control: reflection sends the original negative node
-4 to the positive raw hull coordinate 4; it does not reverse prefix order. -/
theorem negative_reflection_raw_control :
    multiplier 1 9 (-1) (-4) =
      (anchorWeight 1 9 * (4:ℝ)^(-exponent 1)) • (1:ℂ) := by
  rw [multiplier]
  norm_num only [neg_mul]
  rw [reciprocalScalar_raw 1 9 (by norm_num)]

/-- The first original negative node has the claimed raw polynomial value. -/
theorem negative_original_prefix_zero_control :
    analyticDividedDifference (fun n : ℕ => if n=0 then -9 else if n=1 then -6 else -4)
      0 (fun s : ℝ => (2:ℝ)*s^2) = 162 := by
  simp [analyticDividedDifference_zero]
  norm_num

/-- Ascending original negative nodes give -30 in the first prefix. -/
theorem negative_original_prefix_one_control :
    analyticDividedDifference (fun n : ℕ => if n=0 then -9 else if n=1 then -6 else -4)
      1 (fun s : ℝ => (2:ℝ)*s^2) = -30 := by
  rw [analyticDividedDifference_succ, analyticDividedDifference_zero]
  norm_num [dslope, slope]

/-- Reversing the same negative nodes changes the zeroth prefix to 32. -/
theorem reversed_negative_prefix_zero_control :
    analyticDividedDifference (fun n : ℕ => if n=0 then -4 else if n=1 then -6 else -9)
      0 (fun s : ℝ => (2:ℝ)*s^2) = 32 := by
  simp [analyticDividedDifference_zero]
  norm_num

/-- Reversing the same negative nodes changes the first prefix to -20. -/
theorem reversed_negative_prefix_one_control :
    analyticDividedDifference (fun n : ℕ => if n=0 then -4 else if n=1 then -6 else -9)
      1 (fun s : ℝ => (2:ℝ)*s^2) = -20 := by
  rw [analyticDividedDifference_succ, analyticDividedDifference_zero]
  norm_num [dslope, slope]

end
end MeyerGeneralProblem.SignedSquareNormalizedReciprocal
