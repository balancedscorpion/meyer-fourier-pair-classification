module

public import MeyerGeneralProblem.Carrier.HermiteCross
public import MeyerGeneralProblem.Gram.HermiteUniversalLimit

@[expose] public section

/-!
# Uniform all-ratio Mehler remainder scale

The normalized lower-order term is measured relatively to the leading Mehler
matrix by `|sⱼ|⁻¹ + |sₖ|⁻¹`. It is deliberately *not* replaced by
`(|sⱼ| + |sₖ|)⁻¹`, which fails on unbalanced scales.
-/

namespace MeyerGeneralProblem

open Filter Asymptotics

noncomputable section

/-- Relative scale in the corrected uniform all-ratio remainder estimate.
The Hermite order affects the multiplicative constant, not this scale weight. -/
def normalizationError (_m : ℕ) (S T : ℝ) : ℝ :=
  |S|⁻¹ + |T|⁻¹

theorem normalizationError_nonneg (m : ℕ) (S T : ℝ) :
    0 ≤ normalizationError m S T := by
  exact add_nonneg (inv_nonneg.mpr (abs_nonneg S)) (inv_nonneg.mpr (abs_nonneg T))

/-- Uniform form of the corrected tail estimate: when both endpoint scales
are at least `U`, the relative error is at most `2/U`. -/
theorem normalizationError_le_two_mul_inv
    (m : ℕ) {S T U : ℝ} (hU : 0 < U)
    (hS : U ≤ |S|) (hT : U ≤ |T|) :
    normalizationError m S T ≤ 2 * U⁻¹ := by
  have hSinv : |S|⁻¹ ≤ U⁻¹ := inv_anti₀ hU hS
  have hTinv : |T|⁻¹ ≤ U⁻¹ := inv_anti₀ hU hT
  unfold normalizationError
  linarith

/-- In the deliberately unbalanced regime `S = T²`, the corrected relative
error is bounded by `2/T`, hence has order `T⁻¹` rather than `T⁻²`.
This is the regression theorem guarding the reviewer correction. -/
theorem unbalanced_normalization_error_bound (m : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    normalizationError m (T ^ 2) T ≤ 2 * T⁻¹ := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hTnonneg : 0 ≤ T := hTpos.le
  have hTsq : T ≤ T ^ 2 := by nlinarith
  have hinv : (T ^ 2)⁻¹ ≤ T⁻¹ := inv_anti₀ hTpos hTsq
  simp only [normalizationError, abs_of_nonneg hTnonneg,
    abs_of_nonneg (sq_nonneg T)]
  linarith

/-- Asymptotic form of `unbalanced_normalization_error_bound`. -/
theorem unbalanced_normalization_error (m : ℕ) :
    (fun T : ℝ ↦ normalizationError m (T ^ 2) T) =O[atTop]
      (fun T : ℝ ↦ T⁻¹) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hbound := unbalanced_normalization_error_bound m hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (normalizationError_nonneg m (T ^ 2) T),
    abs_of_nonneg (inv_nonneg.mpr hTpos.le)]
  exact hbound

/-- The false sum-inverse scale is quadratically smaller on `S = T²`; this
identity records why it cannot replace the corrected relative weight. -/
theorem unbalanced_falseScale (T : ℝ) :
    ((T ^ 2 + T)⁻¹ : ℝ) = (T * (T + 1))⁻¹ := by
  congr 1
  ring

/-!
## Exact complex cross-kernel scaling

The remainder scale above is complemented here by the exact rescaling of the
closed complex Mehler kernel.  The normalized integral has a single
dimensionless ratio parameter `q * X * Y`, automatically confined to
`[-1/2, 1/2]`.  A ratio-independent integrable envelope gives dominated
convergence across the entire compact range, including sequences whose scale
ratio does not converge.
-/

/-- Nonsingular real prefactor left after the cross-Mehler substitution
`t = q * u`. -/
def crossMehlerScaledPrefactor (q u : ℝ) : ℝ :=
  Real.exp (-(u * q)) * Real.sqrt 2 /
    Real.sqrt (1 + Real.exp (-(u * q)) ^ 2)

/-- Spatial Gaussian decay rate after division by the exact pair scale `q`. -/
def crossMehlerScaledDecayRate (q u : ℝ) : ℝ :=
  (1 - Real.exp (-((2 * u) * q))) /
    (q * (1 + Real.exp (-((2 * u) * q))))

/-- Residual phase rate after extracting the leading Fourier phase
`exp (-2 * pi * I * X * Y)`. -/
def crossMehlerScaledPhaseRate (q u : ℝ) : ℝ :=
  (2 * Real.exp (-(u * q)) /
      (1 + Real.exp (-(u * q)) ^ 2) - 1) / q

/-- Dimensionless cross-resolvent integrand at pair scale `q` and compact
ratio parameter `ω = q * X * Y`. -/
def crossMehlerRescaledIntegrand
    (m : ℕ) (q ω u : ℝ) : ℂ :=
  ((u ^ ((2 * m : ℕ) - 1) * crossMehlerScaledPrefactor q u *
      Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) : ℝ) : ℂ) *
    Complex.exp
      (-2 * Real.pi * Complex.I * ω * crossMehlerScaledPhaseRate q u)

/-- Ratio-independent Gamma density obtained as the pair scale tends to zero. -/
def crossMehlerLeadingIntegrand (m : ℕ) (u : ℝ) : ℂ :=
  ((u ^ ((2 * m : ℕ) - 1) * Real.exp (-Real.pi * u) : ℝ) : ℂ)

/-- Leading negative Fourier phase in the repository's transform convention. -/
def crossMehlerLeadingPhase (X Y : ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * X * Y)

@[simp]
theorem norm_crossMehlerLeadingPhase (X Y : ℝ) :
    ‖crossMehlerLeadingPhase X Y‖ = 1 := by
  unfold crossMehlerLeadingPhase
  rw [Complex.norm_exp]
  norm_num

/-- Positive universal constant used in the stretched-exponential envelope. -/
def crossMehlerDecayConstant : ℝ :=
  Real.exp (-1) / 2

theorem crossMehlerDecayConstant_pos :
    0 < crossMehlerDecayConstant := by
  unfold crossMehlerDecayConstant
  positivity

theorem crossMehlerDecayConstant_le_one :
    crossMehlerDecayConstant ≤ 1 := by
  unfold crossMehlerDecayConstant
  have h := Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0)
  nlinarith [Real.exp_pos (-1)]

theorem crossMehlerScaledPrefactor_nonneg
    (q u : ℝ) :
    0 ≤ crossMehlerScaledPrefactor q u := by
  unfold crossMehlerScaledPrefactor
  positivity

theorem crossMehlerScaledPrefactor_le_sqrt_two
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    crossMehlerScaledPrefactor q u ≤ Real.sqrt 2 := by
  let r := Real.exp (-(u * q))
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hu.le hq.le)
  have hsqrtPos : 0 < Real.sqrt (1 + r ^ 2) := by positivity
  have hsqrtOne : 1 ≤ Real.sqrt (1 + r ^ 2) := by
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg r]
  have hratio : r / Real.sqrt (1 + r ^ 2) ≤ 1 := by
    rw [div_le_one hsqrtPos]
    exact hr1.trans hsqrtOne
  unfold crossMehlerScaledPrefactor
  change r * Real.sqrt 2 / Real.sqrt (1 + r ^ 2) ≤ Real.sqrt 2
  calc
    r * Real.sqrt 2 / Real.sqrt (1 + r ^ 2) =
        Real.sqrt 2 * (r / Real.sqrt (1 + r ^ 2)) := by ring
    _ ≤ Real.sqrt 2 * 1 := by gcongr
    _ = Real.sqrt 2 := mul_one _

theorem crossMehlerScaledDecayRate_pos
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    0 < crossMehlerScaledDecayRate q u := by
  unfold crossMehlerScaledDecayRate
  have he : Real.exp (-((2 * u) * q)) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (by positivity)
  positivity

theorem crossMehlerScaledDecayRate_nonneg
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    0 ≤ crossMehlerScaledDecayRate q u :=
  (crossMehlerScaledDecayRate_pos hq hu).le

theorem crossMehlerDecayConstant_mul_min_div_le_scaledDecayRate
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    crossMehlerDecayConstant * min (2 * u * q) 1 / q ≤
      crossMehlerScaledDecayRate q u := by
  have ht : 0 < 2 * u * q := by positivity
  have hbase := exp_neg_one_div_two_mul_min_le_mehlerSpatialRate ht
  have heq : mehlerSpatialRate (2 * u * q) / q =
      crossMehlerScaledDecayRate q u := by
    unfold mehlerSpatialRate crossMehlerScaledDecayRate
    have hden : 1 + Real.exp (-((2 * u) * q)) ≠ 0 := by positivity
    field_simp [hq.ne', hden]
  rw [← heq, crossMehlerDecayConstant]
  exact (div_le_div_iff_of_pos_right hq).2 hbase

theorem crossMehlerScaledExponent_ge_sqrt
    {q u : ℝ} (hq : 0 < q) (huOne : 1 ≤ u) :
    crossMehlerDecayConstant * Real.sqrt u ≤
      u * q + Real.pi * crossMehlerScaledDecayRate q u := by
  have hu : 0 < u := zero_lt_one.trans_le huOne
  have hc0 := crossMehlerDecayConstant_pos
  have hc1 := crossMehlerDecayConstant_le_one
  have hratePos := crossMehlerScaledDecayRate_pos hq hu
  have hrate0 := hratePos.le
  have hpi : 1 ≤ Real.pi :=
    le_trans (by norm_num : (1 : ℝ) ≤ 2) Real.two_le_pi
  have hsqrt0 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsqrtOne : 1 ≤ Real.sqrt u := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt huOne
  have hsqrtSq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu.le
  have hrate :=
    crossMehlerDecayConstant_mul_min_div_le_scaledDecayRate hq hu
  by_cases hsmall : 2 * u * q ≤ 1
  · rw [min_eq_left hsmall] at hrate
    have hrate' : 2 * crossMehlerDecayConstant * u ≤
        crossMehlerScaledDecayRate q u := by
      calc
        2 * crossMehlerDecayConstant * u =
            crossMehlerDecayConstant * (2 * u * q) / q := by
          field_simp [hq.ne']
        _ ≤ crossMehlerScaledDecayRate q u := hrate
    have hsqrtLeU : Real.sqrt u ≤ u := by
      nlinarith
    have hpiRate : crossMehlerScaledDecayRate q u ≤
        Real.pi * crossMehlerScaledDecayRate q u := by
      exact (le_mul_iff_one_le_left hratePos).2 hpi
    nlinarith
  · have hlarge : 1 ≤ 2 * u * q := le_of_not_ge hsmall
    rw [min_eq_right hlarge] at hrate
    have hrate' : crossMehlerDecayConstant / q ≤
        crossMehlerScaledDecayRate q u := by simpa using hrate
    by_cases hqroot : (Real.sqrt u)⁻¹ ≤ q
    · have huq : Real.sqrt u ≤ u * q := by
        calc
          Real.sqrt u = u * (Real.sqrt u)⁻¹ := by
            field_simp [hsqrt0.ne']
            exact hsqrtSq
          _ ≤ u * q := by gcongr
      have hc : crossMehlerDecayConstant * Real.sqrt u ≤
          Real.sqrt u := by
        exact (mul_le_iff_le_one_left hsqrt0).2 hc1
      nlinarith [Real.pi_pos, hrate0]
    · have hqroot' : q < (Real.sqrt u)⁻¹ := lt_of_not_ge hqroot
      have hinv : Real.sqrt u < q⁻¹ := by
        simpa using
          (inv_lt_inv₀ (inv_pos.mpr hsqrt0) hq).2 hqroot'
      have hcInv : crossMehlerDecayConstant * Real.sqrt u ≤
          crossMehlerDecayConstant / q := by
        rw [div_eq_mul_inv]
        gcongr
      have hpiRate : crossMehlerScaledDecayRate q u ≤
          Real.pi * crossMehlerScaledDecayRate q u := by
        exact (le_mul_iff_one_le_left hratePos).2 hpi
      linarith

theorem crossMehlerScaledPrefactor_le_exp_mul_sqrt_two
    (q u : ℝ) :
    crossMehlerScaledPrefactor q u ≤
      Real.exp (-(u * q)) * Real.sqrt 2 := by
  let r := Real.exp (-(u * q))
  have hsqrtOne : 1 ≤ Real.sqrt (1 + r ^ 2) := by
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg r]
  unfold crossMehlerScaledPrefactor
  change r * Real.sqrt 2 / Real.sqrt (1 + r ^ 2) ≤
    r * Real.sqrt 2
  exact div_le_self (by positivity) hsqrtOne

theorem crossMehlerCombinedExp_le
    {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    Real.exp (-(u * q + Real.pi * crossMehlerScaledDecayRate q u)) ≤
      Real.exp crossMehlerDecayConstant *
        Real.exp (-crossMehlerDecayConstant * Real.sqrt u) := by
  have hc0 := crossMehlerDecayConstant_pos
  have hrate0 := (crossMehlerScaledDecayRate_pos hq hu).le
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  by_cases huOne : u ≤ 1
  · have hsqrtOne : Real.sqrt u ≤ 1 := Real.sqrt_le_one.mpr huOne
    have htotal0 : 0 ≤
        u * q + Real.pi * crossMehlerScaledDecayRate q u :=
      add_nonneg (mul_nonneg hu.le hq.le)
        (mul_nonneg Real.pi_pos.le hrate0)
    nlinarith [Real.sqrt_nonneg u]
  · have huOne' : 1 ≤ u := le_of_not_ge huOne
    have hcombined := crossMehlerScaledExponent_ge_sqrt hq huOne'
    nlinarith

/-- Ratio- and scale-independent integrable majorant for the rescaled
cross-Mehler integrand. -/
def crossMehlerGlobalMajorant (m : ℕ) (u : ℝ) : ℝ :=
  Real.sqrt 2 * Real.exp crossMehlerDecayConstant *
    u ^ ((2 * m : ℕ) - 1) *
      Real.exp (-crossMehlerDecayConstant * Real.sqrt u)

theorem integrableOn_crossMehlerGlobalMajorant
    (m : ℕ) (_hm : 1 ≤ m) :
    MeasureTheory.IntegrableOn
      (crossMehlerGlobalMajorant m) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < (((2 * m : ℕ) - 1 : ℕ) : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ (((2 * m : ℕ) - 1 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have href := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 / 2 : ℝ)) (s := (((2 * m : ℕ) - 1 : ℕ) : ℝ))
    (b := crossMehlerDecayConstant) hs
    (by norm_num : (0 : ℝ) < 1 / 2) crossMehlerDecayConstant_pos
  change MeasureTheory.Integrable (crossMehlerGlobalMajorant m)
    (MeasureTheory.volume.restrict (Set.Ioi 0))
  convert href.const_mul
      (Real.sqrt 2 * Real.exp crossMehlerDecayConstant) using 1
  ext u
  unfold crossMehlerGlobalMajorant
  simp only [Real.rpow_natCast, Real.sqrt_eq_rpow]
  ring

theorem norm_crossMehlerRescaledIntegrand
    (m : ℕ) {q ω u : ℝ} (hu : 0 < u) :
    ‖crossMehlerRescaledIntegrand m q ω u‖ =
      u ^ ((2 * m : ℕ) - 1) * crossMehlerScaledPrefactor q u *
        Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) := by
  have hscalar : 0 ≤
      u ^ ((2 * m : ℕ) - 1) * crossMehlerScaledPrefactor q u *
        Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) := by
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hu.le _)
        (crossMehlerScaledPrefactor_nonneg q u))
      (Real.exp_pos _).le
  have hphase :
      ‖Complex.exp
        (-2 * Real.pi * Complex.I * ω *
          crossMehlerScaledPhaseRate q u)‖ = 1 := by
    rw [show -2 * Real.pi * Complex.I * ω *
        crossMehlerScaledPhaseRate q u =
      (((-2 * Real.pi * ω * crossMehlerScaledPhaseRate q u : ℝ) : ℂ) *
        Complex.I) by
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [crossMehlerRescaledIntegrand, norm_mul, hphase, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscalar]

theorem norm_crossMehlerRescaledIntegrand_le_globalMajorant
    (m : ℕ) {q ω u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    ‖crossMehlerRescaledIntegrand m q ω u‖ ≤
      crossMehlerGlobalMajorant m u := by
  have hpref := crossMehlerScaledPrefactor_le_exp_mul_sqrt_two q u
  have hpow0 : 0 ≤ u ^ ((2 * m : ℕ) - 1) := pow_nonneg hu.le _
  have hrealExp0 : 0 ≤
      Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) :=
    (Real.exp_pos _).le
  have hcombined := crossMehlerCombinedExp_le hq hu
  rw [norm_crossMehlerRescaledIntegrand m hu]
  calc
    u ^ ((2 * m : ℕ) - 1) * crossMehlerScaledPrefactor q u *
        Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) ≤
      u ^ ((2 * m : ℕ) - 1) *
          (Real.exp (-(u * q)) * Real.sqrt 2) *
        Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) := by
      gcongr
    _ = Real.sqrt 2 * u ^ ((2 * m : ℕ) - 1) *
        Real.exp (-(u * q +
          Real.pi * crossMehlerScaledDecayRate q u)) := by
      rw [show u ^ ((2 * m : ℕ) - 1) *
          (Real.exp (-(u * q)) * Real.sqrt 2) *
          Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) =
        Real.sqrt 2 * u ^ ((2 * m : ℕ) - 1) *
          (Real.exp (-(u * q)) *
            Real.exp (-Real.pi * crossMehlerScaledDecayRate q u)) by ring,
        ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.sqrt 2 * u ^ ((2 * m : ℕ) - 1) *
        (Real.exp crossMehlerDecayConstant *
          Real.exp (-crossMehlerDecayConstant * Real.sqrt u)) := by
      gcongr
    _ = crossMehlerGlobalMajorant m u := by
      unfold crossMehlerGlobalMajorant
      ring

theorem tendsto_crossMehlerScaledPrefactor (u : ℝ) :
    Tendsto (fun q : ℝ => crossMehlerScaledPrefactor q u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hr := tendsto_exp_neg_mul (u := u)
  have hsqrt : Tendsto
      (fun q : ℝ => Real.sqrt (1 + Real.exp (-(u * q)) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2)) := by
    have hinside : Tendsto
        (fun q : ℝ => (1 : ℝ) + Real.exp (-(u * q)) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
      convert tendsto_const_nhds.add (hr.pow 2) using 1
      · norm_num
    simpa only [Function.comp_def] using
      (Real.continuous_sqrt.tendsto 2).comp hinside
  have hnum := hr.mul_const (Real.sqrt 2)
  have hquot := hnum.div hsqrt (Real.sqrt_ne_zero'.mpr (by norm_num))
  convert hquot using 1
  · ext q
    rfl
  · field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]

theorem tendsto_crossMehlerScaledDecayRate (u : ℝ) :
    Tendsto (fun q : ℝ => crossMehlerScaledDecayRate q u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds u) := by
  have hnum := tendsto_one_sub_exp_neg_mul_div (u := 2 * u)
  have hexp := tendsto_exp_neg_mul (u := 2 * u)
  have hden : Tendsto
      (fun q : ℝ => 1 + Real.exp (-((2 * u) * q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
    convert tendsto_const_nhds.add hexp using 1
    · ring
  have hquot := hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)
  have hlimit : (2 * u) / 2 = u := by ring
  rw [hlimit] at hquot
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : q ≠ 0 := ne_of_gt hq
  change ((1 - Real.exp (-((2 * u) * q))) / q) /
      (1 + Real.exp (-((2 * u) * q))) = _
  unfold crossMehlerScaledDecayRate
  field_simp [hq0]

theorem crossMehlerScaledPhaseRate_eq
    {q : ℝ} (hq : q ≠ 0) (u : ℝ) :
    crossMehlerScaledPhaseRate q u =
      -q * (((1 - Real.exp (-(u * q))) / q) ^ 2 /
        (1 + Real.exp (-(u * q)) ^ 2)) := by
  unfold crossMehlerScaledPhaseRate
  field_simp
  ring

theorem tendsto_crossMehlerScaledPhaseRate (u : ℝ) :
    Tendsto (fun q : ℝ => crossMehlerScaledPhaseRate q u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hq : Tendsto (fun q : ℝ => q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hslope := tendsto_one_sub_exp_neg_mul_div (u := u)
  have hr := tendsto_exp_neg_mul (u := u)
  have hden : Tendsto
      (fun q : ℝ => 1 + Real.exp (-(u * q)) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
    convert tendsto_const_nhds.add (hr.pow 2) using 1
    · norm_num
  have hfrac := (hslope.pow 2).div hden (by norm_num : (2 : ℝ) ≠ 0)
  have hzero := (hq.mul hfrac).neg
  have hzero' : Tendsto
      (fun q : ℝ => -(q * (((1 - Real.exp (-(u * q))) / q) ^ 2) /
        (1 + Real.exp (-(u * q)) ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert hzero using 1
    · ext q
      simp only [Pi.div_apply]
      ring
    · ring
  apply hzero'.congr'
  filter_upwards [self_mem_nhdsWithin] with q hqpos
  calc
    -(q * (((1 - Real.exp (-(u * q))) / q) ^ 2) /
        (1 + Real.exp (-(u * q)) ^ 2)) =
        -q * (((1 - Real.exp (-(u * q))) / q) ^ 2 /
          (1 + Real.exp (-(u * q)) ^ 2)) := by ring
    _ = crossMehlerScaledPhaseRate q u :=
      (crossMehlerScaledPhaseRate_eq hqpos.ne' u).symm

theorem tendsto_crossMehlerRescaledIntegrand
    (m : ℕ) (ω u : ℝ) :
    Tendsto (fun q : ℝ => crossMehlerRescaledIntegrand m q ω u)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (crossMehlerLeadingIntegrand m u)) := by
  have hpref := tendsto_crossMehlerScaledPrefactor u
  have hdecay := tendsto_crossMehlerScaledDecayRate u
  have hrealexp : Tendsto
      (fun q : ℝ => Real.exp (-Real.pi * crossMehlerScaledDecayRate q u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-Real.pi * u))) := by
    have harg := hdecay.const_mul (-Real.pi)
    simpa only [Function.comp_def] using
      (Real.continuous_exp.tendsto (-Real.pi * u)).comp harg
  have hphaseRate := tendsto_crossMehlerScaledPhaseRate u
  have hphaseRateC : Tendsto
      (fun q : ℝ => (crossMehlerScaledPhaseRate q u : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply ((Complex.continuous_ofReal.tendsto 0).comp hphaseRate).congr'
    exact Filter.Eventually.of_forall (fun _q => rfl)
  have hphaseArg : Tendsto
      (fun q : ℝ =>
        -2 * Real.pi * Complex.I * ω * crossMehlerScaledPhaseRate q u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert tendsto_const_nhds.mul hphaseRateC using 1
    · ring
  have hphase : Tendsto
      (fun q : ℝ => Complex.exp
        (-2 * Real.pi * Complex.I * ω * crossMehlerScaledPhaseRate q u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa only [Function.comp_def, Complex.exp_zero] using
      (Complex.continuous_exp.tendsto 0).comp hphaseArg
  have hpow : Tendsto (fun _q : ℝ => u ^ ((2 * m : ℕ) - 1))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (u ^ ((2 * m : ℕ) - 1))) := tendsto_const_nhds
  have hreal := (hpow.mul hpref).mul hrealexp
  have hrealC : Tendsto
      (fun q : ℝ =>
        ((u ^ ((2 * m : ℕ) - 1) * crossMehlerScaledPrefactor q u *
          Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((u ^ ((2 * m : ℕ) - 1) * Real.exp (-Real.pi * u) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, mul_one] using
      (Complex.continuous_ofReal.tendsto _).comp hreal
  simpa only [crossMehlerRescaledIntegrand, crossMehlerLeadingIntegrand,
    mul_one] using hrealC.mul hphase

/-- Joint all-ratio pointwise limit: the ratio parameter may vary with the
pair scale. -/
theorem tendsto_crossMehlerRescaledIntegrand_of_tendsto
    (m : ℕ) {q ω : ℕ → ℝ} {ω₀ u : ℝ}
    (hq : Tendsto q atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hω : Tendsto ω atTop (nhds ω₀)) :
    Tendsto (fun n => crossMehlerRescaledIntegrand m (q n) (ω n) u)
      atTop (nhds (crossMehlerLeadingIntegrand m u)) := by
  have hpref := (tendsto_crossMehlerScaledPrefactor u).comp hq
  have hdecay := (tendsto_crossMehlerScaledDecayRate u).comp hq
  have hrealexp : Tendsto
      (fun n => Real.exp (-Real.pi * crossMehlerScaledDecayRate (q n) u))
      atTop (nhds (Real.exp (-Real.pi * u))) := by
    have harg := hdecay.const_mul (-Real.pi)
    simpa only [Function.comp_def] using
      (Real.continuous_exp.tendsto (-Real.pi * u)).comp harg
  have hphaseRate := (tendsto_crossMehlerScaledPhaseRate u).comp hq
  have hphaseRateC : Tendsto
      (fun n => (crossMehlerScaledPhaseRate (q n) u : ℂ))
      atTop (nhds 0) := by
    apply ((Complex.continuous_ofReal.tendsto 0).comp hphaseRate).congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hωC : Tendsto (fun n => (ω n : ℂ)) atTop (nhds (ω₀ : ℂ)) := by
    apply ((Complex.continuous_ofReal.tendsto ω₀).comp hω).congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hphaseArg : Tendsto
      (fun n => -2 * Real.pi * Complex.I * ω n *
        crossMehlerScaledPhaseRate (q n) u) atTop (nhds 0) := by
    have hproduct := hωC.mul hphaseRateC
    have hconst : Tendsto
        (fun _n : ℕ => (-2 * Real.pi * Complex.I : ℂ)) atTop
        (nhds (-2 * Real.pi * Complex.I : ℂ)) := tendsto_const_nhds
    have hscaled := hconst.mul hproduct
    convert hscaled using 1
    · ring
    · ring
  have hphase : Tendsto
      (fun n => Complex.exp
        (-2 * Real.pi * Complex.I * ω n *
          crossMehlerScaledPhaseRate (q n) u)) atTop (nhds 1) := by
    simpa only [Function.comp_def, Complex.exp_zero] using
      (Complex.continuous_exp.tendsto 0).comp hphaseArg
  have hpow : Tendsto (fun _n : ℕ => u ^ ((2 * m : ℕ) - 1)) atTop
      (nhds (u ^ ((2 * m : ℕ) - 1))) := tendsto_const_nhds
  have hreal := (hpow.mul hpref).mul hrealexp
  have hrealC : Tendsto
      (fun n =>
        ((u ^ ((2 * m : ℕ) - 1) * crossMehlerScaledPrefactor (q n) u *
          Real.exp (-Real.pi * crossMehlerScaledDecayRate (q n) u) : ℝ) : ℂ))
      atTop
      (nhds ((u ^ ((2 * m : ℕ) - 1) * Real.exp (-Real.pi * u) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, mul_one] using
      (Complex.continuous_ofReal.tendsto _).comp hreal
  simpa only [crossMehlerRescaledIntegrand, crossMehlerLeadingIntegrand,
    mul_one] using hrealC.mul hphase

/-- Joint all-ratio pointwise limit without convergence of the ratio
parameter: a uniform compact bound is enough because the residual phase rate
vanishes. -/
theorem tendsto_crossMehlerRescaledIntegrand_of_bounded
    (m : ℕ) {q ω : ℕ → ℝ} {u : ℝ}
    (hq : Tendsto q atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hω : ∀ n, |ω n| ≤ 1 / 2) :
    Tendsto (fun n => crossMehlerRescaledIntegrand m (q n) (ω n) u)
      atTop (nhds (crossMehlerLeadingIntegrand m u)) := by
  have hpref := (tendsto_crossMehlerScaledPrefactor u).comp hq
  have hdecay := (tendsto_crossMehlerScaledDecayRate u).comp hq
  have hrealexp : Tendsto
      (fun n => Real.exp (-Real.pi * crossMehlerScaledDecayRate (q n) u))
      atTop (nhds (Real.exp (-Real.pi * u))) := by
    have harg := hdecay.const_mul (-Real.pi)
    simpa only [Function.comp_def] using
      (Real.continuous_exp.tendsto (-Real.pi * u)).comp harg
  have hphaseRate := (tendsto_crossMehlerScaledPhaseRate u).comp hq
  have hωBounded : IsBoundedUnder (· ≤ ·) atTop (norm ∘ ω) :=
    isBoundedUnder_of ⟨1 / 2, fun n => by
      simpa only [Function.comp_apply, Real.norm_eq_abs] using hω n⟩
  have hphaseProduct : Tendsto
      (fun n => ω n * crossMehlerScaledPhaseRate (q n) u)
      atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      Filter.isBoundedUnder_le_mul_tendsto_zero hωBounded hphaseRate
  have hphaseProductC : Tendsto
      (fun n => ((ω n * crossMehlerScaledPhaseRate (q n) u : ℝ) : ℂ))
      atTop (nhds 0) := by
    apply ((Complex.continuous_ofReal.tendsto 0).comp hphaseProduct).congr'
    exact Filter.Eventually.of_forall (fun _n => rfl)
  have hphaseArg : Tendsto
      (fun n => -2 * Real.pi * Complex.I * ω n *
        crossMehlerScaledPhaseRate (q n) u) atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _n : ℕ => (-2 * Real.pi * Complex.I : ℂ)) atTop
        (nhds (-2 * Real.pi * Complex.I : ℂ)) := tendsto_const_nhds
    have hscaled := hconst.mul hphaseProductC
    convert hscaled using 1
    · ext n
      push_cast
      ring
    · ring
  have hphase : Tendsto
      (fun n => Complex.exp
        (-2 * Real.pi * Complex.I * ω n *
          crossMehlerScaledPhaseRate (q n) u)) atTop (nhds 1) := by
    simpa only [Function.comp_def, Complex.exp_zero] using
      (Complex.continuous_exp.tendsto 0).comp hphaseArg
  have hpow : Tendsto (fun _n : ℕ => u ^ ((2 * m : ℕ) - 1)) atTop
      (nhds (u ^ ((2 * m : ℕ) - 1))) := tendsto_const_nhds
  have hreal := (hpow.mul hpref).mul hrealexp
  have hrealC : Tendsto
      (fun n =>
        ((u ^ ((2 * m : ℕ) - 1) * crossMehlerScaledPrefactor (q n) u *
          Real.exp (-Real.pi * crossMehlerScaledDecayRate (q n) u) : ℝ) : ℂ))
      atTop
      (nhds ((u ^ ((2 * m : ℕ) - 1) * Real.exp (-Real.pi * u) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, mul_one] using
      (Complex.continuous_ofReal.tendsto _).comp hreal
  simpa only [crossMehlerRescaledIntegrand, crossMehlerLeadingIntegrand,
    mul_one] using hrealC.mul hphase

/-- Dominated convergence for the exact cross-kernel pair scaling.  The
ratio parameter may vary arbitrarily in the compact geometric range; the
majorant is independent of that parameter. -/
theorem tendsto_integral_crossMehlerRescaledIntegrand_of_sequences
    (m : ℕ) (hm : 1 ≤ m)
    {q ω : ℕ → ℝ}
    (hqPos : ∀ n, 0 < q n)
    (hqLim : Tendsto q atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hω : ∀ n, |ω n| ≤ 1 / 2) :
    Tendsto
      (fun n => ∫ u : ℝ in Set.Ioi 0,
        crossMehlerRescaledIntegrand m (q n) (ω n) u)
      atTop
      (nhds (∫ u : ℝ in Set.Ioi 0,
        crossMehlerLeadingIntegrand m u)) := by
  let F : ℕ → ℝ → ℂ := fun n u =>
    crossMehlerRescaledIntegrand m (q n) (ω n) u
  let f : ℝ → ℂ := crossMehlerLeadingIntegrand m
  have hmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (F n)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro n
    apply Measurable.aestronglyMeasurable
    unfold F crossMehlerRescaledIntegrand crossMehlerScaledPrefactor
      crossMehlerScaledDecayRate crossMehlerScaledPhaseRate
    fun_prop
  have hbound : ∀ᶠ n in atTop, ∀ᵐ u ∂
      (MeasureTheory.volume.restrict (Set.Ioi 0)),
      ‖F n u‖ ≤ crossMehlerGlobalMajorant m u := by
    filter_upwards with n
    filter_upwards [MeasureTheory.ae_restrict_mem
      (μ := MeasureTheory.volume) measurableSet_Ioi] with u hu
    exact norm_crossMehlerRescaledIntegrand_le_globalMajorant
      m (hqPos n) hu
  have hlim : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Tendsto (fun n => F n u) atTop (nhds (f u)) := by
    filter_upwards with u
    exact tendsto_crossMehlerRescaledIntegrand_of_bounded
      m hqLim hω
  simpa only [F, f] using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (crossMehlerGlobalMajorant m)
      (Filter.Eventually.of_forall hmeas) hbound
      (integrableOn_crossMehlerGlobalMajorant m hm) hlim

/-- Epsilon-delta form of the all-ratio integral limit, uniform over the
entire compact geometric ratio interval. -/
theorem crossMehlerIntegral_uniformAllRatio
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ ε > 0, ∃ δ > 0, ∀ q ω : ℝ,
      0 < q → q < δ → |ω| ≤ 1 / 2 →
      ‖(∫ u : ℝ in Set.Ioi 0,
          crossMehlerRescaledIntegrand m q ω u) -
        ∫ u : ℝ in Set.Ioi 0,
          crossMehlerLeadingIntegrand m u‖ ≤ ε := by
  intro ε hε
  by_contra hfail
  push Not at hfail
  have hchoice : ∀ n : ℕ, ∃ q ω : ℝ,
      0 < q ∧ q < ((n : ℝ) + 1)⁻¹ ∧ |ω| ≤ 1 / 2 ∧
      ε < ‖(∫ u : ℝ in Set.Ioi 0,
          crossMehlerRescaledIntegrand m q ω u) -
        ∫ u : ℝ in Set.Ioi 0,
          crossMehlerLeadingIntegrand m u‖ := by
    intro n
    exact hfail (((n : ℝ) + 1)⁻¹) (by positivity)
  choose q ω hqPos hqSmall hω hbad using hchoice
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hden
  have hqNhd : Tendsto q atTop (nhds 0) :=
    squeeze_zero (fun n => (hqPos n).le) (fun n => (hqSmall n).le) hinv
  have hqLim : Tendsto q atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hqNhd, Filter.Eventually.of_forall hqPos⟩
  have hIntegral :=
    tendsto_integral_crossMehlerRescaledIntegrand_of_sequences
      m hm hqPos hqLim hω
  have hDifference : Tendsto
      (fun n => (∫ u : ℝ in Set.Ioi 0,
          crossMehlerRescaledIntegrand m (q n) (ω n) u) -
        ∫ u : ℝ in Set.Ioi 0,
          crossMehlerLeadingIntegrand m u)
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _n : ℕ => ∫ u : ℝ in Set.Ioi 0,
          crossMehlerLeadingIntegrand m u)
        atTop
        (nhds (∫ u : ℝ in Set.Ioi 0,
          crossMehlerLeadingIntegrand m u)) := tendsto_const_nhds
    simpa only [sub_self] using hIntegral.sub hconst
  have hNorm : Tendsto
      (fun n => ‖(∫ u : ℝ in Set.Ioi 0,
          crossMehlerRescaledIntegrand m (q n) (ω n) u) -
        ∫ u : ℝ in Set.Ioi 0,
          crossMehlerLeadingIntegrand m u‖)
      atTop (nhds 0) := by
    simpa using hDifference.norm
  have hsmall := hNorm.eventually (Iio_mem_nhds hε)
  rcases hsmall.exists with ⟨n, hn⟩
  linarith [hbad n]

/-- The pair-ratio parameter retained by the exact rescaling always lies in
the compact interval `[-1/2, 1/2]`, uniformly in the scale ratio. -/
theorem abs_pairRatio_le_half
    {q X Y : ℝ} (hq : 0 < q)
    (hqScale : q * (X ^ 2 + Y ^ 2) = 1) :
    |q * X * Y| ≤ 1 / 2 := by
  have hxy : 2 * |X * Y| ≤ X ^ 2 + Y ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|X| - |Y|), sq_abs X, sq_abs Y]
  have hmul := mul_le_mul_of_nonneg_left hxy hq.le
  rw [hqScale] at hmul
  rw [abs_mul] at hmul
  rw [abs_mul, abs_mul, abs_of_pos hq]
  nlinarith [hmul]

theorem q_mul_hermiteCrossResolventClosedIntegrand_scaled
    (m : ℕ) (hm : 1 ≤ m)
    {q u X Y : ℝ} (hq : 0 < q) (_hu : 0 < u)
    (hqScale : q * (X ^ 2 + Y ^ 2) = 1) :
    (q : ℂ) * hermiteCrossResolventClosedIntegrand m X Y (q * u) =
      (q ^ (2 * m) : ℂ) * crossMehlerLeadingPhase X Y *
        crossMehlerRescaledIntegrand m q (q * X * Y) u := by
  let r : ℝ := Real.exp (-(u * q))
  have hr : 0 < r := by positivity
  have hden : 1 + r ^ 2 ≠ 0 := by positivity
  have hsq : r ^ 2 = Real.exp (-((2 * u) * q)) := by
    dsimp [r]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hpow : q * (q * u) ^ ((2 * m : ℕ) - 1) =
      q ^ (2 * m) * u ^ ((2 * m : ℕ) - 1) := by
    rw [mul_pow]
    have hsucc : 2 * m = (2 * m - 1) + 1 := by omega
    calc
      q * (q ^ (2 * m - 1) * u ^ (2 * m - 1)) =
          (q * q ^ (2 * m - 1)) * u ^ (2 * m - 1) := by ring
      _ = q ^ ((2 * m - 1) + 1) * u ^ (2 * m - 1) := by
        rw [pow_succ']
      _ = q ^ (2 * m) * u ^ (2 * m - 1) := by rw [← hsucc]
  have hpowC : (q : ℂ) * ((q : ℂ) * (u : ℂ)) ^ ((2 * m : ℕ) - 1) =
      (q : ℂ) ^ (2 * m) * (u : ℂ) ^ ((2 * m : ℕ) - 1) := by
    exact_mod_cast hpow
  have hdecay :
      -Real.pi * ((1 - r ^ 2) / (1 + r ^ 2)) * (X ^ 2 + Y ^ 2) =
        -Real.pi * crossMehlerScaledDecayRate q u := by
    rw [crossMehlerScaledDecayRate, ← hsq]
    field_simp [hq.ne', hden]
    nlinarith [hqScale]
  have hphase :
      -4 * Real.pi * Complex.I * r * X * Y / (1 + r ^ 2) =
        -2 * Real.pi * Complex.I * X * Y +
          (-2 * Real.pi * Complex.I * (q * X * Y) *
            crossMehlerScaledPhaseRate q u) := by
    dsimp [crossMehlerScaledPhaseRate, r]
    push_cast
    field_simp [hq.ne']
    ring
  have hdecayC :
      -((Real.pi : ℝ) : ℂ) *
          ((1 - (r : ℂ) ^ 2) / (1 + (r : ℂ) ^ 2)) *
            ((X : ℂ) ^ 2 + (Y : ℂ) ^ 2) =
        ((-Real.pi * crossMehlerScaledDecayRate q u : ℝ) : ℂ) := by
    exact_mod_cast hdecay
  have hphase' :
      -(4 * Real.pi * Complex.I * r * X * Y / (1 + r ^ 2)) =
        -2 * Real.pi * Complex.I * X * Y +
          (-2 * Real.pi * Complex.I * (q * X * Y) *
            crossMehlerScaledPhaseRate q u) := by
    rw [show -(4 * Real.pi * Complex.I * r * X * Y / (1 + r ^ 2)) =
      -4 * Real.pi * Complex.I * r * X * Y / (1 + r ^ 2) by ring]
    exact hphase
  have hexp : Complex.exp
      (-Real.pi * ((1 - r ^ 2) / (1 + r ^ 2)) * (X ^ 2 + Y ^ 2) -
        4 * Real.pi * Complex.I * r * X * Y / (1 + r ^ 2)) =
      ((Real.exp (-Real.pi * crossMehlerScaledDecayRate q u) : ℝ) : ℂ) *
        crossMehlerLeadingPhase X Y *
          Complex.exp
            (-2 * Real.pi * Complex.I * (q * X * Y) *
              crossMehlerScaledPhaseRate q u) := by
    rw [sub_eq_add_neg, hdecayC, hphase', Complex.exp_add,
      Complex.exp_add, crossMehlerLeadingPhase, ← Complex.ofReal_exp]
    ring
  unfold hermiteCrossResolventClosedIntegrand
  rw [normalizedHermiteCrossMehlerClosed]
  change (q : ℂ) *
      ((((q * u) ^ (2 * m - 1) * Real.exp (-(q * u)) : ℝ) : ℂ) *
        (((Real.sqrt 2 / Real.sqrt (1 + Real.exp (-(q * u)) ^ 2) : ℝ) : ℂ) *
          Complex.exp
            (-Real.pi * ((1 - Real.exp (-(q * u)) ^ 2) /
              (1 + Real.exp (-(q * u)) ^ 2)) * (X ^ 2 + Y ^ 2) -
              4 * Real.pi * Complex.I * Real.exp (-(q * u)) * X * Y /
                (1 + Real.exp (-(q * u)) ^ 2)))) = _
  rw [show -(q * u) = -(u * q) by ring]
  rw [show Real.exp (-(u * q)) = r by rfl]
  rw [hexp]
  unfold crossMehlerRescaledIntegrand crossMehlerScaledPrefactor
  dsimp only [r]
  push_cast
  let A : ℂ := Complex.exp (-((u : ℂ) * (q : ℂ)))
  let B : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) /
    ((Real.sqrt (1 + Real.exp (-(u * q)) ^ 2) : ℝ) : ℂ)
  let D : ℂ := Complex.exp
    (-Real.pi * (crossMehlerScaledDecayRate q u : ℂ))
  let P : ℂ := crossMehlerLeadingPhase X Y
  let C : ℂ := Complex.exp
    (-2 * Real.pi * Complex.I * (q * X * Y) *
      crossMehlerScaledPhaseRate q u)
  linear_combination (A * B * D * P * C) * hpowC

theorem hermiteCrossClosedResolventIntegral_eq_scaled
    (m : ℕ) (hm : 1 ≤ m)
    {q X Y : ℝ} (hq : 0 < q)
    (hqScale : q * (X ^ 2 + Y ^ 2) = 1) :
    hermiteCrossClosedResolventIntegral m X Y =
      (q ^ (2 * m) : ℂ) * crossMehlerLeadingPhase X Y *
        ∫ u : ℝ in Set.Ioi 0,
          crossMehlerRescaledIntegrand m q (q * X * Y) u := by
  let g : ℝ → ℂ := hermiteCrossResolventClosedIntegrand m X Y
  let C : ℂ := (q ^ (2 * m) : ℂ) * crossMehlerLeadingPhase X Y
  unfold hermiteCrossClosedResolventIntegral
  calc
    (∫ t : ℝ in Set.Ioi 0,
        hermiteCrossResolventClosedIntegrand m X Y t) =
        q • ∫ u : ℝ in Set.Ioi 0, g (q * u) := by
      simpa only [g, mul_zero] using
        (MeasureTheory.integral_comp_mul_left_Ioi' g 0 hq).symm
    _ = ∫ u : ℝ in Set.Ioi 0, q • g (q * u) := by
      rw [MeasureTheory.integral_smul]
    _ = ∫ u : ℝ in Set.Ioi 0,
        C * crossMehlerRescaledIntegrand m q (q * X * Y) u := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      simpa only [Complex.real_smul, g, C] using
        q_mul_hermiteCrossResolventClosedIntegrand_scaled
          m hm hq hu hqScale
    _ = C * ∫ u : ℝ in Set.Ioi 0,
        crossMehlerRescaledIntegrand m q (q * X * Y) u := by
      rw [MeasureTheory.integral_const_mul]
    _ = (q ^ (2 * m) : ℂ) * crossMehlerLeadingPhase X Y *
        ∫ u : ℝ in Set.Ioi 0,
          crossMehlerRescaledIntegrand m q (q * X * Y) u := by rfl

/-- Exact closed-integral formula for the genuinely normalized
physical/Fourier cross kernel. -/
theorem normalizedHermiteCrossKernel_eq_closedIntegral
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) :
    normalizedHermiteCrossKernel m hm x y =
      hermiteCrossClosedResolventIntegral m x y /
        ((Real.sqrt (hermiteClosedResolventIntegral m x x *
          hermiteClosedResolventIntegral m y y) : ℝ) : ℂ) := by
  let F : ℝ := ((2 * m - 1).factorial : ℝ)
  let nx : ℝ := ‖hermitePointMass m hm x‖
  let ny : ℝ := ‖hermitePointMass m hm y‖
  let Ixy : ℂ := hermiteCrossClosedResolventIntegral m x y
  let Ixx : ℝ := hermiteClosedResolventIntegral m x x
  let Iyy : ℝ := hermiteClosedResolventIntegral m y y
  have hF : 0 < F := by
    dsimp only [F]
    positivity
  have hnx : 0 < nx := by
    dsimp only [nx]
    exact norm_pos_iff.mpr (hermitePointMass_ne_zero m hm x)
  have hny : 0 < ny := by
    dsimp only [ny]
    exact norm_pos_iff.mpr (hermitePointMass_ne_zero m hm y)
  have hnormX : nx ^ 2 = F⁻¹ * Ixx := by
    simpa only [nx, F, Ixx] using
      norm_hermitePointMass_sq_eq_closedIntegral m hm x
  have hnormY : ny ^ 2 = F⁻¹ * Iyy := by
    simpa only [ny, F, Iyy] using
      norm_hermitePointMass_sq_eq_closedIntegral m hm y
  have hIxx : Ixx = F * nx ^ 2 := by
    calc
      Ixx = F * (F⁻¹ * Ixx) := by field_simp [hF.ne']
      _ = F * nx ^ 2 := by rw [← hnormX]
  have hIyy : Iyy = F * ny ^ 2 := by
    calc
      Iyy = F * (F⁻¹ * Iyy) := by field_simp [hF.ne']
      _ = F * ny ^ 2 := by rw [← hnormY]
  have hsqrt : Real.sqrt (Ixx * Iyy) = F * nx * ny := by
    rw [hIxx, hIyy]
    rw [show (F * nx ^ 2) * (F * ny ^ 2) =
        (F * nx * ny) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (mul_pos hF hnx) hny)]
  have hraw :=
    factorial_mul_hermiteCrossResolventKernel_eq_closedIntegral
      m hm x y
  have hresolvent : hermiteCrossResolventKernel m x y =
      (F : ℂ)⁻¹ * Ixy := by
    change (F : ℂ) * hermiteCrossResolventKernel m x y = Ixy at hraw
    calc
      hermiteCrossResolventKernel m x y =
          (F : ℂ)⁻¹ *
            ((F : ℂ) * hermiteCrossResolventKernel m x y) := by
        field_simp [hF.ne']
      _ = (F : ℂ)⁻¹ * Ixy := by rw [hraw]
  rw [normalizedHermiteCrossKernel, hresolvent]
  change (((nx⁻¹ * ny⁻¹ : ℝ) : ℂ) * ((F : ℂ)⁻¹ * Ixy)) = _
  rw [show hermiteCrossClosedResolventIntegral m x y = Ixy by rfl,
    show hermiteClosedResolventIntegral m x x = Ixx by rfl,
    show hermiteClosedResolventIntegral m y y = Iyy by rfl, hsqrt]
  push_cast
  field_simp [hF.ne', hnx.ne', hny.ne']

/-- A quotient by a geometric-mean normalization splits exactly when the
numerator and both diagonal terms split into positive scale and shape parts. -/
theorem closedIntegral_ratio_scale_identity_complex
    {Ixy Cxy Jxy : ℂ} {Ixx Iyy Cxx Cyy Jxx Jyy : ℝ}
    (hCxx : 0 < Cxx) (hCyy : 0 < Cyy)
    (hJxx : 0 < Jxx) (hJyy : 0 < Jyy)
    (hxy : Ixy = Cxy * Jxy)
    (hxx : Ixx = Cxx * Jxx)
    (hyy : Iyy = Cyy * Jyy) :
    Ixy / ((Real.sqrt (Ixx * Iyy) : ℝ) : ℂ) =
      (Cxy / ((Real.sqrt (Cxx * Cyy) : ℝ) : ℂ)) *
        (Jxy / ((Real.sqrt (Jxx * Jyy) : ℝ) : ℂ)) := by
  rw [hxy, hxx, hyy]
  have hC : 0 < Cxx * Cyy := mul_pos hCxx hCyy
  have hJ : 0 < Jxx * Jyy := mul_pos hJxx hJyy
  rw [show (Cxx * Jxx) * (Cyy * Jyy) =
      (Cxx * Cyy) * (Jxx * Jyy) by ring,
    Real.sqrt_mul hC.le]
  push_cast
  field_simp [Real.sqrt_ne_zero'.mpr hC, Real.sqrt_ne_zero'.mpr hJ]

/-- Exact normalized cross kernel split into its pair-scale factor and its
dimensionless integral ratio. -/
theorem normalizedHermiteCrossKernel_eq_scaledIntegralRatio
    (m : ℕ) (hm : 1 ≤ m)
    {qxy qxx qyy x y : ℝ}
    (hqxy : 0 < qxy) (hqxx : 0 < qxx) (hqyy : 0 < qyy)
    (hqxyScale : qxy * (x ^ 2 + y ^ 2) = 1)
    (hqxxScale : qxx * (|x| + |x|) ^ 2 = 1)
    (hqyyScale : qyy * (|y| + |y|) ^ 2 = 1) :
    normalizedHermiteCrossKernel m hm x y =
      ((qxy : ℂ) ^ (2 * m) * crossMehlerLeadingPhase x y /
          ((Real.sqrt (hermiteResolventScale m qxx *
            hermiteResolventScale m qyy) : ℝ) : ℂ)) *
        ((∫ u : ℝ in Set.Ioi 0,
            crossMehlerRescaledIntegrand m qxy (qxy * x * y) u) /
          ((Real.sqrt
            ((∫ u : ℝ in Set.Ioi 0,
                mehlerRescaledIntegrand m qxx 0 u) *
              ∫ u : ℝ in Set.Ioi 0,
                mehlerRescaledIntegrand m qyy 0 u) : ℝ) : ℂ)) := by
  let Axy : ℂ := ∫ u : ℝ in Set.Ioi 0,
    crossMehlerRescaledIntegrand m qxy (qxy * x * y) u
  let Axx : ℝ := ∫ u : ℝ in Set.Ioi 0,
    mehlerRescaledIntegrand m qxx 0 u
  let Ayy : ℝ := ∫ u : ℝ in Set.Ioi 0,
    mehlerRescaledIntegrand m qyy 0 u
  have hIxy : hermiteCrossClosedResolventIntegral m x y =
      (qxy : ℂ) ^ (2 * m) * crossMehlerLeadingPhase x y * Axy := by
    simpa only [Axy] using hermiteCrossClosedResolventIntegral_eq_scaled
      m hm hqxy hqxyScale
  have hIxx : hermiteClosedResolventIntegral m x x =
      hermiteResolventScale m qxx * Axx := by
    simpa only [Axx, sub_self] using
      hermiteClosedResolventIntegral_eq_scaled m hm hqxx
        (mul_self_nonneg x) hqxxScale
  have hIyy : hermiteClosedResolventIntegral m y y =
      hermiteResolventScale m qyy * Ayy := by
    simpa only [Ayy, sub_self] using
      hermiteClosedResolventIntegral_eq_scaled m hm hqyy
        (mul_self_nonneg y) hqyyScale
  have hAxx : 0 < Axx := by
    have hi := hermiteClosedResolventIntegral_self_pos m hm x
    rw [hIxx] at hi
    exact pos_of_mul_pos_right hi
      (hermiteResolventScale_pos m hqxx).le
  have hAyy : 0 < Ayy := by
    have hi := hermiteClosedResolventIntegral_self_pos m hm y
    rw [hIyy] at hi
    exact pos_of_mul_pos_right hi
      (hermiteResolventScale_pos m hqyy).le
  rw [normalizedHermiteCrossKernel_eq_closedIntegral]
  simpa only [Axy, Axx, Ayy, mul_assoc] using
    closedIntegral_ratio_scale_identity_complex
      (hermiteResolventScale_pos m hqxx)
      (hermiteResolventScale_pos m hqyy)
      hAxx hAyy hIxy hIxx hIyy

theorem integral_crossMehlerLeadingIntegrand
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ u : ℝ in Set.Ioi 0, crossMehlerLeadingIntegrand m u) =
      ((((2 * m - 1).factorial : ℝ) *
        (Real.pi⁻¹) ^ (2 * m) : ℝ) : ℂ) := by
  have hmpos : 0 < (2 * m : ℝ) := by positivity
  have hgamma :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi hmpos Real.pi_pos
  have hGamma : Real.Gamma (2 * m : ℝ) =
      ((2 * m - 1).factorial : ℝ) := by
    rw [show (2 * m : ℝ) = ((2 * m - 1 : ℕ) : ℝ) + 1 by
      norm_cast
      omega]
    exact Real.Gamma_nat_eq_factorial (2 * m - 1)
  have hweight : (1 / Real.pi) ^ (2 * m : ℝ) =
      (Real.pi⁻¹) ^ (2 * m : ℕ) := by
    rw [show (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) by norm_cast,
      Real.rpow_natCast, one_div]
  have hcast : ((2 * m - 1 : ℕ) : ℝ) = (2 * m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    norm_num
  have hrpow : ∀ u : ℝ, u ∈ Set.Ioi 0 →
      u ^ ((2 * m : ℕ) - 1) = u ^ ((2 * m : ℝ) - 1) := by
    intro u hu
    rw [← hcast, Real.rpow_natCast]
  have hreal :
      (∫ u : ℝ in Set.Ioi 0,
          u ^ ((2 * m : ℕ) - 1) * Real.exp (-Real.pi * u)) =
        ((2 * m - 1).factorial : ℝ) *
          (Real.pi⁻¹) ^ (2 * m) := by
    calc
      (∫ u : ℝ in Set.Ioi 0,
          u ^ ((2 * m : ℕ) - 1) * Real.exp (-Real.pi * u)) =
          ∫ u : ℝ in Set.Ioi 0,
            u ^ ((2 * m : ℝ) - 1) * Real.exp (-(Real.pi * u)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        change u ^ ((2 * m : ℕ) - 1) * Real.exp (-Real.pi * u) =
          u ^ ((2 * m : ℝ) - 1) * Real.exp (-(Real.pi * u))
        rw [hrpow u hu]
        congr 2
        ring
      _ = (1 / Real.pi) ^ (2 * m : ℝ) *
          Real.Gamma (2 * m : ℝ) := hgamma
      _ = ((2 * m - 1).factorial : ℝ) *
          (Real.pi⁻¹) ^ (2 * m) := by
        rw [hGamma, hweight]
        ring
  unfold crossMehlerLeadingIntegrand
  calc
    (∫ u : ℝ in Set.Ioi 0,
        ((u ^ ((2 * m : ℕ) - 1) *
          Real.exp (-Real.pi * u) : ℝ) : ℂ)) =
        ((∫ u : ℝ in Set.Ioi 0,
          u ^ ((2 * m : ℕ) - 1) *
            Real.exp (-Real.pi * u) : ℝ) : ℂ) := integral_ofReal
    _ = _ := by rw [hreal]

/-- Uniform all-ratio leading limit for the exact closed cross resolvent.
No convergence of `q X Y` is assumed; its geometric bound suffices. -/
theorem tendsto_scaledHermiteCrossClosedResolventIntegral_of_sequences
    (m : ℕ) (hm : 1 ≤ m)
    {q X Y : ℕ → ℝ}
    (hqPos : ∀ n, 0 < q n)
    (hqScale : ∀ n, q n * (X n ^ 2 + Y n ^ 2) = 1)
    (hqLim : Tendsto q atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
      (fun n => hermiteCrossClosedResolventIntegral m (X n) (Y n) /
        ((q n : ℂ) ^ (2 * m) * crossMehlerLeadingPhase (X n) (Y n)))
      atTop
      (nhds (((((2 * m - 1).factorial : ℝ) *
        (Real.pi⁻¹) ^ (2 * m) : ℝ) : ℂ))) := by
  have hratio : ∀ n, |q n * X n * Y n| ≤ 1 / 2 := fun n =>
    abs_pairRatio_le_half (hqPos n) (hqScale n)
  have hIntegral :=
    tendsto_integral_crossMehlerRescaledIntegrand_of_sequences
      m hm hqPos hqLim hratio
  rw [integral_crossMehlerLeadingIntegrand m hm] at hIntegral
  apply hIntegral.congr'
  exact Filter.Eventually.of_forall (fun n => by
    change (∫ u : ℝ in Set.Ioi 0,
        crossMehlerRescaledIntegrand m (q n) (q n * X n * Y n) u) =
      hermiteCrossClosedResolventIntegral m (X n) (Y n) /
        ((q n : ℂ) ^ (2 * m) * crossMehlerLeadingPhase (X n) (Y n))
    rw [hermiteCrossClosedResolventIntegral_eq_scaled
      m hm (hqPos n) (hqScale n)]
    have hqC : (q n : ℂ) ≠ 0 := by
      exact_mod_cast (hqPos n).ne'
    have hphase : crossMehlerLeadingPhase (X n) (Y n) ≠ 0 := by
      unfold crossMehlerLeadingPhase
      exact Complex.exp_ne_zero _
    field_simp [hqC, hphase])

/-- Uniform all-ratio leading asymptotic for the genuine phase-weighted
Hermite cross resolvent.  Its leading coefficient is exactly
`pi⁻²ᵐ`, after removal of the negative Fourier phase and pair scale. -/
theorem tendsto_scaledHermiteCrossResolventKernel_of_sequences
    (m : ℕ) (hm : 1 ≤ m)
    {q X Y : ℕ → ℝ}
    (hqPos : ∀ n, 0 < q n)
    (hqScale : ∀ n, q n * (X n ^ 2 + Y n ^ 2) = 1)
    (hqLim : Tendsto q atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
      (fun n => hermiteCrossResolventKernel m (X n) (Y n) /
        ((q n : ℂ) ^ (2 * m) * crossMehlerLeadingPhase (X n) (Y n)))
      atTop
      (nhds ((((Real.pi⁻¹) ^ (2 * m) : ℝ) : ℂ))) := by
  let factorialC : ℂ := (((2 * m - 1).factorial : ℝ) : ℂ)
  have hfactorialC : factorialC ≠ 0 := by
    dsimp only [factorialC]
    exact_mod_cast Nat.factorial_ne_zero (2 * m - 1)
  have hClosed :=
    tendsto_scaledHermiteCrossClosedResolventIntegral_of_sequences
      m hm hqPos hqScale hqLim
  have hScaled :=
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => factorialC⁻¹) atTop
      (nhds factorialC⁻¹)).mul hClosed
  have hlimit : factorialC⁻¹ *
      (((((2 * m - 1).factorial : ℝ) *
        (Real.pi⁻¹) ^ (2 * m) : ℝ) : ℂ)) =
      ((((Real.pi⁻¹) ^ (2 * m) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_mul]
    change factorialC⁻¹ *
      (factorialC * ((((Real.pi⁻¹) ^ (2 * m) : ℝ) : ℂ))) = _
    rw [← mul_assoc, inv_mul_cancel₀ hfactorialC, one_mul]
  rw [hlimit] at hScaled
  apply hScaled.congr'
  exact Filter.Eventually.of_forall (fun n => by
    change factorialC⁻¹ *
        (hermiteCrossClosedResolventIntegral m (X n) (Y n) /
          ((q n : ℂ) ^ (2 * m) *
            crossMehlerLeadingPhase (X n) (Y n))) =
      hermiteCrossResolventKernel m (X n) (Y n) /
        ((q n : ℂ) ^ (2 * m) *
          crossMehlerLeadingPhase (X n) (Y n))
    rw [← factorial_mul_hermiteCrossResolventKernel_eq_closedIntegral
      m hm (X n) (Y n)]
    change factorialC⁻¹ *
        (factorialC * hermiteCrossResolventKernel m (X n) (Y n) / _) = _
    simp only [div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ hfactorialC, one_mul])

/-- Full-sequence all-ratio leading limit for the genuinely diagonally
normalized physical/Fourier cross kernel, after division by its exact
pair/diagonal scale and leading phase. -/
theorem tendsto_normalizedHermiteCrossKernel_div_leadingScale_of_sequences
    (m : ℕ) (hm : 1 ≤ m)
    {qxy qxx qyy X Y : ℕ → ℝ}
    (hqxyPos : ∀ n, 0 < qxy n)
    (hqxxPos : ∀ n, 0 < qxx n)
    (hqyyPos : ∀ n, 0 < qyy n)
    (hqxxOne : ∀ᶠ n in atTop, qxx n ≤ 1)
    (hqyyOne : ∀ᶠ n in atTop, qyy n ≤ 1)
    (hqxyScale : ∀ n, qxy n * (X n ^ 2 + Y n ^ 2) = 1)
    (hqxxScale : ∀ n, qxx n * (|X n| + |X n|) ^ 2 = 1)
    (hqyyScale : ∀ n, qyy n * (|Y n| + |Y n|) ^ 2 = 1)
    (hqxyLim : Tendsto qxy atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hqxxLim : Tendsto qxx atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hqyyLim : Tendsto qyy atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
      (fun n => normalizedHermiteCrossKernel m hm (X n) (Y n) /
        (((qxy n : ℂ) ^ (2 * m) *
            crossMehlerLeadingPhase (X n) (Y n)) /
          ((Real.sqrt (hermiteResolventScale m (qxx n) *
            hermiteResolventScale m (qyy n)) : ℝ) : ℂ)))
      atTop
      (nhds (((((2 * m - 1).factorial : ℝ) *
        (Real.pi⁻¹) ^ (2 * m) : ℝ) : ℂ) /
          (hermiteUniversalLimitIntegral m 0 : ℂ))) := by
  let Axy : ℕ → ℂ := fun n => ∫ u : ℝ in Set.Ioi 0,
    crossMehlerRescaledIntegrand m (qxy n) (qxy n * X n * Y n) u
  let Axx : ℕ → ℝ := fun n => ∫ u : ℝ in Set.Ioi 0,
    mehlerRescaledIntegrand m (qxx n) 0 u
  let Ayy : ℕ → ℝ := fun n => ∫ u : ℝ in Set.Ioi 0,
    mehlerRescaledIntegrand m (qyy n) 0 u
  let Cxy : ℂ := ((((2 * m - 1).factorial : ℝ) *
    (Real.pi⁻¹) ^ (2 * m) : ℝ) : ℂ)
  let J0 : ℝ := hermiteUniversalLimitIntegral m 0
  have hratio : ∀ n, |qxy n * X n * Y n| ≤ 1 / 2 := fun n =>
    abs_pairRatio_le_half (hqxyPos n) (hqxyScale n)
  have hAxy : Tendsto Axy atTop (nhds Cxy) := by
    have hraw := tendsto_integral_crossMehlerRescaledIntegrand_of_sequences
      m hm hqxyPos hqxyLim hratio
    rw [integral_crossMehlerLeadingIntegrand m hm] at hraw
    simpa only [Axy, Cxy] using hraw
  have hzeroX : Tendsto
      (fun n => signedSquare (X n) - signedSquare (X n))
      atTop (nhds 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ))
      atTop (nhds 0))
  have hzeroY : Tendsto
      (fun n => signedSquare (Y n) - signedSquare (Y n))
      atTop (nhds 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ))
      atTop (nhds 0))
  have hAxx : Tendsto Axx atTop (nhds J0) := by
    simpa only [Axx, J0, hermiteUniversalLimitIntegral, sub_self] using
      tendsto_integral_mehlerRescaledIntegrand_of_sequences
        m hm hqxxPos hqxxOne (fun n => mul_self_nonneg (X n))
          hqxxScale hqxxLim hzeroX
  have hAyy : Tendsto Ayy atTop (nhds J0) := by
    simpa only [Ayy, J0, hermiteUniversalLimitIntegral, sub_self] using
      tendsto_integral_mehlerRescaledIntegrand_of_sequences
        m hm hqyyPos hqyyOne (fun n => mul_self_nonneg (Y n))
          hqyyScale hqyyLim hzeroY
  have hJ0 : 0 < J0 := by
    simpa only [J0] using hermiteUniversalLimitIntegral_zero_pos m hm
  have hprod : Tendsto (fun n => Axx n * Ayy n) atTop
      (nhds (J0 * J0)) := hAxx.mul hAyy
  have hsqrtRaw := (Real.continuous_sqrt.tendsto (J0 * J0)).comp hprod
  have hsqrt : Tendsto (fun n => Real.sqrt (Axx n * Ayy n)) atTop
      (nhds J0) := by
    have hsq : Real.sqrt (J0 * J0) = J0 := by
      rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hJ0]
    rw [hsq] at hsqrtRaw
    exact hsqrtRaw
  have hshape : Tendsto
      (fun n => Axy n / ((Real.sqrt (Axx n * Ayy n) : ℝ) : ℂ))
      atTop (nhds (Cxy / (J0 : ℂ))) := by
    exact hAxy.div hsqrt.ofReal (by exact_mod_cast hJ0.ne')
  apply hshape.congr'
  filter_upwards with n
  let S : ℂ := ((qxy n : ℂ) ^ (2 * m) *
      crossMehlerLeadingPhase (X n) (Y n)) /
    ((Real.sqrt (hermiteResolventScale m (qxx n) *
      hermiteResolventScale m (qyy n)) : ℝ) : ℂ)
  have hscaleProd : 0 < hermiteResolventScale m (qxx n) *
      hermiteResolventScale m (qyy n) := mul_pos
    (hermiteResolventScale_pos m (hqxxPos n))
    (hermiteResolventScale_pos m (hqyyPos n))
  have hS : S ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (hqxyPos n).ne'))
        (by unfold crossMehlerLeadingPhase; exact Complex.exp_ne_zero _)
    · exact_mod_cast Real.sqrt_ne_zero'.mpr hscaleProd
  change Axy n / ((Real.sqrt (Axx n * Ayy n) : ℝ) : ℂ) =
    normalizedHermiteCrossKernel m hm (X n) (Y n) / S
  rw [normalizedHermiteCrossKernel_eq_scaledIntegralRatio m hm
    (hqxyPos n) (hqxxPos n) (hqyyPos n)
    (hqxyScale n) (hqxxScale n) (hqyyScale n)]
  change _ = (S *
    (Axy n / ((Real.sqrt (Axx n * Ayy n) : ℝ) : ℂ))) / S
  field_simp [hS]

end

end MeyerGeneralProblem
