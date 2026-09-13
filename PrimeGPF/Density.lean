import PrimeGPF.Counting
import PrimeGPF.Progressions
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

/-!
Asymptotic density results for theorem 6.3.

The theorem remains conditional only on `PrimeAPInput`, the same
PNT-in-arithmetic-progressions input already used for theorem 6.1.
The finite smooth-number and pair-count bounds are proved
unconditionally in `PrimeGPF.Counting`.
-/

namespace PrimeGPF
open Claims

/-- Every prime in one residue class is, in particular, a prime. -/
theorem apCount_le_primeCount
    (r c x : ℕ) :
    Claims.apCount r c x ≤ Claims.primeCount x := by
  classical
  unfold Claims.apCount Claims.primeCount
  apply Finset.card_le_card
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  exact ⟨hq'.1, hq'.2.1⟩

/--
Our primeCount is mathlib's primeCounting function.
-/
theorem primeCount_eq_primeCounting
    (x : ℕ) :
    Claims.primeCount x = Nat.primeCounting x := by
  classical
  unfold Claims.primeCount Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]


/--
If an AP count has the stated PNT-in-AP asymptotic, then eventually it is
at least one half of its asymptotic main term.
-/
theorem APAsymptotic.eventually_half_mainTerm_le
    {r c : ℕ}
    (hr : Nat.Prime r)
    (hA : Claims.APAsymptotic r c) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (1 / 2 : ℝ) *
          ((x : ℝ) /
            (((r : ℝ) - 1) * Real.log (x : ℝ)))
        ≤ (Claims.apCount r c x : ℝ) := by

  have hhalf :
      ∀ᶠ x : ℕ in Filter.atTop,
        (1 / 2 : ℝ) <
          (Claims.apCount r c x : ℝ) /
            ((x : ℝ) /
              (((r : ℝ) - 1) * Real.log (x : ℝ))) := by
    exact
      (tendsto_order.1 hA).1
        (1 / 2 : ℝ)
        (by norm_num)

  filter_upwards
    [hhalf, Filter.eventually_ge_atTop (2 : ℕ)]
      with x hxratio hx2

  have hr2 : 2 ≤ r :=
    hr.two_le

  have hx1 : 1 < x := by
    omega

  have hxR : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast hx1

  have hlog :
      0 < Real.log (x : ℝ) :=
    Real.log_pos hxR

  have hrR :
      (1 : ℝ) < (r : ℝ) := by
    exact_mod_cast (show 1 < r by omega)

  have hrminus :
      0 < (r : ℝ) - 1 := by
    linarith

  have hden :
      0 <
        ((r : ℝ) - 1) *
          Real.log (x : ℝ) :=
    mul_pos hrminus hlog

  have hmain :
      0 <
        (x : ℝ) /
          (((r : ℝ) - 1) *
            Real.log (x : ℝ)) := by
    positivity

  exact
    le_of_lt
      ((lt_div_iff₀ hmain).mp hxratio)




/--
The single progression 1 mod 3 already gives an eventual lower bound for
the total prime-counting function.
-/
theorem PrimeAPInput.eventually_AP3_lower_le_primeCount
    (H : PrimeAPInput) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (1 / 2 : ℝ) *
          ((x : ℝ) /
            (((3 : ℝ) - 1) * Real.log (x : ℝ)))
        ≤ (Claims.primeCount x : ℝ) := by

  have hA : Claims.APAsymptotic 3 1 :=
    H 3 1
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by norm_num)

  have hhalf :=
    APAsymptotic.eventually_half_mainTerm_le
      (r := 3) (c := 1)
      (by norm_num)
      hA

  filter_upwards [hhalf] with x hx

  have hap :
      (Claims.apCount 3 1 x : ℝ)
        ≤ (Claims.primeCount x : ℝ) := by
    exact_mod_cast apCount_le_primeCount 3 1 x

  exact hx.trans hap




open Filter Asymptotics

/--
Every fixed natural power of log x is little-o of x.
-/
theorem isLittleO_log_pow_id_atTop
    (k : ℕ) :
    (fun x : ℝ => (Real.log x) ^ k)
      =o[Filter.atTop] (fun x : ℝ => x) := by

  have h :=
    isLittleO_log_rpow_rpow_atTop
      (k : ℝ)
      (s := (1 : ℝ))
      zero_lt_one

  simpa only [Real.rpow_natCast, Real.rpow_one] using h


/--
Natural-number version of (log x)^k / x -> 0.
-/
theorem tendsto_log_pow_div_natCast_atTop
    (k : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Real.log (n : ℝ)) ^ k / (n : ℝ))
      Filter.atTop
      (nhds 0) := by

  have hreal :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log x) ^ k / x)
        Filter.atTop
        (nhds 0) :=
    (isLittleO_log_pow_id_atTop k).tendsto_div_nhds_zero

  have hcast :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ))
        Filter.atTop
        Filter.atTop :=
    tendsto_natCast_atTop_atTop

  simpa only [Function.comp_apply] using
    hreal.comp hcast




/--
Under the PNT-in-AP input, every fixed power of log divided by the total
prime count tends to zero.
-/
theorem PrimeAPInput.tendsto_log_pow_div_primeCount
    (H : PrimeAPInput)
    (k : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Real.log (n : ℝ)) ^ k /
          (Claims.primeCount n : ℝ))
      Filter.atTop
      (nhds 0) := by

  have hprimeLower :=
    H.eventually_AP3_lower_le_primeCount

  have hmajor :
      Filter.Tendsto
        (fun n : ℕ =>
          4 *
            ((Real.log (n : ℝ)) ^ (k + 1) /
              (n : ℝ)))
        Filter.atTop
        (nhds 0) := by
    simpa using
      (Tendsto.const_mul
        (4 : ℝ)
        (tendsto_log_pow_div_natCast_atTop (k + 1)))

  apply squeeze_zero'

  · filter_upwards
      [hprimeLower,
       Filter.eventually_ge_atTop (2 : ℕ)]
        with n hpc hn

    have hnpos : 0 < n := by
      omega

    have hnR :
        0 < (n : ℝ) := by
      exact_mod_cast hnpos

    have hn1 : 1 < n := by
      omega

    have hn1R :
        (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn1

    have hlog :
        0 < Real.log (n : ℝ) :=
      Real.log_pos hn1R

    have hbase :
        0 <
          (1 / 2 : ℝ) *
            ((n : ℝ) /
              (((3 : ℝ) - 1) *
                Real.log (n : ℝ))) := by
      positivity

    have hprime :
        0 < (Claims.primeCount n : ℝ) :=
      lt_of_lt_of_le hbase hpc

    exact
      div_nonneg
        (pow_nonneg hlog.le k)
        hprime.le

  · filter_upwards
      [hprimeLower,
       Filter.eventually_ge_atTop (2 : ℕ)]
        with n hpc hn

    have hnpos : 0 < n := by
      omega

    have hnR :
        0 < (n : ℝ) := by
      exact_mod_cast hnpos

    have hn1 : 1 < n := by
      omega

    have hn1R :
        (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn1

    have hlog :
        0 < Real.log (n : ℝ) :=
      Real.log_pos hn1R

    have hbase :
        0 <
          (1 / 2 : ℝ) *
            ((n : ℝ) /
              (((3 : ℝ) - 1) *
                Real.log (n : ℝ))) := by
      positivity

    have hstep :
        (Real.log (n : ℝ)) ^ k /
            (Claims.primeCount n : ℝ)
          ≤
        (Real.log (n : ℝ)) ^ k /
          ((1 / 2 : ℝ) *
            ((n : ℝ) /
              (((3 : ℝ) - 1) *
                Real.log (n : ℝ)))) :=
      div_le_div_of_nonneg_left
        (pow_nonneg hlog.le k)
        hbase
        hpc

    calc
      (Real.log (n : ℝ)) ^ k /
          (Claims.primeCount n : ℝ)
        ≤
          (Real.log (n : ℝ)) ^ k /
            ((1 / 2 : ℝ) *
              ((n : ℝ) /
                (((3 : ℝ) - 1) *
                  Real.log (n : ℝ)))) :=
        hstep

      _ =
          4 *
            ((Real.log (n : ℝ)) ^ (k + 1) /
              (n : ℝ)) := by
        rw [pow_succ]
        norm_num
        field_simp [hlog.ne', hnR.ne']
        ring

  · exact hmajor




/--
Evaluating the smooth-count bound at (n+1)^2 only changes the
polylogarithmic constant.
-/
theorem smoothCount_succ_sq_polylog
    (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∃ N : ℕ, ∀ n, N ≤ n →
        (Claims.smoothCount r ((n + 1) * (n + 1)) : ℝ)
          ≤ C * (Real.log (n : ℝ)) ^ Claims.primeCount r := by

  obtain ⟨C, hC, N, hN⟩ :=
    proof_smoothPolylog r

  let C' : ℝ :=
    C * (4 : ℝ) ^ Claims.primeCount r

  refine ⟨C', ?_, max N 2, ?_⟩

  · dsimp [C']
    positivity

  · intro n hn

    have hnN : N ≤ n :=
      le_trans (le_max_left N 2) hn

    have hn2 : 2 ≤ n :=
      le_trans (le_max_right N 2) hn

    have hn1 : 1 ≤ n := by
      omega

    have hnpos : 0 < n := by
      omega

    have hn1R :
        (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn1

    have hnposR :
        0 < (n : ℝ) := by
      exact_mod_cast hnpos

    have hlogn :
        0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg hn1R

    have hsquare_ge :
        N ≤ (n + 1) * (n + 1) := by
      have hn_le_sq :
          n ≤ (n + 1) * (n + 1) := by
        nlinarith
      exact hnN.trans hn_le_sq

    have hsmooth :=
      hN ((n + 1) * (n + 1)) hsquare_ge

    have hsucc_le_sq :
        n + 1 ≤ n * n := by
      nlinarith

    have hsquares :
        (n + 1) * (n + 1)
          ≤ (n * n) * (n * n) :=
      Nat.mul_le_mul hsucc_le_sq hsucc_le_sq

    have hleftpos :
        0 < (((n + 1) * (n + 1) : ℕ) : ℝ) := by
      positivity

    have hlog_le :
        Real.log
            (((n + 1) * (n + 1) : ℕ) : ℝ)
          ≤
        4 * Real.log (n : ℝ) := by

      have hcast :
          ((((n + 1) * (n + 1) : ℕ) : ℝ))
            ≤ (((n * n) * (n * n) : ℕ) : ℝ) := by
        exact_mod_cast hsquares

      calc
        Real.log
            (((n + 1) * (n + 1) : ℕ) : ℝ)
          ≤
            Real.log
              (((n * n) * (n * n) : ℕ) : ℝ) := by
              exact Real.log_le_log hleftpos hcast

        _ = Real.log (((n : ℝ) ^ 4)) := by
              congr 1
              norm_num [pow_succ]
              ring

        _ = 4 * Real.log (n : ℝ) := by
              rw [Real.log_pow]
              norm_num

    have hlogleft :
        0 ≤
          Real.log
            (((n + 1) * (n + 1) : ℕ) : ℝ) := by
      exact Real.log_nonneg (by
        have hprodpos : 0 < (n + 1) * (n + 1) :=
          Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)
        have : (1 : ℕ) ≤ (n + 1) * (n + 1) := by
          omega
        exact_mod_cast this)

    have hpow :
        (Real.log
            (((n + 1) * (n + 1) : ℕ) : ℝ)) ^
              Claims.primeCount r
          ≤
        (4 * Real.log (n : ℝ)) ^
              Claims.primeCount r := by
      gcongr

    calc
      (Claims.smoothCount r ((n + 1) * (n + 1)) : ℝ)
        ≤
          C *
            (Real.log
              (((n + 1) * (n + 1) : ℕ) : ℝ)) ^
                Claims.primeCount r :=
        hsmooth

      _ ≤
          C *
            (4 * Real.log (n : ℝ)) ^
              Claims.primeCount r := by
        gcongr

      _ =
          C' *
            (Real.log (n : ℝ)) ^
              Claims.primeCount r := by
        dsimp [C']
        rw [mul_pow]
        ring




/--
Under PrimeAPInput, the r-smooth count at the quadratic cutoff
(n+1)^2 is negligible relative to the total prime count.
-/
theorem PrimeAPInput.tendsto_smoothCount_succ_sq_div_primeCount
    (H : PrimeAPInput)
    (r : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Claims.smoothCount r ((n + 1) * (n + 1)) : ℝ) /
          (Claims.primeCount n : ℝ))
      Filter.atTop
      (nhds 0) := by

  obtain ⟨C, hC, N, hN⟩ :=
    smoothCount_succ_sq_polylog r

  let k := Claims.primeCount r

  have hprimeLower :=
    H.eventually_AP3_lower_le_primeCount

  have hmajor :
      Filter.Tendsto
        (fun n : ℕ =>
          C *
            ((Real.log (n : ℝ)) ^ k /
              (Claims.primeCount n : ℝ)))
        Filter.atTop
        (nhds 0) := by
    simpa only [mul_zero] using
      (Tendsto.const_mul C
        (H.tendsto_log_pow_div_primeCount k))

  apply squeeze_zero'

  · filter_upwards
      [hprimeLower,
       Filter.eventually_ge_atTop (max N 2)]
        with n hpc hn

    have hn2 : 2 ≤ n :=
      le_trans (le_max_right N 2) hn

    have hn1 : 1 < n := by
      omega

    have hn1R :
        (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn1

    have hlog :
        0 < Real.log (n : ℝ) :=
      Real.log_pos hn1R

    have hbase :
        0 <
          (1 / 2 : ℝ) *
            ((n : ℝ) /
              (((3 : ℝ) - 1) *
                Real.log (n : ℝ))) := by
      positivity

    have hprime :
        0 < (Claims.primeCount n : ℝ) :=
      lt_of_lt_of_le hbase hpc

    exact
      div_nonneg
        (by positivity)
        hprime.le

  · filter_upwards
      [hprimeLower,
       Filter.eventually_ge_atTop (max N 2)]
        with n hpc hn

    have hnN : N ≤ n :=
      le_trans (le_max_left N 2) hn

    have hn2 : 2 ≤ n :=
      le_trans (le_max_right N 2) hn

    have hn1 : 1 < n := by
      omega

    have hn1R :
        (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn1

    have hlog :
        0 < Real.log (n : ℝ) :=
      Real.log_pos hn1R

    have hbase :
        0 <
          (1 / 2 : ℝ) *
            ((n : ℝ) /
              (((3 : ℝ) - 1) *
                Real.log (n : ℝ))) := by
      positivity

    have hprime :
        0 < (Claims.primeCount n : ℝ) :=
      lt_of_lt_of_le hbase hpc

    have hsmooth :=
      hN n hnN

    calc
      (Claims.smoothCount r ((n + 1) * (n + 1)) : ℝ) /
          (Claims.primeCount n : ℝ)
        ≤
          (C * (Real.log (n : ℝ)) ^ k) /
            (Claims.primeCount n : ℝ) := by
          gcongr

      _ =
          C *
            ((Real.log (n : ℝ)) ^ k /
              (Claims.primeCount n : ℝ)) := by
          ring

  · exact hmajor




theorem PrimeAPInput.pairZero_of_pairCount_le
    (H : PrimeAPInput)
    {o : Op}
    {r : ℕ}
    (hpair :
      ∀ n,
        Claims.pairCount o r n
          ≤ Claims.primeCount n *
              Claims.smoothCount r ((n + 1) * (n + 1))) :
    Claims.PairZero o r := by

  unfold Claims.PairZero

  have hsmooth :=
    H.tendsto_smoothCount_succ_sq_div_primeCount r

  have hprimeLower :=
    H.eventually_AP3_lower_le_primeCount

  apply squeeze_zero'

  · exact Filter.Eventually.of_forall (fun n => by
      positivity)

  · filter_upwards
      [hprimeLower,
       Filter.eventually_ge_atTop (2 : ℕ)]
        with n hpc hn

    have hn1 : 1 < n := by
      omega

    have hn1R :
        (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn1

    have hlog :
        0 < Real.log (n : ℝ) :=
      Real.log_pos hn1R

    have hbase :
        0 <
          (1 / 2 : ℝ) *
            ((n : ℝ) /
              (((3 : ℝ) - 1) *
                Real.log (n : ℝ))) := by
      positivity

    have hprime :
        0 < (Claims.primeCount n : ℝ) :=
      lt_of_lt_of_le hbase hpc

    have hpairR :
        (Claims.pairCount o r n : ℝ)
          ≤
        (Claims.primeCount n : ℝ) *
          (Claims.smoothCount r
            ((n + 1) * (n + 1)) : ℝ) := by
      exact_mod_cast hpair n

    rw [div_le_iff₀ (sq_pos_of_pos hprime)]

    calc
      (Claims.pairCount o r n : ℝ)
        ≤
          (Claims.primeCount n : ℝ) *
            (Claims.smoothCount r
              ((n + 1) * (n + 1)) : ℝ) :=
        hpairR

      _ =
          ((Claims.smoothCount r
              ((n + 1) * (n + 1)) : ℝ) /
            (Claims.primeCount n : ℝ)) *
            (Claims.primeCount n : ℝ) ^ 2 := by
        field_simp [hprime.ne']
        ring

  · exact hsmooth


/--
The additive pair density is zero under the same PNT-in-AP input used in 6.1.
-/
theorem PrimeAPInput.pairZero_add
    (H : PrimeAPInput)
    (r : ℕ)
    (hr : Nat.Prime r) :
    Claims.PairZero .add r := by

  apply H.pairZero_of_pairCount_le
  intro n
  exact pairCount_add_le
    (r := r) (x := n) hr


/--
The multiplicative pair density is zero under the same PNT-in-AP input used in 6.1.
-/
theorem PrimeAPInput.pairZero_mul
    (H : PrimeAPInput)
    (r : ℕ)
    (hr : Nat.Prime r) :
    Claims.PairZero .mul r := by

  apply H.pairZero_of_pairCount_le
  intro n
  exact pairCount_mul_le
    (r := r) (x := n) hr



/--
For a prime modulus, an AP count with the stated PNT-in-AP asymptotic
dominates every fixed power of log.
-/
theorem APAsymptotic.tendsto_log_pow_div_apCount
    {r c : ℕ}
    (hr : Nat.Prime r)
    (hA : Claims.APAsymptotic r c)
    (k : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Real.log (n : ℝ)) ^ k /
          (Claims.apCount r c n : ℝ))
      Filter.atTop
      (nhds 0) := by

  have hAPLower :=
    APAsymptotic.eventually_half_mainTerm_le hr hA

  let A : ℝ := 2 * ((r : ℝ) - 1)

  have hmajor :
      Filter.Tendsto
        (fun n : ℕ =>
          A *
            ((Real.log (n : ℝ)) ^ (k + 1) /
              (n : ℝ)))
        Filter.atTop
        (nhds 0) := by
    simpa only [mul_zero] using
      (Tendsto.const_mul A
        (tendsto_log_pow_div_natCast_atTop (k + 1)))

  apply squeeze_zero'

  · filter_upwards
      [hAPLower,
       Filter.eventually_ge_atTop (2 : ℕ)]
        with n hap hn

    have hn1 : 1 < n := by
      omega

    have hn1R :
        (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn1

    have hlog :
        0 < Real.log (n : ℝ) :=
      Real.log_pos hn1R

    have hr1 : 1 < r :=
      hr.one_lt

    have hr1R :
        (1 : ℝ) < (r : ℝ) := by
      exact_mod_cast hr1

    have hrminus :
        0 < (r : ℝ) - 1 := by
      linarith

    have hbase :
        0 <
          (1 / 2 : ℝ) *
            ((n : ℝ) /
              (((r : ℝ) - 1) *
                Real.log (n : ℝ))) := by
      positivity

    have hapPos :
        0 < (Claims.apCount r c n : ℝ) :=
      lt_of_lt_of_le hbase hap

    exact
      div_nonneg
        (pow_nonneg hlog.le k)
        hapPos.le

  · filter_upwards
      [hAPLower,
       Filter.eventually_ge_atTop (2 : ℕ)]
        with n hap hn

    have hnpos : 0 < n := by
      omega

    have hnR :
        0 < (n : ℝ) := by
      exact_mod_cast hnpos

    have hn1 : 1 < n := by
      omega

    have hn1R :
        (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn1

    have hlog :
        0 < Real.log (n : ℝ) :=
      Real.log_pos hn1R

    have hr1 : 1 < r :=
      hr.one_lt

    have hr1R :
        (1 : ℝ) < (r : ℝ) := by
      exact_mod_cast hr1

    have hrminus :
        0 < (r : ℝ) - 1 := by
      linarith

    have hbase :
        0 <
          (1 / 2 : ℝ) *
            ((n : ℝ) /
              (((r : ℝ) - 1) *
                Real.log (n : ℝ))) := by
      positivity

    have hstep :
        (Real.log (n : ℝ)) ^ k /
            (Claims.apCount r c n : ℝ)
          ≤
        (Real.log (n : ℝ)) ^ k /
          ((1 / 2 : ℝ) *
            ((n : ℝ) /
              (((r : ℝ) - 1) *
                Real.log (n : ℝ)))) :=
      div_le_div_of_nonneg_left
        (pow_nonneg hlog.le k)
        hbase
        hap

    calc
      (Real.log (n : ℝ)) ^ k /
          (Claims.apCount r c n : ℝ)
        ≤
          (Real.log (n : ℝ)) ^ k /
            ((1 / 2 : ℝ) *
              ((n : ℝ) /
                (((r : ℝ) - 1) *
                  Real.log (n : ℝ)))) :=
        hstep

      _ =
          A *
            ((Real.log (n : ℝ)) ^ (k + 1) /
              (n : ℝ)) := by
        dsimp [A]
        rw [pow_succ]
        field_simp [hlog.ne', hnR.ne', hrminus.ne']
        ring

  · exact hmajor



/--
A polylogarithmic fiber bound divided by an arithmetic-progression
count with the stated PNT asymptotic has relative density zero.
-/
theorem relativeZero_of_polylog_AP
    {o : Op}
    {a r c : ℕ}
    (hr : Nat.Prime r)
    (hA : Claims.APAsymptotic r c)
    (C : ℝ)
    (N : ℕ)
    (hfiber :
      ∀ n, N ≤ n →
        (Claims.fiberCount o a r n : ℝ)
          ≤ C *
              (Real.log (n : ℝ)) ^
                Claims.primeCount r)
    (hcount :
      ∀ n,
        Claims.divisorCount o a r n =
          Claims.apCount r c n) :
    Claims.RelativeZero o a r := by

  unfold Claims.RelativeZero

  have hAPLower :=
    APAsymptotic.eventually_half_mainTerm_le hr hA

  have hmajor :
      Filter.Tendsto
        (fun n : ℕ =>
          C *
            ((Real.log (n : ℝ)) ^
                Claims.primeCount r /
              (Claims.apCount r c n : ℝ)))
        Filter.atTop
        (nhds 0) := by
    simpa only [mul_zero] using
      (Tendsto.const_mul C
        (APAsymptotic.tendsto_log_pow_div_apCount
          hr hA (Claims.primeCount r)))

  apply squeeze_zero'

  · exact Filter.Eventually.of_forall (fun n => by
      positivity)

  · filter_upwards
      [hAPLower,
       Filter.eventually_ge_atTop (max N 2)]
        with n hap hn

    have hnN : N ≤ n :=
      le_trans (le_max_left N 2) hn

    have hn2 : 2 ≤ n :=
      le_trans (le_max_right N 2) hn

    have hnpos : 0 < n := by
      omega

    have hnR :
        0 < (n : ℝ) := by
      exact_mod_cast hnpos

    have hn1 : 1 < n := by
      omega

    have hn1R :
        (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn1

    have hlog :
        0 < Real.log (n : ℝ) :=
      Real.log_pos hn1R

    have hr1 : 1 < r :=
      hr.one_lt

    have hr1R :
        (1 : ℝ) < (r : ℝ) := by
      exact_mod_cast hr1

    have hrminus :
        0 < (r : ℝ) - 1 := by
      linarith

    have hbase :
        0 <
          (1 / 2 : ℝ) *
            ((n : ℝ) /
              (((r : ℝ) - 1) *
                Real.log (n : ℝ))) := by
      positivity

    have hapPos :
        0 < (Claims.apCount r c n : ℝ) :=
      lt_of_lt_of_le hbase hap

    have hf := hfiber n hnN

    calc
      (Claims.fiberCount o a r n : ℝ) /
          (Claims.divisorCount o a r n : ℝ)
        =
          (Claims.fiberCount o a r n : ℝ) /
            (Claims.apCount r c n : ℝ) := by
              rw [hcount n]

      _ ≤
          (C *
            (Real.log (n : ℝ)) ^
              Claims.primeCount r) /
            (Claims.apCount r c n : ℝ) := by
              exact
                (div_le_div_iff_of_pos_right hapPos).2 hf

      _ =
          C *
            ((Real.log (n : ℝ)) ^
                Claims.primeCount r /
              (Claims.apCount r c n : ℝ)) := by
              ring

  · exact hmajor



/--
Conditional proof of theorem 6.3 from exactly the same PNT-in-AP
input used for theorem 6.1.
-/
theorem proof_6_3_from_PNT_AP
    (H : PrimeAPInput) :
    Claims.t6_3 := by

  intro r hr hr2

  rcases proof_uniformPolylogFibers r hr with
    ⟨C, _, hU⟩

  refine ⟨?_, ?_, ?_⟩

  · intro a ha

    obtain ⟨N, hN⟩ :=
      hU a ha

    constructor

    · intro har

      obtain ⟨c, hc0, hcr, hc, hcount⟩ :=
        multiplicative_progression ha hr har

      have hA :
          Claims.APAsymptotic r c :=
        H r c hr hr2 hc0 hcr

      exact
        relativeZero_of_polylog_AP
          (o := .mul)
          (a := a)
          (r := r)
          (c := c)
          hr
          hA
          C
          N
          (fun n hn => (hN n hn).2)
          hcount

    · intro har

      obtain ⟨c, hc0, hcr, hc, hcount⟩ :=
        additive_progression hr har

      have hA :
          Claims.APAsymptotic r c :=
        H r c hr hr2 hc0 hcr

      exact
        relativeZero_of_polylog_AP
          (o := .add)
          (a := a)
          (r := r)
          (c := c)
          hr
          hA
          C
          N
          (fun n hn => (hN n hn).1)
          hcount

  · exact
      H.pairZero_mul r hr

  · exact
      H.pairZero_add r hr

end PrimeGPF
