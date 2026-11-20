import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementD
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

namespace Formalism.L2.Th1.B.Wr

open MvPowerSeries

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Conclude with `hasSubst_of_constantCoeff_zero ha`.
-/
private theorem hasSubst_fin_three_of_constantCoeff_eq_zero {a : Fin 3 → MvPowerSeries (Fin 3) K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  exact hasSubst_of_constantCoeff_zero ha

/- English proof (translation)
The claim follows from `hasSubst_fin_three_of_constantCoeff_eq_zero (fun s => by fin_cases s <;> simp)`.
-/
theorem hasSubst_restrictThirdZero : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1, 0] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero (fun s => by fin_cases s <;> simp)

/- English proof (translation)
Rewrite using `[rescale_eq_subst]`. Unfold `Formalism.L2.Th1.B.ev3`. Use `congr 1`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `fin_cases s <;> simp`.
-/
theorem restrictThirdZero_eq_rescale (h : MvPowerSeries (Fin 3) K) : ev3 h = rescale ![1, 1, 0] h := by
  rw [rescale_eq_subst]
  unfold Formalism.L2.Th1.B.ev3
  congr 1
  funext s
  fin_cases s <;> simp

/- English proof (translation)
Rewrite using `[restrictThirdZero_eq_rescale]`. Rewrite using `[coeff_rescale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]`. Simplify using `[hn]`.
-/
theorem coeff_restrictThirdZero (h : MvPowerSeries (Fin 3) K) (n : Fin 3 →₀ ℕ) (hn : n 2 = 0) :
    coeff n (ev3 h) = coeff n h := by
  rw [restrictThirdZero_eq_rescale]
  rw [coeff_rescale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
  simp [hn]

/- English proof (translation)
Simplify using `only [restrictThirdZero_eq_rescale, map_mul]`.
-/
theorem restrictThirdZero_mul (f g : MvPowerSeries (Fin 3) K) : ev3 (f * g) = ev3 f * ev3 g := by
  simp only [restrictThirdZero_eq_rescale, map_mul]

/- English proof (translation)
Simplify using `only [restrictThirdZero_eq_rescale, map_add]`.
-/
theorem restrictThirdZero_add (f g : MvPowerSeries (Fin 3) K) : ev3 (f + g) = ev3 f + ev3 g := by
  simp only [restrictThirdZero_eq_rescale, map_add]

/- English proof (translation)
Simplify using `only [restrictThirdZero_eq_rescale, map_sub]`.
-/
theorem restrictThirdZero_sub (f g : MvPowerSeries (Fin 3) K) : ev3 (f - g) = ev3 f - ev3 g := by
  simp only [restrictThirdZero_eq_rescale, map_sub]

/- English proof (translation)
Simplify using `only [restrictThirdZero_eq_rescale, map_natCast]`.
-/
theorem restrictThirdZero_natCast (k : ℕ) : ev3 (k : MvPowerSeries (Fin 3) K) = k := by
  simp only [restrictThirdZero_eq_rescale, map_natCast]

/- English proof (translation)
Unfold `Formalism.L2.Th1.B.ev3`. Rewrite using `[subst_X hasSubst_restrictThirdZero]`. Simplify using the standard rewrite rules.
-/
theorem restrictThirdZero_X_two : ev3 (X 2 : MvPowerSeries (Fin 3) K) = 0 := by
  unfold Formalism.L2.Th1.B.ev3
  rw [subst_X hasSubst_restrictThirdZero]
  simp

/- English proof (translation)
Rewrite using `[X_dvd_iff]`. Introduce `m hm`. Rewrite using `[← coeff_restrictThirdZero h m hm, h0]`. Simplify using the standard rewrite rules.
-/
theorem X_two_dvd_of_restrictThirdZero {h : MvPowerSeries (Fin 3) K} (h0 : ev3 h = 0) : X 2 ∣ h := by
  rw [X_dvd_iff]
  intro m hm
  rw [← coeff_restrictThirdZero h m hm, h0]
  simp

/- English proof (translation)
Introduce `h`. Use `congrArg (coeff (Finsupp.single (2 : Fin 3) 1)) h` as an intermediate fact. Simplify using `[coeff_X] at this`.
-/
private theorem X_two_fin_three_ne_zero : (X 2 : MvPowerSeries (Fin 3) K) ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single (2 : Fin 3) 1)) h
  simp [coeff_X] at this

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem pderiv_X_fin_three_self (i : Fin 3) :
    MvPowerSeries.pderiv K i (X i : MvPowerSeries (Fin 3) K) = 1 := by
  simp

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ (X 2 : MvPowerSeries (Fin 3) K) (m + 1), Derivation.leibniz, ih, pderiv_X_fin_three_self]`. Simplify using `only [smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pderiv_two_X_two_pow_succ (m : ℕ) :
    MvPowerSeries.pderiv K 2 ((X 2 : MvPowerSeries (Fin 3) K) ^ (m + 1)) =
      ((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * X 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (X 2 : MvPowerSeries (Fin 3) K) (m + 1), Derivation.leibniz, ih, pderiv_X_fin_three_self]
    simp only [smul_eq_mul]
    push_cast
    ring

/- English proof (translation)
Unfold `Formalism.L2.Th1.B.pd`. Rewrite using `[Derivation.leibniz, pderiv_two_X_two_pow_succ]`. Simplify using `only [smul_eq_mul]`.
-/
private theorem pd_two_X_two_pow_succ_mul (m : ℕ) (R : MvPowerSeries (Fin 3) K) :
    Formalism.L2.Th1.B.pd 2 (X 2 ^ (m + 1) * R) =
      X 2 ^ (m + 1) * Formalism.L2.Th1.B.pd 2 R + R * (((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * X 2 ^ m) := by
  unfold Formalism.L2.Th1.B.pd
  rw [Derivation.leibniz, pderiv_two_X_two_pow_succ]
  simp only [smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ m : ℕ, ∃ R : MvPowerSeries (Fin 3) K, Q = X 2 ^ (m + 1) * R`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Take `⟨R, hR⟩` from `X_two_dvd_of_restrictThirdZero hQ`.

Conclude with `⟨R, by rw [hR]; ring⟩`. Consider the case `succ m ih`. Take `⟨R, rfl⟩` from `ih`. Rewrite `hw` using `[pd_two_X_two_pow_succ_mul]`. Establish `h1 : X 2 ^ m * (X 2 * R * Formalism.L2.Th1.B.pd 2 B) = X 2 ^ m * (B * (((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * R + X 2 * Formalism.L2.Th1.B.pd 2 R))`.

Take the linear combination `hw`. Establish `h2` using `mul_left_cancel₀ (pow_ne_zero m X_two_fin_three_ne_zero) h1`. Establish `h3` using `congrArg Formalism.L2.Th1.B.ev3 h2`. Simplify using `only [restrictThirdZero_mul, restrictThirdZero_add, restrictThirdZero_X_two, restrictThirdZero_natCast, zero_mul, add_zero] at h3`. Establish `hc : ((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) ≠ 0`.

Introduce `hc`. Use `congrArg (coeff (0 : Fin 3 →₀ ℕ)) hc` as an intermediate fact. Simplify using `at this`. Conclude with `Nat.cast_add_one_ne_zero m this`. Establish `hR : Formalism.L2.Th1.B.ev3 R = 0`.

Break down `mul_eq_zero.mp h3.symm with h | h` into its components or cases. Conclude with `absurd h hB`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `absurd h hc`. Conclude with `h`.

Take `⟨S, hS⟩` from `X_two_dvd_of_restrictThirdZero hR`. Conclude with `⟨S, by rw [hS]; ring⟩`. Use extensionality with `n`. Take `⟨R, hR⟩` from `key (n 2)`. It suffices to establish `hz : coeff n ((X 2 : MvPowerSeries (Fin 3) K) ^ (n 2 + 1) * R) = 0 by`.

Rewrite using `[hR, hz]`. Simplify using the standard rewrite rules. Rewrite using `[coeff_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce and unpack `⟨p, q⟩ hpq`.

Establish `hpq' : p + q = n` using `by simpa using hpq`. Rewrite using `[coeff_X_pow]`. Use `split_ifs with hp`. It suffices to derive a contradiction. Substitute `hp` using the available equality.

Use `DFunLike.congr_fun hpq' 2` as an intermediate fact. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same] at this`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem eq_zero_of_wronsk {Q B : MvPowerSeries (Fin 3) K} (hw : Q * pd 2 B = B * pd 2 Q)
    (hQ : ev3 Q = 0) (hB : ev3 B ≠ 0) : Q = 0 := by
  have key : ∀ m : ℕ, ∃ R : MvPowerSeries (Fin 3) K, Q = X 2 ^ (m + 1) * R := by
    intro m
    induction m with
    | zero =>
      obtain ⟨R, hR⟩ := X_two_dvd_of_restrictThirdZero hQ
      exact ⟨R, by rw [hR]; ring⟩
    | succ m ih =>
      obtain ⟨R, rfl⟩ := ih
      rw [pd_two_X_two_pow_succ_mul] at hw
      have h1 : X 2 ^ m * (X 2 * R * Formalism.L2.Th1.B.pd 2 B) =
          X 2 ^ m * (B * (((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * R + X 2 * Formalism.L2.Th1.B.pd 2 R)) := by
        linear_combination hw
      have h2 := mul_left_cancel₀ (pow_ne_zero m X_two_fin_three_ne_zero) h1
      have h3 := congrArg Formalism.L2.Th1.B.ev3 h2
      simp only [restrictThirdZero_mul, restrictThirdZero_add, restrictThirdZero_X_two,
        restrictThirdZero_natCast, zero_mul, add_zero] at h3
      have hc : ((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) ≠ 0 := by
        intro hc
        have := congrArg (coeff (0 : Fin 3 →₀ ℕ)) hc
        simp at this
        exact Nat.cast_add_one_ne_zero m this
      have hR : Formalism.L2.Th1.B.ev3 R = 0 := by
        rcases mul_eq_zero.mp h3.symm with h | h
        · exact absurd h hB
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h hc
          · exact h
      obtain ⟨S, hS⟩ := X_two_dvd_of_restrictThirdZero hR
      exact ⟨S, by rw [hS]; ring⟩
  ext n
  obtain ⟨R, hR⟩ := key (n 2)
  suffices hz : coeff n ((X 2 : MvPowerSeries (Fin 3) K) ^ (n 2 + 1) * R) = 0 by
    rw [hR, hz]; simp
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨p, q⟩ hpq
  have hpq' : p + q = n := by simpa using hpq
  rw [coeff_X_pow]
  split_ifs with hp
  · exfalso
    subst hp
    have := DFunLike.congr_fun hpq' 2
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  · simp

/- English proof (translation)
Introduce `L _ _ A Bs hw hr hB`. Establish `hQ : Formalism.L2.Th1.B.ev3 (A - Bs) = 0` using `by rw [restrictThirdZero_sub, hr, sub_self]`. Establish `hd : Formalism.L2.Th1.B.pd 2 (A - Bs) = Formalism.L2.Th1.B.pd 2 A - Formalism.L2.Th1.B.pd 2 Bs`. Simplify using `only [Formalism.L2.Th1.B.pd, map_sub]`. Establish `hw' : (A - Bs) * Formalism.L2.Th1.B.pd 2 Bs = Bs * Formalism.L2.Th1.B.pd 2 (A - Bs)`.

Rewrite using `[hd]`. Take the linear combination `hw`. Conclude with `sub_eq_zero.mp (eq_zero_of_wronsk hw' hQ hB)`.
-/
theorem wronskianUniqueness : WronskLemma := by
  intro L _ _ A Bs hw hr hB
  have hQ : Formalism.L2.Th1.B.ev3 (A - Bs) = 0 := by rw [restrictThirdZero_sub, hr, sub_self]
  have hd : Formalism.L2.Th1.B.pd 2 (A - Bs) = Formalism.L2.Th1.B.pd 2 A - Formalism.L2.Th1.B.pd 2 Bs := by
    simp only [Formalism.L2.Th1.B.pd, map_sub]
  have hw' : (A - Bs) * Formalism.L2.Th1.B.pd 2 Bs = Bs * Formalism.L2.Th1.B.pd 2 (A - Bs) := by
    rw [hd]
    linear_combination hw
  exact sub_eq_zero.mp (eq_zero_of_wronsk hw' hQ hB)

def sh (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  subst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] h

def shI (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  subst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] h

/- English proof (translation)
Apply the tactic sequence `fin_cases s <;> simp`.
-/
theorem cc_sh (s : Fin 3) :
    constantCoeff (![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] s) = 0 := by
  fin_cases s <;> simp

/- English proof (translation)
Apply the tactic sequence `fin_cases s <;> simp`.
-/
theorem cc_shI (s : Fin 3) :
    constantCoeff (![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] s) = 0 := by
  fin_cases s <;> simp

/- English proof (translation)
The claim follows from `hasSubst_fin_three_of_constantCoeff_eq_zero cc_sh`.
-/
theorem hasSubst_sh : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero cc_sh

/- English proof (translation)
The claim follows from `hasSubst_fin_three_of_constantCoeff_eq_zero cc_shI`.
-/
theorem hasSubst_shI : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero cc_shI

/- English proof (translation)
Conclude with `subst_mul ha f g`.
-/
private theorem subst_fin_three_mul {a : Fin 3 → MvPowerSeries (Fin 3) K} (ha : HasSubst a)
    (f g : MvPowerSeries (Fin 3) K) : subst a (f * g) = subst a f * subst a g := by
  exact subst_mul ha f g

/- English proof (translation)
Unfold `sh`. Conclude with `subst_fin_three_mul hasSubst_sh f g`.
-/
theorem sh_mul (f g : MvPowerSeries (Fin 3) K) : sh (f * g) = sh f * sh g := by
  unfold sh
  exact subst_fin_three_mul hasSubst_sh f g

/- English proof (translation)
Conclude with `subst_sub ha f g`.
-/
private theorem subst_fin_three_sub {a : Fin 3 → MvPowerSeries (Fin 3) K} (ha : HasSubst a)
    (f g : MvPowerSeries (Fin 3) K) : subst a (f - g) = subst a f - subst a g := by
  exact subst_sub ha f g

/- English proof (translation)
Unfold `sh`. Conclude with `subst_fin_three_sub hasSubst_sh f g`.
-/
theorem sh_sub (f g : MvPowerSeries (Fin 3) K) : sh (f - g) = sh f - sh g := by
  unfold sh
  exact subst_fin_three_sub hasSubst_sh f g

/- English proof (translation)
Rewrite using `[← map_algebraMap_eq_subst_X]`. Simplify using the standard rewrite rules.
-/
private theorem subst_X_fin_three_eq_self (h : MvPowerSeries (Fin 3) K) :
    subst (X : Fin 3 → MvPowerSeries (Fin 3) K) h = h := by
  rw [← map_algebraMap_eq_subst_X]
  simp

/- English proof (translation)
Unfold `shI sh`. Rewrite using `[subst_comp_subst_apply hasSubst_sh hasSubst_shI]`. Use `trans subst (X : Fin 3 → MvPowerSeries (Fin 3) K) h`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Apply the tactic sequence `fin_cases s <;> simp [subst_X hasSubst_shI, subst_fin_three_sub hasSubst_shI]`. Conclude with `subst_X_fin_three_eq_self h`.
-/
theorem shI_sh (h : MvPowerSeries (Fin 3) K) : shI (sh h) = h := by
  unfold shI sh
  rw [subst_comp_subst_apply hasSubst_sh hasSubst_shI]
  trans subst (X : Fin 3 → MvPowerSeries (Fin 3) K) h
  · congr 1
    funext s
    fin_cases s <;> simp [subst_X hasSubst_shI, subst_fin_three_sub hasSubst_shI]
  · exact subst_X_fin_three_eq_self h

/- English proof (translation)
Unfold `Formalism.L2.Th1.B.ev3 sh`. Rewrite using `[subst_comp_subst_apply hasSubst_sh hasSubst_restrictThirdZero]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `fin_cases s <;> simp [subst_X hasSubst_restrictThirdZero, subst_fin_three_sub hasSubst_restrictThirdZero]`.
-/
theorem restrictThirdZero_shear (h : MvPowerSeries (Fin 3) K) : ev3 (sh h) = ev3 h := by
  unfold Formalism.L2.Th1.B.ev3 sh
  rw [subst_comp_subst_apply hasSubst_sh hasSubst_restrictThirdZero]
  congr 1
  funext s
  fin_cases s <;> simp [subst_X hasSubst_restrictThirdZero, subst_fin_three_sub hasSubst_restrictThirdZero]

/- English proof (translation)
Simplify using `[hij]`.
-/
private theorem pderiv_X_fin_three_of_ne {i j : Fin 3} (hij : j ≠ i) :
    MvPowerSeries.pderiv K i (X j : MvPowerSeries (Fin 3) K) = 0 := by
  simp [hij]

/- English proof (translation)
Unfold `sh Formalism.L2.Th1.B.pd`. Rewrite using `[Formalism.G.LogCR.pderiv_subst cc_sh, Fin.sum_univ_three]`. Simplify using `[pderiv_X_fin_three_self, pderiv_X_fin_three_of_ne]`. Apply the tactic sequence `try ring`.
-/
theorem partialDeriv_two_shear (h : MvPowerSeries (Fin 3) K) : pd 2 (sh h) = sh (pd 2 h) - sh (pd 1 h) := by
  unfold sh Formalism.L2.Th1.B.pd
  rw [Formalism.G.LogCR.pderiv_subst cc_sh, Fin.sum_univ_three]
  simp [pderiv_X_fin_three_self, pderiv_X_fin_three_of_ne]
  try ring

/- English proof (translation)
Introduce `L _ _ A Bs hw hr hB`. Establish `h1 : sh A * Formalism.L2.Th1.B.pd 2 (sh Bs) = sh Bs * Formalism.L2.Th1.B.pd 2 (sh A)`. Rewrite using `[partialDeriv_two_shear, partialDeriv_two_shear]`. Establish `e` using `congrArg sh hw`. Rewrite `e` using `[sh_mul, sh_mul, sh_sub, sh_sub]`.

Take the linear combination `-e`. Establish `h2 : Formalism.L2.Th1.B.ev3 (sh A) = Formalism.L2.Th1.B.ev3 (sh Bs)`. Rewrite using `[restrictThirdZero_shear, restrictThirdZero_shear, hr]`. Establish `h3 : Formalism.L2.Th1.B.ev3 (sh Bs) ≠ 0`. Rewrite using `[restrictThirdZero_shear]` and apply the resulting hypothesis.

Establish `h4` using `wronskianUniqueness L (sh A) (sh Bs) h1 h2 h3`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem shearedWronskianUniqueness : ShearLemma := by
  intro L _ _ A Bs hw hr hB
  have h1 : sh A * Formalism.L2.Th1.B.pd 2 (sh Bs) = sh Bs * Formalism.L2.Th1.B.pd 2 (sh A) := by
    rw [partialDeriv_two_shear, partialDeriv_two_shear]
    have e := congrArg sh hw
    rw [sh_mul, sh_mul, sh_sub, sh_sub] at e
    linear_combination -e
  have h2 : Formalism.L2.Th1.B.ev3 (sh A) = Formalism.L2.Th1.B.ev3 (sh Bs) := by
    rw [restrictThirdZero_shear, restrictThirdZero_shear, hr]
  have h3 : Formalism.L2.Th1.B.ev3 (sh Bs) ≠ 0 := by
    rwa [restrictThirdZero_shear]
  have h4 := wronskianUniqueness L (sh A) (sh Bs) h1 h2 h3
  calc A = shI (sh A) := (shI_sh A).symm
    _ = shI (sh Bs) := by rw [h4]
    _ = Bs := shI_sh Bs

end Formalism.L2.Th1.B.Wr
