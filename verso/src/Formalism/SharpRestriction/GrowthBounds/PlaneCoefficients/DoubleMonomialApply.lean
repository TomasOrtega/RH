import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks.Tr

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Gen

variable {σ R : Type*} [CommSemiring R]

/- English proof (translation)
Rewrite using `[show (X i : MvPolynomial σ R) = monomial (Finsupp.single i 1) 1 from rfl, monomial_mul, one_mul, add_comm]`.
-/
theorem X_mul_mon (i : σ) (s : σ →₀ ℕ) (q : R) : X i * monomial s q = monomial (s + Finsupp.single i 1) q := by
  rw [show (X i : MvPolynomial σ R) = monomial (Finsupp.single i 1) 1 from rfl, monomial_mul, one_mul, add_comm]

/- English proof (translation)
Rewrite using `[pderiv_monomial, add_tsub_cancel_right, nsmul_eq_mul, mul_comm, Finsupp.add_apply, Finsupp.single_eq_same]`.
-/
theorem pderiv_mon_succ (i : σ) (s : σ →₀ ℕ) (q : R) :
    pderiv i (monomial (s + Finsupp.single i 1) q) = monomial s ((s i + 1) • q) := by
  rw [pderiv_monomial, add_tsub_cancel_right, nsmul_eq_mul, mul_comm, Finsupp.add_apply, Finsupp.single_eq_same]

/- English proof (translation)
Rewrite using `[pderiv_monomial, h, Nat.cast_zero, mul_zero, map_zero]`.
-/
theorem pderiv_mon_zero (i : σ) (s : σ →₀ ℕ) (q : R) (h : s i = 0) : pderiv i (monomial s q) = 0 := by
  rw [pderiv_monomial, h, Nat.cast_zero, mul_zero, map_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨s - Finsupp.single i 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h))).symm⟩`.
-/
theorem exists_add_single (i : σ) (s : σ →₀ ℕ) (h : s i ≠ 0) : ∃ s', s = s' + Finsupp.single i 1 :=
  ⟨s - Finsupp.single i 1,
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h))).symm⟩

/- English proof (translation)
Distinguish the cases in `h : s i = 0`. Rewrite using `[pderiv_mon_zero i s q h, mul_zero, h, zero_smul, map_zero]`. Take `⟨s', rfl⟩` from `exists_add_single i s h`. Rewrite using `[pderiv_mon_succ, X_mul_mon, Finsupp.add_apply, Finsupp.single_eq_same]`.
-/
theorem euler_mon (i : σ) (s : σ →₀ ℕ) (q : R) : X i * pderiv i (monomial s q) = monomial s (s i • q) := by
  by_cases h : s i = 0
  · rw [pderiv_mon_zero i s q h, mul_zero, h, zero_smul, map_zero]
  · obtain ⟨s', rfl⟩ := exists_add_single i s h
    rw [pderiv_mon_succ, X_mul_mon, Finsupp.add_apply, Finsupp.single_eq_same]

end Gen

/- English proof (translation)
Unfold `oneT`. Distinguish the cases in `h : q = 0`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[support_monomial, if_neg h, Finset.sum_singleton, coeff_monomial, if_pos rfl]`.
-/
theorem oneT_monomial {σ τ Kf : Type} [Field Kf] (e : Module.End Kf (MvPolynomial τ Kf)) (s : σ →₀ ℕ)
    (q : MvPolynomial τ Kf) : oneT e (monomial s q) = monomial s (e q) := by
  unfold oneT
  by_cases h : q = 0
  · subst h; simp
  · rw [support_monomial, if_neg h, Finset.sum_singleton, coeff_monomial, if_pos rfl]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `he`. Establish `h1` using `Nat.div_add_mod e P`. Establish `h2 : e + 1 = P * (e / P) + (t + 1)` using `by omega`. Rewrite using `[h2, Nat.mul_add_mod, Nat.mod_eq_of_lt h]`.

Introduce `he`. Establish `h1` using `Nat.div_add_mod (e + 1) P`. Establish `h2 : e = P * ((e + 1) / P) + t` using `by omega`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nat_A {P e t : ℕ} (h : t + 1 < P) : e % P = t ↔ (e + 1) % P = t + 1 := by
  constructor
  · intro he
    have h1 := Nat.div_add_mod e P
    have h2 : e + 1 = P * (e / P) + (t + 1) := by omega
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  · intro he
    have h1 := Nat.div_add_mod (e + 1) P
    have h2 : e = P * ((e + 1) / P) + t := by omega
    calc e % P = (P * ((e + 1) / P) + t) % P := by rw [← h2]
      _ = t := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/- English proof (translation)
Establish `h1` using `Nat.div_add_mod e P`. Establish `h2 : e + 1 = P * (e / P) + (t + 1)` using `by omega`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nat_A_div {P e t : ℕ} (h : t + 1 < P) (he : e % P = t) : (e + 1) / P = e / P := by
  have h1 := Nat.div_add_mod e P
  have h2 : e + 1 = P * (e / P) + (t + 1) := by omega
  calc (e + 1) / P = (P * (e / P) + (t + 1)) / P := by rw [← h2]
    _ = e / P := by rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt h, add_zero]

/- English proof (translation)
Establish `h1` using `Nat.div_add_mod e P`. Rewrite using `[mul_add, mul_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nat_B_eq {P e t : ℕ} (h : t + 1 = P) (he : e % P = t) : e + 1 = P * (e / P + 1) := by
  have h1 := Nat.div_add_mod e P
  rw [mul_add, mul_one]
  omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `he`. Rewrite using `[nat_B_eq h he, Nat.mul_mod_right]`. Introduce `he`. Take `⟨k, hk⟩` from `Nat.dvd_of_mod_eq_zero he`.

Consider the cases of `k with`. Consider the case `zero => simp at hk`. Consider the case `succ k`. Rewrite `hk` using `[mul_add, mul_one]`. Establish `h2 : e = P * k + t` using `by omega`.

Rewrite using `[h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]`.
-/
theorem nat_B {P e t : ℕ} (h : t + 1 = P) : e % P = t ↔ (e + 1) % P = 0 := by
  constructor
  · intro he
    rw [nat_B_eq h he, Nat.mul_mod_right]
  · intro he
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero he
    cases k with
    | zero => simp at hk
    | succ k =>
      rw [mul_add, mul_one] at hk
      have h2 : e = P * k + t := by omega
      rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/- English proof (translation)
Rewrite using `[nat_B_eq h he, Nat.mul_div_cancel_left _ (by omega)]`.
-/
theorem nat_B_div {P e t : ℕ} (h : t + 1 = P) (he : e % P = t) : (e + 1) / P = e / P + 1 := by
  rw [nat_B_eq h he, Nat.mul_div_cancel_left _ (by omega)]

section Core

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def aVar (x : TL J nL r) (c : Fin (r + K)) : TV n' (m + 1) := (posOf n' (posTL Fr x), Fin.cast hk.symm c)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem plVar_eq (x : TL J nL r) (a : Fin r) : plVar Fr hk nL x a = aVar Fr hk nL x (Fin.castAdd K a) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem noVar_eq (x : TL J nL r) (b : Fin K) : noVar Fr hk nL x b = aVar Fr hk nL x (Fin.natAdd r b) := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x c`. Conclude with `Fin.addCases (motive := fun c => mo (aVar Fr hk nL x c) % lowP Fr p x = rho (x, c)) (fun a => h.1 x a) (fun b => h.2 x b) c`. Introduce `h`. Conclude with `⟨fun x a => h x _, fun x b => h x _⟩`.
-/
theorem inLow_iff (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ) :
    InLow Fr p hk nL rho mo ↔ ∀ x c, mo (aVar Fr hk nL x c) % lowP Fr p x = rho (x, c) := by
  constructor
  · intro h x c
    exact Fin.addCases (motive := fun c => mo (aVar Fr hk nL x c) % lowP Fr p x = rho (x, c))
      (fun a => h.1 x a) (fun b => h.2 x b) c
  · intro h
    exact ⟨fun x a => h x _, fun x b => h x _⟩

/- English proof (translation)
Simplify using `only [plMon, Finsupp.coe_equivFunOnFinite_symm]`. Both sides reduce to the same expression.
-/
theorem plMon_apply (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (a : Fin r) :
    plMon Fr p hk nL mo (x, a) = mo (aVar Fr hk nL x (Fin.castAdd K a)) / lowP Fr p x := by
  simp only [plMon, Finsupp.coe_equivFunOnFinite_symm]
  rfl

/- English proof (translation)
Simplify using `only [noMon, Finsupp.coe_equivFunOnFinite_symm]`. Both sides reduce to the same expression.
-/
theorem noMon_apply (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (b : Fin K) :
    noMon Fr p hk nL mo (x, b) = mo (aVar Fr hk nL x (Fin.natAdd r b)) / lowP Fr p x := by
  simp only [noMon, Finsupp.coe_equivFunOnFinite_symm]
  rfl

/- English proof (translation)
Simplify using `only [plMon_apply, noMon_apply]`. Both sides reduce to the same expression.
-/
theorem inBlock_iff (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ) :
    InBlock Fr p hk nL dPl dNo mo ↔
      (∀ x, ∑ a : Fin r, plMon Fr p hk nL mo (x, a) = dPl x) ∧ ∀ x, ∑ b : Fin K, noMon Fr p hk nL mo (x, b) = dNo x := by
  simp only [plMon_apply, noMon_apply]
  rfl

variable {x0 : TL J nL r} (hx0 : ∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0)
  (c0 : Fin (r + K))

include hx0 in
/- English proof (translation)
Establish `h1` using `congrArg Prod.fst h`. Establish `h2` using `congrArg Prod.snd h`. Simplify using `only [aVar] at h1 h2`. Rewrite using `[hx0 x h1, Fin.cast_injective _ h2]`.
-/
theorem aVar_inj {x : TL J nL r} {c c0 : Fin (r + K)} (h : aVar Fr hk nL x c = aVar Fr hk nL x0 c0) :
    (x, c) = (x0, c0) := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [aVar] at h1 h2
  rw [hx0 x h1, Fin.cast_injective _ h2]

include hx0 in
/- English proof (translation)
Rewrite using `[Finsupp.add_apply, Finsupp.single_apply]`. Use `congr 1`. Distinguish the cases in `h : (x, c) = (x0, c0)`. Take `⟨h1, h2⟩` from `Prod.mk.inj h`. Rewrite using `[if_pos h, if_pos (by rw [h1, h2])]`.

Rewrite using `[if_neg h, if_neg]`. Introduce `h'`. Conclude with `h (aVar_inj Fr hk nL hx0 h'.symm)`.
-/
theorem step_apply (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (c : Fin (r + K)) :
    (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1 : TV n' (m + 1) →₀ ℕ) (aVar Fr hk nL x c) =
      mo (aVar Fr hk nL x c) + if (x, c) = (x0, c0) then 1 else 0 := by
  rw [Finsupp.add_apply, Finsupp.single_apply]
  congr 1
  by_cases h : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [if_pos h, if_pos (by rw [h1, h2])]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (aVar_inj Fr hk nL hx0 h'.symm)

include hx0 in
/- English proof (translation)
Rewrite using `[inLow_iff, inLow_iff]`. Use `forall_congr' fun x => forall_congr' fun c => ?_` and prove the remaining obligations. Rewrite using `[step_apply Fr hk nL hx0]`. Distinguish the cases in `hv : (x, c) = (x0, c0)`. Take `⟨h1, h2⟩` from `Prod.mk.inj hv`.

Rewrite using `[h1, h2, if_pos rfl, Function.update_self]`. Conclude with `nat_A h`. Rewrite using `[if_neg hv, Function.update_of_ne hv, add_zero]`.
-/
theorem inLow_A (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) :
    InLow Fr p hk nL rho mo ↔ InLow Fr p hk nL (Function.update rho (x0, c0) (rho (x0, c0) + 1))
      (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) := by
  rw [inLow_iff, inLow_iff]
  refine forall_congr' fun x => forall_congr' fun c => ?_
  rw [step_apply Fr hk nL hx0]
  by_cases hv : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [h1, h2, if_pos rfl, Function.update_self]
    exact nat_A h
  · rw [if_neg hv, Function.update_of_ne hv, add_zero]

include hx0 in
/- English proof (translation)
Rewrite using `[inLow_iff, inLow_iff]`. Use `forall_congr' fun x => forall_congr' fun c => ?_` and prove the remaining obligations. Rewrite using `[step_apply Fr hk nL hx0]`. Distinguish the cases in `hv : (x, c) = (x0, c0)`. Take `⟨h1, h2⟩` from `Prod.mk.inj hv`.

Rewrite using `[h1, h2, if_pos rfl, Function.update_self]`. Conclude with `nat_B h`. Rewrite using `[if_neg hv, Function.update_of_ne hv, add_zero]`.
-/
theorem inLow_B (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 = lowP Fr p x0) :
    InLow Fr p hk nL rho mo ↔ InLow Fr p hk nL (Function.update rho (x0, c0) 0)
      (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) := by
  rw [inLow_iff, inLow_iff]
  refine forall_congr' fun x => forall_congr' fun c => ?_
  rw [step_apply Fr hk nL hx0]
  by_cases hv : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [h1, h2, if_pos rfl, Function.update_self]
    exact nat_B h
  · rw [if_neg hv, Function.update_of_ne hv, add_zero]

include hx0 in
/- English proof (translation)
Rewrite using `[step_apply Fr hk nL hx0]`. Distinguish the cases in `hv : (x, c) = (x0, c0)`. Take `⟨h1, h2⟩` from `Prod.mk.inj hv`. Rewrite using `[h1, h2, if_pos rfl]`. Conclude with `nat_A_div h ((inLow_iff Fr p hk nL rho mo).1 hL x0 c0)`.

Rewrite using `[if_neg hv, add_zero]`.
-/
theorem div_A (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) (x : TL J nL r) (c : Fin (r + K)) :
    (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1 : TV n' (m + 1) →₀ ℕ) (aVar Fr hk nL x c) / lowP Fr p x =
      mo (aVar Fr hk nL x c) / lowP Fr p x := by
  rw [step_apply Fr hk nL hx0]
  by_cases hv : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [h1, h2, if_pos rfl]
    exact nat_A_div h ((inLow_iff Fr p hk nL rho mo).1 hL x0 c0)
  · rw [if_neg hv, add_zero]

include hx0 in
/- English proof (translation)
Rewrite using `[step_apply Fr hk nL hx0]`. Distinguish the cases in `hv : (x, c) = (x0, c0)`. Take `⟨h1, h2⟩` from `Prod.mk.inj hv`. Rewrite using `[h1, h2, if_pos rfl]`. Conclude with `nat_B_div h ((inLow_iff Fr p hk nL rho mo).1 hL x0 c0)`.

Rewrite using `[if_neg hv, add_zero, add_zero]`.
-/
theorem div_B (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) (x : TL J nL r) (c : Fin (r + K)) :
    (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1 : TV n' (m + 1) →₀ ℕ) (aVar Fr hk nL x c) / lowP Fr p x =
      mo (aVar Fr hk nL x c) / lowP Fr p x + if (x, c) = (x0, c0) then 1 else 0 := by
  rw [step_apply Fr hk nL hx0]
  by_cases hv : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [h1, h2, if_pos rfl]
    exact nat_B_div h ((inLow_iff Fr p hk nL rho mo).1 hL x0 c0)
  · rw [if_neg hv, add_zero, add_zero]

include hx0 in
/- English proof (translation)
Use extensionality with `⟨x, a⟩`. Rewrite using `[plMon_apply, plMon_apply, div_A Fr p hk nL hx0 c0 rho mo h hL]`.
-/
theorem plMon_A (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    plMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) = plMon Fr p hk nL mo := by
  ext ⟨x, a⟩
  rw [plMon_apply, plMon_apply, div_A Fr p hk nL hx0 c0 rho mo h hL]

include hx0 in
/- English proof (translation)
Use extensionality with `⟨x, b⟩`. Rewrite using `[noMon_apply, noMon_apply, div_A Fr p hk nL hx0 c0 rho mo h hL]`.
-/
theorem noMon_A (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    noMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) = noMon Fr p hk nL mo := by
  ext ⟨x, b⟩
  rw [noMon_apply, noMon_apply, div_A Fr p hk nL hx0 c0 rho mo h hL]

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Fin.val h`. Simplify using `only [Fin.val_natAdd, Fin.val_castAdd] at h1`. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem cast_ne_nat (a : Fin r) (b : Fin K) : Fin.natAdd r b ≠ Fin.castAdd K a := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
  have := a.isLt
  omega

include hx0 in
/- English proof (translation)
Use extensionality with `⟨x, a'⟩`. Rewrite using `[plMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, Finsupp.add_apply, plMon_apply, Finsupp.single_apply]`. Use `congr 1`. Distinguish the cases in `hv : (x0, a) = (x, a')`. Take `⟨h1, h2⟩` from `Prod.mk.inj hv`.

Rewrite using `[if_pos hv, if_pos (by rw [h1, h2])]`. Rewrite using `[if_neg hv, if_neg]`. Introduce `h'`. Take `⟨h1, h2⟩` from `Prod.mk.inj h'`. Conclude with `hv (by rw [h1, Fin.castAdd_injective r K h2])`.
-/
theorem plMon_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    plMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.castAdd K a)) 1) =
      plMon Fr p hk nL mo + Finsupp.single (x0, a) 1 := by
  ext ⟨x, a'⟩
  rw [plMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, Finsupp.add_apply, plMon_apply, Finsupp.single_apply]
  congr 1
  by_cases hv : (x0, a) = (x, a')
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [if_pos hv, if_pos (by rw [h1, h2])]
  · rw [if_neg hv, if_neg]
    intro h'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact hv (by rw [h1, Fin.castAdd_injective r K h2])

include hx0 in
/- English proof (translation)
Use extensionality with `⟨x, b⟩`. Rewrite using `[noMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, noMon_apply, if_neg, add_zero]`. Introduce `h'`. Conclude with `cast_ne_nat a b (Prod.mk.inj h').2`.
-/
theorem noMon_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    noMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.castAdd K a)) 1) = noMon Fr p hk nL mo := by
  ext ⟨x, b⟩
  rw [noMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, noMon_apply, if_neg, add_zero]
  intro h'
  exact cast_ne_nat a b (Prod.mk.inj h').2

include hx0 in
/- English proof (translation)
Use extensionality with `⟨x, b'⟩`. Rewrite using `[noMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, Finsupp.add_apply, noMon_apply, Finsupp.single_apply]`. Use `congr 1`. Distinguish the cases in `hv : (x0, b) = (x, b')`. Take `⟨h1, h2⟩` from `Prod.mk.inj hv`.

Rewrite using `[if_pos hv, if_pos (by rw [h1, h2])]`. Rewrite using `[if_neg hv, if_neg]`. Introduce `h'`. Take `⟨h1, h2⟩` from `Prod.mk.inj h'`. Conclude with `hv (by rw [h1, Fin.natAdd_injective K r h2])`.
-/
theorem noMon_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    noMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.natAdd r b)) 1) =
      noMon Fr p hk nL mo + Finsupp.single (x0, b) 1 := by
  ext ⟨x, b'⟩
  rw [noMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, Finsupp.add_apply, noMon_apply, Finsupp.single_apply]
  congr 1
  by_cases hv : (x0, b) = (x, b')
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [if_pos hv, if_pos (by rw [h1, h2])]
  · rw [if_neg hv, if_neg]
    intro h'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact hv (by rw [h1, Fin.natAdd_injective K r h2])

include hx0 in
/- English proof (translation)
Use extensionality with `⟨x, a⟩`. Rewrite using `[plMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, plMon_apply, if_neg, add_zero]`. Introduce `h'`. Conclude with `cast_ne_nat a b (Prod.mk.inj h').2.symm`.
-/
theorem plMon_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    plMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.natAdd r b)) 1) = plMon Fr p hk nL mo := by
  ext ⟨x, a⟩
  rw [plMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, plMon_apply, if_neg, add_zero]
  intro h'
  exact cast_ne_nat a b (Prod.mk.inj h').2.symm

/- English proof (translation)
Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib]`. Use `congr 1`. Distinguish the cases in `h : x = x0`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_eq_single a]`.

Rewrite using `[Finsupp.single_eq_same]`. Introduce `b _ hb`. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h'`. Conclude with `hb (Prod.mk.inj h').2.symm`.

Introduce `h'`. Conclude with `absurd (Finset.mem_univ a) h'`. Rewrite using `[if_neg h]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h'`. Conclude with `h (Prod.mk.inj h').1.symm`.
-/
theorem sum_add_single {ι : Type} [DecidableEq ι] {n : ℕ} (f : ι × Fin n →₀ ℕ) (x0 x : ι) (a : Fin n) :
    ∑ a' : Fin n, (f + Finsupp.single (x0, a) 1 : ι × Fin n →₀ ℕ) (x, a') = ∑ a' : Fin n, f (x, a') + if x = x0 then 1 else 0 := by
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  by_cases h : x = x0
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · rw [Finsupp.single_eq_same]
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro h'
      exact hb (Prod.mk.inj h').2.symm
    · intro h'
      exact absurd (Finset.mem_univ a) h'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b _
    rw [Finsupp.single_apply, if_neg]
    intro h'
    exact h (Prod.mk.inj h').1.symm

/- English proof (translation)
Use `forall_congr' fun x => ?_` and prove the remaining obligations. Distinguish the cases in `h : x = x0`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, Function.update_self]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg h, Function.update_of_ne h, add_zero]`.
-/
theorem deg_upd {ι : Type} [DecidableEq ι] (S d : ι → ℕ) (x0 : ι) :
    (∀ x, S x = d x) ↔ ∀ x, (S x + if x = x0 then 1 else 0) = Function.update d x0 (d x0 + 1) x := by
  refine forall_congr' fun x => ?_
  by_cases h : x = x0
  · subst h
    rw [if_pos rfl, Function.update_self]
    omega
  · rw [if_neg h, Function.update_of_ne h, add_zero]

end Core

section Lev

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

/- English proof (translation)
Unfold `levImg`. Distinguish the cases in `h : c = 0`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[support_monomial, if_neg h, Finset.filter_singleton]`.

Distinguish the cases in `h1 : InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo`. Rewrite using `[if_pos h1, if_pos h1, Finset.sum_singleton, coeff_monomial, if_pos rfl]`. Both sides reduce to the same expression. Rewrite using `[if_neg h1, if_neg h1, Finset.sum_empty]`.
-/
theorem levImg_monomial (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (c : KK O) :
    levImg Fr p hk nL rho dPl dNo (monomial mo c) =
      if InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo then
        mono2 (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) c else 0 := by
  unfold levImg
  by_cases h : c = 0
  · subst h
    simp
  · rw [support_monomial, if_neg h, Finset.filter_singleton]
    by_cases h1 : InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo
    · rw [if_pos h1, if_pos h1, Finset.sum_singleton, coeff_monomial, if_pos rfl]
      rfl
    · rw [if_neg h1, if_neg h1, Finset.sum_empty]

/- English proof (translation)
Unfold `levImg`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `mo hmo`. It suffices to derive a contradiction. Establish `h1` using `(inLow_iff Fr p hk nL rho mo).1 (Finset.mem_filter.1 hmo).2.1 x0 c0`.

Establish `h2` using `Nat.mod_lt (mo (aVar Fr hk nL x0 c0)) (pow_pos hp (Fr.dist (segZ x0.1) (posTL Fr x0)))`. Unfold `lowP at h h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem levImg_empty (hp : 0 < p) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (x0 : TL J nL r)
    (c0 : Fin (r + K)) (h : lowP Fr p x0 ≤ rho (x0, c0)) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo F = 0 := by
  unfold levImg
  apply Finset.sum_eq_zero
  intro mo hmo
  exfalso
  have h1 := (inLow_iff Fr p hk nL rho mo).1 (Finset.mem_filter.1 hmo).2.1 x0 c0
  have h2 := Nat.mod_lt (mo (aVar Fr hk nL x0 c0)) (pow_pos hp (Fr.dist (segZ x0.1) (posTL Fr x0)))
  unfold lowP at h h1
  omega

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem double_monomial_apply {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) :
    mono2 a b c = monomial a (monomial b c) := rfl

/- English proof (translation)
Rewrite using `[double_monomial_apply, euler_mon, smul_monomial, nsmul_eq_mul, double_monomial_apply]`.
-/
theorem pl_euler {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : σ) :
    X i * pderiv i (mono2 a b c) = mono2 a b ((a i : Kf) * c) := by
  rw [double_monomial_apply, euler_mon, smul_monomial, nsmul_eq_mul, double_monomial_apply]

/- English proof (translation)
Rewrite using `[double_monomial_apply, pderiv_mon_succ, smul_monomial, nsmul_eq_mul, double_monomial_apply]`.
-/
theorem pl_der {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : σ) :
    pderiv i (mono2 (a + Finsupp.single i 1) b c) = mono2 a b (((a i + 1 : ℕ) : Kf) * c) := by
  rw [double_monomial_apply, pderiv_mon_succ, smul_monomial, nsmul_eq_mul, double_monomial_apply]

/- English proof (translation)
Rewrite using `[double_monomial_apply, pderiv_mon_zero _ _ _ h]`.
-/
theorem pl_der_zero {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : σ) (h : a i = 0) :
    pderiv i (mono2 a b c) = 0 := by
  rw [double_monomial_apply, pderiv_mon_zero _ _ _ h]

/- English proof (translation)
Rewrite using `[double_monomial_apply, X_mul_mon, double_monomial_apply]`.
-/
theorem pl_mul {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : σ) :
    X i * mono2 a b c = mono2 (a + Finsupp.single i 1) b c := by
  rw [double_monomial_apply, X_mul_mon, double_monomial_apply]

/- English proof (translation)
Rewrite using `[double_monomial_apply, oneT_monomial, double_monomial_apply]`. Use `congr 1`. Use `show X i * pderiv i (monomial b c) = _`. Rewrite using `[euler_mon, nsmul_eq_mul]`.
-/
theorem no_euler {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : τ) :
    oneT (mulN i * derN i) (mono2 a b c) = mono2 a b ((b i : Kf) * c) := by
  rw [double_monomial_apply, oneT_monomial, double_monomial_apply]
  congr 1
  show X i * pderiv i (monomial b c) = _
  rw [euler_mon, nsmul_eq_mul]

/- English proof (translation)
Rewrite using `[double_monomial_apply, oneT_monomial, double_monomial_apply]`. Use `congr 1`. Use `show pderiv i (monomial (b + Finsupp.single i 1) c) = _`. Rewrite using `[pderiv_mon_succ, nsmul_eq_mul]`.
-/
theorem no_der {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : τ) :
    oneT (derN i) (mono2 a (b + Finsupp.single i 1) c) = mono2 a b (((b i + 1 : ℕ) : Kf) * c) := by
  rw [double_monomial_apply, oneT_monomial, double_monomial_apply]
  congr 1
  show pderiv i (monomial (b + Finsupp.single i 1) c) = _
  rw [pderiv_mon_succ, nsmul_eq_mul]

/- English proof (translation)
Rewrite using `[double_monomial_apply, oneT_monomial]`. Establish `: derN i (monomial b c) = 0` using `pderiv_mon_zero i b c h`. Rewrite using `[this, map_zero]`.
-/
theorem no_der_zero {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : τ) (h : b i = 0) :
    oneT (derN i) (mono2 a b c) = 0 := by
  rw [double_monomial_apply, oneT_monomial]
  have : derN i (monomial b c) = 0 := pderiv_mon_zero i b c h
  rw [this, map_zero]

/- English proof (translation)
Rewrite using `[double_monomial_apply, oneT_monomial, double_monomial_apply]`. Use `congr 1`. Use `show X i * monomial b c = _`. Rewrite using `[X_mul_mon]`.
-/
theorem no_mul {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : τ) :
    oneT (mulN i) (mono2 a b c) = mono2 a (b + Finsupp.single i 1) c := by
  rw [double_monomial_apply, oneT_monomial, double_monomial_apply]
  congr 1
  show X i * monomial b c = _
  rw [X_mul_mon]

end Lev

section Main

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
  {x0 : TL J nL r} (hx0 : ∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0)

include hx0 in
/- English proof (translation)
Rewrite using `[levImg_monomial, levImg_monomial]`. Establish `hiff` using `inLow_A Fr p hk nL hx0 c0 rho mo h`. Distinguish the cases in `hL : InLow Fr p hk nL rho mo`. Establish `hpl` using `plMon_A Fr p hk nL hx0 c0 rho mo h hL`. Establish `hno` using `noMon_A Fr p hk nL hx0 c0 rho mo h hL`.

Establish `hB : InBlock Fr p hk nL dPl dNo (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) ↔ InBlock Fr p hk nL dPl dNo mo`. Rewrite using `[inBlock_iff, inBlock_iff, hpl, hno]`. Distinguish the cases in `hBl : InBlock Fr p hk nL dPl dNo mo`. Rewrite using `[if_pos ⟨hiff.1 hL, hB.2 hBl⟩, if_pos ⟨hL, hBl⟩, hpl, hno]`. Rewrite using `[if_neg (fun hh => hBl (hB.1 hh.2)), if_neg (fun hh => hBl hh.2)]`.

Rewrite using `[if_neg (fun hh => hL (hiff.2 hh.1)), if_neg (fun hh => hL hh.1)]`.
-/
theorem lev_A (c0 : Fin (r + K)) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levImg Fr p hk nL (Function.update rho (x0, c0) (rho (x0, c0) + 1)) dPl dNo
        (monomial (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) c) =
      levImg Fr p hk nL rho dPl dNo (monomial mo c) := by
  rw [levImg_monomial, levImg_monomial]
  have hiff := inLow_A Fr p hk nL hx0 c0 rho mo h
  by_cases hL : InLow Fr p hk nL rho mo
  · have hpl := plMon_A Fr p hk nL hx0 c0 rho mo h hL
    have hno := noMon_A Fr p hk nL hx0 c0 rho mo h hL
    have hB : InBlock Fr p hk nL dPl dNo (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) ↔
        InBlock Fr p hk nL dPl dNo mo := by
      rw [inBlock_iff, inBlock_iff, hpl, hno]
    by_cases hBl : InBlock Fr p hk nL dPl dNo mo
    · rw [if_pos ⟨hiff.1 hL, hB.2 hBl⟩, if_pos ⟨hL, hBl⟩, hpl, hno]
    · rw [if_neg (fun hh => hBl (hB.1 hh.2)), if_neg (fun hh => hBl hh.2)]
  · rw [if_neg (fun hh => hL (hiff.2 hh.1)), if_neg (fun hh => hL hh.1)]

include hx0 in
/- English proof (translation)
Rewrite using `[inBlock_iff, inBlock_iff, plMon_Bpl Fr p hk nL hx0 a rho mo h hL, noMon_Bpl Fr p hk nL hx0 a rho mo h hL]`. Simplify using `only [sum_add_single]`. Conclude with `and_congr (deg_upd (fun x => ∑ a' : Fin r, plMon Fr p hk nL mo (x, a')) dPl x0).symm Iff.rfl`.
-/
theorem block_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (hL : InLow Fr p hk nL rho mo) :
    InBlock Fr p hk nL (Function.update dPl x0 (dPl x0 + 1)) dNo
        (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.castAdd K a)) 1) ↔ InBlock Fr p hk nL dPl dNo mo := by
  rw [inBlock_iff, inBlock_iff, plMon_Bpl Fr p hk nL hx0 a rho mo h hL, noMon_Bpl Fr p hk nL hx0 a rho mo h hL]
  simp only [sum_add_single]
  exact and_congr (deg_upd (fun x => ∑ a' : Fin r, plMon Fr p hk nL mo (x, a')) dPl x0).symm Iff.rfl

include hx0 in
/- English proof (translation)
Rewrite using `[inBlock_iff, inBlock_iff, plMon_Bno Fr p hk nL hx0 b rho mo h hL, noMon_Bno Fr p hk nL hx0 b rho mo h hL]`. Simplify using `only [sum_add_single]`. Conclude with `and_congr Iff.rfl (deg_upd (fun x => ∑ b' : Fin K, noMon Fr p hk nL mo (x, b')) dNo x0).symm`.
-/
theorem block_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (hL : InLow Fr p hk nL rho mo) :
    InBlock Fr p hk nL dPl (Function.update dNo x0 (dNo x0 + 1))
        (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.natAdd r b)) 1) ↔ InBlock Fr p hk nL dPl dNo mo := by
  rw [inBlock_iff, inBlock_iff, plMon_Bno Fr p hk nL hx0 b rho mo h hL, noMon_Bno Fr p hk nL hx0 b rho mo h hL]
  simp only [sum_add_single]
  exact and_congr Iff.rfl (deg_upd (fun x => ∑ b' : Fin K, noMon Fr p hk nL mo (x, b')) dNo x0).symm

include hx0 in
/- English proof (translation)
Rewrite using `[levImg_monomial, levImg_monomial]`. Establish `hiff` using `inLow_B Fr p hk nL hx0 (Fin.castAdd K a) rho mo h`. Distinguish the cases in `hL : InLow Fr p hk nL rho mo`. Establish `hB` using `block_Bpl Fr p hk nL hx0 a rho dPl dNo h mo hL`. Distinguish the cases in `hBl : InBlock Fr p hk nL dPl dNo mo`.

Rewrite using `[if_pos ⟨hiff.1 hL, hB.2 hBl⟩, if_pos ⟨hL, hBl⟩, plMon_Bpl Fr p hk nL hx0 a rho mo h hL, noMon_Bpl Fr p hk nL hx0 a rho mo h hL, pl_mul]`. Rewrite using `[if_neg (fun hh => hBl (hB.1 hh.2)), if_neg (fun hh => hBl hh.2), mul_zero]`. Rewrite using `[if_neg (fun hh => hL (hiff.2 hh.1)), if_neg (fun hh => hL hh.1), mul_zero]`.
-/
theorem lev_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) 0) (Function.update dPl x0 (dPl x0 + 1)) dNo
        (monomial (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.castAdd K a)) 1) c) =
      X (x0, a) * levImg Fr p hk nL rho dPl dNo (monomial mo c) := by
  rw [levImg_monomial, levImg_monomial]
  have hiff := inLow_B Fr p hk nL hx0 (Fin.castAdd K a) rho mo h
  by_cases hL : InLow Fr p hk nL rho mo
  · have hB := block_Bpl Fr p hk nL hx0 a rho dPl dNo h mo hL
    by_cases hBl : InBlock Fr p hk nL dPl dNo mo
    · rw [if_pos ⟨hiff.1 hL, hB.2 hBl⟩, if_pos ⟨hL, hBl⟩, plMon_Bpl Fr p hk nL hx0 a rho mo h hL,
        noMon_Bpl Fr p hk nL hx0 a rho mo h hL, pl_mul]
    · rw [if_neg (fun hh => hBl (hB.1 hh.2)), if_neg (fun hh => hBl hh.2), mul_zero]
  · rw [if_neg (fun hh => hL (hiff.2 hh.1)), if_neg (fun hh => hL hh.1), mul_zero]

include hx0 in
/- English proof (translation)
Rewrite using `[levImg_monomial, levImg_monomial]`. Establish `hiff` using `inLow_B Fr p hk nL hx0 (Fin.natAdd r b) rho mo h`. Distinguish the cases in `hL : InLow Fr p hk nL rho mo`. Establish `hB` using `block_Bno Fr p hk nL hx0 b rho dPl dNo h mo hL`. Distinguish the cases in `hBl : InBlock Fr p hk nL dPl dNo mo`.

Rewrite using `[if_pos ⟨hiff.1 hL, hB.2 hBl⟩, if_pos ⟨hL, hBl⟩, plMon_Bno Fr p hk nL hx0 b rho mo h hL, noMon_Bno Fr p hk nL hx0 b rho mo h hL, no_mul]`. Rewrite using `[if_neg (fun hh => hBl (hB.1 hh.2)), if_neg (fun hh => hBl hh.2), oneT_zero]`. Rewrite using `[if_neg (fun hh => hL (hiff.2 hh.1)), if_neg (fun hh => hL hh.1), oneT_zero]`.
-/
theorem lev_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) 0) dPl (Function.update dNo x0 (dNo x0 + 1))
        (monomial (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.natAdd r b)) 1) c) =
      oneT (mulN (x0, b)) (levImg Fr p hk nL rho dPl dNo (monomial mo c)) := by
  rw [levImg_monomial, levImg_monomial]
  have hiff := inLow_B Fr p hk nL hx0 (Fin.natAdd r b) rho mo h
  by_cases hL : InLow Fr p hk nL rho mo
  · have hB := block_Bno Fr p hk nL hx0 b rho dPl dNo h mo hL
    by_cases hBl : InBlock Fr p hk nL dPl dNo mo
    · rw [if_pos ⟨hiff.1 hL, hB.2 hBl⟩, if_pos ⟨hL, hBl⟩, plMon_Bno Fr p hk nL hx0 b rho mo h hL,
        noMon_Bno Fr p hk nL hx0 b rho mo h hL, no_mul]
    · rw [if_neg (fun hh => hBl (hB.1 hh.2)), if_neg (fun hh => hBl hh.2), oneT_zero]
  · rw [if_neg (fun hh => hL (hiff.2 hh.1)), if_neg (fun hh => hL hh.1), oneT_zero]

include hx0 in
/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial mo c => rw [X_mul_mon, lev_A Fr p hk nL hx0 c0 rho dPl dNo h]`. Consider the case `add F G hF hG => rw [mul_add, levImg_add, levImg_add, hF, hG]`.
-/
theorem mul_A (c0 : Fin (r + K)) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL (Function.update rho (x0, c0) (rho (x0, c0) + 1)) dPl dNo (X (aVar Fr hk nL x0 c0) * F) =
      levImg Fr p hk nL rho dPl dNo F := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c => rw [X_mul_mon, lev_A Fr p hk nL hx0 c0 rho dPl dNo h]
  | add F G hF hG => rw [mul_add, levImg_add, levImg_add, hF, hG]

include hx0 in
/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial mo c => rw [X_mul_mon, lev_Bpl Fr p hk nL hx0 a rho dPl dNo h]`. Consider the case `add F G hF hG => rw [mul_add, levImg_add, levImg_add, hF, hG, mul_add]`.
-/
theorem mul_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) 0) (Function.update dPl x0 (dPl x0 + 1)) dNo
        (X (aVar Fr hk nL x0 (Fin.castAdd K a)) * F) = X (x0, a) * levImg Fr p hk nL rho dPl dNo F := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c => rw [X_mul_mon, lev_Bpl Fr p hk nL hx0 a rho dPl dNo h]
  | add F G hF hG => rw [mul_add, levImg_add, levImg_add, hF, hG, mul_add]

include hx0 in
/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial mo c => rw [X_mul_mon, lev_Bno Fr p hk nL hx0 b rho dPl dNo h]`. Consider the case `add F G hF hG => rw [mul_add, levImg_add, levImg_add, hF, hG, oneT_add]`.
-/
theorem mul_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) 0) dPl (Function.update dNo x0 (dNo x0 + 1))
        (X (aVar Fr hk nL x0 (Fin.natAdd r b)) * F) = oneT (mulN (x0, b)) (levImg Fr p hk nL rho dPl dNo F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c => rw [X_mul_mon, lev_Bno Fr p hk nL hx0 b rho dPl dNo h]
  | add F G hF hG => rw [mul_add, levImg_add, levImg_add, hF, hG, oneT_add]

/- English proof (translation)
Rewrite using `[Function.update_idem, Function.update_eq_self]`.
-/
theorem upd_back {α : Type} [DecidableEq α] (f : α → ℕ) (v : α) (t : ℕ) : Function.update (Function.update f v t) v (f v) = f := by
  rw [Function.update_idem, Function.update_eq_self]

include hx0 in
/- English proof (translation)
Establish `hP : 0 < lowP Fr p x0` using `pow_pos hp _`. Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial mo c`. Rewrite using `[X_mul_mon, levImg_monomial, if_neg]`. Introduce and unpack `⟨hL, hB⟩`.

Establish `hs : Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1) (x0, Fin.castAdd K a) + 1 = lowP Fr p x0`. Rewrite using `[Function.update_self]`. Use linear arithmetic over natural numbers and integers. Establish `hiff` using `inLow_B Fr p hk nL hx0 (Fin.castAdd K a) (Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)) mo hs`. Rewrite `hiff` using `[← h, upd_back]`.

Establish `hL'` using `hiff.2 hL`. Rewrite `hB` using `[inBlock_iff, plMon_Bpl Fr p hk nL hx0 a _ mo hs hL']`. Establish `h1` using `hB.1 x0`. Rewrite `h1` using `[sum_add_single, if_pos rfl, hd]`. Use linear arithmetic over natural numbers and integers.

Consider the case `add F G hF hG => rw [mul_add, levImg_add, hF, hG, add_zero]`.
-/
theorem mul_Bpl_zero (hp : 0 < p) (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) = 0) (hd : dPl x0 = 0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (X (aVar Fr hk nL x0 (Fin.castAdd K a)) * F) = 0 := by
  have hP : 0 < lowP Fr p x0 := pow_pos hp _
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    rw [X_mul_mon, levImg_monomial, if_neg]
    rintro ⟨hL, hB⟩
    have hs : Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1) (x0, Fin.castAdd K a) + 1 = lowP Fr p x0 := by
      rw [Function.update_self]; omega
    have hiff := inLow_B Fr p hk nL hx0 (Fin.castAdd K a)
      (Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)) mo hs
    rw [← h, upd_back] at hiff
    have hL' := hiff.2 hL
    rw [inBlock_iff, plMon_Bpl Fr p hk nL hx0 a _ mo hs hL'] at hB
    have h1 := hB.1 x0
    rw [sum_add_single, if_pos rfl, hd] at h1
    omega
  | add F G hF hG => rw [mul_add, levImg_add, hF, hG, add_zero]

include hx0 in
/- English proof (translation)
Establish `hP : 0 < lowP Fr p x0` using `pow_pos hp _`. Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial mo c`. Rewrite using `[X_mul_mon, levImg_monomial, if_neg]`. Introduce and unpack `⟨hL, hB⟩`.

Establish `hs : Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1) (x0, Fin.natAdd r b) + 1 = lowP Fr p x0`. Rewrite using `[Function.update_self]`. Use linear arithmetic over natural numbers and integers. Establish `hiff` using `inLow_B Fr p hk nL hx0 (Fin.natAdd r b) (Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)) mo hs`. Rewrite `hiff` using `[← h, upd_back]`.

Establish `hL'` using `hiff.2 hL`. Rewrite `hB` using `[inBlock_iff, noMon_Bno Fr p hk nL hx0 b _ mo hs hL']`. Establish `h1` using `hB.2 x0`. Rewrite `h1` using `[sum_add_single, if_pos rfl, hd]`. Use linear arithmetic over natural numbers and integers.

Consider the case `add F G hF hG => rw [mul_add, levImg_add, hF, hG, add_zero]`.
-/
theorem mul_Bno_zero (hp : 0 < p) (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) = 0) (hd : dNo x0 = 0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (X (aVar Fr hk nL x0 (Fin.natAdd r b)) * F) = 0 := by
  have hP : 0 < lowP Fr p x0 := pow_pos hp _
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    rw [X_mul_mon, levImg_monomial, if_neg]
    rintro ⟨hL, hB⟩
    have hs : Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1) (x0, Fin.natAdd r b) + 1 = lowP Fr p x0 := by
      rw [Function.update_self]; omega
    have hiff := inLow_B Fr p hk nL hx0 (Fin.natAdd r b)
      (Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)) mo hs
    rw [← h, upd_back] at hiff
    have hL' := hiff.2 hL
    rw [inBlock_iff, noMon_Bno Fr p hk nL hx0 b _ mo hs hL'] at hB
    have h1 := hB.2 x0
    rw [sum_add_single, if_pos rfl, hd] at h1
    omega
  | add F G hF hG => rw [mul_add, levImg_add, hF, hG, add_zero]

end Main

section Der

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
  {x0 : TL J nL r} (hx0 : ∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0)

/- English proof (translation)
Introduce `hL`. Establish `h1` using `(inLow_iff Fr p hk nL _ mo).1 hL x0 c0`. Rewrite `h1` using `[Function.update_self, h0, Nat.zero_mod]`. Use linear arithmetic over natural numbers and integers.
-/
theorem notLow_of_zero (c0 : Fin (r + K)) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h0 : mo (aVar Fr hk nL x0 c0) = 0) :
    ¬ InLow Fr p hk nL (Function.update rho (x0, c0) (rho (x0, c0) + 1)) mo := by
  intro hL
  have h1 := (inLow_iff Fr p hk nL _ mo).1 hL x0 c0
  rw [Function.update_self, h0, Nat.zero_mod] at h1
  omega

include hx0 in
/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial mo c`. Distinguish the cases in `h0 : mo (aVar Fr hk nL x0 (Fin.castAdd K a)) = 0`. Rewrite using `[pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial, if_neg (fun hh => notLow_of_zero Fr p hk nL _ rho mo h0 hh.1)]`. Simplify using the standard rewrite rules.

Take `⟨mo', rfl⟩` from `exists_add_single _ mo h0`. Rewrite using `[pderiv_mon_succ, lev_A Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]`. Distinguish the cases in `hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'`. Rewrite using `[if_pos hc, if_pos hc, pl_euler, ← map_smul, ← map_smul, ← map_add]`. Use `congr 1`.

Establish `e1 : mo' (aVar Fr hk nL x0 (Fin.castAdd K a)) + 1 = (rho (x0, Fin.castAdd K a) + 1) + lowP Fr p x0 * plMon Fr p hk nL mo' (x0, a)`. Rewrite using `[plMon_apply]`. Establish `h1` using `Nat.div_add_mod (mo' (aVar Fr hk nL x0 (Fin.castAdd K a))) (lowP Fr p x0)`. Establish `h2` using `(inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.castAdd K a)`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e1]`. Simplify using `only [smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hc, if_neg hc]`.

Simplify using the standard rewrite rules. Consider the case `add F G hF hG`. Simplify using `only [map_add, levImg_add, mul_add, smul_add, hF, hG]`. Normalize the expressions using the abelian group laws.
-/
theorem der_A_pl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 < lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (pderiv (aVar Fr hk nL x0 (Fin.castAdd K a)) F) =
      ((rho (x0, Fin.castAdd K a) + 1 : ℕ) : KK O) •
        levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) + 1)) dPl dNo F +
      ((lowP Fr p x0 : ℕ) : KK O) • (X (x0, a) * pderiv (x0, a)
        (levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) + 1)) dPl dNo F)) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    by_cases h0 : mo (aVar Fr hk nL x0 (Fin.castAdd K a)) = 0
    · rw [pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial,
        if_neg (fun hh => notLow_of_zero Fr p hk nL _ rho mo h0 hh.1)]
      simp
    · obtain ⟨mo', rfl⟩ := exists_add_single _ mo h0
      rw [pderiv_mon_succ, lev_A Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]
      by_cases hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'
      · rw [if_pos hc, if_pos hc, pl_euler, ← map_smul, ← map_smul, ← map_add]
        congr 1
        have e1 : mo' (aVar Fr hk nL x0 (Fin.castAdd K a)) + 1 =
            (rho (x0, Fin.castAdd K a) + 1) + lowP Fr p x0 * plMon Fr p hk nL mo' (x0, a) := by
          rw [plMon_apply]
          have h1 := Nat.div_add_mod (mo' (aVar Fr hk nL x0 (Fin.castAdd K a))) (lowP Fr p x0)
          have h2 := (inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.castAdd K a)
          omega
        rw [e1]
        simp only [smul_eq_mul]
        push_cast
        ring
      · rw [if_neg hc, if_neg hc]
        simp
  | add F G hF hG =>
    simp only [map_add, levImg_add, mul_add, smul_add, hF, hG]
    abel

include hx0 in
/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial mo c`. Distinguish the cases in `h0 : mo (aVar Fr hk nL x0 (Fin.natAdd r b)) = 0`. Rewrite using `[pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial, if_neg (fun hh => notLow_of_zero Fr p hk nL _ rho mo h0 hh.1), oneT_zero]`. Simplify using the standard rewrite rules.

Take `⟨mo', rfl⟩` from `exists_add_single _ mo h0`. Rewrite using `[pderiv_mon_succ, lev_A Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]`. Distinguish the cases in `hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'`. Rewrite using `[if_pos hc, if_pos hc, no_euler, ← map_smul, ← map_smul, ← map_add]`. Use `congr 1`.

Establish `e1 : mo' (aVar Fr hk nL x0 (Fin.natAdd r b)) + 1 = (rho (x0, Fin.natAdd r b) + 1) + lowP Fr p x0 * noMon Fr p hk nL mo' (x0, b)`. Rewrite using `[noMon_apply]`. Establish `h1` using `Nat.div_add_mod (mo' (aVar Fr hk nL x0 (Fin.natAdd r b))) (lowP Fr p x0)`. Establish `h2` using `(inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.natAdd r b)`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e1]`. Simplify using `only [smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hc, if_neg hc, oneT_zero]`.

Simplify using the standard rewrite rules. Consider the case `add F G hF hG`. Simplify using `only [map_add, levImg_add, oneT_add, smul_add, hF, hG]`. Normalize the expressions using the abelian group laws.
-/
theorem der_A_no (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 < lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (pderiv (aVar Fr hk nL x0 (Fin.natAdd r b)) F) =
      ((rho (x0, Fin.natAdd r b) + 1 : ℕ) : KK O) •
        levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) + 1)) dPl dNo F +
      ((lowP Fr p x0 : ℕ) : KK O) • oneT (mulN (x0, b) * derN (x0, b))
        (levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) + 1)) dPl dNo F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    by_cases h0 : mo (aVar Fr hk nL x0 (Fin.natAdd r b)) = 0
    · rw [pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial,
        if_neg (fun hh => notLow_of_zero Fr p hk nL _ rho mo h0 hh.1), oneT_zero]
      simp
    · obtain ⟨mo', rfl⟩ := exists_add_single _ mo h0
      rw [pderiv_mon_succ, lev_A Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]
      by_cases hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'
      · rw [if_pos hc, if_pos hc, no_euler, ← map_smul, ← map_smul, ← map_add]
        congr 1
        have e1 : mo' (aVar Fr hk nL x0 (Fin.natAdd r b)) + 1 =
            (rho (x0, Fin.natAdd r b) + 1) + lowP Fr p x0 * noMon Fr p hk nL mo' (x0, b) := by
          rw [noMon_apply]
          have h1 := Nat.div_add_mod (mo' (aVar Fr hk nL x0 (Fin.natAdd r b))) (lowP Fr p x0)
          have h2 := (inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.natAdd r b)
          omega
        rw [e1]
        simp only [smul_eq_mul]
        push_cast
        ring
      · rw [if_neg hc, if_neg hc, oneT_zero]
        simp
  | add F G hF hG =>
    simp only [map_add, levImg_add, oneT_add, smul_add, hF, hG]
    abel

include hx0 in
/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial mo c`. Distinguish the cases in `h0 : mo (aVar Fr hk nL x0 (Fin.castAdd K a)) = 0`. Rewrite using `[pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial] split_ifs`. Rewrite using `[pl_der_zero _ _ _ _ (by rw [plMon_apply, h0, Nat.zero_div]), smul_zero]`.

Rewrite using `[map_zero, smul_zero]`. Take `⟨mo', rfl⟩` from `exists_add_single _ mo h0`. Rewrite using `[pderiv_mon_succ, lev_Bpl Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]`. Distinguish the cases in `hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'`. Rewrite using `[if_pos hc, if_pos hc, pl_mul, pl_der, ← map_smul]`.

Use `congr 1`. Establish `e1 : mo' (aVar Fr hk nL x0 (Fin.castAdd K a)) + 1 = lowP Fr p x0 * (plMon Fr p hk nL mo' (x0, a) + 1)`. Rewrite using `[plMon_apply]`. Conclude with `nat_B_eq h ((inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.castAdd K a))`. Rewrite using `[e1]`.

Simplify using `only [smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hc, if_neg hc]`. Simplify using the standard rewrite rules.

Consider the case `add F G hF hG`. Simplify using `only [map_add, levImg_add, smul_add, hF, hG]`.
-/
theorem der_B_pl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (pderiv (aVar Fr hk nL x0 (Fin.castAdd K a)) F) =
      ((lowP Fr p x0 : ℕ) : KK O) • pderiv (x0, a)
        (levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) 0) (Function.update dPl x0 (dPl x0 + 1)) dNo F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    by_cases h0 : mo (aVar Fr hk nL x0 (Fin.castAdd K a)) = 0
    · rw [pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial]
      split_ifs
      · rw [pl_der_zero _ _ _ _ (by rw [plMon_apply, h0, Nat.zero_div]), smul_zero]
      · rw [map_zero, smul_zero]
    · obtain ⟨mo', rfl⟩ := exists_add_single _ mo h0
      rw [pderiv_mon_succ, lev_Bpl Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]
      by_cases hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'
      · rw [if_pos hc, if_pos hc, pl_mul, pl_der, ← map_smul]
        congr 1
        have e1 : mo' (aVar Fr hk nL x0 (Fin.castAdd K a)) + 1 =
            lowP Fr p x0 * (plMon Fr p hk nL mo' (x0, a) + 1) := by
          rw [plMon_apply]
          exact nat_B_eq h ((inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.castAdd K a))
        rw [e1]
        simp only [smul_eq_mul]
        push_cast
        ring
      · rw [if_neg hc, if_neg hc]
        simp
  | add F G hF hG =>
    simp only [map_add, levImg_add, smul_add, hF, hG]

include hx0 in
/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial mo c`. Distinguish the cases in `h0 : mo (aVar Fr hk nL x0 (Fin.natAdd r b)) = 0`. Rewrite using `[pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial] split_ifs`. Rewrite using `[no_der_zero _ _ _ _ (by rw [noMon_apply, h0, Nat.zero_div]), smul_zero]`.

Rewrite using `[oneT_zero, smul_zero]`. Take `⟨mo', rfl⟩` from `exists_add_single _ mo h0`. Rewrite using `[pderiv_mon_succ, lev_Bno Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]`. Distinguish the cases in `hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'`. Rewrite using `[if_pos hc, if_pos hc, no_mul, no_der, ← map_smul]`.

Use `congr 1`. Establish `e1 : mo' (aVar Fr hk nL x0 (Fin.natAdd r b)) + 1 = lowP Fr p x0 * (noMon Fr p hk nL mo' (x0, b) + 1)`. Rewrite using `[noMon_apply]`. Conclude with `nat_B_eq h ((inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.natAdd r b))`. Rewrite using `[e1]`.

Simplify using `only [smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hc, if_neg hc, oneT_zero, oneT_zero, smul_zero]`. Consider the case `add F G hF hG`.

Simplify using `only [map_add, levImg_add, oneT_add, smul_add, hF, hG]`.
-/
theorem der_B_no (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (pderiv (aVar Fr hk nL x0 (Fin.natAdd r b)) F) =
      ((lowP Fr p x0 : ℕ) : KK O) • oneT (derN (x0, b))
        (levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) 0) dPl (Function.update dNo x0 (dNo x0 + 1)) F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    by_cases h0 : mo (aVar Fr hk nL x0 (Fin.natAdd r b)) = 0
    · rw [pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial]
      split_ifs
      · rw [no_der_zero _ _ _ _ (by rw [noMon_apply, h0, Nat.zero_div]), smul_zero]
      · rw [oneT_zero, smul_zero]
    · obtain ⟨mo', rfl⟩ := exists_add_single _ mo h0
      rw [pderiv_mon_succ, lev_Bno Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]
      by_cases hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'
      · rw [if_pos hc, if_pos hc, no_mul, no_der, ← map_smul]
        congr 1
        have e1 : mo' (aVar Fr hk nL x0 (Fin.natAdd r b)) + 1 =
            lowP Fr p x0 * (noMon Fr p hk nL mo' (x0, b) + 1) := by
          rw [noMon_apply]
          exact nat_B_eq h ((inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.natAdd r b))
        rw [e1]
        simp only [smul_eq_mul]
        push_cast
        ring
      · rw [if_neg hc, if_neg hc, oneT_zero, oneT_zero, smul_zero]
  | add F G hF hG =>
    simp only [map_add, levImg_add, oneT_add, smul_add, hF, hG]

end Der

/- English proof (translation)
Introduce `p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 a rho dPl dNo F`. Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Rewrite using `[plVar_eq]`. Break down `lt_trichotomy (rho (x0, Fin.castAdd K a) + 1) (lowP Fr p x0) with h | h | h` into its components or cases. Use `⟨((rho (x0, Fin.castAdd K a) + 1 : ℕ) : KK O), ((lowP Fr p x0 : ℕ) : KK O), 0, Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) + 1), rho, ?_⟩` and prove the remaining obligations.

Rewrite using `[der_A_pl Fr p hk nL hx0 a rho dPl dNo h F, zero_smul, add_zero]`. Use `⟨0, 0, ((lowP Fr p x0 : ℕ) : KK O), rho, Function.update rho (x0, Fin.castAdd K a) 0, ?_⟩` and prove the remaining obligations. Rewrite using `[der_B_pl Fr p hk nL hx0 a rho dPl dNo h F, zero_smul, zero_smul, zero_add, zero_add]`. Use `⟨0, 0, 0, rho, rho, ?_⟩` and prove the remaining obligations. Rewrite using `[levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.castAdd K a) (by omega), zero_smul, zero_smul, zero_smul, add_zero, add_zero]`.
-/
theorem _root_.Formalism.MainNotions.PairMembershipBlocks.trDerPl : TrDerPl := by
  intro p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 a rho dPl dNo F
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [plVar_eq]
  rcases lt_trichotomy (rho (x0, Fin.castAdd K a) + 1) (lowP Fr p x0) with h | h | h
  · refine ⟨((rho (x0, Fin.castAdd K a) + 1 : ℕ) : KK O), ((lowP Fr p x0 : ℕ) : KK O), 0,
      Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) + 1), rho, ?_⟩
    rw [der_A_pl Fr p hk nL hx0 a rho dPl dNo h F, zero_smul, add_zero]
  · refine ⟨0, 0, ((lowP Fr p x0 : ℕ) : KK O), rho, Function.update rho (x0, Fin.castAdd K a) 0, ?_⟩
    rw [der_B_pl Fr p hk nL hx0 a rho dPl dNo h F, zero_smul, zero_smul, zero_add, zero_add]
  · refine ⟨0, 0, 0, rho, rho, ?_⟩
    rw [levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.castAdd K a) (by omega), zero_smul, zero_smul, zero_smul, add_zero,
      add_zero]

/- English proof (translation)
Introduce `p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 a rho dPl dNo F`. Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Establish `hP : 0 < lowP Fr p x0` using `pow_pos hp _`. Rewrite using `[plVar_eq]`. Distinguish the cases in `h0 : rho (x0, Fin.castAdd K a) = 0`.

Distinguish the cases in `hd : dPl x0 = 0`. Use `⟨0, 0, rho, rho, fun _ => rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_Bpl_zero Fr p hk nL hx0 hp a rho dPl dNo h0 hd F, zero_smul, zero_smul, add_zero]`. Use `⟨0, 1, rho, Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1), fun h => absurd h hd, ?_⟩` and prove the remaining obligations. Establish `hs : Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1) (x0, Fin.castAdd K a) + 1 = lowP Fr p x0`.

Rewrite using `[Function.update_self]`. Use linear arithmetic over natural numbers and integers. Establish `key` using `mul_Bpl Fr p hk nL hx0 a (Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)) (Function.update dPl x0 (dPl x0 - 1)) dNo hs F`. Establish `e1 : Function.update (Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)) (x0, Fin.castAdd K a) 0 = rho`. Use `upd_back rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)` as an intermediate fact.

Rewrite `this` using `[h0]`. Then use the resulting hypothesis. Establish `e2 : Function.update (Function.update dPl x0 (dPl x0 - 1)) x0 (Function.update dPl x0 (dPl x0 - 1) x0 + 1) = dPl`. Rewrite using `[Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hd)]`. Conclude with `upd_back dPl x0 _`. Rewrite `key` using `[e1, e2]`.

Rewrite using `[key, zero_smul, zero_add, one_smul]`. Distinguish the cases in `hlt : rho (x0, Fin.castAdd K a) < lowP Fr p x0`. Use `⟨1, 0, Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1), rho, fun _ => rfl, ?_⟩` and prove the remaining obligations. Establish `hs : Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1) (x0, Fin.castAdd K a) + 1 < lowP Fr p x0`. Rewrite using `[Function.update_self]`.

Use linear arithmetic over natural numbers and integers. Establish `key` using `mul_A Fr p hk nL hx0 (Fin.castAdd K a) (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1)) dPl dNo hs F`. Establish `e1 : Function.update (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1)) (x0, Fin.castAdd K a) (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1) (x0, Fin.castAdd K a) + 1) = rho`. Rewrite using `[Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]`. Conclude with `upd_back rho (x0, Fin.castAdd K a) _`.

Rewrite `key` using `[e1]`. Rewrite using `[key, one_smul, zero_smul, add_zero]`. Use `⟨0, 0, rho, rho, fun _ => rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.castAdd K a) (by omega), zero_smul, zero_smul, add_zero]`.
-/
theorem _root_.Formalism.MainNotions.PairMembershipBlocks.trMulPl : TrMulPl := by
  intro p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 a rho dPl dNo F
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hP : 0 < lowP Fr p x0 := pow_pos hp _
  rw [plVar_eq]
  by_cases h0 : rho (x0, Fin.castAdd K a) = 0
  · by_cases hd : dPl x0 = 0
    · refine ⟨0, 0, rho, rho, fun _ => rfl, ?_⟩
      rw [mul_Bpl_zero Fr p hk nL hx0 hp a rho dPl dNo h0 hd F, zero_smul, zero_smul, add_zero]
    · refine ⟨0, 1, rho, Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1), fun h => absurd h hd, ?_⟩
      have hs : Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1) (x0, Fin.castAdd K a) + 1 = lowP Fr p x0 := by
        rw [Function.update_self]; omega
      have key := mul_Bpl Fr p hk nL hx0 a (Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1))
        (Function.update dPl x0 (dPl x0 - 1)) dNo hs F
      have e1 : Function.update (Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)) (x0, Fin.castAdd K a) 0 = rho := by
        have := upd_back rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)
        rwa [h0] at this
      have e2 : Function.update (Function.update dPl x0 (dPl x0 - 1)) x0
          (Function.update dPl x0 (dPl x0 - 1) x0 + 1) = dPl := by
        rw [Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hd)]
        exact upd_back dPl x0 _
      rw [e1, e2] at key
      rw [key, zero_smul, zero_add, one_smul]
  · by_cases hlt : rho (x0, Fin.castAdd K a) < lowP Fr p x0
    · refine ⟨1, 0, Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1), rho, fun _ => rfl, ?_⟩
      have hs : Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1) (x0, Fin.castAdd K a) + 1 < lowP Fr p x0 := by
        rw [Function.update_self]; omega
      have key := mul_A Fr p hk nL hx0 (Fin.castAdd K a) (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1)) dPl dNo hs F
      have e1 : Function.update (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1)) (x0, Fin.castAdd K a)
          (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1) (x0, Fin.castAdd K a) + 1) = rho := by
        rw [Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
        exact upd_back rho (x0, Fin.castAdd K a) _
      rw [e1] at key
      rw [key, one_smul, zero_smul, add_zero]
    · refine ⟨0, 0, rho, rho, fun _ => rfl, ?_⟩
      rw [levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.castAdd K a) (by omega), zero_smul, zero_smul, add_zero]

/- English proof (translation)
Introduce `p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 b rho dPl dNo F`. Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Rewrite using `[noVar_eq]`. Break down `lt_trichotomy (rho (x0, Fin.natAdd r b) + 1) (lowP Fr p x0) with h | h | h` into its components or cases. Use `⟨((rho (x0, Fin.natAdd r b) + 1 : ℕ) : KK O), ((lowP Fr p x0 : ℕ) : KK O), 0, Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) + 1), rho, ?_⟩` and prove the remaining obligations.

Rewrite using `[der_A_no Fr p hk nL hx0 b rho dPl dNo h F, zero_smul, add_zero]`. Use `⟨0, 0, ((lowP Fr p x0 : ℕ) : KK O), rho, Function.update rho (x0, Fin.natAdd r b) 0, ?_⟩` and prove the remaining obligations. Rewrite using `[der_B_no Fr p hk nL hx0 b rho dPl dNo h F, zero_smul, zero_smul, zero_add, zero_add]`. Use `⟨0, 0, 0, rho, rho, ?_⟩` and prove the remaining obligations. Rewrite using `[levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.natAdd r b) (by omega), zero_smul, zero_smul, zero_smul, add_zero, add_zero]`.
-/
theorem _root_.Formalism.MainNotions.PairMembershipBlocks.trDerNo : TrDerNo := by
  intro p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 b rho dPl dNo F
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [noVar_eq]
  rcases lt_trichotomy (rho (x0, Fin.natAdd r b) + 1) (lowP Fr p x0) with h | h | h
  · refine ⟨((rho (x0, Fin.natAdd r b) + 1 : ℕ) : KK O), ((lowP Fr p x0 : ℕ) : KK O), 0,
      Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) + 1), rho, ?_⟩
    rw [der_A_no Fr p hk nL hx0 b rho dPl dNo h F, zero_smul, add_zero]
  · refine ⟨0, 0, ((lowP Fr p x0 : ℕ) : KK O), rho, Function.update rho (x0, Fin.natAdd r b) 0, ?_⟩
    rw [der_B_no Fr p hk nL hx0 b rho dPl dNo h F, zero_smul, zero_smul, zero_add, zero_add]
  · refine ⟨0, 0, 0, rho, rho, ?_⟩
    rw [levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.natAdd r b) (by omega), zero_smul, zero_smul, zero_smul, add_zero,
      add_zero]

/- English proof (translation)
Introduce `p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 b rho dPl dNo F`. Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Establish `hP : 0 < lowP Fr p x0` using `pow_pos hp _`. Rewrite using `[noVar_eq]`. Distinguish the cases in `h0 : rho (x0, Fin.natAdd r b) = 0`.

Distinguish the cases in `hd : dNo x0 = 0`. Use `⟨0, 0, rho, rho, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_Bno_zero Fr p hk nL hx0 hp b rho dPl dNo h0 hd F, zero_smul, zero_smul, add_zero]`. Use `⟨0, 1, rho, Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1), ?_⟩` and prove the remaining obligations. Establish `hs : Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1) (x0, Fin.natAdd r b) + 1 = lowP Fr p x0`.

Rewrite using `[Function.update_self]`. Use linear arithmetic over natural numbers and integers. Establish `key` using `mul_Bno Fr p hk nL hx0 b (Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)) dPl (Function.update dNo x0 (dNo x0 - 1)) hs F`. Establish `e1 : Function.update (Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)) (x0, Fin.natAdd r b) 0 = rho`. Use `upd_back rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)` as an intermediate fact.

Rewrite `this` using `[h0]`. Then use the resulting hypothesis. Establish `e2 : Function.update (Function.update dNo x0 (dNo x0 - 1)) x0 (Function.update dNo x0 (dNo x0 - 1) x0 + 1) = dNo`. Rewrite using `[Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hd)]`. Conclude with `upd_back dNo x0 _`. Rewrite `key` using `[e1, e2]`.

Rewrite using `[key, zero_smul, zero_add, one_smul]`. Distinguish the cases in `hlt : rho (x0, Fin.natAdd r b) < lowP Fr p x0`. Use `⟨1, 0, Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1), rho, ?_⟩` and prove the remaining obligations. Establish `hs : Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1) (x0, Fin.natAdd r b) + 1 < lowP Fr p x0`. Rewrite using `[Function.update_self]`.

Use linear arithmetic over natural numbers and integers. Establish `key` using `mul_A Fr p hk nL hx0 (Fin.natAdd r b) (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1)) dPl dNo hs F`. Establish `e1 : Function.update (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1)) (x0, Fin.natAdd r b) (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1) (x0, Fin.natAdd r b) + 1) = rho`. Rewrite using `[Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]`. Conclude with `upd_back rho (x0, Fin.natAdd r b) _`.

Rewrite `key` using `[e1]`. Rewrite using `[key, one_smul, zero_smul, add_zero]`. Use `⟨0, 0, rho, rho, ?_⟩` and prove the remaining obligations. Rewrite using `[levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.natAdd r b) (by omega), zero_smul, zero_smul, add_zero]`.
-/
theorem _root_.Formalism.MainNotions.PairMembershipBlocks.trMulNo : TrMulNo := by
  intro p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 b rho dPl dNo F
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hP : 0 < lowP Fr p x0 := pow_pos hp _
  rw [noVar_eq]
  by_cases h0 : rho (x0, Fin.natAdd r b) = 0
  · by_cases hd : dNo x0 = 0
    · refine ⟨0, 0, rho, rho, ?_⟩
      rw [mul_Bno_zero Fr p hk nL hx0 hp b rho dPl dNo h0 hd F, zero_smul, zero_smul, add_zero]
    · refine ⟨0, 1, rho, Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1), ?_⟩
      have hs : Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1) (x0, Fin.natAdd r b) + 1 = lowP Fr p x0 := by
        rw [Function.update_self]; omega
      have key := mul_Bno Fr p hk nL hx0 b (Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1))
        dPl (Function.update dNo x0 (dNo x0 - 1)) hs F
      have e1 : Function.update (Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)) (x0, Fin.natAdd r b) 0 = rho := by
        have := upd_back rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)
        rwa [h0] at this
      have e2 : Function.update (Function.update dNo x0 (dNo x0 - 1)) x0
          (Function.update dNo x0 (dNo x0 - 1) x0 + 1) = dNo := by
        rw [Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hd)]
        exact upd_back dNo x0 _
      rw [e1, e2] at key
      rw [key, zero_smul, zero_add, one_smul]
  · by_cases hlt : rho (x0, Fin.natAdd r b) < lowP Fr p x0
    · refine ⟨1, 0, Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1), rho, ?_⟩
      have hs : Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1) (x0, Fin.natAdd r b) + 1 < lowP Fr p x0 := by
        rw [Function.update_self]; omega
      have key := mul_A Fr p hk nL hx0 (Fin.natAdd r b) (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1)) dPl dNo hs F
      have e1 : Function.update (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1)) (x0, Fin.natAdd r b)
          (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1) (x0, Fin.natAdd r b) + 1) = rho := by
        rw [Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
        exact upd_back rho (x0, Fin.natAdd r b) _
      rw [e1] at key
      rw [key, one_smul, zero_smul, add_zero]
    · refine ⟨0, 0, rho, rho, ?_⟩
      rw [levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.natAdd r b) (by omega), zero_smul, zero_smul, add_zero]

end Formalism.MainNotions.PairMembershipBlocks.Tr
