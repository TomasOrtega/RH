import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.HasUniqueFixedPoint

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.BaseCaseIdentities (OrdGE NoConst)

section Gen

variable {k : Type*} [Field k] {Z B : Type*}

structure Contr (Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)) : Prop where
  noConst : ∀ t, NoConst (Ψ t)
  contr : ∀ (t t' : B → MvPowerSeries Z k) (n : ℕ), NoConst t → NoConst t' →
    (∀ c, OrdGE (n + 1) (t c - t' c)) → ∀ b, OrdGE (n + 2) (Ψ t b - Ψ t' b)

namespace Contr

variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)

include H

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simpa using ht`. Consider the case `succ n`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `H.noConst _`.
-/
theorem noConst_iterate {t : B → MvPowerSeries Z k} (ht : NoConst t) (n : ℕ) :
    NoConst (Ψ^[n] t) := by
  cases n with
  | zero => simpa using ht
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact H.noConst _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `c A hA`. Simplify using `only [Function.iterate_zero, id_eq, map_sub, ha c A hA, hb c A hA, sub_zero]`. Consider the case `succ n ih`.

Introduce `c`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply']`. Conclude with `H.contr _ _ n (H.noConst_iterate ha n) (H.noConst_iterate hb n) ih c`.
-/
theorem iterate_close {a b : B → MvPowerSeries Z k} (ha : NoConst a) (hb : NoConst b) (n : ℕ) :
    ∀ c, OrdGE (n + 1) (Ψ^[n] a c - Ψ^[n] b c) := by
  induction n with
  | zero =>
    intro c A hA
    simp only [Function.iterate_zero, id_eq, map_sub, ha c A hA, hb c A hA, sub_zero]
  | succ n ih =>
    intro c
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact H.contr _ _ n (H.noConst_iterate ha n) (H.noConst_iterate hb n) ih c

omit H in
/- English proof (translation)
Introduce `c A _`. Simplify using the standard rewrite rules.
-/
theorem noConst_zero : NoConst (0 : B → MvPowerSeries Z k) := by
  intro c A _
  simp

def fixPt (_H : Contr Ψ) : B → MvPowerSeries Z k := fun c A => coeff A (Ψ^[A.degree] 0 c)

/- English proof (translation)
Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hn`. Establish `e : coeff A (H.fixPt c) = coeff A (Ψ^[A.degree] 0 c)` using `rfl`. Establish `h1` using `H.iterate_close (a := Ψ^[j] 0) (b := 0) (H.noConst_iterate noConst_zero j) noConst_zero A.degree c A (Nat.lt_succ_self _)`. Rewrite `h1` using `[map_sub, sub_eq_zero]`. Rewrite using `[Function.iterate_add_apply, e]`.

Conclude with `h1`.
-/
theorem coeff_iterate_zero (c : B) (A : Z →₀ ℕ) {n : ℕ} (hn : A.degree ≤ n) :
    coeff A (Ψ^[n] 0 c) = coeff A (H.fixPt c) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e : coeff A (H.fixPt c) = coeff A (Ψ^[A.degree] 0 c) := rfl
  have h1 := H.iterate_close (a := Ψ^[j] 0) (b := 0) (H.noConst_iterate noConst_zero j)
    noConst_zero A.degree c A (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at h1
  rw [Function.iterate_add_apply, e]
  exact h1

/- English proof (translation)
Introduce `A hA`. Rewrite using `[map_sub, ← H.coeff_iterate_zero c A (Nat.lt_succ_iff.mp hA), sub_self]`.
-/
theorem fixPt_close (n : ℕ) (c : B) : OrdGE (n + 1) (H.fixPt c - Ψ^[n] 0 c) := by
  intro A hA
  rw [map_sub, ← H.coeff_iterate_zero c A (Nat.lt_succ_iff.mp hA), sub_self]

/- English proof (translation)
Introduce `c A hA`. Establish `h` using `H.fixPt_close 0 c A hA`. Simplify using `using h`.
-/
theorem noConst_fixPt : NoConst H.fixPt := by
  intro c A hA
  have h := H.fixPt_close 0 c A hA
  simpa using h

/- English proof (translation)
Use function extensionality and compare the values at `c`. Use extensionality with `A`. Establish `h1` using `H.contr H.fixPt (Ψ^[A.degree] 0) A.degree H.noConst_fixPt (H.noConst_iterate noConst_zero _) (fun c' => H.fixPt_close A.degree c') c A (by omega)`. Rewrite `h1` using `[map_sub, sub_eq_zero, ← Function.iterate_succ_apply' Ψ A.degree 0]`. Rewrite using `[h1, H.coeff_iterate_zero c A (Nat.le_succ _)]`.
-/
theorem fix_fixPt : Ψ H.fixPt = H.fixPt := by
  funext c
  ext A
  have h1 := H.contr H.fixPt (Ψ^[A.degree] 0) A.degree H.noConst_fixPt
    (H.noConst_iterate noConst_zero _) (fun c' => H.fixPt_close A.degree c') c A (by omega)
  rw [map_sub, sub_eq_zero, ← Function.iterate_succ_apply' Ψ A.degree 0] at h1
  rw [h1, H.coeff_iterate_zero c A (Nat.le_succ _)]

/- English proof (translation)
Use `⟨H.fixPt, ⟨H.noConst_fixPt, H.fix_fixPt⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨ht, hft⟩`. Use function extensionality and compare the values at `c`. Use extensionality with `A`. Establish `h1` using `H.iterate_close ht H.noConst_fixPt A.degree c A (Nat.lt_succ_self _)`.

Rewrite `h1` using `[Function.iterate_fixed hft, Function.iterate_fixed H.fix_fixPt, map_sub, sub_eq_zero]`. Conclude with `h1`.
-/
theorem exists_unique : ∃! t : B → MvPowerSeries Z k, NoConst t ∧ Ψ t = t := by
  refine ⟨H.fixPt, ⟨H.noConst_fixPt, H.fix_fixPt⟩, ?_⟩
  rintro t ⟨ht, hft⟩
  funext c
  ext A
  have h1 := H.iterate_close ht H.noConst_fixPt A.degree c A (Nat.lt_succ_self _)
  rw [Function.iterate_fixed hft, Function.iterate_fixed H.fix_fixPt, map_sub, sub_eq_zero] at h1
  exact h1

end Contr

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h c`. Establish `h0` using `h c 0 (by simp)`. Simplify using `using h0`. Introduce `h c A hA`.

Establish `hA0 : A.degree = 0` using `by omega`. Establish `hA1 : A = 0` using `by first`. Consider the case `exact (Finsupp.degree_eq_zero_iff A).mp hA0`. Consider the case `exact Finsupp.degree_eq_zero_iff.mp hA0`. Consider the case `simpa using hA0`.

Substitute `hA1` using the available equality. Simplify using `using h c`.
-/
theorem noConst_iff (t : B → MvPowerSeries Z k) :
    NoConst t ↔ ∀ c, MvPowerSeries.constantCoeff (t c) = 0 := by
  constructor
  · intro h c
    have h0 := h c 0 (by simp)
    simpa using h0
  · intro h c A hA
    have hA0 : A.degree = 0 := by omega
    have hA1 : A = 0 := by
      first
      | exact (Finsupp.degree_eq_zero_iff A).mp hA0
      | exact Finsupp.degree_eq_zero_iff.mp hA0
      | simpa using hA0
    subst hA1
    simpa using h c

end Gen

section Main

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {X : Cart V d I J}

namespace Sys

variable (S : Sys X)

def Mt : Matrix I I C := Matrix.of S.tan

/- English proof (translation)
Establish `h` using `S.3 c`. Unfold `Cart.IsCurve at h`. Unfold `Sys.al`. Rewrite using `[h.2.1]`. Both sides reduce to the same expression.
-/
theorem al_zero (c x : I) : S.al c 0 x = S.Mt c x := by
  have h := S.3 c
  unfold Cart.IsCurve at h
  unfold Sys.al
  rw [h.2.1]
  rfl

/- English proof (translation)
Introduce `h`. Establish `h5` using `S.4`. Express the relevant statement in the definitionally equal form `V.v S.Mt.det = 0 at h5`. Rewrite `h5` using `[h, AddValuation.map_zero]`. Simplify using `at h5`.
-/
theorem det_ne : S.Mt.det ≠ 0 := by
  intro h
  have h5 := S.4
  change V.v S.Mt.det = 0 at h5
  rw [h, AddValuation.map_zero] at h5
  simp at h5

def Rr (t : I → MvPowerSeries I C) (x : I) (μ : I →₀ ℕ) : C :=
  ∑ s ∈ Finset.range μ.degree, ∑ c : I, S.al c (s + 1) x * coeff μ (t c ^ (V.l ^ (s + 1)))

def dl (x : I) (μ : I →₀ ℕ) : C := if μ = Finsupp.single x 1 then 1 else 0

def Ps (t : I → MvPowerSeries I C) : I → MvPowerSeries I C := fun c μ =>
  Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹ c

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_Ps (t : I → MvPowerSeries I C) (c : I) (μ : I →₀ ℕ) :
    coeff μ (S.Ps t c) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹ c := rfl

/- English proof (translation)
Use `first`. Consider the case `exact V.3.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero s) _)`. Consider the case `exact le_trans V.3.two_le (Nat.le_self_pow (by omega) _)`. Consider the case `calc 2 ≤ V.l := V.3.two_le _ = V.l ^ 1 := (pow_one _).symm _ ≤ V.l ^ (s + 1) := Nat.pow_le_pow_right V.3.pos (by omega)`.
-/
theorem two_le_pow (s : ℕ) : 2 ≤ V.l ^ (s + 1) := by
  first
  | exact V.3.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero s) _)
  | exact le_trans V.3.two_le (Nat.le_self_pow (by omega) _)
  | calc 2 ≤ V.l := V.3.two_le
      _ = V.l ^ 1 := (pow_one _).symm
      _ ≤ V.l ^ (s + 1) := Nat.pow_le_pow_right V.3.pos (by omega)

/- English proof (translation)
Establish `hA0 : A.degree = 0` using `by omega`. Rewrite using `[coeff_Ps]`. Establish `: (fun x => dl x A - S.Rr t x A) = (0 : I → C)`. Use function extensionality and compare the values at `x`. Establish `h1 : dl (C` using `C) x A = 0 := by`.

Unfold `dl`. Rewrite using `[if_neg]`. Introduce `h`. Rewrite `hA0` using `[h, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers.

Establish `h2 : S.Rr t x A = 0`. Unfold `Rr`. Rewrite using `[hA0]`. Simplify using the standard rewrite rules. Simplify using `[h1, h2]`.

Rewrite using `[this, Matrix.zero_vecMul]`. Both sides reduce to the same expression. Use `contr t t' n ht ht' h b A hA := by`. Rewrite using `[map_sub, coeff_Ps, coeff_Ps, sub_eq_zero]`. Establish `: (fun x => dl x A - S.Rr t x A) = (fun x => dl x A - S.Rr t' x A)`.

Use function extensionality and compare the values at `x`. Use `congr 1`. Unfold `Rr`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `hN` using `two_le_pow (V := V) s`.

Use `Formalism.BaseCaseIdentities.OrdGE.pow_sub_pow (ht c) (ht' c) (h c) (N := V.l ^ (s + 1)) (by omega) A (by omega)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Rewrite using `[this]`. Rewrite using `[this]`.
-/
theorem contr : Contr S.Ps where
  noConst t c A hA := by
    have hA0 : A.degree = 0 := by omega
    rw [coeff_Ps]
    have : (fun x => dl x A - S.Rr t x A) = (0 : I → C) := by
      funext x
      have h1 : dl (C := C) x A = 0 := by
        unfold dl
        rw [if_neg]
        intro h
        rw [h, Finsupp.degree_single] at hA0
        omega
      have h2 : S.Rr t x A = 0 := by
        unfold Rr
        rw [hA0]
        simp
      simp [h1, h2]
    rw [this, Matrix.zero_vecMul]
    rfl
  contr t t' n ht ht' h b A hA := by
    rw [map_sub, coeff_Ps, coeff_Ps, sub_eq_zero]
    have : (fun x => dl x A - S.Rr t x A) = (fun x => dl x A - S.Rr t' x A) := by
      funext x
      congr 1
      unfold Rr
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
      have hN := two_le_pow (V := V) s
      have := Formalism.BaseCaseIdentities.OrdGE.pow_sub_pow (ht c) (ht' c) (h c) (N := V.l ^ (s + 1)) (by omega) A
        (by omega)
      rw [map_sub, sub_eq_zero] at this
      rw [this]
    rw [this]

/- English proof (translation)
Rewrite using `[Finset.sum_range_succ', add_comm (Matrix.vecMul _ _ _)]`. Use `congr 1`. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `(show _ = ∑ c, coeff μ (t c) * S.Mt c x`.

Conclude with `Finset.sum_congr rfl fun c _ => by rw [S.al_zero c x, pow_zero, pow_one, mul_comm])`.
-/
theorem eqn_eq (t : I → MvPowerSeries I C) (x : I) (μ : I →₀ ℕ) :
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ c : I,
        S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s))) =
      Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ := by
  rw [Finset.sum_range_succ', add_comm (Matrix.vecMul _ _ _)]
  congr 1
  all_goals first
    | rfl
    | (show _ = ∑ c, coeff μ (t c) * S.Mt c x
       exact Finset.sum_congr rfl fun c _ => by rw [S.al_zero c x, pow_zero, pow_one, mul_comm])

/- English proof (translation)
Establish `hdet : IsUnit S.Mt.det` using `isUnit_iff_ne_zero.mpr S.det_ne`. Establish `key : ∀ μ : I →₀ ℕ, ((∀ x, Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ = dl x μ) ↔ (fun c => coeff μ (t c)) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹)`. Introduce `μ`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h' : Matrix.vecMul (fun c => coeff μ (t c)) S.Mt = fun x => dl x μ - S.Rr t x μ`. Use function extensionality and compare the values at `x`. Conclude with `eq_sub_of_add_eq (h x)`. Rewrite using `[← h', Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]`. Introduce `h x`.

Rewrite using `[h, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]`. Simplify using the standard rewrite rules. Rewrite using `[Sys.IsT, noConst_iff]`. Use `and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `c`.

Use extensionality with `μ`. Rewrite using `[S.coeff_Ps]`. Establish `hk` using `(key μ).mp (fun x => by rw [← S.eqn_eq t x μ]; exact h x μ)`. Conclude with `(congrFun hk c).symm`. Introduce `x μ`.

Rewrite using `[S.eqn_eq t x μ]`. Use `(key μ).mpr ?_ x` and prove the remaining obligations. Use function extensionality and compare the values at `c`. Rewrite using `[← S.coeff_Ps, h]`.
-/
theorem isT_iff (t : I → MvPowerSeries I C) : S.IsT t ↔ NoConst t ∧ S.Ps t = t := by
  have hdet : IsUnit S.Mt.det := isUnit_iff_ne_zero.mpr S.det_ne
  have key : ∀ μ : I →₀ ℕ, ((∀ x, Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ = dl x μ) ↔
      (fun c => coeff μ (t c)) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹) := by
    intro μ
    constructor
    · intro h
      have h' : Matrix.vecMul (fun c => coeff μ (t c)) S.Mt = fun x => dl x μ - S.Rr t x μ := by
        funext x
        exact eq_sub_of_add_eq (h x)
      rw [← h', Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    · intro h x
      rw [h, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
      simp
  rw [Sys.IsT, noConst_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · funext c
    ext μ
    rw [S.coeff_Ps]
    have hk := (key μ).mp (fun x => by rw [← S.eqn_eq t x μ]; exact h x μ)
    exact (congrFun hk c).symm
  · intro x μ
    rw [S.eqn_eq t x μ]
    refine (key μ).mpr ?_ x
    funext c
    rw [← S.coeff_Ps, h]

end Sys

/- English proof (translation)
Introduce `S`. Take `⟨t, ⟨h1, h2⟩, hu⟩` from `S.contr.exists_unique`. Conclude with `⟨t, (S.isT_iff t).mpr ⟨h1, h2⟩, fun t' ht' => hu t' ((S.isT_iff t').mp ht')⟩`.
-/
theorem tExistsUnique (X : Cart V d I J) : TExistsUnique X := by
  intro S
  obtain ⟨t, ⟨h1, h2⟩, hu⟩ := S.contr.exists_unique
  exact ⟨t, (S.isT_iff t).mpr ⟨h1, h2⟩, fun t' ht' => hu t' ((S.isT_iff t').mp ht')⟩

end Main

end Formalism.L2.FormalSeriesBounds
