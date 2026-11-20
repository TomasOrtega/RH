import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnRel

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Simplify using `only [Cas, two_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `noncomm_ring`.
-/
private theorem UpperTheory.RealTr.casPK {n : ℕ} {A : Type} [Ring A] (E1 E2 : Fin n → Fin n → A) :
    Cas (fun a b => E1 a b - E2 a b) + Cas (fun a b => E1 a b + E2 a b) = 2 * (Cas E1 + Cas E2) := by
  simp only [Cas, two_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  noncomm_ring

/- English proof (translation)
Establish `h1 : ∑ a, ∑ b, s a b * K b a = ∑ a, ∑ b, K a b * s b a`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (h a b b a).symm`. Establish `h2 : Cas (fun a b => K a b + s a b) = Cas K + Cas s + (∑ a, ∑ b, K a b * s b a + ∑ a, ∑ b, s a b * K b a)`. Simplify using `only [Cas, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `noncomm_ring`. Rewrite using `[h2, h1, two_mul]`.
-/
private theorem UpperTheory.RealTr.casAdd {n : ℕ} {A : Type} [Ring A] (K s : Fin n → Fin n → A)
    (h : ∀ a b d e, K a b * s d e = s d e * K a b) :
    Cas (fun a b => K a b + s a b) = Cas K + Cas s + 2 * ∑ a, ∑ b, K a b * s b a := by
  have h1 : ∑ a, ∑ b, s a b * K b a = ∑ a, ∑ b, K a b * s b a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (h a b b a).symm
  have h2 : Cas (fun a b => K a b + s a b) =
      Cas K + Cas s + (∑ a, ∑ b, K a b * s b a + ∑ a, ∑ b, s a b * K b a) := by
    simp only [Cas, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    noncomm_ring
  rw [h2, h1, two_mul]

/- English proof (translation)
Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.
-/
private theorem UpperTheory.RealTr.dd1 {n : ℕ} {A : Type} [Ring A] (u : Fin n → Fin n → A) :
    (∑ a, ∑ b, u a b) * (∑ a, ∑ b, u a b) = ∑ a, ∑ b, ∑ d, ∑ e, u a b * u d e := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.
-/
private theorem UpperTheory.RealTr.dd2 {n : ℕ} {A : Type} [Ring A] (u : Fin n → Fin n → A) :
    (∑ a, ∑ b, u a b) * (∑ a, ∑ b, u a b) = ∑ a, ∑ b, ∑ d, ∑ e, u d e * u a b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private theorem UpperTheory.RealTr.sum3 {n : ℕ} {A : Type} [AddCommMonoid A] (g : Fin n → Fin n → Fin n → A) :
    ∑ a, ∑ b, ∑ d, g a b d = ∑ d, ∑ b, ∑ a, g a b d := by
  calc ∑ a, ∑ b, ∑ d, g a b d = ∑ a, ∑ d, ∑ b, g a b d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, g a b d := Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ a, g a b d := Finset.sum_congr rfl fun d _ => Finset.sum_comm

/- English proof (translation)
Simplify using `only [spn, sub_add_cancel]`.
-/
private theorem UpperTheory.RealTr.sumSpn {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (x y : Fin n) :
    ∑ z, c x z * c z y = spn c x y + if x = y then algebraMap ℂ A ((n : ℂ) / 2) else 0 := by
  simp only [spn, sub_add_cancel]

/- English proof (translation)
Rewrite using `[← UpperTheory.RealTr.sumSpn, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]`. Establish `h : ∀ z, c z x * c y z + c y z * c z x = if x = y then 1 else 0`. Introduce `z`. Rewrite using `[hc z x y z]`. Simplify using the standard rewrite rules.

Simplify using `only [h]`. Apply the tactic sequence `by_cases hxy : x = y <;> simp [hxy]`.
-/
private theorem UpperTheory.RealTr.sumSwap {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (hc : Clif c) (x y : Fin n) :
    ∑ z, c z x * c y z = (if x = y then (n : A) else 0) -
      (spn c y x + if y = x then algebraMap ℂ A ((n : ℂ) / 2) else 0) := by
  rw [← UpperTheory.RealTr.sumSpn, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  have h : ∀ z, c z x * c y z + c y z * c z x = if x = y then 1 else 0 := by
    intro z
    rw [hc z x y z]
    simp
  simp only [h]
  by_cases hxy : x = y <;> simp [hxy]

/- English proof (translation)
Establish `hmul : ∀ a b d e, (P a b * c b a) * (P d e * c e d) = P a b * P d e * (c b a * c e d)`. Introduce `a b d e`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = P a b * (P d e * c b a) * c e d := by rw [hPc d e b a]`.

Use `_ = _ := by simp only [mul_assoc]`. Establish `hpt : ∀ a b d e, (P a b * c b a) * (P d e * c e d) + (P d e * c e d) * (P a b * c b a) = (if a = e then (if b = d then P a b * P d e else 0) else 0) - (if b = d then K a e * (c e d * c b a) else 0) + (if e = a then K d b * (c e d * c b a) else 0)`. Introduce `a b d e`. Establish `h1` using `hc b a e d`. Establish `h3 : P d e * P a b = P a b * P d e - ((if b = d then K a e else 0) - (if e = a then K d b else 0))`.

Rewrite using `[← hPP a b d e]`. Normalize the expressions using the abelian group laws. Establish `h4 : P a b * P d e * (c b a * c e d) + P d e * P a b * (c e d * c b a) = P a b * P d e * (c b a * c e d + c e d * c b a) - ((if b = d then K a e else 0) - (if e = a then K d b else 0)) * (c e d * c b a)`. Rewrite using `[h3, sub_mul, mul_add]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hmul, hmul, h4, h1]`. Apply the tactic sequence `by_cases hae : a = e <;> by_cases hbd : b = d <;> simp [hae, hbd, sub_mul, eq_comm] <;> abel`. Establish `hS1 : ∑ a, ∑ b, ∑ d, ∑ e, (if a = e then (if b = d then P a b * P d e else 0) else 0) = Cas P`. Simplify using `[Cas, Finset.sum_ite_eq]`. Establish `hS2 : ∑ a, ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0) = ∑ a, ∑ b, K a b * (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0)`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Simplify using the standard rewrite rules.

Use `_ = ∑ e, ∑ b, K a e * (c e b * c b a) := Finset.sum_comm`. Use `_ = _ := by`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, UpperTheory.RealTr.sumSpn]`. Establish `hS3 : ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0) = ∑ a, ∑ b, K a b * ((if a = b then (n : A) else 0) - (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0))`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, UpperTheory.RealTr.sumSwap c hc]`. Establish `hhalf : algebraMap ℂ A ((n : ℂ) / 2) + algebraMap ℂ A ((n : ℂ) / 2) = (n : A)`. Rewrite using `[← map_add, add_halves, map_natCast]`.

Establish `hfin : ∑ a, ∑ b, K a b * (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) - ∑ a, ∑ b, K a b * ((if a = b then (n : A) else 0) - (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0)) = 2 * ∑ a, ∑ b, K a b * spn c b a`. Simplify using `only [Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hi : (if a = b then (n : A) else 0) = (if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) + (if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0)`. Distinguish the cases in `hab : a = b`.

Simplify using `[hab, hhalf]`. Simplify using `[hab, Ne.symm hab]`. Rewrite using `[hi]`. Use `noncomm_ring`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[UpperTheory.RealTr.dd2 (fun a b => P a b * c b a)]`. Simplify using `only [Finset.sum_add_distrib]`. Use `_ = ∑ a, ∑ b, ∑ d, ∑ e, (if a = e then (if b = d then P a b * P d e else 0) else 0) - ∑ a, ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0) + ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0) := by`. Simplify using `only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Use `_ = _ := by`.

Rewrite using `[hS1, hS2, hS3, ← hfin]`. Normalize the expressions using the abelian group laws.
-/
private theorem UpperTheory.RealTr.dCore {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]
    (P K c : Fin n → Fin n → A)
    (hPP : ∀ a b d e, P a b * P d e - P d e * P a b =
      (if b = d then K a e else 0) - (if e = a then K d b else 0))
    (hPc : ∀ a b d e, P a b * c d e = c d e * P a b)
    (hc : Clif c) :
    2 * ((∑ a, ∑ b, P a b * c b a) * ∑ a, ∑ b, P a b * c b a) =
      Cas P - 2 * ∑ a, ∑ b, K a b * spn c b a := by
  have hmul : ∀ a b d e, (P a b * c b a) * (P d e * c e d) = P a b * P d e * (c b a * c e d) := by
    intro a b d e
    calc P a b * c b a * (P d e * c e d) = P a b * (c b a * P d e) * c e d := by
          simp only [mul_assoc]
      _ = P a b * (P d e * c b a) * c e d := by rw [hPc d e b a]
      _ = _ := by simp only [mul_assoc]
  have hpt : ∀ a b d e, (P a b * c b a) * (P d e * c e d) + (P d e * c e d) * (P a b * c b a) =
      (if a = e then (if b = d then P a b * P d e else 0) else 0)
      - (if b = d then K a e * (c e d * c b a) else 0)
      + (if e = a then K d b * (c e d * c b a) else 0) := by
    intro a b d e
    have h1 := hc b a e d
    have h3 : P d e * P a b = P a b * P d e -
        ((if b = d then K a e else 0) - (if e = a then K d b else 0)) := by
      rw [← hPP a b d e]; abel
    have h4 : P a b * P d e * (c b a * c e d) + P d e * P a b * (c e d * c b a) =
        P a b * P d e * (c b a * c e d + c e d * c b a) -
          ((if b = d then K a e else 0) - (if e = a then K d b else 0)) * (c e d * c b a) := by
      rw [h3, sub_mul, mul_add]; abel
    rw [hmul, hmul, h4, h1]
    by_cases hae : a = e <;> by_cases hbd : b = d <;> simp [hae, hbd, sub_mul, eq_comm] <;> abel
  have hS1 : ∑ a, ∑ b, ∑ d, ∑ e, (if a = e then (if b = d then P a b * P d e else 0) else 0) = Cas P := by
    simp [Cas, Finset.sum_ite_eq]
  have hS2 : ∑ a, ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0) =
      ∑ a, ∑ b, K a b * (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0)
        = ∑ b, ∑ e, K a e * (c e b * c b a) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          simp
      _ = ∑ e, ∑ b, K a e * (c e b * c b a) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.mul_sum, UpperTheory.RealTr.sumSpn]
  have hS3 : ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0) =
      ∑ a, ∑ b, K a b * ((if a = b then (n : A) else 0) -
        (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0)) := by
    calc ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0)
        = ∑ a, ∑ b, ∑ d, K d b * (c a d * c b a) := by simp
      _ = ∑ d, ∑ b, ∑ a, K d b * (c a d * c b a) := UpperTheory.RealTr.sum3 _
      _ = _ := by
          refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.mul_sum, UpperTheory.RealTr.sumSwap c hc]
  have hhalf : algebraMap ℂ A ((n : ℂ) / 2) + algebraMap ℂ A ((n : ℂ) / 2) = (n : A) := by
    rw [← map_add, add_halves, map_natCast]
  have hfin : ∑ a, ∑ b, K a b * (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) -
      ∑ a, ∑ b, K a b * ((if a = b then (n : A) else 0) -
        (spn c b a + if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0)) =
      2 * ∑ a, ∑ b, K a b * spn c b a := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hi : (if a = b then (n : A) else 0) =
        (if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) +
          (if b = a then algebraMap ℂ A ((n : ℂ) / 2) else 0) := by
      by_cases hab : a = b
      · simp [hab, hhalf]
      · simp [hab, Ne.symm hab]
    rw [hi]
    noncomm_ring
  calc 2 * ((∑ a, ∑ b, P a b * c b a) * ∑ a, ∑ b, P a b * c b a)
      = (∑ a, ∑ b, P a b * c b a) * (∑ a, ∑ b, P a b * c b a) +
        (∑ a, ∑ b, P a b * c b a) * (∑ a, ∑ b, P a b * c b a) := two_mul _
    _ = ∑ a, ∑ b, ∑ d, ∑ e, ((P a b * c b a) * (P d e * c e d) + (P d e * c e d) * (P a b * c b a)) := by
        nth_rewrite 1 [UpperTheory.RealTr.dd1 (fun a b => P a b * c b a)]
        rw [UpperTheory.RealTr.dd2 (fun a b => P a b * c b a)]
        simp only [Finset.sum_add_distrib]
    _ = ∑ a, ∑ b, ∑ d, ∑ e, (if a = e then (if b = d then P a b * P d e else 0) else 0)
        - ∑ a, ∑ b, ∑ d, ∑ e, (if b = d then K a e * (c e d * c b a) else 0)
        + ∑ a, ∑ b, ∑ d, ∑ e, (if e = a then K d b * (c e d * c b a) else 0) := by
        simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
        rw [hS1, hS2, hS3, ← hfin]; abel

/- English proof (translation)
Establish `h' : Commute x (spn c a b)`. Unfold `spn`. Use `Commute.sub_right (Commute.sum_right _ _ _ fun d _ => Commute.mul_right (h _ _) (h _ _)) ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `Algebra.commutes _ _ |>.symm`.

Conclude with `Commute.zero_right _`. Conclude with `h'`.
-/
private theorem UpperTheory.RealTr.commSpn {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (x : A) (h : ∀ d e, x * c d e = c d e * x) (a b : Fin n) : x * spn c a b = spn c a b * x := by
  have h' : Commute x (spn c a b) := by
    unfold spn
    refine Commute.sub_right (Commute.sum_right _ _ _ fun d _ => Commute.mul_right (h _ _) (h _ _)) ?_
    split_ifs
    · exact Algebra.commutes _ _ |>.symm
    · exact Commute.zero_right _
  exact h'

/- English proof (translation)
Introduce `n A _ _ E1 E2 c h1 h2 h12 hc hEc`. Establish `hPP : ∀ a b d e, (E1 a b - E2 a b) * (E1 d e - E2 d e) - (E1 d e - E2 d e) * (E1 a b - E2 a b) = (if b = d then E1 a e + E2 a e else 0) - (if e = a then E1 d b + E2 d b else 0)`. Introduce `a b d e`. Establish `h : (E1 a b - E2 a b) * (E1 d e - E2 d e) - (E1 d e - E2 d e) * (E1 a b - E2 a b) = (E1 a b * E1 d e - E1 d e * E1 a b) + (E2 a b * E2 d e - E2 d e * E2 a b)`. Simplify using `only [sub_mul, mul_sub, h12 a b d e, h12 d e a b]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h, h1 a b d e, h2 a b d e]`. Apply the tactic sequence `split_ifs <;> abel`. Establish `hPc : ∀ a b d e, (E1 a b - E2 a b) * c d e = c d e * (E1 a b - E2 a b)`. Introduce `a b d e`.

Rewrite using `[sub_mul, mul_sub, (hEc a b d e).1, (hEc a b d e).2]`. Establish `hK : ∀ a b d e, (E1 a b + E2 a b) * spn c d e = spn c d e * (E1 a b + E2 a b)`. Introduce `a b d e`. Use `UpperTheory.RealTr.commSpn c _ (fun d e => ?_) d e` and prove the remaining obligations. Rewrite using `[add_mul, mul_add, (hEc a b d e).1, (hEc a b d e).2]`.

Establish `e1 : Cas (fun a b => E1 a b + E2 a b + spn c a b) = Cas (fun a b => E1 a b + E2 a b) + Cas (spn c) + 2 * ∑ a, ∑ b, (E1 a b + E2 a b) * spn c b a` using `UpperTheory.RealTr.casAdd (fun a b => E1 a b + E2 a b) (spn c) hK`. Rewrite using `[UpperTheory.RealTr.dCore (fun a b => E1 a b - E2 a b) (fun a b => E1 a b + E2 a b) c hPP hPc hc, e1, ← UpperTheory.RealTr.casPK E1 E2]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.RealTr.diracAlg :
    ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (E1 E2 c : Fin n → Fin n → A), GlRel E1 → GlRel E2 → (∀ a b d e, E1 a b * E2 d e = E2 d e * E1 a b) →
      Clif c → (∀ a b d e, E1 a b * c d e = c d e * E1 a b ∧ E2 a b * c d e = c d e * E2 a b) →
      2 * ((∑ a, ∑ b, (E1 a b - E2 a b) * c b a) * ∑ a, ∑ b, (E1 a b - E2 a b) * c b a) =
        2 * (Cas E1 + Cas E2) + Cas (spn c) - Cas fun a b => E1 a b + E2 a b + spn c a b := by
  intro n A _ _ E1 E2 c h1 h2 h12 hc hEc
  have hPP : ∀ a b d e, (E1 a b - E2 a b) * (E1 d e - E2 d e) - (E1 d e - E2 d e) * (E1 a b - E2 a b) =
      (if b = d then E1 a e + E2 a e else 0) - (if e = a then E1 d b + E2 d b else 0) := by
    intro a b d e
    have h : (E1 a b - E2 a b) * (E1 d e - E2 d e) - (E1 d e - E2 d e) * (E1 a b - E2 a b) =
        (E1 a b * E1 d e - E1 d e * E1 a b) + (E2 a b * E2 d e - E2 d e * E2 a b) := by
      simp only [sub_mul, mul_sub, h12 a b d e, h12 d e a b]
      abel
    rw [h, h1 a b d e, h2 a b d e]
    split_ifs <;> abel
  have hPc : ∀ a b d e, (E1 a b - E2 a b) * c d e = c d e * (E1 a b - E2 a b) := by
    intro a b d e
    rw [sub_mul, mul_sub, (hEc a b d e).1, (hEc a b d e).2]
  have hK : ∀ a b d e, (E1 a b + E2 a b) * spn c d e = spn c d e * (E1 a b + E2 a b) := by
    intro a b d e
    refine UpperTheory.RealTr.commSpn c _ (fun d e => ?_) d e
    rw [add_mul, mul_add, (hEc a b d e).1, (hEc a b d e).2]
  have e1 : Cas (fun a b => E1 a b + E2 a b + spn c a b) =
      Cas (fun a b => E1 a b + E2 a b) + Cas (spn c) +
        2 * ∑ a, ∑ b, (E1 a b + E2 a b) * spn c b a :=
    UpperTheory.RealTr.casAdd (fun a b => E1 a b + E2 a b) (spn c) hK
  rw [UpperTheory.RealTr.dCore (fun a b => E1 a b - E2 a b) (fun a b => E1 a b + E2 a b) c hPP hPc hc, e1,
    ← UpperTheory.RealTr.casPK E1 E2]
  abel
