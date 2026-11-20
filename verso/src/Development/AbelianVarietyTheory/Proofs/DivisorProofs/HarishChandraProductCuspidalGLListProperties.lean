import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLAssocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnitStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.ListProd

variable {F : Type} [Field F]

/- English proof (translation)
Simplify using `[deg]`.
-/
theorem deg_cons' (p : ℕ × ℕ) (L : List (ℕ × ℕ)) : deg (p :: L) = p.1 + deg L := by
  simp [deg]

/- English proof (translation)
Simplify using `[deg]`.
-/
theorem deg_append' (L L' : List (ℕ × ℕ)) : deg (L ++ L') = deg L + deg L' := by
  simp [deg]

/- English proof (translation)
The claim follows from `(h.map Prod.fst).sum_eq`.
-/
theorem deg_perm' {L L' : List (ℕ × ℕ)} (h : L.Perm L') : deg L = deg L' :=
  (h.map Prod.fst).sum_eq

/- English proof (translation)
Substitute `hb` using the available equality. Both sides reduce to the same expression.
-/
theorem hc_congr_right (a b b' : ℕ) (hb : b = b') (α : GL (Fin a) F → ℂ)
    (β : (m : ℕ) → GL (Fin m) F → ℂ) (n : ℕ) :
    hc a b α (β b) n = hc a b' α (β b') n := by
  subst hb
  rfl

/- English proof (translation)
Substitute `ha` using the available equality. Both sides reduce to the same expression.
-/
theorem hc_congr_left (a a' b : ℕ) (ha : a = a') (α : (m : ℕ) → GL (Fin m) F → ℂ)
    (β : GL (Fin b) F → ℂ) (n : ℕ) :
    hc a b (α a) β n = hc a' b (α a') β n := by
  subst ha
  rfl

variable [Finite F]

/- English proof (translation)
Establish `h` using `((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 m (fun _ => 0) (fun _ => 0)).2.2 (rootSum θ k)).1`. Introduce `x y`. Simplify using `only [cusp]`. Rewrite using `[h x y]`.
-/
theorem isCl_cusp (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) : IsCl (cusp θ m k) := by

  have h := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 m (fun _ => 0) (fun _ => 0)).2.2 (rootSum θ k)).1
  intro x y
  simp only [cusp]
  rw [h x y]

/- English proof (translation)
Consider the cases of `L with`. Consider the case `nil`. Rewrite using `[J_nil]`. Introduce `x y`. Both sides reduce to the same expression.

Consider the case `cons p L`. Rewrite using `[J_cons]`. Conclude with `(GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1`.
-/
theorem isCl_J (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) (n : ℕ) : IsCl (J θ L n) := by
  cases L with
  | nil =>
    rw [J_nil]
    intro x y
    rfl
  | cons p L =>
    rw [J_cons]
    exact (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) _ _ n _ _).2.1

/- English proof (translation)
Proceed by induction on `L generalizing n with`. Consider the case `nil`. Establish `h0 : deg ([] : List (ℕ × ℕ)) = 0` using `rfl`. Establish `hn' : n = deg L'` using `by rw [hn, h0, Nat.zero_add]`. Substitute `hn'` using the available equality.

Express the relevant statement in the definitionally equal form `J θ L' (deg L') = hc 0 (deg L') (J θ [] 0) (J θ L' (deg L')) (deg L')`. Rewrite using `[J_nil]`. Conclude with `((GlobalTheory.T.harishChandraInductionGL_one_left_right_unit F (deg L') (J θ L' (deg L')) (isCl_J θ L' _)).1).symm`. Consider the case `cons p L ih`. Rewrite using `[List.cons_append, J_cons, ih (deg (L ++ L')) (deg_append' L L'), J_cons]`.

Use `(hc_congr_right p.1 _ _ (deg_append' L L') (cusp θ p.1 p.2) (fun m => hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) m) n).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (hc_congr_left _ _ (deg L') (deg_cons' p L).symm (fun m => hc p.1 (deg L) (cusp θ p.1 p.2) (J θ L (deg L)) m) (J θ L' (deg L')) n)` and prove the remaining obligations. Establish `hn' : n = p.1 + deg L + deg L'` using `by rw [hn, deg_cons']`. Conclude with `(GlobalTheory.T.harishChandraInductionGL_assoc F p.1 (deg L) (deg L') n (cusp θ p.1 p.2) (J θ L (deg L)) (J θ L' (deg L')) (isCl_cusp θ _ _) (isCl_J θ L _) (isCl_J θ L' _) hn').symm`.
-/
theorem J_append (θ : AlgebraicClosure F →* ℂ) (L L' : List (ℕ × ℕ)) (n : ℕ) (hn : n = deg L + deg L') :
    J θ (L ++ L') n = hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) n := by
  induction L generalizing n with
  | nil =>

    have h0 : deg ([] : List (ℕ × ℕ)) = 0 := rfl
    have hn' : n = deg L' := by rw [hn, h0, Nat.zero_add]
    subst hn'
    change J θ L' (deg L') = hc 0 (deg L') (J θ [] 0) (J θ L' (deg L')) (deg L')
    rw [J_nil]
    exact ((GlobalTheory.T.harishChandraInductionGL_one_left_right_unit F (deg L') (J θ L' (deg L')) (isCl_J θ L' _)).1).symm
  | cons p L ih =>

    rw [List.cons_append, J_cons, ih (deg (L ++ L')) (deg_append' L L'), J_cons]
    refine (hc_congr_right p.1 _ _ (deg_append' L L') (cusp θ p.1 p.2)
      (fun m => hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) m) n).trans ?_
    refine Eq.trans ?_ (hc_congr_left _ _ (deg L') (deg_cons' p L).symm
      (fun m => hc p.1 (deg L) (cusp θ p.1 p.2) (J θ L (deg L)) m) (J θ L' (deg L')) n)
    have hn' : n = p.1 + deg L + deg L' := by rw [hn, deg_cons']
    exact (GlobalTheory.T.harishChandraInductionGL_assoc F p.1 (deg L) (deg L') n (cusp θ p.1 p.2) (J θ L (deg L)) (J θ L' (deg L'))
      (isCl_cusp θ _ _) (isCl_J θ L _) (isCl_J θ L' _) hn').symm

/- English proof (translation)
Use `revert n`. Proceed by induction on `h with`. Consider the case `nil => intro n _`. Both sides reduce to the same expression. Consider the case `cons p h ih`.

Name the introduced variables `l₁ l₂`. Introduce `n _`. Rewrite using `[J_cons, J_cons, ih (deg l₁) rfl]`. Conclude with `hc_congr_right p.1 _ _ (deg_perm' h) (cusp θ p.1 p.2) (J θ l₂) n`. Consider the case `swap q p l`.

Introduce `n hn`. Rewrite using `[J_cons, J_cons, J_cons, J_cons]`. Establish `hcp` using `isCl_cusp θ p.1 p.2`. Establish `hcq` using `isCl_cusp θ q.1 q.2`. Establish `hl` using `isCl_J θ l (deg l)`.

Establish `e1 : n = p.1 + q.1 + deg l` using `by rw [hn, deg_cons', deg_cons', Nat.add_assoc]`. Establish `e2 : n = q.1 + p.1 + deg l` using `by rw [e1, Nat.add_comm p.1 q.1]`. Use `(hc_congr_right p.1 _ _ (deg_cons' q l) (cusp θ p.1 p.2) (fun m => hc q.1 (deg l) (cusp θ q.1 q.2) (J θ l (deg l)) m) n).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (hc_congr_right q.1 _ _ (deg_cons' p l).symm (cusp θ q.1 q.2) (fun m => hc p.1 (deg l) (cusp θ p.1 p.2) (J θ l (deg l)) m) n)` and prove the remaining obligations. Rewrite using `[← GlobalTheory.T.harishChandraInductionGL_assoc F p.1 q.1 (deg l) n _ _ _ hcp hcq hl e1, ← GlobalTheory.T.harishChandraInductionGL_assoc F q.1 p.1 (deg l) n _ _ _ hcq hcp hl e2, GlobalTheory.T.harishChandraInductionGL_comm F p.1 q.1 (p.1 + q.1) _ _ hcp hcq rfl]`.

Conclude with `hc_congr_left _ _ (deg l) (Nat.add_comm p.1 q.1) (fun m => hc q.1 p.1 (cusp θ q.1 q.2) (cusp θ p.1 p.2) m) (J θ l (deg l)) n`. Consider the case `trans h₁ _ ih₁ ih₂`. Introduce `n hn`. Conclude with `(ih₁ n hn).trans (ih₂ n (hn.trans (deg_perm' h₁)))`.
-/
theorem J_perm (θ : AlgebraicClosure F →* ℂ) (L L' : List (ℕ × ℕ)) (n : ℕ) (hn : n = deg L) (h : L.Perm L') :
    J θ L n = J θ L' n := by
  revert n
  induction h with
  | nil => intro n _; rfl
  | cons p h ih =>
    rename_i l₁ l₂
    intro n _
    rw [J_cons, J_cons, ih (deg l₁) rfl]
    exact hc_congr_right p.1 _ _ (deg_perm' h) (cusp θ p.1 p.2) (J θ l₂) n
  | swap q p l =>

    intro n hn
    rw [J_cons, J_cons, J_cons, J_cons]
    have hcp := isCl_cusp θ p.1 p.2
    have hcq := isCl_cusp θ q.1 q.2
    have hl := isCl_J θ l (deg l)
    have e1 : n = p.1 + q.1 + deg l := by rw [hn, deg_cons', deg_cons', Nat.add_assoc]
    have e2 : n = q.1 + p.1 + deg l := by rw [e1, Nat.add_comm p.1 q.1]
    refine (hc_congr_right p.1 _ _ (deg_cons' q l) (cusp θ p.1 p.2)
      (fun m => hc q.1 (deg l) (cusp θ q.1 q.2) (J θ l (deg l)) m) n).trans ?_
    refine Eq.trans ?_ (hc_congr_right q.1 _ _ (deg_cons' p l).symm (cusp θ q.1 q.2)
      (fun m => hc p.1 (deg l) (cusp θ p.1 p.2) (J θ l (deg l)) m) n)
    rw [← GlobalTheory.T.harishChandraInductionGL_assoc F p.1 q.1 (deg l) n _ _ _ hcp hcq hl e1,
      ← GlobalTheory.T.harishChandraInductionGL_assoc F q.1 p.1 (deg l) n _ _ _ hcq hcp hl e2,
      GlobalTheory.T.harishChandraInductionGL_comm F p.1 q.1 (p.1 + q.1) _ _ hcp hcq rfl]
    exact hc_congr_left _ _ (deg l) (Nat.add_comm p.1 q.1)
      (fun m => hc q.1 p.1 (cusp θ q.1 q.2) (cusp θ p.1 p.2) m) (J θ l (deg l)) n
  | trans h₁ _ ih₁ ih₂ =>
    intro n hn
    exact (ih₁ n hn).trans (ih₂ n (hn.trans (deg_perm' h₁)))

end GlobalTheory.Shin.ListProd

open GlobalTheory.Shin.ListProd in

/- English proof (translation)
Introduce `F _ _ θ`. Conclude with `⟨fun L n => isCl_J θ L n, fun L L' n hn => J_append θ L L' n hn, fun L L' n hn h => J_perm θ L L' n hn h⟩`.
-/
theorem GlobalTheory.Shin.J_list_props : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ L n, IsCl (J θ L n)) ∧
    (∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L + deg L' →
      J θ (L ++ L') n = hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) n) ∧
    ∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L → L.Perm L' → J θ L n = J θ L' n := by
  intro F _ _ θ
  exact ⟨fun L n => isCl_J θ L n, fun L L' n hn => J_append θ L L' n hn,
    fun L L' n hn h => J_perm θ L L' n hn h⟩
