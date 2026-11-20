import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans

set_option autoImplicit false

open CategoryTheory

universe v u

namespace GlobalTheory.CatH.DSq

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{0} R)

/- English proof (translation)
Establish `h : (i.succAbove k : ℕ) + (k.predAbove i : ℕ) + 1 = (i : ℕ) + (k : ℕ) ∨ (i.succAbove k : ℕ) + (k.predAbove i : ℕ) = (i : ℕ) + (k : ℕ) + 1`. Simplify using `only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val, Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[← pow_add, ← pow_add]`. Break down `h with h | h` into its components or cases.

Rewrite using `[← h, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sign_swap {q : ℕ} (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (-1 : ℤ) ^ (i.succAbove k : ℕ) * (-1) ^ (k.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (k : ℕ)) := by
  have h : (i.succAbove k : ℕ) + (k.predAbove i : ℕ) + 1 = (i : ℕ) + (k : ℕ) ∨
      (i.succAbove k : ℕ) + (k.predAbove i : ℕ) = (i : ℕ) + (k : ℕ) + 1 := by
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val, Fin.val_pred,
      Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
    split_ifs <;> omega
  rw [← pow_add, ← pow_add]
  rcases h with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

noncomputable def term {n : ℕ} (s : ComposableArrows C (n + 2)) (f : Cn F n) (g : Fin (n + 1) → Fin (n + 3))
    (hg : Monotone g) : F.obj (s.obj (Fin.last (n + 2))) :=
  (F.map (s.map (homOfLE (Fin.le_last (g (Fin.last n)))))).hom (f (hg.functor ⋙ s))

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem term_congr {n : ℕ} (s : ComposableArrows C (n + 2)) (f : Cn F n) {g g' : Fin (n + 1) → Fin (n + 3)}
    (hg : Monotone g) (hg' : Monotone g') (h : g = g') : term F s f g hg = term F s f g' hg' := by
  subst h; rfl

/- English proof (translation)
Establish `e : toLast i (face j s) ≫ toLast j s = s.map (homOfLE (Fin.le_last (j.succAbove (i.succAbove (Fin.last n)))))`. Express the relevant statement in the definitionally equal form `s.map _ ≫ s.map _ = _`. Rewrite using `[← s.map_comp]`. Both sides reduce to the same expression. Rewrite using `[← ModuleCat.comp_apply, ← F.map_comp, e]`.

Both sides reduce to the same expression.
-/
theorem face_face_apply {n : ℕ} (s : ComposableArrows C (n + 2)) (f : Cn F n) (j : Fin (n + 3)) (i : Fin (n + 2)) :
    (F.map (toLast j s)).hom ((F.map (toLast i (face j s))).hom (f (face i (face j s)))) =
      term F s f (j.succAbove ∘ i.succAbove)
        ((Fin.strictMono_succAbove j).monotone.comp (Fin.strictMono_succAbove i).monotone) := by
  have e : toLast i (face j s) ≫ toLast j s =
      s.map (homOfLE (Fin.le_last (j.succAbove (i.succAbove (Fin.last n))))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [← ModuleCat.comp_apply, ← F.map_comp, e]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) • (F.map (toLast j s)).hom (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i (face j s))).hom (f (face i (face j s)))) = 0`. Simplify using `only [map_sum, map_zsmul, Finset.smul_sum, smul_smul, face_face_apply]`. Rewrite using `[← Fintype.sum_prod_type']`. Use `Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce and unpack `⟨j, i⟩ _ dsimp only`. Establish `e : ((j.succAbove i).succAbove ∘ (i.predAbove j).succAbove) = j.succAbove ∘ i.succAbove`. Use function extensionality and compare the values at `fun t => Fin.succAbove_succAbove_succAbove_predAbove j i t`. Rewrite using `[term_congr F s f _ ((Fin.strictMono_succAbove j).monotone.comp (Fin.strictMono_succAbove i).monotone) e, sign_swap, neg_smul, add_neg_cancel]`. Introduce and unpack `⟨j, i⟩ _ _ h`.

Conclude with `Fin.succAbove_ne j i (congrArg Prod.fst h)`. Introduce `_ _`. Conclude with `Finset.mem_univ _`. Introduce and unpack `⟨j, i⟩ _`. Simplify using `only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]`.
-/
theorem d_d {n : ℕ} (f : Cn F n) : d F (n + 1) (d F n f) = 0 := by
  funext s
  change ∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) • (F.map (toLast j s)).hom
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i (face j s))).hom (f (face i (face j s)))) = 0
  simp only [map_sum, map_zsmul, Finset.smul_sum, smul_smul, face_face_apply]
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    dsimp only
    have e : ((j.succAbove i).succAbove ∘ (i.predAbove j).succAbove) = j.succAbove ∘ i.succAbove :=
      funext fun t => Fin.succAbove_succAbove_succAbove_predAbove j i t
    rw [term_congr F s f _ ((Fin.strictMono_succAbove j).monotone.comp (Fin.strictMono_succAbove i).monotone) e,
      sign_swap, neg_smul, add_neg_cancel]
  · rintro ⟨j, i⟩ _ _ h
    exact Fin.succAbove_ne j i (congrArg Prod.fst h)
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨j, i⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

end GlobalTheory.CatH.DSq
