import Development.EtaleCohomology.EtaleSheaves.AdjoinRootExtension.AdjoinRootOfInjective
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Polynomial

namespace LateralTheory.E.AICExtPf

def towerObj (C : CommRingCat.{0}) : ℕ → CommRingCat.{0}
  | 0 => C
  | n + 1 => CommRingCat.of (StepRing (towerObj C n))

def towerMap (C : CommRingCat.{0}) (n : ℕ) : towerObj C n ⟶ towerObj C (n + 1) :=
  CommRingCat.ofHom (stepHom (towerObj C n))

abbrev towerF (C : CommRingCat.{0}) : ℕ ⥤ CommRingCat.{0} := Functor.ofSequence (towerMap C)

def fm (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : towerObj C i →+* towerObj C j :=
  ((towerF C).map (homOfLE h)).hom

instance (C : CommRingCat.{0}) :
    DirectedSystem (fun i => (towerObj C i : Type)) (fun i j h => fm C i j h) where
  map_self i x := by
    have h1 : (towerF C).map (homOfLE (le_refl i)) = 𝟙 _ :=
      (congrArg (towerF C).map (Subsingleton.elim _ _)).trans ((towerF C).map_id i)
    exact congrArg (fun φ : (towerF C).obj i ⟶ (towerF C).obj i => φ.hom x) h1
  map_map k j i hij hjk x := by
    show ((towerF C).map (homOfLE hij) ≫ (towerF C).map (homOfLE hjk)).hom x = _
    rw [← Functor.map_comp, homOfLE_comp]; rfl

/- English proof (translation)
Use `Functor.ofSequence_map_homOfLE_succ (towerMap C) n` as an intermediate fact. Simplify using `only [fm]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
lemma fm_succ (C : CommRingCat.{0}) (n : ℕ) (h : n ≤ n + 1) : fm C n (n + 1) h = stepHom (towerObj C n) := by
  have := Functor.ofSequence_map_homOfLE_succ (towerMap C) n
  simp only [fm]
  rw [this]; rfl

/- English proof (translation)
Rewrite using `[← fm_succ C j (Nat.le_succ j)]`. Use `show ((towerF C).map (homOfLE h')).hom = ((towerF C).map (homOfLE h) ≫ (towerF C).map (homOfLE (Nat.le_succ j))).hom`. Rewrite using `[← Functor.map_comp, homOfLE_comp]`.
-/
lemma fm_comp_succ (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) (h' : i ≤ j + 1) :
    fm C i (j + 1) h' = (stepHom (towerObj C j)).comp (fm C i j h) := by
  rw [← fm_succ C j (Nat.le_succ j)]
  show ((towerF C).map (homOfLE h')).hom =
    ((towerF C).map (homOfLE h) ≫ (towerF C).map (homOfLE (Nat.le_succ j))).hom
  rw [← Functor.map_comp, homOfLE_comp]

/- English proof (translation)
Proceed by induction on `j, h using Nat.le_induction with`. Consider the case `base => intro x y hxy`. Simplify `hxy` using `[DirectedSystem.map_self (f := fun i j h => fm C i j h)]`. Consider the case `succ j hij ih`. Rewrite using `[fm_comp_succ C i j hij]`.

Conclude with `(stepHom_injective _).comp ih`.
-/
lemma fm_injective (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : Function.Injective (fm C i j h) := by
  induction j, h using Nat.le_induction with
  | base => intro x y hxy; simpa [DirectedSystem.map_self (f := fun i j h => fm C i j h)] using hxy
  | succ j hij ih =>
    rw [fm_comp_succ C i j hij]
    exact (stepHom_injective _).comp ih

/- English proof (translation)
Proceed by induction on `j, h using Nat.le_induction with`. Consider the case `base`. Introduce `x`. Establish `e : ∀ y, fm C i i le_rfl y = y` using `fun y => DirectedSystem.map_self (f := fun i j h => fm C i j h) y`. Conclude with `⟨X - Polynomial.C x, monic_X_sub_C x, by simp [eval₂_sub, e]⟩`.

Consider the case `succ j hij ih`. Rewrite using `[fm_comp_succ C i j hij]`. Conclude with `RingHom.IsIntegral.trans _ _ ih (stepHom_isIntegral _)`.
-/
lemma fm_isIntegral (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : (fm C i j h).IsIntegral := by
  induction j, h using Nat.le_induction with
  | base =>
    intro x
    have e : ∀ y, fm C i i le_rfl y = y := fun y => DirectedSystem.map_self (f := fun i j h => fm C i j h) y
    exact ⟨X - Polynomial.C x, monic_X_sub_C x, by simp [eval₂_sub, e]⟩
  | succ j hij ih =>
    rw [fm_comp_succ C i j hij]
    exact RingHom.IsIntegral.trans _ _ ih (stepHom_isIntegral _)

abbrev Lim (C : CommRingCat.{0}) : Type :=
  Ring.DirectLimit (fun i => (towerObj C i : Type)) (fun i j h => fm C i j h)

/- English proof (translation)
Use extensionality with `x`. Conclude with `Ring.DirectLimit.of_f (G := fun i => (towerObj C i : Type)) (f := fun i j h => fm C i j h) h x`.
-/
lemma of_comp (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) :
    (Ring.DirectLimit.of _ (fun i j h => fm C i j h) j).comp (fm C i j h) =
      Ring.DirectLimit.of _ (fun i j h => fm C i j h) i := by
  ext x
  exact Ring.DirectLimit.of_f (G := fun i => (towerObj C i : Type)) (f := fun i j h => fm C i j h) h x

/- English proof (translation)
Introduce `p hp hd`. Take `⟨n, q, hq⟩` from `Ring.DirectLimit.Polynomial.exists_of p`. Establish `hinj` using `Ring.DirectLimit.of_injective (fun i j h => fm C i j h) (fm_injective C) n`. Establish `hqm : q.Monic`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← leadingCoeff_map_of_injective hinj, hq, hp.leadingCoeff, map_one]`. Establish `hqd : 0 < q.natDegree`. Rewrite using `[← natDegree_map_eq_of_injective hinj, hq]`. Conclude with `hd`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha'⟩ : ∃ a : towerObj C (n + 1), (q.map (fm C n (n + 1) (Nat.le_succ n))).eval a = 0 := by`.

Rewrite using `[fm_succ]`. Conclude with `step_has_root (towerObj C n) q hqm hqd`. Use `⟨Ring.DirectLimit.of _ (fun i j h => fm C i j h) (n + 1) a, ?_⟩` and prove the remaining obligations. Rewrite using `[← hq, ← of_comp C n (n + 1) (Nat.le_succ n), ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha', map_zero]`.
-/
theorem lim_aic (C : CommRingCat.{0}) : GlobalTheory.EtC.AIC (Lim C) := by
  intro p hp hd
  obtain ⟨n, q, hq⟩ := Ring.DirectLimit.Polynomial.exists_of p
  have hinj := Ring.DirectLimit.of_injective (fun i j h => fm C i j h) (fm_injective C) n
  have hqm : q.Monic := by
    apply hinj
    rw [← leadingCoeff_map_of_injective hinj, hq, hp.leadingCoeff, map_one]
  have hqd : 0 < q.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hq]; exact hd
  obtain ⟨a, ha'⟩ : ∃ a : towerObj C (n + 1), (q.map (fm C n (n + 1) (Nat.le_succ n))).eval a = 0 := by
    rw [fm_succ]; exact step_has_root (towerObj C n) q hqm hqd
  refine ⟨Ring.DirectLimit.of _ (fun i j h => fm C i j h) (n + 1) a, ?_⟩
  rw [← hq, ← of_comp C n (n + 1) (Nat.le_succ n), ← Polynomial.map_map, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, ha', map_zero]

/- English proof (translation)
Introduce `C`. Use `⟨CommRingCat.of (Lim C), CommRingCat.ofHom (Ring.DirectLimit.of _ (fun i j h => fm C i j h) 0), ?_, ?_, lim_aic C⟩` and prove the remaining obligations. Introduce `x`. Take `⟨n, y, rfl⟩` from `Ring.DirectLimit.exists_of x`. Take `⟨p, hp, hy⟩` from `fm_isIntegral C 0 n (Nat.zero_le n) y`.

Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `eval₂ (Ring.DirectLimit.of _ (fun i j h => fm C i j h) 0) _ p = 0`. Rewrite using `[← of_comp C 0 n (Nat.zero_le n), ← hom_eval₂, hy, map_zero]`. Conclude with `Ring.DirectLimit.of_injective (fun i j h => fm C i j h) (fm_injective C) 0`.
-/
theorem AICExt_of : LateralTheory.E.t_E3Cut.AICExt := by
  intro C
  refine ⟨CommRingCat.of (Lim C), CommRingCat.ofHom (Ring.DirectLimit.of _ (fun i j h => fm C i j h) 0),
    ?_, ?_, lim_aic C⟩
  · intro x
    obtain ⟨n, y, rfl⟩ := Ring.DirectLimit.exists_of x
    obtain ⟨p, hp, hy⟩ := fm_isIntegral C 0 n (Nat.zero_le n) y
    refine ⟨p, hp, ?_⟩
    change eval₂ (Ring.DirectLimit.of _ (fun i j h => fm C i j h) 0) _ p = 0
    rw [← of_comp C 0 n (Nat.zero_le n), ← hom_eval₂, hy, map_zero]
  · exact Ring.DirectLimit.of_injective (fun i j h => fm C i j h) (fm_injective C) 0

end LateralTheory.E.AICExtPf
