import Development.EtaleCohomology.CohomologicalPurity.LeafTauPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Substitute `h3` using the available equality. Substitute `h4` using the available equality. Both sides reduce to the same expression.
-/
theorem tt_cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'')
    (h4 : i' = i'') (a : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 a) = Ht.cast (h1.trans h3) (h2.trans h4) a := by
  subst h1; subst h2; subst h3; subst h4; rfl

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem tt_pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) : pull _ f _ _ (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f _ _ a) := by
  subst h1; subst h2; rfl

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem tt_cup_cast_right {q : ℕ} {E : Spc} {n i m j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i)
    (b : Ht q E m j) : cup q a (Ht.cast h1 h2 b) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

/- English proof (translation)
Substitute `h1` using the available equality. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem tt_cup_cast_left {q : ℕ} {E : Spc} {n i m j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i)
    (b : Ht q E m j) : cup q (Ht.cast h1 h2 a) b = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1; subst h2; rfl

/- English proof (translation)
Introduce `H q _ d R _ n i x a`. Establish `h6 : DivisorNaturality` using `H.2.2.2.2.1`. Establish `hr : DivisorRingCompatibility` using `H.2.2.2.2.2.1`. Set `e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ))` to `Fin.lastCases (motive := fun j : Fin (d + 1) => Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ))) (x.cast (by simp) (by simp)) (fun j => (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring) (by simp only [Fin.val_castSucc]; ring))`. Use `⟨e, by simp [e], ?_⟩` and prove the remaining obligations.

Establish `he : ∀ j : Fin d, e j.castSucc = (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring) (by simp only [Fin.val_castSucc]; ring)` using `fun j => by simp [e]`. Establish `hl : e (Fin.last d) = x.cast (by simp) (by simp)` using `by simp [e]`. Unfold `poly`. Rewrite using `[map_add, map_sum, Fin.sum_univ_castSucc]`. Use `(add_comm _ _).trans ?_` and prove the remaining obligations.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[he, tt_pull_cast, tt_cup_cast_left, (h6 q).1, (hr q _).2.1, tt_cup_cast_right]`. Repeat the step `rw [tt_cast_cast]` while it applies. Both sides reduce to the same expression.

Rewrite using `[hl, tt_pull_cast, tt_cup_cast_left]`. Repeat the step `rw [tt_cast_cast]` while it applies. Both sides reduce to the same expression.
-/
theorem tauTop : LeafTauTop := by
  intro H q _ d R _ n i x a
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hr : DivisorRingCompatibility := H.2.2.2.2.2.1
  let e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)) :=
    Fin.lastCases (motive := fun j : Fin (d + 1) =>
        Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)))
      (x.cast (by simp) (by simp))
      (fun j => (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring) (by simp only [Fin.val_castSucc]; ring))
  refine ⟨e, by simp [e], ?_⟩
  have he : ∀ j : Fin d, e j.castSucc = (cup q x (a j)).cast (by simp only [Fin.val_castSucc]; ring)
      (by simp only [Fin.val_castSucc]; ring) := fun j => by simp [e]
  have hl : e (Fin.last d) = x.cast (by simp) (by simp) := by simp [e]
  unfold poly
  rw [map_add, map_sum, Fin.sum_univ_castSucc]
  refine (add_comm _ _).trans ?_
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [he, tt_pull_cast, tt_cup_cast_left, (h6 q).1, (hr q _).2.1, tt_cup_cast_right]
    repeat rw [tt_cast_cast]
    rfl
  · rw [hl, tt_pull_cast, tt_cup_cast_left]
    repeat rw [tt_cast_cast]
    rfl

/- English proof (translation)
The claim follows from `tauTop`.
-/
theorem LeafTauTop_of : LeafTauTop := tauTop

end LateralTheory.CohomologicalPurity.Thom
