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
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
lemma fm_succ (C : CommRingCat.{0}) (n : ℕ) (h : n ≤ n + 1) : fm C n (n + 1) h = stepHom (towerObj C n) := by
  have := Functor.ofSequence_map_homOfLE_succ (towerMap C) n
  simp only [fm]
  rw [this]; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma fm_comp_succ (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) (h' : i ≤ j + 1) :
    fm C i (j + 1) h' = (stepHom (towerObj C j)).comp (fm C i j h) := by
  rw [← fm_succ C j (Nat.le_succ j)]
  show ((towerF C).map (homOfLE h')).hom =
    ((towerF C).map (homOfLE h) ≫ (towerF C).map (homOfLE (Nat.le_succ j))).hom
  rw [← Functor.map_comp, homOfLE_comp]

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
lemma fm_injective (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : Function.Injective (fm C i j h) := by
  induction j, h using Nat.le_induction with
  | base => intro x y hxy; simpa [DirectedSystem.map_self (f := fun i j h => fm C i j h)] using hxy
  | succ j hij ih =>
    rw [fm_comp_succ C i j hij]
    exact (stepHom_injective _).comp ih

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components.

Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
lemma of_comp (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) :
    (Ring.DirectLimit.of _ (fun i j h => fm C i j h) j).comp (fm C i j h) =
      Ring.DirectLimit.of _ (fun i j h => fm C i j h) i := by
  ext x
  exact Ring.DirectLimit.of_f (G := fun i => (towerObj C i : Type)) (f := fun i j h => fm C i j h) h x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
