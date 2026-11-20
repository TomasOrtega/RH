import Development.EtaleCohomology.KummerTheory.FinalTheorems

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LhNatPf

/- English proof (translation)
Substitute using the available equality. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem rst_fst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    LateralTheory.KummerTheory.LHCut.rst p g ≫ pullback.fst p U.hom = pullback.fst p V.hom := by
  unfold LateralTheory.KummerTheory.LHCut.rst; rw [pullback.lift_fst, Category.comp_id]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem rst_snd {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    LateralTheory.KummerTheory.LHCut.rst p g ≫ pullback.snd p U.hom = pullback.snd p V.hom ≫ g.left := by
  unfold LateralTheory.KummerTheory.LHCut.rst; exact pullback.lift_snd _ _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pull_pull (q : ℕ) {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {n i : ℤ} (x : Ht q E'' n i) :
    pull _ f _ _ (pull _ g _ _ x) = pull _ (f ≫ g) _ _ x := (pull_comp _ f g _ _ x).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities.
-/
theorem lhNat_of : LateralTheory.KummerTheory.LHCut.LhNat := by
  intro hA q _ X S p i r c M n V U g y
  unfold LateralTheory.KummerTheory.lh
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
  unfold LateralTheory.KummerTheory.ext
  rw [pull_cast, (hA q).1, pull_pull, pull_pull, pull_pull, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, rst_fst, rst_snd]

end LateralTheory.KummerTheory.LhNatPf
