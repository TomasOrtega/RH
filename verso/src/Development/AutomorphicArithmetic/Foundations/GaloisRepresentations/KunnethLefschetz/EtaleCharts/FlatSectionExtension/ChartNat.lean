import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V' V : Scheme.{0}} (s : V' ⟶ V) (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ (s ≫ y) ⁻¹ᵁ (B.c α).C k), (∀ m, uV B α k (s ≫ y) h' m = s.appTop.hom (uV B α k y h m)) ∧ secOf B α k (s ≫ y) h' = s ≫ secOf B α k y h := by
  intro K _ W Z Y q i π D d B α k V' V s y h h'
  constructor
  · intro m
    have hs : (⊤ : V'.Opens) ≤ s ⁻¹ᵁ (⊤ : V.Opens) := le_rfl
    have key : (s ≫ y).appLE ((B.c α).C k) ⊤ h' = y.appLE ((B.c α).C k) ⊤ h ≫ s.appTop := by
      have h1 := Scheme.Hom.appLE_comp_appLE s y ((B.c α).C k) ⊤ ⊤ h hs
      rw [← h1]
      congr 1
      simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
      change _ ≫ V'.presheaf.map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    unfold uV
    rw [key]
    rfl
  · unfold secOf
    rw [← Category.assoc]
    congr 1
    symm
    apply IsOpenImmersion.lift_uniq
    rw [Category.assoc, IsOpenImmersion.lift_fac]
