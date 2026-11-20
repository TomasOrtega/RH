import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.EqLocus

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Express the relevant assertion in an equivalent form by its definition.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_fin (H : Scheme.{0}) (G : Over H) [IsSeparated G.hom] :
    ∀ (n : ℕ) (Z : Over H), IsFinite Z.hom → ∀ (a b : Fin n → (Z ⟶ G)),
      ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧ (∀ k, i ≫ a k = i ≫ b k) ∧
        ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) → ∃! h' : T ⟶ Y, h' ≫ i = h := by
  intro n
  induction n with
  | zero =>
    intro Z hZ a b
    refine ⟨Z, 𝟙 Z, hZ, fun k => k.elim0, fun T h _ => ⟨h, by simp, fun g hg => by simpa using hg⟩⟩
  | succ n ih =>
    intro Z hZ a b
    let e := equalizer.ι (a 0) (b 0)
    have hE : IsFinite (equalizer (a 0) (b 0)).hom := by
      rw [← Over.w e]
      infer_instance
    obtain ⟨Y, i', hY, hi', hu⟩ := ih _ hE (fun k => e ≫ a k.succ) (fun k => e ≫ b k.succ)
    refine ⟨Y, i' ≫ e, hY, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [Category.assoc]
        rw [equalizer.condition]
      · simpa only [Category.assoc] using hi' k
    · intro T h hh
      let l : T ⟶ equalizer (a 0) (b 0) := equalizer.lift h (hh 0)
      have hl : l ≫ e = h := equalizer.lift_ι _ _
      obtain ⟨h'', hh'', hu''⟩ := hu T l (fun k => by
        simp only [← Category.assoc, hl]
        exact hh k.succ)
      refine ⟨h'', show h'' ≫ i' ≫ e = h by rw [← Category.assoc, hh'', hl], fun g hg => hu'' g ?_⟩
      change g ≫ i' ≫ e = h at hg
      change g ≫ i' = l
      apply (cancel_mono e).1
      rw [Category.assoc, hg, hl]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.
-/
theorem exists_finite_eqLocus : ∀ (H : Scheme.{0}) (Z G : Over H), IsFinite Z.hom → IsSeparated G.hom →
    ∀ (Ix : Type) [Finite Ix] (a b : Ix → (Z ⟶ G)), ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧
      (∀ k, i ≫ a k = i ≫ b k) ∧ ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) →
        ∃! h' : T ⟶ Y, h' ≫ i = h := by
  intro H Z G hZ hG Ix _ a b
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin Ix
  obtain ⟨Y, i, hY, hi, hu⟩ := exists_fin H G n Z hZ (fun k => a (σ.symm k)) (fun k => b (σ.symm k))
  refine ⟨Y, i, hY, fun k => by simpa using hi (σ k), fun T h hh => hu T h (fun k => hh _)⟩

end GlobalTheory.EqLocus
