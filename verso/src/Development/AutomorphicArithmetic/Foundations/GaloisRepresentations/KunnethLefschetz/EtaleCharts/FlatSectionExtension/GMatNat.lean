import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatNat

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V' V : Scheme.{0}} (s : V' ⟶ V) (a b : V ⟶ WP B) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), GMat B a b M → GMat B (s ≫ a) (s ≫ b) (M.map s.appTop.hom) := by
  intro K _ W Z Y q i π D d B V' V s a b M h x'
  obtain ⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩ := h (s x')
  have hι : (s ∣_ U) ≫ U.ι = (s ⁻¹ᵁ U).ι ≫ s := morphismRestrict_ι s U
  refine ⟨s ⁻¹ᵁ U, α, β, (s ∣_ U) ≫ a₁, (s ∣_ U) ≫ b₁, hx, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← ha, reassoc_of% hι]
  · rw [Category.assoc, ← hb, reassoc_of% hι]
  · have h2 := locMatNat B α β (s ∣_ U) _ _ hL
    have e1 : (s ∣_ U) ≫ U.ι ≫ a ≫ cP B = (s ⁻¹ᵁ U).ι ≫ (s ≫ a) ≫ cP B := by
      rw [← Category.assoc, hι]; simp only [Category.assoc]
    have e2 : ((M.map U.ι.appTop.hom).map (s ∣_ U).appTop.hom) =
        ((M.map s.appTop.hom).map (s ⁻¹ᵁ U).ι.appTop.hom) := by
      ext m l
      simp only [Matrix.map_apply]
      have h3 : U.ι.appTop ≫ (s ∣_ U).appTop = s.appTop ≫ (s ⁻¹ᵁ U).ι.appTop := by
        rw [← Scheme.Hom.comp_appTop, hι, Scheme.Hom.comp_appTop]
      exact congrArg (fun f => f.hom (M m l)) h3
    rw [e1, e2] at h2
    exact h2
