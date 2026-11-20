import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaDisj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SectionExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatUnique

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem map_restrict {V : Scheme.{0}} {d : ℕ} (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    {U P : V.Opens} (s : (P : Scheme.{0}) ⟶ U) (hs : s ≫ U.ι = P.ι) :
    (M.map U.ι.appTop.hom).map s.appTop.hom = M.map P.ι.appTop.hom := by
  ext m l
  simp only [Matrix.map_apply, ← hs, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatUnique :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), GMat B a b M → GMat B a b M' → M = M' := by
  intro K _ W Z Y q i π D d B V a b M M' hM hM'
  ext m l
  refine sectionExt _ _ fun x => ?_
  obtain ⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩ := hM x
  obtain ⟨U', α', β', a₁', b₁', hx', ha', hb', hL'⟩ := hM' x
  have hs : V.homOfLE (inf_le_left : U ⊓ U' ≤ U) ≫ U.ι = (U ⊓ U').ι := Scheme.homOfLE_ι _ _
  have hs' : V.homOfLE (inf_le_right : U ⊓ U' ≤ U') ≫ U'.ι = (U ⊓ U').ι := Scheme.homOfLE_ι _ _
  generalize V.homOfLE (inf_le_left : U ⊓ U' ≤ U) = s at hs
  generalize V.homOfLE (inf_le_right : U ⊓ U' ≤ U') = s' at hs'
  have pt : ((U ⊓ U' : V.Opens) : Scheme.{0}) := ⟨x, hx, hx'⟩
  have eα : α = α' := by
    refine sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (s ≫ a₁) (s' ≫ a₁') pt ?_
    change (s ≫ a₁) ≫ wI B α = (s' ≫ a₁') ≫ wI B α'
    rw [Category.assoc, Category.assoc, ← ha, ← ha', ← Category.assoc, ← Category.assoc, hs, hs']
  have eβ : β = β' := by
    refine sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (s ≫ b₁) (s' ≫ b₁') pt ?_
    change (s ≫ b₁) ≫ wI B β = (s' ≫ b₁') ≫ wI B β'
    rw [Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, hs, hs']
  subst eα eβ
  have h₁ := locMatNat B α β s _ _ hL
  have h₂ := locMatNat B α β s' _ _ hL'
  rw [map_restrict M s hs, ← Category.assoc, hs] at h₁
  rw [map_restrict M' s' hs', ← Category.assoc, hs'] at h₂
  have e := locMatUnique B α β _ _ _ h₁ h₂
  exact ⟨U ⊓ U', ⟨hx, hx'⟩, congrFun (congrFun e m) l⟩
