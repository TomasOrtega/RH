import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaDisj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SectionExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatUnique

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Use extensionality with `m l`. Simplify using `only [Matrix.map_apply, ← hs, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]`.
-/
private theorem map_restrict {V : Scheme.{0}} {d : ℕ} (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    {U P : V.Opens} (s : (P : Scheme.{0}) ⟶ U) (hs : s ≫ U.ι = P.ι) :
    (M.map U.ι.appTop.hom).map s.appTop.hom = M.map P.ι.appTop.hom := by
  ext m l
  simp only [Matrix.map_apply, ← hs, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

/- English proof (translation)
Introduce `K _ W Z Y q i π D d B V a b M M' hM hM'`. Use extensionality with `m l`. Use `sectionExt _ _ fun x => ?_` and prove the remaining obligations. Take `⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩` from `hM x`. Take `⟨U', α', β', a₁', b₁', hx', ha', hb', hL'⟩` from `hM' x`.

Establish `hs : V.homOfLE (inf_le_left : U ⊓ U' ≤ U) ≫ U.ι = (U ⊓ U').ι` using `Scheme.homOfLE_ι _ _`. Establish `hs' : V.homOfLE (inf_le_right : U ⊓ U' ≤ U') ≫ U'.ι = (U ⊓ U').ι` using `Scheme.homOfLE_ι _ _`. Generalize the expression as in `V.homOfLE (inf_le_left : U ⊓ U' ≤ U) = s at hs`. Generalize the expression as in `V.homOfLE (inf_le_right : U ⊓ U' ≤ U') = s' at hs'`. Establish `pt : ((U ⊓ U' : V.Opens) : Scheme.{0})` using `⟨x, hx, hx'⟩`.

Establish `eα : α = α'`. Use `sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (s ≫ a₁) (s' ≫ a₁') pt ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s ≫ a₁) ≫ wI B α = (s' ≫ a₁') ≫ wI B α'`. Rewrite using `[Category.assoc, Category.assoc, ← ha, ← ha', ← Category.assoc, ← Category.assoc, hs, hs']`. Establish `eβ : β = β'`.

Use `sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (s ≫ b₁) (s' ≫ b₁') pt ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s ≫ b₁) ≫ wI B β = (s' ≫ b₁') ≫ wI B β'`. Rewrite using `[Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, hs, hs']`. Substitute `eα eβ` using the available equality. Establish `h₁` using `locMatNat B α β s _ _ hL`.

Establish `h₂` using `locMatNat B α β s' _ _ hL'`. Rewrite `h₁` using `[map_restrict M s hs, ← Category.assoc, hs]`. Rewrite `h₂` using `[map_restrict M' s' hs', ← Category.assoc, hs']`. Establish `e` using `locMatUnique B α β _ _ _ h₁ h₂`. Conclude with `⟨U ⊓ U', ⟨hx, hx'⟩, congrFun (congrFun e m) l⟩`.
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
