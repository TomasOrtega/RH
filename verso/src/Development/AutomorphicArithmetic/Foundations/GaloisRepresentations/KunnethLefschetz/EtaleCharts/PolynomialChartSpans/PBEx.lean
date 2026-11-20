import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ExistsG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ExistsV
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.WCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.TCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.CoverComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.InjField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.OntoField

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

/- English proof (translation)
Introduce `K _ W Z Y T q i π D d hB j r hsq`. Take `⟨B⟩` from `hB`. Take `⟨g, gn, gc, gs⟩` from `existsG B`. Take `⟨v, hv, hu⟩` from `existsV B j`. Take `⟨sc, uc⟩` from `wCover B`.

Take `⟨se, ue⟩` from `tCover B j r hsq`. Take `⟨cm, ct⟩` from `coverComm B j r hsq.w`. Establish `hτ : ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j), a ≫ eP B j = b ≫ eP B j → (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f` using `fun a b h => by`. Rewrite using `[Category.assoc, Category.assoc, ct, reassoc_of% h]`. Establish `hone : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (e : a = b) (h : a ≫ cP B = b ≫ cP B), g a b h = 1`.

Introduce `V a b e h`. Substitute `e` using the available equality. Use `gc a a a h h` as an intermediate fact. Conclude with `mul_eq_left.1 this`. Set `P : PBData r d` to `{ W' := WP B c := cP B g := g g_nat := gn g_coc := gc T' := TP B j e := eP B j ρ := rhoP B j r hsq.w comm := cm v := fun a => ⟨a.appTop.hom ∘ v, by`.

Rewrite using `[Set.range_comp, ← Ideal.map_span, hu, Ideal.map_top]⟩`. Use `v_nat := fun s a => by`. Use function extensionality and compare the values at `m`. Simplify using `only [Function.comp_apply, Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.

Use `w := fun a b h => (D.u _ _ (hτ a b h))⁻¹`. Use `gv := fun a b h h' => gvField B j r hsq v hv a b h (hτ a b h) _ (gs _ _ h')`. Use `inj := fun a b h' u hh => injField B j r hsq v hv a b _ h' (gs _ _ h') u hh`. Use `onto := fun a₀ v₀ x => by`. Take `⟨U, a, u, hx, ha, hv'⟩` from `ontoField B j r hsq v hv a₀ v₀ x`.

Establish `h : (a ≫ rhoP B j r hsq.w) ≫ cP B = (U.ι ≫ a₀) ≫ cP B` using `by rw [ha]`. Use `⟨U, a, h, u, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[hone _ _ ha h]`. Simplify using `using hv' }`. Conclude with `⟨P, tauP B j, ct, fun a b h h' => rfl⟩`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.pBEx : UpperTheory.Gal.KunnethLefschetz.G.PBEx := by
  intro K _ W Z Y T q i π D d hB j r hsq
  obtain ⟨B⟩ := hB
  obtain ⟨g, gn, gc, gs⟩ := existsG B
  obtain ⟨v, hv, hu⟩ := existsV B j
  obtain ⟨sc, uc⟩ := wCover B
  obtain ⟨se, ue⟩ := tCover B j r hsq
  obtain ⟨cm, ct⟩ := coverComm B j r hsq.w
  have hτ : ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j), a ≫ eP B j = b ≫ eP B j →
      (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f := fun a b h => by
    rw [Category.assoc, Category.assoc, ct, reassoc_of% h]
  have hone : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (e : a = b) (h : a ≫ cP B = b ≫ cP B), g a b h = 1 := by
    intro V a b e h
    subst e
    have := gc a a a h h
    exact mul_eq_left.1 this
  let P : PBData r d :=
    { W' := WP B
      c := cP B
      g := g
      g_nat := gn
      g_coc := gc
      T' := TP B j
      e := eP B j
      ρ := rhoP B j r hsq.w
      comm := cm
      v := fun a => ⟨a.appTop.hom ∘ v, by
        rw [Set.range_comp, ← Ideal.map_span, hu, Ideal.map_top]⟩
      v_nat := fun s a => by
        funext m
        simp only [Function.comp_apply, Scheme.Hom.comp_appTop]
        rfl
      w := fun a b h => (D.u _ _ (hτ a b h))⁻¹
      gv := fun a b h h' => gvField B j r hsq v hv a b h (hτ a b h) _ (gs _ _ h')
      inj := fun a b h' u hh => injField B j r hsq v hv a b _ h' (gs _ _ h') u hh
      onto := fun a₀ v₀ x => by
        obtain ⟨U, a, u, hx, ha, hv'⟩ := ontoField B j r hsq v hv a₀ v₀ x
        have h : (a ≫ rhoP B j r hsq.w) ≫ cP B = (U.ι ≫ a₀) ≫ cP B := by rw [ha]
        refine ⟨U, a, h, u, hx, ?_⟩
        rw [hone _ _ ha h]
        simpa using hv' }
  exact ⟨P, tauP B j, ct, fun a b h h' => rfl⟩
