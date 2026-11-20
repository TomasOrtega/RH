import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowKillsOnCompactOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulAppEqZeroNearOfRepresentedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ClosedGlue
open Scheme TopologicalSpace

/- English proof (translation)
Establish `e : (g ≫ U.ι).app (U.ι ''ᵁ V) = g.app V ≫ T.presheaf.map (eqToHom (by simp)).op`. Simplify using `only [Scheme.Hom.comp_app, Scheme.Opens.ι_app]`. Use `(g.naturality (homOfLE (U.ι.preimage_image_eq V).le).op).trans ?_` and prove the remaining obligations. Use `congr 2`. Rewrite using `[e]`.

Conclude with `map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1`.
-/
theorem app_comp_ι_eq_zero_iff {T S : Scheme.{0}} (U : S.Opens) (g : T ⟶ U) (V : U.toScheme.Opens)
    (x : Γ(S, U.ι ''ᵁ V)) :
    ((g ≫ U.ι).app (U.ι ''ᵁ V)).hom x = 0 ↔ (g.app V).hom x = 0 := by
  have e : (g ≫ U.ι).app (U.ι ''ᵁ V) = g.app V ≫ T.presheaf.map (eqToHom (by simp)).op := by
    simp only [Scheme.Hom.comp_app, Scheme.Opens.ι_app]
    refine (g.naturality (homOfLE (U.ι.preimage_image_eq V).le).op).trans ?_
    congr 2
  rw [e]
  exact map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1

/- English proof (translation)
Rewrite using `[morphismRestrict_app]`. Conclude with `map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1`.
-/
theorem restrict_app_eq_zero_iff {T S : Scheme.{0}} (f : T ⟶ S) (U : S.Opens) (V : U.toScheme.Opens)
    (a : Γ(S, U.ι ''ᵁ V)) : ((f ∣_ U).app V).hom a = 0 ↔ (f.app (U.ι ''ᵁ V)).hom a = 0 := by
  rw [morphismRestrict_app]
  exact map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1

def killIdeal {S : Scheme.{0}} (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) (W : S.Opens) :
    Ideal Γ(S, W) :=
  ⨅ (T : Scheme.{0}) (t : T ⟶ S) (_ : Φ T t), RingHom.ker (t.app W).hom

/- English proof (translation)
Simplify using `[killIdeal, Submodule.mem_iInf, RingHom.mem_ker]`.
-/
theorem mem_killIdeal {S : Scheme.{0}} (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) {W : S.Opens}
    {b : Γ(S, W)} :
    b ∈ killIdeal Φ W ↔ ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app W).hom b = 0 := by
  simp [killIdeal, Submodule.mem_iInf, RingHom.mem_ker]

/- English proof (translation)
Establish `e` using `congrArg (fun φ => φ.hom b) (t.naturality (homOfLE h).op)`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e`. Rewrite using `[e, hb, map_zero]`.
-/
theorem app_res_eq_zero {S T : Scheme.{0}} (t : T ⟶ S) {V W : S.Opens} (h : V ≤ W) (b : Γ(S, W))
    (hb : (t.app W).hom b = 0) : (t.app V).hom ((S.presheaf.map (homOfLE h).op).hom b) = 0 := by
  have e := congrArg (fun φ => φ.hom b) (t.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e, hb, map_zero]

/- English proof (translation)
Establish `inst` using `W.2.isLocalization_basicOpen f`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `b hb`. Rewrite using `[Ideal.mem_comap, mem_killIdeal]`.

Introduce `T t ht`. Conclude with `app_res_eq_zero t _ b ((mem_killIdeal Φ).1 hb T t ht)`. Introduce `a ha`. Take `⟨c, m, rfl⟩` from `IsLocalization.exists_mk'_eq (Submonoid.powers f) a`. Establish `hc : algebraMap Γ(S, W) Γ(S, S.basicOpen f) c ∈ killIdeal Φ (S.basicOpen f)`.

Rewrite using `[← IsLocalization.mk'_spec Γ(S, S.basicOpen f) c m]`. Conclude with `Ideal.mul_mem_right _ _ ha`. Take `⟨n, hn⟩` from `GlobalTheory.T.exists_pow_kills_on_compact_of_local S Φ (W : S.Opens) W.2.isCompact f c (fun y hy => by`. Take `⟨U, Z, i, hyU, hi, hrep⟩` from `hcov y`. Conclude with `GlobalTheory.T.exists_pow_mul_app_eq_zero_near_of_represented' S Φ hstab U Z i hi hrep (W : S.Opens) f c (fun T t ht => (mem_killIdeal Φ).1 hc T t ht) y hyU hy)`.

Express the relevant statement in the definitionally equal form `IsLocalization.mk' _ c _ ∈ Ideal.map (algebraMap Γ(S, W) Γ(S, S.basicOpen f)) _`. Rewrite using `[IsLocalization.mk'_mem_map_algebraMap_iff]`. Conclude with `⟨f ^ n, ⟨n, rfl⟩, (mem_killIdeal Φ).2 hn⟩`.
-/
theorem killIdeal_map_basicOpen {S : Scheme.{0}} (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop)
    (hstab : ∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t))
    (hcov : ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t)
    (W : S.affineOpens) (f : Γ(S, W)) :
    (killIdeal Φ W).map (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom =
      killIdeal Φ (S.basicOpen f) := by
  have inst := W.2.isLocalization_basicOpen f
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, mem_killIdeal]
    intro T t ht
    exact app_res_eq_zero t _ b ((mem_killIdeal Φ).1 hb T t ht)
  · intro a ha
    obtain ⟨c, m, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) a
    have hc : algebraMap Γ(S, W) Γ(S, S.basicOpen f) c ∈ killIdeal Φ (S.basicOpen f) := by
      rw [← IsLocalization.mk'_spec Γ(S, S.basicOpen f) c m]
      exact Ideal.mul_mem_right _ _ ha
    obtain ⟨n, hn⟩ := GlobalTheory.T.exists_pow_kills_on_compact_of_local S Φ (W : S.Opens) W.2.isCompact f c (fun y hy => by
      obtain ⟨U, Z, i, hyU, hi, hrep⟩ := hcov y
      exact GlobalTheory.T.exists_pow_mul_app_eq_zero_near_of_represented' S Φ hstab U Z i hi hrep (W : S.Opens) f c
        (fun T t ht => (mem_killIdeal Φ).1 hc T t ht) y hyU hy)
    change IsLocalization.mk' _ c _ ∈ Ideal.map (algebraMap Γ(S, W) Γ(S, S.basicOpen f)) _
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨f ^ n, ⟨n, rfl⟩, (mem_killIdeal Φ).2 hn⟩

end GlobalTheory.ClosedGlue

open GlobalTheory.ClosedGlue in

/- English proof (translation)
Introduce `S Φ hstab hloc hcov`. Set `J : S.IdealSheafData` to `{ ideal := fun W => killIdeal Φ W map_ideal_basicOpen := fun W f => killIdeal_map_basicOpen Φ hstab hcov W f }`. Establish `hfac : ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → ∃ z : T ⟶ J.subscheme, z ≫ J.subschemeι = t`. Introduce `T t ht`. Establish `hle : J ≤ t.ker`.

Use `Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_` and prove the remaining obligations. Introduce `W b hb`. Conclude with `(mem_killIdeal Φ).1 hb T t ht`. Conclude with `⟨t.toImage ≫ Scheme.IdealSheafData.inclusion hle, by simp⟩`. Establish `hZ : Φ J.subscheme J.subschemeι`.

Apply `hloc` to reduce the goal to its premises. Introduce `τ`. Take `⟨U, Z, i, hxU, hi, hrep⟩` from `hcov (J.subschemeι τ)`. Use `⟨J.subschemeι ⁻¹ᵁ U, hxU, ?_⟩` and prove the remaining obligations. Rewrite using `[← morphismRestrict_ι]`.

Use `(hrep _ _).2 ⟨IsClosedImmersion.lift i (J.subschemeι ∣_ U) ?_, IsClosedImmersion.lift_fac _ _ _⟩` and prove the remaining obligations. Use `Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_` and prove the remaining obligations. Introduce `W a ha`. Rewrite `ha` using `[Scheme.Hom.ker_apply]`. Rewrite using `[RingHom.mem_ker]`.

Use `(restrict_app_eq_zero_iff _ U W a).2 ?_` and prove the remaining obligations. Establish `hmem : a ∈ killIdeal Φ (U.ι ''ᵁ W)` using `(mem_killIdeal Φ).2 fun T t ht => by`. Take `⟨z, hz⟩` from `(hrep _ (t ∣_ U)).1 (by rw [morphismRestrict_ι]; exact hstab _ _ _ _ ht)`. Use `(restrict_app_eq_zero_iff t U W a).1 ?_` and prove the remaining obligations. Rewrite using `[← hz]`.

Use `show (z.app (i ⁻¹ᵁ W)).hom ((i.app W).hom a) = 0`. Rewrite using `[RingHom.mem_ker.1 ha, map_zero]`. Establish `h2` using `(J.ker_subschemeι_app ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion _⟩).ge hmem`. Conclude with `h2`. Use `⟨J.subscheme, J.subschemeι, inferInstance, fun T t => ⟨hfac T t, ?_⟩⟩` and prove the remaining obligations.

Introduce and unpack `⟨z, rfl⟩`. Conclude with `hstab _ _ _ _ hZ`.
-/
theorem GlobalTheory.closedSubscheme_glue : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → (∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ Φ V (V.ι ≫ t)) → Φ T t) → (∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  intro S Φ hstab hloc hcov
  let J : S.IdealSheafData :=
    { ideal := fun W => killIdeal Φ W
      map_ideal_basicOpen := fun W f => killIdeal_map_basicOpen Φ hstab hcov W f }
  have hfac : ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t →
      ∃ z : T ⟶ J.subscheme, z ≫ J.subschemeι = t := by
    intro T t ht
    have hle : J ≤ t.ker := by
      refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
      intro W b hb
      exact (mem_killIdeal Φ).1 hb T t ht
    exact ⟨t.toImage ≫ Scheme.IdealSheafData.inclusion hle, by simp⟩
  have hZ : Φ J.subscheme J.subschemeι := by
    apply hloc
    intro τ
    obtain ⟨U, Z, i, hxU, hi, hrep⟩ := hcov (J.subschemeι τ)
    refine ⟨J.subschemeι ⁻¹ᵁ U, hxU, ?_⟩
    rw [← morphismRestrict_ι]
    refine (hrep _ _).2 ⟨IsClosedImmersion.lift i (J.subschemeι ∣_ U) ?_,
      IsClosedImmersion.lift_fac _ _ _⟩
    refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
    intro W a ha
    rw [Scheme.Hom.ker_apply] at ha
    rw [RingHom.mem_ker]
    refine (restrict_app_eq_zero_iff _ U W a).2 ?_
    have hmem : a ∈ killIdeal Φ (U.ι ''ᵁ W) := (mem_killIdeal Φ).2 fun T t ht => by
      obtain ⟨z, hz⟩ := (hrep _ (t ∣_ U)).1 (by rw [morphismRestrict_ι]; exact hstab _ _ _ _ ht)
      refine (restrict_app_eq_zero_iff t U W a).1 ?_
      rw [← hz]
      show (z.app (i ⁻¹ᵁ W)).hom ((i.app W).hom a) = 0
      rw [RingHom.mem_ker.1 ha, map_zero]
    have h2 := (J.ker_subschemeι_app ⟨U.ι ''ᵁ W, W.2.image_of_isOpenImmersion _⟩).ge hmem
    exact h2
  refine ⟨J.subscheme, J.subschemeι, inferInstance, fun T t => ⟨hfac T t, ?_⟩⟩
  rintro ⟨z, rfl⟩
  exact hstab _ _ _ _ hZ
