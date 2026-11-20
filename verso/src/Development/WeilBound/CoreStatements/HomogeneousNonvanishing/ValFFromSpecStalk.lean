import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.Cartier GlobalTheory.ZH

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination

/- English proof (translation)
Establish `hsp : ∀ w, (X.fromSpecStalk (genericPoint X)).base w ⤳ genericPoint X`. Introduce `w`. Establish `hw : (X.fromSpecStalk (genericPoint X)).base w ∈ Set.range (X.fromSpecStalk (genericPoint X)).base` using `⟨w, rfl⟩`. Rewrite `hw` using `[Scheme.range_fromSpecStalk]`. Conclude with `hw`.

Establish `hU : ⊤ ≤ (Opens.map (X.fromSpecStalk (genericPoint X)).base).obj U`. Introduce `w _`. Conclude with `(hsp w).mem_open U.isOpen h`. Establish `key : Scheme.Hom.appLE (X.fromSpecStalk (genericPoint X)) U ⊤ hU ≫ (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom = X.presheaf.germ U (genericPoint X) h`. Rewrite using `[Scheme.Hom.appLE, Scheme.fromSpecStalk_app h]`.

Simplify using `only [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, homOfLE_comp, homOfLE_refl, op_id, Functor.map_id, Category.id_comp, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]`. Simplify using the standard rewrite rules. Unfold `valF`. Rewrite using `[dif_pos hU]`. Conclude with `congrArg (fun φ => CommRingCat.Hom.hom φ f) key`.
-/
theorem valF_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)) :
    valF (F := X.functionField) (X.fromSpecStalk (genericPoint X)) U f = fnOf U h f := by
  have hsp : ∀ w, (X.fromSpecStalk (genericPoint X)).base w ⤳ genericPoint X := by
    intro w
    have hw : (X.fromSpecStalk (genericPoint X)).base w ∈ Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hw
    exact hw
  have hU : ⊤ ≤ (Opens.map (X.fromSpecStalk (genericPoint X)).base).obj U := by
    intro w _
    exact (hsp w).mem_open U.isOpen h
  have key : Scheme.Hom.appLE (X.fromSpecStalk (genericPoint X)) U ⊤ hU ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom = X.presheaf.germ U (genericPoint X) h := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app h]
    simp only [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, homOfLE_comp, homOfLE_refl, op_id,
      Functor.map_id, Category.id_comp, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
    simp
  unfold valF
  rw [dif_pos hU]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ f) key

/- English proof (translation)
Introduce `w _`. Establish `hw : (X.fromSpecStalk (genericPoint X)).base w ∈ Set.range (X.fromSpecStalk (genericPoint X)).base` using `⟨w, rfl⟩`. Rewrite `hw` using `[Scheme.range_fromSpecStalk]`. Conclude with `hw.mem_open U.isOpen h`.
-/
private theorem top_le_map_fromSpecStalk_genericPoint (X : Scheme.{0}) [IsIntegral X] (U : X.Opens)
    (h : genericPoint X ∈ U) : ⊤ ≤ (Opens.map (X.fromSpecStalk (genericPoint X)).base).obj U := by
  intro w _
  have hw : (X.fromSpecStalk (genericPoint X)).base w ∈ Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨w, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hw
  exact hw.mem_open U.isOpen h

/- English proof (translation)
Establish `h2 : ⊤ ≤ (Opens.map (spMap σ ≫ y).base).obj U` using `fun w _ => hy (Opens.mem_top ((spMap σ).base w))`. Establish `k2 : Scheme.Hom.appLE (spMap σ) ⊤ ⊤ (fun _ _ => trivial) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom σ`. Establish `hn` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)`. Use `hn using 2` and compare the differences between its conclusion and the goal. Conclude with `Scheme.Hom.appLE_eq_app (spMap σ) (U := ⊤)`.

Unfold `valF`. Rewrite using `[dif_pos h2, dif_pos hy, ← Scheme.Hom.appLE_comp_appLE (spMap σ) y U ⊤ ⊤ hy (fun _ _ => trivial)]`. Conclude with `congrArg (fun φ => CommRingCat.Hom.hom φ (CommRingCat.Hom.hom (Scheme.Hom.appLE y U ⊤ hy) f)) k2`.
-/
private theorem valF_spMap_comp' {K L : Type} [Field K] [Field L] (σ : K →+* L) {Y : Scheme.{0}}
    (y : Sp K ⟶ Y) (U : Y.Opens) (hy : ⊤ ≤ (Opens.map y.base).obj U) (f : Γ(Y, U)) :
    valF (spMap σ ≫ y) U f = σ (valF y U f) := by
  have h2 : ⊤ ≤ (Opens.map (spMap σ ≫ y).base).obj U := fun w _ => hy (Opens.mem_top ((spMap σ).base w))
  have k2 : Scheme.Hom.appLE (spMap σ) ⊤ ⊤ (fun _ _ => trivial) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom σ := by
    have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
    convert hn using 2
    exact Scheme.Hom.appLE_eq_app (spMap σ) (U := ⊤)
  unfold valF
  rw [dif_pos h2, dif_pos hy, ← Scheme.Hom.appLE_comp_appLE (spMap σ) y U ⊤ ⊤ hy (fun _ _ => trivial)]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (CommRingCat.Hom.hom (Scheme.Hom.appLE y U ⊤ hy) f)) k2

/- English proof (translation)
Set `e : Ω ≃+* X.functionField` to `RingEquiv.ofBijective ψ hψ`. Set `σ : X.functionField →+* Ω` to `e.symm.toRingHom`. Establish `H4 : ∀ (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)), ψ (valF (spMap σ ≫ X.fromSpecStalk (genericPoint X)) U f) = fnOf U h f`. Introduce `U h f`. Rewrite using `[valF_spMap_comp' σ _ U (top_le_map_fromSpecStalk_genericPoint X U h) f, valF_fromSpecStalk X U h f]`.

Conclude with `e.apply_symm_apply _`. Establish `hval : ∀ a : o, valF (spMap σ ≫ X.fromSpecStalk (genericPoint X)) ⊤ (algX p ⊤ a) = algebraMap o Ω a`. Introduce `a`. Apply `hψ.1` to reduce the goal to its premises. Rewrite using `[H4 ⊤ (Opens.mem_top _) (algX p ⊤ a), hb a]`.

Establish `hrange : ∀ w, (spMap σ ≫ X.fromSpecStalk (genericPoint X)).base w = genericPoint X`. Introduce `w`. Establish `hw : (X.fromSpecStalk (genericPoint X)).base ((spMap σ).base w) ∈ Set.range (X.fromSpecStalk (genericPoint X)).base` using `⟨_, rfl⟩`. Rewrite `hw` using `[Scheme.range_fromSpecStalk]`. Conclude with `(Specializes.antisymm hw ((genericPoint_spec ↥X).specializes trivial)).eq`.

Use `⟨(spMap σ ≫ X.fromSpecStalk (genericPoint X)), ?_, ?_, ?_, H4⟩` and prove the remaining obligations. Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of o)).inv, ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom]`. Establish `hR : (Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ (spMap (algebraMap o Ω)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap o Ω)`. Rewrite using `[spMap, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]`.

Establish `hL : (Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ ((spMap σ ≫ X.fromSpecStalk (genericPoint X)) ≫ p).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap o Ω)`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `_ = algebraMap o Ω a`. Rewrite using `[← hval a]`. Establish `q1 : Scheme.Hom.appLE p ⊤ ⊤ (fun _ _ => trivial) = p.appTop` using `Scheme.Hom.appLE_eq_app p (U := ⊤)`.

Establish `q2 : Scheme.Hom.appLE (spMap σ ≫ X.fromSpecStalk (genericPoint X)) ⊤ ⊤ (fun _ _ => trivial) = (spMap σ ≫ X.fromSpecStalk (genericPoint X)).appTop` using `Scheme.Hom.appLE_eq_app _ (U := ⊤)`. Unfold `valF algX`. Rewrite using `[dif_pos (show ⊤ ≤ (Opens.map (spMap σ ≫ X.fromSpecStalk (genericPoint X)).base).obj ⊤ from fun _ _ => trivial), q1, q2]`. Both sides reduce to the same expression. Simplify using `only [Category.assoc] at hL hR ⊢`.

Rewrite using `[hL, hR]`. Use `Set.eq_singleton_iff_unique_mem.mpr ⟨⟨IsLocalRing.closedPoint Ω, hrange _⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `hrange w`. Introduce `x`.

Take `⟨V, hV, s, hs⟩` from `X.presheaf.exists_germ_eq (ψ x)`. Use `⟨V, s, ⟨_, hV⟩, hψ.1 ?_⟩` and prove the remaining obligations. Rewrite using `[H4 V hV s]`. Conclude with `hs`.
-/
theorem exists_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp o)
    (ψ : Ω →+* X.functionField) (hψ : Function.Bijective ψ)
    (hb : ∀ a : o, ψ (algebraMap o Ω a) = fnOf ⊤ (Opens.mem_top _) (algX p ⊤ a)) :
    ∃ pt : Sp Ω ⟶ X, pt ≫ p = spMap (algebraMap o Ω) ∧ Set.range pt = {genericPoint X} ∧
      (∀ x : Ω, ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧
      ∀ (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)), ψ (valF pt U f) = fnOf U h f := by
  let e : Ω ≃+* X.functionField := RingEquiv.ofBijective ψ hψ
  let σ : X.functionField →+* Ω := e.symm.toRingHom
  have H4 : ∀ (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)),
      ψ (valF (spMap σ ≫ X.fromSpecStalk (genericPoint X)) U f) = fnOf U h f := by
    intro U h f
    rw [valF_spMap_comp' σ _ U (top_le_map_fromSpecStalk_genericPoint X U h) f, valF_fromSpecStalk X U h f]
    exact e.apply_symm_apply _
  have hval : ∀ a : o, valF (spMap σ ≫ X.fromSpecStalk (genericPoint X)) ⊤ (algX p ⊤ a) = algebraMap o Ω a := by
    intro a
    apply hψ.1
    rw [H4 ⊤ (Opens.mem_top _) (algX p ⊤ a), hb a]
  have hrange : ∀ w, (spMap σ ≫ X.fromSpecStalk (genericPoint X)).base w = genericPoint X := by
    intro w
    have hw : (X.fromSpecStalk (genericPoint X)).base ((spMap σ).base w) ∈
        Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hw
    exact (Specializes.antisymm hw ((genericPoint_spec ↥X).specializes trivial)).eq
  refine ⟨(spMap σ ≫ X.fromSpecStalk (genericPoint X)), ?_, ?_, ?_, H4⟩
  · apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of o)).inv,
      ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom]
    have hR : (Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ (spMap (algebraMap o Ω)).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap o Ω) := by
      rw [spMap, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    have hL : (Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ ((spMap σ ≫ X.fromSpecStalk (genericPoint X)) ≫ p).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap o Ω) := by
      ext a
      change _ = algebraMap o Ω a
      rw [← hval a]
      have q1 : Scheme.Hom.appLE p ⊤ ⊤ (fun _ _ => trivial) = p.appTop := Scheme.Hom.appLE_eq_app p (U := ⊤)
      have q2 : Scheme.Hom.appLE (spMap σ ≫ X.fromSpecStalk (genericPoint X)) ⊤ ⊤ (fun _ _ => trivial) = (spMap σ ≫ X.fromSpecStalk (genericPoint X)).appTop :=
        Scheme.Hom.appLE_eq_app _ (U := ⊤)
      unfold valF algX
      rw [dif_pos (show ⊤ ≤ (Opens.map (spMap σ ≫ X.fromSpecStalk (genericPoint X)).base).obj ⊤ from fun _ _ => trivial),
        q1, q2]
      rfl
    simp only [Category.assoc] at hL hR ⊢
    rw [hL, hR]
  · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨IsLocalRing.closedPoint Ω, hrange _⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact hrange w
  · intro x
    obtain ⟨V, hV, s, hs⟩ := X.presheaf.exists_germ_eq (ψ x)
    refine ⟨V, s, ⟨_, hV⟩, hψ.1 ?_⟩
    rw [H4 V hV s]
    exact hs

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination
