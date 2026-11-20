import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FlatRoots

/- English proof (translation)
Use `haveI : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)`. Set `e` to `(pullback t f).isoSpec`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (e.inv ≫ pullback.fst t f)`. Establish `hff : ψ.hom.FaithfullyFlat`. Rewrite using `[← flat_and_surjective_SpecMap_iff, hψ]`.

Conclude with `⟨inferInstance, inferInstance⟩`. Use `⟨Γ(pullback t f, ⊤), inferInstance, ψ.hom, e.inv ≫ pullback.snd t f, hff, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = Spec.map ψ ≫ t`. Rewrite using `[hψ, Category.assoc, Category.assoc, pullback.condition]`.
-/
theorem exists_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f]
    (S : Type) [CommRing S] (t : Sp S ⟶ Y) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : Sp B ⟶ X),
      φ.FaithfullyFlat ∧ w ≫ f = spMap φ ≫ t := by
  haveI : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let e := (pullback t f).isoSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (e.inv ≫ pullback.fst t f)
  have hff : ψ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hψ]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨Γ(pullback t f, ⊤), inferInstance, ψ.hom, e.inv ≫ pullback.snd t f, hff, ?_⟩
  change _ = Spec.map ψ ≫ t
  rw [hψ, Category.assoc, Category.assoc, pullback.condition]

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨S, inferInstance, RingHom.id S, RingHom.FaithfullyFlat.of_bijective Function.bijective_id, fun i hi => absurd hi (Finset.notMem_empty i)⟩`. Consider the case `insert j s _ ih`. Take `⟨B, _, φ, hφ, h⟩` from `ih`. Take `⟨C, _, ψ, w, hψ, hw⟩` from `exists_lift f B (spMap φ ≫ t j)`.

Use `⟨C, inferInstance, ψ.comp φ, RingHom.FaithfullyFlat.stableUnderComposition φ ψ hφ hψ, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[spMap_comp, Category.assoc]`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `⟨w, hw⟩`. Take `⟨v, hv⟩` from `h i hi`.

Conclude with `⟨spMap ψ ≫ v, by rw [Category.assoc, hv]⟩`.
-/
theorem exists_lifts {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f]
    (S : Type) [CommRing S] (J : Type) (t : J → (Sp S ⟶ Y)) (s : Finset J) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B), φ.FaithfullyFlat ∧
      ∀ i ∈ s, ∃ w : Sp B ⟶ X, w ≫ f = spMap φ ≫ t i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, inferInstance, RingHom.id S, RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j s _ ih =>
    obtain ⟨B, _, φ, hφ, h⟩ := ih
    obtain ⟨C, _, ψ, w, hψ, hw⟩ := exists_lift f B (spMap φ ≫ t j)
    refine ⟨C, inferInstance, ψ.comp φ, RingHom.FaithfullyFlat.stableUnderComposition φ ψ hφ hψ, fun i hi => ?_⟩
    rw [spMap_comp, Category.assoc]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨w, hw⟩
    · obtain ⟨v, hv⟩ := h i hi
      exact ⟨spMap ψ ≫ v, by rw [Category.assoc, hv]⟩

end FlatRoots

/- English proof (translation)
Introduce `hL E _ _ _ H Dw l Xo S _ x0 N k hN _ J _ t _`. Use `haveI := UnivPol.isLocallyNoetherian Xo`. Take `⟨h1, h2, h3, -⟩` from `hL.mulN _ (UnivPol.pol Xo) N hN`. Set `m : Xo.univ.t.G ⟶ Xo.univ.t.G` to `(𝟙 Xo.univ.t.G) ^ N`. Use `haveI : IsFinite m.left := h1`.

Use `haveI : Flat m.left := h2`. Use `haveI : Surjective m.left := h3`. Take `⟨B, _, φ, hφ, h⟩` from `FlatRoots.exists_lifts m.left S J (fun i => (t i).left) Finset.univ`. Use `choose w hw using fun i => h i (Finset.mem_univ i)`. Establish `hb : ∀ i, w i ≫ Xo.univ.t.G.hom = spMap φ ≫ x0` using `fun i => by`.

Rewrite using `[← Over.w m, ← Category.assoc, hw i, Category.assoc, Over.w (t i)]`. Both sides reduce to the same expression. Use `⟨B, inferInstance, φ, fun i => Over.homMk (w i) (hb i), hφ, fun i => ?_⟩` and prove the remaining obligations. Establish `e : ∀ x : ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G, x ^ N = x ≫ m` using `fun x => by`. Rewrite using `[MonObj.comp_pow, Category.comp_id]`.

Rewrite using `[e, Over.comp_left]`. Conclude with `hw i`.
-/
theorem exists_faithfullyFlat_roots :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (N k : ℕ), 0 < N → 0 < k → ∀ (J : Type) [Fintype J] (t : J → (ptO Xo x0 ⟶ Xo.univ.t.G)), (∀ i, t i ^ k = 1) → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ ∀ i, (w i ^ N).left = spMap φ ≫ (t i).left := by
  intro hL E _ _ _ H Dw l Xo S _ x0 N k hN _ J _ t _
  haveI := UnivPol.isLocallyNoetherian Xo
  obtain ⟨h1, h2, h3, -⟩ := hL.mulN _ (UnivPol.pol Xo) N hN
  let m : Xo.univ.t.G ⟶ Xo.univ.t.G := (𝟙 Xo.univ.t.G) ^ N
  haveI : IsFinite m.left := h1
  haveI : Flat m.left := h2
  haveI : Surjective m.left := h3
  obtain ⟨B, _, φ, hφ, h⟩ := FlatRoots.exists_lifts m.left S J (fun i => (t i).left) Finset.univ
  choose w hw using fun i => h i (Finset.mem_univ i)
  have hb : ∀ i, w i ≫ Xo.univ.t.G.hom = spMap φ ≫ x0 := fun i => by
    rw [← Over.w m, ← Category.assoc, hw i, Category.assoc, Over.w (t i)]
    rfl
  refine ⟨B, inferInstance, φ, fun i => Over.homMk (w i) (hb i), hφ, fun i => ?_⟩
  have e : ∀ x : ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G, x ^ N = x ≫ m := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e, Over.comp_left]
  exact hw i

end GlobalTheory
