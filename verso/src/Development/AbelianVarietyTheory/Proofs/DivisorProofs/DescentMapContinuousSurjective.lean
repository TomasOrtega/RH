import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

/- English proof (translation)
Set `` to `(V.π.residueFieldMap w).hom.toAlgebra`. Establish `: Module.Finite (Y.X.residueField (V.π w)) (V.G.residueField w)` using `residueFieldMap_finite_of_locallyQuasiFinite V.π _`. Conclude with `Module.finrank_pos`.
-/
theorem residueDegree_pos_at (w : V.G) : 0 < V.π.residueDegree w := by
  let := (V.π.residueFieldMap w).hom.toAlgebra
  have : Module.Finite (Y.X.residueField (V.π w)) (V.G.residueField w) :=
    residueFieldMap_finite_of_locallyQuasiFinite V.π _
  exact Module.finrank_pos

/- English proof (translation)
Take `⟨x, hx⟩` from `V.π.surjective (below y)`. Establish `hp : 0 < Nat.card {z : Sp ℂ ⟶ V.G // below z = x ∧ z ≫ V.π = y}` using `(CoverHt.card_lifts V.π x y hx.symm).symm ▸ residueDegree_pos_at V x`. Take `⟨⟨z, -, hz⟩⟩` from `(Nat.card_pos_iff.1 hp).1`. Conclude with `⟨z, hz⟩`.
-/
theorem exists_lift_cx (y : Sp ℂ ⟶ Y.X) : ∃ w : Sp ℂ ⟶ V.G, w ≫ V.π = y := by
  obtain ⟨x, hx⟩ := V.π.surjective (below y)
  have hp : 0 < Nat.card {z : Sp ℂ ⟶ V.G // below z = x ∧ z ≫ V.π = y} :=
    (CoverHt.card_lifts V.π x y hx.symm).symm ▸ residueDegree_pos_at V x
  obtain ⟨⟨z, -, hz⟩⟩ := (Nat.card_pos_iff.1 hp).1
  exact ⟨z, hz⟩

/- English proof (translation)
Introduce `F _ _ Y V e M I ε π hD σ`. Take `⟨hε, hw⟩` from `hD σ`. Establish `hs : spMap σ = spMap (I.ε (ε σ)) ≫ spMap (algebraMap (𝓞 F) F)` using `(congrArg spMap hε.symm).trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _))`. Set `L : CxPts V.p σ → (Sp ℂ ⟶ V.G)` to `fun z => V.pb.lift z.1 (spMap (I.ε (ε σ))) (z.2.trans hs)`. Establish `key (z : CxPts V.p σ) : (I.pt _ (π σ z)).1 = L z ≫ V.π`.

Take `⟨w, hw1, hw2⟩` from `hw z`. Establish `h : w = L z` using `V.pb.hom_ext (by rw [hw1, V.pb.lift_fst]) (by rw [V.pb.lift_snd, ← Category.assoc, hw2]; exact (I.pt _ (π σ z)).2)`. Rewrite using `[← hw2, h]`. Establish `hL : Continuous L`. Rewrite using `[(Points.isEmbedding_of_isPullback (C := ℂ) V.pb).continuous_iff]`.

Establish `h : ((fun z : Sp ℂ ⟶ V.G => (z ≫ V.j, z ≫ (V.π ≫ Y.str))) ∘ L) = fun z => (z.1, spMap (I.ε (ε σ)))`. Use function extensionality and compare the values at `fun z => Prod.ext (V.pb.lift_fst _ _ _) (V.pb.lift_snd _ _ _)`. Rewrite using `[h]`. Conclude with `continuous_subtype_val.prodMk continuous_const`. Use `⟨?_, fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[← (I.pt (ε σ)).comp_continuous_iff]`. Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Conclude with `((Points.continuous_comp V.π).comp hL).congr fun z => (key z).symm`. Take `⟨w, hw'⟩` from `exists_lift_cx V (I.pt _ y).1`. Establish `hwτ : w ≫ V.π ≫ Y.str = spMap (I.ε (ε σ))`.

Rewrite using `[← Category.assoc, hw']`. Conclude with `(I.pt _ y).2`. Establish `hz : (w ≫ V.j) ≫ V.p = spMap σ`. Rewrite using `[Category.assoc, V.pb.w, ← Category.assoc, hwτ, hs]`. Use `⟨⟨w ≫ V.j, hz⟩, (I.pt _).injective (Subtype.ext ?_)⟩` and prove the remaining obligations.

Rewrite using `[key]`. Establish `h : L ⟨w ≫ V.j, hz⟩ = w` using `V.pb.hom_ext (V.pb.lift_fst _ _ _) ((V.pb.lift_snd _ _ _).trans hwτ.symm)`. Rewrite using `[h, hw']`.
-/
theorem isDown_continuous_surjective : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ)
    (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)),
    V.IsDown I ε π → ∀ σ, Continuous (π σ) ∧ Function.Surjective (π σ) := by
  intro F _ _ Y V e M I ε π hD σ
  obtain ⟨hε, hw⟩ := hD σ
  have hs : spMap σ = spMap (I.ε (ε σ)) ≫ spMap (algebraMap (𝓞 F) F) :=
    (congrArg spMap hε.symm).trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _))
  let L : CxPts V.p σ → (Sp ℂ ⟶ V.G) := fun z => V.pb.lift z.1 (spMap (I.ε (ε σ))) (z.2.trans hs)
  have key (z : CxPts V.p σ) : (I.pt _ (π σ z)).1 = L z ≫ V.π := by
    obtain ⟨w, hw1, hw2⟩ := hw z
    have h : w = L z := V.pb.hom_ext (by rw [hw1, V.pb.lift_fst])
      (by rw [V.pb.lift_snd, ← Category.assoc, hw2]; exact (I.pt _ (π σ z)).2)
    rw [← hw2, h]
  have hL : Continuous L := by
    rw [(Points.isEmbedding_of_isPullback (C := ℂ) V.pb).continuous_iff]
    have h : ((fun z : Sp ℂ ⟶ V.G => (z ≫ V.j, z ≫ (V.π ≫ Y.str))) ∘ L) =
        fun z => (z.1, spMap (I.ε (ε σ))) :=
      funext fun z => Prod.ext (V.pb.lift_fst _ _ _) (V.pb.lift_snd _ _ _)
    rw [h]
    exact continuous_subtype_val.prodMk continuous_const
  refine ⟨?_, fun y => ?_⟩
  · rw [← (I.pt (ε σ)).comp_continuous_iff]
    refine continuous_induced_rng.2 ?_
    exact ((Points.continuous_comp V.π).comp hL).congr fun z => (key z).symm
  · obtain ⟨w, hw'⟩ := exists_lift_cx V (I.pt _ y).1
    have hwτ : w ≫ V.π ≫ Y.str = spMap (I.ε (ε σ)) := by
      rw [← Category.assoc, hw']; exact (I.pt _ y).2
    have hz : (w ≫ V.j) ≫ V.p = spMap σ := by
      rw [Category.assoc, V.pb.w, ← Category.assoc, hwτ, hs]
    refine ⟨⟨w ≫ V.j, hz⟩, (I.pt _).injective (Subtype.ext ?_)⟩
    rw [key]
    have h : L ⟨w ≫ V.j, hz⟩ = w := V.pb.hom_ext (V.pb.lift_fst _ _ _) ((V.pb.lift_snd _ _ _).trans hwτ.symm)
    rw [h, hw']

end GlobalTheory.Mean4O.Cover
