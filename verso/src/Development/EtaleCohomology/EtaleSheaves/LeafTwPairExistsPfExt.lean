import Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPf
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairExistsPf

variable (q : ℕ) (k : ℤ)

instance resKInj : (res (ZMod q) (tw q k)).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

/- English proof (translation)
Set `_` to `HasDerivedCategory.standard (Shv (ZMod q))`. Set `Φ` to `DerivedCategory.quotientCompQhIso (Shv (ZMod q))`. Take `⟨g, hg⟩` from `(IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj T) L).2 (Φ.hom.app T ≫ inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map a ≫ Φ.inv.app L)`. Take `⟨u, rfl⟩` from `(HomotopyCategory.quotient _ _).map_surjective g`. Use `⟨u, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩` and prove the remaining obligations.

Apply `(IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj S) L).1` to reduce the goal to its premises. Establish `nat : ∀ {X Y : Cx (ZMod q)} (f : X ⟶ Y), DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) = Φ.hom.app X ≫ DerivedCategory.Q.map f ≫ Φ.inv.app Y`. Introduce `X Y f`. Use `Φ.hom.naturality f` as an intermediate fact. Simplify using `only [Functor.comp_map] at this`.

Rewrite using `[← Category.assoc, ← this]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (ε ≫ u)) = _`. Rewrite using `[Functor.map_comp, Functor.map_comp, hg, nat ε, nat a]`. Simplify using `only [Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id_assoc]`.
-/
theorem ext_homotopy {S T L : Cx (ZMod q)} (ε : S ⟶ T) [QuasiIso ε] (a : S ⟶ L) [L.IsKInjective] :
    ∃ u : T ⟶ L, Nonempty (Homotopy (ε ≫ u) a) := by
  let _ := HasDerivedCategory.standard (Shv (ZMod q))
  let Φ := DerivedCategory.quotientCompQhIso (Shv (ZMod q))
  obtain ⟨g, hg⟩ := (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj T) L).2
    (Φ.hom.app T ≫ inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map a ≫ Φ.inv.app L)
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨u, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj S) L).1
  have nat : ∀ {X Y : Cx (ZMod q)} (f : X ⟶ Y), DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) =
      Φ.hom.app X ≫ DerivedCategory.Q.map f ≫ Φ.inv.app Y := by
    intro X Y f
    have := Φ.hom.naturality f
    simp only [Functor.comp_map] at this
    rw [← Category.assoc, ← this]
    simp
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (ε ≫ u)) = _
  rw [Functor.map_comp, Functor.map_comp, hg, nat ε, nat a]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id_assoc]

/- English proof (translation)
Introduce `q _ k T e ⟨_, ε, hε, he⟩`. Take `⟨u, ⟨H⟩⟩` from `ext_homotopy q (ε := ε) (a := resAug (tw q k))`. Use `⟨u, fun U ζ => ?_⟩` and prove the remaining obligations. Establish `h0 : ε.f 0 ≫ u.f 0 = (resAug (tw q k)).f 0`. Establish `hc` using `H.comm 0`.

Rewrite `hc` using `[dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp), prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]`. Establish `z1 : IsZero ((sgl (tw q k)).X 1)` using `HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)`. Establish `z2 : IsZero ((res (ZMod q) (tw q k)).X (-1))`. Unfold `res InjectiveResolution.cochainComplex`. Conclude with `HomologicalComplex.isZero_extend_X _ _ _ (by`.

Introduce `n hn`. Express the relevant statement in the definitionally equal form `((n : ℕ) : ℤ) = -1 at hn`. Use the proof step `omega)`. Establish `e1 : H.hom 1 0 = 0` using `z1.eq_of_src _ _`. Establish `e2 : H.hom 0 (-1) = 0` using `z2.eq_of_tgt _ _`.

Rewrite `hc` using `[e1, e2]`. Simplify using `using hc`. Rewrite using `[← he U ζ, map_map, map_map, h0]`. Both sides reduce to the same expression.
-/
theorem leafTwResExt : LeafTwResExt := by
  intro q _ k T e ⟨_, ε, hε, he⟩
  obtain ⟨u, ⟨H⟩⟩ := ext_homotopy q (ε := ε) (a := resAug (tw q k))
  refine ⟨u, fun U ζ => ?_⟩
  have h0 : ε.f 0 ≫ u.f 0 = (resAug (tw q k)).f 0 := by
    have hc := H.comm 0
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hc
    have z1 : IsZero ((sgl (tw q k)).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
    have z2 : IsZero ((res (ZMod q) (tw q k)).X (-1)) := by
      unfold res InjectiveResolution.cochainComplex
      exact HomologicalComplex.isZero_extend_X _ _ _ (by
        intro n hn
        change ((n : ℕ) : ℤ) = -1 at hn
        omega)
    have e1 : H.hom 1 0 = 0 := z1.eq_of_src _ _
    have e2 : H.hom 0 (-1) = 0 := z2.eq_of_tgt _ _
    rw [e1, e2] at hc
    simpa using hc
  rw [← he U ζ, map_map, map_map, h0]
  rfl

/- English proof (translation)
The claim follows from `LeafTwPairExists_of h1 h2 leafTwResExt`.
-/
theorem LeafTwPairExists_of' (h1 : LeafTwTensEx) (h2 : LeafTwTensRes) : LateralTheory.E.CupProductRingLaws.LeafTwPairExists :=
  LeafTwPairExists_of h1 h2 leafTwResExt

end LateralTheory.E.LeafTwPairExistsPf
