import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueExtensionOfForallNormLeOne

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechRoot

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gen_res {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} [Nonempty V] [Nonempty W]
    (h : W ≤ V) (s : Γ(X, V)) :
    (X.germToFunctionField W).hom ((X.presheaf.map (homOfLE h).op).hom s) = (X.germToFunctionField V).hom s :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ s

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem nonempty_inf {X : Scheme.{0}} [IsIntegral X] (V W : X.Opens) [hV : Nonempty V] [hW : Nonempty W] :
    Nonempty (V ⊓ W : X.Opens) := by
  obtain ⟨⟨v, hv⟩⟩ := hV
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen ⟨v, hv⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_section_of_pow {X : Scheme.{0}} [IsIntegral X] (hN : ∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b))
    {l : ℕ} (hl : 0 < l) (V : X.Opens) [Nonempty V] (f : Γ(X, V)) (t : X.functionField)
    (ht : t ^ l = (X.germToFunctionField V).hom f) : ∃ s : Γ(X, V), (X.germToFunctionField V).hom s = t := by
  refine IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  refine exists_germToFunctionField_eq_of_mem_range_stalk ?_ hx
  haveI := hN x
  refine IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow hl ?_)
  rw [ht, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx f]
  exact isIntegral_algebraMap

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem charP_functionField {X : Scheme.{0}} [IsIntegral X] (l : ℕ) [Fact l.Prime] (h : (l : Γ(X, ⊤)) = 0) :
    CharP X.functionField l := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
  rw [← map_natCast (X.germToFunctionField ⊤).hom, h, map_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_root : ∀ (X : Scheme.{0}) [IsIntegral X], (∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b)) → ∀ (l : ℕ) [Fact l.Prime], (l : Γ(X, ⊤)) = 0 → ∀ (J : Type) (U : J → X.Opens) (f : ∀ j, Γ(X, U j)) (n : ∀ j j', Γ(X, U j ⊓ U j')), (∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (f j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (f j') = n j j' ^ l) → ∀ (i : J) (b : X) (hb : b ∈ U i) (h : FractionRing (X.presheaf.stalk b)), h ^ l = algebraMap (X.presheaf.stalk b) _ ((X.presheaf.germ (U i) b hb).hom (f i)) → ∃ H : ∀ j, Γ(X, U j), ∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (H j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (H j') = n j j' := by
  intro X _ hN l _ hl J U f n hf i b hb h hh
  haveI := charP_functionField l hl
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  haveI : Nonempty (U i) := ⟨⟨b, hb⟩⟩
  let e := FractionRing.algEquiv (X.presheaf.stalk b) X.functionField
  have he : e h ^ l = (X.germToFunctionField (U i)).hom (f i) := by
    rw [← map_pow, hh, AlgEquiv.commutes]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hb (f i)
  have hg : ∀ j j' [Nonempty (U j)] [Nonempty (U j')] [Nonempty (U j ⊓ U j' : X.Opens)],
      (X.germToFunctionField (U j)).hom (f j) - (X.germToFunctionField (U j')).hom (f j') =
        (X.germToFunctionField (U j ⊓ U j')).hom (n j j') ^ l := by
    intro j j' _ _ _
    rw [← map_pow, ← hf, map_sub, gen_res, gen_res]
  have ex : ∀ j, ∃ H : Γ(X, U j), ∀ [Nonempty (U j)],
      (X.germToFunctionField (U j)).hom H ^ l = (X.germToFunctionField (U j)).hom (f j) := by
    intro j
    by_cases hj : Nonempty (U j)
    · haveI := nonempty_inf (U j) (U i)
      have ht : (e h + (X.germToFunctionField (U j ⊓ U i)).hom (n j i)) ^ l =
          (X.germToFunctionField (U j)).hom (f j) := by
        rw [add_pow_char, he, ← hg, add_sub_cancel]
      obtain ⟨s, hs⟩ := exists_section_of_pow hN hl0 (U j) (f j) _ ht
      exact ⟨s, by intro _; rw [hs, ht]⟩
    · exact ⟨0, by intro h; exact absurd h hj⟩
  choose H hH using ex
  refine ⟨H, fun j j' => ?_⟩
  by_cases hj : Nonempty (U j ⊓ U j' : X.Opens)
  · obtain ⟨⟨z, hz⟩⟩ := id hj
    haveI : Nonempty (U j) := ⟨⟨z, hz.1⟩⟩
    haveI : Nonempty (U j') := ⟨⟨z, hz.2⟩⟩
    apply X.germToFunctionField_injective (U j ⊓ U j')
    apply frobenius_inj X.functionField l
    change (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l = (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l
    rw [map_sub, gen_res, gen_res, sub_pow_char, hH, hH, hg]
  · exact fn_ext (V := U j ⊓ U j') fun x hx => absurd ⟨⟨x, hx⟩⟩ hj

end GlobalTheory.CechRoot
