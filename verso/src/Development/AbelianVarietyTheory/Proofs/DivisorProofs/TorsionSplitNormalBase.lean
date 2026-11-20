import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointTorsionSplitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen

/- English proof (translation)
Introduce `E _ _ _ H X _ t S _ ρ p _ n hN hK hζ hsplit`. Use `haveI : CharZero S.functionField := hK`. Use `haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]`. Establish `hq : p ^ n ≠ 0` using `pow_ne_zero _ (Fact.out : p.Prime).ne_zero`. Establish `hgen (s : S) : spMap (algebraMap (S.presheaf.stalk s) S.functionField) ≫ (S.fromSpecStalk s ≫ ρ) = S.fromSpecStalk (genericPoint S) ≫ ρ`.

Rewrite using `[← Category.assoc]`. Use `congr 1`. Conclude with `Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes s)`. Establish `key (s : S)` using `by haveI := (hN s).1 haveI := (hN s).2`. Conclude with `GlobalTheory.T.integral_point_extension_split E H X t S.functionField _ (p ^ n) hq hζ hsplit (S.presheaf.stalk s) _ (hgen s)`.

Use `haveI := (key (genericPoint S)).1`. Take `⟨N, ⟨eqv⟩⟩` from `Finite.exists_equiv_fin (TorsK t (S.fromSpecStalk (genericPoint S) ≫ ρ) (p ^ n) →* S.functionFieldˣ)`. Establish `hz (y : Sp ↥(intO ℂ_[p]) ⟶ S) : spMap (Scheme.stalkClosedPointTo y).hom ≫ (S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ) = y ≫ ρ`. Rewrite using `[← Category.assoc]`. Conclude with `congrArg (· ≫ ρ) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y)`.

Establish `L (y : Sp ↥(intO ℂ_[p]) ⟶ S)` using `(key (y (IsLocalRing.closedPoint _))).2 p (Scheme.stalkClosedPointTo y).hom (y ≫ ρ) inferInstance (hz y)`. Set `c : Fin N → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar t (y ≫ ρ) (p ^ n)` to `fun j y => Classical.choose ((L y).1 (eqv.symm j))`. Establish `hc (j : Fin N) (y : Sp ↥(intO ℂ_[p]) ⟶ S)` using `Classical.choose_spec ((L y).1 (eqv.symm j))`. Establish `memU (U : S.Opens) (hU : IsAffineOpen U) (x : Γ(S, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ S) (hxy : spMap x ≫ hU.fromSpec = y) : y (IsLocalRing.closedPoint _) ∈ U`. Rewrite using `[← SetLike.mem_coe, ← hU.range_fromSpec, ← hxy]`.

Conclude with `⟨_, rfl⟩`. Use `⟨N, c, fun y c' => ?_, fun U hU g e he => ?_⟩` and prove the remaining obligations. Take `⟨χ, hχ⟩` from `(L y).2.1 c'`. Use `⟨eqv χ, (L y).2.2 χ c' (c (eqv χ) y) hχ ?_⟩` and prove the remaining obligations. Establish `gen : ∀ j, eqv.symm j = χ → InducedBy χ (S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ) (algebraMap (S.presheaf.stalk (y (IsLocalRing.closedPoint _))) S.functionField) (Scheme.stalkClosedPointTo y).hom (c j y)`.

Introduce and unpack `j rfl`. Conclude with `hc j y`. Conclude with `gen _ (eqv.symm_apply_apply χ)`. Distinguish the cases in `hne : Nonempty U swap`. Conclude with `⟨fun _ _ => 0, fun x y hxy _ => absurd ⟨⟨_, memU U hU x y hxy⟩⟩ hne⟩`.

Use `haveI : IsIntegrallyClosed Γ(S, U) := GlobalTheory.LineNorm.Chart.isIntegrallyClosed_sections hN hU`. Use `haveI := functionField_isFractionRing_of_isAffineOpen S U hU`. Establish `hgU : genericPoint S ∈ U`. Take `⟨u⟩` from `hne`. Conclude with `(genericPoint_specializes u.1).mem_open U.isOpen u.2`.

Establish `hchart : spMap (algebraMap Γ(S, U) S.functionField) ≫ (hU.fromSpec ≫ ρ) = S.fromSpecStalk (genericPoint S) ≫ ρ`. Rewrite using `[← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hgU]`. Both sides reduce to the same expression. Use `choose hh hhs using fun j : Fin N => GlobalTheory.T.integral_point_torsion_split E H X t S.functionField _ p n hsplit Γ(S, U) (hU.fromSpec ≫ ρ) hchart g e he.1 (eqv.symm j)`. Use `⟨hh, fun x y hxy j => ?_⟩` and prove the remaining obligations.

Establish `hs` using `memU U hU x y hxy`. Set `φ` to `(S.presheaf.germ U _ hs).hom`. Establish `hu : (algebraMap (S.presheaf.stalk (y (IsLocalRing.closedPoint _))) S.functionField).comp φ = algebraMap Γ(S, U) S.functionField` using `by show (S.presheaf.germ U _ hs ≫ S.presheaf.stalkSpecializes (genericPoint_specializes _)).hom = _`. Rewrite using `[TopCat.Presheaf.germ_stalkSpecializes]`. Both sides reduce to the same expression.

Establish `hx0 : spMap φ ≫ hU.fromSpec ≫ ρ = S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ`. Rewrite using `[← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hs]`. Both sides reduce to the same expression. Establish `heq : (Scheme.stalkClosedPointTo y).hom.comp φ = x`. Apply `GlobalTheory.LineNorm.Chart.ringHom_ext hU` to reduce the goal to its premises.

Rewrite using `[hxy]`. Use `show Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo y).hom.comp φ)) ≫ hU.fromSpec = y`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]`. Use `show _ ≫ hU.fromSpecStalk hs = y`. Rewrite using `[hU.fromSpecStalk_eq_fromSpecStalk hs]`.

Conclude with `Scheme.Spec_stalkClosedPointTo_fromSpecStalk y`. Establish `k : DlogIs t p n (c j y) (fun i => spMap (dualMap ((Scheme.stalkClosedPointTo y).hom.comp φ)) ≫ e i) (fun i => ((Scheme.stalkClosedPointTo y).hom.comp φ) (hh j i))` using `hhs j _ φ _ _ _ _ (c j y) hu hx0 inferInstance (hz y) (hc j y)`. Rewrite `k` using `[heq]`. Conclude with `k`.
-/
theorem charFam_of_normal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (S : Scheme.{0}) [IsIntegral S] (ρ : S ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → CharZero S.functionField → (∃ ζ : S.functionField, IsPrimitiveRoot ζ (p ^ n)) → SplitK t (K := S.functionField) (S.fromSpecStalk (genericPoint S) ≫ ρ) (p ^ n) → CharFam t ρ p n := by
  intro E _ _ _ H X _ t S _ ρ p _ n hN hK hζ hsplit
  classical
  haveI : CharZero S.functionField := hK
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  have hq : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hgen (s : S) : spMap (algebraMap (S.presheaf.stalk s) S.functionField) ≫ (S.fromSpecStalk s ≫ ρ) =
      S.fromSpecStalk (genericPoint S) ≫ ρ := by
    rw [← Category.assoc]
    congr 1
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes s)
  have key (s : S) := by
    haveI := (hN s).1
    haveI := (hN s).2
    exact GlobalTheory.T.integral_point_extension_split E H X t S.functionField _ (p ^ n) hq hζ hsplit (S.presheaf.stalk s) _ (hgen s)
  haveI := (key (genericPoint S)).1
  obtain ⟨N, ⟨eqv⟩⟩ := Finite.exists_equiv_fin (TorsK t (S.fromSpecStalk (genericPoint S) ≫ ρ) (p ^ n) →* S.functionFieldˣ)
  have hz (y : Sp ↥(intO ℂ_[p]) ⟶ S) :
      spMap (Scheme.stalkClosedPointTo y).hom ≫ (S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ) = y ≫ ρ := by
    rw [← Category.assoc]
    exact congrArg (· ≫ ρ) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y)
  have L (y : Sp ↥(intO ℂ_[p]) ⟶ S) := (key (y (IsLocalRing.closedPoint _))).2 p (Scheme.stalkClosedPointTo y).hom (y ≫ ρ)
    inferInstance (hz y)
  let c : Fin N → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar t (y ≫ ρ) (p ^ n) :=
    fun j y => Classical.choose ((L y).1 (eqv.symm j))
  have hc (j : Fin N) (y : Sp ↥(intO ℂ_[p]) ⟶ S) := Classical.choose_spec ((L y).1 (eqv.symm j))
  have memU (U : S.Opens) (hU : IsAffineOpen U) (x : Γ(S, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ S)
      (hxy : spMap x ≫ hU.fromSpec = y) : y (IsLocalRing.closedPoint _) ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec, ← hxy]
    exact ⟨_, rfl⟩
  refine ⟨N, c, fun y c' => ?_, fun U hU g e he => ?_⟩
  · obtain ⟨χ, hχ⟩ := (L y).2.1 c'
    refine ⟨eqv χ, (L y).2.2 χ c' (c (eqv χ) y) hχ ?_⟩
    have gen : ∀ j, eqv.symm j = χ → InducedBy χ (S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ)
        (algebraMap (S.presheaf.stalk (y (IsLocalRing.closedPoint _))) S.functionField) (Scheme.stalkClosedPointTo y).hom
        (c j y) := by
      rintro j rfl
      exact hc j y
    exact gen _ (eqv.symm_apply_apply χ)
  · by_cases hne : Nonempty U
    swap
    · exact ⟨fun _ _ => 0, fun x y hxy _ => absurd ⟨⟨_, memU U hU x y hxy⟩⟩ hne⟩
    haveI : IsIntegrallyClosed Γ(S, U) := GlobalTheory.LineNorm.Chart.isIntegrallyClosed_sections hN hU
    haveI := functionField_isFractionRing_of_isAffineOpen S U hU
    have hgU : genericPoint S ∈ U := by
      obtain ⟨u⟩ := hne
      exact (genericPoint_specializes u.1).mem_open U.isOpen u.2
    have hchart : spMap (algebraMap Γ(S, U) S.functionField) ≫ (hU.fromSpec ≫ ρ) = S.fromSpecStalk (genericPoint S) ≫ ρ := by
      rw [← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hgU]
      rfl
    choose hh hhs using fun j : Fin N =>
      GlobalTheory.T.integral_point_torsion_split E H X t S.functionField _ p n hsplit Γ(S, U) (hU.fromSpec ≫ ρ) hchart g e he.1 (eqv.symm j)
    refine ⟨hh, fun x y hxy j => ?_⟩
    have hs := memU U hU x y hxy
    let φ := (S.presheaf.germ U _ hs).hom
    have hu : (algebraMap (S.presheaf.stalk (y (IsLocalRing.closedPoint _))) S.functionField).comp φ =
        algebraMap Γ(S, U) S.functionField := by
      show (S.presheaf.germ U _ hs ≫ S.presheaf.stalkSpecializes (genericPoint_specializes _)).hom = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    have hx0 : spMap φ ≫ hU.fromSpec ≫ ρ = S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ := by
      rw [← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hs]
      rfl
    have heq : (Scheme.stalkClosedPointTo y).hom.comp φ = x := by
      apply GlobalTheory.LineNorm.Chart.ringHom_ext hU
      rw [hxy]
      show Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo y).hom.comp φ)) ≫ hU.fromSpec = y
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      show _ ≫ hU.fromSpecStalk hs = y
      rw [hU.fromSpecStalk_eq_fromSpecStalk hs]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk y
    have k : DlogIs t p n (c j y) (fun i => spMap (dualMap ((Scheme.stalkClosedPointTo y).hom.comp φ)) ≫ e i)
        (fun i => ((Scheme.stalkClosedPointTo y).hom.comp φ) (hh j i)) :=
      hhs j _ φ _ _ _ _ (c j y) hu hx0 inferInstance (hz y) (hc j y)
    rw [heq] at k
    exact k

end GlobalTheory.HtGen
