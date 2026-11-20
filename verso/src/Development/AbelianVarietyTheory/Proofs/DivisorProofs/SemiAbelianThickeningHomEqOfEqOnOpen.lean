import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOpenPartGroupSchemeProductMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumAgree

/- English proof (translation)
Establish `key : ∀ P : PrimeSpectrum (R ⧸ maximalIdeal R ^ (e + 1)), P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) = maximalIdeal R`. Introduce `P`. Establish `hp : (P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hle : maximalIdeal R ^ (e + 1) ≤ P.asIdeal.comap (Ideal.Quotient.mk _)`. Introduce `r hr`.

Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]`. Conclude with `P.asIdeal.zero_mem`. Establish `hm : maximalIdeal R ≤ _` using `hp.le_of_pow_le hle`. Conclude with `((maximalIdeal.isMaximal R).eq_of_le hp.ne_top hm).symm`. Prove the components needed by the constructor for the conclusion.

Introduce `P Q`. Express the relevant statement in the definitionally equal form `PrimeSpectrum _ at P Q`. Conclude with `PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ((key P).trans (key Q).symm))`.
-/
theorem subsingleton_thick (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    Subsingleton (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) := by
  have key : ∀ P : PrimeSpectrum (R ⧸ maximalIdeal R ^ (e + 1)),
      P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) = maximalIdeal R := by
    intro P
    have hp : (P.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))).IsPrime :=
      Ideal.comap_isPrime _ _
    have hle : maximalIdeal R ^ (e + 1) ≤ P.asIdeal.comap (Ideal.Quotient.mk _) := by
      intro r hr
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]
      exact P.asIdeal.zero_mem
    have hm : maximalIdeal R ≤ _ := hp.le_of_pow_le hle
    exact ((maximalIdeal.isMaximal R).eq_of_le hp.ne_top hm).symm
  constructor
  intro P Q
  change PrimeSpectrum _ at P Q
  exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    ((key P).trans (key Q).symm))

/- English proof (translation)
Introduce `R _ _ _ _ D A G _ _ hG U e x x' hx hx' W y hy hW`. Establish `hH : IsSemiAbelian (thickObj R (maximalIdeal R) e G)` using `IsSemiAbelian.pullback (thick R (maximalIdeal R) e) G hG`. Use `hH.smooth` as an intermediate fact. Establish `hflat : Flat (thickObj R (maximalIdeal R) e G).hom` using `inferInstance`. Set `V : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))` to `Over.mk (W.ι ≫ (thickObj R (maximalIdeal R) e G).hom)`.

Set `j : V ⟶ thickObj R (maximalIdeal R) e G` to `Over.homMk W.ι rfl`. Establish `hsub` using `subsingleton_thick R e`. Establish `hVs : Surjective V.hom` using `⟨fun s => ⟨⟨y, hy⟩, Subsingleton.elim _ _⟩⟩`. Establish `hj : IsOpenImmersion j.left` using `inferInstanceAs (IsOpenImmersion W.ι)`. Establish `hF` using `GlobalTheory.Mum.FlatMul.main _ _ V j hj hflat`.

Establish `hS` using `GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres _ _ V j hj hVs (fun K _ t => GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ _ hH K t)`. Establish `: Epi ((fst V V ≫ j) * (snd V V ≫ j)).left` using `Flat.epi_of_flat_of_surjective _`. Establish `: Epi ((fst V V ≫ j) * (snd V V ≫ j))` using `Over.epi_of_epi_left _`. Establish `hjx : j ≫ x = j ≫ x'` using `Over.OverMorphism.ext hW`. Rewrite using `[← cancel_epi ((fst V V ≫ j) * (snd V V ≫ j)), MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hjx]`.
-/
theorem eq_of_eq_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (e : ℕ) (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), IsMonHom x → IsMonHom x' → ∀ (W : (thickObj R (maximalIdeal R) e G).left.Opens) (y : (thickObj R (maximalIdeal R) e G).left), y ∈ W → W.ι ≫ x.left = W.ι ≫ x'.left → x = x' := by
  intro R _ _ _ _ D A G _ _ hG U e x x' hx hx' W y hy hW
  have hH : IsSemiAbelian (thickObj R (maximalIdeal R) e G) :=
    IsSemiAbelian.pullback (thick R (maximalIdeal R) e) G hG
  have := hH.smooth
  have hflat : Flat (thickObj R (maximalIdeal R) e G).hom := inferInstance
  let V : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :=
    Over.mk (W.ι ≫ (thickObj R (maximalIdeal R) e G).hom)
  let j : V ⟶ thickObj R (maximalIdeal R) e G := Over.homMk W.ι rfl
  have hsub := subsingleton_thick R e
  have hVs : Surjective V.hom := ⟨fun s => ⟨⟨y, hy⟩, Subsingleton.elim _ _⟩⟩
  have hj : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hF := GlobalTheory.Mum.FlatMul.main _ _ V j hj hflat
  have hS := GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres _ _ V j hj hVs
    (fun K _ t => GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ _ hH K t)
  have : Epi ((fst V V ≫ j) * (snd V V ≫ j)).left := Flat.epi_of_flat_of_surjective _
  have : Epi ((fst V V ≫ j) * (snd V V ≫ j)) := Over.epi_of_epi_left _
  have hjx : j ≫ x = j ≫ x' := Over.OverMorphism.ext hW
  rw [← cancel_epi ((fst V V ≫ j) * (snd V V ≫ j)), MonObj.mul_comp, MonObj.mul_comp,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, hjx]

end GlobalTheory.MumAgree
