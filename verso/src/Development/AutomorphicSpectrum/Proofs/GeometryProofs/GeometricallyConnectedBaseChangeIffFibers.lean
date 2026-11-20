import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Approx

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
private theorem eq_of_sp_complex_pts {K : Type} [Field K] (a b : ↥(Sp K)) : a = b := by
  revert a b
  change ∀ a b : PrimeSpectrum K, a = b
  intro a b
  exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm)

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
private theorem nonempty_sp (K : Type) [Field K] : Nonempty ↥(Sp K) := by
  change Nonempty (PrimeSpectrum K)
  infer_instance

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem connectedSpace_pullback_of_fieldHom {k K K' : Type} [CommRing k] [Field K] [Field K']
    {X : Scheme.{0}} (p : X ⟶ Sp k) (f : k →+* K) (j : K →+* K')
    (h : ConnectedSpace ↥(pullback p (spMap (j.comp f)))) :
    ConnectedSpace ↥(pullback p (spMap f)) := by
  rw [spMap_comp] at h
  let e := pullbackLeftPullbackSndIso p (spMap f) (spMap j)
  let g : pullback p (spMap j ≫ spMap f) ⟶ pullback p (spMap f) :=
    e.inv ≫ pullback.fst (pullback.snd p (spMap f)) (spMap j)
  refine Function.Surjective.connectedSpace (f := ⇑g) ?_ g.continuous
  intro z
  obtain ⟨y'⟩ := nonempty_sp K'
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd p (spMap f)) (g := spMap j) z y' (eq_of_sp_complex_pts _ _)
  refine ⟨e.hom w, ?_⟩
  have h2 : e.hom ≫ g = pullback.fst (pullback.snd p (spMap f)) (spMap j) := by
    simp [g, e]
  rw [← hw, ← h2]
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem connectedSpace_of_iso {A B : Scheme.{0}} (e : A ≅ B) [ConnectedSpace A] :
    ConnectedSpace B := by
  refine Function.Surjective.connectedSpace (f := ⇑e.hom) (fun b => ⟨e.inv b, ?_⟩) e.hom.continuous
  rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem geometricallyConnected_pullback_snd_iff {X S T : Scheme.{0}} (p : X ⟶ S) (g : T ⟶ S) :
    GeometricallyConnected (pullback.snd p g) ↔
      ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ T),
        ConnectedSpace ↥(pullback p (y ≫ g)) := by
  rw [geometricallyConnected_iff]
  constructor
  · intro H K _ y
    haveI : ConnectedSpace ↥(pullback (pullback.snd p g) y) :=
      H y (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    exact connectedSpace_of_iso (pullbackLeftPullbackSndIso p g y)
  · intro H K _ y Z fst snd hpb
    haveI := H K y
    exact connectedSpace_of_iso (hpb.isoPullback ≪≫ pullbackLeftPullbackSndIso p g y).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem geometricallyConnected_pullback_snd_spMap_iff {k R : Type} [CommRing k] [CommRing R]
    {X : Scheme.{0}} (p : X ⟶ Sp k) (a : k →+* R) :
    GeometricallyConnected (pullback.snd p (spMap a)) ↔
      ∀ (K : Type) [Field K] (φ : R →+* K), ConnectedSpace ↥(pullback p (spMap (φ.comp a))) := by
  rw [geometricallyConnected_pullback_snd_iff]
  constructor
  · intro H K _ φ
    have := H K (spMap φ)
    rwa [← spMap_comp] at this
  · intro H K _ y
    obtain ⟨φ, rfl⟩ : ∃ φ : R →+* K, spMap φ = y :=
      ⟨(Spec.preimage (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))).hom, Spec.map_preimage _⟩
    rw [← spMap_comp]
    exact H K φ

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem exists_field_amalgam {F K₁ K₂ : Type} [Field F] [Field K₁] [Field K₂]
    (a : F →+* K₁) (b : F →+* K₂) :
    ∃ (L : Type) (_ : Field L) (i : K₁ →+* L) (j : K₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  haveI : Nontrivial (K₁ ⊗[F] K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K₁ ⊗[F] K₂)
  letI := Ideal.Quotient.field m
  refine ⟨K₁ ⊗[F] K₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext x
  simp only [RingHom.comp_apply]
  congr 1
  exact (Algebra.TensorProduct.algebraMap_apply x).symm.trans (Algebra.TensorProduct.algebraMap_apply' x)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem exists_residueField_lift {k K : Type} [CommRing k] [Field K] (f : k →+* K)
    (x : PrimeSpectrum k) (hx : x.asIdeal = RingHom.ker f) :
    ∃ ψ : x.asIdeal.ResidueField →+* K, ψ.comp (algebraMap k x.asIdeal.ResidueField) = f := by
  have h2 : x.asIdeal.primeCompl ≤ Submonoid.comap f (IsUnit.submonoid K) := by
    intro r hr
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    refine isUnit_iff_ne_zero.mpr fun h0 => Ideal.mem_primeCompl_iff.mp hr ?_
    rw [hx]
    exact RingHom.mem_ker.mpr h0
  refine ⟨Ideal.ResidueField.lift x.asIdeal f hx.le h2, ?_⟩
  ext r
  exact Ideal.ResidueField.lift_algebraMap x.asIdeal f hx.le h2 r

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem geometricallyConnected_pullback_snd_spMap_iff_residueField :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k),
      GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔
        ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)),
          GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  intro k V _ _ _ X p
  rw [geometricallyConnected_pullback_snd_spMap_iff]
  constructor
  · rintro H x ⟨q, rfl⟩
    rw [geometricallyConnected_pullback_snd_spMap_iff]
    intro K _ ψ
    have hker : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker ((algebraMap V q.asIdeal.ResidueField).comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
      rfl
    obtain ⟨ψ', hψ'⟩ := exists_residueField_lift _ _ hker
    obtain ⟨L, hL, i, j', hij⟩ := exists_field_amalgam ψ ψ'
    apply connectedSpace_pullback_of_fieldHom p _ i
    have e : i.comp (ψ.comp (algebraMap k (PrimeSpectrum.comap (algebraMap k V) q).asIdeal.ResidueField)) =
        (j'.comp (algebraMap V q.asIdeal.ResidueField)).comp (algebraMap k V) := by
      rw [← RingHom.comp_assoc, hij, RingHom.comp_assoc, hψ', RingHom.comp_assoc]
    rw [e]
    exact H L _
  · intro H K _ φ
    haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    let q : PrimeSpectrum V := ⟨RingHom.ker φ, inferInstance⟩
    have hx : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker (φ.comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker]
      rfl
    obtain ⟨ψ, hψ⟩ := exists_residueField_lift _ _ hx
    have := (geometricallyConnected_pullback_snd_spMap_iff p _).mp (H _ ⟨q, rfl⟩) K ψ
    rwa [hψ] at this

end GlobalTheory.CompanionTheory.Ar.Approx
