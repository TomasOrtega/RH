import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsCoveringPairOfIsOpenImmersionOfJointlySurjecti

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.SchemePresentationCover

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private theorem sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  unfold sch; infer_instance

/- English proof (translation)
Substitute using the available equality. A detailed English derivation is pending.
-/
private theorem pb {Y : Scheme.{0}} {A B C D : Y.Opens} (hC : C = A ⊓ B) (hCA : C ≤ A) (hCB : C ≤ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    IsPullback (Y.homOfLE hCA) (Y.homOfLE hCB) (Y.homOfLE hA) (Y.homOfLE hB) := by
  subst hC
  exact isPullback_opens_inf_le hA hB

/- English proof (translation)
Substitute using the available equality. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Prove the first alternative. Prove the second alternative. A detailed English derivation is pending.
-/
private theorem cov (R : Type) [CommRing R] {Y : Scheme.{0}} {A B D : Y.Opens} (hD : D = A ⊔ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    Cover2 R (sch.map (Y.homOfLE hA)) (sch.map (Y.homOfLE hB)) := by
  subst hD
  apply UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective
  · infer_instance
  · infer_instance
  · intro y
    have hy : (y.1 : Y) ∈ A ⊔ B := y.2
    rcases (by simpa using hy : (y.1 : Y) ∈ A ∨ (y.1 : Y) ∈ B) with h | h
    · exact Or.inl ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩
    · exact Or.inr ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩

end UpperTheory.SchemePresentationCover

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem sq_lemma' {T S : Scheme.{0}} (f : T ⟶ S) {P Q : S.Opens} (h : P ≤ Q) (h' : f ⁻¹ᵁ P ≤ f ⁻¹ᵁ Q) :
    T.homOfLE h' ≫ f ∣_ Q = f ∣_ P ≫ S.homOfLE h := by
  rw [← cancel_mono Q.ι]
  simp [morphismRestrict_ι]

open UpperTheory.SchemePresentationCover in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_mayerVietoris_preimage_of_restrictions_vanish :
    ∀ (R : Type) [CommRing R] (F : Shv R) {S : Scheme.{0}} (U V : S.Opens) (n : ℤ)
        (x : H R (sch.obj (U ⊔ V).toScheme) F (n + 1)),
        pull R (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) F (n + 1) x = 0 →
        pull R (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V))) F (n + 1) x = 0 →
        ∃ y : H R (sch.obj (U ⊓ V).toScheme) F n,
          ∀ {T : Scheme.{0}} (f : T ⟶ S) (a : H R (sch.obj (f ⁻¹ᵁ U).toScheme) F n)
            (b : H R (sch.obj (f ⁻¹ᵁ V).toScheme) F n),
            pull R (sch.map (f ∣_ (U ⊓ V))) F n y =
              pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_left))) F n a -
                pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_right))) F n b →
            pull R (sch.map (f ∣_ (U ⊔ V))) F (n + 1) x = 0 := by
  intro R _ F S U V n x hx1 hx2
  obtain ⟨d, hd, hnat⟩ := mayerVietoris R F
  haveI := sch_pres
  have hc := cov R (rfl : U ⊔ V = U ⊔ V) le_sup_left le_sup_right
  obtain ⟨c, hc'⟩ := ((hd _ _ hc n).2.2 x).1 ⟨hx1, hx2⟩
  have P := (pb (rfl : U ⊓ V = U ⊓ V) inf_le_left inf_le_right
    (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch
  refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
  intro T f a b hab
  have hD : f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V := by
    ext; simp
  have hC : f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V := by
    ext; simp
  have hcT := cov R hD (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)
  have PT := (pb hC (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
    (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)).map sch
  have hu : sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ U) ≫ sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have hv : sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ V) ≫ sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have key := hnat (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))))
    (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)))
    (sch.map (f ∣_ (U ⊔ V))) (sch.map (f ∣_ U)) (sch.map (f ∣_ V)) hu hv hcT hc n c
  rw [← hc', key, ((hd (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V)))) hcT n).2.1)]
  refine ⟨a, b, ?_⟩
  have inj : Function.Injective (pull R PT.isoPullback.hom F n) := by
    intro z w h
    have h2 := congrArg (pull R PT.isoPullback.inv F n) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h2
  apply inj
  rw [map_sub, ← pull_comp, ← pull_comp, ← pull_comp, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd, ← hab, ← pull_comp]
  refine congrArg (fun φ => pull R φ F n c) ?_
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
      IsPullback.isoPullback_hom_snd, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
