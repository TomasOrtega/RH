import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieCarrier

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

def epsHom (φ : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') : epsAt x' ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualMap φ))) (by
    subst h
    show _ ≫ _ ≫ x = _ ≫ _ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem dualMap_epsMul (φ : R →+* R') (c : R) :
    (dualMap φ).comp (epsMul c) = (epsMul (φ c)).comp (dualMap φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [dualMap, epsMul, mul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem surjective_fst :
    Function.Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)) := by
  intro p
  have hn : ∀ m : R, (TrivSqZeroExt.inr m : TrivSqZeroExt R R) ∈ p.asIdeal := fun m =>
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact p.asIdeal.zero_mem)
  have : p.asIdeal.IsPrime := p.isPrime
  refine ⟨⟨Ideal.comap (TrivSqZeroExt.inlHom R R) p.asIdeal, Ideal.IsPrime.comap _⟩, ?_⟩
  change PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom _ = p
  ext y
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_comap]
  change TrivSqZeroExt.inl y.fst ∈ p.asIdeal ↔ y ∈ p.asIdeal
  have hy : TrivSqZeroExt.inl y.fst = y - TrivSqZeroExt.inr y.snd :=
    eq_sub_of_add_eq (TrivSqZeroExt.inl_fst_add_inr_snd_eq y)
  rw [hy]
  constructor
  · intro h
    have := p.asIdeal.add_mem h (hn y.snd)
    rwa [sub_add_cancel] at this
  · intro h
    exact p.asIdeal.sub_mem h (hn y.snd)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem tan_ext {G : Over S} [GrpObj G] (φ : R →+* R') (hφ : Function.Injective φ)
    (x : Spec (CommRingCat.of R) ⟶ S) (v v' : epsAt x ⟶ G) (hv : IsTanAt G x v) (hv' : IsTanAt G x v')
    (h : Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v'.left) :
    v = v' := by
  apply Over.OverMorphism.ext
  have hinj : Function.Injective ((TrivSqZeroExt.fstHom R R R).toRingHom.prod (dualMap φ)) := by
    intro a b hab
    have h2 : dualMap φ a = dualMap φ b := congrArg Prod.snd hab
    have h3 := congrArg TrivSqZeroExt.fst h2
    have h4 := congrArg TrivSqZeroExt.snd h2
    simp [dualMap, hφ.eq_iff] at h3 h4
    exact TrivSqZeroExt.ext h3 h4
  unfold IsTanAt at hv hv'
  exact GlobalTheory.CompanionTheory.Ar.LieEx.joint_epi _ _ hinj surjective_fst v.left v'.left (hv.trans hv'.symm) h

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem genMap_fromSpecStalk (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have hxW : genPt ξ ∈ W := p.2.mem_open W.isOpen hyW
  have key : Spec.map (X.presheaf.stalkSpecializes p.2) ≫ X.fromSpecStalk p.1 =
      X.fromSpecStalk (genPt ξ) := by
    rw [← hW.fromSpecStalk_eq_fromSpecStalk hyW, ← hW.fromSpecStalk_eq_fromSpecStalk hxW]
    simp only [IsAffineOpen.fromSpecStalk]
    rw [← Category.assoc, ← Spec.map_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have e1 : Spec.map (CommRingCat.ofHom (genMap ξ p)) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes p.2) :=
    Spec.map_comp _ _
  rw [e1, Category.assoc]
  exact (congrArg (fun f => Spec.map (Scheme.stalkClosedPointTo ξ) ≫ f) key).trans
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

/- English proof (translation)
Reduce the argument to an intermediate assertion. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem span_ext {G : Over S} [GrpObj G] (φ : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S)
    (x' : Spec (CommRingCat.of R') ⟶ S) (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x')
    {E : Type} [AddCommGroup E] [Module R' E] (M : LieModel G x' E) (e : E)
    (he : e ∈ Submodule.span φ.range {e | ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧
      (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left}) :
    ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left := by
  suffices H : ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧ M.pt e = epsHom φ x x' h ≫ v by
    obtain ⟨v, hv, hev⟩ := H
    exact ⟨v, hv, by rw [hev]; rfl⟩
  induction he using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨v, hv, hav⟩ := ha
    exact ⟨v, hv, Over.OverMorphism.ext hav⟩
  | zero =>
    refine ⟨1, (GlobalTheory.CompanionTheory.Ar.LieEx.isTanAt_iff x G 1).mpr (MonObj.comp_one _), ?_⟩
    rw [MonObj.comp_one]
    have h0 : M.pt 0 * 1 = M.pt 0 * M.pt 0 := by rw [_root_.mul_one, ← M.add, add_zero]
    exact (mul_left_cancel h0).symm
  | add a b _ _ ha hb =>
    obtain ⟨v, hv, hva⟩ := ha
    obtain ⟨w, hw, hwb⟩ := hb
    refine ⟨v * w, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.LieEx.isTanAt_iff] at hv hw ⊢
      rw [MonObj.comp_mul, hv, hw, _root_.mul_one]
    · rw [M.add, hva, hwb, MonObj.comp_mul]
  | smul a b _ hb =>
    obtain ⟨v, hv, hvb⟩ := hb
    obtain ⟨r, hr⟩ := a
    obtain ⟨c, rfl⟩ := RingHom.mem_range.mp hr
    refine ⟨GlobalTheory.CompanionTheory.Ar.LieEx.hom x (c • LinearMap.id) ≫ v, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.LieEx.isTanAt_iff] at hv ⊢
      rw [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieEx.zsec_hom]
      exact hv
    · apply Over.OverMorphism.ext
      change (M.pt ((φ c) • b)).left = _
      rw [M.smul, hvb]
      have e2 : Spec.map (CommRingCat.ofHom (epsMul (φ c))) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) =
          Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) := by
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
          dualMap_epsMul]
      change Spec.map (CommRingCat.ofHom (epsMul (φ c))) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left =
        Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) ≫ v.left
      rw [← Category.assoc, e2, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.LieCarrier

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem lieLat_carrier (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    (∀ e, e ∈ M.lat p ↔ ∃ v, M.Extends p e v) ∧
      (IsCptGen ξ → Smooth G.hom → ∀ e v v', M.Extends p e v → M.Extends p e v' → v = v') := by
  refine ⟨fun e => ⟨fun he => ?_, fun hv => Submodule.subset_span hv⟩, ?_⟩
  · exact LieCarrier.span_ext (genMap ξ p) (X.fromSpecStalk p.1) ξ
      (LieCarrier.genMap_fromSpecStalk p) M e he
  · intro hgen _ e v v' hv hv'
    exact LieCarrier.tan_ext (genMap ξ p) (hgen.inj p) _ v v' hv.1 hv'.1 (hv.2.symm.trans hv'.2)

end GlobalTheory.CompanionTheory.Ar
