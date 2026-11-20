import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersDefs
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.OrbitInvariants
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyPlaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal MulAction

universe u

noncomputable section

section PlaceAction

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  {v : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Use `set w := placeOfAlgHom j`. Establish `h : w.1 = τ • (τ⁻¹ • w).1`. Rewrite using `[coe_smul_placesOver, smul_inv_smul]`. Set `c : (τ⁻¹ • w).1.adicCompletion L →ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F)` to `(completionEmbeddingOfAlgHom j).comp (galEquiv v τ (τ⁻¹ • w).1 w.1 h).toAlgHom`. Use `(eq_placeOfAlgHom (j.comp (τ : L →ₐ[F] L)) c fun x => ?_).symm` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `completionEmbeddingOfAlgHom j (galEquiv v τ (τ⁻¹ • w).1 w.1 h (algebraMap L _ x)) = j (τ x)`. Rewrite using `[galEquiv_algebraMap, completionEmbeddingOfAlgHom_algebraMap]`.
-/
theorem placeOfAlgHom_comp_algEquiv (j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))
    (τ : L ≃ₐ[F] L) :
    placeOfAlgHom (j.comp (τ : L →ₐ[F] L)) = τ⁻¹ • placeOfAlgHom j := by
  set w := placeOfAlgHom j
  have h : w.1 = τ • (τ⁻¹ • w).1 := by
    rw [coe_smul_placesOver, smul_inv_smul]
  let c : (τ⁻¹ • w).1.adicCompletion L →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F) :=
    (completionEmbeddingOfAlgHom j).comp (galEquiv v τ (τ⁻¹ • w).1 w.1 h).toAlgHom
  refine (eq_placeOfAlgHom (j.comp (τ : L →ₐ[F] L)) c fun x => ?_).symm
  change completionEmbeddingOfAlgHom j (galEquiv v τ (τ⁻¹ • w).1 w.1 h (algebraMap L _ x)) = j (τ x)
  rw [galEquiv_algebraMap, completionEmbeddingOfAlgHom_algebraMap]

end PlaceAction

section Finite

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) [IsGalois F L]
  (ιs : ∀ v : S, Ω →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

/- English proof (translation)
Use extensionality with `l`. Express the relevant statement in the definitionally equal form `ιs v ((((σ * x)⁻¹ : galUnramifiedOutside F Ω S) (gsEmbedding hL l) : maxUnramifiedOutside F Ω S) : Ω) = ιs v ((((x⁻¹ : galUnramifiedOutside F Ω S) (gsEmbedding hL ((gsRestrictGal hL σ)⁻¹ l))) : maxUnramifiedOutside F Ω S) : Ω)`. Rewrite using `[← map_inv, gsEmbedding_gsRestrictGal, mul_inv_rev, AlgEquiv.mul_apply]`.
-/
theorem gsLocalEmbedding_mul_left (v : S) (σ x : galUnramifiedOutside F Ω S) :
    gsLocalEmbedding hL ιs v (σ * x) =
      (gsLocalEmbedding hL ιs v x).comp (((gsRestrictGal hL σ)⁻¹ : L ≃ₐ[F] L) : L →ₐ[F] L) := by
  ext l
  change ιs v ((((σ * x)⁻¹ : galUnramifiedOutside F Ω S) (gsEmbedding hL l) :
      maxUnramifiedOutside F Ω S) : Ω) = ιs v ((((x⁻¹ : galUnramifiedOutside F Ω S)
      (gsEmbedding hL ((gsRestrictGal hL σ)⁻¹ l))) : maxUnramifiedOutside F Ω S) : Ω)
  rw [← map_inv, gsEmbedding_gsRestrictGal, mul_inv_rev, AlgEquiv.mul_apply]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = placeOfAlgHom (gsLocalEmbedding hL ιs v (σ * x))`. Rewrite using `[gsLocalEmbedding_mul_left, placeOfAlgHom_comp_algEquiv, inv_inv]`.
-/
theorem gsRestrictGal_smul_gsLocalPlace (v : S) (σ x : galUnramifiedOutside F Ω S) :
    gsRestrictGal hL σ • gsLocalPlace hL ιs v x = gsLocalPlace hL ιs v (σ * x) := by
  change _ = placeOfAlgHom (gsLocalEmbedding hL ιs v (σ * x))
  rw [gsLocalEmbedding_mul_left, placeOfAlgHom_comp_algEquiv, inv_inv]

/- English proof (translation)
Rewrite using `[mem_stabilizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hτ`. Take `⟨σ, rfl⟩` from `gsRestrictGal_surjective hL τ`. Rewrite `hτ` using `[gsRestrictGal_smul_gsLocalPlace, mul_one]`.

Take `⟨g, hg⟩` from `exists_algEquiv_of_placeOfAlgHom_eq _ _ hτ`. Use `⟨g, (gsRestrictGal_eq_iff hL _ _).2 fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[gsEmbedding_gsRestrictGal]`. Establish `h1` using `hg (gsRestrictGal hL σ l)`. Rewrite `h1` using `[gsLocalEmbedding_apply, gsLocalEmbedding_apply, inv_one, AlgEquiv.one_apply, gsEmbedding_gsRestrictGal, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply, ← gsFinFamily_apply]`.

Conclude with `(Subtype.ext ((ιs v).injective h1)).symm`. Introduce and unpack `⟨g, rfl⟩`. Express the relevant statement in the definitionally equal form `gsRestrictGal hL (gsFinFamily S ιs v g) • _ = _`. Rewrite using `[gsRestrictGal_smul_gsLocalPlace]`. Establish `h` using `gsLocalPlace_mul hL ιs v 1 (one_mem _) g`.

Rewrite `h` using `[mul_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem mem_stabilizer_gsLocalPlace_iff (v : S) (τ : L ≃ₐ[F] L) :
    τ ∈ MulAction.stabilizer (L ≃ₐ[F] L) (gsLocalPlace hL ιs v 1) ↔ τ ∈ gsDecompGroup hL ιs v := by
  rw [mem_stabilizer_iff]
  constructor
  · intro hτ
    obtain ⟨σ, rfl⟩ := gsRestrictGal_surjective hL τ
    rw [gsRestrictGal_smul_gsLocalPlace, mul_one] at hτ
    obtain ⟨g, hg⟩ := exists_algEquiv_of_placeOfAlgHom_eq _ _ hτ
    refine ⟨g, (gsRestrictGal_eq_iff hL _ _).2 fun l => ?_⟩
    rw [gsEmbedding_gsRestrictGal]
    have h1 := hg (gsRestrictGal hL σ l)
    rw [gsLocalEmbedding_apply, gsLocalEmbedding_apply, inv_one, AlgEquiv.one_apply,
      gsEmbedding_gsRestrictGal, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply,
      ← gsFinFamily_apply] at h1
    exact (Subtype.ext ((ιs v).injective h1)).symm
  · rintro ⟨g, rfl⟩
    change gsRestrictGal hL (gsFinFamily S ιs v g) • _ = _
    rw [gsRestrictGal_smul_gsLocalPlace]
    have h := gsLocalPlace_mul hL ιs v 1 (one_mem _) g
    rwa [mul_one, one_mul] at h

/- English proof (translation)
The claim follows from `Subgroup.ext fun τ => mem_stabilizer_gsLocalPlace_iff hL ιs v τ`.
-/
theorem stabilizer_gsLocalPlace (v : S) :
    MulAction.stabilizer (L ≃ₐ[F] L) (gsLocalPlace hL ιs v 1) = gsDecompGroup hL ιs v :=
  Subgroup.ext fun τ => mem_stabilizer_gsLocalPlace_iff hL ιs v τ

omit [NumberField F] [NumberField L] [IsGalois F L] in

/- English proof (translation)
Take `⟨v, hv, hlies⟩` from `hw`. Conclude with `⟨v, hv, (τ • (⟨w, hlies⟩ : PlacesOver L v)).2⟩`.
-/
theorem galSmul_mem_placesOver (τ : L ≃ₐ[F] L) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ placesOver S) : τ • w ∈ placesOver S := by
  obtain ⟨v, hv, hlies⟩ := hw
  exact ⟨v, hv, (τ • (⟨w, hlies⟩ : PlacesOver L v)).2⟩

variable (S) in

abbrev placesOverAction : MulAction (L ≃ₐ[F] L) (placesOver S : Set (HeightOneSpectrum (𝓞 L))) :=
  stableMulAction (placesOver S) fun τ _ hw => galSmul_mem_placesOver τ hw

def gsPlaceAbove (v : S) : (placesOver S : Set (HeightOneSpectrum (𝓞 L))) :=
  ⟨(gsLocalPlace hL ιs v 1).1, v.1, v.2, (gsLocalPlace hL ιs v 1).2⟩

/- English proof (translation)
Set `_` to `placesOverAction (L := L) S`. Rewrite using `[← stabilizer_gsLocalPlace hL ιs v]`. Use extensionality with `τ`. Rewrite using `[mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff, Subtype.ext_iff]`. Both sides reduce to the same expression.
-/
theorem stabilizer_gsPlaceAbove (v : S) :
    let _ := placesOverAction (L := L) S
    MulAction.stabilizer (L ≃ₐ[F] L) (gsPlaceAbove hL ιs v) = gsDecompGroup hL ιs v := by
  let _ := placesOverAction (L := L) S
  rw [← stabilizer_gsLocalPlace hL ιs v]
  ext τ
  rw [mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff, Subtype.ext_iff]
  rfl

omit [IsGalois F L] in

/- English proof (translation)
Use `Finite.of_surjective (fun p : Σ v : S, PlacesOver L (v : HeightOneSpectrum (𝓞 F)) => (⟨p.2.1, p.1.1, p.1.2, p.2.2⟩ : (placesOver S : Set (HeightOneSpectrum (𝓞 L))))) ?_` and prove the remaining obligations. Introduce and unpack `⟨w, v, hv, hw⟩`. Conclude with `⟨⟨⟨v, hv⟩, ⟨w, hw⟩⟩, rfl⟩`.
-/
theorem finite_placesOver [Finite S] :
    Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L))) := by
  refine Finite.of_surjective (fun p : Σ v : S, PlacesOver L (v : HeightOneSpectrum (𝓞 F)) =>
    (⟨p.2.1, p.1.1, p.1.2, p.2.2⟩ : (placesOver S : Set (HeightOneSpectrum (𝓞 L))))) ?_
  rintro ⟨w, v, hv, hw⟩
  exact ⟨⟨⟨v, hv⟩, ⟨w, hw⟩⟩, rfl⟩

/- English proof (translation)
Set `_` to `placesOverAction (L := L) S`. Prove the components needed by the constructor for the conclusion. Introduce `v v' h`. Take `⟨τ, hτ⟩` from `Quotient.exact h`. Establish `hτ' : τ • (gsPlaceAbove hL ιs v').1 = (gsPlaceAbove hL ιs v).1` using `congrArg Subtype.val hτ`.

Establish `e1` using `eq_placeBelow_of_liesOver (K := F) (gsLocalPlace hL ιs v 1).2`. Establish `e2` using `eq_placeBelow_of_liesOver (K := F) (gsLocalPlace hL ιs v' 1).2`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[e1, e2]`. Express the relevant statement in the definitionally equal form `placeBelow (gsPlaceAbove hL ιs v).1 = placeBelow (gsPlaceAbove hL ιs v').1`.

Rewrite using `[← hτ', placeBelow_smul]`. Introduce `ω`. Proceed by induction on `ω using Quotient.inductionOn with`. Consider the case `h w`. Take `⟨v0, hv0, hw⟩` from `w.2`.

Set `v : S` to `⟨v0, hv0⟩`. Take `⟨τ, hτ⟩` from `MulAction.exists_smul_eq (L ≃ₐ[F] L) (gsLocalPlace hL ιs v 1) (⟨w.1, hw⟩ : PlacesOver L v0)`. Use `⟨v, Quotient.sound ⟨τ⁻¹, ?_⟩⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `τ⁻¹ • w.1 = (gsLocalPlace hL ιs v 1).1`.

Use `congrArg Subtype.val hτ` as an intermediate fact. Express the relevant statement in the definitionally equal form `τ • (gsLocalPlace hL ιs v 1).1 = w.1 at this`. Rewrite using `[← this, inv_smul_smul]`.
-/
theorem bijective_mk_gsPlaceAbove :
    let _ := placesOverAction (L := L) S
    Function.Bijective fun v : S =>
      Quotient.mk (orbitRel (L ≃ₐ[F] L) (placesOver S : Set (HeightOneSpectrum (𝓞 L))))
        (gsPlaceAbove hL ιs v) := by
  let _ := placesOverAction (L := L) S
  constructor
  · intro v v' h
    obtain ⟨τ, hτ⟩ := Quotient.exact h
    have hτ' : τ • (gsPlaceAbove hL ιs v').1 = (gsPlaceAbove hL ιs v).1 := congrArg Subtype.val hτ
    have e1 := eq_placeBelow_of_liesOver (K := F) (gsLocalPlace hL ιs v 1).2
    have e2 := eq_placeBelow_of_liesOver (K := F) (gsLocalPlace hL ιs v' 1).2
    apply Subtype.ext
    rw [e1, e2]
    change placeBelow (gsPlaceAbove hL ιs v).1 = placeBelow (gsPlaceAbove hL ιs v').1
    rw [← hτ', placeBelow_smul]
  · intro ω
    induction ω using Quotient.inductionOn with
    | h w =>
      obtain ⟨v0, hv0, hw⟩ := w.2
      let v : S := ⟨v0, hv0⟩
      obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (L ≃ₐ[F] L) (gsLocalPlace hL ιs v 1)
        (⟨w.1, hw⟩ : PlacesOver L v0)
      refine ⟨v, Quotient.sound ⟨τ⁻¹, ?_⟩⟩
      apply Subtype.ext
      change τ⁻¹ • w.1 = (gsLocalPlace hL ιs v 1).1
      have := congrArg Subtype.val hτ
      change τ • (gsLocalPlace hL ιs v 1).1 = w.1 at this
      rw [← this, inv_smul_smul]

variable {k N : Type*} [Field k] [AddCommGroup N] [Module k N] [FiniteDimensional k N]
  (σN : Representation k (L ≃ₐ[F] L) N)

/- English proof (translation)
Introduce `_`. Use `finite_placesOver (L := L) (S := S)` as an intermediate fact. Set `_` to `Fintype.ofFinite (placesOver S : Set (HeightOneSpectrum (𝓞 L)))`. Set `_` to `Fintype.ofFinite (orbitRel.Quotient (L ≃ₐ[F] L) (placesOver S : Set (HeightOneSpectrum (𝓞 L))))`. Rewrite using `[finrank_invariants_funPermRep_tprod]`.

Use `(Fintype.sum_bijective _ (bijective_mk_gsPlaceAbove hL ιs) _ _ fun v => ?_).symm` and prove the remaining obligations. Establish `h1` using `orbitMover_smul (Γ := L ≃ₐ[F] L) (gsPlaceAbove hL ιs v)`. Rewrite using `[← stabilizer_gsPlaceAbove hL ιs v]`. Use `conv_lhs => rw [← h1]`. Rewrite using `[finrank_invariants_stabilizer_smul]`.
-/
theorem finrank_invariants_funPermRep_placesOver [Fintype S] :
    let _ := placesOverAction (L := L) S
    Module.finrank k ((funPermRep k (L ≃ₐ[F] L)
        (placesOver S : Set (HeightOneSpectrum (𝓞 L)))).tprod σN).invariants =
      ∑ v : S, Module.finrank k (Representation.invariants (σN.comp (gsDecompGroup hL ιs v).subtype)) := by
  intro _
  classical
  have := finite_placesOver (L := L) (S := S)
  let _ := Fintype.ofFinite (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
  let _ := Fintype.ofFinite (orbitRel.Quotient (L ≃ₐ[F] L) (placesOver S : Set (HeightOneSpectrum (𝓞 L))))
  rw [finrank_invariants_funPermRep_tprod]
  refine (Fintype.sum_bijective _ (bijective_mk_gsPlaceAbove hL ιs) _ _ fun v => ?_).symm
  have h1 := orbitMover_smul (Γ := L ≃ₐ[F] L) (gsPlaceAbove hL ιs v)
  rw [← stabilizer_gsPlaceAbove hL ιs v]
  conv_lhs => rw [← h1]
  rw [finrank_invariants_stabilizer_smul]

end Finite

end

end GroundTheory.ProfCoh
