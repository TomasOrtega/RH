import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfForallExistsFix
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeGal

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix`. Consider the case `exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix`. Consider the case `(apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix ..)`.
-/
theorem continuous_galHom_of_fix {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
    [Algebra k' F'] [Algebra.IsIntegral k F] (φ : (F ≃ₐ[k] F) →* (F' ≃ₐ[k'] F'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : F ≃ₐ[k] F, σ x = x → φ σ y = y) : Continuous φ := by
  first
  | exact @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | (apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix ..)

/- English proof (translation)
Establish `hc : (commutator G).map (φ : G →* H) = commutator H`. Rewrite using `[commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]`. Establish `hmap : (Subgroup.topologicalClosure (commutator G)).map (φ : G →* H) = Subgroup.topologicalClosure (commutator H)`. Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe, ← hc, Subgroup.coe_map]`.

Conclude with `(hφ.homeomorph φ).image_closure _`. Set `ψ` to `QuotientGroup.congr _ _ φ hmap`. Establish `h1 : Continuous ψ` using `(QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2 (QuotientGroup.continuous_mk.comp hφ.continuous)`. Establish `hs : Continuous φ.symm` using `(φ.toEquiv.toHomeomorphOfContinuousOpen hφ.continuous hφ.isOpenMap).symm.continuous`. Establish `h2 : Continuous ψ.symm` using `(QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2 (QuotientGroup.continuous_mk.comp hs)`.

Conclude with `⟨ψ, (Homeomorph.mk ψ.toEquiv h1 h2).isHomeomorph, fun g => rfl⟩`.
-/
theorem exists_topAbelianization_mulEquiv {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : G ≃* H) (hφ : IsHomeomorph φ) :
    ∃ ψ : TopologicalAbelianization G ≃* TopologicalAbelianization H, IsHomeomorph ψ ∧
      ∀ g : G, ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := by
  have hc : (commutator G).map (φ : G →* H) = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]
  have hmap : (Subgroup.topologicalClosure (commutator G)).map (φ : G →* H) =
      Subgroup.topologicalClosure (commutator H) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe, ← hc, Subgroup.coe_map]
    exact (hφ.homeomorph φ).image_closure _
  let ψ := QuotientGroup.congr _ _ φ hmap
  have h1 : Continuous ψ :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hφ.continuous)
  have hs : Continuous φ.symm :=
    (φ.toEquiv.toHomeomorphOfContinuousOpen hφ.continuous hφ.isOpenMap).symm.continuous
  have h2 : Continuous ψ.symm :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hs)
  exact ⟨ψ, (Homeomorph.mk ψ.toEquiv h1 h2).isHomeomorph, fun g => rfl⟩

/- English proof (translation)
Introduce `K _ _ Ω _ _ e`. Use `haveI hint : Algebra.IsIntegral K Ω := ⟨fun x => (isIntegral_algEquiv e).1 (Algebra.IsIntegral.isIntegral (e x))⟩`. Set `φ : (Ω ≃ₐ[K] Ω) ≃* Field.absoluteGaloisGroup K` to `AlgEquiv.autCongr e`. Establish `h1 : Continuous φ.toMonoidHom` using `continuous_galHom_of_fix φ.toMonoidHom fun y => ⟨e.symm y, fun σ hσ => by show e (σ (e.symm y)) = y`. Rewrite using `[hσ, AlgEquiv.apply_symm_apply]⟩`.

Establish `h2 : Continuous φ.symm.toMonoidHom` using `continuous_galHom_of_fix φ.symm.toMonoidHom fun y => ⟨e y, fun τ hτ => by show e.symm (τ (e y)) = y`. Rewrite using `[hτ, AlgEquiv.symm_apply_apply]⟩`. Establish `hφ : IsHomeomorph φ` using `(Homeomorph.mk φ.toEquiv h1 h2).isHomeomorph`. Take `⟨ψ, hψ, hψg⟩` from `exists_topAbelianization_mulEquiv φ hφ`. Use `⟨ψ.toMonoidHom, hψ.continuous, ψ.bijective, fun σ => ?_⟩` and prove the remaining obligations.

Conclude with `hψg σ`.
-/
theorem exists_abMap_of_algEquiv : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]
    (e : Ω ≃ₐ[K] AlgebraicClosure K), ∃ φ : GlobalTheory.HeckeGal.Gab K Ω →* Field.absoluteGaloisGroupAbelianization K,
      Continuous φ ∧ Function.Bijective φ ∧
      ∀ σ : Formalism.ConjugateSelfDual.G K Ω, φ (GlobalTheory.HeckeGal.toAb K Ω σ) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  intro K _ _ Ω _ _ e
  haveI hint : Algebra.IsIntegral K Ω :=
    ⟨fun x => (isIntegral_algEquiv e).1 (Algebra.IsIntegral.isIntegral (e x))⟩
  let φ : (Ω ≃ₐ[K] Ω) ≃* Field.absoluteGaloisGroup K := AlgEquiv.autCongr e
  have h1 : Continuous φ.toMonoidHom :=
    continuous_galHom_of_fix φ.toMonoidHom fun y => ⟨e.symm y, fun σ hσ => by
      show e (σ (e.symm y)) = y
      rw [hσ, AlgEquiv.apply_symm_apply]⟩
  have h2 : Continuous φ.symm.toMonoidHom :=
    continuous_galHom_of_fix φ.symm.toMonoidHom fun y => ⟨e y, fun τ hτ => by
      show e.symm (τ (e y)) = y
      rw [hτ, AlgEquiv.symm_apply_apply]⟩
  have hφ : IsHomeomorph φ := (Homeomorph.mk φ.toEquiv h1 h2).isHomeomorph
  obtain ⟨ψ, hψ, hψg⟩ := exists_topAbelianization_mulEquiv φ hφ
  refine ⟨ψ.toMonoidHom, hψ.continuous, ψ.bijective, fun σ => ?_⟩
  exact hψg σ

end GlobalTheory.HeckeGal
