import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOfQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorBasisCriterion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorToSubschemeSectionsRestricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealsEqOfSpanIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingMapFromAffineOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisQuotientTensorBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertTensorToSubschemeSectionsSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfKerTensorToSubschemeSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorPullbackEqMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfQuotientBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHomStatement

namespace GlobalTheory.HilbAff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

/- English proof (translation)
Establish `hch : ∀ U : Z.affineOpens, ∃ φ : C →+* Γ(Z, U), ∃ hφ : ∀ a : A, φ (algebraMap A C a) = secAlg A g U a,`. Use `letI := (secAlg A g U).toAlgebra`. Use the proof step `RingHom.ker (kappa A B g I U) = J.map (Algebra.TensorProduct.map ({ toRingHom := φ, commutes' := hφ } : C →ₐ[A] Γ(Z, U)) (AlgHom.id A B)) ∧`. Use the proof step `∀ ψ : C →ₐ[A] Γ(Z, U), RingHom.ker (kappa A B g I U) = J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B)) → ψ.toRingHom = φ := by`. Introduce `U`.

Use `letI := (secAlg A g U).toAlgebra`. Take `⟨-, hli', hsp'⟩` from `(GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)`. Take `⟨φ, hφ, hφu⟩` from `huniv Γ(Z, U) _ hli' hsp'`. Conclude with `⟨φ.toRingHom, φ.commutes, hφ, fun ψ hψ => congrArg AlgHom.toRingHom (hφu ψ hψ)⟩`. Use `choose φ hφA hφ hφu using hch`.

Establish `compat : ∀ (U V : Z.affineOpens) (hUV : (U : Z.Opens) ≤ V), (Z.presheaf.map (homOfLE hUV).op).hom.comp (φ V) = φ U`. Introduce `U V hUV`. Use `letI iU := (secAlg A g U).toAlgebra`. Use `letI iV := (secAlg A g V).toAlgebra`. Take `⟨ρ, hρ, hle⟩` from `GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict A B g I U V hUV`.

Set `φV : C →ₐ[A] Γ(Z, V)` to `{ toRingHom := φ V, commutes' := hφA V }`. Establish `hmap : J.map (Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B)) = (RingHom.ker (kappa A B g I V)).map (Algebra.TensorProduct.map ρ (AlgHom.id A B))`. Rewrite using `[hφ V, show Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B) = (Algebra.TensorProduct.map ρ (AlgHom.id A B)).comp (Algebra.TensorProduct.map φV (AlgHom.id A B)) by`. Rewrite using `[← Algebra.TensorProduct.map_comp, AlgHom.comp_id]]`. Conclude with `(Ideal.map_map (Algebra.TensorProduct.map φV (AlgHom.id A B)).toRingHom (Algebra.TensorProduct.map ρ (AlgHom.id A B)).toRingHom).symm`.

Establish `hsp2` using `(GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J (ρ.comp φV) hli hsp).2`. Establish `hliU` using `((GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)).2.1`. Establish `heq` using `GlobalTheory.T.ideals_eq_of_span_independent A B Γ(Z, U) (fun k => e (σ k)) _ _ (hmap ▸ hle) hsp2 hliU`. Rewrite using `[← hφu U (ρ.comp φV) heq.symm, ← hρ]`. Both sides reduce to the same expression.

Take `⟨Φ, hΦ, hΦu⟩` from `GlobalTheory.T.ring_map_from_affine_opens Z C φ compat`. Take `⟨h, hh⟩` from `GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom Z C Φ`. Establish `hhU : ∀ U : Z.affineOpens, secAlg C h U = φ U` using `fun U => by`. Rewrite using `[← secAlg_res C h (le_top : (U : Z.Opens) ≤ ⊤), hh, hΦ U]`. Establish `hgA : h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = g`.

Apply `eq_of_secAlg_top` to reduce the goal to its premises. Rewrite using `[secAlg_comp, hh]`. Take `⟨Ψ, -, hΨu⟩` from `GlobalTheory.T.ring_map_from_affine_opens Z A (fun U => secAlg A g U) (fun U V hUV => secAlg_res A g hUV)`. Establish `h1` using `hΨu (Φ.comp (algebraMap A C)) (fun U => by`. Rewrite using `[← RingHom.comp_assoc, hΦ U]`.

Use extensionality with `a`. Conclude with `hφA U a)`. Establish `h2` using `hΨu (secAlg A g ⊤) (fun U => secAlg_res A g le_top)`. Rewrite using `[h1, h2]`. Use `⟨h, ?_, ?_⟩` and prove the remaining obligations.

Substitute `hgA` using the available equality. Use `Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))` and prove the remaining obligations. Apply `GlobalTheory.T.idealSheaf_eq_of_ker_tensorToSubschemeSections` to reduce the goal to its premises. Introduce `U`. Take `⟨φ', hφ', hker⟩` from `GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U`.

Use `letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra`. Use `(hker.trans ?_).trans (hφ U).symm` and prove the remaining obligations. Use `congr 2`. Conclude with `AlgHom.ext fun c => congrArg (fun F => F c) (hφ'.trans (hhU U))`. Introduce `h' hh'`.

Establish `hU : ∀ U : Z.affineOpens, secAlg C h' U = φ U`. Introduce `U`. Take `⟨φ', hφ', hker⟩` from `GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h' U`. Consider the cases of `hh'`. Rewrite using `[← hφ']`.

Conclude with `hφu U φ' hker`. Establish `hΦ' : secAlg C h' ⊤ = Φ` using `hΦu _ (fun U => by rw [secAlg_res, hU U])`. Conclude with `eq_of_secAlg_top C (hΦ'.trans hh.symm)`.
-/
theorem exists_unique_lift (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (C : Type) [CommRing C] [Algebra A C]
    (J : Ideal (C ⊗[A] B))
    (hli : LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k))))
    (hsp : Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k)))) = ⊤)
    (huniv : ∀ (A' : Type) [CommRing A'] [Algebra A A'] (J' : Ideal (A' ⊗[A] B)),
      LinearIndependent A' (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k))) →
      Submodule.span A' (Set.range (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k)))) = ⊤ →
      ∃! φ : C →ₐ[A] A', J' = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)))
    (hgood : Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (xI A B C J))
    (Z : Scheme.{0}) (g : Z ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    (hI : Good A B r g I)
    (hy : ∀ U : Z.affineOpens, letI := (secAlg A g U).toAlgebra
      Function.Bijective fun c : Fin r → Γ(Z, U) => kappa A B g I U (∑ k, c k ⊗ₜ[A] e (σ k))) :
    ∃! h : Z ⟶ Spec (CommRingCat.of C), (functor A B r).map h.op
      (⟨Spec.map (CommRingCat.ofHom (algebraMap A C)), ⟨xI A B C J, hgood⟩⟩ :
        (functor A B r).obj (op (Spec (CommRingCat.of C)))) = ⟨g, ⟨I, hI⟩⟩ := by
  have hch : ∀ U : Z.affineOpens, ∃ φ : C →+* Γ(Z, U), ∃ hφ : ∀ a : A,
      φ (algebraMap A C a) = secAlg A g U a,
      letI := (secAlg A g U).toAlgebra
      RingHom.ker (kappa A B g I U) = J.map (Algebra.TensorProduct.map
        ({ toRingHom := φ, commutes' := hφ } : C →ₐ[A] Γ(Z, U)) (AlgHom.id A B)) ∧
      ∀ ψ : C →ₐ[A] Γ(Z, U), RingHom.ker (kappa A B g I U) =
        J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B)) → ψ.toRingHom = φ := by
    intro U
    letI := (secAlg A g U).toAlgebra
    obtain ⟨-, hli', hsp'⟩ := (GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)
    obtain ⟨φ, hφ, hφu⟩ := huniv Γ(Z, U) _ hli' hsp'
    exact ⟨φ.toRingHom, φ.commutes, hφ, fun ψ hψ => congrArg AlgHom.toRingHom (hφu ψ hψ)⟩
  choose φ hφA hφ hφu using hch
  have compat : ∀ (U V : Z.affineOpens) (hUV : (U : Z.Opens) ≤ V),
      (Z.presheaf.map (homOfLE hUV).op).hom.comp (φ V) = φ U := by
    intro U V hUV
    letI iU := (secAlg A g U).toAlgebra
    letI iV := (secAlg A g V).toAlgebra
    obtain ⟨ρ, hρ, hle⟩ := GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict A B g I U V hUV
    let φV : C →ₐ[A] Γ(Z, V) := { toRingHom := φ V, commutes' := hφA V }
    have hmap : J.map (Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B)) =
        (RingHom.ker (kappa A B g I V)).map (Algebra.TensorProduct.map ρ (AlgHom.id A B)) := by
      rw [hφ V, show Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B) =
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)).comp
          (Algebra.TensorProduct.map φV (AlgHom.id A B)) by
        rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id]]
      exact (Ideal.map_map (Algebra.TensorProduct.map φV (AlgHom.id A B)).toRingHom
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)).toRingHom).symm
    have hsp2 := (GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J (ρ.comp φV) hli hsp).2
    have hliU := ((GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)).2.1
    have heq := GlobalTheory.T.ideals_eq_of_span_independent A B Γ(Z, U) (fun k => e (σ k)) _ _ (hmap ▸ hle) hsp2 hliU
    rw [← hφu U (ρ.comp φV) heq.symm, ← hρ]
    rfl
  obtain ⟨Φ, hΦ, hΦu⟩ := GlobalTheory.T.ring_map_from_affine_opens Z C φ compat
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom Z C Φ
  have hhU : ∀ U : Z.affineOpens, secAlg C h U = φ U := fun U => by
    rw [← secAlg_res C h (le_top : (U : Z.Opens) ≤ ⊤), hh, hΦ U]
  have hgA : h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = g := by
    apply eq_of_secAlg_top
    rw [secAlg_comp, hh]
    obtain ⟨Ψ, -, hΨu⟩ := GlobalTheory.T.ring_map_from_affine_opens Z A (fun U => secAlg A g U) (fun U V hUV => secAlg_res A g hUV)
    have h1 := hΨu (Φ.comp (algebraMap A C)) (fun U => by
      rw [← RingHom.comp_assoc, hΦ U]; ext a; exact hφA U a)
    have h2 := hΨu (secAlg A g ⊤) (fun U => secAlg_res A g le_top)
    rw [h1, h2]
  refine ⟨h, ?_, ?_⟩
  · subst hgA
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
    apply GlobalTheory.T.idealSheaf_eq_of_ker_tensorToSubschemeSections
    intro U
    obtain ⟨φ', hφ', hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U
    letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
    refine (hker.trans ?_).trans (hφ U).symm
    congr 2
    exact AlgHom.ext fun c => congrArg (fun F => F c) (hφ'.trans (hhU U))
  · intro h' hh'
    have hU : ∀ U : Z.affineOpens, secAlg C h' U = φ U := by
      intro U
      obtain ⟨φ', hφ', hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h' U
      cases hh'
      rw [← hφ']
      exact hφu U φ' hker
    have hΦ' : secAlg C h' ⊤ = Φ := hΦu _ (fun U => by rw [secAlg_res, hU U])
    exact eq_of_secAlg_top C (hΦ'.trans hh.symm)

/- English proof (translation)
Take `⟨C, _, _, J, hfp, hli, hsp, huniv⟩` from `GlobalTheory.hilbChart_representable A B N r e σ`. Establish `hgood : Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (xI A B C J)` using `GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_quotient_basis A B C J (fun k => e (σ k)) hli hsp`. Set `x : (functor A B r).obj (op (Spec (CommRingCat.of C)))` to `⟨Spec.map (CommRingCat.ofHom (algebraMap A C)), ⟨xI A B C J, hgood⟩⟩`. Establish `hBx : ∀ (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)), Basic A B e σ ((functor A B r).map h.op x)`. Introduce `Z h`.

Rewrite using `[functor_map, basic_iff_kappa]`. Introduce `U`. Take `⟨φ, -, hker⟩` from `GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U`. Use `letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra`. Take `⟨hli', hsp'⟩` from `GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J φ hli hsp`.

Use `(GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mpr ⟨GlobalTheory.T.affineHilbertTensorToSubschemeSections_surjective A B _ _ U, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hker]`. Conclude with `hli'`. Rewrite using `[hker]`. Conclude with `hsp'`.

Establish `hBasic : Basic A B e σ x`. Simplify using `using hBx _ (𝟙 _)`. Use `⟨Spec (CommRingCat.of C), x, inferInstance, ?_, hBasic, ?_⟩` and prove the remaining obligations. Use `show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A C)))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`.

Use `haveI := hfp`. Conclude with `RingHom.finiteType_algebraMap.mpr inferInstance`. Introduce `Z y hy`. Take `⟨g, I, hI⟩` from `y`. Rewrite `hy` using `[basic_iff_kappa]`.

Conclude with `exists_unique_lift A B e σ C J hli hsp huniv hgood Z g I hI hy`.
-/
theorem chart_represents (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) :
    ∃ (X : Scheme.{0}) (x : (functor A B r).obj (op X)), IsAffine X ∧ LocallyOfFiniteType x.1 ∧
      Basic A B e σ x ∧ ∀ (Z : Scheme.{0}) (y : (functor A B r).obj (op Z)), Basic A B e σ y →
        ∃! g : Z ⟶ X, (functor A B r).map g.op x = y := by
  obtain ⟨C, _, _, J, hfp, hli, hsp, huniv⟩ := GlobalTheory.hilbChart_representable A B N r e σ
  have hgood : Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (xI A B C J) :=
    GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_quotient_basis A B C J (fun k => e (σ k)) hli hsp
  let x : (functor A B r).obj (op (Spec (CommRingCat.of C))) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap A C)), ⟨xI A B C J, hgood⟩⟩
  have hBx : ∀ (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)),
      Basic A B e σ ((functor A B r).map h.op x) := by
    intro Z h
    rw [functor_map, basic_iff_kappa]
    intro U
    obtain ⟨φ, -, hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U
    letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
    obtain ⟨hli', hsp'⟩ := GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J φ hli hsp
    refine (GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mpr ⟨GlobalTheory.T.affineHilbertTensorToSubschemeSections_surjective A B _ _ U, ?_, ?_⟩
    · rw [hker]; exact hli'
    · rw [hker]; exact hsp'
  have hBasic : Basic A B e σ x := by
    simpa using hBx _ (𝟙 _)
  refine ⟨Spec (CommRingCat.of C), x, inferInstance, ?_, hBasic, ?_⟩
  · show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A C)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    haveI := hfp
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  intro Z y hy
  obtain ⟨g, I, hI⟩ := y
  rw [basic_iff_kappa] at hy
  exact exists_unique_lift A B e σ C J hli hsp huniv hgood Z g I hI hy
end GlobalTheory.HilbAff
