import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsIntClosedLocalDomainStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgCStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingAtPrimeOfEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainMonicRootsOfIsIndEtaleLocalStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.HInvAic

/- English proof (translation)
Simplify using `only [spMap]`. Rewrite using `[← Functor.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

/- English proof (translation)
Simplify using `only [spMap]`. Rewrite using `[show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]`.
-/
theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

/- English proof (translation)
Introduce `n`. Establish `: (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n` using `funext fun x => pull_comp R f g F n x`. Rewrite using `[this]`. Conclude with `(hf n).comp (hg n)`.
-/
theorem eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : _ → _) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [this]
  exact (hf n).comp (hg n)

/- English proof (translation)
Introduce `n`. Establish `h1 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _`. Rewrite using `[← spMap_comp]`. Use `spMap_id B` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Simplify using the standard rewrite rules. Establish `h2 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _`. Rewrite using `[← spMap_comp]`. Use `spMap_id A` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Simplify using the standard rewrite rules. Use `Function.bijective_iff_has_inverse.mpr ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← pull_comp, h2, pull_id]`. Rewrite using `[← pull_comp, h1, pull_id]`.
-/
theorem eqv_spMap_equiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) :
    Eqv R (spMap (e : A →+* B)) F := by
  intro n
  have h1 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id B; ext x; simp
  have h2 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp]; convert spMap_id A; ext x; simp
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h2, pull_id]
  · rw [← pull_comp, h1, pull_id]

end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

/- English proof (translation)
Introduce `hT hSH hInd`. Take `⟨hH, -⟩` from `hSH`. Take `⟨-, hac⟩` from `(GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT`. Use `haveI : IsIntegrallyClosed T := ((GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT).1`. Use `GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local T O hInd ?_` and prove the remaining obligations.

Introduce `E _ _ _ P _`. Take `⟨hd, hc⟩` from `GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale T P (Localization.AtPrime P)`. Conclude with `⟨hd, (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed _).2 ⟨hc, GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' T E P hac⟩⟩`.
-/
theorem alg (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O] :
    AIC T → SH O → IndEt T O → IsDomain O ∧ AIC O := by
  intro hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  obtain ⟨-, hac⟩ := (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT
  haveI : IsIntegrallyClosed T := ((GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed T).1 hT).1
  refine GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local T O hInd ?_
  intro E _ _ _ P _
  obtain ⟨hd, hc⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale T P (Localization.AtPrime P)
  exact ⟨hd, (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed _).2 ⟨hc, GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' T E P hac⟩⟩
end GlobalTheory.HInvAic

namespace GlobalTheory.HInvAic

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul o t`. Simplify using `only [RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.rid_tmul, polyEquivTensor_apply, Polynomial.eval₂_C]`.

Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.ofId_apply, Polynomial.algebraMap_eq]`. Rewrite using `[TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Polynomial.algebraMap_eq]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem tensor_map_eq (T O : Type) [CommRing T] [CommRing O] [Algebra T O] :
    (Algebra.TensorProduct.map (AlgHom.id T O) (Algebra.ofId T (Polynomial T))).toRingHom =
      (((polyEquivTensor T O).toRingEquiv : Polynomial O →+* O ⊗[T] Polynomial T).comp Polynomial.C).comp
        ((Algebra.TensorProduct.rid T T O).toRingEquiv : O ⊗[T] T →+* O) := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o t =>
    simp only [RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Algebra.TensorProduct.rid_tmul, polyEquivTensor_apply, Polynomial.eval₂_C]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.ofId_apply, Polynomial.algebraMap_eq]
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, Polynomial.algebraMap_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Introduce `q _ T _ _ hT hq i`. Establish `hφ : ((Algebra.ofId T (Polynomial T)).toRingHom : T →+* Polynomial T) = Polynomial.C`. Apply the tactic sequence `ext x <;> simp [Algebra.ofId_apply]`. Rewrite using `[← hφ]`. Use `GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) T T (Polynomial T) (Algebra.ofId T (Polynomial T)) ?_` and prove the remaining obligations.

Introduce `O _ _ hSH hInd`. Take `⟨hdom, haic⟩` from `alg T O hT hSH hInd`. Take `⟨hH, -⟩` from `hSH`. Establish `hqO : IsUnit (q : O)` using `by simpa using hq.map (algebraMap T O)`. Establish `hC` using `GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain q O haic hqO i`.

Rewrite using `[tensor_map_eq, spMap_comp, spMap_comp]`. Conclude with `eqv_comp _ _ _ (eqv_comp _ _ _ (eqv_spMap_equiv _ _) hC) (eqv_spMap_equiv _ _)`.
-/
theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  intro q _ T _ _ hT hq i
  have hφ : ((Algebra.ofId T (Polynomial T)).toRingHom : T →+* Polynomial T) = Polynomial.C := by
    ext x <;> simp [Algebra.ofId_apply]
  rw [← hφ]
  refine GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) T T (Polynomial T) (Algebra.ofId T (Polynomial T)) ?_
  intro O _ _ hSH hInd
  obtain ⟨hdom, haic⟩ := alg T O hT hSH hInd
  obtain ⟨hH, -⟩ := hSH
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  have hC := GlobalTheory.T.etaleHomotopyInvariance_absIntClosedLocalDomain q O haic hqO i
  rw [tensor_map_eq, spMap_comp, spMap_comp]
  exact eqv_comp _ _ _ (eqv_comp _ _ _ (eqv_spMap_equiv _ _) hC) (eqv_spMap_equiv _ _)

end GlobalTheory.HInvAic
