import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyGenericFibreHenselLineSubsingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleCohomologyGenericFibreHenselianStatement
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHense
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct

namespace GlobalTheory.EtC.LineLocal

open Polynomial

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨x, Subsingleton.elim _ _⟩⟩`.
-/
theorem bijective_of_subsingleton {X Y : Type*} [Subsingleton X] [Subsingleton Y] (f : X → Y) (x : X) :
    Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨x, Subsingleton.elim _ _⟩⟩

/- English proof (translation)
Establish `h : e * (e - 1) = 0` using `by rw [mul_sub, mul_one, he.eq, sub_self]`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (sub_eq_zero.mp h)`.
-/
theorem idem_of_domain {A : Type} [CommRing A] [IsDomain A] (e : A) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

/- English proof (translation)
Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (O ⊗[T] FractionRing T) := by`. Rewrite using `[Algebra.isLocalization_iff_isPushout (nonZeroDivisors T) (FractionRing T)]`. Use `infer_instance`. Conclude with `IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (O ⊗[T] FractionRing T) (by`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Conclude with `mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))`.
-/
theorem isDomain_tensor_fractionRing (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsDomain O]
    [Algebra T O] (hinj : Function.Injective (algebraMap T O)) : IsDomain (O ⊗[T] FractionRing T) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      (O ⊗[T] FractionRing T) := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors T) (FractionRing T)]
    infer_instance
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    (O ⊗[T] FractionRing T) (by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))

/- English proof (translation)
Introduce `q _ T _ _ _ hT hq O _ _ _ _ hSH hInd i`. Unfold `Eqv`. Introduce `n`. Establish `hfac : ∀ a : O, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] O), a ∈ φ.range`. Introduce `a`.

Take `⟨C, _, _, _, ψ, χ, h⟩` from `exists_etale_factor_of_indEt (Polynomial T) O hInd (Polynomial (Polynomial T)) (Polynomial.aeval a)`. Use `⟨C, ‹_›, ‹_›, ‹_›, χ, ⟨ψ Polynomial.X, ?_⟩⟩` and prove the remaining obligations. Use `DFunLike.congr_fun h Polynomial.X` as an intermediate fact. Simplify using `using this`. Break down `lt_trichotomy n 0 with hn | rfl | hn` into its components or cases.

Establish `h1` using `(GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1 haveI := h1 (sp O) n hn haveI := h1 (sp (TensorProduct T (FractionRing T) O)) n hn`. Conclude with `bijective_of_subsingleton _ 0`. Use `haveI : IsIntegrallyClosed T := GlobalTheory.AICStalk.isIntegrallyClosed_of_aic hT`. Take `⟨hH, -⟩` from `hSH`. Use `haveI : IsLocalRing O := hH.toIsLocalRing`.

Use `haveI : IsDomain O := GlobalTheory.AICStalk.isDomain_of_indEt hInd`. Establish `hinjX : Function.Injective (algebraMap (Polynomial T) O)` using `GlobalTheory.AICStalk.algebraMap_injective_of_indEt hInd`. Establish `hinj : Function.Injective (algebraMap T O)`. Rewrite using `[IsScalarTower.algebraMap_eq T (Polynomial T) O]`. Conclude with `hinjX.comp (Polynomial.C_injective)`.

Use `haveI : IsDomain (O ⊗[T] FractionRing T) := isDomain_tensor_fractionRing T O hinj`. Use `haveI : IsDomain (TensorProduct T (FractionRing T) O) := MulEquiv.isDomain _ (Algebra.TensorProduct.comm T (FractionRing T) O).toRingEquiv.toMulEquiv`. Establish `hqO : IsUnit (q : O)`. Use `hq.map (algebraMap T O)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Take `⟨z, hz⟩` from `hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T) (by`. Rewrite using `[Polynomial.natDegree_cyclotomic]`. Conclude with `Nat.totient_pos.2 (NeZero.pos q))`. Establish `hζ : Polynomial.aeval (algebraMap T O z) (Polynomial.cyclotomic q ℤ) = 0`. Rewrite using `[Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic, hz, map_zero]`.

Conclude with `GlobalTheory.T.h_zero_pullback_twist_bijective q O (TensorProduct T (FractionRing T) O) (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom hqO ⟨_, hζ⟩ inferInstance (idem_of_domain) (idem_of_domain) i`. Use `haveI : Subsingleton (H (ZMod q) (sp O) (tw q i) n) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) O hSH (tw q i) n hn haveI : Subsingleton (H (ZMod q) (sp (TensorProduct T (FractionRing T) O)) (tw q i) n) := by`. Break down `(show n = 1 ∨ 2 ≤ n by omega) with rfl | h2` into its components or cases. Conclude with `GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover q T hT hq O hSH hfac i`. Conclude with `GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine q T hT hq O hSH hInd n i h2`.

Conclude with `bijective_of_subsingleton _ 0`.
-/
theorem eqv_local : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T →
    IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O]
    [IsScalarTower T (Polynomial T) O], SH O → IndEt (Polynomial T) O → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom)
      (tw q i) := by
  intro q _ T _ _ _ hT hq O _ _ _ _ hSH hInd i
  unfold Eqv
  intro n
  have hfac : ∀ a : O, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E)
      (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] O), a ∈ φ.range := by
    intro a
    obtain ⟨C, _, _, _, ψ, χ, h⟩ := exists_etale_factor_of_indEt (Polynomial T) O hInd
      (Polynomial (Polynomial T)) (Polynomial.aeval a)
    refine ⟨C, ‹_›, ‹_›, ‹_›, χ, ⟨ψ Polynomial.X, ?_⟩⟩
    have := DFunLike.congr_fun h Polynomial.X
    simpa using this
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have h1 := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1
    haveI := h1 (sp O) n hn
    haveI := h1 (sp (TensorProduct T (FractionRing T) O)) n hn
    exact bijective_of_subsingleton _ 0
  · haveI : IsIntegrallyClosed T := GlobalTheory.AICStalk.isIntegrallyClosed_of_aic hT
    obtain ⟨hH, -⟩ := hSH
    haveI : IsLocalRing O := hH.toIsLocalRing
    haveI : IsDomain O := GlobalTheory.AICStalk.isDomain_of_indEt hInd
    have hinjX : Function.Injective (algebraMap (Polynomial T) O) :=
      GlobalTheory.AICStalk.algebraMap_injective_of_indEt hInd
    have hinj : Function.Injective (algebraMap T O) := by
      rw [IsScalarTower.algebraMap_eq T (Polynomial T) O]
      exact hinjX.comp (Polynomial.C_injective)
    haveI : IsDomain (O ⊗[T] FractionRing T) := isDomain_tensor_fractionRing T O hinj
    haveI : IsDomain (TensorProduct T (FractionRing T) O) :=
      MulEquiv.isDomain _ (Algebra.TensorProduct.comm T (FractionRing T) O).toRingEquiv.toMulEquiv
    have hqO : IsUnit (q : O) := by
      have := hq.map (algebraMap T O)
      rwa [map_natCast] at this
    obtain ⟨z, hz⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T) (by
      rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
    have hζ : Polynomial.aeval (algebraMap T O z) (Polynomial.cyclotomic q ℤ) = 0 := by
      rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.map_cyclotomic, hz, map_zero]
    exact GlobalTheory.T.h_zero_pullback_twist_bijective q O (TensorProduct T (FractionRing T) O)
      (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom hqO
      ⟨_, hζ⟩ inferInstance (idem_of_domain) (idem_of_domain) i
  · haveI : Subsingleton (H (ZMod q) (sp O) (tw q i) n) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) O hSH (tw q i) n hn
    haveI : Subsingleton (H (ZMod q) (sp (TensorProduct T (FractionRing T) O)) (tw q i) n) := by
      rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
      · exact GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover q T hT hq O hSH hfac i
      · exact GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine q T hT hq O hSH hInd n i h2
    exact bijective_of_subsingleton _ 0

end GlobalTheory.EtC.LineLocal
