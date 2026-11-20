import Formalism.GaussIdealIdentity.StatementLA

open MvPolynomial IsLocalRing

noncomputable section

namespace Formalism.DV.GaussP

variable (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Establish `h` using `MvPolynomial.ker_map (σ := σ) (IsLocalRing.residue O)`. Rewrite `h` using `[IsLocalRing.ker_residue]`. Unfold `gaussIdeal`. Rewrite using `[← h]`. Conclude with `RingHom.ker_isPrime _`.
-/
theorem gaussIdeal_isPrime : (gaussIdeal σ O).IsPrime := by
  have h := MvPolynomial.ker_map (σ := σ) (IsLocalRing.residue O)
  rw [IsLocalRing.ker_residue] at h
  unfold gaussIdeal
  rw [← h]
  exact RingHom.ker_isPrime _

variable [(gaussIdeal σ O).IsPrime]

local notation "A" => Localization.AtPrime (gaussIdeal σ O)

/- English proof (translation)
Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A, ← Ideal.map_map, MvPolynomial.algebraMap_eq]`. Apply the tactic sequence `try rfl`.
-/
theorem maximalIdeal_eq :
    IsLocalRing.maximalIdeal A = Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A,
    ← Ideal.map_map, MvPolynomial.algebraMap_eq]
  try rfl

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A, RingHom.coe_comp, MvPolynomial.algebraMap_eq]`. Conclude with `(IsLocalization.injective (S := A) (M := (gaussIdeal σ O).primeCompl) (Ideal.primeCompl_le_nonZeroDivisors (gaussIdeal σ O))).comp (MvPolynomial.C_injective σ O)`.
-/
theorem algebraMap_injective : Function.Injective (algebraMap O A) := by
  rw [IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A, RingHom.coe_comp, MvPolynomial.algebraMap_eq]
  exact (IsLocalization.injective (S := A) (M := (gaussIdeal σ O).primeCompl)
    (Ideal.primeCompl_le_nonZeroDivisors (gaussIdeal σ O))).comp (MvPolynomial.C_injective σ O)

instance isDomain_A : IsDomain A :=
  IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (gaussIdeal σ O))

instance isNoetherianRing_A : IsNoetherianRing A :=
  IsLocalization.isNoetherianRing (gaussIdeal σ O).primeCompl A inferInstance

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `Submodule.IsPrincipal.principal (IsLocalRing.maximalIdeal O)`. Establish `hϖ' : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `hϖ`. Establish `hmA : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap O A ϖ}`. Rewrite using `[maximalIdeal_eq σ O, hϖ', Ideal.map_span, Set.image_singleton]`. Establish `hne : algebraMap O A ϖ ≠ 0`.

Introduce `h0`. Apply `IsDiscreteValuationRing.not_a_field O` to reduce the goal to its premises. Rewrite using `[hϖ', Ideal.span_singleton_eq_bot]`. Conclude with `algebraMap_injective σ O (h0.trans (map_zero _).symm)`. Establish `hnf : ¬ IsField A`.

Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq, hmA, Ideal.span_singleton_eq_bot]`. Conclude with `hne`. Establish `hp : (IsLocalRing.maximalIdeal A).IsPrincipal` using `⟨⟨_, hmA⟩⟩`. Conclude with `((IsDiscreteValuationRing.TFAE A hnf).out 0 4).2 hp`.
-/
theorem isDVR : IsDiscreteValuationRing A := by
  obtain ⟨ϖ, hϖ⟩ := Submodule.IsPrincipal.principal (IsLocalRing.maximalIdeal O)
  have hϖ' : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ
  have hmA : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap O A ϖ} := by
    rw [maximalIdeal_eq σ O, hϖ', Ideal.map_span, Set.image_singleton]
  have hne : algebraMap O A ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field O
    rw [hϖ', Ideal.span_singleton_eq_bot]
    exact algebraMap_injective σ O (h0.trans (map_zero _).symm)
  have hnf : ¬ IsField A := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmA, Ideal.span_singleton_eq_bot]
    exact hne
  have hp : (IsLocalRing.maximalIdeal A).IsPrincipal := ⟨⟨_, hmA⟩⟩
  exact ((IsDiscreteValuationRing.TFAE A hnf).out 0 4).2 hp

instance isLocalHom_A : IsLocalHom (algebraMap O A) := by
  constructor
  intro a ha
  rw [IsScalarTower.algebraMap_eq O (MvPolynomial σ O) A, RingHom.comp_apply,
    IsLocalization.AtPrime.isUnit_to_map_iff A (gaussIdeal σ O)] at ha
  by_contra hna
  apply ha
  have : a ∈ IsLocalRing.maximalIdeal O := hna
  show MvPolynomial.C a ∈ gaussIdeal σ O
  exact Ideal.mem_map_of_mem _ this

instance flat_A : Module.Flat O A := by
  have : Module.Flat (MvPolynomial σ O) A := IsLocalization.flat A (gaussIdeal σ O).primeCompl
  exact Module.Flat.trans O (MvPolynomial σ O) A

/- English proof (translation)
Rewrite using `[← maximalIdeal_eq σ O]`. Conclude with `Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal)))`.
-/
theorem length_residue :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal O).map (algebraMap O A)) = 1 := by
  rw [← maximalIdeal_eq σ O]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2
    (Ideal.isMaximal_def.1 (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal)))

end GaussP

/- English proof (translation)
Introduce `σ O _ _ _ _`. Use `⟨GaussP.gaussIdeal_isPrime σ O, ?_⟩` and prove the remaining obligations. Introduce `_`. Conclude with `⟨GaussP.isDVR σ O, GaussP.maximalIdeal_eq σ O⟩`.
-/
theorem gaussLocalizationIsDVR_holds : GaussDVR := by
  intro σ O _ _ _ _
  refine ⟨GaussP.gaussIdeal_isPrime σ O, ?_⟩
  intro _
  exact ⟨GaussP.isDVR σ O, GaussP.maximalIdeal_eq σ O⟩

/- English proof (translation)
Establish `fin : ∀ (M : Type) [AddCommGroup M] [Module O M], IsFiniteLength O M → Module.length A (TensorProduct O A M) = Module.length O M`. Introduce `M _ _ hM`. Proceed by induction on `hM with`. Consider the case `@of_subsingleton M _ _ _`. Establish `h0 : Subsingleton (TensorProduct O A M)`.

Use `subsingleton_of_forall_eq 0 (fun x => ?_)` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul a n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`.

Establish `h1 : Module.length O M = 0` using `Module.length_eq_zero_iff.2 inferInstance`. Establish `h2 : Module.length A (TensorProduct O A M) = 0` using `Module.length_eq_zero_iff.2 h0`. Rewrite using `[h1, h2]`. Consider the case `@of_simple_quotient M _ _ K _ _ ih`. Establish `hf : Function.Injective K.subtype` using `fun a b h => Subtype.ext h`.

Establish `hg : Function.Surjective K.mkQ` using `by first`. Consider the case `exact Submodule.mkQ_surjective K`. Consider the case `exact Submodule.Quotient.mk_surjective K`. Establish `hfg : Function.Exact K.subtype K.mkQ` using `LinearMap.exact_subtype_mkQ K`. Establish `hf' : Function.Injective (K.subtype.baseChange A)` using `by first`.

Consider the case `exact Module.Flat.lTensor_preserves_injective_linearMap _ hf`. Consider the case `exact Module.Flat.lTensor_preserves_injective_linearMap (M := A) _ hf`. Consider the case `(rw [LinearMap.baseChange_eq_ltensor]; exact Module.Flat.lTensor_preserves_injective_linearMap _ hf)`. Establish `hg' : Function.Surjective (K.mkQ.baseChange A)` using `by first`. Consider the case `exact LinearMap.lTensor_surjective A hg`.

Consider the case `exact LinearMap.lTensor_surjective _ hg`. Consider the case `(rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective A hg)`. Establish `hfg' : Function.Exact (K.subtype.baseChange A) (K.mkQ.baseChange A)` using `by first`. Consider the case `exact lTensor_exact A hfg hg`. Consider the case `exact lTensor_exact (Q := A) hfg hg`.

Consider the case `exact lTensor_exact hfg hg`. Consider the case `(rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]; exact lTensor_exact A hfg hg)`. Establish `h1 : Module.length O (M ⧸ K) = 1` using `Module.length_eq_one_iff.2 inferInstance`. Rewrite using `[Module.length_eq_add_of_exact _ _ hf hg hfg, Module.length_eq_add_of_exact _ _ hf' hg' hfg', ih, hk (M ⧸ K) inferInstance, h1]`. Establish `mono : ∀ P Q : Submodule O N, P ≤ Q → LinearMap.range (P.subtype.baseChange A) ≤ LinearMap.range (Q.subtype.baseChange A)`.

Introduce `P Q h`. Establish `e : P.subtype = Q.subtype.comp (Submodule.inclusion h)` using `LinearMap.ext fun _ => rfl`. Rewrite using `[e, LinearMap.baseChange_comp]`. Conclude with `LinearMap.range_comp_le_range _ _`. Establish `key : ∀ P Q : Submodule O N, LinearMap.range (Q.subtype.baseChange A) ≤ LinearMap.range (P.subtype.baseChange A) → Q ≤ P`.

Introduce `P Q h`. Establish `hz : P.mkQ.comp P.subtype = 0` using `LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero P).2 x.2`. Establish `hg0 : LinearMap.lTensor A (P.mkQ.comp Q.subtype) = 0`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`.

Take `⟨y, hy⟩` from `LinearMap.mem_range.1 (h (LinearMap.mem_range_self (Q.subtype.baseChange A) x))`. Rewrite using `[LinearMap.zero_apply, LinearMap.lTensor_comp, LinearMap.comp_apply]`. Express the relevant statement in the definitionally equal form `(P.mkQ.baseChange A) ((Q.subtype.baseChange A) x) = 0`. Rewrite using `[← hy]`. Use `first`.

Consider the case `rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hz, LinearMap.baseChange_zero, LinearMap.zero_apply]`. Consider the case `simp [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hz]`. Establish `hg : P.mkQ.comp Q.subtype = 0` using `(Module.FaithfullyFlat.zero_iff_lTensor_zero O A _).2 hg0`. Introduce `n hn`. Establish `h2 : (Submodule.Quotient.mk n : N ⧸ P) = 0` using `LinearMap.congr_fun hg ⟨n, hn⟩`.

Conclude with `(Submodule.Quotient.mk_eq_zero P).1 h2`. Establish `sm : StrictMono (fun P : Submodule O N => LinearMap.range (P.subtype.baseChange A))`. Introduce `P Q hPQ`. Conclude with `(mono P Q hPQ.le).lt_of_ne fun h => hPQ.ne (le_antisymm hPQ.le (key P Q h.ge))`. Establish `ineq : Module.length O N ≤ Module.length A (TensorProduct O A N)`.

Establish `h3` using `Order.krullDim_le_of_strictMono _ sm`. Rewrite `h3` using `[← Module.coe_length, ← Module.coe_length]`. Conclude with `h3` after adjusting the coercions. Distinguish the cases in `hN : Module.length O N = ⊤`. Rewrite `ineq` using `[hN]`.

Rewrite using `[hN]`. Conclude with `top_le_iff.1 ineq`. Conclude with `fin N (Module.length_ne_top_iff.1 hN)`.
-/
private theorem length_tensor_eq_length_of_simple_length_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.FaithfullyFlat O A]
    (hk : ∀ (S : Type) [AddCommGroup S] [Module O S], IsSimpleModule O S →
      Module.length A (TensorProduct O A S) = 1)
    (N : Type) [AddCommGroup N] [Module O N] :
    Module.length A (TensorProduct O A N) = Module.length O N := by
  have fin : ∀ (M : Type) [AddCommGroup M] [Module O M], IsFiniteLength O M →
      Module.length A (TensorProduct O A M) = Module.length O M := by
    intro M _ _ hM
    induction hM with
    | @of_subsingleton M _ _ _ =>
      have h0 : Subsingleton (TensorProduct O A M) := by
        refine subsingleton_of_forall_eq 0 (fun x => ?_)
        induction x using TensorProduct.induction_on with
        | zero => rfl
        | tmul a n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [hx, hy, add_zero]
      have h1 : Module.length O M = 0 := Module.length_eq_zero_iff.2 inferInstance
      have h2 : Module.length A (TensorProduct O A M) = 0 := Module.length_eq_zero_iff.2 h0
      rw [h1, h2]
    | @of_simple_quotient M _ _ K _ _ ih =>
      have hf : Function.Injective K.subtype := fun a b h => Subtype.ext h
      have hg : Function.Surjective K.mkQ := by
        first
          | exact Submodule.mkQ_surjective K
          | exact Submodule.Quotient.mk_surjective K
      have hfg : Function.Exact K.subtype K.mkQ := LinearMap.exact_subtype_mkQ K
      have hf' : Function.Injective (K.subtype.baseChange A) := by
        first
          | exact Module.Flat.lTensor_preserves_injective_linearMap _ hf
          | exact Module.Flat.lTensor_preserves_injective_linearMap (M := A) _ hf
          | (rw [LinearMap.baseChange_eq_ltensor]; exact Module.Flat.lTensor_preserves_injective_linearMap _ hf)
      have hg' : Function.Surjective (K.mkQ.baseChange A) := by
        first
          | exact LinearMap.lTensor_surjective A hg
          | exact LinearMap.lTensor_surjective _ hg
          | (rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective A hg)
      have hfg' : Function.Exact (K.subtype.baseChange A) (K.mkQ.baseChange A) := by
        first
          | exact lTensor_exact A hfg hg
          | exact lTensor_exact (Q := A) hfg hg
          | exact lTensor_exact hfg hg
          | (rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]; exact lTensor_exact A hfg hg)
      have h1 : Module.length O (M ⧸ K) = 1 := Module.length_eq_one_iff.2 inferInstance
      rw [Module.length_eq_add_of_exact _ _ hf hg hfg,
        Module.length_eq_add_of_exact _ _ hf' hg' hfg', ih, hk (M ⧸ K) inferInstance, h1]
  have mono : ∀ P Q : Submodule O N, P ≤ Q →
      LinearMap.range (P.subtype.baseChange A) ≤ LinearMap.range (Q.subtype.baseChange A) := by
    intro P Q h
    have e : P.subtype = Q.subtype.comp (Submodule.inclusion h) := LinearMap.ext fun _ => rfl
    rw [e, LinearMap.baseChange_comp]
    exact LinearMap.range_comp_le_range _ _
  have key : ∀ P Q : Submodule O N,
      LinearMap.range (Q.subtype.baseChange A) ≤ LinearMap.range (P.subtype.baseChange A) → Q ≤ P := by
    intro P Q h
    have hz : P.mkQ.comp P.subtype = 0 :=
      LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero P).2 x.2
    have hg0 : LinearMap.lTensor A (P.mkQ.comp Q.subtype) = 0 := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, hy⟩ :=
        LinearMap.mem_range.1 (h (LinearMap.mem_range_self (Q.subtype.baseChange A) x))
      rw [LinearMap.zero_apply, LinearMap.lTensor_comp, LinearMap.comp_apply]
      change (P.mkQ.baseChange A) ((Q.subtype.baseChange A) x) = 0
      rw [← hy]
      first
        | rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hz, LinearMap.baseChange_zero,
            LinearMap.zero_apply]
        | simp [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hz]
    have hg : P.mkQ.comp Q.subtype = 0 := (Module.FaithfullyFlat.zero_iff_lTensor_zero O A _).2 hg0
    intro n hn
    have h2 : (Submodule.Quotient.mk n : N ⧸ P) = 0 := LinearMap.congr_fun hg ⟨n, hn⟩
    exact (Submodule.Quotient.mk_eq_zero P).1 h2
  have sm : StrictMono (fun P : Submodule O N => LinearMap.range (P.subtype.baseChange A)) := by
    intro P Q hPQ
    exact (mono P Q hPQ.le).lt_of_ne fun h => hPQ.ne (le_antisymm hPQ.le (key P Q h.ge))
  have ineq : Module.length O N ≤ Module.length A (TensorProduct O A N) := by
    have h3 := Order.krullDim_le_of_strictMono _ sm
    rw [← Module.coe_length, ← Module.coe_length] at h3
    exact_mod_cast h3
  by_cases hN : Module.length O N = ⊤
  · rw [hN] at ineq
    rw [hN]
    exact top_le_iff.1 ineq
  · exact fin N (Module.length_ne_top_iff.1 hN)

/- English proof (translation)
Introduce `σ O _ _ _ _ _ N _ _`. Use `haveI : Module.FaithfullyFlat O (Localization.AtPrime (gaussIdeal σ O)) := Module.FaithfullyFlat.of_flat_of_isLocalHom`. Use `length_tensor_eq_length_of_simple_length_one ?_ N` and prove the remaining obligations. Introduce `S _ _ hS`. Take `⟨I, hI, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.1 hS`.

Establish `hIm : I = IsLocalRing.maximalIdeal O` using `IsLocalRing.eq_maximalIdeal hI`. Substitute `hIm` using the available equality. Establish `e1` using `LinearEquiv.length_eq (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Localization.AtPrime (gaussIdeal σ O)) (Localization.AtPrime (gaussIdeal σ O))) e)`. Establish `e2` using `LinearEquiv.length_eq (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime (gaussIdeal σ O)) (IsLocalRing.maximalIdeal O)).toLinearEquiv`. Conclude with `e1.trans (e2.symm.trans (GaussP.length_residue σ O))`.
-/
theorem gaussLocalizationLength_holds : GaussLength := by
  intro σ O _ _ _ _ _ N _ _
  haveI : Module.FaithfullyFlat O (Localization.AtPrime (gaussIdeal σ O)) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine length_tensor_eq_length_of_simple_length_one ?_ N
  intro S _ _ hS
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hS
  have hIm : I = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  subst hIm
  have e1 := LinearEquiv.length_eq (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (Localization.AtPrime (gaussIdeal σ O)) (Localization.AtPrime (gaussIdeal σ O))) e)
  have e2 := LinearEquiv.length_eq (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (Localization.AtPrime (gaussIdeal σ O)) (IsLocalRing.maximalIdeal O)).toLinearEquiv
  exact e1.trans (e2.symm.trans (GaussP.length_residue σ O))

end Formalism.DV
