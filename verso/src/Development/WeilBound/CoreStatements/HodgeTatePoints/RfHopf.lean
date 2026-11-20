import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsCounitEqOneMulEqZeroOfIsNilpotent

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
open scoped TensorProduct

namespace PositivityTheory.HtPt.Rf

/- English proof (translation)
Establish `h : ∀ a : A, ∃ r : R, algebraMap R C r = φ a` using `fun a => IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := R) a).map φ)`. Use `choose f hf using h`. Establish `inj` using `IsFractionRing.injective R C`. Set `ψ : A →ₐ[R] R` to `{ toFun := f, map_one' := inj (by rw [hf, map_one, map_one]), map_mul' := fun a b => inj (by rw [hf, map_mul, map_mul, hf, hf]), map_zero' := inj (by rw [hf, map_zero, map_zero]), map_add' := fun a b => inj (by rw [hf, map_add, map_add, hf, hf]), commutes' := fun r => inj (by rw …`. Conclude with `⟨ψ, fun a => hf a⟩`.
-/
theorem exists_pt_of_gen {C R A : Type} [Field C] [CommRing R] [IsDomain R] [Algebra R C]
    [IsFractionRing R C] [IsIntegrallyClosed R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] R, ∀ a, algebraMap R C (ψ a) = φ a := by
  have h : ∀ a : A, ∃ r : R, algebraMap R C r = φ a := fun a =>
    IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := R) a).map φ)
  choose f hf using h
  have inj := IsFractionRing.injective R C
  let ψ : A →ₐ[R] R :=
    { toFun := f,
      map_one' := inj (by rw [hf, map_one, map_one]),
      map_mul' := fun a b => inj (by rw [hf, map_mul, map_mul, hf, hf]),
      map_zero' := inj (by rw [hf, map_zero, map_zero]),
      map_add' := fun a b => inj (by rw [hf, map_add, map_add, hf, hf]),
      commutes' := fun r => inj (by rw [hf, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]) }
  exact ⟨ψ, fun a => hf a⟩

noncomputable def evGen (C : Type) {R A : Type} [Field C] [CommRing R] [Algebra R C]
    [CommRing A] [Algebra R A] {N : Type} (pt : N → (A →ₐ[R] R)) : C ⊗[R] A →ₐ[C] (N → C) :=
  AlgHom.pi fun x => Algebra.TensorProduct.lift (AlgHom.id C C) ((Algebra.ofId R C).comp (pt x))
    fun _ _ => Commute.all _ _

/- English proof (translation)
Simplify using `[evGen, Algebra.ofId_apply]`.
-/
theorem evGen_tmul (C : Type) {R A : Type} [Field C] [CommRing R] [Algebra R C]
    [CommRing A] [Algebra R A] {N : Type} (pt : N → (A →ₐ[R] R)) (c : C) (a : A) (x : N) :
    evGen C pt (c ⊗ₜ a) x = c * algebraMap R C (pt x a) := by
  simp [evGen, Algebra.ofId_apply]

/- English proof (translation)
Establish `inj : Function.Injective (algebraMap R C)` using `IsFractionRing.injective R C`. Establish `key : ∀ χ : C ⊗[R] A →ₐ[C] C, ∃ x, ∀ b, χ b = evGen C pt b x`. Introduce `χ`. Take `⟨ψ, hψ⟩` from `exists_pt_of_gen ((χ.restrictScalars R).comp Algebra.TensorProduct.includeRight)`. Take `⟨x, rfl⟩` from `hpt.2 ψ`.

Use `⟨x, fun b => ?_⟩` and prove the remaining obligations. Establish `h : χ = (Pi.evalAlgHom C (fun _ : N => C) x).comp (evGen C pt)`. Apply `Algebra.TensorProduct.ext (Subsingleton.elim _ _)` to reduce the goal to its premises. Use extensionality with `a`. Use `show χ (1 ⊗ₜ a) = evGen C pt (1 ⊗ₜ a) x`.

Rewrite using `[evGen_tmul, one_mul]`. Conclude with `(hψ a).symm`. Rewrite using `[h]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `b hb`. Use `haveI : IsReduced (C ⊗[R] A) := GlobalTheory.isReduced_of_hopfAlgebra_of_isAlgClosed C _`. Use `haveI : IsArtinianRing (C ⊗[R] A) := IsArtinianRing.of_finite C _`. Apply `(IsArtinianRing.equivPi (C ⊗[R] A)).injective` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use function extensionality and compare the values at `m`. Rewrite using `[IsArtinianRing.equivPi_apply]`. Use `haveI := m.isMaximal`. Use `letI : Field ((C ⊗[R] A) ⧸ m.asIdeal) := Ideal.Quotient.field _`.

Establish `bij` using `IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C) (K := (C ⊗[R] A) ⧸ m.asIdeal)`. Set `e` to `AlgEquiv.ofBijective (Algebra.ofId C ((C ⊗[R] A) ⧸ m.asIdeal)) bij`. Take `⟨x, hx⟩` from `key (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m.asIdeal))`. Establish `h1` using `hx b`. Rewrite `h1` using `[hb]`.

Establish `h2 : e.symm (Ideal.Quotient.mk m.asIdeal b) = 0` using `h1`. Establish `h3` using `congrArg e h2`. Rewrite `h3` using `[AlgEquiv.apply_symm_apply, map_zero]`. Conclude with `h3`. Assume the negation of the conclusion as `hns`.

Establish `hlt : LinearMap.range (evGen C pt).toLinearMap < ⊤`. Rewrite using `[lt_top_iff_ne_top]`. Introduce `h`. Apply `hns` to reduce the goal to its premises. Conclude with `LinearMap.range_eq_top.1 h`.

Take `⟨f, hf0, hf⟩` from `Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance`. Establish `hfE : ∀ b, f (evGen C pt b) = 0` using `fun b => by`. Establish `h : f (evGen C pt b) ∈ (LinearMap.range (evGen C pt).toLinearMap).map f` using `⟨evGen C pt b, ⟨b, rfl⟩, rfl⟩`. Rewrite `h` using `[hf]`. Conclude with `(Submodule.mem_bot C).1 h`.

Set `M : N → (C ⊗[R] A →* C)` to `fun x => ((Pi.evalAlgHom C (fun _ : N => C) x).comp (evGen C pt)).toRingHom.toMonoidHom`. Establish `hM : ∀ x b, M x b = evGen C pt b x` using `fun _ _ => rfl`. Establish `hMinj : Function.Injective M`. Introduce `x y hxy`. Apply `hpt.1` to reduce the goal to its premises.

Use extensionality with `a`. Apply `inj` to reduce the goal to its premises. Establish `h` using `congrArg (fun g : C ⊗[R] A →* C => g (1 ⊗ₜ a)) hxy`. Simplify using `only [hM, evGen_tmul, one_mul] at h`. Conclude with `h`.

Establish `hli` using `(linearIndependent_monoidHom (C ⊗[R] A) C).comp M hMinj`. Establish `hsingle : ∀ (x : N) (c : C), (Pi.single x c : N → C) = c • Pi.single x 1`. Introduce `x c`. Use extensionality with `j`. Distinguish the cases in `h : j = x`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Establish `hc` using `Fintype.linearIndependent_iff.1 hli (fun x => f (Pi.single x 1)) (by`. Use function extensionality and compare the values at `b`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp_apply, hM]`. Rewrite using `[← hfE b]`. Use `conv_rhs => rw [← Finset.univ_sum_single (evGen C pt b)]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[hsingle x (evGen C pt b x), map_smul, smul_eq_mul, mul_comm])`. Apply `hf0` to reduce the goal to its premises. Apply `LinearMap.pi_ext` to reduce the goal to its premises. Introduce `x c`. Rewrite using `[hsingle x c, map_smul, hc x, smul_zero]`.

Both sides reduce to the same expression.
-/
theorem evGen_bij {C R A : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing R] [IsDomain R]
    [Algebra R C] [IsFractionRing R C] [IsIntegrallyClosed R] [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] {N : Type} [Fintype N] (pt : N → (A →ₐ[R] R)) (hpt : Function.Bijective pt) :
    Function.Bijective (evGen C pt) := by
  classical
  have inj : Function.Injective (algebraMap R C) := IsFractionRing.injective R C
  have key : ∀ χ : C ⊗[R] A →ₐ[C] C, ∃ x, ∀ b, χ b = evGen C pt b x := by
    intro χ
    obtain ⟨ψ, hψ⟩ := exists_pt_of_gen ((χ.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    obtain ⟨x, rfl⟩ := hpt.2 ψ
    refine ⟨x, fun b => ?_⟩
    have h : χ = (Pi.evalAlgHom C (fun _ : N => C) x).comp (evGen C pt) := by
      apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      ext a
      show χ (1 ⊗ₜ a) = evGen C pt (1 ⊗ₜ a) x
      rw [evGen_tmul, one_mul]
      exact (hψ a).symm
    rw [h]
    rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    haveI : IsReduced (C ⊗[R] A) := GlobalTheory.isReduced_of_hopfAlgebra_of_isAlgClosed C _
    haveI : IsArtinianRing (C ⊗[R] A) := IsArtinianRing.of_finite C _
    apply (IsArtinianRing.equivPi (C ⊗[R] A)).injective
    rw [map_zero]
    funext m
    rw [IsArtinianRing.equivPi_apply]
    haveI := m.isMaximal
    letI : Field ((C ⊗[R] A) ⧸ m.asIdeal) := Ideal.Quotient.field _
    have bij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C) (K := (C ⊗[R] A) ⧸ m.asIdeal)
    let e := AlgEquiv.ofBijective (Algebra.ofId C ((C ⊗[R] A) ⧸ m.asIdeal)) bij
    obtain ⟨x, hx⟩ := key (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m.asIdeal))
    have h1 := hx b
    rw [hb] at h1
    have h2 : e.symm (Ideal.Quotient.mk m.asIdeal b) = 0 := h1
    have h3 := congrArg e h2
    rw [AlgEquiv.apply_symm_apply, map_zero] at h3
    exact h3
  · by_contra hns
    have hlt : LinearMap.range (evGen C pt).toLinearMap < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply hns
      exact LinearMap.range_eq_top.1 h
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    have hfE : ∀ b, f (evGen C pt b) = 0 := fun b => by
      have h : f (evGen C pt b) ∈ (LinearMap.range (evGen C pt).toLinearMap).map f := ⟨evGen C pt b, ⟨b, rfl⟩, rfl⟩
      rw [hf] at h
      exact (Submodule.mem_bot C).1 h
    let M : N → (C ⊗[R] A →* C) := fun x => ((Pi.evalAlgHom C (fun _ : N => C) x).comp (evGen C pt)).toRingHom.toMonoidHom
    have hM : ∀ x b, M x b = evGen C pt b x := fun _ _ => rfl
    have hMinj : Function.Injective M := by
      intro x y hxy
      apply hpt.1
      ext a
      apply inj
      have h := congrArg (fun g : C ⊗[R] A →* C => g (1 ⊗ₜ a)) hxy
      simp only [hM, evGen_tmul, one_mul] at h
      exact h
    have hli := (linearIndependent_monoidHom (C ⊗[R] A) C).comp M hMinj
    have hsingle : ∀ (x : N) (c : C), (Pi.single x c : N → C) = c • Pi.single x 1 := by
      intro x c
      ext j
      by_cases h : j = x
      · subst h; simp
      · simp [Pi.single_apply, h]
    have hc := Fintype.linearIndependent_iff.1 hli (fun x => f (Pi.single x 1)) (by
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp_apply, hM]
      rw [← hfE b]
      conv_rhs => rw [← Finset.univ_sum_single (evGen C pt b)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsingle x (evGen C pt b x), map_smul, smul_eq_mul, mul_comm])
    apply hf0
    apply LinearMap.pi_ext
    intro x c
    rw [hsingle x c, map_smul, hc x, smul_zero]
    rfl

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp A _ _ _ _ _ N _ _ _ pt hbij hadd`. Use `haveI : IsDomain R := hv.hom_inj.isDomain`. Use `haveI : IsFractionRing R C := hv.isFractionRing`. Use `haveI : ValuationRing R := ValuationRing.of_integers v hv`. Establish `hB` using `evGen_bij (C := C) pt hbij`.

Establish `hinjA : Function.Injective (fun a : A => (1 : C) ⊗ₜ[R] a)`. Establish `h1` using `Module.Flat.rTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R C) hv.hom_inj`. Introduce `a b hab`. Apply `(TensorProduct.lid R A).symm.injective` to reduce the goal to its premises. Apply `h1` to reduce the goal to its premises.

Simplify `hab` using `[TensorProduct.lid_symm_apply]`. Establish `sep : ∀ a : A, (∀ x, pt x a = 0) → a = 0`. Introduce `a ha`. Apply `hinjA` to reduce the goal to its premises. Apply `hB.1` to reduce the goal to its premises.

Use function extensionality and compare the values at `x`. Simplify using `only [evGen_tmul, ha x, map_zero, mul_zero, TensorProduct.tmul_zero, Pi.zero_apply]`. Establish `card : Fintype.card N = Module.finrank R A`. Establish `h1` using `(LinearEquiv.ofBijective (evGen C pt).toLinearMap hB).finrank_eq`. Rewrite `h1` using `[Module.finrank_fintype_fun_eq_card, Module.finrank_baseChange]`.

Conclude with `h1.symm`. Establish `hP : ∀ x y, WithConv.toConv (pt (x + y)) = WithConv.toConv (pt x) * WithConv.toConv (pt y)`. Introduce `x y`. Apply `WithConv.ofConv_injective` to reduce the goal to its premises. Use extensionality with `a`.

Rewrite using `[hadd, AlgHom.convMul_apply]`. Establish `h0 : WithConv.toConv (pt 0) = (1 : WithConv (A →ₐ[R] R))`. Establish `h` using `hP 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_left_cancel (a := WithConv.toConv (pt 0)) (by rw [mul_one, ← h])`.

Establish `hS : ∀ x a, pt (-x) a = pt x (HopfAlgebra.antipode R a)`. Introduce `x a`. Establish `hn : WithConv.toConv (pt (-x)) = (WithConv.toConv (pt x))⁻¹`. Rewrite using `[eq_inv_iff_mul_eq_one, ← hP, neg_add_cancel, h0]`. Establish `h` using `congrArg (fun f : WithConv (A →ₐ[R] R) => (WithConv.ofConv f) a) hn`.

Conclude with `h`. Set `E : A →ₗ[R] (N → C)` to `LinearMap.pi (fun x => (Algebra.linearMap R C).comp (pt x).toLinearMap)`. Establish `hE : ∀ a x, E a x = algebraMap R C (pt x a)` using `fun _ _ => rfl`. Use `⟨sep, card, ⟨{ carrier := LinearMap.range E, lat := ?_, le_int := ?_, one_mem := ?_, mul_mem := ?_, comul := ?_, antipode := ?_ }, ?_⟩⟩` and prove the remaining obligations. Establish `hc : Fintype.card N = Fintype.card (Module.Free.ChooseBasisIndex R A)`.

Rewrite using `[card, Module.finrank_eq_card_chooseBasisIndex]`. Set `b : Module.Basis N R A` to `(Module.Free.chooseBasis R A).reindex (Fintype.equivOfCardEq hc).symm`. Set `bc : Module.Basis N C (C ⊗[R] A)` to `Algebra.TensorProduct.basis C b`. Set `le` to `LinearEquiv.ofBijective (evGen C pt).toLinearMap hB`. Use `⟨LinearMap.toMatrix bc (Pi.basisFun C N) le, LinearEquiv.isUnit_det le bc (Pi.basisFun C N), ?_⟩` and prove the remaining obligations.

Establish `hcol : (fun j x => LinearMap.toMatrix bc (Pi.basisFun C N) le x j) = E ∘ b`. Use function extensionality and compare the values at `j x`. Rewrite using `[LinearMap.toMatrix_apply, Pi.basisFun_repr]`. Use `show evGen C pt (bc j) x = _`. Rewrite using `[Algebra.TensorProduct.basis_apply, evGen_tmul, one_mul]`.

Both sides reduce to the same expression. Rewrite using `[hcol, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]`. Introduce and unpack `g ⟨a, rfl⟩ x`. Conclude with `⟨pt x a, rfl⟩`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Simplify using `[hE]`. Introduce and unpack `f g ⟨a, rfl⟩ ⟨b, rfl⟩`. Use `⟨a * b, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `[hE]`. Introduce and unpack `f ⟨a, rfl⟩`. Establish `gen : ∀ t : A ⊗[R] A, (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) t)) ∈ tensorSpan R (LinearMap.range E)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero`. Establish `h : (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) (0 : A ⊗[R] A))) = 0`. Use function extensionality and compare the values at `q`. Simplify using the standard rewrite rules. Rewrite using `[h]`.

Conclude with `zero_mem _`. Consider the case `tmul a b`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨E a, ⟨a, rfl⟩, E b, ⟨b, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`.

Simplify using `[hE]`. Consider the case `add s t hs ht`. Establish `h : (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) (s + t))) = (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) s)) + (fun q : N × N => algebraMap R C (Algebra. …`. Use function extensionality and compare the values at `q`. Simplify using the standard rewrite rules.

Rewrite using `[h]`. Conclude with `add_mem hs ht`. Establish `h` using `gen (Coalgebra.comul a)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `q`.

Use `show E a (q.1 + q.2) = _`. Rewrite using `[hE, hadd]`. Introduce and unpack `f ⟨a, rfl⟩`. Use `⟨HopfAlgebra.antipode R a, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Rewrite using `[hE, hE, hS]`. Introduce `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨a, rfl⟩`.

Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨a, rfl⟩`.
-/
theorem hopfalg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Free R A], ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ pt : N → (A →ₐ[R] R), Function.Bijective pt → (∀ x y a, pt (x + y) a = Algebra.TensorProduct.lift (pt x) (pt y) (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := R) a)) → (∀ a : A, (∀ x, pt x a = 0) → a = 0) ∧ Fintype.card N = Module.finrank R A ∧ ∃ AA : HopfOrder (C := C) R N, ∀ g, g ∈ AA.carrier ↔ ∃ a : A, g = fun x => algebraMap R C (pt x a) := by
  intro p _ C _ _ _ v R _ _ hv hp A _ _ _ _ _ N _ _ _ pt hbij hadd
  classical
  haveI : IsDomain R := hv.hom_inj.isDomain
  haveI : IsFractionRing R C := hv.isFractionRing
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  have hB := evGen_bij (C := C) pt hbij
  have hinjA : Function.Injective (fun a : A => (1 : C) ⊗ₜ[R] a) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R C) hv.hom_inj
    intro a b hab
    apply (TensorProduct.lid R A).symm.injective
    apply h1
    simpa [TensorProduct.lid_symm_apply] using hab
  have sep : ∀ a : A, (∀ x, pt x a = 0) → a = 0 := by
    intro a ha
    apply hinjA
    apply hB.1
    funext x
    simp only [evGen_tmul, ha x, map_zero, mul_zero, TensorProduct.tmul_zero, Pi.zero_apply]
  have card : Fintype.card N = Module.finrank R A := by
    have h1 := (LinearEquiv.ofBijective (evGen C pt).toLinearMap hB).finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_baseChange] at h1
    exact h1.symm
  have hP : ∀ x y, WithConv.toConv (pt (x + y)) = WithConv.toConv (pt x) * WithConv.toConv (pt y) := by
    intro x y
    apply WithConv.ofConv_injective
    ext a
    rw [hadd, AlgHom.convMul_apply]
  have h0 : WithConv.toConv (pt 0) = (1 : WithConv (A →ₐ[R] R)) := by
    have h := hP 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := WithConv.toConv (pt 0)) (by rw [mul_one, ← h])
  have hS : ∀ x a, pt (-x) a = pt x (HopfAlgebra.antipode R a) := by
    intro x a
    have hn : WithConv.toConv (pt (-x)) = (WithConv.toConv (pt x))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hP, neg_add_cancel, h0]
    have h := congrArg (fun f : WithConv (A →ₐ[R] R) => (WithConv.ofConv f) a) hn
    exact h
  let E : A →ₗ[R] (N → C) := LinearMap.pi (fun x => (Algebra.linearMap R C).comp (pt x).toLinearMap)
  have hE : ∀ a x, E a x = algebraMap R C (pt x a) := fun _ _ => rfl
  refine ⟨sep, card, ⟨{ carrier := LinearMap.range E, lat := ?_, le_int := ?_, one_mem := ?_, mul_mem := ?_, comul := ?_, antipode := ?_ }, ?_⟩⟩
  · have hc : Fintype.card N = Fintype.card (Module.Free.ChooseBasisIndex R A) := by
      rw [card, Module.finrank_eq_card_chooseBasisIndex]
    let b : Module.Basis N R A := (Module.Free.chooseBasis R A).reindex (Fintype.equivOfCardEq hc).symm
    let bc : Module.Basis N C (C ⊗[R] A) := Algebra.TensorProduct.basis C b
    let le := LinearEquiv.ofBijective (evGen C pt).toLinearMap hB
    refine ⟨LinearMap.toMatrix bc (Pi.basisFun C N) le, LinearEquiv.isUnit_det le bc (Pi.basisFun C N), ?_⟩
    have hcol : (fun j x => LinearMap.toMatrix bc (Pi.basisFun C N) le x j) = E ∘ b := by
      funext j x
      rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
      show evGen C pt (bc j) x = _
      rw [Algebra.TensorProduct.basis_apply, evGen_tmul, one_mul]
      rfl
    rw [hcol, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
  · rintro g ⟨a, rfl⟩ x
    exact ⟨pt x a, rfl⟩
  · refine ⟨1, ?_⟩
    funext x
    simp [hE]
  · rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    funext x
    simp [hE]
  · rintro f ⟨a, rfl⟩
    have gen : ∀ t : A ⊗[R] A, (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) t)) ∈ tensorSpan R (LinearMap.range E) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero =>
        have h : (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) (0 : A ⊗[R] A))) = 0 := by
          funext q
          simp
        rw [h]
        exact zero_mem _
      | tmul a b =>
        apply Submodule.subset_span
        refine ⟨E a, ⟨a, rfl⟩, E b, ⟨b, rfl⟩, ?_⟩
        funext q
        simp [hE]
      | add s t hs ht =>
        have h : (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) (s + t))) = (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) s)) + (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) t)) := by
          funext q
          simp
        rw [h]
        exact add_mem hs ht
    have h := gen (Coalgebra.comul a)
    convert h using 1
    funext q
    show E a (q.1 + q.2) = _
    rw [hE, hadd]
  · rintro f ⟨a, rfl⟩
    refine ⟨HopfAlgebra.antipode R a, ?_⟩
    funext x
    rw [hE, hE, hS]
  · intro g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩

end PositivityTheory.HtPt.Rf
