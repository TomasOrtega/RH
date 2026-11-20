import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMulParabolicInductionTrivialStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumCardCyclicVectorsInvariantSubspacesStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassOfCharpolyCardCyclicVectorsStatement

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h U hU hv`. Establish `h1 : U.comap (e : V →ₗ[F] V') = ⊤`. Use `h _ (fun x hx => ?_) hv` and prove the remaining obligations. Use `hU (e x) hx` as an intermediate fact.

Simplify `this` using `[LinearEquiv.conj_apply]`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Establish `: e.symm y ∈ U.comap (e : V →ₗ[F] V')` using `h1 ▸ Submodule.mem_top`. Simplify using `using this`. Introduce `h U hU hv`.

Establish `h1 : U.comap (e.symm : V' →ₗ[F] V) = ⊤`. Use `h _ (fun x hx => ?_) (by simpa using hv)` and prove the remaining obligations. Use `hU (e.symm x) hx` as an intermediate fact. Simplify `this` using `[LinearEquiv.conj_apply]`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations.

Establish `: e y ∈ U.comap (e.symm : V' →ₗ[F] V)` using `h1 ▸ Submodule.mem_top`. Simplify using `using this`.
-/
theorem cyclic_conj {F : Type} [Field F] {V V' : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup V'] [Module F V'] (e : V ≃ₗ[F] V') (g : Module.End F V) (v : V) :
    (∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤) ↔
      (∀ U : Submodule F V', (∀ x ∈ U, (e.conj g) x ∈ U) → e v ∈ U → U = ⊤) := by
  constructor
  · intro h U hU hv
    have h1 : U.comap (e : V →ₗ[F] V') = ⊤ := by
      refine h _ (fun x hx => ?_) hv
      have := hU (e x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e.symm y ∈ U.comap (e : V →ₗ[F] V') := h1 ▸ Submodule.mem_top
    simpa using this
  · intro h U hU hv
    have h1 : U.comap (e.symm : V' →ₗ[F] V) = ⊤ := by
      refine h _ (fun x hx => ?_) (by simpa using hv)
      have := hU (e.symm x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e y ∈ U.comap (e.symm : V' →ₗ[F] V) := h1 ▸ Submodule.mem_top
    simpa using this

/- English proof (translation)
Unfold `glCard`. Conclude with `(Nat.card_pos (α := GL (Fin n) F)).ne'` after adjusting the coercions.
-/
theorem glCard_ne_zero_of_finite (F : Type) [Field F] [Finite F] (n : ℕ) : glCard F n ≠ 0 := by
  unfold glCard
  exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'

/- English proof (translation)
Unfold `mass`. Use `haveI : Finite V := Module.finite_of_finite F`. Use `haveI : Finite (Module.End F V) := Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective`. Establish `hs : {g : Module.End F V | LinearMap.charpoly g = P}.Finite` using `Set.toFinite _`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]`.

Simplify using `[mul_comm]`.
-/
theorem mass_const {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (c : ℂ) (P : F[X]) :
    mass (fun _ : Module.End F V => c) P = c * mass (fun _ : Module.End F V => (1 : ℂ)) P := by
  unfold mass
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective (fun g : Module.End F V => (g : V → V))
    DFunLike.coe_injective
  have hs : {g : Module.End F V | LinearMap.charpoly g = P}.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  simp [mul_comm]

/- English proof (translation)
Unfold `mu`. Establish `h : ∀ n : ℕ, n = 0 → mass (fun _ : Module.End F (Fin n → F) => (1 : ℂ)) 1 / glCard F n = 1`. Introduce and unpack `n rfl`. Establish `h1 : glCard F 0 = 1`. Unfold `glCard`.

Use `haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩`. Rewrite using `[Nat.card_unique]`. Simplify using the standard rewrite rules. Establish `h2 : {g : Module.End F (Fin 0 → F) | LinearMap.charpoly g = 1} = {0}`. Use extensionality with `g`.

Establish `hg : g = 0` using `Subsingleton.elim _ _`. Establish `hc : LinearMap.charpoly g = 1`. Apply `(LinearMap.charpoly_monic g).natDegree_eq_zero.1` to reduce the goal to its premises. Rewrite using `[LinearMap.charpoly_natDegree]`. Simplify using the standard rewrite rules.

Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Conclude with `⟨fun _ => hg, fun _ => hc⟩`. Unfold `mass`. Rewrite using `[h1, h2, finsum_mem_singleton]`. Simplify using the standard rewrite rules.

Conclude with `h _ natDegree_one`.
-/
theorem mu_one (F : Type) [Field F] : mu (1 : F[X]) = 1 := by
  unfold mu
  have h : ∀ n : ℕ, n = 0 →
      mass (fun _ : Module.End F (Fin n → F) => (1 : ℂ)) 1 / glCard F n = 1 := by
    rintro n rfl
    have h1 : glCard F 0 = 1 := by
      unfold glCard
      haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
      rw [Nat.card_unique]
      simp
    have h2 : {g : Module.End F (Fin 0 → F) | LinearMap.charpoly g = 1} = {0} := by
      ext g
      have hg : g = 0 := Subsingleton.elim _ _
      have hc : LinearMap.charpoly g = 1 := by
        apply (LinearMap.charpoly_monic g).natDegree_eq_zero.1
        rw [LinearMap.charpoly_natDegree]
        simp
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun _ => hg, fun _ => hc⟩
    unfold mass
    rw [h1, h2, finsum_mem_singleton]
    simp
  exact h _ natDegree_one

/- English proof (translation)
Introduce `F _ _ P hP`. Use `⟨?_, mu_one F⟩` and prove the remaining obligations. Establish `key` using `GlobalTheory.T.endomorphismMass_mul_parabolic_induction_trivial F (Fin P.natDegree → F) (fun V _ _ _ g => (Nat.card {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) (by`. Introduce `V V' _ _ _ _ _ _ e g`. Use `congr 1`.

Conclude with `(Nat.card_congr (e.toEquiv.subtypeEquiv fun v => cyclic_conj e g v)).symm)`. Use `P hP (by simp)`. Simplify using `only [GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces] at key`. Rewrite `key` using `[mass_const]`. Establish `hr : conv (fun D : F[X] => mass (fun g : Module.End F (Fin D.natDegree → F) => (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F), (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D / glCard F D.natDegree) mu P = conv (fun _ => 1) mu P`.

Unfold `conv`. Use `finsum_mem_congr rfl fun x hx => ?_` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors F x.1 hx.1, div_self (glCard_ne_zero_of_finite F _)]`. Rewrite using `[← hr, ← key]`.

Unfold `mu`. Simplify using `[mul_div_assoc]`.
-/
theorem mu_rec : ∀ (F : Type) [Field F] [Finite F] (P : F[X]), P.Monic →
    (Nat.card F : ℂ) ^ P.natDegree * mu P = conv (fun _ => 1) mu P ∧ mu (1 : F[X]) = 1 := by
  intro F _ _ P hP
  refine ⟨?_, mu_one F⟩
  have key := GlobalTheory.T.endomorphismMass_mul_parabolic_induction_trivial F (Fin P.natDegree → F)
    (fun V _ _ _ g => (Nat.card {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ))
    (by
      intro V V' _ _ _ _ _ _ e g
      congr 1
      exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun v => cyclic_conj e g v)).symm)
    P hP (by simp)
  simp only [GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces] at key
  rw [mass_const] at key
  have hr : conv (fun D : F[X] => mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D / glCard F D.natDegree) mu P
      = conv (fun _ => 1) mu P := by
    unfold conv
    refine finsum_mem_congr rfl fun x hx => ?_
    beta_reduce
    rw [GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors F x.1 hx.1, div_self (glCard_ne_zero_of_finite F _)]
  rw [← hr, ← key]
  unfold mu
  simp [mul_div_assoc]

end GlobalTheory.CuspGL
