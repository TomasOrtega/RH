import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideDef
import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

section Ten

variable {Kf : Type} [Field Kf] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

/- English proof (translation)
Establish `hKK : IsFractionRing Kf Kf` using `jr_KK Kf`. Establish `hLI : ∀ s, LinearIndependent Kf (fun i => ((b s i : V s) : MvPolynomial (Fin k × Fin n) Kf))` using `fun s => (b s).linearIndependent.map' (V s).subtype (Submodule.ker_subtype _)`. Establish `hsp : ∀ s, Submodule.span Kf (Set.range fun i => ((b s i : V s) : MvPolynomial (Fin k × Fin n) Kf)) = V s`. Introduce `s`. Establish `: (Set.range fun i => ((b s i : V s) : MvPolynomial (Fin k × Fin n) Kf)) = (V s).subtype '' Set.range (b s)`.

Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span, (b s).span_eq, Submodule.map_top, Submodule.range_subtype]`. Take `⟨kL, kS⟩` from `tensorBasis Kf Kf S k n I V _ hLI hsp`. Use `⟨(Module.Basis.span kL).map (LinearEquiv.ofEq _ _ kS), fun i => ?_⟩` and prove the remaining obligations.

Use `show (((LinearEquiv.ofEq _ _ kS) (Module.Basis.span kL i) : tensorLat Kf Kf V) : MvPolynomial (S × (Fin k × Fin n)) Kf) = _`. Rewrite using `[LinearEquiv.coe_ofEq_apply]`. Conclude with `congrArg Subtype.val (Module.Basis.span_apply kL i)`.
-/
theorem prodBasis (V : S → Submodule Kf (MvPolynomial (Fin k × Fin n) Kf)) {I : S → Type}
    (b : ∀ s, Module.Basis (I s) Kf (V s)) :
    ∃ x : Module.Basis (∀ s, I s) Kf (tensorLat Kf Kf V),
      ∀ i, ((x i : tensorLat Kf Kf V) : MvPolynomial (S × (Fin k × Fin n)) Kf) =
        ∏ s, blockEmb Kf s ((b s (i s) : V s) : MvPolynomial (Fin k × Fin n) Kf) := by
  have hKK : IsFractionRing Kf Kf := jr_KK Kf
  have hLI : ∀ s, LinearIndependent Kf (fun i => ((b s i : V s) : MvPolynomial (Fin k × Fin n) Kf)) :=
    fun s => (b s).linearIndependent.map' (V s).subtype (Submodule.ker_subtype _)
  have hsp : ∀ s, Submodule.span Kf
      (Set.range fun i => ((b s i : V s) : MvPolynomial (Fin k × Fin n) Kf)) = V s := by
    intro s
    have : (Set.range fun i => ((b s i : V s) : MvPolynomial (Fin k × Fin n) Kf)) =
        (V s).subtype '' Set.range (b s) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, (b s).span_eq, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨kL, kS⟩ := tensorBasis Kf Kf S k n I V _ hLI hsp
  refine ⟨(Module.Basis.span kL).map (LinearEquiv.ofEq _ _ kS), fun i => ?_⟩
  show (((LinearEquiv.ofEq _ _ kS) (Module.Basis.span kL i) : tensorLat Kf Kf V) :
    MvPolynomial (S × (Fin k × Fin n)) Kf) = _
  rw [LinearEquiv.coe_ofEq_apply]
  exact congrArg Subtype.val (Module.Basis.span_apply kL i)

/- English proof (translation)
Use `set c : (∀ s, I s) → Kf := fun p => ∏ s, (b s).repr (F s) (p s) with hc`. Establish `hT' : T = ∑ p, c p • x p`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hT, Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul, hx]`.

Establish `hF : ∀ s, ((F s : V s) : MvPolynomial (Fin k × Fin n) Kf) = ∑ j, (b s).repr (F s) j • ((b s j : V s) : MvPolynomial (Fin k × Fin n) Kf)`. Introduce `s`. Use `conv_lhs => rw [← (b s).sum_repr (F s)]`. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`.

Simplify using `only [hF, map_sum, map_smul]`. Rewrite using `[Finset.prod_univ_sum]`. Use `Finset.sum_congr (by simp) fun p _ => ?_` and prove the remaining obligations. Simplify using `only [hc, MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]`. Rewrite using `[hT']`.

Use `first`. Consider the case `rw [Module.Basis.repr_sum_self]`. Consider the case `simp [map_sum, Finsupp.single_apply, hc]`.
-/
theorem repr_prod (V : S → Submodule Kf (MvPolynomial (Fin k × Fin n) Kf)) {I : S → Type} [∀ s, Fintype (I s)]
    (b : ∀ s, Module.Basis (I s) Kf (V s)) (x : Module.Basis (∀ s, I s) Kf (tensorLat Kf Kf V))
    (hx : ∀ i, ((x i : tensorLat Kf Kf V) : MvPolynomial (S × (Fin k × Fin n)) Kf) =
        ∏ s, blockEmb Kf s ((b s (i s) : V s) : MvPolynomial (Fin k × Fin n) Kf))
    (F : ∀ s, V s) (T : tensorLat Kf Kf V)
    (hT : (T : MvPolynomial (S × (Fin k × Fin n)) Kf) =
      ∏ s, blockEmb Kf s ((F s : V s) : MvPolynomial (Fin k × Fin n) Kf)) (i : ∀ s, I s) :
    x.repr T i = ∏ s, (b s).repr (F s) (i s) := by
  classical
  set c : (∀ s, I s) → Kf := fun p => ∏ s, (b s).repr (F s) (p s) with hc
  have hT' : T = ∑ p, c p • x p := by
    apply Subtype.ext
    rw [hT, Submodule.coe_sum]
    simp only [Submodule.coe_smul, hx]
    have hF : ∀ s, ((F s : V s) : MvPolynomial (Fin k × Fin n) Kf) =
        ∑ j, (b s).repr (F s) j • ((b s j : V s) : MvPolynomial (Fin k × Fin n) Kf) := by
      intro s
      conv_lhs => rw [← (b s).sum_repr (F s)]
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
    simp only [hF, map_sum, map_smul]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr (by simp) fun p _ => ?_
    simp only [hc, MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  rw [hT']
  first
  | rw [Module.Basis.repr_sum_self]
  | simp [map_sum, Finsupp.single_apply, hc]

end Ten

section Dual

variable {Kf : Type} [Field Kf]

def dualB {V : Type} [AddCommGroup V] [Module Kf V] {I : Type} [Fintype I] [DecidableEq I]
    (β : V ≃ₗ[Kf] Module.Dual Kf V) (Z : Module.Basis I Kf V) : Module.Basis I Kf V :=
  Z.dualBasis.map β.symm

/- English proof (translation)
Unfold `dualB`. Rewrite using `[Module.Basis.map_apply, LinearEquiv.apply_symm_apply]`. Use extensionality with `x`. Simplify using `[Module.Basis.dualBasis_apply]`.
-/
theorem beta_dualB {V : Type} [AddCommGroup V] [Module Kf V] {I : Type} [Fintype I] [DecidableEq I]
    (β : V ≃ₗ[Kf] Module.Dual Kf V) (Z : Module.Basis I Kf V) (j : I) : β (dualB β Z j) = Z.coord j := by
  unfold dualB
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  ext x
  simp [Module.Basis.dualBasis_apply]

/- English proof (translation)
Unfold `dualB`. Simplify using `[Module.Basis.map_repr, Module.Basis.dualBasis_repr]`.
-/
theorem dualB_repr {V : Type} [AddCommGroup V] [Module Kf V] {I : Type} [Fintype I] [DecidableEq I]
    (β : V ≃ₗ[Kf] Module.Dual Kf V) (b : Module.Basis I Kf V) (Q : V) (a : I) :
    (dualB β b).repr Q a = β Q (b a) := by
  unfold dualB
  simp [Module.Basis.map_repr, Module.Basis.dualBasis_repr]

end Dual

section Psi

variable {Kf : Type} [Field Kf] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

/- English proof (translation)
Take `⟨x, hx⟩` from `prodBasis V b`. Take `⟨x', hx'⟩` from `prodBasis V (fun s => dualB (β s) (b s))`. Use `⟨x.dualBasis.equiv x' (Equiv.refl _), ?_⟩` and prove the remaining obligations. Introduce `Z z z' hz hz' j`. Establish `hΨ : ∀ (φ : Module.Dual Kf (tensorLat Kf Kf V)) i, x'.repr ((x.dualBasis.equiv x' (Equiv.refl _)) φ) i = φ (x i)`.

Introduce `φ i`. Establish `h1 : (x.dualBasis.equiv x' (Equiv.refl _)) φ = ∑ a, φ (x a) • x' a` using `by conv_lhs => rw [← x.dualBasis.sum_repr φ]`. Rewrite using `[map_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`.

Rewrite using `[map_smul, Module.Basis.equiv_apply, Module.Basis.dualBasis_repr, Equiv.refl_apply]`. Rewrite using `[h1, x'.repr_sum_self]`. Apply `x'.ext_elem` to reduce the goal to its premises. Introduce `i`. Rewrite using `[hΨ, Module.Basis.coord_apply, repr_prod V Z z hz (fun s => b s (i s)) (x i) (hx i) j, repr_prod V (fun s => dualB (β s) (b s)) x' hx' (fun s => dualB (β s) (Z s) (j s)) (z' j) (hz' j) i]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `s _`. Rewrite using `[dualB_repr, beta_dualB, Module.Basis.coord_apply]`.
-/
theorem psi_exists (V : S → Submodule Kf (MvPolynomial (Fin k × Fin n) Kf))
    (β : ∀ s, V s ≃ₗ[Kf] Module.Dual Kf (V s)) {I : S → Type} [∀ s, Fintype (I s)] [∀ s, DecidableEq (I s)]
    (b : ∀ s, Module.Basis (I s) Kf (V s)) :
    ∃ Ψ : Module.Dual Kf (tensorLat Kf Kf V) ≃ₗ[Kf] tensorLat Kf Kf V,
      ∀ (Z : ∀ s, Module.Basis (I s) Kf (V s)) (z z' : Module.Basis (∀ s, I s) Kf (tensorLat Kf Kf V)),
        (∀ i, ((z i : tensorLat Kf Kf V) : MvPolynomial (S × (Fin k × Fin n)) Kf) =
          ∏ s, blockEmb Kf s ((Z s (i s) : V s) : MvPolynomial (Fin k × Fin n) Kf)) →
        (∀ i, ((z' i : tensorLat Kf Kf V) : MvPolynomial (S × (Fin k × Fin n)) Kf) =
          ∏ s, blockEmb Kf s ((dualB (β s) (Z s) (i s) : V s) : MvPolynomial (Fin k × Fin n) Kf)) →
        ∀ j, Ψ (z.coord j) = z' j := by
  obtain ⟨x, hx⟩ := prodBasis V b
  obtain ⟨x', hx'⟩ := prodBasis V (fun s => dualB (β s) (b s))
  refine ⟨x.dualBasis.equiv x' (Equiv.refl _), ?_⟩
  intro Z z z' hz hz' j
  have hΨ : ∀ (φ : Module.Dual Kf (tensorLat Kf Kf V)) i,
      x'.repr ((x.dualBasis.equiv x' (Equiv.refl _)) φ) i = φ (x i) := by
    intro φ i
    have h1 : (x.dualBasis.equiv x' (Equiv.refl _)) φ = ∑ a, φ (x a) • x' a := by
      conv_lhs => rw [← x.dualBasis.sum_repr φ]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_smul, Module.Basis.equiv_apply, Module.Basis.dualBasis_repr, Equiv.refl_apply]
    rw [h1, x'.repr_sum_self]
  apply x'.ext_elem
  intro i
  rw [hΨ, Module.Basis.coord_apply, repr_prod V Z z hz (fun s => b s (i s)) (x i) (hx i) j,
    repr_prod V (fun s => dualB (β s) (b s)) x' hx' (fun s => dualB (β s) (Z s) (j s)) (z' j) (hz' j) i]
  apply Finset.prod_congr rfl
  intro s _
  rw [dualB_repr, beta_dualB, Module.Basis.coord_apply]

end Psi

end Formalism.L2.G.Model
