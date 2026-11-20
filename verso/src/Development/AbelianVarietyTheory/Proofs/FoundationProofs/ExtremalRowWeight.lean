import Mathlib
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeightStatement

open GlobalTheory.DualWeyl MvPolynomial NumberField
open Formalism.GradedWeylDivisibility (rowAct rowW rowNu)
open Formalism.REAL (fockF)
open scoped Matrix ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.DualWeylFock

variable {N : ℕ} {la : Fin N → ℕ}

/- English proof (translation)
Rewrite using `[Formalism.REAL.fischerInner_eq_sum_of_subset _ _ f.support support_smul, fockF, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_smul_left {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) : fockF (c • f) g = c * fockF f g := by
  rw [Formalism.REAL.fischerInner_eq_sum_of_subset _ _ f.support support_smul, fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

def fockLeft {σ : Type} (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun f := fockF f g
  map_add' f f' := Formalism.REAL.fischerInner_add_left f f' g
  map_smul' c f := fock_smul_left c f g

/- English proof (translation)
Establish `hnu : rowNu (r` using `N) la = la := by`. Use function extensionality and compare the values at `b`. Simplify using `[rowNu]`. Use `Formalism.GradedWeylDivisibility.hwRowWeight ℂ N N le_rfl la hla` as an intermediate fact. Rewrite `this` using `[hnu]`. Then use the resulting hypothesis.
-/
theorem extremal_rowWeight (hla : Antitone la) : IsWeightedHomogeneous (rowW N N) (extremal la ℂ) la := by
  have hnu : rowNu (r := N) la = la := by
    funext b
    simp [rowNu]
  have := Formalism.GradedWeylDivisibility.hwRowWeight ℂ N N le_rfl la hla
  rwa [hnu] at this

/- English proof (translation)
Take `⟨a, ha⟩` from `Function.ne_iff.mp hμ`. Set `t : Fin N → ℂ` to `fun b => if b = a then 2 else 1`. Establish `hprod : ∀ e : Fin N → ℕ, ∏ b, t b ^ e b = 2 ^ e a`. Introduce `e`. Rewrite using `[Finset.prod_eq_single a]`.

Simplify using `[t]`. Introduce `b _ hb`. Simplify using `[t, hb]`. Simplify using the standard rewrite rules. Establish `h1` using `evalAt_rowAct 1 (Matrix.diagonal t) q`.

Establish `h2` using `evalAt_colAct 1 (Matrix.diagonal t) q`. Rewrite `h1` using `[Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ N N t μ _ hw, hprod, Matrix.mul_one, map_smul, smul_eq_mul]`. Rewrite `h2` using `[colAct_of_mem hq _ (Matrix.blockTriangular_diagonal t), Matrix.one_mul, map_smul, smul_eq_mul]`. Simplify using `only [diagChar, Matrix.diagonal_apply_eq] at h2`. Rewrite `h2` using `[hprod]`.

Establish `hne : (2 : ℂ) ^ μ a - 2 ^ la a ≠ 0`. Rewrite using `[sub_ne_zero]`. Introduce `h`. Establish `h' : (2 : ℕ) ^ μ a = 2 ^ la a` using `by exact_mod_cast h`. Conclude with `ha (Nat.pow_right_injective le_rfl h')`.

Establish `: ((2 : ℂ) ^ μ a - 2 ^ la a) * evalAt 1 q = 0` using `by rw [sub_mul, h1, h2, sub_self]`. Conclude with `(mul_eq_zero.mp this).resolve_left hne`.
-/
theorem evalAt_one_of_ne {μ : Fin N → ℕ} (hμ : μ ≠ la) {q : Pol N ℂ} (hq : q ∈ nabla la ℂ)
    (hw : IsWeightedHomogeneous (rowW N N) q μ) : evalAt 1 q = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hμ
  let t : Fin N → ℂ := fun b => if b = a then 2 else 1
  have hprod : ∀ e : Fin N → ℕ, ∏ b, t b ^ e b = 2 ^ e a := by
    intro e
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb; simp [t, hb]
    · simp
  have h1 := evalAt_rowAct 1 (Matrix.diagonal t) q
  have h2 := evalAt_colAct 1 (Matrix.diagonal t) q
  rw [Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ N N t μ _ hw, hprod, Matrix.mul_one, map_smul, smul_eq_mul] at h1
  rw [colAct_of_mem hq _ (Matrix.blockTriangular_diagonal t), Matrix.one_mul, map_smul, smul_eq_mul] at h2
  simp only [diagChar, Matrix.diagonal_apply_eq] at h2
  rw [hprod] at h2
  have hne : (2 : ℂ) ^ μ a - 2 ^ la a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h' : (2 : ℕ) ^ μ a = 2 ^ la a := by exact_mod_cast h
    exact ha (Nat.pow_right_injective le_rfl h')
  have : ((2 : ℂ) ^ μ a - 2 ^ la a) * evalAt 1 q = 0 := by rw [sub_mul, h1, h2, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

/- English proof (translation)
Establish `hfin` using `weightedHomogeneousComponent_finsupp (w := rowW N N) f`. Establish `hsum` using `sum_weightedHomogeneousComponent (rowW N N) f`. Rewrite `hsum` using `[finsum_eq_sum _ hfin]`. Rewrite using `[← hsum, Formalism.REAL.fischerInner_sum_left, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations.

Establish `hmem` using `Formalism.GradedWeylDivisibility.dualWeylRowGraded ℂ N N la μ f hf`. Establish `hw'` using `weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW N N) μ f`. Distinguish the cases in `hμ : μ = la`. Substitute `hμ conv_lhs => rw [GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight ℂ N μ hla _ hmem hw']` using the available equality. Rewrite using `[fock_smul_left]`.

Rewrite using `[evalAt_one_of_ne hμ hmem hw', zero_mul]`. Conclude with `Formalism.GradedWeylDivisibility.fockWeightOrth _ _ _ μ la _ _ hμ hw' (extremal_rowWeight hla)`.
-/
theorem fock_extremal (hla : Antitone la) {f : Pol N ℂ} (hf : f ∈ nabla la ℂ) :
    fockF f (extremal la ℂ) = evalAt 1 f * fockF (extremal la ℂ) (extremal la ℂ) := by
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW N N) f
  have hsum := sum_weightedHomogeneousComponent (rowW N N) f
  rw [finsum_eq_sum _ hfin] at hsum
  rw [← hsum, Formalism.REAL.fischerInner_sum_left, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hmem := Formalism.GradedWeylDivisibility.dualWeylRowGraded ℂ N N la μ f hf
  have hw' := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW N N) μ f
  by_cases hμ : μ = la
  · subst hμ
    conv_lhs => rw [GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight ℂ N μ hla _ hmem hw']
    rw [fock_smul_left]
  · rw [evalAt_one_of_ne hμ hmem hw', zero_mul]
    exact Formalism.GradedWeylDivisibility.fockWeightOrth _ _ _ μ la _ _ hμ hw' (extremal_rowWeight hla)

/- English proof (translation)
Establish `: CompleteSpace (Space la)` using `FiniteDimensional.complete ℂ _`. Set `φ : Space la →ₗ[ℂ] ℂ` to `ψ ∘ₗ (nabla la ℂ).subtype ∘ₗ (toSpace la).symm.toLinearMap`. Set `v : Space la` to `(InnerProductSpace.toDual ℂ (Space la)).symm (LinearMap.toContinuousLinearMap φ)`. Use `⟨((toSpace la).symm v).1, ((toSpace la).symm v).2, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h1 : ⟪v, toSpace la ⟨f, hf⟩⟫_ℂ = φ (toSpace la ⟨f, hf⟩)` using `InnerProductSpace.toDual_symm_apply`.

Conclude with `h1`.
-/
theorem exists_form_eq (ψ : Pol N ℂ →ₗ[ℂ] ℂ) : ∃ h ∈ nabla la ℂ, ∀ f ∈ nabla la ℂ, form la f h = ψ f := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  let φ : Space la →ₗ[ℂ] ℂ := ψ ∘ₗ (nabla la ℂ).subtype ∘ₗ (toSpace la).symm.toLinearMap
  let v : Space la := (InnerProductSpace.toDual ℂ (Space la)).symm (LinearMap.toContinuousLinearMap φ)
  refine ⟨((toSpace la).symm v).1, ((toSpace la).symm v).2, fun f hf => ?_⟩
  have h1 : ⟪v, toSpace la ⟨f, hf⟩⟫_ℂ = φ (toSpace la ⟨f, hf⟩) := InnerProductSpace.toDual_symm_apply
  exact h1

/- English proof (translation)
Introduce `f hf f' hf'`. Take `⟨hre, him⟩` from `Formalism.GradedWeylDivisibility.fockPos _ (extremal la ℂ) extremal_ne_zero`. Use `set c := fockF (extremal la ℂ) (extremal la ℂ) with hc`. Establish `hc0 : c ≠ 0` using `fun h => by rw [h] at hre; simp at hre`. Establish `hcc : conj c = c` using `Complex.conj_eq_iff_im.mpr him`.

Take `⟨h, hh, H⟩` from `exists_form_eq (la := la) (c⁻¹ • fockLeft f')`. Establish `H' : ∀ g ∈ nabla la ℂ, form la g h = fockF g f' / c` using `fun g hg => by`. Rewrite using `[H g hg, div_eq_inv_mul]`. Both sides reduce to the same expression. Establish `hE` using `extremal_mem (R := ℂ) hla`.

Establish `key : h = f'`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_evalAt_unitary (Submodule.sub_mem _ hh hf') fun u => ?_` and prove the remaining obligations. Establish `hst : ∀ (g : Matrix (Fin N) (Fin N) ℂ), ∀ p ∈ nabla la ℂ, rowAct ℂ g p ∈ nabla la ℂ` using `fun g p hp => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N la g p hp`. Establish `h1` using `H' _ (hst (u.1)ᴴ _ hE)`.

Establish `h2 : rowAct ℂ u.1 (rowAct ℂ (u.1)ᴴ (extremal la ℂ)) = extremal la ℂ`. Establish `h3 : (u.1)ᴴ * u.1 = 1` using `Matrix.mem_unitaryGroup_iff'.mp u.2`. Rewrite using `[← AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowActMul ℂ N N, h3, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]`. Both sides reduce to the same expression. Rewrite `h1` using `[← form_rowAct u, h2, Formalism.GradedWeylDivisibility.fockRowAdj, Matrix.conjTranspose_conjTranspose, ← conj_form, (GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one N la hla).1 _ (hst _ _ hh), Formalism.GradedWeylDivisibility.fockHerm, fock_extremal hla (hst _ _ hf'), eva …`.

Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `(starRingEnd ℂ).injective h1`. Rewrite using `[← H' f hf, key]`.
-/
theorem form_eq_fock_div (N : ℕ) (la : Fin N → ℕ) (hla : Antitone la) :
    ∀ f ∈ nabla la ℂ, ∀ f' ∈ nabla la ℂ,
      form la f f' = fockF f f' / fockF (extremal la ℂ) (extremal la ℂ) := by
  intro f hf f' hf'
  obtain ⟨hre, him⟩ := Formalism.GradedWeylDivisibility.fockPos _ (extremal la ℂ) extremal_ne_zero
  set c := fockF (extremal la ℂ) (extremal la ℂ) with hc
  have hc0 : c ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hcc : conj c = c := Complex.conj_eq_iff_im.mpr him
  obtain ⟨h, hh, H⟩ := exists_form_eq (la := la) (c⁻¹ • fockLeft f')
  have H' : ∀ g ∈ nabla la ℂ, form la g h = fockF g f' / c := fun g hg => by
    rw [H g hg, div_eq_inv_mul]; rfl
  have hE := extremal_mem (R := ℂ) hla
  have key : h = f' := by
    rw [← sub_eq_zero]
    refine eq_zero_of_evalAt_unitary (Submodule.sub_mem _ hh hf') fun u => ?_
    have hst : ∀ (g : Matrix (Fin N) (Fin N) ℂ), ∀ p ∈ nabla la ℂ, rowAct ℂ g p ∈ nabla la ℂ :=
      fun g p hp => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N la g p hp
    have h1 := H' _ (hst (u.1)ᴴ _ hE)
    have h2 : rowAct ℂ u.1 (rowAct ℂ (u.1)ᴴ (extremal la ℂ)) = extremal la ℂ := by
      have h3 : (u.1)ᴴ * u.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp u.2
      rw [← AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowActMul ℂ N N, h3, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
      rfl
    rw [← form_rowAct u, h2, Formalism.GradedWeylDivisibility.fockRowAdj, Matrix.conjTranspose_conjTranspose, ← conj_form,
      (GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one N la hla).1 _ (hst _ _ hh), Formalism.GradedWeylDivisibility.fockHerm, fock_extremal hla (hst _ _ hf'),
      evalAt_rowAct, evalAt_rowAct, Matrix.mul_one, ← hc, ← starRingEnd_apply, map_mul, hcc,
      mul_div_cancel_right₀ _ hc0] at h1
    rw [map_sub, sub_eq_zero]
    exact (starRingEnd ℂ).injective h1
  rw [← H' f hf, key]

end GlobalTheory.DualWeylFock
