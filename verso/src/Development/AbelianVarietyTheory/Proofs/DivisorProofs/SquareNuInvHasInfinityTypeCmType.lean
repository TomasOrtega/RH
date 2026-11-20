import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

/- English proof (translation)
Introduce `D T L sc μ₀ hL G i j k`. Establish `a1 : 1 ≤ D.R.m - i` using `by have := i.2; omega`. Establish `a2 : D.R.m - i ≤ D.R.m` using `by omega`. Take `⟨n', hn', hinf⟩` from `(L.C.isMu0 j).inf`. Establish `hk : ∀ τ, Formalism.L2.Host.embTau D τ (k : D.host.E) ≠ 0` using `fun τ => by simp`.

Rewrite using `[nuH, hL.xi_base, mul_one, div_eq_mul_inv, HChar.inf_inv, HChar.inf_mul, HChar.inf_inv, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_inv_eq_inv_val, hinf k, G.ch.inf _ a1 a2 k, ← D.eTau.prod_comp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distr …`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h1 : n' (D.eTau τ) = -(2 * (num D sc.cGap τ).e (j + 1))`. Use `hn' (D.eTau τ)` as an intermediate fact. Use `beta_reduce at this`.

Rewrite `this` using `[Formalism.L2.Host.eExp, Equiv.symm_apply_apply, (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D sc.cGap) (cen D sc.cGap τ)).2.2]`. Establish `h2 : ((n' (D.eTau τ) : ℤ) : ℚ) = ((-(2 * (num D sc.cGap τ).e (j + 1)) : ℤ) : ℚ)`. Rewrite using `[this]`. Use `push_cast`. Unfold `num`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h2` after adjusting the coercions. Establish `hne : (Formalism.L2.Host.embTau D τ (k : D.host.E) / ((‖Formalism.L2.Host.embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ≠ 0` using `div_ne_zero (hk τ) (by simpa using hk τ)`. Use `beta_reduce`. Rewrite using `[h1]`.

Express the relevant statement in the definitionally equal form `((Formalism.L2.Host.embTau D τ (k : D.host.E) / ((‖Formalism.L2.Host.embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ _ * _)⁻¹ = _`. Rewrite using `[← zpow_neg, ← zpow_add₀ hne, ← zpow_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nuH_inv_hasInf : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), (nuH G μ₀ i j)⁻¹.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  intro D T L sc μ₀ hL G i j k
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  obtain ⟨n', hn', hinf⟩ := (L.C.isMu0 j).inf
  have hk : ∀ τ, Formalism.L2.Host.embTau D τ (k : D.host.E) ≠ 0 := fun τ => by simp
  rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv, HChar.inf_inv, HChar.inf_mul, HChar.inf_inv, Units.val_inv_eq_inv_val,
    Units.val_mul, Units.val_inv_eq_inv_val, hinf k, G.ch.inf _ a1 a2 k, ← D.eTau.prod_comp, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 : n' (D.eTau τ) = -(2 * (num D sc.cGap τ).e (j + 1)) := by
    have := hn' (D.eTau τ)
    beta_reduce at this
    rw [Formalism.L2.Host.eExp, Equiv.symm_apply_apply,
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D sc.cGap) (cen D sc.cGap τ)).2.2] at this
    have h2 : ((n' (D.eTau τ) : ℤ) : ℚ) = ((-(2 * (num D sc.cGap τ).e (j + 1)) : ℤ) : ℚ) := by
      rw [this]; push_cast; unfold num; ring
    exact_mod_cast h2
  have hne : (Formalism.L2.Host.embTau D τ (k : D.host.E) / ((‖Formalism.L2.Host.embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ≠ 0 :=
    div_ne_zero (hk τ) (by simpa using hk τ)
  beta_reduce
  rw [h1]
  change ((Formalism.L2.Host.embTau D τ (k : D.host.E) / ((‖Formalism.L2.Host.embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ _ * _)⁻¹ = _
  rw [← zpow_neg, ← zpow_add₀ hne, ← zpow_neg]
  congr 1
  ring

end GlobalTheory.FunObj.SqNum
