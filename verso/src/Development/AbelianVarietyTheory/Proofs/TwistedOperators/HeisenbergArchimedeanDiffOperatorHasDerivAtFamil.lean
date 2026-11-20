import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

noncomputable section

namespace GlobalTheory.HeisOrbit.DOpDeriv

/- English proof (translation)
Establish `hd : Differentiable ℝ H` using `hH.differentiable (by norm_num)`. Establish `hd1 : Differentiable ℝ (fderiv ℝ H)` using `(hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)`. Establish `h1 : ∀ (t : ℝ) (v : E), fderiv ℝ (fun z => H (t, z)) y v = fderiv ℝ H (t, y) (0, v)`. Introduce `t v`. Use `((hd (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).fderiv` as an intermediate fact.

Establish `e : (fun z => H (t, z)) = H ∘ (fun z => (t, z))` using `rfl`. Rewrite using `[e, this]`. Simplify using the standard rewrite rules. Establish `h2 : g = fun z => fderiv ℝ H (0, z) (1, 0)`. Use function extensionality and compare the values at `z`.

Establish `hc : HasDerivAt (fun t : ℝ => (t, z)) ((1 : ℝ), (0 : E)) 0` using `(hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z)`. Use `(hd (0, z)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc` as an intermediate fact. Conclude with `(hg z).unique this`. Establish `h3 : ∀ v : E, fderiv ℝ g y v = fderiv ℝ (fderiv ℝ H) (0, y) (0, v) (1, 0)`. Introduce `v`.

Establish `a` using `(hd1 (0, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (0 : ℝ) y)`. Establish `b` using `(a.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E)) y)).fderiv`. Establish `e : g = fun z => ((fderiv ℝ H) ∘ (fun z => ((0 : ℝ), z))) z (1, 0)` using `h2`. Rewrite using `[e, b]`. Simplify using the standard rewrite rules.

Establish `hs : IsSymmSndFDerivAt ℝ H (0, y)` using `hH.contDiffAt.isSymmSndFDerivAt (by simp)`. Establish `hc : HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : E)) 0` using `(hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)`. Establish `a` using `(hd1 (0, y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc`. Establish `hQ : HasDerivAt (fun t : ℝ => ((0 : ℝ), P t)) ((0 : ℝ), P') 0` using `(hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk hP`. Establish `b` using `a.clm_apply hQ`.

Simplify using `only [h1, h3]`. Rewrite using `[hs.eq (0, P 0) (1, 0)]`. Conclude with `b`.
-/
theorem hasDerivAt_fderiv_family {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ × E → ℂ) (hH : ContDiff ℝ 2 H) (g : E → ℂ)
    (hg : ∀ y, HasDerivAt (fun t => H (t, y)) (g y) 0) (P : ℝ → E) (P' : E) (hP : HasDerivAt P P' 0) (y : E) :
    HasDerivAt (fun t => fderiv ℝ (fun z => H (t, z)) y (P t))
      (fderiv ℝ g y (P 0) + fderiv ℝ (fun z => H (0, z)) y P') 0 := by
  have hd : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (fderiv ℝ H) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : ∀ (t : ℝ) (v : E), fderiv ℝ (fun z => H (t, z)) y v = fderiv ℝ H (t, y) (0, v) := by
    intro t v
    have := ((hd (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).fderiv
    have e : (fun z => H (t, z)) = H ∘ (fun z => (t, z)) := rfl
    rw [e, this]
    simp
  have h2 : g = fun z => fderiv ℝ H (0, z) (1, 0) := by
    funext z
    have hc : HasDerivAt (fun t : ℝ => (t, z)) ((1 : ℝ), (0 : E)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z)
    have := (hd (0, z)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    exact (hg z).unique this
  have h3 : ∀ v : E, fderiv ℝ g y v = fderiv ℝ (fderiv ℝ H) (0, y) (0, v) (1, 0) := by
    intro v
    have a := (hd1 (0, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (0 : ℝ) y)
    have b := (a.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E)) y)).fderiv
    have e : g = fun z => ((fderiv ℝ H) ∘ (fun z => ((0 : ℝ), z))) z (1, 0) := h2
    rw [e, b]
    simp
  have hs : IsSymmSndFDerivAt ℝ H (0, y) :=
    hH.contDiffAt.isSymmSndFDerivAt (by simp)
  have hc : HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : E)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)
  have a := (hd1 (0, y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hQ : HasDerivAt (fun t : ℝ => ((0 : ℝ), P t)) ((0 : ℝ), P') 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk hP
  have b := a.clm_apply hQ
  simp only [h1, h3]
  rw [hs.eq (0, P 0) (1, 0)]
  exact b

/- English proof (translation)
Introduce `F _ _ κ _ G P Q g' P' Q' hG hg hP hQ y`. Establish `h1` using `hasDerivAt_fderiv_family (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) (hG.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) g' hg P P' hP y`. Set `L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ` to `{ toFun := fun q => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * q i) map_add' := by`. Introduce `a b`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]`.

Use the proof step `map_smul' := by`. Introduce `c a`. Simplify using `only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, RingHom.id_apply] }`. Establish `h2 : HasDerivAt (fun t => L (Q t)) (L Q') 0` using `(LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hQ`. Establish `h3` using `((h2.ofReal_comp.const_mul (2 * Real.pi * Complex.I : ℂ)).mul (hg y))`.

Establish `h4` using `h1.sub h3`. Use `HasDerivAt.congr_deriv (f := fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) h4 ?_` and prove the remaining obligations. Use `symm`. Simplify using `only [GlobalTheory.HeisOrbit.dOp]`. Express the relevant statement in the definitionally equal form `_ = fderiv ℝ g' y (P 0) + fderiv ℝ (G 0) y P' - (2 * Real.pi * Complex.I * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q' i) : ℝ) : ℂ) * G 0 y + 2 * Real.pi * Complex.I * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q 0 i) : ℝ) : ℂ) * g' y)`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dOp_hasDerivAt : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F))
    (g' : SInf F κ) (P' Q' : κ → mixedEmbedding.mixedSpace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    (∀ y, HasDerivAt (fun t => G t y) (g' y) 0) → HasDerivAt P P' 0 → HasDerivAt Q Q' 0 → ∀ y,
    HasDerivAt (fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) (GlobalTheory.HeisOrbit.dOp (P 0) (Q 0) g' y + GlobalTheory.HeisOrbit.dOp P' Q' (G 0) y) 0 := by
  intro F _ _ κ _ G P Q g' P' Q' hG hg hP hQ y
  have h1 := hasDerivAt_fderiv_family (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2)
    (hG.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) g' hg P P' hP y
  let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    { toFun := fun q => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * q i)
      map_add' := by
        intro a b
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]
      map_smul' := by
        intro c a
        simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, RingHom.id_apply] }
  have h2 : HasDerivAt (fun t => L (Q t)) (L Q') 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hQ
  have h3 := ((h2.ofReal_comp.const_mul (2 * Real.pi * Complex.I : ℂ)).mul (hg y))
  have h4 := h1.sub h3
  refine HasDerivAt.congr_deriv (f := fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) h4 ?_
  symm
  simp only [GlobalTheory.HeisOrbit.dOp]
  change _ = fderiv ℝ g' y (P 0) + fderiv ℝ (G 0) y P' - (2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q' i) : ℝ) : ℂ) * G 0 y + 2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q 0 i) : ℝ) : ℂ) * g' y)
  ring

end GlobalTheory.HeisOrbit.DOpDeriv
