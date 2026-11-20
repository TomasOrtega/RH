import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWordLeIntegralOfAevalCasimirEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftTranslateSmoothCommuteLeftInvariantOpsStatement
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons X l ih`. Use function extensionality and compare the values at `g`. Simplify using `only [List.foldr_cons, ih]`.

Simplify using `only [IsExpLieAlgebra.rightDeriv, mul_assoc]`.
-/
theorem solGFam_foldr_rightDeriv_leftTranslate (l : List 𝔤) (f : G → ℂ) (x : G) :
    l.foldr h.rightDeriv (fun y => f (x * y)) = fun y => l.foldr h.rightDeriv f (x * y) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    funext g
    simp only [List.foldr_cons, ih]
    simp only [IsExpLieAlgebra.rightDeriv, mul_assoc]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact hf`. Consider the case `cons X l ih => exact h.isSmoothFun_rightDeriv ih X`.
-/
theorem solGFam_isSmoothFun_foldr_rightDeriv (l : List 𝔤) {f : G → ℂ} (hf : h.IsSmoothFun f) :
    h.IsSmoothFun (l.foldr h.rightDeriv f) := by
  induction l with
  | nil => exact hf
  | cons X l ih => exact h.isSmoothFun_rightDeriv ih X

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons X l ih`. Simplify using `only [List.foldr_cons, ih]`. Establish `h1` using `GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h l hf`.

Establish `h2` using `GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h l hf'`. Establish `h3 : h.IsSmoothFun (c • l.foldr h.rightDeriv f)` using `(h.smoothFuns (F := ℂ)).smul_mem c h1`. Rewrite using `[h.rightDeriv_add h3 h2, h.rightDeriv_smul h1]`.
-/
theorem solGFam_foldr_rightDeriv_smul_add (l : List 𝔤) {f f' : G → ℂ} (hf : h.IsSmoothFun f)
    (hf' : h.IsSmoothFun f') (c : ℂ) :
    l.foldr h.rightDeriv (c • f + f') = c • l.foldr h.rightDeriv f + l.foldr h.rightDeriv f' := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons, ih]
    have h1 := GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h l hf
    have h2 := GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h l hf'
    have h3 : h.IsSmoothFun (c • l.foldr h.rightDeriv f) := (h.smoothFuns (F := ℂ)).smul_mem c h1
    rw [h.rightDeriv_add h3 h2, h.rightDeriv_smul h1]

end GlobalTheory.HCA

/- English proof (translation)
Introduce `𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf`. Take `⟨hs, -⟩` from `(mem_solG h b).1 hf`. Use `letI := h.chartedSpace`.

Conclude with `ContMDiff.continuous hs`. Introduce `f hf g`. Take `⟨hs, h0⟩` from `(mem_solG h b).1 hf`. Take `⟨f', hf'1, hf'2⟩` from `GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps 𝔸 G 𝔤 h ⟨f, hs⟩ g`. Establish `hΔ : (∑ i, h.rightDerivEnd (F` using `ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) := Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩)`.

Establish `hT : Polynomial.aeval (∑ i, h.rightDerivEnd (F` using `ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) := Algebra.adjoin_le (Set.singleton_subset_iff.2 hΔ) (Polynomial.aeval_mem_adjoin_singleton ℂ _)`. Establish `e : (f' : G → ℂ) = fun y => f (g * y)` using `funext hf'1`. Rewrite using `[mem_solG]`. Use `⟨e ▸ f'.2, ?_⟩` and prove the remaining obligations. Establish `hf'eq : (⟨fun y => f (g * y), e ▸ f'.2⟩ : h.smoothFuns (F` using `ℂ)) = f' := Subtype.ext e.symm`.

Rewrite using `[hf'eq]`. Use extensionality with `y`. Rewrite using `[hf'2 _ hT y, h0]`. Both sides reduce to the same expression. Take `⟨K, hK, hC⟩` from `GlobalTheory.T.exists_compact_derivWord_bound_of_aeval_casimir 𝔸 G 𝔤 h d b P hP μ hμ`.

Use `⟨K, hK, fun l₀ => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `l f hf f' hf' c`. Take `⟨hs, -⟩` from `(mem_solG h b).1 hf`. Take `⟨hs', -⟩` from `(mem_solG h b).1 hf'`. Simplify using `only [GlobalTheory.HCA.solGFam_foldr_rightDeriv_smul_add h _ hs hs' c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Introduce `l`. Take `⟨C, hC'⟩` from `hC (l.map b ++ l₀)`. Use `⟨C, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨hs, h0⟩` from `(mem_solG h b).1 hf`. Conclude with `hC' ⟨f, hs⟩ h0`.

Introduce `l i f hf`. Take `⟨hs, -⟩` from `(mem_solG h b).1 hf`. Establish `hL` using `GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h (l.map b ++ l₀) hs`. Establish `hd` using `h.hasDerivAt_rightDeriv hL (b i) 1`. Simplify using `only [List.map_cons, List.cons_append, List.foldr_cons]`.

Use `hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [GlobalTheory.HCA.solGFam_foldr_rightDeriv_leftTranslate h, mul_one, one_mul]`.
-/
theorem GlobalTheory.HCA.solG_smFn : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → (∀ f ∈ solG h b P, Continuous f) ∧ (∀ f ∈ solG h b P, ∀ g, (fun y => f (g * y)) ∈ solG h b P) ∧ ∃ K : Set G, IsCompact K ∧ ∀ l₀ : List 𝔤, SmFn h b μ (solG h b P) K fun l f => (l.map b ++ l₀).foldr h.rightDeriv f 1 := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP _ _ μ hμ
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨hs, -⟩ := (mem_solG h b).1 hf
    letI := h.chartedSpace
    exact ContMDiff.continuous hs
  · intro f hf g
    obtain ⟨hs, h0⟩ := (mem_solG h b).1 hf
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps 𝔸 G 𝔤 h ⟨f, hs⟩ g
    have hΔ : (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ∈
        Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩)
    have hT : Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P ∈
        Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hΔ) (Polynomial.aeval_mem_adjoin_singleton ℂ _)
    have e : (f' : G → ℂ) = fun y => f (g * y) := funext hf'1
    rw [mem_solG]
    refine ⟨e ▸ f'.2, ?_⟩
    have hf'eq : (⟨fun y => f (g * y), e ▸ f'.2⟩ : h.smoothFuns (F := ℂ)) = f' := Subtype.ext e.symm
    rw [hf'eq]
    ext y
    rw [hf'2 _ hT y, h0]
    rfl
  · obtain ⟨K, hK, hC⟩ := GlobalTheory.T.exists_compact_derivWord_bound_of_aeval_casimir 𝔸 G 𝔤 h d b P hP μ hμ
    refine ⟨K, hK, fun l₀ => ⟨?_, ?_, ?_⟩⟩
    · intro l f hf f' hf' c
      obtain ⟨hs, -⟩ := (mem_solG h b).1 hf
      obtain ⟨hs', -⟩ := (mem_solG h b).1 hf'
      simp only [GlobalTheory.HCA.solGFam_foldr_rightDeriv_smul_add h _ hs hs' c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · intro l
      obtain ⟨C, hC'⟩ := hC (l.map b ++ l₀)
      refine ⟨C, fun f hf => ?_⟩
      obtain ⟨hs, h0⟩ := (mem_solG h b).1 hf
      exact hC' ⟨f, hs⟩ h0
    · intro l i f hf
      obtain ⟨hs, -⟩ := (mem_solG h b).1 hf
      have hL := GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv h (l.map b ++ l₀) hs
      have hd := h.hasDerivAt_rightDeriv hL (b i) 1
      simp only [List.map_cons, List.cons_append, List.foldr_cons]
      refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [GlobalTheory.HCA.solGFam_foldr_rightDeriv_leftTranslate h, mul_one, one_mul]
