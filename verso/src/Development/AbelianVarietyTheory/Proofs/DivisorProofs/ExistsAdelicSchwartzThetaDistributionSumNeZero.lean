import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.ThetaSumNe

/- English proof (translation)
Introduce `F _ _ κ _`. Set `V` to `κ → mixedEmbedding.mixedSpace F`. Set `b : ContDiffBump (0 : V)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ))` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`. Set `f : SchwartzMap V ℂ` to `h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)`.

Establish `hf : ∀ x, f x = ((b x : ℝ) : ℂ)` using `fun x => rfl`. Set `g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ` to `(GlobalTheory.SchANonzero.intPts F κ).indicator 1`. Establish `hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)` using `GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ`. Establish `hmem : pureA F f g ∈ schA F κ` using `Submodule.subset_span ⟨f, g, hg, rfl⟩`. Use `⟨pureA F f g, hmem, ?_⟩` and prove the remaining obligations.

Use `set t : (κ → F) → ℂ := fun ξ => pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) with ht`. Establish `hsum : Summable t` using `summable_pureA F f hg`. Establish `hre : ∀ ξ, (t ξ).re = b (fun i => mixedEmbedding F (ξ i)) * (g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))).re` using `fun ξ => by`. Simplify using `only [ht, pureA_algebraMap, hf, Complex.re_ofReal_mul]`. Establish `hg0 : ∀ y, 0 ≤ (g y).re` using `fun y => by`.

Distinguish the cases in `hy : y ∈ GlobalTheory.SchANonzero.intPts F κ`. Simplify using `[g, Set.indicator_of_mem hy]`. Simplify using `[g, Set.indicator_of_notMem hy]`. Establish `hnn : ∀ ξ, 0 ≤ (t ξ).re` using `fun ξ => by`. Rewrite using `[hre]`.

Conclude with `mul_nonneg (b.nonneg) (hg0 _)`. Establish `hz : (t 0).re = 1`. Rewrite using `[hre]`. Establish `h0 : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈ GlobalTheory.SchANonzero.intPts F κ` using `fun i _ v => by show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0) v ∈ v.adicCompletionIntegers F`. Rewrite using `[map_zero]`.

Conclude with `zero_mem (v.adicCompletionIntegers F)`. Establish `hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0`. Use function extensionality and compare the values at `i`. Conclude with `map_zero _`. Rewrite using `[hx, b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]`.

Simplify using `only [g, Set.indicator_of_mem h0, Pi.one_apply, Complex.one_re, one_mul]`. Establish `hpos : 0 < ∑' ξ, (t ξ).re` using `(Complex.reCLM.summable hsum).tsum_pos hnn 0 (by show 0 < (t 0).re; rw [hz]; exact one_pos)`. Introduce `h`. Establish `: (thetaSum F (pureA F f g)).re = ∑' ξ, (t ξ).re` using `Complex.re_tsum hsum`. Rewrite `this` using `[h, Complex.zero_re]`.

Conclude with `hpos.ne' this.symm`.
-/
theorem exists_mem_schA_thetaSum_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ φ ∈ schA F κ, thetaSum F φ ≠ 0 := by
  intro F _ _ κ _
  classical
  let V := κ → mixedEmbedding.mixedSpace F
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap V ℂ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  have hmem : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨pureA F f g, hmem, ?_⟩
  set t : (κ → F) → ℂ := fun ξ => pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) with ht
  have hsum : Summable t := summable_pureA F f hg
  have hre : ∀ ξ, (t ξ).re = b (fun i => mixedEmbedding F (ξ i)) *
      (g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))).re := fun ξ => by
    simp only [ht, pureA_algebraMap, hf, Complex.re_ofReal_mul]
  have hg0 : ∀ y, 0 ≤ (g y).re := fun y => by
    by_cases hy : y ∈ GlobalTheory.SchANonzero.intPts F κ
    · simp [g, Set.indicator_of_mem hy]
    · simp [g, Set.indicator_of_notMem hy]
  have hnn : ∀ ξ, 0 ≤ (t ξ).re := fun ξ => by
    rw [hre]; exact mul_nonneg (b.nonneg) (hg0 _)
  have hz : (t 0).re = 1 := by
    rw [hre]
    have h0 : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈
        GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0) v ∈ v.adicCompletionIntegers F
      rw [map_zero]
      exact zero_mem (v.adicCompletionIntegers F)
    have hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0 := by
      funext i; exact map_zero _
    rw [hx, b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
    simp only [g, Set.indicator_of_mem h0, Pi.one_apply, Complex.one_re, one_mul]
  have hpos : 0 < ∑' ξ, (t ξ).re :=
    (Complex.reCLM.summable hsum).tsum_pos hnn 0 (by show 0 < (t 0).re; rw [hz]; exact one_pos)
  intro h
  have : (thetaSum F (pureA F f g)).re = ∑' ξ, (t ξ).re := Complex.re_tsum hsum
  rw [h, Complex.zero_re] at this
  exact hpos.ne' this.symm

end GlobalTheory.ThetaSumNe

end
