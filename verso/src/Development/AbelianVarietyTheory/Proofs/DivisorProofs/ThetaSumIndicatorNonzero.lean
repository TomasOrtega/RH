import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.ThetaScaledNe

/- English proof (translation)
Distinguish the cases in `hw : w.IsReal`. Rewrite using `[mixedEmbedding.normAtPlace_apply_of_isReal hw]`. Conclude with `(norm_le_pi_norm _ _).trans (norm_fst_le _)`. Establish `hc : w.IsComplex` using `InfinitePlace.not_isReal_iff_isComplex.mp hw`. Rewrite using `[mixedEmbedding.normAtPlace_apply_of_isComplex hc]`.

Conclude with `(norm_le_pi_norm _ _).trans (norm_snd_le _)`.
-/
theorem normAtPlace_le_norm {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (y : mixedEmbedding.mixedSpace F) : mixedEmbedding.normAtPlace w y ≤ ‖y‖ := by
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
    exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
    exact (norm_le_pi_norm _ _).trans (norm_snd_le _)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hlt : ∀ z : InfinitePlace F, z (y : F) < 1` using `fun z => by`. Use `normAtPlace_le_norm z (mixedEmbedding F (y : F))` as an intermediate fact. Rewrite `this` using `[mixedEmbedding.normAtPlace_apply]`.

Conclude with `this.trans_lt h`. Set `w : InfinitePlace F` to `Classical.arbitrary _`. Use `InfinitePlace.one_le_of_lt_one (w := w) hy (fun z _ => hlt z)` as an intermediate fact. Conclude with `absurd (hlt w) (not_lt.mpr this)`.
-/
theorem one_le_norm_mixedEmbedding {F : Type} [Field F] [NumberField F] {y : 𝓞 F} (hy : y ≠ 0) :
    1 ≤ ‖mixedEmbedding F (y : F)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ z : InfinitePlace F, z (y : F) < 1 := fun z => by
    have := normAtPlace_le_norm z (mixedEmbedding F (y : F))
    rw [mixedEmbedding.normAtPlace_apply] at this
    exact this.trans_lt h
  let w : InfinitePlace F := Classical.arbitrary _
  have := InfinitePlace.one_le_of_lt_one (w := w) hy (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr this)

/- English proof (translation)
Establish `hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (a⁻¹ * ξ i) ≤ 1` using `fun v => by`. Establish `h1` using `h i v`. Establish `e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v = algebraMap F (v.adicCompletion F) (ξ i)` using `rfl`. Rewrite `h1` using `[e, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀]`. Rewrite using `[Valuation.map_mul, map_inv₀]`.

Establish `e1 : Valued.v (algebraMap F (v.adicCompletion F) a) = v.valuation F a` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a`. Establish `e2 : Valued.v (algebraMap F (v.adicCompletion F) (ξ i)) = v.valuation F (ξ i)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ i)`. Rewrite `h1` using `[e1, e2]`. Conclude with `h1`. Take `⟨y, hy⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `hy' : (y : F) = a⁻¹ * ξ i` using `hy`. Rewrite using `[hy', mul_inv_cancel_left₀ ha]`.
-/
theorem exists_int_of_mem_scaledInt {F : Type} [Field F] [NumberField F] {κ : Type} {a : F} (ha : a ≠ 0)
    {ξ : κ → F} (h : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a)
    (i : κ) : ∃ y : 𝓞 F, ξ i = a * (y : F) := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (a⁻¹ * ξ i) ≤ 1 := fun v => by
    have h1 := h i v
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v = algebraMap F (v.adicCompletion F) (ξ i) := rfl
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀] at h1
    rw [Valuation.map_mul, map_inv₀]
    have e1 : Valued.v (algebraMap F (v.adicCompletion F) a) = v.valuation F a :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) (ξ i)) = v.valuation F (ξ i) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ i)
    rw [e1, e2] at h1
    exact h1
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv
  refine ⟨y, ?_⟩
  have hy' : (y : F) = a⁻¹ * ξ i := hy
  rw [hy', mul_inv_cancel_left₀ ha]

/- English proof (translation)
Introduce `F _ _ κ _ a ha`. Set `V` to `κ → mixedEmbedding.mixedSpace F`. Use `set c : mixedEmbedding.mixedSpace F := mixedEmbedding F a⁻¹ with hc`. Use `set ε : ℝ := 1 / (‖c‖ + 1) with hε`. Establish `hε0 : 0 < ε` using `by positivity`.

Set `b : ContDiffBump (0 : V)` to `⟨ε / 2, ε, half_pos hε0, half_lt_self hε0⟩`. Establish `h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ))` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`. Set `f : SchwartzMap V ℂ` to `h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)`. Establish `hf : ∀ x, f x = ((b x : ℝ) : ℂ)` using `fun x => rfl`. Use `⟨f, ?_⟩` and prove the remaining obligations.

Use `set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) with hg`. Establish `hzero : ∀ ξ : κ → F, ξ ≠ 0 → pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = 0`. Introduce `ξ hξ`. Rewrite using `[pureA_algebraMap]`. Distinguish the cases in `hm : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a`.

Use `mul_eq_zero_of_left ?_ _` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hξ (funext h)`.

Take `⟨y, hy⟩` from `exists_int_of_mem_scaledInt ha hm i`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Conclude with `hi (by simpa using hy)`. Establish `hn1` using `one_le_norm_mixedEmbedding hy0`.

Establish `e : mixedEmbedding F (y : F) = c * mixedEmbedding F (ξ i)`. Rewrite using `[hc, ← map_mul, hy, inv_mul_cancel_left₀ ha]`. Establish `h2 : ‖mixedEmbedding F (ξ i)‖ ≤ ‖(fun j => mixedEmbedding F (ξ j) : V)‖` using `norm_le_pi_norm (fun j => mixedEmbedding F (ξ j)) i`. Establish `h3 : 1 ≤ ‖c‖ * ‖(fun j => mixedEmbedding F (ξ j) : V)‖`. Rewrite `hn1` using `[e]`.

Conclude with `hn1.trans ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))`. Rewrite using `[hf, b.zero_of_le_dist, Complex.ofReal_zero]`. Use `show ε ≤ dist (fun j => mixedEmbedding F (ξ j) : V) 0`. Rewrite using `[dist_zero_right, hε, div_le_iff₀ (by positivity)]`. Use polynomial arithmetic with `[norm_nonneg c, norm_nonneg (fun j => mixedEmbedding F (ξ j) : V)]`.

Use `mul_eq_zero_of_right _ ?_` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `Set.indicator_of_notMem hm _`. Establish `h0 : pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 1`. Rewrite using `[pureA_algebraMap]`.

Establish `hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0`. Use function extensionality and compare the values at `i`. Conclude with `map_zero _`. Establish `hm : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a`. Establish `e : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 0`.

Use function extensionality and compare the values at `i`. Conclude with `map_zero _`. Rewrite using `[e]`. Conclude with `zero_mem _`. Rewrite using `[hx, hf, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε0).le), hg, Set.indicator_of_mem hm]`.

Simplify using the standard rewrite rules. Use `show (∑' ξ : κ → F, pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ≠ 0`. Rewrite using `[tsum_eq_single 0 hzero, h0]`. Conclude with `one_ne_zero`.
-/
theorem exists_thetaSum_scaledInt_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator
        (fun _ => (1 : ℂ)))) ≠ 0 := by
  intro F _ _ κ _ a ha
  let V := κ → mixedEmbedding.mixedSpace F
  set c : mixedEmbedding.mixedSpace F := mixedEmbedding F a⁻¹ with hc
  set ε : ℝ := 1 / (‖c‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  let b : ContDiffBump (0 : V) := ⟨ε / 2, ε, half_pos hε0, half_lt_self hε0⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap V ℂ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  refine ⟨f, ?_⟩
  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) with hg
  have hzero : ∀ ξ : κ → F, ξ ≠ 0 → pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = 0 := by
    intro ξ hξ
    rw [pureA_algebraMap]
    by_cases hm : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a
    · refine mul_eq_zero_of_left ?_ _
      obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
        by_contra h; push_neg at h; exact hξ (funext h)
      obtain ⟨y, hy⟩ := exists_int_of_mem_scaledInt ha hm i
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hi (by simpa using hy)
      have hn1 := one_le_norm_mixedEmbedding hy0
      have e : mixedEmbedding F (y : F) = c * mixedEmbedding F (ξ i) := by
        rw [hc, ← map_mul, hy, inv_mul_cancel_left₀ ha]
      have h2 : ‖mixedEmbedding F (ξ i)‖ ≤ ‖(fun j => mixedEmbedding F (ξ j) : V)‖ :=
        norm_le_pi_norm (fun j => mixedEmbedding F (ξ j)) i
      have h3 : 1 ≤ ‖c‖ * ‖(fun j => mixedEmbedding F (ξ j) : V)‖ := by
        rw [e] at hn1
        exact hn1.trans ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
      rw [hf, b.zero_of_le_dist, Complex.ofReal_zero]
      show ε ≤ dist (fun j => mixedEmbedding F (ξ j) : V) 0
      rw [dist_zero_right, hε, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg c, norm_nonneg (fun j => mixedEmbedding F (ξ j) : V)]
    · refine mul_eq_zero_of_right _ ?_
      rw [hg]
      exact Set.indicator_of_notMem hm _
  have h0 : pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 1 := by
    rw [pureA_algebraMap]
    have hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0 := by
      funext i; exact map_zero _
    have hm : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a := by
      have e : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 0 := by
        funext i; exact map_zero _
      rw [e]; exact zero_mem _
    rw [hx, hf, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε0).le), hg,
      Set.indicator_of_mem hm]
    simp
  show (∑' ξ : κ → F, pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ≠ 0
  rw [tsum_eq_single 0 hzero, h0]
  exact one_ne_zero

end GlobalTheory.ThetaScaledNe

end
