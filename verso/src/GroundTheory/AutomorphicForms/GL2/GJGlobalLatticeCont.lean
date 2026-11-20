import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalLatticeBounds

open MeasureTheory NumberField Topology Filter Set
open scoped NumberField.AdeleRing Classical nonZeroDivisors

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open GroundTheory.Global GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Establish `hF` using `continuous_of_mem_schwartzBruhatPi (mem_matrixSchwartzBruhat.mp hΦ)`. Establish `h : Φ = (fun z : Fin n × Fin n → 𝔸[K] => Φ (Matrix.of fun i j => z (i, j))) ∘ (fun X : Matrix (Fin n) (Fin n) 𝔸[K] => fun p : Fin n × Fin n => X p.1 p.2)` using `rfl`. Rewrite using `[h]`. Conclude with `hF.comp (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)`.
-/
theorem continuous_of_mem_matrixSchwartzBruhat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) : Continuous Φ := by
  have hF := continuous_of_mem_schwartzBruhatPi (mem_matrixSchwartzBruhat.mp hΦ)
  have h : Φ = (fun z : Fin n × Fin n → 𝔸[K] => Φ (Matrix.of fun i j => z (i, j))) ∘
      (fun X : Matrix (Fin n) (Fin n) 𝔸[K] => fun p : Fin n × Fin n => X p.1 p.2) := rfl
  rw [h]
  exact hF.comp (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)

/- English proof (translation)
Establish `hc : Continuous fun g : AdelicGLn.AdelicGL K n => ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])` using `Units.continuous_val.comp continuous_inv`. Unfold `infNorm`. Use `continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun w _ => continuous_norm.comp ?_` and prove the remaining obligations. Conclude with `(continuous_apply w).comp (continuous_fst.comp (hc.matrix_elem i j))`.
-/
theorem continuous_infNorm_coe_inv : Continuous fun g : AdelicGLn.AdelicGL K n =>
    infNorm ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  have hc : Continuous fun g : AdelicGLn.AdelicGL K n =>
      ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) :=
    Units.continuous_val.comp continuous_inv
  unfold infNorm
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun w _ => continuous_norm.comp ?_
  exact (continuous_apply w).comp (continuous_fst.comp (hc.matrix_elem i j))

/- English proof (translation)
The claim follows from `Real.rpow_le_rpow s.2.le h (inv_nonneg.2 (by positivity))`.
-/
theorem centralScale_mono {s t : {r : ℝ // 0 < r}} (h : (s : ℝ) ≤ t) :
    centralScale (K := K) n s ≤ centralScale (K := K) n t :=
  Real.rpow_le_rpow s.2.le h (inv_nonneg.2 (by positivity))

/- English proof (translation)
Use `set M : ℕ := Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) + 1 with hM`. Take `⟨C₁, hC₁, I, hmaj⟩` from `exists_majorant hΦ M`. Use `set Q : Set (Matrix (Fin n) (Fin n) 𝔸ᶠ[K]) := (fun g : AdelicGLn.AdelicGL K n => finMat ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) '' (A ∪ B) with hQ`. Establish `hQc : IsCompact Q` using `(hA.union hB).image (continuous_finMat_coe.comp continuous_inv)`. Take `⟨J, hJ⟩` from `exists_ideal_mul_mul hQc I`.

Take `⟨R, hR⟩` from `(hA.union hB).exists_bound_of_continuousOn (continuous_infNorm_coe_inv (K := K) (n := n)).continuousOn`. Use `set m : ℝ := (max 1 (centralScale (K := K) n t₁)⁻¹) ^ M with hm`. Establish `hm0 : 0 ≤ m` using `pow_nonneg (zero_le_one.trans (le_max_left _ _)) M`. Use `set R' : ℝ := 1 + max R 0 with hR'`. Use `⟨fun ξ => C₁ * m * (R' * R') ^ M * latticeWeight J M ξ, (summable_latticeWeight J (by omega)).mul_left _, fun t ht a ha b hb ξ => ?_⟩` and prove the remaining obligations.

Establish `hpt` using `norm_le_twistedWeight hC₁ hmaj t a⁻¹ b ξ`. Rewrite `hpt` using `[inv_inv]`. Establish `hxQ : finMat ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q` using `⟨a, Or.inl ha, rfl⟩`. Establish `hyQ : finMat ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q` using `⟨b, Or.inr hb, rfl⟩`. Establish `htw` using `twistedWeight_le hJ M hxQ hyQ ξ`.

Establish `hRa : infNorm ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ≤ max R 0`. Use `hR a (Or.inl ha)` as an intermediate fact. Rewrite `this` using `[Real.norm_of_nonneg (infNorm_nonneg _)]`. Conclude with `this.trans (le_max_left _ _)`. Establish `hRb : infNorm ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ≤ max R 0`.

Use `hR b (Or.inr hb)` as an intermediate fact. Rewrite `this` using `[Real.norm_of_nonneg (infNorm_nonneg _)]`. Conclude with `this.trans (le_max_left _ _)`. Establish `hmt : (max 1 (centralScale (K` using `K) n t)⁻¹) ^ M ≤ m := by`. Use `pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (max_le_max le_rfl ?_) M` and prove the remaining obligations.

Conclude with `inv_anti₀ (centralScale_pos n t₁) (centralScale_mono ht)`. Establish `hlw` using `latticeWeight_nonneg J M ξ`. Establish `hcomb : ((1 + infNorm ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) * (1 + infNorm ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) ^ M ≤ (R' * R') ^ M`. Use `pow_le_pow_left₀ (mul_nonneg (by linarith [infNorm_nonneg ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])]) (by linarith [infNorm_nonneg ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])])) ?_ M` and prove the remaining obligations. Conclude with `mul_le_mul (by linarith) (by linarith) (by linarith [infNorm_nonneg ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])]) (by linarith [le_max_right R 0])`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_summable_bound {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (t₁ : {r : ℝ // 0 < r})
    {A B : Set (AdelicGLn.AdelicGL K n)} (hA : IsCompact A) (hB : IsCompact B) :
    ∃ u : Matrix (Fin n) (Fin n) K → ℝ, Summable u ∧ ∀ t : {r : ℝ // 0 < r}, (t₁ : ℝ) ≤ t →
      ∀ a ∈ A, ∀ b ∈ B, ∀ ξ, ‖Φ (((Reduction.centralSection K n t * a : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (b : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ u ξ := by
  set M : ℕ := Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) + 1 with hM
  obtain ⟨C₁, hC₁, I, hmaj⟩ := exists_majorant hΦ M
  set Q : Set (Matrix (Fin n) (Fin n) 𝔸ᶠ[K]) := (fun g : AdelicGLn.AdelicGL K n =>
    finMat ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) '' (A ∪ B) with hQ
  have hQc : IsCompact Q := (hA.union hB).image (continuous_finMat_coe.comp continuous_inv)
  obtain ⟨J, hJ⟩ := exists_ideal_mul_mul hQc I
  obtain ⟨R, hR⟩ := (hA.union hB).exists_bound_of_continuousOn
    (continuous_infNorm_coe_inv (K := K) (n := n)).continuousOn
  set m : ℝ := (max 1 (centralScale (K := K) n t₁)⁻¹) ^ M with hm
  have hm0 : 0 ≤ m := pow_nonneg (zero_le_one.trans (le_max_left _ _)) M
  set R' : ℝ := 1 + max R 0 with hR'
  refine ⟨fun ξ => C₁ * m * (R' * R') ^ M * latticeWeight J M ξ,
    (summable_latticeWeight J (by omega)).mul_left _, fun t ht a ha b hb ξ => ?_⟩
  have hpt := norm_le_twistedWeight hC₁ hmaj t a⁻¹ b ξ
  rw [inv_inv] at hpt
  have hxQ : finMat ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q :=
    ⟨a, Or.inl ha, rfl⟩
  have hyQ : finMat ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q :=
    ⟨b, Or.inr hb, rfl⟩
  have htw := twistedWeight_le hJ M hxQ hyQ ξ
  have hRa : infNorm ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ≤ max R 0 := by
    have := hR a (Or.inl ha)
    rw [Real.norm_of_nonneg (infNorm_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  have hRb : infNorm ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ≤ max R 0 := by
    have := hR b (Or.inr hb)
    rw [Real.norm_of_nonneg (infNorm_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  have hmt : (max 1 (centralScale (K := K) n t)⁻¹) ^ M ≤ m := by
    refine pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (max_le_max le_rfl ?_) M
    exact inv_anti₀ (centralScale_pos n t₁) (centralScale_mono ht)
  have hlw := latticeWeight_nonneg J M ξ
  have hcomb : ((1 + infNorm ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) *
      (1 + infNorm ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) ^ M ≤
      (R' * R') ^ M := by
    refine pow_le_pow_left₀ (mul_nonneg (by linarith [infNorm_nonneg ((a⁻¹ :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])]) (by linarith [infNorm_nonneg ((b⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])])) ?_ M
    exact mul_le_mul (by linarith) (by linarith)
      (by linarith [infNorm_nonneg ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])])
      (by linarith [le_max_right R 0])
  calc ‖Φ (((Reduction.centralSection K n t * a : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (b : Matrix (Fin n) (Fin n) 𝔸[K]))‖
      ≤ C₁ * (max 1 (centralScale (K := K) n t)⁻¹) ^ M * twistedWeight I M a⁻¹ b ξ := hpt
    _ ≤ C₁ * m * ((R' * R') ^ M * latticeWeight J M ξ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmt hC₁)
          (htw.trans (mul_le_mul_of_nonneg_right hcomb hlw))
          (twistedWeight_nonneg I M a⁻¹ b ξ) (mul_nonneg hC₁ hm0)
    _ = C₁ * m * (R' * R') ^ M * latticeWeight J M ξ := by ring

/- English proof (translation)
Establish `h : Continuous fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n => (Reduction.centralSection K n p.1 * p.2.1 : AdelicGLn.AdelicGL K n)` using `(Reduction.continuous_centralSection.comp continuous_fst).mul (continuous_fst.comp continuous_snd)`. Conclude with `Units.continuous_val.comp h`.
-/
theorem continuous_centralSection_mul_coe : Continuous fun p : {r : ℝ // 0 < r} ×
    AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ((Reduction.centralSection K n p.1 * p.2.1 : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) := by
  have h : Continuous fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      (Reduction.centralSection K n p.1 * p.2.1 : AdelicGLn.AdelicGL K n) :=
    (Reduction.continuous_centralSection.comp continuous_fst).mul
      (continuous_fst.comp continuous_snd)
  exact Units.continuous_val.comp h

/- English proof (translation)
The claim follows from `Units.continuous_val.comp (continuous_snd.comp continuous_snd)`.
-/
theorem continuous_snd_snd_coe : Continuous fun p : {r : ℝ // 0 < r} ×
    AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ((p.2.2 : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) :=
  Units.continuous_val.comp (continuous_snd.comp continuous_snd)

/- English proof (translation)
Use `AdelicGLn.locallyCompactSpace K n` as an intermediate fact. Take `⟨A, hA, hAn⟩` from `exists_compact_mem_nhds p₀.2.1`. Take `⟨B, hB, hBn⟩` from `exists_compact_mem_nhds p₀.2.2`. Use `⟨A, B, hA, hB, ?_⟩` and prove the remaining obligations. Establish `h1 : {p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n | (p₀.1 : ℝ) / 2 < p.1} ∈ 𝓝 p₀` using `(isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).mem_nhds (half_lt_self p₀.1.2)`.

Establish `h2 : (Prod.snd ⁻¹' (A ×ˢ B) : Set ({r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n)) ∈ 𝓝 p₀` using `continuous_snd.continuousAt.preimage_mem_nhds (prod_mem_nhds hAn hBn)`. Use `filter_upwards [h1, h2] with p hp1 hp2`. Conclude with `⟨hp1, hp2.1, hp2.2⟩`.
-/
theorem exists_nhds_compact (p₀ : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n ×
    AdelicGLn.AdelicGL K n) :
    ∃ A B : Set (AdelicGLn.AdelicGL K n), IsCompact A ∧ IsCompact B ∧
      {p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n |
        (p₀.1 : ℝ) / 2 < p.1 ∧ p.2.1 ∈ A ∧ p.2.2 ∈ B} ∈ 𝓝 p₀ := by
  have := AdelicGLn.locallyCompactSpace K n
  obtain ⟨A, hA, hAn⟩ := exists_compact_mem_nhds p₀.2.1
  obtain ⟨B, hB, hBn⟩ := exists_compact_mem_nhds p₀.2.2
  refine ⟨A, B, hA, hB, ?_⟩
  have h1 : {p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n |
      (p₀.1 : ℝ) / 2 < p.1} ∈ 𝓝 p₀ :=
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).mem_nhds
      (half_lt_self p₀.1.2)
  have h2 : (Prod.snd ⁻¹' (A ×ˢ B) : Set ({r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n ×
      AdelicGLn.AdelicGL K n)) ∈ 𝓝 p₀ :=
    continuous_snd.continuousAt.preimage_mem_nhds (prod_mem_nhds hAn hBn)
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2.1, hp2.2⟩

/- English proof (translation)
Establish `hΦc` using `continuous_of_mem_matrixSchwartzBruhat hΦ`. Use `continuous_iff_continuousAt.2 fun p₀ => ?_` and prove the remaining obligations. Take `⟨A, B, hA, hB, hU⟩` from `exists_nhds_compact (K := K) (n := n) p₀`. Take `⟨u, hu, hbd⟩` from `exists_summable_bound hΦ ⟨(p₀.1 : ℝ) / 2, half_pos p₀.1.2⟩ hA hB`. Use `(continuousOn_tsum (fun ξ => ?_) hu (fun ξ p hp => hbd p.1 hp.1.le p.2.1 hp.2.1 p.2.2 hp.2.2 ξ)).continuousAt hU` and prove the remaining obligations.

Conclude with `(hΦc.comp ((continuous_centralSection_mul_coe.matrix_mul continuous_const).matrix_mul continuous_snd_snd_coe)).continuousOn`.
-/
theorem continuous_tsum_ratMat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    Continuous (fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ (((Reduction.centralSection K n p.1 * p.2.1 :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (p.2.2 : Matrix (Fin n) (Fin n) 𝔸[K]))) := by
  have hΦc := continuous_of_mem_matrixSchwartzBruhat hΦ
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨A, B, hA, hB, hU⟩ := exists_nhds_compact (K := K) (n := n) p₀
  obtain ⟨u, hu, hbd⟩ := exists_summable_bound hΦ ⟨(p₀.1 : ℝ) / 2, half_pos p₀.1.2⟩ hA hB
  refine (continuousOn_tsum (fun ξ => ?_) hu (fun ξ p hp => hbd p.1 hp.1.le p.2.1 hp.2.1 p.2.2
    hp.2.2 ξ)).continuousAt hU
  exact (hΦc.comp ((continuous_centralSection_mul_coe.matrix_mul continuous_const).matrix_mul
    continuous_snd_snd_coe)).continuousOn

/- English proof (translation)
Establish `hΦc` using `continuous_of_mem_matrixSchwartzBruhat hΦ`. Establish `heq : ∀ (p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n) (γ : GL (Fin n) K), ((Reduction.centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ * p.2.2 : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) = ((Reduction.centralSection K n p.1 * p.2.1 …` using `fun p γ => by`. Simplify using `only [Units.val_mul, coe_diagonal]`. Repeatedly rewrite using `[heq]`. Use `continuous_iff_continuousAt.2 fun p₀ => ?_` and prove the remaining obligations.

Take `⟨A, B, hA, hB, hU⟩` from `exists_nhds_compact (K := K) (n := n) p₀`. Take `⟨u, hu, hbd⟩` from `exists_summable_bound hΦ ⟨(p₀.1 : ℝ) / 2, half_pos p₀.1.2⟩ hA hB`. Use `(continuousOn_tsum (u := fun γ : GL (Fin n) K => u (γ : Matrix (Fin n) (Fin n) K)) (fun γ => ?_) (hu.comp_injective (fun _ _ h => Units.ext h)) (fun γ p hp => hbd p.1 hp.1.le p.2.1 hp.2.1 p.2.2 hp.2.2 _)).continuousAt hU` and prove the remaining obligations. Conclude with `(hΦc.comp ((continuous_centralSection_mul_coe.matrix_mul continuous_const).matrix_mul continuous_snd_snd_coe)).continuousOn`.
-/
theorem continuous_tsum_GL {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    Continuous (fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ∑' γ : GL (Fin n) K, Φ ((Reduction.centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ *
        p.2.2 : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  have hΦc := continuous_of_mem_matrixSchwartzBruhat hΦ
  have heq : ∀ (p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n)
      (γ : GL (Fin n) K), ((Reduction.centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ *
        p.2.2 : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((Reduction.centralSection K n p.1 * p.2.1 : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
          (p.2.2 : Matrix (Fin n) (Fin n) 𝔸[K]) := fun p γ => by
    simp only [Units.val_mul, coe_diagonal]
  simp_rw [heq]
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨A, B, hA, hB, hU⟩ := exists_nhds_compact (K := K) (n := n) p₀
  obtain ⟨u, hu, hbd⟩ := exists_summable_bound hΦ ⟨(p₀.1 : ℝ) / 2, half_pos p₀.1.2⟩ hA hB
  refine (continuousOn_tsum (u := fun γ : GL (Fin n) K => u (γ : Matrix (Fin n) (Fin n) K))
    (fun γ => ?_) (hu.comp_injective (fun _ _ h => Units.ext h))
    (fun γ p hp => hbd p.1 hp.1.le p.2.1 hp.2.1 p.2.2 hp.2.2 _)).continuousAt hU
  exact (hΦc.comp ((continuous_centralSection_mul_coe.matrix_mul continuous_const).matrix_mul
    continuous_snd_snd_coe)).continuousOn

end GJGlobal

end

end GroundTheory.Automorphic
