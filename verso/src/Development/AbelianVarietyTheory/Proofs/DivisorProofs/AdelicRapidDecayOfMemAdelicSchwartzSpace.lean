import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.SchwartzDecay

open NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

/- English proof (translation)
Use `Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)` and prove the remaining obligations. Conclude with `(isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)`. Conclude with `(isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)`.
-/
theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

/- English proof (translation)
Use `set e := InfiniteAdeleRing.ringEquiv_mixedSpace F`. Break down `v.isReal_or_isComplex with hv | hv` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_le_mixed (x : InfiniteAdeleRing F) (v : InfinitePlace F) :
    ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  rcases v.isReal_or_isComplex with hv | hv
  · calc ‖x v‖ = ‖(e x).1 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).1 ⟨v, hv⟩).trans (norm_fst_le (e x))
  · calc ‖x v‖ = ‖(e x).2 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).2 ⟨v, hv⟩).trans (norm_snd_le (e x))

/- English proof (translation)
The claim follows from `|re x v| ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by refine (Complex.abs_re_le_norm _).trans ?_ rw [(isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)] exact norm_le_mixed x v`.
-/
theorem abs_re_le (x : Ainf F) (v : InfinitePlace F) :
    |re x v| ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [(isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)]
  exact norm_le_mixed x v

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _`.
-/
theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/- English proof (translation)
Use `set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sz_le (u : Fin N → AF F) :
    sz u ≤ (N * Fintype.card (InfinitePlace F) : ℝ) *
      ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1‖ := by
  set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
  calc sz u ≤ ∑ _l : Fin N, ∑ _w : InfinitePlace F, ‖t‖ :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun w _ =>
          (abs_re_le (inf u l) w).trans (norm_le_pi_norm t l)
    _ = _ := by simp [mul_assoc]

/- English proof (translation)
Take `⟨hc, ⟨K, hK, hK0⟩, hd⟩` from `h`. Take `⟨hc', ⟨K', hK', hK0'⟩, hd'⟩` from `h'`. Use `⟨hc.add hc', ⟨K ∪ K', hK.union hK', fun u hu => ?_⟩, fun k => ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[Set.mem_union, not_or]`. Simplify using `[hK0 u hu.1, hK0' u hu.2]`.

Take `⟨C, hC⟩` from `hd k`. Take `⟨C', hC'⟩` from `hd' k`. Use `⟨C + C', fun u => ?_⟩` and prove the remaining obligations. Establish `h0 : 0 ≤ (1 + sz u) ^ k` using `pow_nonneg (by linarith [sz_nonneg u]) k`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decay_add {Φ Ψ : (Fin N → AF F) → ℂ} (h : Decay Φ) (h' : Decay Ψ) : Decay (Φ + Ψ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  obtain ⟨hc', ⟨K', hK', hK0'⟩, hd'⟩ := h'
  refine ⟨hc.add hc', ⟨K ∪ K', hK.union hK', fun u hu => ?_⟩, fun k => ?_⟩
  · rw [Set.mem_union, not_or] at hu
    simp [hK0 u hu.1, hK0' u hu.2]
  · obtain ⟨C, hC⟩ := hd k
    obtain ⟨C', hC'⟩ := hd' k
    refine ⟨C + C', fun u => ?_⟩
    have h0 : 0 ≤ (1 + sz u) ^ k := pow_nonneg (by linarith [sz_nonneg u]) k
    calc ‖(Φ + Ψ) u‖ * (1 + sz u) ^ k ≤ (‖Φ u‖ + ‖Ψ u‖) * (1 + sz u) ^ k :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) h0
      _ ≤ C + C' := by rw [add_mul]; exact add_le_add (hC u) (hC' u)

/- English proof (translation)
Take `⟨hc, ⟨K, hK, hK0⟩, hd⟩` from `h`. Use `⟨hc.const_smul a, ⟨K, hK, fun u hu => by simp [hK0 u hu]⟩, fun k => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `hd k`. Use `⟨‖a‖ * C, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, norm_smul, mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left (hC u) (norm_nonneg a)`.
-/
theorem decay_smul (a : ℂ) {Φ : (Fin N → AF F) → ℂ} (h : Decay Φ) : Decay (a • Φ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  refine ⟨hc.const_smul a, ⟨K, hK, fun u hu => by simp [hK0 u hu]⟩, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hd k
  refine ⟨‖a‖ * C, fun u => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg a)

/- English proof (translation)
Use `fun t => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f t` as an intermediate fact. Simplify using `only [norm_iteratedFDeriv_zero] at this`. Conclude with `⟨_, this⟩`.
-/
theorem schwartz_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ t, (1 + ‖t‖) ^ k * ‖f t‖ ≤ C := by
  have := fun t => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f t
  simp only [norm_iteratedFDeriv_zero] at this
  exact ⟨_, this⟩

/- English proof (translation)
Take `⟨hg1, hg2⟩` from `hg`. Use `⟨?_, ⟨tsupport g, hg2, fun u hu => ?_⟩, fun k => ?_⟩` and prove the remaining obligations. Use `Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_)) (hg1.continuous.comp (continuous_pi fun i => ?_))` and prove the remaining obligations. Conclude with `continuous_mixed.comp (continuous_fst.comp (continuous_apply i))`. Conclude with `continuous_snd.comp (continuous_apply i)`.

Conclude with `mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hu)`. Take `⟨B, hB⟩` from `hg1.continuous.bounded_above_of_compact_support hg2`. Take `⟨C, hC⟩` from `schwartz_bound f k`. Use `set c : ℝ := N * Fintype.card (InfinitePlace F)`. Establish `hc : 0 ≤ c` using `by positivity`.

Use `⟨(1 + c) ^ k * C * B, fun u => ?_⟩` and prove the remaining obligations. Use `set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1`. Establish `h1 : 1 + sz u ≤ (1 + c) * (1 + ‖t‖)`. Establish `: sz u ≤ c * ‖t‖` using `sz_le u`. Use polynomial arithmetic with `[norm_nonneg t]`.

Establish `h2 : (1 + sz u) ^ k ≤ (1 + c) ^ k * (1 + ‖t‖) ^ k`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by linarith [sz_nonneg u]) h1 k`. Establish `hC0 : 0 ≤ C` using `le_trans (by positivity) (hC 0)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decay_pure (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) : Decay (GlobalTheory.WeilM.pureA F f g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ⟨tsupport g, hg2, fun u hu => ?_⟩, fun k => ?_⟩
  · refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_))
      (hg1.continuous.comp (continuous_pi fun i => ?_))
    · exact continuous_mixed.comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_snd.comp (continuous_apply i)
  · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hu)
  · obtain ⟨B, hB⟩ := hg1.continuous.bounded_above_of_compact_support hg2
    obtain ⟨C, hC⟩ := schwartz_bound f k
    set c : ℝ := N * Fintype.card (InfinitePlace F)
    have hc : 0 ≤ c := by positivity
    refine ⟨(1 + c) ^ k * C * B, fun u => ?_⟩
    set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
    have h1 : 1 + sz u ≤ (1 + c) * (1 + ‖t‖) := by
      have : sz u ≤ c * ‖t‖ := sz_le u
      nlinarith [norm_nonneg t]
    have h2 : (1 + sz u) ^ k ≤ (1 + c) ^ k * (1 + ‖t‖) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [sz_nonneg u]) h1 k
    have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
    calc ‖GlobalTheory.WeilM.pureA F f g u‖ * (1 + sz u) ^ k
        = ‖f t‖ * ‖g fun i => (u i).2‖ * (1 + sz u) ^ k := by rw [← norm_mul]; rfl
      _ ≤ ‖f t‖ * ‖g fun i => (u i).2‖ * ((1 + c) ^ k * (1 + ‖t‖) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 + c) ^ k * ((1 + ‖t‖) ^ k * ‖f t‖) * ‖g fun i => (u i).2‖ := by ring
      _ ≤ (1 + c) ^ k * C * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hC t) (by positivity)) (hB _) (norm_nonneg _) (by positivity)

/- English proof (translation)
Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Conclude with `decay_pure f g hg`.

Consider the case `zero => exact decay_zero`. Consider the case `add x y _ _ hx hy => exact decay_add hx hy`. Consider the case `smul a x _ hx => exact decay_smul a hx`.
-/
theorem decay_of_mem_schA (F : Type) [Field F] [NumberField F] (N : ℕ) :
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact decay_pure f g hg
  | zero => exact decay_zero
  | add x y _ _ hx hy => exact decay_add hx hy
  | smul a x _ hx => exact decay_smul a hx

end GlobalTheory.SchwartzDecay
