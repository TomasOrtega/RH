import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

open scoped ContDiff

namespace GlobalTheory.FourierSndDecay

/- English proof (translation)
Establish `c0 : ContDiff ℝ ∞ h` using `h.smooth'`. Establish `e : (fun s : V => h (u, s)) = (fun x : U × V => h (x + (u, 0))) ∘ (ContinuousLinearMap.inr ℝ U V)`. Use function extensionality and compare the values at `s`. Simplify using the standard rewrite rules. Establish `ct : ContDiff ℝ ∞ (fun x : U × V => h (x + (u, 0)))` using `c0.comp (contDiff_id.add contDiff_const)`.

Rewrite using `[e, ContinuousLinearMap.iteratedFDeriv_comp_right _ ct t (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Establish `h1 : ∏ _i : Fin q, ‖(ContinuousLinearMap.inr ℝ U V)‖ ≤ 1` using `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ U V)`. Establish `: ContinuousLinearMap.inr ℝ U V t + (u, 0) = (u, t)` using `by simp`. Rewrite using `[this]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) h1`.
-/
lemma norm_iteratedFDeriv_slice_le {U V : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : SchwartzMap (U × V) ℂ) (u : U) (q : ℕ) (t : V) :
    ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ ≤ ‖iteratedFDeriv ℝ q h (u, t)‖ := by
  have c0 : ContDiff ℝ ∞ h := h.smooth'
  have e : (fun s : V => h (u, s)) =
      (fun x : U × V => h (x + (u, 0))) ∘ (ContinuousLinearMap.inr ℝ U V) := by
    funext s; simp
  have ct : ContDiff ℝ ∞ (fun x : U × V => h (x + (u, 0))) :=
    c0.comp (contDiff_id.add contDiff_const)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ ct t (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin q, ‖(ContinuousLinearMap.inr ℝ U V)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ U V)
  have : ContinuousLinearMap.inr ℝ U V t + (u, 0) = (u, t) := by simp
  rw [this]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

/- English proof (translation)
Establish `h1 : 1 + t ≤ 2 * max 1 t`. Break down `le_total 1 t with h | h` into its components or cases. Rewrite using `[max_eq_right h]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[max_eq_left h]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (max 1 t) ^ n ≤ 1 + t ^ n`. Break down `le_total 1 t with h | h` into its components or cases. Rewrite using `[max_eq_right h]`. Combine the linear relations using `[pow_nonneg ht n]`.

Rewrite using `[max_eq_left h, one_pow]`. Combine the linear relations using `[pow_nonneg ht n]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma one_add_pow_le_two_pow_mul (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 t) ^ n ≤ 1 + t ^ n := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ht n]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg ht n]
  calc (1 + t) ^ n ≤ (2 * max 1 t) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = 2 ^ n * (max 1 t) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (1 + t ^ n) := by gcongr

/- English proof (translation)
Introduce `U V _ _ _ _ _ _ _ _ h k`. Use `set d := Module.finrank ℝ V with hd`. Use `set N := k + (d + 1) with hN`. Use `set S := 2 ^ N * ((Finset.Iic (N, k)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hSdef`. Use `set I := ∫ t : V, (1 + ‖t‖) ^ (-((d : ℝ) + 1)) with hIdef`.

Establish `hint : Integrable (fun t : V => (1 + ‖t‖) ^ (-((d : ℝ) + 1)))` using `integrable_one_add_norm (by linarith)`. Establish `hpt : ∀ (u : U) (t : V) (q : ℕ), q ≤ k → (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ ≤ S * (1 + ‖t‖) ^ (-((d : ℝ) + 1))`. Introduce `u t q hq`. Establish `hS` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, k)) (k := N) (n := q) le_rfl hq h (u, t)`. Establish `hu : ‖u‖ ≤ ‖(u, t)‖` using `norm_fst_le (u, t)`.

Establish `ht : ‖t‖ ≤ ‖(u, t)‖` using `norm_snd_le (u, t)`. Establish `hpos : 0 < (1 + ‖t‖) ^ ((d : ℝ) + 1)` using `by positivity`. Rewrite using `[Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]`. Establish `e : (1 + ‖t‖) ^ ((d : ℝ) + 1) = (1 + ‖t‖) ^ (d + 1)`. Rewrite using `[show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]`.

Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcd : ∀ u : U, ContDiff ℝ ∞ (fun s : V => h (u, s))` using `fun u => h.smooth'.comp (contDiff_const.prodMk contDiff_id)`. Establish `hintq : ∀ (u : U) (q : ℕ), q ≤ k → Integrable (fun t => ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖)`. Introduce `u q hq`.

Use `(hint.const_mul S).mono' ((hcd u).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.aestronglyMeasurable ?_` and prove the remaining obligations. Use `filter_upwards with t`. Rewrite using `[Real.norm_of_nonneg (norm_nonneg _)]`. Use `hpt u t q hq` as an intermediate fact. Establish `h1 : 1 ≤ (1 + ‖u‖) ^ k` using `one_le_pow₀ (by linarith [norm_nonneg u])`.

Use polynomial arithmetic with `[norm_nonneg (iteratedFDeriv ℝ q (fun s : V => h (u, s)) t)]`. Establish `hintb : ∀ (u : U) (q : ℕ), q ≤ k → (1 + ‖u‖) ^ k * ∫ t, ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ ≤ S * I`. Introduce `u q hq`. Combine the equalities or inequalities in the displayed calculation. Establish `hF : ∀ (u : U) (w : V) (n : ℕ), n ≤ k → (1 + ‖u‖) ^ k * (‖w‖ ^ n * ‖𝓕 (fun t : V => h (u, t)) w‖) ≤ 2 ^ n * ((n + 1) * (S * I))`.

Introduce `u w n hn`. Establish `h'f : ∀ (k' m : ℕ), (k' : ℕ∞) ≤ 0 → (m : ℕ∞) ≤ (n : ℕ∞) → Integrable (fun v : V => ‖v‖ ^ k' * ‖iteratedFDeriv ℝ m (fun s : V => h (u, s)) v‖)`. Introduce `k' m hk' hm`. Establish `hk0 : k' = 0` using `by exact_mod_cast nonpos_iff_eq_zero.mp hk'`. Establish `hmn : m ≤ n` using `by exact_mod_cast hm`.

Substitute `hk0` using the available equality. Simplify using `using hintq u m (hmn.trans hn)`. Establish `key` using `Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := fun t : V => h (u, t)) (K := 0) (N := n) ((hcd u).of_le (by exact_mod_cast le_top)) h'f (k := 0) (n := n) le_rfl le_rfl w`. Establish `hsum : (∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1), ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun s : V => h (u, s)) v‖) = ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖`. Rewrite using `[Finset.sum_product]`.

Simplify using the standard rewrite rules. Rewrite `key` using `[hsum, norm_iteratedFDeriv_zero]`. Simplify using `only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add] at key`. Establish `hsb : (1 + ‖u‖) ^ k * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖ ≤ (n + 1) * (S * I)`. Rewrite using `[Finset.mul_sum]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hu0 : 0 ≤ (1 + ‖u‖) ^ k` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `⟨2 ^ k * (S * I + 2 ^ k * ((k + 1) * (S * I))), fun u w => ?_⟩` and prove the remaining obligations. Establish `h0` using `hF u w 0 (Nat.zero_le _)`.

Establish `hk` using `hF u w k le_rfl`. Simplify using `only [pow_zero, one_mul, Nat.cast_zero, zero_add] at h0`. Establish `hw` using `one_add_pow_le_two_pow_mul ‖w‖ (norm_nonneg _) k`. Establish `hu0 : 0 ≤ (1 + ‖u‖) ^ k` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fourier_snd_rapid_decay : ∀ (U V : Type) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (h : SchwartzMap (U × V) ℂ) (k : ℕ), ∃ C : ℝ,
    ∀ (u : U) (w : V), (1 + ‖u‖) ^ k * (1 + ‖w‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖ ≤ C := by
  intro U V _ _ _ _ _ _ _ _ h k
  set d := Module.finrank ℝ V with hd
  set N := k + (d + 1) with hN
  set S := 2 ^ N * ((Finset.Iic (N, k)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hSdef
  set I := ∫ t : V, (1 + ‖t‖) ^ (-((d : ℝ) + 1)) with hIdef
  have hint : Integrable (fun t : V => (1 + ‖t‖) ^ (-((d : ℝ) + 1))) :=
    integrable_one_add_norm (by linarith)
  have hpt : ∀ (u : U) (t : V) (q : ℕ), q ≤ k →
      (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖
        ≤ S * (1 + ‖t‖) ^ (-((d : ℝ) + 1)) := by
    intro u t q hq
    have hS := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, k)) (k := N) (n := q)
      le_rfl hq h (u, t)
    have hu : ‖u‖ ≤ ‖(u, t)‖ := norm_fst_le (u, t)
    have ht : ‖t‖ ≤ ‖(u, t)‖ := norm_snd_le (u, t)
    have hpos : 0 < (1 + ‖t‖) ^ ((d : ℝ) + 1) := by positivity
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
    have e : (1 + ‖t‖) ^ ((d : ℝ) + 1) = (1 + ‖t‖) ^ (d + 1) := by
      rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [e]
    calc (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ * (1 + ‖t‖) ^ (d + 1)
        ≤ (1 + ‖(u, t)‖) ^ k * ‖iteratedFDeriv ℝ q h (u, t)‖ * (1 + ‖(u, t)‖) ^ (d + 1) := by
          gcongr; exact norm_iteratedFDeriv_slice_le h u q t
      _ = (1 + ‖(u, t)‖) ^ N * ‖iteratedFDeriv ℝ q h (u, t)‖ := by rw [hN, pow_add]; ring
      _ ≤ S := hS
  have hcd : ∀ u : U, ContDiff ℝ ∞ (fun s : V => h (u, s)) := fun u =>
    h.smooth'.comp (contDiff_const.prodMk contDiff_id)
  have hintq : ∀ (u : U) (q : ℕ), q ≤ k →
      Integrable (fun t => ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖) := by
    intro u q hq
    refine (hint.const_mul S).mono'
      ((hcd u).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have := hpt u t q hq
    have h1 : 1 ≤ (1 + ‖u‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg u])
    nlinarith [norm_nonneg (iteratedFDeriv ℝ q (fun s : V => h (u, s)) t)]
  have hintb : ∀ (u : U) (q : ℕ), q ≤ k →
      (1 + ‖u‖) ^ k * ∫ t, ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ ≤ S * I := by
    intro u q hq
    calc (1 + ‖u‖) ^ k * ∫ t, ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖
        = ∫ t, (1 + ‖u‖) ^ k * ‖iteratedFDeriv ℝ q (fun s : V => h (u, s)) t‖ :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ t : V, S * (1 + ‖t‖) ^ (-((d : ℝ) + 1)) :=
          integral_mono ((hintq u q hq).const_mul _) (hint.const_mul S) (fun t => hpt u t q hq)
      _ = S * I := integral_const_mul _ _
  have hF : ∀ (u : U) (w : V) (n : ℕ), n ≤ k →
      (1 + ‖u‖) ^ k * (‖w‖ ^ n * ‖𝓕 (fun t : V => h (u, t)) w‖) ≤ 2 ^ n * ((n + 1) * (S * I)) := by
    intro u w n hn
    have h'f : ∀ (k' m : ℕ), (k' : ℕ∞) ≤ 0 → (m : ℕ∞) ≤ (n : ℕ∞) →
        Integrable (fun v : V => ‖v‖ ^ k' * ‖iteratedFDeriv ℝ m (fun s : V => h (u, s)) v‖) := by
      intro k' m hk' hm
      have hk0 : k' = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hk'
      have hmn : m ≤ n := by exact_mod_cast hm
      subst hk0
      simpa using hintq u m (hmn.trans hn)
    have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := fun t : V => h (u, t)) (K := 0)
      (N := n) ((hcd u).of_le (by exact_mod_cast le_top)) h'f (k := 0) (n := n) le_rfl le_rfl w
    have hsum : (∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun s : V => h (u, s)) v‖)
        = ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖ := by
      rw [Finset.sum_product]; simp
    rw [hsum, norm_iteratedFDeriv_zero] at key
    simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add] at key
    have hsb : (1 + ‖u‖) ^ k *
        ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖
        ≤ (n + 1) * (S * I) := by
      rw [Finset.mul_sum]
      calc ∑ j ∈ Finset.range (n + 1),
            (1 + ‖u‖) ^ k * ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖
          ≤ ∑ _j ∈ Finset.range (n + 1), S * I := Finset.sum_le_sum fun j hj =>
            hintb u j ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hn)
        _ = (n + 1) * (S * I) := by simp
    have hu0 : 0 ≤ (1 + ‖u‖) ^ k := by positivity
    calc (1 + ‖u‖) ^ k * (‖w‖ ^ n * ‖𝓕 (fun t : V => h (u, t)) w‖)
        ≤ (1 + ‖u‖) ^ k * (2 ^ n * ∑ j ∈ Finset.range (n + 1),
            ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖) :=
          mul_le_mul_of_nonneg_left key hu0
      _ = 2 ^ n * ((1 + ‖u‖) ^ k * ∑ j ∈ Finset.range (n + 1),
            ∫ v, ‖iteratedFDeriv ℝ j (fun s : V => h (u, s)) v‖) := by ring
      _ ≤ 2 ^ n * ((n + 1) * (S * I)) := by gcongr
  refine ⟨2 ^ k * (S * I + 2 ^ k * ((k + 1) * (S * I))), fun u w => ?_⟩
  have h0 := hF u w 0 (Nat.zero_le _)
  have hk := hF u w k le_rfl
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at h0
  have hw := one_add_pow_le_two_pow_mul ‖w‖ (norm_nonneg _) k
  have hu0 : 0 ≤ (1 + ‖u‖) ^ k := by positivity
  calc (1 + ‖u‖) ^ k * (1 + ‖w‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖
      ≤ (1 + ‖u‖) ^ k * (2 ^ k * (1 + ‖w‖ ^ k)) * ‖𝓕 (fun t : V => h (u, t)) w‖ := by gcongr
    _ = 2 ^ k * ((1 + ‖u‖) ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖
          + (1 + ‖u‖) ^ k * (‖w‖ ^ k * ‖𝓕 (fun t : V => h (u, t)) w‖)) := by ring
    _ ≤ 2 ^ k * (S * I + 2 ^ k * ((k + 1) * (S * I))) := by gcongr

end GlobalTheory.FourierSndDecay
