import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleForms
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionFormsTools
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagBundleSectionForms

noncomputable section

/- English proof (translation)
Introduce `F _ Ω _ _ K _ _ ι _ y e hP _ N E _ _ B w b hfl M a φ hφ Φ _ _ t ht i`. Establish `hc0 : ∀ k, ∃ j : ι k, y ⟨k, j⟩ ≠ 0`. Introduce `k`. Take `⟨j, hj⟩` from `hP.relevant k`. Use `⟨j, fun h0 => hj ?_⟩` and prove the remaining obligations.

Simplify using `[pointIdeal, RingHom.mem_ker, pointConeMap, h0]`. Use `choose c hY using hc0`. Establish `hsc : segreVec y c ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hY k`. Take `⟨ψ, hψint, hψlow, hψi⟩` from `exists_flag_dual y B w b hfl c hsc i`. Take `⟨u, hu, hψ⟩` from `hφ.generate c hsc ψ hψint`.

Establish `hstar : t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ = ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) * projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩`. Establish `h1 : ∑ j, truncCoord t ((i : ℕ) + 1) j * algebraMap Ω Φ (ψ (w j)) = t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[truncCoord, hψi]`. Introduce `j _ hji`.

Break down `lt_or_gt_of_ne hji with h | h` into its components or cases. Simplify using `[hψlow j h]`. Establish `: ¬ (j : ℕ) < (i : ℕ) + 1`. Establish `: (i : ℕ) < j` using `h`. Use linear arithmetic over natural numbers and integers.

Simplify using `[truncCoord, this]`. Simplify using the standard rewrite rules. Rewrite using `[← h1, hψ]`. Simplify using `only [projCoord, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [chartPow, Pi.neg_apply]`. Expand and normalize the polynomial expressions, which then agree. Choose the witnesses or unpack the hypotheses as in `⟨n, U, hUh, hUe⟩ : ∃ (n : ℕ) (U : Fin M → MRing (bundleIdx ι M) F), (∀ l, IsMultiHomog (U l) (liftNat fun _ => n)) ∧ ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (U l) = algebraMap Ω Φ (u l * segreVec y c ^ n) := by`. Establish `h` using `fun l => chartRing_forms y w φ (truncCoord t ((i : ℕ) + 1)) c hsc (hu l)`.

Use `choose n U hU hUe using h`. Use `⟨∑ l, n l, fun l => U l * chartMono M c (fun _ => ∑ l, n l - n l), fun l => ?_, fun l => ?_⟩` and prove the remaining obligations. Establish `hle : n l ≤ ∑ l, n l` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)`. Establish `hd : liftNat (K` using `K) (fun _ => ∑ l, n l) = liftNat (fun _ => n l) + liftNat (fun _ => ∑ l, n l - n l) := by`. Apply the tactic sequence `funext o; cases o <;> simp [liftNat]; omega`.

Rewrite using `[hd]`. Conclude with `(hU l).mul (chartMono_homog M c _)`. Establish `hle : n l ≤ ∑ l, n l` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)`. Rewrite using `[eval₂_mul, hUe, eval_chartMono, ← map_mul]`. Use `congr 1`.

Rewrite using `[Finset.prod_pow, mul_assoc, ← segreVec, ← pow_add, Nat.add_sub_cancel' hle]`. Set `α : K → ℕ` to `fun k => (|a k| + |b i k| - a k).toNat`. Set `β : K → ℕ` to `fun k => (|a k| + |b i k| + n - b i k).toNat`. Establish `hid : segreVec y c ^ n * ∏ k, y ⟨k, c k⟩ ^ α k = (∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i) * chartPow y c (-a)`. Rewrite using `[segreVec_pow, ← chartPow_natCast, ← chartPow_natCast, ← chartPow_add hY, ← chartPow_add hY, ← chartPow_add hY]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Establish `h1` using `le_abs_self (a k)`. Establish `h2` using `neg_abs_le (a k)`. Establish `h3` using `le_abs_self (b i k)`.

Establish `h4` using `neg_abs_le (b i k)`. Simplify using `only [Pi.add_apply, Pi.neg_apply, α, β]`. Use linear arithmetic over natural numbers and integers. Set `f : MRing (bundleIdx ι M) F` to `∑ l, U l * chartMono M c α * X ⟨none, l⟩`. Set `g : MRing (bundleIdx ι M) F` to `chartMono M c β`.

Establish `hg : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g = algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k)` using `eval_chartMono y w φ _ c β`. Establish `hp : algebraMap Ω Φ (chartPow y c (b i)) ≠ 0` using `(map_ne_zero _).2 (chartPow_ne_zero hY _)`. Establish `hf : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f = t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g`. Rewrite using `[hg]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [f, eval₂_sum, eval₂_mul, eval₂_X, hUe, eval_chartMono]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hl : algebraMap Ω Φ (u l * segreVec y c ^ n) * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) = algebraMap Ω Φ (u l * chartPow y c (-a)) * algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i))`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`.

Rewrite using `[mul_assoc, hid]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_comm _ (projCoord _ _ _ _ _), mul_assoc, hl]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ * algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by`.

Rewrite using `[hstar, Finset.sum_mul]`. Use `_ = t i * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := by`. Rewrite using `[map_inv₀, map_mul]`. Clear the denominators using the available nonvanishing facts. Establish `hg0 : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g ≠ 0`.

Rewrite using `[hg]`. Conclude with `(map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hY k))`. Use `⟨fun o => Option.elim o 1 (fun k => n + α k), liftNat β, f, g, ?_, chartMono_homog M c β, ?_, fun hmem => ?_, fun hmem => ?_, hf⟩` and prove the remaining obligations. Use `IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_` and prove the remaining obligations. Establish `h` using `((hUh l).mul (chartMono_homog (F := F) M c α)).mul (isWeightedHomogeneous_X F (blockWeight (bundleIdx ι M)) ⟨none, l⟩)`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `o`. Apply the tactic sequence `cases o <;> simp [liftNat, blockWeight, Pi.single_apply]`. Use function extensionality and compare the values at `o`. Consider the cases of `o with`.

Consider the case `none => simp [liftNat, zetaDeg, liftDeg]`. Consider the case `some k`. Establish `h1` using `le_abs_self (a k)`. Establish `h2` using `neg_abs_le (a k)`. Establish `h3` using `le_abs_self (b i k)`.

Establish `h4` using `neg_abs_le (b i k)`. Simplify using `only [liftNat, zetaDeg, liftDeg, Option.elim, Pi.add_apply, Pi.sub_apply, α, β]`. Use linear arithmetic over natural numbers and integers. Conclude with `(mul_ne_zero (ht.ne_zero i) hg0) (hf ▸ eval_eq_zero_of_mem_projIdeal y w φ _ hmem)`. Conclude with `hg0 (eval_eq_zero_of_mem_projIdeal y w φ _ hmem)`.
-/
theorem FlagBundleSectionForms.proof : FlagBundleSectionForms.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hP _ N E _ _ B w b hfl M a φ hφ Φ _ _ t ht i
  have hc0 : ∀ k, ∃ j : ι k, y ⟨k, j⟩ ≠ 0 := by
    intro k
    obtain ⟨j, hj⟩ := hP.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    simp [pointIdeal, RingHom.mem_ker, pointConeMap, h0]
  choose c hY using hc0
  have hsc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hY k
  obtain ⟨ψ, hψint, hψlow, hψi⟩ := exists_flag_dual y B w b hfl c hsc i
  obtain ⟨u, hu, hψ⟩ := hφ.generate c hsc ψ hψint
  have hstar : t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ =
      ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
        projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ := by
    have h1 : ∑ j, truncCoord t ((i : ℕ) + 1) j * algebraMap Ω Φ (ψ (w j)) =
        t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ := by
      rw [Finset.sum_eq_single i]
      · simp [truncCoord, hψi]
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with h | h
        · simp [hψlow j h]
        · have : ¬ (j : ℕ) < (i : ℕ) + 1 := by
            have : (i : ℕ) < j := h
            omega
          simp [truncCoord, this]
      · simp
    rw [← h1, hψ]
    simp only [projCoord, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [chartPow, Pi.neg_apply]
    ring
  obtain ⟨n, U, hUh, hUe⟩ : ∃ (n : ℕ) (U : Fin M → MRing (bundleIdx ι M) F),
      (∀ l, IsMultiHomog (U l) (liftNat fun _ => n)) ∧
      ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1)))
        (U l) = algebraMap Ω Φ (u l * segreVec y c ^ n) := by
    have h := fun l => chartRing_forms y w φ (truncCoord t ((i : ℕ) + 1)) c hsc (hu l)
    choose n U hU hUe using h
    refine ⟨∑ l, n l, fun l => U l * chartMono M c (fun _ => ∑ l, n l - n l), fun l => ?_, fun l => ?_⟩
    · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      have hd : liftNat (K := K) (fun _ => ∑ l, n l) =
          liftNat (fun _ => n l) + liftNat (fun _ => ∑ l, n l - n l) := by
        funext o; cases o <;> simp [liftNat]; omega
      rw [hd]
      exact (hU l).mul (chartMono_homog M c _)
    · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      rw [eval₂_mul, hUe, eval_chartMono, ← map_mul]
      congr 1
      rw [Finset.prod_pow, mul_assoc, ← segreVec, ← pow_add, Nat.add_sub_cancel' hle]
  let α : K → ℕ := fun k => (|a k| + |b i k| - a k).toNat
  let β : K → ℕ := fun k => (|a k| + |b i k| + n - b i k).toNat
  have hid : segreVec y c ^ n * ∏ k, y ⟨k, c k⟩ ^ α k =
      (∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i) * chartPow y c (-a) := by
    rw [segreVec_pow, ← chartPow_natCast, ← chartPow_natCast, ← chartPow_add hY, ← chartPow_add hY,
      ← chartPow_add hY]
    congr 1
    funext k
    have h1 := le_abs_self (a k)
    have h2 := neg_abs_le (a k)
    have h3 := le_abs_self (b i k)
    have h4 := neg_abs_le (b i k)
    simp only [Pi.add_apply, Pi.neg_apply, α, β]
    omega
  let f : MRing (bundleIdx ι M) F := ∑ l, U l * chartMono M c α * X ⟨none, l⟩
  let g : MRing (bundleIdx ι M) F := chartMono M c β
  have hg : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g
      = algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := eval_chartMono y w φ _ c β
  have hp : algebraMap Ω Φ (chartPow y c (b i)) ≠ 0 :=
    (map_ne_zero _).2 (chartPow_ne_zero hY _)
  have hf : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f
      = t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
        (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g := by
    rw [hg]
    calc _ = ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
            projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          simp only [f, eval₂_sum, eval₂_mul, eval₂_X, hUe, eval_chartMono]
          refine Finset.sum_congr rfl fun l _ => ?_
          have hl : algebraMap Ω Φ (u l * segreVec y c ^ n) * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) =
              algebraMap Ω Φ (u l * chartPow y c (-a)) *
                algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
            rw [← map_mul, ← map_mul]
            congr 1
            rw [mul_assoc, hid]
            ring
          rw [mul_comm _ (projCoord _ _ _ _ _), mul_assoc, hl]
          ring
      _ = t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          rw [hstar, Finset.sum_mul]
      _ = t i * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := by
          rw [map_inv₀, map_mul]
          field_simp
  have hg0 : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hY k))
  refine ⟨fun o => Option.elim o 1 (fun k => n + α k), liftNat β, f, g, ?_, chartMono_homog M c β, ?_,
    fun hmem => ?_, fun hmem => ?_, hf⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
    have h := ((hUh l).mul (chartMono_homog (F := F) M c α)).mul
      (isWeightedHomogeneous_X F (blockWeight (bundleIdx ι M)) ⟨none, l⟩)
    convert h using 1
    funext o
    cases o <;> simp [liftNat, blockWeight, Pi.single_apply]
  · funext o
    cases o with
    | none => simp [liftNat, zetaDeg, liftDeg]
    | some k =>
      have h1 := le_abs_self (a k)
      have h2 := neg_abs_le (a k)
      have h3 := le_abs_self (b i k)
      have h4 := neg_abs_le (b i k)
      simp only [liftNat, zetaDeg, liftDeg, Option.elim, Pi.add_apply, Pi.sub_apply, α, β]
      omega
  · exact (mul_ne_zero (ht.ne_zero i) hg0) (hf ▸ eval_eq_zero_of_mem_projIdeal y w φ _ hmem)
  · exact hg0 (eval_eq_zero_of_mem_projIdeal y w φ _ hmem)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
