import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver cellMon)

namespace RowSecGlue

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [Algebra S Ω]

def ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[chartRingOver, Algebra.adjoin_range_eq_range_aeval]`. Conclude with `⟨R, rfl⟩`.
-/
theorem aeval_ratioPt_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (R : MRingOver S ι) :
    aeval (ratioPt y c) R ∈ chartRingOver S y c := by
  rw [chartRingOver, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨R, rfl⟩

/- English proof (translation)
Use `conv_lhs => rw [F.as_sum]`. Use `conv_rhs => rw [F.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Simplify using `only [aeval_monomial]`.

Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]`. Establish `h1 : ∀ p : (Σ k, ι k), y p ^ μ p = ratioPt y c p ^ μ p * y ⟨p.1, c p.1⟩ ^ μ p`. Introduce `p`. Rewrite using `[ratioPt, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hc p.1))]`. Establish `h2 : ∏ p : (Σ k, ι k), y ⟨p.1, c p.1⟩ ^ μ p = ∏ k, y ⟨k, c k⟩ ^ d k`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hF μ hμ k]`. Rewrite using `[Finset.prod_congr rfl fun p _ => h1 p, Finset.prod_mul_distrib, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_eq_ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {F : MRingOver S ι} {d : K → ℕ} (hF : IsMultiHomog F d) :
    aeval y F = aeval (ratioPt y c) F * ∏ k, y ⟨k, c k⟩ ^ d k := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  simp only [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have h1 : ∀ p : (Σ k, ι k), y p ^ μ p = ratioPt y c p ^ μ p * y ⟨p.1, c p.1⟩ ^ μ p := by
    intro p
    rw [ratioPt, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hc p.1))]
  have h2 : ∏ p : (Σ k, ι k), y ⟨p.1, c p.1⟩ ^ μ p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hF μ hμ k]
  rw [Finset.prod_congr rfl fun p _ => h1 p, Finset.prod_mul_distrib, h2]
  ring

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `hone : ∀ k, ratioPt y c ⟨k, c k⟩ = 1` using `fun k => div_self (hc k)`. Proceed by induction on `ht using Submonoid.closure_induction with`. Consider the case `mem f hf`. Take `⟨k, i, hi, rfl⟩` from `hf`. Unfold `baseCell at hi`.

Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite `hi` using `[Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map]`. Break down `hi with rfl | ⟨j, hj, rfl⟩` into its components or cases. Conclude with `⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩`.

Use `⟨1, ∏ j' ∈ J.erase j, ratioPt y c ⟨k, e.symm j'⟩, prod_mem fun j' _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k, e.symm j'⟩), ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_X, pow_one]`. Conclude with `Finset.prod_erase_mul J (fun j' => ratioPt y c ⟨k, e.symm j'⟩) hj`. Rewrite `hi` using `[Function.update_of_ne hk, Finset.mem_singleton]`. Substitute `hi` using the available equality.

Conclude with `⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩`. Consider the case `one => exact ⟨0, 1, one_mem _, by simp⟩`. Consider the case `mul f g _ _ h₁ h₂`. Take `⟨n₁, w₁, hw₁, e₁⟩` from `h₁`. Take `⟨n₂, w₂, hw₂, e₂⟩` from `h₂`.

Conclude with `⟨n₁ + n₂, w₁ * w₂, mul_mem hw₁ hw₂, by rw [map_mul, pow_add, ← e₁, ← e₂]; ring⟩`.
-/
theorem exists_mul_eq_pow (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (J : Finset (Fin (N + 1))) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {t : MRingOver S ι}
    (ht : t ∈ cellMon S (baseCell k₀ e J fun k => {c k})) :
    ∃ (n : ℕ) (w : Ω), w ∈ chartRingOver S y c ∧
      w * aeval (ratioPt y c) t = (∏ j ∈ J, ratioPt y c ⟨k₀, e.symm j⟩) ^ n := by
  have hone : ∀ k, ratioPt y c ⟨k, c k⟩ = 1 := fun k => div_self (hc k)
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map] at hi
      rcases hi with rfl | ⟨j, hj, rfl⟩
      · exact ⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩
      · refine ⟨1, ∏ j' ∈ J.erase j, ratioPt y c ⟨k, e.symm j'⟩,
          prod_mem fun j' _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k, e.symm j'⟩), ?_⟩
        rw [aeval_X, pow_one]
        exact Finset.prod_erase_mul J (fun j' => ratioPt y c ⟨k, e.symm j'⟩) hj
    · rw [Function.update_of_ne hk, Finset.mem_singleton] at hi
      subst hi
      exact ⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul f g _ _ h₁ h₂ =>
    obtain ⟨n₁, w₁, hw₁, e₁⟩ := h₁
    obtain ⟨n₂, w₂, hw₂, e₂⟩ := h₂
    exact ⟨n₁ + n₂, w₁ * w₂, mul_mem hw₁ hw₂, by rw [map_mul, pow_add, ← e₁, ← e₂]; ring⟩

/- English proof (translation)
Establish `h : ∀ k, Y k ^ (-(γ + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) = (Y k ^ γ k)⁻¹ * (Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k))⁻¹`. Introduce `k`. Rewrite using `[Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_add, zpow_add₀ (hY k), zpow_neg, zpow_neg, IndefiniteRowSideFullHecke.Kleiman2.baseDeg]`. Establish `h2 : ∏ k, Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k) = Y k₀ ^ m`. Rewrite using `[Finset.prod_eq_single k₀ (fun k _ hk => by simp [Pi.single_apply, hk]) (fun h => absurd (Finset.mem_univ _) h)]`.

Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_congr rfl fun k _ => h k, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib, h2]`.
-/
theorem prod_zpow_neg (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) (k₀ : K) (γ : K → ℤ) (m : ℕ) :
    ∏ k, Y k ^ (-(γ + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) = (∏ k, Y k ^ γ k)⁻¹ * (Y k₀ ^ m)⁻¹ := by
  have h : ∀ k, Y k ^ (-(γ + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (Y k ^ γ k)⁻¹ * (Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k))⁻¹ := by
    intro k
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_add, zpow_add₀ (hY k), zpow_neg, zpow_neg,
      IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  have h2 : ∏ k, Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k) = Y k₀ ^ m := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [Pi.single_apply, hk])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [Finset.prod_congr rfl fun k _ => h k, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_inv_distrib, h2]

/- English proof (translation)
Establish `hJ : ∀ j ∈ J.1, y ⟨k₀, e.symm j⟩ ≠ 0` using `fun j hj => (Kleiman.mem_support _).mp (J.2.2 hj)`. Establish `hmeet : CellMeets y (baseCell k₀ e J.1 fun k => {c k})`. Introduce `k i hi`. Unfold `baseCell at hi`. Distinguish the cases in `hk : k = k₀`.

Substitute `hk` using the available equality. Rewrite `hi` using `[Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map]`. Break down `hi with rfl | ⟨j, hj, rfl⟩` into its components or cases. Conclude with `hc k`. Conclude with `hJ j hj`.

Rewrite `hi` using `[Function.update_of_ne hk, Finset.mem_singleton]`. Substitute `hi` using the available equality. Conclude with `hc k`. Unfold `cellSec at hz`. Rewrite `hz` using `[if_pos hmeet]`.

Use `set u := ratioPt y c with hu`. Use `set xJ := ∏ j ∈ J.1, u ⟨k₀, e.symm j⟩ with hxJdef`. Establish `hxJ : xJ ∈ chartRingOver S y c` using `prod_mem fun j _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k₀, e.symm j⟩)`. Establish `hxJ0 : xJ ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun j hj => div_ne_zero (hJ j hj) (hc k₀)`. Establish `hX : Kleiman.xProd J = xJ * y ⟨k₀, c k₀⟩ ^ J.1.card`.

Rewrite using `[Kleiman.xProd, hxJdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [hu, ratioPt, Function.comp, IndefiniteRowSideFullHecke.Kleiman2.blockVec]`. Rewrite using `[div_mul_cancel₀ _ (hc k₀)]`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨g, t, a', ht, hta, hγ, hg, rfl⟩` from `hz`. Take `⟨n₀, w, hw, hwt⟩` from `exists_mul_eq_pow y k₀ e J.1 c hc ht`. Use `⟨n₀, fun n hn => ?_⟩` and prove the remaining obligations. Establish `ht0 : aeval u t ≠ 0` using `fun h0 => pow_ne_zero n₀ hxJ0 (by rw [← hwt, h0, mul_zero])`.

Establish `hg'` using `aeval_eq_ratioPt y c hc hg`. Establish `ht'` using `aeval_eq_ratioPt y c hc hta`. Establish `hexp : ∏ k, y ⟨k, c k⟩ ^ (γ k + a' k).toNat = (∏ k, y ⟨k, c k⟩ ^ γ k) * ∏ k, y ⟨k, c k⟩ ^ a' k`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← zpow_natCast, Int.toNat_of_nonneg (hγ k), zpow_add₀ (hc k), zpow_natCast]`. Establish `hW : (∏ k, y ⟨k, c k⟩ ^ γ k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`. Establish `hA : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Rewrite `hg'`, `ht'` using `[← hu]`. Establish `hn' : xJ ^ n = xJ ^ (n - n₀) * (w * aeval u t)`.

Rewrite using `[hwt, ← pow_add, Nat.sub_add_cancel hn]`. Establish `key : Kleiman.xProd J ^ n * (aeval y g / aeval y t) * ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) = xJ ^ (n - n₀) * w * aeval u g`. Rewrite using `[prod_zpow_neg (fun k => y ⟨k, c k⟩) hc k₀ γ, hX, mul_pow, hn', hg', ht', hexp, pow_mul]`. Establish `hp : y ⟨k₀, c k₀⟩ ^ (J.1.card * n) * (y ⟨k₀, c k₀⟩)⁻¹ ^ (J.1.card * n) = 1`. Rewrite using `[← mul_pow, mul_inv_cancel₀ (hc k₀), one_pow]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(w * aeval u g) * hp`. Rewrite using `[key]`. Conclude with `mul_mem (mul_mem (pow_mem hxJ _) hw) (aeval_ratioPt_mem y c g)`. Consider the case `zero => exact ⟨0, fun n _ => by simp⟩`.

Consider the case `add z₁ z₂ _ _ h₁ h₂`. Take `⟨n₁, h₁⟩` from `h₁`. Take `⟨n₂, h₂⟩` from `h₂`. Use `⟨max n₁ n₂, fun n hn => ?_⟩` and prove the remaining obligations. Use `add_mem (h₁ n (le_of_max_le_left hn)) (h₂ n (le_of_max_le_right hn))` as an intermediate fact.

Rewrite `this` using `[← add_mul, ← mul_add]`. Then use the resulting hypothesis. Consider the case `smul r z _ h`. Take `⟨n₀, h⟩` from `h`. Use `⟨n₀, fun n hn => ?_⟩` and prove the remaining obligations. Establish `e1 : Kleiman.xProd J ^ n * (r • z) * ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) = algebraMap S Ω r * (Kleiman.xProd J ^ n * z * ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.base …`.

Rewrite using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `mul_mem (Subalgebra.algebraMap_mem _ r) (h n hn)`.
-/
theorem exists_pow_of_mem_cellSec (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ)
    (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {z : Ω}
    (hz : z ∈ cellSec S y γ (baseCell k₀ e J.1 fun k => {c k})) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Kleiman.xProd J ^ n * z *
      ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) ∈ chartRingOver S y c := by
  have hJ : ∀ j ∈ J.1, y ⟨k₀, e.symm j⟩ ≠ 0 := fun j hj => (Kleiman.mem_support _).mp (J.2.2 hj)
  have hmeet : CellMeets y (baseCell k₀ e J.1 fun k => {c k}) := by
    intro k i hi
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map] at hi
      rcases hi with rfl | ⟨j, hj, rfl⟩
      · exact hc k
      · exact hJ j hj
    · rw [Function.update_of_ne hk, Finset.mem_singleton] at hi
      subst hi; exact hc k
  unfold cellSec at hz
  rw [if_pos hmeet] at hz
  set u := ratioPt y c with hu
  set xJ := ∏ j ∈ J.1, u ⟨k₀, e.symm j⟩ with hxJdef
  have hxJ : xJ ∈ chartRingOver S y c :=
    prod_mem fun j _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k₀, e.symm j⟩)
  have hxJ0 : xJ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj => div_ne_zero (hJ j hj) (hc k₀)
  have hX : Kleiman.xProd J = xJ * y ⟨k₀, c k₀⟩ ^ J.1.card := by
    rw [Kleiman.xProd, hxJdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hu, ratioPt, Function.comp, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    rw [div_mul_cancel₀ _ (hc k₀)]
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, t, a', ht, hta, hγ, hg, rfl⟩ := hz
    obtain ⟨n₀, w, hw, hwt⟩ := exists_mul_eq_pow y k₀ e J.1 c hc ht
    refine ⟨n₀, fun n hn => ?_⟩
    have ht0 : aeval u t ≠ 0 := fun h0 => pow_ne_zero n₀ hxJ0 (by rw [← hwt, h0, mul_zero])
    have hg' := aeval_eq_ratioPt y c hc hg
    have ht' := aeval_eq_ratioPt y c hc hta
    have hexp : ∏ k, y ⟨k, c k⟩ ^ (γ k + a' k).toNat = (∏ k, y ⟨k, c k⟩ ^ γ k) * ∏ k, y ⟨k, c k⟩ ^ a' k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, Int.toNat_of_nonneg (hγ k), zpow_add₀ (hc k), zpow_natCast]
    have hW : (∏ k, y ⟨k, c k⟩ ^ γ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hA : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    rw [← hu] at hg' ht'
    have hn' : xJ ^ n = xJ ^ (n - n₀) * (w * aeval u t) := by
      rw [hwt, ← pow_add, Nat.sub_add_cancel hn]
    have key : Kleiman.xProd J ^ n * (aeval y g / aeval y t) *
        ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
        xJ ^ (n - n₀) * w * aeval u g := by
      rw [prod_zpow_neg (fun k => y ⟨k, c k⟩) hc k₀ γ, hX, mul_pow, hn', hg', ht', hexp, pow_mul]
      have hp : y ⟨k₀, c k₀⟩ ^ (J.1.card * n) * (y ⟨k₀, c k₀⟩)⁻¹ ^ (J.1.card * n) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (hc k₀), one_pow]
      field_simp
      linear_combination (w * aeval u g) * hp
    rw [key]
    exact mul_mem (mul_mem (pow_mem hxJ _) hw) (aeval_ratioPt_mem y c g)
  | zero => exact ⟨0, fun n _ => by simp⟩
  | add z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨n₁, h₁⟩ := h₁
    obtain ⟨n₂, h₂⟩ := h₂
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    have := add_mem (h₁ n (le_of_max_le_left hn)) (h₂ n (le_of_max_le_right hn))
    rwa [← add_mul, ← mul_add] at this
  | smul r z _ h =>
    obtain ⟨n₀, h⟩ := h
    refine ⟨n₀, fun n hn => ?_⟩
    have e1 : Kleiman.xProd J ^ n * (r • z) *
        ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
        algebraMap S Ω r * (Kleiman.xProd J ^ n * z *
          ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) := by
      rw [Algebra.smul_def]; ring
    rw [e1]
    exact mul_mem (Subalgebra.algebraMap_mem _ r) (h n hn)

end RowSecGlue

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J a h`. Establish `hc : ∀ c : ∀ k, ι k, ∃ n₀ : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ n ≥ n₀, Kleiman.xProd J ^ n * a * ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) ∈ chartRingOver S y c`. Introduce `c`. Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Take `⟨n₀, h'⟩` from `RowSecGlue.exists_pow_of_mem_cellSec y k₀ e γ J c hc (h c hc)`.

Conclude with `⟨n₀, fun _ => h'⟩`. Conclude with `⟨0, fun h' => absurd h' hc⟩`. Use `choose n₀ hn₀ using hc`. Use `⟨Finset.univ.sup n₀, ?_⟩` and prove the remaining obligations. Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule]`.

Introduce `c hc'`. Conclude with `hn₀ c hc' _ (Finset.le_sup (Finset.mem_univ c))`.
-/
theorem RowSecGlue.proof : RowSecGlue.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J a h
  have hc : ∀ c : ∀ k, ι k, ∃ n₀ : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ n ≥ n₀, Kleiman.xProd J ^ n * a *
      ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) ∈ chartRingOver S y c := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n₀, h'⟩ := RowSecGlue.exists_pow_of_mem_cellSec y k₀ e γ J c hc (h c hc)
      exact ⟨n₀, fun _ => h'⟩
    · exact ⟨0, fun h' => absurd h' hc⟩
  choose n₀ hn₀ using hc
  refine ⟨Finset.univ.sup n₀, ?_⟩
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c hc'
  exact hn₀ c hc' _ (Finset.le_sup (Finset.mem_univ c))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
