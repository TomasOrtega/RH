import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowIndexLeOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaMove

/- English proof (translation)
Introduce `g hg`. Establish `h` using `hx _ (hH.conj_mem' g hg σ)`. Establish `h2 : σ ((σ⁻¹ * g * σ) x) = g (σ x)`. Rewrite using `[← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]`. Use `congr 1`.

Use `group`. Rewrite using `[← h2, h]`.
-/
theorem fixed_apply {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal) (σ : GQ l)
    {x : Om l} (hx : ∀ g ∈ H, g x = x) : ∀ g ∈ H, g (σ x) = σ x := by
  intro g hg
  have h := hx _ (hH.conj_mem' g hg σ)
  have h2 : σ ((σ⁻¹ * g * σ) x) = g (σ x) := by
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  rw [← h2, h]

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

/- English proof (translation)
The claim follows from `IsUltrametricDist.norm_natCast_le_one _ _`.
-/
theorem norm_natCast_le_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one _ _

/- English proof (translation)
Introduce `l hl γ hγ H hH hi m n hm hn j`. Establish `hτ0 : 0 ≤ ‖((l : ℕ) : Om l)‖` using `norm_nonneg _`. Establish `hτ1` using `norm_natCast_le_one l`. Establish `hl0 : l ≠ 0` using `hl.out.ne_zero`. Establish `hlR : (0 : ℝ) < l` using `by exact_mod_cast hl.out.pos`.

Establish `hτpos : 0 < ‖((l : ℕ) : Om l)‖`. Rewrite using `[norm_pos_iff]`. Conclude with `hl0` after adjusting the coercions. Proceed by induction on `j with`. Consider the case `zero`.

Introduce `_ x hx`. Distinguish the cases in `hx0 : x = 0`. Simplify using `[hx0]`. Establish `hxpos : 0 < ‖x‖` using `norm_pos_iff.2 hx0`. Establish `hlt` using `GlobalTheory.WildMove.norm_sub_lt l γ hγ n x hx0 (hx _ hn)`.

Use `set z : Om l := (γ x - x) / x with hz`. Establish `hzfix : ∀ g ∈ H, g z = z`. Introduce `g hg`. Rewrite using `[hz, map_div₀, map_sub, fixed_apply hH γ hx g hg, hx g hg]`. Establish `hzn : ‖z‖ = ‖γ x - x‖ / ‖x‖` using `norm_div _ _`.

Establish `hz1 : ‖z‖ < 1` using `by rw [hzn, div_lt_one hxpos]; exact hlt`. Establish `hv` using `GlobalTheory.Per.norm_pow_index_le_of_fixed l H hi z hzfix hz1`. Establish `h1 : ‖z‖ ^ (l ^ m) ≤ ‖((l : ℕ) : Om l)‖` using `(pow_le_pow_of_le_one (norm_nonneg _) hz1.le hm).trans hv`. Establish `h2 : ‖z‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ m)`. Establish `h3` using `Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ ((l ^ m : ℕ) : ℝ)⁻¹ by positivity)`.

Rewrite `h3` using `[Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ hl0)]`. Rewrite using `[one_div]`. Conclude with `h3` after adjusting the coercions. Rewrite `h2` using `[hzn, div_le_iff₀ hxpos]`. Simplify using `using h2`.

Consider the case `succ j ih`. Introduce `hj x hx`. Establish `ih'` using `ih (by omega)`. Take `⟨k, hk⟩ : ∃ k, m - j = k + 1` from `⟨m - j - 1, by omega⟩`. Establish `hk' : m - (j + 1) = k` using `by omega`.

Rewrite `ih'` using `[hk]`. Rewrite using `[hk']`. Use `set s : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hs`. Establish `hs0 : 0 ≤ s` using `Real.rpow_nonneg hτ0 _`. Establish `hs1 : s ≤ 1` using `Real.rpow_le_one hτ0 hτ1 (by positivity)`.

Establish `h` using `(GlobalTheory.MemLoc.norm_geom_sum_galois_le l (γ ^ l ^ j) (fixedAdd H) s hs0 hs1 (fun y hy => fixed_apply hH _ hy) (fun y hy => ih' y hy) x hx).2`. Rewrite `h` using `[← pow_mul, ← pow_succ]`. Establish `hsl : s ^ l = ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ k)`. Rewrite using `[hs, ← Real.rpow_natCast, ← Real.rpow_mul hτ0]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hτs : ‖((l : ℕ) : Om l)‖ ≤ s ^ (l - 1)`. Establish `h1 : s ^ l ≤ s ^ (l - 1)` using `pow_le_pow_of_le_one hs0 hs1 (by omega)`. Use `le_trans ?_ h1` and prove the remaining obligations.

Rewrite using `[hsl]`. Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast hl.out.pos`. Establish `h2 : (1 : ℝ) / (l : ℝ) ^ k ≤ 1`. Rewrite using `[div_le_one (by positivity)]`. Conclude with `one_le_pow₀ hl1`.

Establish `h3` using `Real.rpow_le_rpow_of_exponent_ge hτpos hτ1 h2`. Rewrite `h3` using `[Real.rpow_one]`. Then use the resulting hypothesis. Rewrite `h` using `[max_eq_left hτs, ← pow_succ, Nat.sub_add_cancel hl.out.pos, hsl]`. Conclude with `h`.
-/
theorem norm_pow_sub_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : Subgroup (GQ l)), H.Normal → H.index ≠ 0 → ∀ m n : ℕ, H.index ≤ l ^ m → γ ^ l ^ n ∈ H → ∀ j ≤ m, ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖(γ ^ l ^ j) x - x‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (m - j)) * ‖x‖ := by
  intro l hl γ hγ H hH hi m n hm hn j
  have hτ0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have hτ1 := norm_natCast_le_one l
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hτpos : 0 < ‖((l : ℕ) : Om l)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hl0
  induction j with
  | zero =>
    intro _ x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hlt := GlobalTheory.WildMove.norm_sub_lt l γ hγ n x hx0 (hx _ hn)
    set z : Om l := (γ x - x) / x with hz
    have hzfix : ∀ g ∈ H, g z = z := by
      intro g hg
      rw [hz, map_div₀, map_sub, fixed_apply hH γ hx g hg, hx g hg]
    have hzn : ‖z‖ = ‖γ x - x‖ / ‖x‖ := norm_div _ _
    have hz1 : ‖z‖ < 1 := by rw [hzn, div_lt_one hxpos]; exact hlt
    have hv := GlobalTheory.Per.norm_pow_index_le_of_fixed l H hi z hzfix hz1
    have h1 : ‖z‖ ^ (l ^ m) ≤ ‖((l : ℕ) : Om l)‖ :=
      (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hm).trans hv
    have h2 : ‖z‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ m) := by
      have h3 := Real.rpow_le_rpow (by positivity) h1
        (show (0 : ℝ) ≤ ((l ^ m : ℕ) : ℝ)⁻¹ by positivity)
      rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ hl0)] at h3
      rw [one_div]
      exact_mod_cast h3
    rw [hzn, div_le_iff₀ hxpos] at h2
    simpa using h2
  | succ j ih =>
    intro hj x hx
    have ih' := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
    have hk' : m - (j + 1) = k := by omega
    rw [hk] at ih'
    rw [hk']
    set s : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hs
    have hs0 : 0 ≤ s := Real.rpow_nonneg hτ0 _
    have hs1 : s ≤ 1 := Real.rpow_le_one hτ0 hτ1 (by positivity)
    have h := (GlobalTheory.MemLoc.norm_geom_sum_galois_le l (γ ^ l ^ j) (fixedAdd H) s hs0 hs1
      (fun y hy => fixed_apply hH _ hy) (fun y hy => ih' y hy) x hx).2
    rw [← pow_mul, ← pow_succ] at h
    have hsl : s ^ l = ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ k) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hτ0]
      congr 1
      field_simp
      ring
    have hτs : ‖((l : ℕ) : Om l)‖ ≤ s ^ (l - 1) := by
      have h1 : s ^ l ≤ s ^ (l - 1) := pow_le_pow_of_le_one hs0 hs1 (by omega)
      refine le_trans ?_ h1
      rw [hsl]
      have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.pos
      have h2 : (1 : ℝ) / (l : ℝ) ^ k ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ hl1
      have h3 := Real.rpow_le_rpow_of_exponent_ge hτpos hτ1 h2
      rwa [Real.rpow_one] at h3
    rw [max_eq_left hτs, ← pow_succ, Nat.sub_add_cancel hl.out.pos, hsl] at h
    exact h

end GlobalTheory.InertiaMove
