import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelLatticeFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SpanStepLocal

def powMulSub {Ω : Type*} [Field Ω] (R : Subalgebra ℤ Ω) (v : Ω) (hv : v ∈ R) : Subalgebra ℤ Ω where
  carrier := {x | ∃ E : ℕ, x * v ^ E ∈ R}
  mul_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : x * z * v ^ (E₁ + E₂) = (x * v ^ E₁) * (z * v ^ E₂) := by ring
    rw [e]; exact R.mul_mem h₁ h₂
  add_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : (x + z) * v ^ (E₁ + E₂) = (x * v ^ E₁) * v ^ E₂ + (z * v ^ E₂) * v ^ E₁ := by ring
    rw [e]; exact R.add_mem (R.mul_mem h₁ (R.pow_mem hv _)) (R.mul_mem h₂ (R.pow_mem hv _))
  algebraMap_mem' r := ⟨0, by rw [pow_zero, mul_one]; exact R.algebraMap_mem r⟩

/- English proof (translation)
Rewrite using `[mul_pow, ← Finset.prod_pow, mul_assoc]`. Use `congr 3`. Use function extensionality and compare the values at `k`. Rewrite using `[← zpow_natCast, ← zpow_mul]`. Put the polynomial expressions in normal form.
-/
theorem pow_twist {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω)
    (a : K → ℤ) (c : ∀ k, ι k) (g w : Ω) (n : ℕ) :
    g * w ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) = g * (w * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ n := by
  rw [mul_pow, ← Finset.prod_pow, mul_assoc]
  congr 3; funext k
  rw [← zpow_natCast, ← zpow_mul]; ring_nf

end SpanStepLocal

open SpanStepLocal in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y a q w hy hw hgen j hj`. Use `set P := Algebra.adjoin ℤ (Set.range fun i => w i / w j) with hPdef`. Use `set v : (∀ k, ι k) → Fin q → Ω := fun c i => w i * ∏ k, y ⟨k, c k⟩ ^ (-a k) with hvdef`. Establish `hv : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ i, v c i ∈ chartRingZ y c` using `fun c hc i => by`. Simplify `hw i c hc` using `[hvdef]`.

Establish `hv0 : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → v c j ≠ 0` using `fun c hc => mul_ne_zero hj (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))`. Establish `hquot : ∀ c i, w i / w j * v c j = v c i` using `fun c i => by`. Simplify using `only [hvdef]`. Rewrite using `[← mul_assoc, div_mul_cancel₀ _ hj]`. Establish `hrel : ∀ (g : Ω) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (g ∈ Algebra.adjoin P (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ↔ g * ∏ k, y ⟨k, c k⟩ ^ (-(((0 : ℕ) : ℤ) * (fun _ => (0 : ℤ)) k)) ∈ Algebra.adjoin P (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩))` using `fun g c _ => by simp`.

Establish `incl₁ : ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n → g ∈ relChartLat P y (fun _ => 0) 0`. Introduce `g n hg c hc`. Rewrite using `[← hrel g c hc]`. Use `set S := Algebra.adjoin P (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)`. Establish `hRS : ∀ x ∈ chartRingZ y c, x ∈ S` using `fun x hx => (Algebra.adjoin_le Algebra.subset_adjoin : chartRingZ y c ≤ S.restrictScalars ℤ) hx`.

Establish `hPS : ∀ x ∈ P, x ∈ S` using `fun x hx => S.algebraMap_mem (⟨x, hx⟩ : P)`. Take `⟨u, hu, hsum⟩` from `hgen c hc`. Establish `hinv : (∑ i, u i * (w i / w j)) = (v c j)⁻¹`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, ← hsum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, hquot]`. Establish `hinvS : (v c j)⁻¹ ∈ S` using `hinv ▸ S.sum_mem fun i _ => S.mul_mem (hRS _ (hu i)) (hPS _ (Algebra.subset_adjoin ⟨i, rfl⟩))`. Establish `hgv : g * v c j ^ n ∈ S` using `hRS _ (by rw [← pow_twist]; exact hg c hc)`. Establish `e : g = g * v c j ^ n * (v c j)⁻¹ ^ n`.

Rewrite using `[mul_assoc, ← mul_pow, mul_inv_cancel₀ (hv0 c hc), one_pow, mul_one]`. Rewrite using `[e]`. Conclude with `S.mul_mem hgv (S.pow_mem hinvS n)`. Establish `incl₂ : ∀ g ∈ relChartLat P y (fun _ => 0) 0, ∃ n : ℕ, g * w j ^ n ∈ chartLat y a n`. Introduce `g hg`.

Establish `hE : ∀ c, ∃ E : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → g * v c j ^ E ∈ chartRingZ y c`. Introduce `c`. Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Use `swap`. Use the proof step `· exact ⟨0, fun h => absurd h hc⟩`.

Establish `hgS` using `(hrel g c hc).2 (hg c hc)`. Establish `hg' : g ∈ Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪ Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)`. Rewrite using `[Algebra.adjoin_union_eq_adjoin_adjoin]`. Conclude with `hgS`. Establish `hle : Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪ Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ≤ powMulSub _ _ (hv c hc j)`.

Use `Algebra.adjoin_le (Set.union_subset ?_ ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩; exact ⟨1, by rw [pow_one, hquot]; exact hv c hc i⟩`. Introduce and unpack `_ ⟨p, rfl⟩; exact ⟨0, by rw [pow_zero, mul_one]; exact Algebra.subset_adjoin ⟨p, rfl⟩⟩`. Take `⟨E, hE⟩` from `hle hg'`. Conclude with `⟨E, fun _ => hE⟩`.

Use `choose E hE using hE`. Use `⟨∑ c, E c, fun c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_twist]`. Establish `e : g * v c j ^ (∑ c, E c) = g * v c j ^ E c * v c j ^ (∑ c, E c - E c)`. Rewrite using `[mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))]`.

Rewrite using `[e]`. Conclude with `(chartRingZ y c).mul_mem (hE c hc) ((chartRingZ y c).pow_mem (hv c hc j) _)`. Take `⟨r, b, hb⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp (hR K ι Ω y (fun _ => 0) 0 q (fun i => w i / w j) hy)`. Establish `hbmem : ∀ l, b l ∈ relChartLat P y (fun _ => 0) 0` using `fun l => hb ▸ Submodule.subset_span ⟨l, rfl⟩`. Use `⟨r, b, fun l => incl₂ _ (hbmem l), fun g n hg => ?_⟩` and prove the remaining obligations.

Establish `hgN` using `incl₁ g n hg`. Rewrite `hgN` using `[← hb, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, hc⟩` from `hgN`. Conclude with `⟨fun l => (c l : Ω), fun l => (c l).2, by rw [← hc]; rfl⟩`.
-/
theorem SpanStepLocal.proof (hR : RelLatticeFinite.Statement) : SpanStepLocal.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen j hj
  classical
  set P := Algebra.adjoin ℤ (Set.range fun i => w i / w j) with hPdef

  set v : (∀ k, ι k) → Fin q → Ω := fun c i => w i * ∏ k, y ⟨k, c k⟩ ^ (-a k) with hvdef
  have hv : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ i, v c i ∈ chartRingZ y c := fun c hc i => by
    simpa [hvdef] using hw i c hc
  have hv0 : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → v c j ≠ 0 := fun c hc =>
    mul_ne_zero hj (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))
  have hquot : ∀ c i, w i / w j * v c j = v c i := fun c i => by
    simp only [hvdef]; rw [← mul_assoc, div_mul_cancel₀ _ hj]
  have hrel : ∀ (g : Ω) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (g ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ↔
      g * ∏ k, y ⟨k, c k⟩ ^ (-(((0 : ℕ) : ℤ) * (fun _ => (0 : ℤ)) k)) ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) := fun g c _ => by simp

  have incl₁ : ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n → g ∈ relChartLat P y (fun _ => 0) 0 := by
    intro g n hg c hc
    rw [← hrel g c hc]
    set S := Algebra.adjoin P (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
    have hRS : ∀ x ∈ chartRingZ y c, x ∈ S := fun x hx =>
      (Algebra.adjoin_le Algebra.subset_adjoin : chartRingZ y c ≤ S.restrictScalars ℤ) hx
    have hPS : ∀ x ∈ P, x ∈ S := fun x hx => S.algebraMap_mem (⟨x, hx⟩ : P)
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    have hinv : (∑ i, u i * (w i / w j)) = (v c j)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [Finset.sum_mul, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, hquot]
    have hinvS : (v c j)⁻¹ ∈ S := hinv ▸ S.sum_mem fun i _ =>
      S.mul_mem (hRS _ (hu i)) (hPS _ (Algebra.subset_adjoin ⟨i, rfl⟩))
    have hgv : g * v c j ^ n ∈ S := hRS _ (by rw [← pow_twist]; exact hg c hc)
    have e : g = g * v c j ^ n * (v c j)⁻¹ ^ n := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (hv0 c hc), one_pow, mul_one]
    rw [e]; exact S.mul_mem hgv (S.pow_mem hinvS n)
  have incl₂ : ∀ g ∈ relChartLat P y (fun _ => 0) 0, ∃ n : ℕ, g * w j ^ n ∈ chartLat y a n := by
    intro g hg
    have hE : ∀ c, ∃ E : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → g * v c j ^ E ∈ chartRingZ y c := by
      intro c
      by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
      swap; · exact ⟨0, fun h => absurd h hc⟩
      have hgS := (hrel g c hc).2 (hg c hc)
      have hg' : g ∈ Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
        rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact hgS
      have hle : Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ≤ powMulSub _ _ (hv c hc j) := by
        refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
        · rintro _ ⟨i, rfl⟩; exact ⟨1, by rw [pow_one, hquot]; exact hv c hc i⟩
        · rintro _ ⟨p, rfl⟩; exact ⟨0, by rw [pow_zero, mul_one]; exact Algebra.subset_adjoin ⟨p, rfl⟩⟩
      obtain ⟨E, hE⟩ := hle hg'
      exact ⟨E, fun _ => hE⟩
    choose E hE using hE
    refine ⟨∑ c, E c, fun c hc => ?_⟩
    rw [pow_twist]
    have e : g * v c j ^ (∑ c, E c) = g * v c j ^ E c * v c j ^ (∑ c, E c - E c) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c))]
    rw [e]; exact (chartRingZ y c).mul_mem (hE c hc) ((chartRingZ y c).pow_mem (hv c hc j) _)

  obtain ⟨r, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (hR K ι Ω y (fun _ => 0) 0 q (fun i => w i / w j) hy)
  have hbmem : ∀ l, b l ∈ relChartLat P y (fun _ => 0) 0 := fun l =>
    hb ▸ Submodule.subset_span ⟨l, rfl⟩
  refine ⟨r, b, fun l => incl₂ _ (hbmem l), fun g n hg => ?_⟩
  have hgN := incl₁ g n hg
  rw [← hb, Submodule.mem_span_range_iff_exists_fun] at hgN
  obtain ⟨c, hc⟩ := hgN
  exact ⟨fun l => (c l : Ω), fun l => (c l).2, by rw [← hc]; rfl⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
