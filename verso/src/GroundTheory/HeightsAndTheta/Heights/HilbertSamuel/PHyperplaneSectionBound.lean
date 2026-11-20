import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneQuotientBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Mul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `c' hc'`. Establish `h` using `ht c' hc'`. Establish `hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) = y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k)) / y ⟨k, c' k⟩`. Introduce `k`. Rewrite using `[eq_div_iff (hc' k), ← zpow_add_one₀ (hc' k)]`.

Use `congr 1`. Simplify using `only [Pi.sub_apply, Pi.one_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `heq : (∏ k, y ⟨k, c k⟩) * t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) = (t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩)`. Simplify using `only [hk, Finset.prod_div_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Use `Subalgebra.mul_mem _ h (Subalgebra.prod_mem _ fun k _ => ?_)` and prove the remaining obligations. Conclude with `Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩`.
-/
theorem mul_mem_chartLatQ (b : K → ℤ) {t : Ω} (ht : t ∈ chartLatQ y (b - 1) 1) :
    (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1 := by
  intro c' hc'
  have h := ht c' hc'
  have hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k)) / y ⟨k, c' k⟩ := by
    intro k
    rw [eq_div_iff (hc' k), ← zpow_add_one₀ (hc' k)]
    congr 1
    simp only [Pi.sub_apply, Pi.one_apply]
    ring
  have heq : (∏ k, y ⟨k, c k⟩) * t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      (t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) := by
    simp only [hk, Finset.prod_div_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ h (Subalgebra.prod_mem _ fun k _ => ?_)
  exact Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩

/- English proof (translation)
Distinguish the cases in `hfin : FiniteDimensional ℚ (chartLatQ y b 1)`. Use `swap`. Rewrite using `[Module.finrank_of_not_finite hfin]`. Conclude with `Nat.zero_le _`. Establish `hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`.

Set `φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b` to `{ toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, mul_mem_chartLatQ b t.2⟩, Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩ map_add' := fun s t => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_add, mul_add]`. Use the proof step `map_smul' := fun r t => by`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }`. Establish `hinj : Function.Injective φ` using `fun s t h => by`. Establish `h'` using `congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h`.

Conclude with `Subtype.ext (mul_left_cancel₀ hm0 h')`. Establish `hsurj : Function.Surjective φ`. Introduce and unpack `⟨⟨s, hsV⟩, hs⟩`. Take `⟨t, ht, hts⟩` from `Submodule.mem_map.mp (Submodule.mem_comap.mp hs)`. Conclude with `⟨⟨t, ht⟩, Subtype.ext (Subtype.ext hts)⟩`.

Establish `hφ` using `(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq`. Rewrite using `[← Submodule.finrank_quotient_add_finrank (chartDivSec y c b), ← hφ, add_comm]`.
-/
theorem finrank_chartLatQ_le (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) :
    Module.finrank ℚ (chartLatQ y b 1) ≤
      Module.finrank ℚ (chartLatQ y (b - 1) 1) + Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) := by
  by_cases hfin : FiniteDimensional ℚ (chartLatQ y b 1)
  swap
  · rw [Module.finrank_of_not_finite hfin]; exact Nat.zero_le _
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  let φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b :=
    { toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, mul_mem_chartLatQ b t.2⟩,
        Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩
      map_add' := fun s t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun r t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective φ := fun s t h => by
    have h' := congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h
    exact Subtype.ext (mul_left_cancel₀ hm0 h')
  have hsurj : Function.Surjective φ := by
    rintro ⟨⟨s, hsV⟩, hs⟩
    obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hs)
    exact ⟨⟨t, ht⟩, Subtype.ext (Subtype.ext hts)⟩
  have hφ := (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  rw [← Submodule.finrank_quotient_add_finrank (chartDivSec y c b), ← hφ, add_comm]

end Mul

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D a hD hV hB`. Establish `hc : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Introduce `k`. Take `⟨i, hi⟩` from `hV.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations.

Rewrite using `[mCoordIdeal, RingHom.mem_ker]`. Simplify using `[mConeMap, h0]`. Use `choose c hc using hc`. Take `⟨C, hC⟩` from `hQ K ι Ω y D a c hD hV hB hc`. Use `⟨C, hC.mono fun n hn => ?_⟩` and prove the remaining obligations.

Establish `h` using `finrank_chartLatQ_le hc ((n : ℤ) • a)`. Establish `h' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) ≤ (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a - 1) 1) : ℝ) + (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ)`. Conclude with `h` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem HyperplaneSectionBound.proof (hQ : HyperplaneQuotientBound.Statement) :
    HyperplaneSectionBound.Statement := by
  intro K _ ι _ Ω _ _ y D a hD hV hB
  have hc : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  choose c hc using hc
  obtain ⟨C, hC⟩ := hQ K ι Ω y D a c hD hV hB hc
  refine ⟨C, hC.mono fun n hn => ?_⟩
  have h := finrank_chartLatQ_le hc ((n : ℤ) • a)
  have h' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a - 1) 1) : ℝ) +
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ) := by
    exact_mod_cast h
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
