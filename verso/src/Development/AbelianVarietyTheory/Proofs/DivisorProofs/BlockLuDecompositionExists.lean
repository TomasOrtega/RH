import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsLowerMulUpperOfLeadingMinors
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun i => ((Finset.range (i + 1)).filter (· ∈ S)).card, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Use `Finset.card_le_card (Finset.filter_subset_filter _ ?_)` and prove the remaining obligations. Conclude with `Finset.range_subset_range.2 (by omega)`. Introduce `i j`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, h1, h2⟩`. Use `Finset.card_lt_card ⟨Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega)), ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `: s ∈ (Finset.range (j + 1)).filter (· ∈ S)` using `h (by simp [hs]; omega)`.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Assume the negation of the conclusion as `hne`. Use `absurd h (not_lt.2 (Finset.card_le_card ?_))` and prove the remaining obligations.

Introduce `s hs`. Simplify using `only [Finset.mem_filter, Finset.mem_range] at hs ⊢`. Use `⟨?_, hs.2⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h'`. Conclude with `hne ⟨s, hs.2, by omega, by omega⟩`.
-/
theorem exists_monotone_blockFun (S : Set ℕ) :
    ∃ f : ℕ → ℕ, Monotone f ∧ ∀ i j : ℕ, (∃ s ∈ S, j < s ∧ s ≤ i) ↔ f j < f i := by
  classical
  refine ⟨fun i => ((Finset.range (i + 1)).filter (· ∈ S)).card, ?_, ?_⟩
  · intro a b hab
    refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
    exact Finset.range_subset_range.2 (by omega)
  · intro i j
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      refine Finset.card_lt_card ⟨Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega)), ?_⟩
      intro h
      have : s ∈ (Finset.range (j + 1)).filter (· ∈ S) := h (by simp [hs]; omega)
      simp at this
      omega
    · intro h
      by_contra hne
      refine absurd h (not_lt.2 (Finset.card_le_card ?_))
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
      refine ⟨?_, hs.2⟩
      by_contra h'
      exact hne ⟨s, hs.2, by omega, by omega⟩

/- English proof (translation)
Introduce `A _ N S g hm`. Take `⟨l, u, hl0, hl1, hu, hg⟩` from `exists_lower_mul_upper_of_leading_minors N g.1 hm`. Take `⟨f₀, hf, hS⟩` from `exists_monotone_blockFun S`. Set `f : Fin N → ℕ` to `fun i => f₀ i`. Establish `hlt : ∀ i j : Fin N, f i < f j → i < j` using `fun i j h => hf.reflect_lt h`.

Set `d : Matrix (Fin N) (Fin N) A` to `Matrix.of fun i j => if f i = f j then l i j else 0`. Establish `hdd : d.det = 1` using `det_eq_one_of_lower_unitriangular d (fun i j h => by simp [d, hl0 i j h]) (fun i => by simp [d, hl1])`. Establish `hdu : IsUnit d.det` using `by rw [hdd]; exact isUnit_one`. Establish `hld : l.det = 1` using `det_eq_one_of_lower_unitriangular l hl0 hl1`. Establish `hd1 : d.BlockTriangular f` using `fun i j h => by simp [d, h.ne']`.

Establish `hd2 : d.BlockTriangular (OrderDual.toDual ∘ f)` using `fun i j h => by`. Establish `h' : f i < f j` using `h`. Simplify using `[d, h'.ne]`. Use `letI := Matrix.invertibleOfIsUnitDet d hdu`. Establish `hi1` using `Matrix.blockTriangular_inv_of_blockTriangular hd1`.

Establish `hi2` using `Matrix.blockTriangular_inv_of_blockTriangular hd2`. Establish `hLu : IsUnit (l * d⁻¹)`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, hld, one_mul]`. Conclude with `Matrix.isUnit_nonsing_inv_det d hdu`. Take `⟨L, hL⟩` from `hLu`.

Establish `hb : (L⁻¹ * g).1 = d * u`. Establish `: g.1 = L.1 * (d * u)`. Rewrite using `[hL, hg, Matrix.mul_assoc, ← Matrix.mul_assoc d⁻¹, Matrix.nonsing_inv_mul _ hdu, Matrix.one_mul]`. Rewrite using `[Units.val_mul, this, ← mul_assoc, Units.inv_mul, one_mul]`. Use `⟨L, L⁻¹ * g, by rw [mul_inv_cancel_left], ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j hij`. Rewrite `hij` using `[hS]`. Establish `hij' : f i ≤ f j` using `not_lt.1 hij`. Rewrite using `[hL, ← Matrix.mul_nonsing_inv d hdu, Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Break down `lt_trichotomy (f k) (f j) with h | h | h` into its components or cases. Rewrite using `[hi2 (i := k) (j := j) h, mul_zero, mul_zero]`. Distinguish the cases in `h' : f i = f k`. Simplify using `[d, h']`. Establish `: l i k = 0` using `hl0 i k (hlt _ _ (lt_of_le_of_ne (h ▸ hij') h'))`.

Simplify using `[d, this]`. Rewrite using `[hi1 (i := k) (j := j) h, mul_zero, mul_zero]`. Introduce `i j hij`. Rewrite `hij` using `[hS]`. Establish `hu' : u.BlockTriangular f` using `fun i j h => hu (hlt _ _ h)`.

Rewrite using `[hb]`. Conclude with `(hd1.mul hu') hij`.
-/
theorem exists_blockLower_mul_blockUpper :
    ∀ (A : Type) [CommRing A] (N : ℕ) (S : Set ℕ) (g : GL (Fin N) A), (∀ (k : ℕ) (hk : k ≤ N), IsUnit (g.1.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) → ∃ L b : GL (Fin N) A, g = L * b ∧ (∀ i j : Fin N, ¬ (∃ s ∈ S, (j : ℕ) < s ∧ s ≤ (i : ℕ)) → L.1 i j = (1 : Matrix (Fin N) (Fin N) A) i j) ∧ ∀ i j : Fin N, (∃ s ∈ S, (j : ℕ) < s ∧ s ≤ (i : ℕ)) → b.1 i j = 0 := by
  intro A _ N S g hm
  obtain ⟨l, u, hl0, hl1, hu, hg⟩ := exists_lower_mul_upper_of_leading_minors N g.1 hm
  obtain ⟨f₀, hf, hS⟩ := exists_monotone_blockFun S
  let f : Fin N → ℕ := fun i => f₀ i
  have hlt : ∀ i j : Fin N, f i < f j → i < j := fun i j h => hf.reflect_lt h
  let d : Matrix (Fin N) (Fin N) A := Matrix.of fun i j => if f i = f j then l i j else 0
  have hdd : d.det = 1 := det_eq_one_of_lower_unitriangular d
    (fun i j h => by simp [d, hl0 i j h]) (fun i => by simp [d, hl1])
  have hdu : IsUnit d.det := by rw [hdd]; exact isUnit_one
  have hld : l.det = 1 := det_eq_one_of_lower_unitriangular l hl0 hl1
  have hd1 : d.BlockTriangular f := fun i j h => by simp [d, h.ne']
  have hd2 : d.BlockTriangular (OrderDual.toDual ∘ f) := fun i j h => by
    have h' : f i < f j := h
    simp [d, h'.ne]
  letI := Matrix.invertibleOfIsUnitDet d hdu
  have hi1 := Matrix.blockTriangular_inv_of_blockTriangular hd1
  have hi2 := Matrix.blockTriangular_inv_of_blockTriangular hd2
  have hLu : IsUnit (l * d⁻¹) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, hld, one_mul]
    exact Matrix.isUnit_nonsing_inv_det d hdu
  obtain ⟨L, hL⟩ := hLu
  have hb : (L⁻¹ * g).1 = d * u := by
    have : g.1 = L.1 * (d * u) := by
      rw [hL, hg, Matrix.mul_assoc, ← Matrix.mul_assoc d⁻¹, Matrix.nonsing_inv_mul _ hdu,
        Matrix.one_mul]
    rw [Units.val_mul, this, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨L, L⁻¹ * g, by rw [mul_inv_cancel_left], ?_, ?_⟩
  · intro i j hij
    rw [hS] at hij
    have hij' : f i ≤ f j := not_lt.1 hij
    rw [hL, ← Matrix.mul_nonsing_inv d hdu, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases lt_trichotomy (f k) (f j) with h | h | h
    · rw [hi2 (i := k) (j := j) h, mul_zero, mul_zero]
    · by_cases h' : f i = f k
      · simp [d, h']
      · have : l i k = 0 := hl0 i k (hlt _ _ (lt_of_le_of_ne (h ▸ hij') h'))
        simp [d, this]
    · rw [hi1 (i := k) (j := j) h, mul_zero, mul_zero]
  · intro i j hij
    rw [hS] at hij
    have hu' : u.BlockTriangular f := fun i j h => hu (hlt _ _ h)
    rw [hb]
    exact (hd1.mul hu') hij

end GlobalTheory
