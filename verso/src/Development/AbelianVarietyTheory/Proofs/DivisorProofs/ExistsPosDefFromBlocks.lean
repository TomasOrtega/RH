import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl.BlockPos

/- English proof (translation)
Use `⟨∑ i, ∑ j, |S i j|, fun x => ?_⟩` and prove the remaining obligations. Establish `h : ∀ i, x i * x i ≤ x ⬝ᵥ x` using `fun i => Finset.single_le_sum (f := fun i => x i * x i) (fun _ _ => mul_self_nonneg _) (Finset.mem_univ i)`. Rewrite using `[Finset.sum_mul, ← Finset.sum_neg_distrib]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, ← Finset.sum_neg_distrib, mulVec, dotProduct, dotProduct, Finset.mul_sum]`.

Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Establish `hi` using `h i`. Establish `hj` using `h j`. Rewrite `hi`, `hj` using `[dotProduct]`. Apply the tactic sequence `rcases abs_cases (S i j) with ⟨e, p⟩ | ⟨e, p⟩ <;> rw [e]`.

Use polynomial arithmetic with `[mul_nonneg p (sq_nonneg (x i + x j)), mul_le_mul_of_nonneg_left hi p, mul_le_mul_of_nonneg_left hj p]`. Establish `p' : 0 ≤ -S i j` using `by linarith`. Use polynomial arithmetic with `[mul_nonneg p' (sq_nonneg (x i - x j)), mul_le_mul_of_nonneg_left hi p', mul_le_mul_of_nonneg_left hj p']`.
-/
theorem exists_neg_mul_le {n : Type} [Fintype n] (S : Matrix n n ℝ) :
    ∃ C : ℝ, ∀ x : n → ℝ, -(C * (x ⬝ᵥ x)) ≤ x ⬝ᵥ S *ᵥ x := by
  refine ⟨∑ i, ∑ j, |S i j|, fun x => ?_⟩
  have h : ∀ i, x i * x i ≤ x ⬝ᵥ x := fun i =>
    Finset.single_le_sum (f := fun i => x i * x i) (fun _ _ => mul_self_nonneg _) (Finset.mem_univ i)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib, mulVec, dotProduct, dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hi := h i
  have hj := h j
  rw [dotProduct] at hi hj
  rcases abs_cases (S i j) with ⟨e, p⟩ | ⟨e, p⟩ <;> rw [e]
  · nlinarith [mul_nonneg p (sq_nonneg (x i + x j)), mul_le_mul_of_nonneg_left hi p, mul_le_mul_of_nonneg_left hj p]
  · have p' : 0 ≤ -S i j := by linarith
    nlinarith [mul_nonneg p' (sq_nonneg (x i - x j)), mul_le_mul_of_nonneg_left hi p', mul_le_mul_of_nonneg_left hj p']

/- English proof (translation)
Take `⟨c, hc, hcB⟩` from `posDef_exists_mul_dotProduct_le hB`. Take `⟨C, hC⟩` from `exists_neg_mul_le (Q - Pᴴ * Y⁻¹ * P)`. Establish `: Invertible Y` using `(isUnit_iff_isUnit_det Y).mpr (hY.det_pos.ne').isUnit |>.invertible`. Use `⟨max 0 (C / c), fun t ht => ?_⟩` and prove the remaining obligations. Establish `ht0 : 0 < t` using `(le_max_left _ _).trans_lt ht`.

Establish `htC : C < t * c` using `(div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt ht)`. Establish `hH : (Q + t • B).IsHermitian` using `hQ.add (hB.smul ht0).1`. Use `PosDef.of_dotProduct_mulVec_pos (hY.1.fromBlocks rfl hH) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← Sum.elim_comp_inl_inr x, dotProduct_mulVec, schur_complement_eq₁₁ P _ _ _ hY.1, ← dotProduct_mulVec, ← dotProduct_mulVec]`. Distinguish the cases in `h2 : x ∘ Sum.inr = 0`.

Establish `h1 : x ∘ Sum.inl ≠ 0` using `fun h1 => hx (by rw [← Sum.elim_comp_inl_inr x, h1, h2]; simp)`. Simplify `hY.dotProduct_mulVec_pos h1` using `[h2]`. Use `add_pos_of_nonneg_of_pos (hY.posSemidef.dotProduct_mulVec_nonneg _) ?_` and prove the remaining obligations. Establish `e : Q + t • B - Pᴴ * Y⁻¹ * P = (Q - Pᴴ * Y⁻¹ * P) + t • B` using `by abel`. Rewrite using `[e, star_trivial, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]`.

Establish `a1` using `hC (x ∘ Sum.inr)`. Establish `a2` using `mul_le_mul_of_nonneg_left (hcB (x ∘ Sum.inr)) ht0.le`. Establish `a3 : 0 < (x ∘ Sum.inr) ⬝ᵥ (x ∘ Sum.inr)`. Simplify using `using (dotProduct_star_self_pos_iff (v := x ∘ Sum.inr)).mpr h2`. Use polynomial arithmetic with `[mul_pos (sub_pos.mpr htC) a3]`.
-/
theorem exists_posDef_fromBlocks {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {Y : Matrix m m ℝ} (hY : Y.PosDef) (P : Matrix m n ℝ) {Q B : Matrix n n ℝ} (hQ : Q.IsHermitian) (hB : B.PosDef) :
    ∃ T : ℝ, ∀ t : ℝ, T < t → (fromBlocks Y P Pᴴ (Q + t • B)).PosDef := by
  obtain ⟨c, hc, hcB⟩ := posDef_exists_mul_dotProduct_le hB
  obtain ⟨C, hC⟩ := exists_neg_mul_le (Q - Pᴴ * Y⁻¹ * P)
  have : Invertible Y := (isUnit_iff_isUnit_det Y).mpr (hY.det_pos.ne').isUnit |>.invertible
  refine ⟨max 0 (C / c), fun t ht => ?_⟩
  have ht0 : 0 < t := (le_max_left _ _).trans_lt ht
  have htC : C < t * c := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt ht)
  have hH : (Q + t • B).IsHermitian := hQ.add (hB.smul ht0).1
  refine PosDef.of_dotProduct_mulVec_pos (hY.1.fromBlocks rfl hH) fun x hx => ?_
  rw [← Sum.elim_comp_inl_inr x, dotProduct_mulVec, schur_complement_eq₁₁ P _ _ _ hY.1, ← dotProduct_mulVec,
    ← dotProduct_mulVec]
  by_cases h2 : x ∘ Sum.inr = 0
  · have h1 : x ∘ Sum.inl ≠ 0 := fun h1 => hx (by rw [← Sum.elim_comp_inl_inr x, h1, h2]; simp)
    simpa [h2] using hY.dotProduct_mulVec_pos h1
  · refine add_pos_of_nonneg_of_pos (hY.posSemidef.dotProduct_mulVec_nonneg _) ?_
    have e : Q + t • B - Pᴴ * Y⁻¹ * P = (Q - Pᴴ * Y⁻¹ * P) + t • B := by abel
    rw [e, star_trivial, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
    have a1 := hC (x ∘ Sum.inr)
    have a2 := mul_le_mul_of_nonneg_left (hcB (x ∘ Sum.inr)) ht0.le
    have a3 : 0 < (x ∘ Sum.inr) ⬝ᵥ (x ∘ Sum.inr) := by
      simpa using (dotProduct_star_self_pos_iff (v := x ∘ Sum.inr)).mpr h2
    nlinarith [mul_pos (sub_pos.mpr htC) a3]

/- English proof (translation)
Introduce `N g' r g bX d σ k β`. Establish `hB` using `(ClassMin.realExtension_posDef_iff _ bX).mp (ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos)`. Establish `hQ : (d.t22.map Complex.im).IsHermitian`. Use extensionality with `i j`. Simplify using `[d.toricPeriodBlock_isSymm.apply i j]`.

Take `⟨T, hT⟩` from `exists_posDef_fromBlocks d.pos (d.t12.map Complex.im) hQ hB`. Use `⟨T, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hs : (w • bmat bX β).IsSymm`. Use extensionality with `i j`. Simplify using `[bmat, β.symm (bX j) (bX i)]`.

Use `⟨hs, (IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hs)).submatrix σ, ?_⟩` and prove the remaining obligations. Use `(hT w.im hw).submatrix σ.injective using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `only [CD.full, map_apply, submatrix_apply]`. Apply the tactic sequence `rcases σ i with a | a <;> rcases σ j with b | b <;> simp [bmat, ClassMin.polar_ofIntBilin β.symm]`.
-/
theorem full_posDef : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ (k : ℕ) (β : N.Form k), ∃ T : ℝ, ∀ w : ℂ, T < w.im →
    (w • bmat bX β).IsSymm ∧ (d.full σ (w • bmat bX β)).IsSymm ∧
      ((d.full σ (w • bmat bX β)).map Complex.im).PosDef := by
  intro N g' r g bX d σ k β
  have hB := (ClassMin.realExtension_posDef_iff _ bX).mp (ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos)
  have hQ : (d.t22.map Complex.im).IsHermitian := by
    ext i j
    simp [d.toricPeriodBlock_isSymm.apply i j]
  obtain ⟨T, hT⟩ := exists_posDef_fromBlocks d.pos (d.t12.map Complex.im) hQ hB
  refine ⟨T, fun w hw => ?_⟩
  have hs : (w • bmat bX β).IsSymm := by
    ext i j
    simp [bmat, β.symm (bX j) (bX i)]
  refine ⟨hs, (IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hs)).submatrix σ, ?_⟩
  convert (hT w.im hw).submatrix σ.injective using 1
  ext i j
  simp only [CD.full, map_apply, submatrix_apply]
  rcases σ i with a | a <;> rcases σ j with b | b <;> simp [bmat, ClassMin.polar_ofIntBilin β.symm]

end GlobalTheory.MBLow.Cl.BlockPos
