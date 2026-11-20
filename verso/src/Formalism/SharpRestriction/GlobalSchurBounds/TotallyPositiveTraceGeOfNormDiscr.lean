import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.UpperSlopeOfMaximalConstant
import Formalism.LocalToGlobal.GlobalTheory.GL4.PShortFrame
import Formalism.LocalToGlobal.GlobalTheory.GL4.PCoord
import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingIntegralNormalised
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP

noncomputable section

namespace Formalism.MainNotions.flipTwoThree

section RatTrans

open Module
open scoped InnerProductSpace Matrix

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder in
/- English proof (translation)
Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg`. Use `⟨B, ?_⟩` and prove the remaining obligations. Rewrite using `[hB, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]`.
-/
theorem posSemidef_eq_transpose_mul {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) :
    ∃ A : Matrix (Fin d) (Fin d) ℝ, G = A.transpose * A := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  refine ⟨B, ?_⟩
  rw [hB, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/- English proof (translation)
Establish `hfin : (S ∩ {r | R < r}).Finite` using `hS.subset Set.inter_subset_left`. Establish `hopen : IsOpen (S ∩ {r | R < r})ᶜ` using `hfin.isClosed.isOpen_compl`. Establish `hR : R ∈ (S ∩ {r | R < r})ᶜ` using `fun h => lt_irrefl R h.2`. Take `⟨ε, hε, hb⟩` from `Metric.isOpen_iff.mp hopen R hR`. Use `⟨ε, hε, fun r hr hlt => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Establish `hc' : R < r` using `not_le.mp hc`. Establish `: r ∈ Metric.ball R ε`. Rewrite using `[Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hb this ⟨hr, hc'⟩`.
-/
theorem exists_gap_above_finite_set (S : Set ℝ) (hS : S.Finite) (R : ℝ) : ∃ ε > 0, ∀ r ∈ S, r < R + ε → r ≤ R := by
  have hfin : (S ∩ {r | R < r}).Finite := hS.subset Set.inter_subset_left
  have hopen : IsOpen (S ∩ {r | R < r})ᶜ := hfin.isClosed.isOpen_compl
  have hR : R ∈ (S ∩ {r | R < r})ᶜ := fun h => lt_irrefl R h.2
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hopen R hR
  refine ⟨ε, hε, fun r hr hlt => ?_⟩
  by_contra hc
  have hc' : R < r := not_le.mp hc
  have : r ∈ Metric.ball R ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  exact hb this ⟨hr, hc'⟩

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {d : ℕ}

/- English proof (translation)
Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem bilinear_sum_smul_expand (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (b : Fin d → V) (c c' : Fin d → ℚ) :
    B (∑ i, c i • b i) (∑ j, c' j • b j) = ∑ i, ∑ j, c i * c' j * B (b i) (b j) := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `set Gq : Matrix (Fin d) (Fin d) ℚ := Matrix.of fun i j => B (b i) (b j) with hGq`. Use `set G : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => ((B (b i) (b j) : ℚ) : ℝ) with hG`. Establish `hquad : ∀ c : Fin d → ℚ, c ⬝ᵥ (Gq *ᵥ c) = B (∑ i, c i • b i) (∑ i, c i • b i)`. Introduce `c`. Rewrite using `[bilinear_sum_smul_expand]`.

Simplify using `only [dotProduct, Matrix.mulVec, hGq, Matrix.of_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Establish `hnn : ∀ x, 0 ≤ B x x`. Introduce `x`. Distinguish the cases in `hx : x = 0`.

Rewrite using `[hx]`. Simplify using the standard rewrite rules. Conclude with `(hpos x hx).le`. Establish `hdetq : Gq.det ≠ 0`. Introduce `h0`.

Take `⟨c, hc, hc0⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Establish `h1` using `hquad c`. Rewrite `h1` using `[hc0, dotProduct_zero]`. Establish `hx : (∑ i, c i • b i) = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `absurd h1 (ne_of_lt (hpos _ hne))`. Conclude with `hc (funext ((Fintype.linearIndependent_iff.mp b.linearIndependent) c hx))`. Establish `hGmap : G = (Rat.castHom ℝ).mapMatrix Gq`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hdet : G.det ≠ 0`. Rewrite using `[hGmap, ← RingHom.map_det]`. Simplify using `using hdetq`. Establish `hpsd : G.PosSemidef`. Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using `[hG, Matrix.conjTranspose_apply, hsymm (b j) (b i)]`. Introduce `x`. Establish `hden : DenseRange (Pi.map (fun (_ : Fin d) (q : ℚ) => (q : ℝ)))` using `DenseRange.piMap (fun _ => Rat.denseRange_cast)`. Use `hden.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ (G *ᵥ x)) x ?_ ?_` and prove the remaining obligations.

Apply `isClosed_le continuous_const` to reduce the goal to its premises. Simplify using `only [star_trivial, dotProduct, Matrix.mulVec]`. Use `fun_prop`. Introduce `c`. Establish `h1 : star (Pi.map (fun (_ : Fin d) (q : ℚ) => (q : ℝ)) c) ⬝ᵥ (G *ᵥ (Pi.map (fun (_ : Fin d) (q : ℚ) => (q : ℝ)) c)) = ((c ⬝ᵥ (Gq *ᵥ c) : ℚ) : ℝ)`.

Simplify using `[dotProduct, Matrix.mulVec, hG, hGq, Pi.map]`. Rewrite using `[h1, hquad]`. Conclude with `hnn _` after adjusting the coercions. Take `⟨A, hA⟩` from `posSemidef_eq_transpose_mul G hpsd`. Set `w : Fin d → EuclideanSpace ℝ (Fin d)` to `fun i => WithLp.toLp 2 (fun r => A r i)`.

Establish `hw : ∀ i j, ⟪w i, w j⟫_ℝ = ((B (b i) (b j) : ℚ) : ℝ)`. Introduce `i j`. Establish `h1 : G i j = ∑ r, A r i * A r j`. Rewrite using `[hA, Matrix.mul_apply]`. Both sides reduce to the same expression.

Establish `h2 : G i j = ((B (b i) (b j) : ℚ) : ℝ)` using `rfl`. Rewrite using `[← h2, h1]`. Use `show ⟪WithLp.toLp 2 (fun r => A r i), WithLp.toLp 2 (fun r => A r j)⟫_ℝ = _`. Rewrite using `[EuclideanSpace.inner_toLp_toLp]`. Simplify using `[dotProduct, mul_comm]`.

Establish `hli : LinearIndependent ℝ w`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Assume the negation of the conclusion as `hne`. Establish `hc0 : c ≠ 0` using `fun h => hne (fun i => congrFun h i)`.

Apply `hdet` to reduce the goal to its premises. Apply `Matrix.exists_mulVec_eq_zero_iff.mp` to reduce the goal to its premises. Use `⟨c, hc0, ?_⟩` and prove the remaining obligations. Use extensionality with `j`. Establish `h1 : ⟪w j, ∑ i, c i • w i⟫_ℝ = 0` using `by rw [hc, inner_zero_right]`.

Rewrite `h1` using `[inner_sum]`. Simplify using `only [real_inner_smul_right, hw] at h1`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun i _ => by simp [hG, mul_comm]` and prove the remaining obligations.

Establish `: Nonempty (Fin d)` using `⟨⟨0, hd⟩⟩`. Set `bE : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp)`. Establish `hbE : ∀ i, bE i = w i` using `fun i => by simp [bE]`. Set `M : Submodule ℤ (EuclideanSpace ℝ (Fin d))` to `Submodule.span ℤ (Set.range bE)`. Establish `hdisc : DiscreteTopology M` using `inferInstance`.

Establish `hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin d))) = ⊤`. Rewrite using `[Submodule.span_span_of_tower]`. Conclude with `bE.span_eq`. Set `φ : V → EuclideanSpace ℝ (Fin d)` to `fun x => ∑ i, ((b.repr x i : ℚ) : ℝ) • w i`. Establish `hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = ((B x y : ℚ) : ℝ)`.

Introduce `x y`. Establish `h1 : B x y = ∑ i, ∑ j, b.repr x i * b.repr y j * B (b i) (b j)`. Rewrite using `[← bilinear_sum_smul_expand, b.sum_repr, b.sum_repr]`. Rewrite using `[h1]`. Simplify using `only [φ, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hw]`.

Use `push_cast`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Establish `hφsum : ∀ c : Fin d → ℚ, φ (∑ i, c i • b i) = ∑ i, (c i : ℝ) • w i`. Introduce `c`.

Simplify using `only [φ, b.repr_sum_self]`. Establish `hφb : ∀ i, φ (b i) = w i`. Introduce `i`. Establish `h1 : b i = ∑ j, (Pi.single i (1 : ℚ) : Fin d → ℚ) j • b j`. Simplify using `[Pi.single_apply]`.

Rewrite using `[h1, hφsum]`. Simplify using `[Pi.single_apply, apply_ite (Rat.cast : ℚ → ℝ)]`. Establish `hsolve : ∀ n : Fin d → ℤ, ∃ x : V, ∀ i, B x (b i) = n i`. Introduce `n`. Use `⟨∑ i, (Gq⁻¹ *ᵥ (fun j => (n j : ℚ))) i • b i, fun j => ?_⟩` and prove the remaining obligations.

Establish `h1 : Gq *ᵥ (Gq⁻¹ *ᵥ (fun j => (n j : ℚ))) = fun j => (n j : ℚ)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetq), Matrix.one_mulVec]`. Establish `h2` using `congrFun h1 j`. Rewrite using `[← h2]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Use `conv_rhs => rw [Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun i _ => by` and prove the remaining obligations. Rewrite using `[hsymm (b i) (b j)]`. Simplify using `only [hGq, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hlow : ∀ y ∈ PI.dualZ M, y ≠ 0 → κ ≤ ‖y‖`. Introduce `y hy hy0`. Establish `h1 : ∀ i, ∃ z : ℤ, ⟪y, bE i⟫_ℝ = z` using `fun i => hy (bE i) (Submodule.subset_span ⟨i, rfl⟩)`. Use `choose n hn using h1`. Take `⟨x, hx⟩` from `hsolve n`.

Establish `hxy : φ x = y`. Use `InnerProductSpace.ext_inner_right_basis bE fun i => ?_` and prove the remaining obligations. Rewrite using `[hn i, hbE i, ← hφb i, hφ, hx]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Apply `hy0` to reduce the goal to its premises. Rewrite using `[← hxy]`. Simplify using `[φ]`.

Establish `h2` using `hdual x hx0 (fun i => ⟨n i, hx i⟩)`. Rewrite `h2` using `[← hφ, hxy, real_inner_self_eq_norm_sq]`. Assume the negation of the conclusion as `hc`. Establish `hc' : ‖y‖ < κ` using `not_le.mp hc`. Use polynomial arithmetic with `[norm_nonneg y]`.

Establish `hs1 : κ ≤ PI.succMin (PI.dualZ M) 1`. Unfold `PI.succMin`. Apply `le_csInf` to reduce the goal to its premises. Take `⟨x, hx⟩` from `hsolve (fun _ => 1)`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Use `hx ⟨0, hd⟩` as an intermediate fact. Simplify using `at this`. Establish `hφx0 : φ x ≠ 0`. Introduce `h`.

Establish `h1` using `hφ x x`. Rewrite `h1` using `[h, inner_zero_left]`. Establish `h2` using `hpos x hx0`. Establish `h3 : (0 : ℝ) < ((B x x : ℚ) : ℝ)` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨‖φ x‖, norm_nonneg _, fun _ => φ x, fun _ => ?_, ?_, fun _ => le_rfl⟩` and prove the remaining obligations. Introduce `y hy`. Use `Submodule.span_induction (p := fun y _ => ∃ z : ℤ, ⟪φ x, y⟫_ℝ = z) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨1, by rw [hbE, ← hφb, hφ, hx]; simp⟩`.

Conclude with `⟨0, by simp⟩`. Introduce and unpack `a c _ _ ⟨z1, h1⟩ ⟨z2, h2⟩`. Conclude with `⟨z1 + z2, by rw [inner_add_right, h1, h2]; push_cast; ring⟩`. Introduce and unpack `k a _ ⟨z, h⟩`. Conclude with `⟨k * z, by rw [← Int.cast_smul_eq_zsmul ℝ k a, real_inner_smul_right, h]; push_cast; ring⟩`.

Conclude with `linearIndependent_unique_iff.mpr hφx0`. Introduce and unpack `t ⟨_, v, hv, hvli, hvt⟩`. Conclude with `(hlow (v 0) (hv 0) (hvli.ne_zero 0)).trans (hvt 0)`. Establish `hmain` using `hT d M hdisc hspan d hd le_rfl`. Rewrite `hmain` using `[show d + 1 - d = 1 by omega]`.

Establish `hs0 : 0 ≤ PI.succMin M d` using `Real.sInf_nonneg (fun t ht => ht.1)`. Establish `hR : PI.succMin M d ≤ d / κ`. Rewrite using `[le_div_iff₀ hκ]`. Conclude with `(mul_le_mul_of_nonneg_left hs1 hs0).trans hmain`. Establish `hfin : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (d / κ + 1) ∩ (M : Set (EuclideanSpace ℝ (Fin d)))).Finite` using `ZSpan.setFinite_inter bE Metric.isBounded_closedBall`.

Take `⟨ε, hε, hgap⟩` from `exists_gap_above_finite_set _ (hfin.image norm) (d / κ)`. Establish `hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin d → EuclideanSpace ℝ (Fin d), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty` using `⟨∑ i, ‖bE i‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), bE, fun j => Submodule.subset_span ⟨j, rfl⟩, bE.linearIndependent, fun j => Finset.single_le_sum (f := fun i => ‖bE i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)⟩`. Establish `hlt : PI.succMin M d < d / κ + min ε 1`. Use `lt_min hε one_pos` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨t, ⟨_, v, hvM, hvli, hvt⟩, htlt⟩` from `exists_lt_of_csInf_lt hne hlt`. Establish `hvR : ∀ j, ‖v j‖ ≤ d / κ`. Introduce `j`. Establish `h1` using `hvt j`. Establish `h2` using `min_le_left ε 1`.

Establish `h3` using `min_le_right ε 1`. Use `hgap _ ⟨v j, ⟨?_, hvM j⟩, rfl⟩ (by linarith)` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hex : ∀ j, ∃ n : Fin d → ℤ, ∑ i, n i • bE i = v j` using `fun j => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hvM j)`.

Use `choose n hn using hex`. Establish `hφy : ∀ j, φ (∑ i, ((n j i : ℤ) : ℚ) • b i) = v j`. Introduce `j`. Rewrite using `[hφsum, ← hn j]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hbE, ← Int.cast_smul_eq_zsmul ℝ]`. Use `push_cast`. Both sides reduce to the same expression. Use `⟨fun j => ∑ i, ((n j i : ℤ) : ℚ) • b i, fun j => ?_, ?_, fun j => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun i _ => by`.

Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `q hq`. Establish `h2 : ∑ j, q j • ∑ i, ((n j i : ℤ) : ℚ) • b i = ∑ i, (∑ j, q j * (n j i : ℚ)) • b i`.

Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Rewrite `hq` using `[h2]`. Establish `h3` using `Fintype.linearIndependent_iff.mp b.linearIndependent _ hq`. Establish `h1 : ∑ j, (q j : ℝ) • v j = 0`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [← hφy, hφsum, Finset.smul_sum, smul_smul]`. Use `push_cast`. Simplify using `only [Finset.sum_smul]`. Conclude with `Finset.sum_comm`.

Use `_ = 0 := by simp [h3]`. Establish `h4` using `Fintype.linearIndependent_iff.mp hvli _ h1`. Introduce `j`. Conclude with `h4 j` after adjusting the coercions. Rewrite using `[← hφ, hφy, real_inner_self_eq_norm_sq, ← div_pow]`.

Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hvR j) 2`.
-/
theorem rational_transference_short_basis (hT : PI.TransferenceMinima) (hd : 0 < d)
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hsymm : ∀ x y, B x y = B y x) (hpos : ∀ x, x ≠ 0 → 0 < B x x)
    (b : Basis (Fin d) ℚ V) (κ : ℝ) (hκ : 0 < κ)
    (hdual : ∀ x : V, x ≠ 0 → (∀ i, ∃ z : ℤ, B x (b i) = z) → κ ^ 2 ≤ ((B x x : ℚ) : ℝ)) :
    ∃ y : Fin d → V, (∀ j, y j ∈ Submodule.span ℤ (Set.range b)) ∧ LinearIndependent ℚ y ∧
      ∀ j, ((B (y j) (y j) : ℚ) : ℝ) ≤ (d : ℝ) ^ 2 / κ ^ 2 := by
  classical
  set Gq : Matrix (Fin d) (Fin d) ℚ := Matrix.of fun i j => B (b i) (b j) with hGq
  set G : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => ((B (b i) (b j) : ℚ) : ℝ) with hG
  have hquad : ∀ c : Fin d → ℚ, c ⬝ᵥ (Gq *ᵥ c) = B (∑ i, c i • b i) (∑ i, c i • b i) := by
    intro c
    rw [bilinear_sum_smul_expand]
    simp only [dotProduct, Matrix.mulVec, hGq, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hnn : ∀ x, 0 ≤ B x x := by
    intro x
    by_cases hx : x = 0
    · rw [hx]; simp
    · exact (hpos x hx).le
  have hdetq : Gq.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 := hquad c
    rw [hc0, dotProduct_zero] at h1
    have hx : (∑ i, c i • b i) = 0 := by
      by_contra hne
      exact absurd h1 (ne_of_lt (hpos _ hne))
    exact hc (funext ((Fintype.linearIndependent_iff.mp b.linearIndependent) c hx))
  have hGmap : G = (Rat.castHom ℝ).mapMatrix Gq := by
    ext i j
    rfl
  have hdet : G.det ≠ 0 := by
    rw [hGmap, ← RingHom.map_det]
    simpa using hdetq
  have hpsd : G.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simp [hG, Matrix.conjTranspose_apply, hsymm (b j) (b i)]
    · intro x
      have hden : DenseRange (Pi.map (fun (_ : Fin d) (q : ℚ) => (q : ℝ))) :=
        DenseRange.piMap (fun _ => Rat.denseRange_cast)
      refine hden.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ (G *ᵥ x)) x ?_ ?_
      · apply isClosed_le continuous_const
        simp only [star_trivial, dotProduct, Matrix.mulVec]
        fun_prop
      · intro c
        have h1 : star (Pi.map (fun (_ : Fin d) (q : ℚ) => (q : ℝ)) c) ⬝ᵥ
            (G *ᵥ (Pi.map (fun (_ : Fin d) (q : ℚ) => (q : ℝ)) c)) = ((c ⬝ᵥ (Gq *ᵥ c) : ℚ) : ℝ) := by
          simp [dotProduct, Matrix.mulVec, hG, hGq, Pi.map]
        rw [h1, hquad]
        exact_mod_cast hnn _
  obtain ⟨A, hA⟩ := posSemidef_eq_transpose_mul G hpsd
  let w : Fin d → EuclideanSpace ℝ (Fin d) := fun i => WithLp.toLp 2 (fun r => A r i)
  have hw : ∀ i j, ⟪w i, w j⟫_ℝ = ((B (b i) (b j) : ℚ) : ℝ) := by
    intro i j
    have h1 : G i j = ∑ r, A r i * A r j := by
      rw [hA, Matrix.mul_apply]
      rfl
    have h2 : G i j = ((B (b i) (b j) : ℚ) : ℝ) := rfl
    rw [← h2, h1]
    show ⟪WithLp.toLp 2 (fun r => A r i), WithLp.toLp 2 (fun r => A r j)⟫_ℝ = _
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, mul_comm]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    have hc0 : c ≠ 0 := fun h => hne (fun i => congrFun h i)
    apply hdet
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨c, hc0, ?_⟩
    ext j
    have h1 : ⟪w j, ∑ i, c i • w i⟫_ℝ = 0 := by rw [hc, inner_zero_right]
    rw [inner_sum] at h1
    simp only [real_inner_smul_right, hw] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => by simp [hG, mul_comm]
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let bE : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hbE : ∀ i, bE i = w i := fun i => by simp [bE]
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℤ (Set.range bE)
  have hdisc : DiscreteTopology M := inferInstance
  have hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin d))) = ⊤ := by
    rw [Submodule.span_span_of_tower]
    exact bE.span_eq
  let φ : V → EuclideanSpace ℝ (Fin d) := fun x => ∑ i, ((b.repr x i : ℚ) : ℝ) • w i
  have hφ : ∀ x y, ⟪φ x, φ y⟫_ℝ = ((B x y : ℚ) : ℝ) := by
    intro x y
    have h1 : B x y = ∑ i, ∑ j, b.repr x i * b.repr y j * B (b i) (b j) := by
      rw [← bilinear_sum_smul_expand, b.sum_repr, b.sum_repr]
    rw [h1]
    simp only [φ, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hw]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hφsum : ∀ c : Fin d → ℚ, φ (∑ i, c i • b i) = ∑ i, (c i : ℝ) • w i := by
    intro c
    simp only [φ, b.repr_sum_self]
  have hφb : ∀ i, φ (b i) = w i := by
    intro i
    have h1 : b i = ∑ j, (Pi.single i (1 : ℚ) : Fin d → ℚ) j • b j := by
      simp [Pi.single_apply]
    rw [h1, hφsum]
    simp [Pi.single_apply, apply_ite (Rat.cast : ℚ → ℝ)]
  have hsolve : ∀ n : Fin d → ℤ, ∃ x : V, ∀ i, B x (b i) = n i := by
    intro n
    refine ⟨∑ i, (Gq⁻¹ *ᵥ (fun j => (n j : ℚ))) i • b i, fun j => ?_⟩
    have h1 : Gq *ᵥ (Gq⁻¹ *ᵥ (fun j => (n j : ℚ))) = fun j => (n j : ℚ) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetq), Matrix.one_mulVec]
    have h2 := congrFun h1 j
    rw [← h2]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    conv_rhs => rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => by
      rw [hsymm (b i) (b j)]
      simp only [hGq, Matrix.of_apply]
      ring
  have hlow : ∀ y ∈ PI.dualZ M, y ≠ 0 → κ ≤ ‖y‖ := by
    intro y hy hy0
    have h1 : ∀ i, ∃ z : ℤ, ⟪y, bE i⟫_ℝ = z := fun i => hy (bE i) (Submodule.subset_span ⟨i, rfl⟩)
    choose n hn using h1
    obtain ⟨x, hx⟩ := hsolve n
    have hxy : φ x = y := by
      refine InnerProductSpace.ext_inner_right_basis bE fun i => ?_
      rw [hn i, hbE i, ← hφb i, hφ, hx]
      push_cast
      rfl
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hy0
      rw [← hxy]
      simp [φ]
    have h2 := hdual x hx0 (fun i => ⟨n i, hx i⟩)
    rw [← hφ, hxy, real_inner_self_eq_norm_sq] at h2
    by_contra hc
    have hc' : ‖y‖ < κ := not_le.mp hc
    nlinarith [norm_nonneg y]
  have hs1 : κ ≤ PI.succMin (PI.dualZ M) 1 := by
    unfold PI.succMin
    apply le_csInf
    · obtain ⟨x, hx⟩ := hsolve (fun _ => 1)
      have hx0 : x ≠ 0 := by
        rintro rfl
        have := hx ⟨0, hd⟩
        simp at this
      have hφx0 : φ x ≠ 0 := by
        intro h
        have h1 := hφ x x
        rw [h, inner_zero_left] at h1
        have h2 := hpos x hx0
        have h3 : (0 : ℝ) < ((B x x : ℚ) : ℝ) := by exact_mod_cast h2
        linarith
      refine ⟨‖φ x‖, norm_nonneg _, fun _ => φ x, fun _ => ?_, ?_, fun _ => le_rfl⟩
      · intro y hy
        refine Submodule.span_induction (p := fun y _ => ∃ z : ℤ, ⟪φ x, y⟫_ℝ = z) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨i, rfl⟩
          exact ⟨1, by rw [hbE, ← hφb, hφ, hx]; simp⟩
        · exact ⟨0, by simp⟩
        · rintro a c _ _ ⟨z1, h1⟩ ⟨z2, h2⟩
          exact ⟨z1 + z2, by rw [inner_add_right, h1, h2]; push_cast; ring⟩
        · rintro k a _ ⟨z, h⟩
          exact ⟨k * z, by rw [← Int.cast_smul_eq_zsmul ℝ k a, real_inner_smul_right, h]; push_cast; ring⟩
      · exact linearIndependent_unique_iff.mpr hφx0
    · rintro t ⟨_, v, hv, hvli, hvt⟩
      exact (hlow (v 0) (hv 0) (hvli.ne_zero 0)).trans (hvt 0)
  have hmain := hT d M hdisc hspan d hd le_rfl
  rw [show d + 1 - d = 1 by omega] at hmain
  have hs0 : 0 ≤ PI.succMin M d := Real.sInf_nonneg (fun t ht => ht.1)
  have hR : PI.succMin M d ≤ d / κ := by
    rw [le_div_iff₀ hκ]
    exact (mul_le_mul_of_nonneg_left hs1 hs0).trans hmain
  have hfin : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (d / κ + 1) ∩
      (M : Set (EuclideanSpace ℝ (Fin d)))).Finite := ZSpan.setFinite_inter bE Metric.isBounded_closedBall
  obtain ⟨ε, hε, hgap⟩ := exists_gap_above_finite_set _ (hfin.image norm) (d / κ)
  have hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin d → EuclideanSpace ℝ (Fin d),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty :=
    ⟨∑ i, ‖bE i‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), bE,
      fun j => Submodule.subset_span ⟨j, rfl⟩, bE.linearIndependent,
      fun j => Finset.single_le_sum (f := fun i => ‖bE i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)⟩
  have hlt : PI.succMin M d < d / κ + min ε 1 := by
    have := lt_min hε one_pos
    linarith
  obtain ⟨t, ⟨_, v, hvM, hvli, hvt⟩, htlt⟩ := exists_lt_of_csInf_lt hne hlt
  have hvR : ∀ j, ‖v j‖ ≤ d / κ := by
    intro j
    have h1 := hvt j
    have h2 := min_le_left ε 1
    have h3 := min_le_right ε 1
    refine hgap _ ⟨v j, ⟨?_, hvM j⟩, rfl⟩ (by linarith)
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hex : ∀ j, ∃ n : Fin d → ℤ, ∑ i, n i • bE i = v j :=
    fun j => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hvM j)
  choose n hn using hex
  have hφy : ∀ j, φ (∑ i, ((n j i : ℤ) : ℚ) • b i) = v j := by
    intro j
    rw [hφsum, ← hn j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbE, ← Int.cast_smul_eq_zsmul ℝ]
    push_cast
    rfl
  refine ⟨fun j => ∑ i, ((n j i : ℤ) : ℚ) • b i, fun j => ?_, ?_, fun j => ?_⟩
  · exact Submodule.sum_mem _ fun i _ => by
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Fintype.linearIndependent_iff]
    intro q hq
    have h2 : ∑ j, q j • ∑ i, ((n j i : ℤ) : ℚ) • b i = ∑ i, (∑ j, q j * (n j i : ℚ)) • b i := by
      simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    rw [h2] at hq
    have h3 := Fintype.linearIndependent_iff.mp b.linearIndependent _ hq
    have h1 : ∑ j, (q j : ℝ) • v j = 0 := by
      calc ∑ j, (q j : ℝ) • v j = ∑ i, ((∑ j, q j * (n j i : ℚ) : ℚ) : ℝ) • w i := by
            simp only [← hφy, hφsum, Finset.smul_sum, smul_smul]
            push_cast
            simp only [Finset.sum_smul]
            exact Finset.sum_comm
        _ = 0 := by simp [h3]
    have h4 := Fintype.linearIndependent_iff.mp hvli _ h1
    intro j
    exact_mod_cast h4 j
  · rw [← hφ, hφy, real_inner_self_eq_norm_sq, ← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hvR j) 2

end RatTrans

section Arith

open Module NumberField
open scoped nonZeroDivisors

variable (E : Type*) [Field E] [NumberField E]

/- English proof (translation)
Use `set dd : FractionalIdeal (𝓞 E)⁰ E := ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) with hdd`. Establish `hdual0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero`. Establish `hinv : dd = (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹` using `coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)`. Establish `hdd0 : dd ≠ 0`. Rewrite using `[hinv]`.

Conclude with `inv_ne_zero hdual0`. Establish `h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * dd ≤ FractionalIdeal.dual ℤ ℚ 1`. Rewrite using `[FractionalIdeal.mul_le]`. Introduce `i hi j hj`. Take `⟨z, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).mp hi`.

Take `⟨δ, hδ, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hj`. Establish `h2` using `h δ hδ`. Establish `e : z • β * algebraMap (𝓞 E) E δ = z • (algebraMap (𝓞 E) E δ * β)`. Rewrite using `[smul_mul_assoc, mul_comm]`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ z h2`. Establish `h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * dd * dd ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨I', hI'⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.mp h2`. Establish `hne : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * dd * dd ≠ 0` using `mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ) hdd0) hdd0`.

Establish `hI0 : I' ≠ ⊥`. Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hI']`. Simplify using the standard rewrite rules.

Establish `hn` using `congrArg FractionalIdeal.absNorm hI'`. Rewrite `hn` using `[FractionalIdeal.coeIdeal_absNorm, map_mul, map_mul, FractionalIdeal.absNorm_span_singleton, hdd, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E]`. Establish `h3 : 1 ≤ Ideal.absNorm I'` using `Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`. Establish `h4 : (1 : ℚ) ≤ (Ideal.absNorm I' : ℚ)` using `by exact_mod_cast h3`. Rewrite `h4` using `[hn]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_norm_mul_discr_sq (β : E) (hβ : β ≠ 0)
    (h : ∀ δ ∈ differentIdeal ℤ (𝓞 E),
      algebraMap (𝓞 E) E δ * β ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    (1 : ℚ) ≤ |Algebra.norm ℚ β| * ((discr E).natAbs : ℚ) ^ 2 := by
  set dd : FractionalIdeal (𝓞 E)⁰ E := ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) with hdd
  have hdual0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hinv : dd = (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  have hdd0 : dd ≠ 0 := by
    rw [hinv]
    exact inv_ne_zero hdual0
  have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * dd ≤ FractionalIdeal.dual ℤ ℚ 1 := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hi
    obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hj
    have h2 := h δ hδ
    have e : z • β * algebraMap (𝓞 E) E δ = z • (algebraMap (𝓞 E) E δ * β) := by
      rw [smul_mul_assoc, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ z h2
  have h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * dd * dd ≤ 1 := by
    calc FractionalIdeal.spanSingleton (𝓞 E)⁰ β * dd * dd
        ≤ FractionalIdeal.dual ℤ ℚ 1 * dd := mul_le_mul_left h1 dd
      _ = 1 := by rw [hinv, mul_inv_cancel₀ hdual0]
  obtain ⟨I', hI'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp h2
  have hne : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * dd * dd ≠ 0 :=
    mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ) hdd0) hdd0
  have hI0 : I' ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [← hI']
    simp
  have hn := congrArg FractionalIdeal.absNorm hI'
  rw [FractionalIdeal.coeIdeal_absNorm, map_mul, map_mul, FractionalIdeal.absNorm_span_singleton, hdd,
    FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E] at hn
  have h3 : 1 ≤ Ideal.absNorm I' := Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have h4 : (1 : ℚ) ≤ (Ideal.absNorm I' : ℚ) := by exact_mod_cast h3
  rw [hn] at h4
  calc (1 : ℚ) ≤ _ := h4
    _ = _ := by ring

/- English proof (translation)
Use `choose c hc0 hc using fun σ : E →ₐ[ℚ] ℂ => hpos σ.toRingHom`. Establish `hc' : ∀ σ : E →ₐ[ℚ] ℂ, σ β = (c σ : ℂ)` using `hc`. Establish `hT : ((Algebra.trace ℚ E β : ℚ) : ℝ) = ∑ σ, c σ`. Establish `h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ E β) = ∑ σ : E →ₐ[ℚ] ℂ, σ β` using `trace_eq_sum_embeddings ℂ`. Simplify using `only [hc', eq_ratCast] at h1`.

Establish `h2 : (((Algebra.trace ℚ E β : ℚ) : ℝ) : ℂ) = ((∑ σ, c σ : ℝ) : ℂ)`. Use `push_cast`. Conclude with `h1`. Conclude with `h2` after adjusting the coercions. Establish `hNm : ((Algebra.norm ℚ β : ℚ) : ℝ) = ∏ σ, c σ`.

Establish `h1 : (algebraMap ℚ ℂ) (Algebra.norm ℚ β) = ∏ σ : E →ₐ[ℚ] ℂ, σ β` using `Algebra.norm_eq_prod_embeddings ℚ ℂ β`. Simplify using `only [hc', eq_ratCast] at h1`. Establish `h2 : (((Algebra.norm ℚ β : ℚ) : ℝ) : ℂ) = ((∏ σ, c σ : ℝ) : ℂ)`. Use `push_cast`. Conclude with `h1`.

Conclude with `h2` after adjusting the coercions. Use `set P : ℝ := ∏ σ, c σ with hP`. Establish `hP0 : 0 < P` using `Finset.prod_pos fun σ _ => hc0 σ`. Use `set n : ℝ := (finrank ℚ E : ℝ) with hn`. Establish `hn0 : 0 < n`.

Rewrite using `[hn]`. Conclude with `finrank_pos` after adjusting the coercions. Use `set Dd : ℝ := |(discr E : ℝ)| with hDd`. Establish `hDd0 : 0 ≤ Dd` using `abs_nonneg _`. Establish `hN' : 1 ≤ P * Dd ^ 2`.

Establish `h1 : ((1 : ℚ) : ℝ) ≤ ((|Algebra.norm ℚ β| * ((discr E).natAbs : ℚ) ^ 2 : ℚ) : ℝ)` using `by exact_mod_cast hN`. Move the coercions through the operations in `at h1`. Rewrite `h1` using `[hNm, abs_of_pos hP0]`. Establish `h2 : (((discr E).natAbs : ℕ) : ℝ) = Dd`. Rewrite using `[hDd, Nat.cast_natAbs]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Establish `hcard : (∑ _σ : E →ₐ[ℚ] ℂ, (1 : ℝ)) = n`. Simplify using `[hn, AlgHom.card ℚ E ℂ]`.

Establish `hAG` using `Real.geom_mean_le_arith_mean (Finset.univ : Finset (E →ₐ[ℚ] ℂ)) (fun _ => 1) c (fun _ _ => zero_le_one) (by rw [hcard]; exact hn0) (fun σ _ => (hc0 σ).le)`. Simplify using `only [Real.rpow_one, one_mul, hcard] at hAG`. Rewrite `hAG` using `[← hP, ← hT]`. Use `set r : ℝ := Dd ^ ((1 : ℝ) / n) with hr`. Establish `hr0 : 0 ≤ r` using `Real.rpow_nonneg hDd0 _`.

Establish `hr2 : r ^ 2 = (Dd ^ 2) ^ (n⁻¹)`. Rewrite using `[hr, one_div, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hDd0, ← Real.rpow_mul hDd0, mul_comm]`. Establish `h5 : 1 ≤ P ^ (n⁻¹) * r ^ 2`. Rewrite using `[hr2, ← Real.mul_rpow hP0.le (by positivity)]`. Conclude with `Real.one_le_rpow hN' (inv_nonneg.mpr hn0.le)`.

Establish `hr20 : 0 < r ^ 2`. Assume the negation of the conclusion as `hc`. Establish `: r ^ 2 = 0` using `le_antisymm (not_lt.mp hc) (by positivity)`. Rewrite `h5` using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[div_le_iff₀ hr20]`. Rewrite `hAG` using `[le_div_iff₀ hn0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem totally_positive_trace_ge_of_norm_discr (β : E) (hpos : ∀ τ : E →+* ℂ, ∃ c : ℝ, 0 < c ∧ τ β = c)
    (hN : (1 : ℚ) ≤ |Algebra.norm ℚ β| * ((discr E).natAbs : ℚ) ^ 2) :
    (finrank ℚ E : ℝ) / (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2 ≤
      ((Algebra.trace ℚ E β : ℚ) : ℝ) := by
  classical
  choose c hc0 hc using fun σ : E →ₐ[ℚ] ℂ => hpos σ.toRingHom
  have hc' : ∀ σ : E →ₐ[ℚ] ℂ, σ β = (c σ : ℂ) := hc
  have hT : ((Algebra.trace ℚ E β : ℚ) : ℝ) = ∑ σ, c σ := by
    have h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ E β) = ∑ σ : E →ₐ[ℚ] ℂ, σ β := trace_eq_sum_embeddings ℂ
    simp only [hc', eq_ratCast] at h1
    have h2 : (((Algebra.trace ℚ E β : ℚ) : ℝ) : ℂ) = ((∑ σ, c σ : ℝ) : ℂ) := by
      push_cast
      exact h1
    exact_mod_cast h2
  have hNm : ((Algebra.norm ℚ β : ℚ) : ℝ) = ∏ σ, c σ := by
    have h1 : (algebraMap ℚ ℂ) (Algebra.norm ℚ β) = ∏ σ : E →ₐ[ℚ] ℂ, σ β := Algebra.norm_eq_prod_embeddings ℚ ℂ β
    simp only [hc', eq_ratCast] at h1
    have h2 : (((Algebra.norm ℚ β : ℚ) : ℝ) : ℂ) = ((∏ σ, c σ : ℝ) : ℂ) := by
      push_cast
      exact h1
    exact_mod_cast h2
  set P : ℝ := ∏ σ, c σ with hP
  have hP0 : 0 < P := Finset.prod_pos fun σ _ => hc0 σ
  set n : ℝ := (finrank ℚ E : ℝ) with hn
  have hn0 : 0 < n := by
    rw [hn]
    exact_mod_cast finrank_pos
  set Dd : ℝ := |(discr E : ℝ)| with hDd
  have hDd0 : 0 ≤ Dd := abs_nonneg _
  have hN' : 1 ≤ P * Dd ^ 2 := by
    have h1 : ((1 : ℚ) : ℝ) ≤ ((|Algebra.norm ℚ β| * ((discr E).natAbs : ℚ) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hN
    push_cast at h1
    rw [hNm, abs_of_pos hP0] at h1
    have h2 : (((discr E).natAbs : ℕ) : ℝ) = Dd := by
      rw [hDd, Nat.cast_natAbs]
      push_cast
      rfl
    rwa [h2] at h1
  have hcard : (∑ _σ : E →ₐ[ℚ] ℂ, (1 : ℝ)) = n := by
    simp [hn, AlgHom.card ℚ E ℂ]
  have hAG := Real.geom_mean_le_arith_mean (Finset.univ : Finset (E →ₐ[ℚ] ℂ)) (fun _ => 1) c
    (fun _ _ => zero_le_one) (by rw [hcard]; exact hn0) (fun σ _ => (hc0 σ).le)
  simp only [Real.rpow_one, one_mul, hcard] at hAG
  rw [← hP, ← hT] at hAG
  set r : ℝ := Dd ^ ((1 : ℝ) / n) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hDd0 _
  have hr2 : r ^ 2 = (Dd ^ 2) ^ (n⁻¹) := by
    rw [hr, one_div, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hDd0, ← Real.rpow_mul hDd0, mul_comm]
  have h5 : 1 ≤ P ^ (n⁻¹) * r ^ 2 := by
    rw [hr2, ← Real.mul_rpow hP0.le (by positivity)]
    exact Real.one_le_rpow hN' (inv_nonneg.mpr hn0.le)
  have hr20 : 0 < r ^ 2 := by
    by_contra hc
    have : r ^ 2 = 0 := le_antisymm (not_lt.mp hc) (by positivity)
    rw [this] at h5
    linarith
  rw [div_le_iff₀ hr20]
  rw [le_div_iff₀ hn0] at hAG
  calc n = 1 * n := (one_mul n).symm
    _ ≤ P ^ (n⁻¹) * r ^ 2 * n := mul_le_mul_of_nonneg_right h5 hn0.le
    _ = P ^ (n⁻¹) * n * r ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hAG hr20.le

end Arith

section LemT

open Module NumberField Formalism.BasicNotions
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Take `⟨o, rfl⟩` from `ha`. Establish `h1 : IsIntegral ℤ (algebraMap (𝓞 E) E o)` using `RingOfIntegers.isIntegral_coe o`. Establish `h2 : IsIntegral ℤ ((starRingEnd E) (algebraMap (𝓞 E) E o))` using `map_isIntegral_int (starRingEnd E) h1`. Conclude with `(IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp h2`.
-/
theorem star_mem_ring_of_integers (a : E) (ha : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨o, rfl⟩ := ha
  have h1 : IsIntegral ℤ (algebraMap (𝓞 E) E o) := RingOfIntegers.isIntegral_coe o
  have h2 : IsIntegral ℤ ((starRingEnd E) (algebraMap (𝓞 E) E o)) := map_isIntegral_int (starRingEnd E) h1
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp h2

/- English proof (translation)
The claim follows from `Algebra.trace_eq_of_algEquiv (starRingAut : E ≃+* E).toRatAlgEquiv a`.
-/
theorem trace_star_eq_trace (a : E) : Algebra.trace ℚ E (star a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv (starRingAut : E ≃+* E).toRatAlgEquiv a

/- English proof (translation)
Rewrite `hz`, the goal using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]`. Introduce `a ha`. Establish `ha' : star a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)` using `(FractionalIdeal.mem_one_iff _).mpr (star_mem_ring_of_integers a ((FractionalIdeal.mem_one_iff _).mp ha))`. Establish `h1` using `hz (star a) ha'`. Rewrite `h1`, the goal using `[Algebra.traceForm_apply]`.

Rewrite `h1` using `[← trace_star_eq_trace, star_mul, star_star]`. Rewrite `h1` using `[mul_comm]`. Then use the resulting hypothesis.
-/
theorem star_mem_inverseDifferent (z : E) (hz : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    star z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)] at hz ⊢
  intro a ha
  have ha' : star a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
    (FractionalIdeal.mem_one_iff _).mpr (star_mem_ring_of_integers a ((FractionalIdeal.mem_one_iff _).mp ha))
  have h1 := hz (star a) ha'
  rw [Algebra.traceForm_apply] at h1 ⊢
  rw [← trace_star_eq_trace, star_mul, star_star] at h1
  rwa [mul_comm] at h1

/- English proof (translation)
Establish `hdual0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero`. Establish `h1 : algebraMap (𝓞 E) E δ * z ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * FractionalIdeal.dual ℤ ℚ 1` using `FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).mpr ⟨δ, hδ, rfl⟩) hz`. Rewrite `h1` using `[coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_mul_cancel₀ hdual0]`. Conclude with `(FractionalIdeal.mem_one_iff _).mp h1`.
-/
theorem different_mul_dual_mem_range (δ : 𝓞 E) (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) (z : E)
    (hz : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    algebraMap (𝓞 E) E δ * z ∈ (algebraMap (𝓞 E) E).range := by
  have hdual0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have h1 : algebraMap (𝓞 E) E δ * z ∈
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * FractionalIdeal.dual ℤ ℚ 1 :=
    FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).mpr ⟨δ, hδ, rfl⟩) hz
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_mul_cancel₀ hdual0] at h1
  exact (FractionalIdeal.mem_one_iff _).mp h1

/- English proof (translation)
Introduce `l hl`. Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `mul_mem ⟨o, rfl⟩ (hy l hl)`.
-/
theorem dualLattice_smul_mem (S : HSpace E) (L : Submodule (𝓞 E) S.V) (o : 𝓞 E) (y : S.V) (hy : y ∈ dualSub S L) :
    (algebraMap (𝓞 E) E o) • y ∈ dualSub S L := by
  intro l hl
  rw [map_smul, smul_eq_mul]
  exact mul_mem ⟨o, rfl⟩ (hy l hl)

/- English proof (translation)
Establish `hD : ∀ y ∈ dualSub S L, S.hT x y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)`. Introduce `y hy`. Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]`. Introduce `a ha`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`.

Take `⟨z, hz⟩` from `hd _ (dualLattice_smul_mem S L o y hy)`. Rewrite using `[Algebra.traceForm_apply]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[map_smul, smul_eq_mul, mul_comm]`. Rewrite using `[hz]`.

Simplify using the standard rewrite rules. Establish `hβ0 : S.hT x x ≠ 0`. Introduce `h0`. Take `⟨c, hc0, hc⟩` from `hpos (Classical.arbitrary (E →+* ℂ)) x hx`. Rewrite `hc` using `[h0, map_zero]`.

Establish `: c = 0` using `by exact_mod_cast hc.symm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hreal : star (S.hT x x) = S.hT x x` using `S.herm.eq x x`. Apply `totally_positive_trace_ge_of_norm_discr E _ (fun τ => hpos τ x hx)` to reduce the goal to its premises. Apply `one_le_norm_mul_discr_sq E _ hβ0` to reduce the goal to its premises.

Introduce `δ hδ`. Establish `hx1 : ∀ y ∈ dualSub S L, S.hT (star (algebraMap (𝓞 E) E δ) • x) y ∈ (algebraMap (𝓞 E) E).range`. Introduce `y hy`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]`. Conclude with `different_mul_dual_mem_range δ hδ _ (hD y hy)`.

Establish `hx2 : star (algebraMap (𝓞 E) E δ) • x ∈ dualSub S L`. Introduce `l hl`. Rewrite using `[← S.herm.eq]`. Conclude with `star_mem_ring_of_integers _ (hx1 l (hint l hl))`. Establish `h3` using `star_mem_inverseDifferent _ (hD _ hx2)`.

Rewrite `h3` using `[map_smul, smul_eq_mul, star_mul, star_star, hreal, mul_comm]`. Then use the resulting hypothesis.
-/
theorem trace_form_lower_bound_dual (S : HSpace E)
    (hpos : ∀ (τ : E →+* ℂ) (x : S.V), x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ))
    (L : Submodule (𝓞 E) S.V) (hint : ∀ x ∈ L, x ∈ dualSub S L) (x : S.V) (hx : x ≠ 0)
    (hd : ∀ y ∈ dualSub S L, ∃ z : ℤ, Algebra.trace ℚ E (S.hT x y) = z) :
    (finrank ℚ E : ℝ) / (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2 ≤
      ((Algebra.trace ℚ E (S.hT x x) : ℚ) : ℝ) := by
  have hD : ∀ y ∈ dualSub S L, S.hT x y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro y hy
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨z, hz⟩ := hd _ (dualLattice_smul_mem S L o y hy)
    rw [Algebra.traceForm_apply]
    refine ⟨z, ?_⟩
    rw [map_smul, smul_eq_mul, mul_comm] at hz
    rw [hz]
    simp
  have hβ0 : S.hT x x ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := hpos (Classical.arbitrary (E →+* ℂ)) x hx
    rw [h0, map_zero] at hc
    have : c = 0 := by exact_mod_cast hc.symm
    linarith
  have hreal : star (S.hT x x) = S.hT x x := S.herm.eq x x
  apply totally_positive_trace_ge_of_norm_discr E _ (fun τ => hpos τ x hx)
  apply one_le_norm_mul_discr_sq E _ hβ0
  intro δ hδ
  have hx1 : ∀ y ∈ dualSub S L, S.hT (star (algebraMap (𝓞 E) E δ) • x) y ∈ (algebraMap (𝓞 E) E).range := by
    intro y hy
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
    exact different_mul_dual_mem_range δ hδ _ (hD y hy)
  have hx2 : star (algebraMap (𝓞 E) E δ) • x ∈ dualSub S L := by
    intro l hl
    rw [← S.herm.eq]
    exact star_mem_ring_of_integers _ (hx1 l (hint l hl))
  have h3 := star_mem_inverseDifferent _ (hD _ hx2)
  rwa [map_smul, smul_eq_mul, star_mul, star_star, hreal, mul_comm] at h3

/- English proof (translation)
Take `⟨s, hs⟩` from `hL.fg`. Establish `hsE : Submodule.span E (s : Set S.V) = ⊤`. Rewrite using `[← Submodule.span_span_of_tower (𝓞 E) E, hs]`. Conclude with `hL.span_eq_top`. Set `Θ : S.V →ₗ[ℤ] (s → E)` to `LinearMap.pi fun l => (S.hT l.1).toAddMonoidHom.toIntLinearMap`.

Establish `hΘ : Function.Injective Θ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Apply `S.nondeg.2 y` to reduce the goal to its premises. Introduce `v`.

Establish `hv : v ∈ Submodule.span E (s : Set S.V)` using `by rw [hsE]; trivial`. Use `Submodule.span_induction (p := fun v _ => S.hT v y = 0) ?_ ?_ ?_ ?_ hv` and prove the remaining obligations. Introduce `l hl`. Conclude with `congrFun hy ⟨l, hl⟩`. Simplify using the standard rewrite rules.

Introduce `a c _ _ ha hc`. Rewrite using `[map_add, LinearMap.add_apply, ha, hc, add_zero]`. Introduce `e a _ ha`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]`. Apply `Submodule.fg_of_fg_map_injective Θ hΘ` to reduce the goal to its premises.

Set `P : Submodule ℤ (s → E)` to `LinearMap.range (((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ).compLeft s)`. Establish `hP : P.FG` using `Module.Finite.iff_fg.mp inferInstance`. Use `hP.of_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `h1 : ∀ l : s, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT l.1 y` using `fun l => hy l.1 (by rw [← hs]; exact Submodule.subset_span l.2)`.

Use `choose o ho using h1`. Conclude with `⟨o, funext fun l => ho l⟩`.
-/
theorem dualSub_toIntSubmodule_fg_of_isLattice (S : HSpace E) (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) :
    (AddSubgroup.toIntSubmodule (dualSub S L)).FG := by
  classical
  obtain ⟨s, hs⟩ := hL.fg
  have hsE : Submodule.span E (s : Set S.V) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 E) E, hs]
    exact hL.span_eq_top
  let Θ : S.V →ₗ[ℤ] (s → E) := LinearMap.pi fun l => (S.hT l.1).toAddMonoidHom.toIntLinearMap
  have hΘ : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply S.nondeg.2 y
    intro v
    have hv : v ∈ Submodule.span E (s : Set S.V) := by rw [hsE]; trivial
    refine Submodule.span_induction (p := fun v _ => S.hT v y = 0) ?_ ?_ ?_ ?_ hv
    · intro l hl
      exact congrFun hy ⟨l, hl⟩
    · simp
    · intro a c _ _ ha hc
      rw [map_add, LinearMap.add_apply, ha, hc, add_zero]
    · intro e a _ ha
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]
  apply Submodule.fg_of_fg_map_injective Θ hΘ
  let P : Submodule ℤ (s → E) := LinearMap.range (((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ).compLeft s)
  have hP : P.FG := Module.Finite.iff_fg.mp inferInstance
  refine hP.of_le ?_
  rintro _ ⟨y, hy, rfl⟩
  have h1 : ∀ l : s, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT l.1 y := fun l =>
    hy l.1 (by rw [← hs]; exact Submodule.subset_span l.2)
  choose o ho using h1
  exact ⟨o, funext fun l => ho l⟩

end LemT

section LemT2

open Module NumberField Formalism.BasicNotions
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Use `choose c hc0 hc using fun σ : E →ₐ[ℚ] ℂ => hpos σ.toRingHom`. Establish `hc' : ∀ σ : E →ₐ[ℚ] ℂ, σ β = (c σ : ℂ)` using `hc`. Establish `hT : ((Algebra.trace ℚ E β : ℚ) : ℝ) = ∑ σ, c σ`. Establish `h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ E β) = ∑ σ : E →ₐ[ℚ] ℂ, σ β` using `trace_eq_sum_embeddings ℂ`. Simplify using `only [hc', eq_ratCast] at h1`.

Establish `h2 : (((Algebra.trace ℚ E β : ℚ) : ℝ) : ℂ) = ((∑ σ, c σ : ℝ) : ℂ)`. Use `push_cast`. Conclude with `h1`. Conclude with `h2` after adjusting the coercions. Establish `hnE : Nonempty (E →ₐ[ℚ] ℂ)` using `Fintype.card_pos_iff.mp (by rw [AlgHom.card ℚ E ℂ]; exact finrank_pos)`.

Establish `hne : (Finset.univ : Finset (E →ₐ[ℚ] ℂ)).Nonempty` using `Finset.univ_nonempty`. Establish `h3 : (0 : ℝ) < ((Algebra.trace ℚ E β : ℚ) : ℝ)`. Rewrite using `[hT]`. Conclude with `Finset.sum_pos (fun σ _ => hc0 σ) hne`. Conclude with `h3` after adjusting the coercions.
-/
theorem trace_pos_of_totally_positive (β : E) (hpos : ∀ τ : E →+* ℂ, ∃ c : ℝ, 0 < c ∧ τ β = c) :
    0 < Algebra.trace ℚ E β := by
  classical
  choose c hc0 hc using fun σ : E →ₐ[ℚ] ℂ => hpos σ.toRingHom
  have hc' : ∀ σ : E →ₐ[ℚ] ℂ, σ β = (c σ : ℂ) := hc
  have hT : ((Algebra.trace ℚ E β : ℚ) : ℝ) = ∑ σ, c σ := by
    have h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ E β) = ∑ σ : E →ₐ[ℚ] ℂ, σ β := trace_eq_sum_embeddings ℂ
    simp only [hc', eq_ratCast] at h1
    have h2 : (((Algebra.trace ℚ E β : ℚ) : ℝ) : ℂ) = ((∑ σ, c σ : ℝ) : ℂ) := by
      push_cast
      exact h1
    exact_mod_cast h2
  have hnE : Nonempty (E →ₐ[ℚ] ℂ) := Fintype.card_pos_iff.mp (by rw [AlgHom.card ℚ E ℂ]; exact finrank_pos)
  have hne : (Finset.univ : Finset (E →ₐ[ℚ] ℂ)).Nonempty := Finset.univ_nonempty
  have h3 : (0 : ℝ) < ((Algebra.trace ℚ E β : ℚ) : ℝ) := by
    rw [hT]
    exact Finset.sum_pos (fun σ _ => hc0 σ) hne
  exact_mod_cast h3

/- English proof (translation)
Set `_ : Module ℚ S.V` to `Module.compHom S.V (algebraMap ℚ E)`. Establish `hsm : ∀ (q : ℚ) (v : S.V), q • v = (algebraMap ℚ E q) • v` using `fun _ _ => rfl`. Establish `: IsScalarTower ℚ E S.V` using `⟨fun q e v => by rw [hsm, Algebra.smul_def, mul_smul]⟩`. Set `B : S.V →ₗ[ℚ] S.V →ₗ[ℚ] ℚ` to `LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (S.hT x y)) (fun x x' y => by simp only [map_add, LinearMap.add_apply]) (fun q x y => by`. Rewrite using `[hsm, LinearMap.map_smulₛₗ, LinearMap.smul_apply, eq_ratCast, map_ratCast, smul_eq_mul, ← Rat.smul_def, map_smul])`.

Use the proof step `(fun x y y' => by simp only [map_add])`. Use the proof step `(fun q x y => by`. Rewrite using `[hsm, map_smul, eq_ratCast, smul_eq_mul, ← Rat.smul_def, map_smul])`. Establish `hB : ∀ x y, B x y = Algebra.trace ℚ E (S.hT x y)` using `fun _ _ => rfl`. Establish `hsymm : ∀ x y, B x y = B y x`.

Introduce `x y`. Rewrite using `[hB, hB, ← S.herm.eq x y]`. Conclude with `(trace_star_eq_trace _).symm`. Establish `hposB : ∀ x, x ≠ 0 → 0 < B x x` using `fun x hx => trace_pos_of_totally_positive _ (fun τ => hpos τ x hx)`. Set `Y : Submodule ℤ S.V` to `AddSubgroup.toIntSubmodule Y0`.

Establish `hspanL : Submodule.span ℚ (L : Set S.V) = ⊤`. Establish `hcl : ∀ (e : E) (v : S.V), v ∈ Submodule.span ℚ (L : Set S.V) → e • v ∈ Submodule.span ℚ (L : Set S.V)`. Introduce `e v hv`. Use `Submodule.span_induction (p := fun v _ => e • v ∈ Submodule.span ℚ (L : Set S.V)) ?_ ?_ ?_ ?_ hv` and prove the remaining obligations. Introduce `l hl`.

Rewrite using `[← (integralBasis E).sum_repr e, Finset.sum_smul]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Rewrite using `[integralBasis_apply, algebraMap_smul]`.

Conclude with `L.smul_mem _ hl`. Simplify using the standard rewrite rules. Introduce `a c _ _ ha hc`. Rewrite using `[smul_add]`. Conclude with `add_mem ha hc`.

Introduce `q a _ ha`. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ _ ha`. Rewrite using `[eq_top_iff]`. Introduce `v _`.

Establish `hv : v ∈ Submodule.span E (L : Set S.V)` using `by rw [hL.span_eq_top]; trivial`. Use `Submodule.span_induction (p := fun v _ => v ∈ Submodule.span ℚ (L : Set S.V)) ?_ ?_ ?_ ?_ hv` and prove the remaining obligations. Conclude with `fun l hl => Submodule.subset_span hl`. Conclude with `zero_mem _`. Conclude with `fun a c _ _ ha hc => add_mem ha hc`.

Conclude with `fun e a _ ha => hcl e a ha`. Establish `hYlat : Submodule.IsLattice ℚ Y` using `⟨hfg, top_le_iff.mp (hspanL ▸ Submodule.span_mono (fun l hl => hint l hl))⟩`. Set `b0 : Basis (Fin (finrank ℤ Y)) ℤ Y` to `Module.finBasis ℤ Y`. Set `b : Basis (Fin (finrank ℤ Y)) ℚ S.V` to `b0.extendOfIsLattice ℚ`. Establish `hb : ∀ i, b i = (b0 i).val` using `fun i => Basis.extendOfIsLattice_apply ℚ b0 i`.

Establish `hdV : finrank ℚ S.V = finrank ℤ Y`. Rewrite using `[finrank_eq_card_basis b]`. Simplify using the standard rewrite rules. Establish `hd : finrank ℤ Y = finrank ℚ E * S.rank`. Rewrite using `[← hdV, ← S.rank_eq, finrank_mul_finrank]`.

Establish `hbY : Submodule.span ℤ (Set.range b) = Y`. Establish `h1 : (b : Fin (finrank ℤ Y) → S.V) = Y.subtype ∘ b0` using `funext hb`. Rewrite using `[h1, Set.range_comp, Submodule.span_image, b0.span_eq, Submodule.map_subtype_top]`. Establish `hκ2 : (Real.sqrt κ2) ^ 2 = κ2` using `Real.sq_sqrt hκ.le`. Establish `hd0 : 0 < finrank ℤ Y`.

Rewrite using `[hd]`. Conclude with `Nat.mul_pos finrank_pos hrk`. Take `⟨y, hyY, hyli, hyB⟩` from `rational_transference_short_basis hT hd0 B hsymm hposB b (Real.sqrt κ2) (Real.sqrt_pos.mpr hκ) (by`. Introduce `x hx hz`. Rewrite using `[hκ2]`.

Apply `hlow x hx` to reduce the goal to its premises. Introduce `y hy`. Establish `hy' : y ∈ Submodule.span ℤ (Set.range b)` using `by rw [hbY]; exact hy`. Use `Submodule.span_induction (p := fun y _ => ∃ z : ℤ, Algebra.trace ℚ E (S.hT x y) = z) ?_ ?_ ?_ ?_ hy'` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `hz i`. Conclude with `⟨0, by simp⟩`. Introduce and unpack `a c _ _ ⟨z1, h1⟩ ⟨z2, h2⟩`. Conclude with `⟨z1 + z2, by rw [map_add, map_add, h1, h2]; push_cast; rfl⟩`. Introduce and unpack `k a _ ⟨z, h⟩`.

Conclude with `⟨k * z, by rw [map_zsmul, map_zsmul, h]; simp⟩)`. Establish `: Module.Finite ℚ S.V` using `Module.Finite.of_basis b`. Establish `: Nonempty (Fin (finrank ℤ Y))` using `⟨⟨0, hd0⟩⟩`. Establish `hspanQ : Submodule.span ℚ (Set.range y) = ⊤` using `hyli.span_eq_top_of_card_eq_finrank (by rw [hdV]; simp)`. Establish `hspanE : Submodule.span E (Set.range y) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `h1 : v ∈ Submodule.span ℚ (Set.range y)` using `by rw [hspanQ]; trivial`. Conclude with `Submodule.span_le_restrictScalars ℚ E _ h1`. Take `⟨t, htsub, htspan, htli⟩` from `exists_linearIndependent E (Set.range y)`.

Set `bt : Basis t E S.V` to `Basis.mk htli (by rw [Subtype.range_coe, htspan, hspanE])`. Establish `hcard : Nat.card t = S.rank` using `by rw [← finrank_eq_nat_card_basis bt, S.rank_eq]`. Establish `: Finite t` using `((Set.finite_range y).subset htsub).to_subtype`. Set `e : t ≃ Fin S.rank` to `Finite.equivFinOfCardEq hcard`. Use `⟨fun a => (e.symm a).1, fun a => ?_, htli.comp _ e.symm.injective, fun a => ?_⟩` and prove the remaining obligations.

Take `⟨j, hj⟩` from `htsub (e.symm a).2`. Establish `h1` using `hyY j`. Rewrite `h1` using `[hbY, hj]`. Conclude with `h1`. Take `⟨j, hj⟩` from `htsub (e.symm a).2`.

Establish `h1` using `hyB j`. Rewrite `h1` using `[hj, hB, hκ2, hd]`. Use `h1.trans_eq ?_` and prove the remaining obligations. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem exists_short_basis_of_dual_lower (hT : PI.TransferenceMinima) (S : HSpace E)
    (hpos : ∀ (τ : E →+* ℂ) (x : S.V), x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ))
    (Y0 : AddSubgroup S.V) (hfg : (AddSubgroup.toIntSubmodule Y0).FG)
    (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (hint : ∀ x ∈ L, x ∈ Y0)
    (hrk : 0 < S.rank) (κ2 : ℝ) (hκ : 0 < κ2)
    (hlow : ∀ x : S.V, x ≠ 0 → (∀ y ∈ Y0, ∃ z : ℤ, Algebra.trace ℚ E (S.hT x y) = z) →
      κ2 ≤ ((Algebra.trace ℚ E (S.hT x x) : ℚ) : ℝ)) :
    ∃ y : Fin S.rank → S.V, (∀ a, y a ∈ Y0) ∧ LinearIndependent E y ∧
      ∀ a, ((Algebra.trace ℚ E (S.hT (y a) (y a)) : ℚ) : ℝ) ≤
        ((finrank ℚ E : ℝ) * (S.rank : ℝ)) ^ 2 / κ2 := by
  classical
  let _ : Module ℚ S.V := Module.compHom S.V (algebraMap ℚ E)
  have hsm : ∀ (q : ℚ) (v : S.V), q • v = (algebraMap ℚ E q) • v := fun _ _ => rfl
  have : IsScalarTower ℚ E S.V := ⟨fun q e v => by rw [hsm, Algebra.smul_def, mul_smul]⟩
  let B : S.V →ₗ[ℚ] S.V →ₗ[ℚ] ℚ := LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (S.hT x y))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply])
    (fun q x y => by
      rw [hsm, LinearMap.map_smulₛₗ, LinearMap.smul_apply, eq_ratCast, map_ratCast, smul_eq_mul,
        ← Rat.smul_def, map_smul])
    (fun x y y' => by simp only [map_add])
    (fun q x y => by
      rw [hsm, map_smul, eq_ratCast, smul_eq_mul, ← Rat.smul_def, map_smul])
  have hB : ∀ x y, B x y = Algebra.trace ℚ E (S.hT x y) := fun _ _ => rfl
  have hsymm : ∀ x y, B x y = B y x := by
    intro x y
    rw [hB, hB, ← S.herm.eq x y]
    exact (trace_star_eq_trace _).symm
  have hposB : ∀ x, x ≠ 0 → 0 < B x x := fun x hx => trace_pos_of_totally_positive _ (fun τ => hpos τ x hx)
  let Y : Submodule ℤ S.V := AddSubgroup.toIntSubmodule Y0
  have hspanL : Submodule.span ℚ (L : Set S.V) = ⊤ := by
    have hcl : ∀ (e : E) (v : S.V), v ∈ Submodule.span ℚ (L : Set S.V) →
        e • v ∈ Submodule.span ℚ (L : Set S.V) := by
      intro e v hv
      refine Submodule.span_induction (p := fun v _ => e • v ∈ Submodule.span ℚ (L : Set S.V)) ?_ ?_ ?_ ?_ hv
      · intro l hl
        rw [← (integralBasis E).sum_repr e, Finset.sum_smul]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [smul_assoc]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        rw [integralBasis_apply, algebraMap_smul]
        exact L.smul_mem _ hl
      · simp
      · intro a c _ _ ha hc
        rw [smul_add]
        exact add_mem ha hc
      · intro q a _ ha
        rw [smul_comm]
        exact Submodule.smul_mem _ _ ha
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ Submodule.span E (L : Set S.V) := by rw [hL.span_eq_top]; trivial
    refine Submodule.span_induction (p := fun v _ => v ∈ Submodule.span ℚ (L : Set S.V)) ?_ ?_ ?_ ?_ hv
    · exact fun l hl => Submodule.subset_span hl
    · exact zero_mem _
    · exact fun a c _ _ ha hc => add_mem ha hc
    · exact fun e a _ ha => hcl e a ha
  have hYlat : Submodule.IsLattice ℚ Y :=
    ⟨hfg, top_le_iff.mp (hspanL ▸ Submodule.span_mono (fun l hl => hint l hl))⟩
  let b0 : Basis (Fin (finrank ℤ Y)) ℤ Y := Module.finBasis ℤ Y
  let b : Basis (Fin (finrank ℤ Y)) ℚ S.V := b0.extendOfIsLattice ℚ
  have hb : ∀ i, b i = (b0 i).val := fun i => Basis.extendOfIsLattice_apply ℚ b0 i
  have hdV : finrank ℚ S.V = finrank ℤ Y := by
    rw [finrank_eq_card_basis b]
    simp
  have hd : finrank ℤ Y = finrank ℚ E * S.rank := by
    rw [← hdV, ← S.rank_eq, finrank_mul_finrank]
  have hbY : Submodule.span ℤ (Set.range b) = Y := by
    have h1 : (b : Fin (finrank ℤ Y) → S.V) = Y.subtype ∘ b0 := funext hb
    rw [h1, Set.range_comp, Submodule.span_image, b0.span_eq, Submodule.map_subtype_top]
  have hκ2 : (Real.sqrt κ2) ^ 2 = κ2 := Real.sq_sqrt hκ.le
  have hd0 : 0 < finrank ℤ Y := by
    rw [hd]
    exact Nat.mul_pos finrank_pos hrk
  obtain ⟨y, hyY, hyli, hyB⟩ := rational_transference_short_basis hT hd0 B hsymm hposB b (Real.sqrt κ2)
    (Real.sqrt_pos.mpr hκ) (by
      intro x hx hz
      rw [hκ2]
      apply hlow x hx
      intro y hy
      have hy' : y ∈ Submodule.span ℤ (Set.range b) := by rw [hbY]; exact hy
      refine Submodule.span_induction (p := fun y _ => ∃ z : ℤ, Algebra.trace ℚ E (S.hT x y) = z) ?_ ?_ ?_ ?_ hy'
      · rintro _ ⟨i, rfl⟩
        exact hz i
      · exact ⟨0, by simp⟩
      · rintro a c _ _ ⟨z1, h1⟩ ⟨z2, h2⟩
        exact ⟨z1 + z2, by rw [map_add, map_add, h1, h2]; push_cast; rfl⟩
      · rintro k a _ ⟨z, h⟩
        exact ⟨k * z, by rw [map_zsmul, map_zsmul, h]; simp⟩)
  have : Module.Finite ℚ S.V := Module.Finite.of_basis b
  have : Nonempty (Fin (finrank ℤ Y)) := ⟨⟨0, hd0⟩⟩
  have hspanQ : Submodule.span ℚ (Set.range y) = ⊤ :=
    hyli.span_eq_top_of_card_eq_finrank (by rw [hdV]; simp)
  have hspanE : Submodule.span E (Set.range y) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : v ∈ Submodule.span ℚ (Set.range y) := by rw [hspanQ]; trivial
    exact Submodule.span_le_restrictScalars ℚ E _ h1
  obtain ⟨t, htsub, htspan, htli⟩ := exists_linearIndependent E (Set.range y)
  let bt : Basis t E S.V := Basis.mk htli (by rw [Subtype.range_coe, htspan, hspanE])
  have hcard : Nat.card t = S.rank := by rw [← finrank_eq_nat_card_basis bt, S.rank_eq]
  have : Finite t := ((Set.finite_range y).subset htsub).to_subtype
  let e : t ≃ Fin S.rank := Finite.equivFinOfCardEq hcard
  refine ⟨fun a => (e.symm a).1, fun a => ?_, htli.comp _ e.symm.injective, fun a => ?_⟩
  · obtain ⟨j, hj⟩ := htsub (e.symm a).2
    have h1 := hyY j
    rw [hbY, hj] at h1
    exact h1
  · obtain ⟨j, hj⟩ := htsub (e.symm a).2
    have h1 := hyB j
    rw [hj, hB, hκ2, hd] at h1
    refine h1.trans_eq ?_
    push_cast
    rfl

/- English proof (translation)
Establish `hn0 : (0 : ℝ) < (finrank ℚ E : ℝ)` using `by exact_mod_cast finrank_pos`. Establish `hr0 : 0 < |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))` using `Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))) _`. Take `⟨y, h1, h2, h3⟩` from `exists_short_basis_of_dual_lower hT S hpos (dualSub S L) (dualSub_toIntSubmodule_fg_of_isLattice S L hL) L hL hint hrk ((finrank ℚ E : ℝ) / (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2) (by positivity) (fun x hx hz => trace_form_lower_bound_dual S hpos L hint x hx hz)`. Use `⟨y, h1, h2, fun a => (h3 a).trans_eq ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_short_basis_dual (hT : PI.TransferenceMinima) (S : HSpace E)
    (hpos : ∀ (τ : E →+* ℂ) (x : S.V), x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ))
    (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (hint : ∀ x ∈ L, x ∈ dualSub S L)
    (hrk : 0 < S.rank) :
    ∃ y : Fin S.rank → S.V, (∀ a, y a ∈ dualSub S L) ∧ LinearIndependent E y ∧
      ∀ a, ((Algebra.trace ℚ E (S.hT (y a) (y a)) : ℚ) : ℝ) ≤
        (finrank ℚ E : ℝ) * (S.rank : ℝ) ^ 2 * (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2 := by
  have hn0 : (0 : ℝ) < (finrank ℚ E : ℝ) := by exact_mod_cast finrank_pos
  have hr0 : 0 < |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) :=
    Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))) _
  obtain ⟨y, h1, h2, h3⟩ := exists_short_basis_of_dual_lower hT S hpos (dualSub S L) (dualSub_toIntSubmodule_fg_of_isLattice S L hL) L hL hint hrk
    ((finrank ℚ E : ℝ) / (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2) (by positivity)
    (fun x hx hz => trace_form_lower_bound_dual S hpos L hint x hx hz)
  refine ⟨y, h1, h2, fun a => (h3 a).trans_eq ?_⟩
  field_simp

end LemT2

section LemTi

open Module NumberField Formalism.BasicNotions
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `set dd : FractionalIdeal (𝓞 E)⁰ E := ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) with hdd`. Establish `hdual0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero`. Establish `hinv : dd = (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹` using `coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)`. Establish `hdd0 : dd ≠ 0`. Rewrite using `[hinv]`.

Conclude with `inv_ne_zero hdual0`. Establish `hJ0 : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hJ`. Establish `h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * (J : FractionalIdeal (𝓞 E)⁰ E) ≤ FractionalIdeal.dual ℤ ℚ 1`. Rewrite using `[FractionalIdeal.mul_le]`. Introduce `i hi j hj`.

Take `⟨z, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).mp hi`. Take `⟨δ, hδ, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hj`. Establish `h2` using `h δ hδ`. Establish `e : z • β * algebraMap (𝓞 E) E δ = z • (algebraMap (𝓞 E) E δ * β)`. Rewrite using `[smul_mul_assoc, mul_comm]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ z h2`. Establish `h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * (J : FractionalIdeal (𝓞 E)⁰ E) * dd ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨I', hI'⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.mp h2`.

Establish `hne : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * (J : FractionalIdeal (𝓞 E)⁰ E) * dd ≠ 0` using `mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ) hJ0) hdd0`. Establish `hI0 : I' ≠ ⊥`. Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hI']`.

Simplify using the standard rewrite rules. Establish `hn` using `congrArg FractionalIdeal.absNorm hI'`. Rewrite `hn` using `[FractionalIdeal.coeIdeal_absNorm, map_mul, map_mul, FractionalIdeal.absNorm_span_singleton, hdd, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E]`. Establish `h3 : 1 ≤ Ideal.absNorm I'` using `Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`. Establish `h4 : (1 : ℚ) ≤ (Ideal.absNorm I' : ℚ)` using `by exact_mod_cast h3`.

Rewrite `h4` using `[hn]`. Conclude with `h4`.
-/
theorem one_le_norm_mul_absNorm_discr (β : E) (hβ : β ≠ 0) (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥)
    (h : ∀ a ∈ J, algebraMap (𝓞 E) E a * β ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    (1 : ℚ) ≤ |Algebra.norm ℚ β| * (Ideal.absNorm J : ℚ) * ((discr E).natAbs : ℚ) := by
  set dd : FractionalIdeal (𝓞 E)⁰ E := ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) with hdd
  have hdual0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hinv : dd = (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  have hdd0 : dd ≠ 0 := by
    rw [hinv]
    exact inv_ne_zero hdual0
  have hJ0 : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * (J : FractionalIdeal (𝓞 E)⁰ E) ≤
      FractionalIdeal.dual ℤ ℚ 1 := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hi
    obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hj
    have h2 := h δ hδ
    have e : z • β * algebraMap (𝓞 E) E δ = z • (algebraMap (𝓞 E) E δ * β) := by
      rw [smul_mul_assoc, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ z h2
  have h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * (J : FractionalIdeal (𝓞 E)⁰ E) * dd ≤ 1 := by
    calc FractionalIdeal.spanSingleton (𝓞 E)⁰ β * (J : FractionalIdeal (𝓞 E)⁰ E) * dd
        ≤ FractionalIdeal.dual ℤ ℚ 1 * dd := mul_le_mul_left h1 dd
      _ = 1 := by rw [hinv, mul_inv_cancel₀ hdual0]
  obtain ⟨I', hI'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp h2
  have hne : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * (J : FractionalIdeal (𝓞 E)⁰ E) * dd ≠ 0 :=
    mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ) hJ0) hdd0
  have hI0 : I' ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [← hI']
    simp
  have hn := congrArg FractionalIdeal.absNorm hI'
  rw [FractionalIdeal.coeIdeal_absNorm, map_mul, map_mul, FractionalIdeal.absNorm_span_singleton, hdd,
    FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E] at hn
  have h3 : 1 ≤ Ideal.absNorm I' := Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have h4 : (1 : ℚ) ≤ (Ideal.absNorm I' : ℚ) := by exact_mod_cast h3
  rw [hn] at h4
  exact h4

/- English proof (translation)
Use `choose c hc0 hc using fun σ : E →ₐ[ℚ] ℂ => hpos σ.toRingHom`. Establish `hc' : ∀ σ : E →ₐ[ℚ] ℂ, σ β = (c σ : ℂ)` using `hc`. Establish `hT : ((Algebra.trace ℚ E β : ℚ) : ℝ) = ∑ σ, c σ`. Establish `h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ E β) = ∑ σ : E →ₐ[ℚ] ℂ, σ β` using `trace_eq_sum_embeddings ℂ`. Simplify using `only [hc', eq_ratCast] at h1`.

Establish `h2 : (((Algebra.trace ℚ E β : ℚ) : ℝ) : ℂ) = ((∑ σ, c σ : ℝ) : ℂ)`. Use `push_cast`. Conclude with `h1`. Conclude with `h2` after adjusting the coercions. Establish `hNm : ((Algebra.norm ℚ β : ℚ) : ℝ) = ∏ σ, c σ`.

Establish `h1 : (algebraMap ℚ ℂ) (Algebra.norm ℚ β) = ∏ σ : E →ₐ[ℚ] ℂ, σ β` using `Algebra.norm_eq_prod_embeddings ℚ ℂ β`. Simplify using `only [hc', eq_ratCast] at h1`. Establish `h2 : (((Algebra.norm ℚ β : ℚ) : ℝ) : ℂ) = ((∏ σ, c σ : ℝ) : ℂ)`. Use `push_cast`. Conclude with `h1`.

Conclude with `h2` after adjusting the coercions. Use `set P : ℝ := ∏ σ, c σ with hP`. Establish `hP0 : 0 < P` using `Finset.prod_pos fun σ _ => hc0 σ`. Use `set n : ℝ := (finrank ℚ E : ℝ) with hn`. Establish `hn0 : 0 < n`.

Rewrite using `[hn]`. Conclude with `finrank_pos` after adjusting the coercions. Rewrite `hN` using `[hNm, abs_of_pos hP0]`. Establish `hcard : (∑ _σ : E →ₐ[ℚ] ℂ, (1 : ℝ)) = n`. Simplify using `[hn, AlgHom.card ℚ E ℂ]`.

Establish `hAG` using `Real.geom_mean_le_arith_mean (Finset.univ : Finset (E →ₐ[ℚ] ℂ)) (fun _ => 1) c (fun _ _ => zero_le_one) (by rw [hcard]; exact hn0) (fun σ _ => (hc0 σ).le)`. Simplify using `only [Real.rpow_one, one_mul, hcard] at hAG`. Rewrite `hAG` using `[← hP, ← hT]`. Establish `hr0 : 0 < Q ^ ((1 : ℝ) / n)` using `Real.rpow_pos_of_pos hQ _`. Establish `h5 : 1 ≤ P ^ (n⁻¹) * Q ^ ((1 : ℝ) / n)`.

Rewrite using `[one_div, ← Real.mul_rpow hP0.le hQ.le]`. Conclude with `Real.one_le_rpow hN (inv_nonneg.mpr hn0.le)`. Rewrite using `[div_le_iff₀ hr0]`. Rewrite `hAG` using `[le_div_iff₀ hn0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem totally_positive_trace_ge_of_norm_bound (β : E) (hpos : ∀ τ : E →+* ℂ, ∃ c : ℝ, 0 < c ∧ τ β = c) (Q : ℝ) (hQ : 0 < Q)
    (hN : 1 ≤ |((Algebra.norm ℚ β : ℚ) : ℝ)| * Q) :
    (finrank ℚ E : ℝ) / Q ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) ≤ ((Algebra.trace ℚ E β : ℚ) : ℝ) := by
  classical
  choose c hc0 hc using fun σ : E →ₐ[ℚ] ℂ => hpos σ.toRingHom
  have hc' : ∀ σ : E →ₐ[ℚ] ℂ, σ β = (c σ : ℂ) := hc
  have hT : ((Algebra.trace ℚ E β : ℚ) : ℝ) = ∑ σ, c σ := by
    have h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ E β) = ∑ σ : E →ₐ[ℚ] ℂ, σ β := trace_eq_sum_embeddings ℂ
    simp only [hc', eq_ratCast] at h1
    have h2 : (((Algebra.trace ℚ E β : ℚ) : ℝ) : ℂ) = ((∑ σ, c σ : ℝ) : ℂ) := by
      push_cast
      exact h1
    exact_mod_cast h2
  have hNm : ((Algebra.norm ℚ β : ℚ) : ℝ) = ∏ σ, c σ := by
    have h1 : (algebraMap ℚ ℂ) (Algebra.norm ℚ β) = ∏ σ : E →ₐ[ℚ] ℂ, σ β := Algebra.norm_eq_prod_embeddings ℚ ℂ β
    simp only [hc', eq_ratCast] at h1
    have h2 : (((Algebra.norm ℚ β : ℚ) : ℝ) : ℂ) = ((∏ σ, c σ : ℝ) : ℂ) := by
      push_cast
      exact h1
    exact_mod_cast h2
  set P : ℝ := ∏ σ, c σ with hP
  have hP0 : 0 < P := Finset.prod_pos fun σ _ => hc0 σ
  set n : ℝ := (finrank ℚ E : ℝ) with hn
  have hn0 : 0 < n := by
    rw [hn]
    exact_mod_cast finrank_pos
  rw [hNm, abs_of_pos hP0] at hN
  have hcard : (∑ _σ : E →ₐ[ℚ] ℂ, (1 : ℝ)) = n := by
    simp [hn, AlgHom.card ℚ E ℂ]
  have hAG := Real.geom_mean_le_arith_mean (Finset.univ : Finset (E →ₐ[ℚ] ℂ)) (fun _ => 1) c
    (fun _ _ => zero_le_one) (by rw [hcard]; exact hn0) (fun σ _ => (hc0 σ).le)
  simp only [Real.rpow_one, one_mul, hcard] at hAG
  rw [← hP, ← hT] at hAG
  have hr0 : 0 < Q ^ ((1 : ℝ) / n) := Real.rpow_pos_of_pos hQ _
  have h5 : 1 ≤ P ^ (n⁻¹) * Q ^ ((1 : ℝ) / n) := by
    rw [one_div, ← Real.mul_rpow hP0.le hQ.le]
    exact Real.one_le_rpow hN (inv_nonneg.mpr hn0.le)
  rw [div_le_iff₀ hr0]
  rw [le_div_iff₀ hn0] at hAG
  calc n = 1 * n := (one_mul n).symm
    _ ≤ P ^ (n⁻¹) * Q ^ ((1 : ℝ) / n) * n := mul_le_mul_of_nonneg_right h5 hn0.le
    _ = P ^ (n⁻¹) * n * Q ^ ((1 : ℝ) / n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hAG hr0.le

variable [StarRing E]

/- English proof (translation)
Set `f : 𝓞 E →ₗ[𝓞 E] S.V` to `LinearMap.toSpanSingleton (𝓞 E) S.V x`. Set `J : Ideal (𝓞 E)` to `L.comap f ⊓ I`. Establish `hJeq : J.toAddSubgroup = (L.toAddSubgroup.comap f.toAddMonoidHom) ⊓ I.toAddSubgroup`. Use extensionality with `a`. Conclude with `Iff.rfl`.

Establish `hrel : J.toAddSubgroup.relIndex I.toAddSubgroup = L.toAddSubgroup.relIndex (I.toAddSubgroup.map f.toAddMonoidHom)`. Rewrite using `[← AddSubgroup.relIndex_comap, hJeq]`. Conclude with `AddSubgroup.inf_relIndex_right _ _`. Establish `hle : I.toAddSubgroup.map f.toAddMonoidHom ≤ dualSub S L`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Conclude with `hI a ha`. Establish `hq : L.toAddSubgroup.relIndex (dualSub S L) ≠ 0` using `by rw [hLat.2]; exact hq0`. Establish `hrel1 : J.toAddSubgroup.relIndex I.toAddSubgroup ≤ q`. Rewrite using `[hrel, ← hLat.2]`. Conclude with `AddSubgroup.relIndex_le_of_le_right hle hq`.

Establish `hrel0 : J.toAddSubgroup.relIndex I.toAddSubgroup ≠ 0`. Rewrite using `[hrel]`. Conclude with `fun h0 => hq (AddSubgroup.relIndex_eq_zero_of_le_right hle h0)`. Establish `hidx : Ideal.absNorm J = J.toAddSubgroup.relIndex I.toAddSubgroup * Ideal.absNorm I`. Rewrite using `[Ideal.absNorm_eq_index, Ideal.absNorm_eq_index]`.

Conclude with `(AddSubgroup.relIndex_mul_index (show J.toAddSubgroup ≤ I.toAddSubgroup from fun a ha => ha.2)).symm`. Use `⟨J, ?_, fun a ha => ha.1, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1 : Ideal.absNorm J = 0` using `by rw [h0]; simp`. Rewrite `h1` using `[hidx]`.

Conclude with `(Nat.mul_ne_zero hrel0 hI0) h1`. Rewrite using `[hidx]`. Conclude with `Nat.mul_le_mul_right _ hrel1`.
-/
theorem exists_ideal_index_dual_to_lattice (S : HSpace E) (L : Submodule (𝓞 E) S.V) (q : ℕ) (hq0 : q ≠ 0) (hLat : LatT S q L) (x : S.V)
    (I : Ideal (𝓞 E)) (hI0 : Ideal.absNorm I ≠ 0) (hI : ∀ a ∈ I, a • x ∈ dualSub S L) :
    ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ (∀ a ∈ J, a • x ∈ L) ∧ Ideal.absNorm J ≤ q * Ideal.absNorm I := by
  let f : 𝓞 E →ₗ[𝓞 E] S.V := LinearMap.toSpanSingleton (𝓞 E) S.V x
  let J : Ideal (𝓞 E) := L.comap f ⊓ I
  have hJeq : J.toAddSubgroup = (L.toAddSubgroup.comap f.toAddMonoidHom) ⊓ I.toAddSubgroup := by
    ext a
    exact Iff.rfl
  have hrel : J.toAddSubgroup.relIndex I.toAddSubgroup =
      L.toAddSubgroup.relIndex (I.toAddSubgroup.map f.toAddMonoidHom) := by
    rw [← AddSubgroup.relIndex_comap, hJeq]
    exact AddSubgroup.inf_relIndex_right _ _
  have hle : I.toAddSubgroup.map f.toAddMonoidHom ≤ dualSub S L := by
    rintro _ ⟨a, ha, rfl⟩
    exact hI a ha
  have hq : L.toAddSubgroup.relIndex (dualSub S L) ≠ 0 := by rw [hLat.2]; exact hq0
  have hrel1 : J.toAddSubgroup.relIndex I.toAddSubgroup ≤ q := by
    rw [hrel, ← hLat.2]
    exact AddSubgroup.relIndex_le_of_le_right hle hq
  have hrel0 : J.toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 := by
    rw [hrel]
    exact fun h0 => hq (AddSubgroup.relIndex_eq_zero_of_le_right hle h0)
  have hidx : Ideal.absNorm J = J.toAddSubgroup.relIndex I.toAddSubgroup * Ideal.absNorm I := by
    rw [Ideal.absNorm_eq_index, Ideal.absNorm_eq_index]
    exact (AddSubgroup.relIndex_mul_index (show J.toAddSubgroup ≤ I.toAddSubgroup from fun a ha => ha.2)).symm
  refine ⟨J, ?_, fun a ha => ha.1, ?_⟩
  · intro h0
    have h1 : Ideal.absNorm J = 0 := by rw [h0]; simp
    rw [hidx] at h1
    exact (Nat.mul_ne_zero hrel0 hI0) h1
  · rw [hidx]
    exact Nat.mul_le_mul_right _ hrel1

/- English proof (translation)
Establish `hD : ∀ y ∈ L, S.hT x y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)`. Introduce `y hy`. Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]`. Introduce `a ha`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`.

Take `⟨z, hz⟩` from `hd (o • y) (L.smul_mem o hy)`. Rewrite using `[Algebra.traceForm_apply]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[← algebraMap_smul E o y, map_smul, smul_eq_mul, mul_comm]`. Rewrite using `[hz]`.

Simplify using the standard rewrite rules. Establish `hβ0 : S.hT x x ≠ 0`. Introduce `h0`. Take `⟨c, hc0, hc⟩` from `hpos (Classical.arbitrary (E →+* ℂ)) x hx`. Rewrite `hc` using `[h0, map_zero]`.

Establish `: c = 0` using `by exact_mod_cast hc.symm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hI1 : ∀ a ∈ differentIdeal ℤ (𝓞 E), a • x ∈ dualSub S L`. Introduce `a ha l hl`. Rewrite using `[← algebraMap_smul E a x, map_smul, smul_eq_mul, ← S.herm.eq x l]`.

Conclude with `different_mul_dual_mem_range a ha _ (star_mem_inverseDifferent _ (hD l hl))`. Establish `hdisc0 : (discr E).natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr (discr_ne_zero E)`. Take `⟨J, hJ, hJL, hJn⟩` from `exists_ideal_index_dual_to_lattice S L q hq0 hLat x (differentIdeal ℤ (𝓞 E)) (by rw [absNorm_differentIdeal E (𝒪 := 𝓞 E)]; exact hdisc0) hI1`. Rewrite `hJn` using `[absNorm_differentIdeal E (𝒪 := 𝓞 E)]`. Establish `hN` using `one_le_norm_mul_absNorm_discr (S.hT x x) hβ0 J hJ (by`.

Introduce `a ha`. Establish `h1` using `hD (a • x) (hJL a ha)`. Rewrite using `[← algebraMap_smul E a x, map_smul, smul_eq_mul] at h1)` and apply the resulting hypothesis. Establish `hDd : (((discr E).natAbs : ℕ) : ℝ) = |(discr E : ℝ)|`. Rewrite using `[Nat.cast_natAbs]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hDpos : 0 < |(discr E : ℝ)|` using `abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))`. Establish `hqpos : (0 : ℝ) < q` using `by exact_mod_cast Nat.pos_of_ne_zero hq0`. Apply `totally_positive_trace_ge_of_norm_bound _ (fun τ => hpos τ x hx) _ (by positivity)` to reduce the goal to its premises.

Establish `hN' : ((1 : ℚ) : ℝ) ≤ ((|Algebra.norm ℚ (S.hT x x)| * (Ideal.absNorm J : ℚ) * ((discr E).natAbs : ℚ) : ℚ) : ℝ)`. Conclude with `hN` after adjusting the coercions. Move the coercions through the operations in `at hN'`. Rewrite `hN'` using `[hDd]`. Establish `hr1 : ((Ideal.absNorm J : ℕ) : ℝ) ≤ q * |(discr E : ℝ)|`.

Rewrite using `[← hDd]`. Conclude with `hJn` after adjusting the coercions. Establish `habs : 0 ≤ |((Algebra.norm ℚ (S.hT x x) : ℚ) : ℝ)|` using `abs_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ habs` to reduce the goal to its premises.

Conclude with `mul_le_mul_of_nonneg_right hr1 hDpos.le`. Use `_ = _ := by ring`.
-/
theorem dual_lattice_vector_trace_lower_bound (S : HSpace E)
    (hpos : ∀ (τ : E →+* ℂ) (x : S.V), x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ))
    (L : Submodule (𝓞 E) S.V) (q : ℕ) (hq0 : q ≠ 0) (hLat : LatT S q L) (x : S.V) (hx : x ≠ 0)
    (hd : ∀ y ∈ L.toAddSubgroup, ∃ z : ℤ, Algebra.trace ℚ E (S.hT x y) = z) :
    (finrank ℚ E : ℝ) / (|(discr E : ℝ)| ^ 2 * q) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) ≤
      ((Algebra.trace ℚ E (S.hT x x) : ℚ) : ℝ) := by
  have hD : ∀ y ∈ L, S.hT x y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro y hy
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨z, hz⟩ := hd (o • y) (L.smul_mem o hy)
    rw [Algebra.traceForm_apply]
    refine ⟨z, ?_⟩
    rw [← algebraMap_smul E o y, map_smul, smul_eq_mul, mul_comm] at hz
    rw [hz]
    simp
  have hβ0 : S.hT x x ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := hpos (Classical.arbitrary (E →+* ℂ)) x hx
    rw [h0, map_zero] at hc
    have : c = 0 := by exact_mod_cast hc.symm
    linarith
  have hI1 : ∀ a ∈ differentIdeal ℤ (𝓞 E), a • x ∈ dualSub S L := by
    intro a ha l hl
    rw [← algebraMap_smul E a x, map_smul, smul_eq_mul, ← S.herm.eq x l]
    exact different_mul_dual_mem_range a ha _ (star_mem_inverseDifferent _ (hD l hl))
  have hdisc0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  obtain ⟨J, hJ, hJL, hJn⟩ := exists_ideal_index_dual_to_lattice S L q hq0 hLat x (differentIdeal ℤ (𝓞 E))
    (by rw [absNorm_differentIdeal E (𝒪 := 𝓞 E)]; exact hdisc0) hI1
  rw [absNorm_differentIdeal E (𝒪 := 𝓞 E)] at hJn
  have hN := one_le_norm_mul_absNorm_discr (S.hT x x) hβ0 J hJ (by
    intro a ha
    have h1 := hD (a • x) (hJL a ha)
    rwa [← algebraMap_smul E a x, map_smul, smul_eq_mul] at h1)
  have hDd : (((discr E).natAbs : ℕ) : ℝ) = |(discr E : ℝ)| := by
    rw [Nat.cast_natAbs]
    push_cast
    rfl
  have hDpos : 0 < |(discr E : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  apply totally_positive_trace_ge_of_norm_bound _ (fun τ => hpos τ x hx) _ (by positivity)
  have hN' : ((1 : ℚ) : ℝ) ≤ ((|Algebra.norm ℚ (S.hT x x)| * (Ideal.absNorm J : ℚ) * ((discr E).natAbs : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast hN
  push_cast at hN'
  rw [hDd] at hN'
  have hr1 : ((Ideal.absNorm J : ℕ) : ℝ) ≤ q * |(discr E : ℝ)| := by
    rw [← hDd]
    exact_mod_cast hJn
  have habs : 0 ≤ |((Algebra.norm ℚ (S.hT x x) : ℚ) : ℝ)| := abs_nonneg _
  calc (1 : ℝ) ≤ _ := hN'
    _ = |((Algebra.norm ℚ (S.hT x x) : ℚ) : ℝ)| * (((Ideal.absNorm J : ℕ) : ℝ) * |(discr E : ℝ)|) := by ring
    _ ≤ |((Algebra.norm ℚ (S.hT x x) : ℚ) : ℝ)| * ((q * |(discr E : ℝ)|) * |(discr E : ℝ)|) := by
      apply mul_le_mul_of_nonneg_left _ habs
      exact mul_le_mul_of_nonneg_right hr1 hDpos.le
    _ = _ := by ring

/- English proof (translation)
Establish `hn0 : (0 : ℝ) < (finrank ℚ E : ℝ)` using `by exact_mod_cast finrank_pos`. Establish `hDpos : 0 < |(discr E : ℝ)|` using `abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))`. Establish `hqpos : (0 : ℝ) < q` using `by exact_mod_cast Nat.pos_of_ne_zero hq0`. Establish `hr0 : 0 < (|(discr E : ℝ)| ^ 2 * q) ^ ((1 : ℝ) / (finrank ℚ E : ℝ))` using `Real.rpow_pos_of_pos (by positivity) _`. Establish `hfg : (AddSubgroup.toIntSubmodule L.toAddSubgroup).FG` using `(dualSub_toIntSubmodule_fg_of_isLattice S L hL).of_le (fun x hx => hLat.1 x hx)`.

Take `⟨y, h1, h2, h3⟩` from `exists_short_basis_of_dual_lower hT S hpos L.toAddSubgroup hfg L hL (fun x hx => hx) hrk ((finrank ℚ E : ℝ) / (|(discr E : ℝ)| ^ 2 * q) ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) (by positivity) (fun x hx hz => dual_lattice_vector_trace_lower_bound S hpos L q hq0 hLat x hx hz)`. Use `⟨y, h1, h2, fun a => (h3 a).trans_eq ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_short_basis_lattice (hT : PI.TransferenceMinima) (S : HSpace E)
    (hpos : ∀ (τ : E →+* ℂ) (x : S.V), x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ))
    (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (q : ℕ) (hq0 : q ≠ 0) (hLat : LatT S q L)
    (hrk : 0 < S.rank) :
    ∃ y : Fin S.rank → S.V, (∀ a, y a ∈ L) ∧ LinearIndependent E y ∧
      ∀ a, ((Algebra.trace ℚ E (S.hT (y a) (y a)) : ℚ) : ℝ) ≤
        (finrank ℚ E : ℝ) * (S.rank : ℝ) ^ 2 * (|(discr E : ℝ)| ^ 2 * q) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := by
  have hn0 : (0 : ℝ) < (finrank ℚ E : ℝ) := by exact_mod_cast finrank_pos
  have hDpos : 0 < |(discr E : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hr0 : 0 < (|(discr E : ℝ)| ^ 2 * q) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hfg : (AddSubgroup.toIntSubmodule L.toAddSubgroup).FG :=
    (dualSub_toIntSubmodule_fg_of_isLattice S L hL).of_le (fun x hx => hLat.1 x hx)
  obtain ⟨y, h1, h2, h3⟩ := exists_short_basis_of_dual_lower hT S hpos L.toAddSubgroup hfg L hL (fun x hx => hx) hrk
    ((finrank ℚ E : ℝ) / (|(discr E : ℝ)| ^ 2 * q) ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) (by positivity)
    (fun x hx hz => dual_lattice_vector_trace_lower_bound S hpos L q hq0 hLat x hx hz)
  refine ⟨y, h1, h2, fun a => (h3 a).trans_eq ?_⟩
  field_simp

end LemTi

section LemTiP

open Module NumberField Formalism.BasicNotions

/- English proof (translation)
Take `⟨y, h1, h2, h3⟩` from `exists_short_basis_lattice hT S hpos L hL q hq0 hLat hrk`. Use `⟨y, h1, h2, fun a => ?_⟩` and prove the remaining obligations. Establish `hN0 : 2 * f ≠ 0`. Rewrite using `[← hf]`. Conclude with `finrank_pos.ne'`.

Establish `hNr : (0 : ℝ) < 2 * (f : ℝ)`. Establish `: 0 < 2 * f` using `Nat.pos_of_ne_zero hN0`. Conclude with `this` after adjusting the coercions. Establish `hDd0 : 0 ≤ |(discr E : ℝ)|` using `abs_nonneg _`. Establish `hfr : (finrank ℚ E : ℝ) = ((2 * f : ℕ) : ℝ)` using `by rw [hf]`.

Establish `hle : (|(discr E : ℝ)| ^ 2 * q) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) ≤ (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2 * T`. Establish `hq' : (q : ℝ) ≤ (T : ℝ) ^ (2 * f)` using `by exact_mod_cast hqT`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hq' (by positivity))` to reduce the goal to its premises. Check the signs of the components of the expression.

Use `_ = (|(discr E : ℝ)| ^ 2) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) * ((T : ℝ) ^ (2 * f)) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := Real.mul_rpow (by positivity) (by positivity)`. Use `_ = _ := by`. Use `congr 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hDd0, ← Real.rpow_mul hDd0, mul_comm]`. Rewrite using `[hfr, one_div]`.

Conclude with `Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hN0`. Establish `h4` using `h3 a`. Rewrite using `[div_le_iff₀ hNr]`. Establish `hfr' : (finrank ℚ E : ℝ) = 2 * (f : ℝ)` using `by rw [hfr]; push_cast; ring`. Combine the equalities or inequalities in the displayed calculation.

Generalize the expression as in `(|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) = r`. Rewrite using `[hfr']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_short_basis_lattice_pow {E : Type} [Field E] [NumberField E] [StarRing E] (hT : PI.TransferenceMinima) (S : HSpace E)
    (hpos : ∀ (τ : E →+* ℂ) (x : S.V), x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ))
    (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (q T f : ℕ) (hf : finrank ℚ E = 2 * f)
    (hq0 : q ≠ 0) (hqT : q ≤ T ^ (2 * f)) (hLat : LatT S q L) (hrk : 0 < S.rank) :
    ∃ y : Fin S.rank → S.V, (∀ a, y a ∈ L) ∧ LinearIndependent E y ∧
      ∀ a, ((Algebra.trace ℚ E (S.hT (y a) (y a)) : ℚ) : ℝ) / (2 * f) ≤
        (S.rank : ℝ) ^ 2 * T * (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2 := by
  obtain ⟨y, h1, h2, h3⟩ := exists_short_basis_lattice hT S hpos L hL q hq0 hLat hrk
  refine ⟨y, h1, h2, fun a => ?_⟩
  have hN0 : 2 * f ≠ 0 := by
    rw [← hf]
    exact finrank_pos.ne'
  have hNr : (0 : ℝ) < 2 * (f : ℝ) := by
    have : 0 < 2 * f := Nat.pos_of_ne_zero hN0
    exact_mod_cast this
  have hDd0 : 0 ≤ |(discr E : ℝ)| := abs_nonneg _
  have hfr : (finrank ℚ E : ℝ) = ((2 * f : ℕ) : ℝ) := by rw [hf]
  have hle : (|(discr E : ℝ)| ^ 2 * q) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) ≤
      (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2 * T := by
    have hq' : (q : ℝ) ≤ (T : ℝ) ^ (2 * f) := by exact_mod_cast hqT
    calc (|(discr E : ℝ)| ^ 2 * q) ^ ((1 : ℝ) / (finrank ℚ E : ℝ))
        ≤ (|(discr E : ℝ)| ^ 2 * (T : ℝ) ^ (2 * f)) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := by
          apply Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hq' (by positivity))
          positivity
      _ = (|(discr E : ℝ)| ^ 2) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) *
          ((T : ℝ) ^ (2 * f)) ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := Real.mul_rpow (by positivity) (by positivity)
      _ = _ := by
          congr 1
          · rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hDd0, ← Real.rpow_mul hDd0, mul_comm]
          · rw [hfr, one_div]
            exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hN0
  have h4 := h3 a
  rw [div_le_iff₀ hNr]
  have hfr' : (finrank ℚ E : ℝ) = 2 * (f : ℝ) := by rw [hfr]; push_cast; ring
  calc _ ≤ _ := h4
    _ ≤ (finrank ℚ E : ℝ) * (S.rank : ℝ) ^ 2 *
        ((|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2 * T) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by
      generalize (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) = r
      rw [hfr']
      ring

end LemTiP

section Rec

open Module NumberField Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Rewrite using `[D.host.finrank_cmField, Ranks.f, Ranks.n]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_cmField_eq_two_mul (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
  ring

/- English proof (translation)
Introduce `u c hLat`. Establish `hr : (D.sp.X 0).rank = D.R.N 0` using `D.sp.X_rank 0 (Nat.zero_le _)`. Take `⟨y, hy1, hy2, hy3⟩` from `exists_short_basis_dual transference_successive_minima (D.sp.X 0) (fun τ x hx => D.X_form_pos 0 (Nat.zero_le _) τ x hx) (D.clsLat u 0 c) (D.clsLat_lat u 0 c) hLat.1 (by rw [hr]; exact rank_zero_pos D)`. Use `⟨y ∘ Fin.cast hr.symm, fun a => hy1 _, hy2.comp _ (Fin.cast_injective _), fun a => ?_⟩` and prove the remaining obligations. Establish `h1` using `hy3 (Fin.cast hr.symm a)`.

Establish `hf : (0 : ℝ) < 2 * (D.R.f : ℝ)`. Use `finrank_cmField_eq_two_mul D` as an intermediate fact. Establish `h0 : 0 < Module.finrank ℚ D.host.E` using `Module.finrank_pos`. Establish `: 0 < 2 * D.R.f` using `by omega`. Conclude with `this` after adjusting the coercions.

Establish `hv : 2 * D.host.v = |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))`. Unfold `Host.v Host.rdE`. Expand and normalize the polynomial expressions, which then agree. Establish `hrk : (((D.sp.X 0).rank : ℕ) : ℝ) = (D.R.k : ℝ)` using `by rw [hr, Ranks.N_zero]`. Rewrite `h1` using `[← hv, hrk, finrank_cmField_eq_two_mul]`.

Move the coercions through the operations in `at h1`. Rewrite using `[div_le_iff₀ hf]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem shortDual_holds (D : D7) : ShortDual D := by
  intro u c hLat
  have hr : (D.sp.X 0).rank = D.R.N 0 := D.sp.X_rank 0 (Nat.zero_le _)
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_short_basis_dual transference_successive_minima (D.sp.X 0)
    (fun τ x hx => D.X_form_pos 0 (Nat.zero_le _) τ x hx) (D.clsLat u 0 c) (D.clsLat_lat u 0 c) hLat.1
    (by rw [hr]; exact rank_zero_pos D)
  refine ⟨y ∘ Fin.cast hr.symm, fun a => hy1 _, hy2.comp _ (Fin.cast_injective _), fun a => ?_⟩
  have h1 := hy3 (Fin.cast hr.symm a)
  have hf : (0 : ℝ) < 2 * (D.R.f : ℝ) := by
    have := finrank_cmField_eq_two_mul D
    have h0 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have : 0 < 2 * D.R.f := by omega
    exact_mod_cast this
  have hv : 2 * D.host.v = |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ)) := by
    unfold Host.v Host.rdE
    ring
  have hrk : (((D.sp.X 0).rank : ℕ) : ℝ) = (D.R.k : ℝ) := by rw [hr, Ranks.N_zero]
  rw [← hv, hrk, finrank_cmField_eq_two_mul] at h1
  push_cast at h1
  rw [div_le_iff₀ hf]
  calc _ ≤ _ := h1
    _ = _ := by ring

/- English proof (translation)
The claim follows from `slopeMaxC_of D (shortDual_holds D) hG`.
-/
theorem slopeMaxC_of' (D : D7) (hG : SlopeMaxGiven D) : SlopeMaxC D := slopeMaxC_of D (shortDual_holds D) hG

/- English proof (translation)
The claim follows from `slope_max_open_four_of_hookBound hH D (shortDual_holds D) hG`.
-/
theorem slope_bound_of_max_slope (hH : HookBound) (D : D7) (hG : SlopeMaxGiven D) : SlopeMaxOpenPart D 4 :=
  slope_max_open_four_of_hookBound hH D (shortDual_holds D) hG

/- English proof (translation)
Take `⟨x0, hx⟩` from `h`. Conclude with `⟨x0, fun x hx0 hx1 i => slope_bound_of_max_slope hH _ (hx x hx0 hx1 i)⟩`.
-/
theorem family_slope_bound_of_max_slope (hH : HookBound) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : fam0 Fm SlopeMaxGiven) :
    FamilySlopeMaxOpenPart Fm 4 := by
  obtain ⟨x0, hx⟩ := h
  exact ⟨x0, fun x hx0 hx1 i => slope_bound_of_max_slope hH _ (hx x hx0 hx1 i)⟩

end Rec

section ColAbs

open Module NumberField Formalism.BasicNotions IsDedekindDomain

def IntSpanAtG {LL : Type} [Field LL] (Pl : Rows.Places LL) {Tau : Type} [Fintype Tau] {n : ℕ} (w : Pl.Pl)
    (lam : Tau → DomWeight n) : AddSubgroup (MvPolynomial (Tau × Fin n × Fin n) LL) :=
  AddSubgroup.closure {p | ∃ (r : LL) (f : Tau → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ intW Pl w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = r • ten (fun τ => MvPolynomial.map (Int.castRingHom LL) (f τ))}

def LocBasisG {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (Pl : Rows.Places LL) {n : ℕ} (w : Pl.Pl)
    (Q : HLat LL) (e : Q.ι ≃ Fin n) (γ : Matrix (Fin n) (Fin n) LL) : Prop :=
  IsUnit γ.det ∧ locW Pl w Q.L =
    Submodule.span (intW Pl w) (Set.range fun a : Fin n => ∑ i, γ i a • Q.b (e.symm i))

structure ColValG {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (Pl : Rows.Places LL)
    (Tau : Type) [Fintype Tau] {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (n q : ℕ)
    (C : Type) [Fintype C] (Lc : C → Submodule (𝓞 E) S.V) (lam : Tau → DomWeight n) (A : HLat LL) where
  ne : Nonempty C
  rho : Tau → (E →+* LL)
  Q : C → Tau → HLat LL
  Q_good : ∀ c τ, (Q c τ).Good
  eQ : ∀ c τ, (Q c τ).ι ≃ Fin n
  bc : ∀ c τ, S.V →+ (Q c τ).V
  bc_smul : ∀ c τ (a : E) y, bc c τ (a • y) = rho τ a • bc c τ y
  bc_L : ∀ c τ, (Q c τ).L = Submodule.span (𝓞 LL) (bc c τ '' (Lc c : Set S.V))
  bc_norm : ∀ c τ (v : InfinitePlace LL) y,
    (Formalism.HermitianLatticesTheory.majAt (Q c τ).b (Q c τ).X v (bc c τ y) (bc c τ y)).re =
      (v.embedding (rho τ (S.hT y y))).re
  latT : ∀ c, LatT S q (Lc c)
  co : A.V →ₗ[LL] (C → MvPolynomial (Tau × Fin n × Fin n) LL)
  co_inj : Function.Injective co
  co_range : ∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ TSpan LL lam
  fin : ∀ (w : Pl.Pl) (γ : C → Tau → Matrix (Fin n) (Fin n) LL),
    (∀ c τ, LocBasisG Pl w (Q c τ) (eQ c τ) (γ c τ)) →
    ∀ x, x ∈ locW Pl w A.L ↔ ∀ c, actAll lam (fun τ => (γ c τ)⁻¹) (co x c) ∈ IntSpanAtG Pl w lam
  inf : ∀ (v : InfinitePlace LL) x,
    (Formalism.HermitianLatticesTheory.majAt A.b A.X v x x).re =
      ∑ c, (nfAll lam
        (actAll lam (fun τ => Matrix.reindex (eQ c τ) (eQ c τ) ((Q c τ).X v)⁻¹)
          (MvPolynomial.map v.embedding (co x c)))
        (actAll lam (fun τ => Matrix.reindex (eQ c τ) (eQ c τ) ((Q c τ).X v)⁻¹)
          (MvPolynomial.map v.embedding (co x c)))).re

structure ColHyp {LL : Type} [Field LL] [NumberField LL] (Pl : Rows.Places LL)
    {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (f n T : ℕ)
    {C : Type} (Lc : C → Submodule (𝓞 E) S.V) : Prop where
  tc : IsTotallyComplex LL

  tcE : IsTotallyComplex E
  pl : ∃ plEq : Pl.Pl ≃ HeightOneSpectrum (𝓞 LL),
    ∀ w (x : LL), x ≠ 0 → Pl.val w x = ((vAdd (plEq w) x : ℤ) : WithTop ℤ)
  deg : finrank ℚ E = 2 * f
  rank : S.rank = n
  npos : 0 < n
  Tpos : 0 < T
  conj : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)
  pos : ∀ (τ : E →+* ℂ) (x : S.V), x ≠ 0 → ∃ c : ℝ, 0 < c ∧ τ (S.hT x x) = (c : ℂ)
  lat : ∀ c, Submodule.IsLattice E (Lc c)

def ColSlopeAbs : Prop :=
  ∀ (LL : Type) [Field LL] [NumberField LL] [StarRing LL] (Pl : Rows.Places LL)
    (Tau : Type) [Fintype Tau] (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (f n T : ℕ)
    (C : Type) [Fintype C] (Lc : C → Submodule (𝓞 E) S.V) (lam : Tau → DomWeight n) (A : HLat LL),
    ColHyp Pl S f n T Lc → ColValG Pl Tau S n (T ^ (2 * f)) C Lc lam A →
    ∃ μs : Tau → ℝ, (∀ τ, MuStd (lam τ).natW (μs τ)) ∧
      A.mu = -(∑ τ, (∑ i, ((lam τ).w i : ℝ)) / n * Real.log T) + ∑ τ, μs τ

def SlopeMaxAbs : Prop :=
  ∀ (LL : Type) [Field LL] [NumberField LL] [StarRing LL] (Pl : Rows.Places LL)
    (Tau : Type) [Fintype Tau] (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (f n T : ℕ)
    (C : Type) [Fintype C] (Lc : C → Submodule (𝓞 E) S.V) (lam : Tau → DomWeight n) (A : HLat LL),
    ColHyp Pl S f n T Lc → ColValG Pl Tau S n (T ^ (2 * f)) C Lc lam A →
    (∀ c, ∃ y : Fin n → S.V, (∀ a, y a ∈ dualSub S (Lc c)) ∧ LinearIndependent E y ∧
      ∀ a, ((Algebra.trace ℚ E (S.hT (y a) (y a)) : ℚ) : ℝ) / (2 * f) ≤
        (n : ℝ) ^ 2 * (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ))) ^ 2) →
    A.muMax ≤ ∑ τ, ((∑ i, ((lam τ).natW i : ℝ)) *
        Real.log (4 * (n : ℝ) ^ 4 * (|(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) / 2) ^ 2) +
      Real.log (cNu (lam τ).natW) - ((lam τ).detShift : ℝ) * Real.log T)

end ColAbs

section Polar

open Module NumberField Formalism.BasicNotions IsDedekindDomain

/- English proof (translation)
Establish `hc : (InfinitePlace.mk φ).IsComplex` using `IsTotallyComplex.isComplex _`. Rewrite `hc` using `[InfinitePlace.isComplex_mk_iff]`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_not] at hcon`. Apply `hc` to reduce the goal to its premises.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `a`. Simplify using `only [ComplexEmbedding.conjugate_coe_eq]`. Conclude with `Complex.conj_eq_iff_im.2 (hcon a)`.
-/
theorem exists_im_ne_zero_totallyComplex {E : Type} [Field E] [NumberField E] (hE : IsTotallyComplex E) (φ : E →+* ℂ) :
    ∃ a : E, (φ a).im ≠ 0 := by
  have hc : (InfinitePlace.mk φ).IsComplex := IsTotallyComplex.isComplex _
  rw [InfinitePlace.isComplex_mk_iff] at hc
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hcon a)

/- English proof (translation)
Take `⟨m1, m2, m3, m4⟩` from `Formalism.L2.GlobalTheoryTheory.HLatOps.isSesq_maj (h.Q c τ).b (h.Q c τ).X v`. Use `Formalism.L2.GlobalTheoryTheory.HLatOps.sesq_ext (K := E) (V := S.V) (σ := v.embedding.comp (h.rho τ)) (F := fun y y' => Formalism.HermitianLatticesTheory.majAt (h.Q c τ).b (h.Q c τ).X v (h.bc c τ y) (h.bc c τ y')) (G := fun y y' => v.embedding (h.rho τ (S.hT y y'))) (exists_im_n …` and prove the remaining obligations. Introduce `x x' z`. Simplify using `only [map_add, m1]`. Introduce `x z z'`.

Simplify using `only [map_add, m2]`. Introduce `a x z`. Simplify using `only [h.bc_smul, m3, RingHom.comp_apply]`. Introduce `a x z`. Simplify using `only [h.bc_smul, m4, RingHom.comp_apply]`.

Introduce `x x' z`. Simplify using `only [map_add, LinearMap.add_apply]`. Introduce `x z z'`. Simplify using `only [map_add]`. Introduce `a x z`.

Establish `h1` using `hH.conj (v.embedding.comp (h.rho τ)) a`. Simplify using `only [RingHom.comp_apply] at h1 ⊢`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, map_mul, starRingEnd_apply, h1]`. Introduce `a x z`. Simplify using `only [map_smul, smul_eq_mul, map_mul, RingHom.comp_apply]`.

Introduce `x`. Apply `Complex.ext` to reduce the goal to its premises. Conclude with `h.bc_norm c τ v x`. Establish `h1 : (Formalism.HermitianLatticesTheory.majAt (h.Q c τ).b (h.Q c τ).X v (h.bc c τ x) (h.bc c τ x)).im = 0`. Unfold `Formalism.HermitianLatticesTheory.majAt`.

Rewrite using `[Complex.im_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Simplify using `[Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`.

Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Take `⟨r, _, hr⟩` from `hH.pos (v.embedding.comp (h.rho τ)) x hx`. Simplify using `only [RingHom.comp_apply] at hr`. Rewrite using `[hr]`.

Simplify using the standard rewrite rules.
-/
theorem ColValG.gram_eq {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {f n T q : ℕ}
    {C : Type} [Fintype C] {Lc : C → Submodule (𝓞 E) S.V} {lam : Tau → DomWeight n} {A : HLat LL}
    (hH : ColHyp Pl S f n T Lc) (h : ColValG Pl Tau S n q C Lc lam A) (c : C) (τ : Tau)
    (v : InfinitePlace LL) (y y' : S.V) :
    Formalism.HermitianLatticesTheory.majAt (h.Q c τ).b (h.Q c τ).X v (h.bc c τ y) (h.bc c τ y') =
      v.embedding (h.rho τ (S.hT y y')) := by
  obtain ⟨m1, m2, m3, m4⟩ := Formalism.L2.GlobalTheoryTheory.HLatOps.isSesq_maj (h.Q c τ).b (h.Q c τ).X v
  refine Formalism.L2.GlobalTheoryTheory.HLatOps.sesq_ext (K := E) (V := S.V) (σ := v.embedding.comp (h.rho τ))
    (F := fun y y' => Formalism.HermitianLatticesTheory.majAt (h.Q c τ).b (h.Q c τ).X v (h.bc c τ y) (h.bc c τ y'))
    (G := fun y y' => v.embedding (h.rho τ (S.hT y y')))
    (exists_im_ne_zero_totallyComplex hH.tcE _) ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ y y'
  · intro x x' z
    simp only [map_add, m1]
  · intro x z z'
    simp only [map_add, m2]
  · intro a x z
    simp only [h.bc_smul, m3, RingHom.comp_apply]
  · intro a x z
    simp only [h.bc_smul, m4, RingHom.comp_apply]
  · intro x x' z
    simp only [map_add, LinearMap.add_apply]
  · intro x z z'
    simp only [map_add]
  · intro a x z
    have h1 := hH.conj (v.embedding.comp (h.rho τ)) a
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, map_mul, starRingEnd_apply, h1]
  · intro a x z
    simp only [map_smul, smul_eq_mul, map_mul, RingHom.comp_apply]
  · intro x
    apply Complex.ext
    · exact h.bc_norm c τ v x
    · have h1 : (Formalism.HermitianLatticesTheory.majAt (h.Q c τ).b (h.Q c τ).X v (h.bc c τ x) (h.bc c τ x)).im = 0 := by
        unfold Formalism.HermitianLatticesTheory.majAt
        rw [Complex.im_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [Complex.mul_im]
        ring
      rw [h1]
      by_cases hx : x = 0
      · simp [hx]
      · obtain ⟨r, _, hr⟩ := hH.pos (v.embedding.comp (h.rho τ)) x hx
        simp only [RingHom.comp_apply] at hr
        rw [hr]
        simp

end Polar

section F7

open Module NumberField Formalism.BasicNotions IsDedekindDomain

/- English proof (translation)
Set `_ : Algebra E LL` to `ρ.toAlgebra`. Establish `hρ : ∀ x, ρ x = algebraMap E LL x` using `fun _ => rfl`. Establish `hz : ρ β ≠ 0` using `(map_ne_zero ρ).mpr hβ`. Establish `hN : Algebra.norm ℚ (ρ β) = (Algebra.norm ℚ β) ^ (finrank E LL)`. Rewrite using `[← Algebra.norm_norm (S := E), hρ, Algebra.norm_algebraMap, map_pow]`.

Establish `hprod` using `InfinitePlace.prod_eq_abs_norm (ρ β)`. Simplify using `only [IsTotallyComplex.mult_eq] at hprod`. Establish `hlog : 2 * ∑ v : InfinitePlace LL, Real.log (v (ρ β)) = (finrank E LL : ℝ) * Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)|`. Establish `h1` using `congrArg Real.log hprod`. Rewrite `h1` using `[Real.log_prod (fun v _ => pow_ne_zero _ ((InfinitePlace.pos_iff.mpr hz).ne'))]`.

Simplify using `only [Real.log_pow] at h1`. Rewrite `h1` using `[← Finset.mul_sum]`. Rewrite `h1` using `[hN]`. Move the coercions through the operations in `at h1`. Rewrite `h1` using `[abs_pow, Real.log_pow]`.

Conclude with `h1`. Establish `hn` using `nPl_two_mul LL`. Establish `hmul : (finrank ℚ LL : ℝ) = (finrank ℚ E : ℝ) * (finrank E LL : ℝ)`. Conclude with `(finrank_mul_finrank ℚ E LL).symm` after adjusting the coercions. Establish `hE0 : (0 : ℝ) < (finrank ℚ E : ℝ)` using `by exact_mod_cast finrank_pos`.

Establish `hEL0 : (0 : ℝ) < (finrank E LL : ℝ)` using `by exact_mod_cast finrank_pos`. Establish `hP0 : (0 : ℝ) < (Formalism.HN.nPl LL : ℝ)`. Establish `: (0 : ℝ) < (finrank ℚ LL : ℝ)` using `by exact_mod_cast finrank_pos`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS : ∑ v : InfinitePlace LL, Real.log (v (ρ β)) = (finrank E LL : ℝ) * Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| / 2` using `by linarith`.

Establish `hP : (Formalism.HN.nPl LL : ℝ) = (finrank ℚ E : ℝ) * (finrank E LL : ℝ) / 2` using `by linarith`. Rewrite using `[hS, hP]`. Clear the denominators using the available nonvanishing facts.
-/
theorem mean_log_places_eq_log_norm {LL E : Type} [Field LL] [NumberField LL] [IsTotallyComplex LL] [Field E] [NumberField E]
    (ρ : E →+* LL) (β : E) (hβ : β ≠ 0) :
    (1 / (Formalism.HN.nPl LL : ℝ)) * ∑ v : InfinitePlace LL, Real.log (v (ρ β)) =
      (1 / (finrank ℚ E : ℝ)) * Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| := by
  let _ : Algebra E LL := ρ.toAlgebra
  have hρ : ∀ x, ρ x = algebraMap E LL x := fun _ => rfl
  have hz : ρ β ≠ 0 := (map_ne_zero ρ).mpr hβ
  have hN : Algebra.norm ℚ (ρ β) = (Algebra.norm ℚ β) ^ (finrank E LL) := by
    rw [← Algebra.norm_norm (S := E), hρ, Algebra.norm_algebraMap, map_pow]
  have hprod := InfinitePlace.prod_eq_abs_norm (ρ β)
  simp only [IsTotallyComplex.mult_eq] at hprod
  have hlog : 2 * ∑ v : InfinitePlace LL, Real.log (v (ρ β)) =
      (finrank E LL : ℝ) * Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| := by
    have h1 := congrArg Real.log hprod
    rw [Real.log_prod (fun v _ => pow_ne_zero _ ((InfinitePlace.pos_iff.mpr hz).ne'))] at h1
    simp only [Real.log_pow] at h1
    rw [← Finset.mul_sum] at h1
    rw [hN] at h1
    push_cast at h1
    rw [abs_pow, Real.log_pow] at h1
    exact h1
  have hn := nPl_two_mul LL
  have hmul : (finrank ℚ LL : ℝ) = (finrank ℚ E : ℝ) * (finrank E LL : ℝ) := by
    exact_mod_cast (finrank_mul_finrank ℚ E LL).symm
  have hE0 : (0 : ℝ) < (finrank ℚ E : ℝ) := by exact_mod_cast finrank_pos
  have hEL0 : (0 : ℝ) < (finrank E LL : ℝ) := by exact_mod_cast finrank_pos
  have hP0 : (0 : ℝ) < (Formalism.HN.nPl LL : ℝ) := by
    have : (0 : ℝ) < (finrank ℚ LL : ℝ) := by exact_mod_cast finrank_pos
    linarith
  have hS : ∑ v : InfinitePlace LL, Real.log (v (ρ β)) =
      (finrank E LL : ℝ) * Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| / 2 := by linarith
  have hP : (Formalism.HN.nPl LL : ℝ) = (finrank ℚ E : ℝ) * (finrank E LL : ℝ) / 2 := by linarith
  rw [hS, hP]
  field_simp

/- English proof (translation)
Use `hH.tc` as an intermediate fact. Rewrite using `[← mean_log_places_eq_log_norm (h.rho τ) _ hdet]`. Unfold `Formalism.LFunctionChainParameters.LLcv.lcvInf`. Use `congr 1`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Establish `h1 : Formalism.HN.gramPl (h.Q c τ).b (h.Q c τ).X v (fun a => h.bc c τ (x a)) = (v.embedding.comp (h.rho τ)).mapMatrix (Matrix.of fun a b => S.hT (x a) (x b))`. Use extensionality with `a b`. Simplify using `only [Formalism.HN.gramPl, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply]`. Conclude with `h.gram_eq hH c τ v (x a) (x b)`. Rewrite using `[h1, ← RingHom.map_det, RingHom.comp_apply]`.

Take `⟨r, hr0, hr⟩` from `hpos v`. Rewrite using `[hr, Complex.ofReal_re, ← InfinitePlace.norm_embedding_eq v, hr, Complex.norm_real, Real.norm_of_nonneg hr0.le]`.
-/
theorem ColValG.lcvInf_eq {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {f n T q : ℕ}
    {C : Type} [Fintype C] {Lc : C → Submodule (𝓞 E) S.V} {lam : Tau → DomWeight n} {A : HLat LL}
    (hH : ColHyp Pl S f n T Lc) (h : ColValG Pl Tau S n q C Lc lam A) (c : C) (τ : Tau)
    {j : ℕ} (x : Fin j → S.V) (hdet : (Matrix.of fun a b => S.hT (x a) (x b)).det ≠ 0)
    (hpos : ∀ v : InfinitePlace LL, ∃ r : ℝ, 0 < r ∧
      v.embedding (h.rho τ (Matrix.of fun a b => S.hT (x a) (x b)).det) = (r : ℂ)) :
    Formalism.LFunctionChainParameters.LLcv.lcvInf (h.Q c τ).b (h.Q c τ).X (fun a => h.bc c τ (x a)) =
      (1 / (finrank ℚ E : ℝ)) *
        Real.log |((Algebra.norm ℚ (Matrix.of fun a b => S.hT (x a) (x b)).det : ℚ) : ℝ)| := by
  have := hH.tc
  rw [← mean_log_places_eq_log_norm (h.rho τ) _ hdet]
  unfold Formalism.LFunctionChainParameters.LLcv.lcvInf
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  have h1 : Formalism.HN.gramPl (h.Q c τ).b (h.Q c τ).X v (fun a => h.bc c τ (x a)) =
      (v.embedding.comp (h.rho τ)).mapMatrix (Matrix.of fun a b => S.hT (x a) (x b)) := by
    ext a b
    simp only [Formalism.HN.gramPl, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply]
    exact h.gram_eq hH c τ v (x a) (x b)
  rw [h1, ← RingHom.map_det, RingHom.comp_apply]
  obtain ⟨r, hr0, hr⟩ := hpos v
  rw [hr, Complex.ofReal_re, ← InfinitePlace.norm_embedding_eq v, hr, Complex.norm_real, Real.norm_of_nonneg hr0.le]

end F7

section ColRec

open Module NumberField Formalism.BasicNotions IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ColVal.toG {D : D7} {u : D.what₂.Word} (h : ColVal D u) :
    ColValG D.what₂.places D.what₂.Tau (D.sp.X 0) (D.R.N 0) (Tu D u ^ (2 * D.R.f)) ((D.mem u).C.cls 0)
      (D.clsLat u 0) ((D.fm u).lam 0) ((D.fm u).lat 0) where
  ne := h.ne
  rho := h.rho
  Q := h.Q
  Q_good := h.Q_good
  eQ := h.eQ
  bc := h.bc
  bc_smul := h.bc_smul
  bc_L := h.bc_L
  bc_norm := h.bc_norm
  latT := h.latT
  co := h.co
  co_inj := h.co_inj
  co_range := h.co_range
  fin := h.fin
  inf := h.inf

/- English proof (translation)
The claim follows from `inferInstance tcE := D.sp.cm.cmUnram.1 pl := ⟨D.plEq, D.val_eq⟩ deg := finrank_cmField_eq_two_mul D rank := D.sp.X_rank 0 (Nat.zero_le _) npos := rank_zero_pos D Tpos := by exact_mod_cast b_Tu_pos D u conj := D.sp.cm.cmUnram.2.1 pos := fun τ x hx => D.X_form_pos 0 (Nat.zero_le _) …`.
-/
theorem columnHypotheses (D : D7) (u : D.what₂.Word) :
    ColHyp D.what₂.places (D.sp.X 0) D.R.f (D.R.N 0) (Tu D u) (D.clsLat u 0) where
  tc := inferInstance
  tcE := D.sp.cm.cmUnram.1
  pl := ⟨D.plEq, D.val_eq⟩
  deg := finrank_cmField_eq_two_mul D
  rank := D.sp.X_rank 0 (Nat.zero_le _)
  npos := rank_zero_pos D
  Tpos := by exact_mod_cast b_Tu_pos D u
  conj := D.sp.cm.cmUnram.2.1
  pos := fun τ x hx => D.X_form_pos 0 (Nat.zero_le _) τ x hx
  lat := D.clsLat_lat u 0

/- English proof (translation)
Rewrite using `[Finset.sum_congr rfl (fun i _ => weight_eq_lamCol D u τ i)]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => ((lamCol D u τ i : ℚ) : ℝ)) (D.R.N 0), Ranks.N_zero]`. Both sides reduce to the same expression.
-/
theorem sum_weight_eq_colAbs (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (∑ i : Fin (D.R.N 0), ((((D.fm u).lam 0 τ).w i : ℤ) : ℝ)) = colAbs D u τ := by
  rw [Finset.sum_congr rfl (fun i _ => weight_eq_lamCol D u τ i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((lamCol D u τ i : ℚ) : ℝ)) (D.R.N 0), Ranks.N_zero]
  rfl

/- English proof (translation)
Unfold `DomWeight.detShift`. Rewrite using `[dif_pos (rank_zero_pos D), weight_eq_lamCol]`. Simplify using `only [Ranks.N_zero]`.
-/
theorem detShift_eq_lamCol_last (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ((((D.fm u).lam 0 τ).detShift : ℤ) : ℝ) = (lamCol D u τ (D.R.k - 1) : ℝ) := by
  unfold DomWeight.detShift
  rw [dif_pos (rank_zero_pos D), weight_eq_lamCol]
  simp only [Ranks.N_zero]

/- English proof (translation)
Introduce `u hu`. Take `⟨μs, h1, h2⟩` from `h _ _ _ _ _ _ _ _ _ _ _ _ (columnHypotheses D u) hu.toG`. Use `⟨μs, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Use `congr 2`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[sum_weight_eq_colAbs, Ranks.N_zero]`.
-/
theorem colSlopeEq_of_abs (h : ColSlopeAbs) (D : D7) : ColSlopeEq D := by
  intro u hu
  obtain ⟨μs, h1, h2⟩ := h _ _ _ _ _ _ _ _ _ _ _ _ (columnHypotheses D u) hu.toG
  refine ⟨μs, h1, ?_⟩
  rw [h2]
  congr 2
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [sum_weight_eq_colAbs, Ranks.N_zero]

/- English proof (translation)
Introduce `u hu`. Establish `hv : |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ)) = 2 * D.host.v`. Unfold `Host.v Host.rdE`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `h _ _ _ _ _ _ _ _ _ _ _ _ (columnHypotheses D u) hu.toG (fun c => by`.

Take `⟨y, hy1, hy2, hy3⟩` from `shortDual_holds D u c (hu.latT c)`. Use `⟨y, hy1, hy2, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hv, Ranks.N_zero]`. Conclude with `hy3 a)`. Use `h1.trans_eq (Finset.sum_congr rfl fun τ _ => ?_)` and prove the remaining obligations.

Establish `hNk : ((D.R.N 0 : ℕ) : ℝ) = D.R.k` using `by rw [Ranks.N_zero]`. Rewrite using `[sum_natWeight_eq_colAbsShifted, detShift_eq_lamCol_last, hv, hNk, mul_div_cancel_left₀ _ (two_ne_zero)]`.
-/
theorem slopeMaxC_of_abs (h : SlopeMaxAbs) (D : D7) : SlopeMaxC D := by
  intro u hu
  have hv : |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ)) = 2 * D.host.v := by
    unfold Host.v Host.rdE
    ring
  have h1 := h _ _ _ _ _ _ _ _ _ _ _ _ (columnHypotheses D u) hu.toG (fun c => by
    obtain ⟨y, hy1, hy2, hy3⟩ := shortDual_holds D u c (hu.latT c)
    refine ⟨y, hy1, hy2, fun a => ?_⟩
    rw [hv, Ranks.N_zero]
    exact hy3 a)
  refine h1.trans_eq (Finset.sum_congr rfl fun τ _ => ?_)
  have hNk : ((D.R.N 0 : ℕ) : ℝ) = D.R.k := by rw [Ranks.N_zero]
  rw [sum_natWeight_eq_colAbsShifted, detShift_eq_lamCol_last, hv, hNk, mul_div_cancel_left₀ _ (two_ne_zero)]

end ColRec

section Fin23

open Formalism.BasicNotions

/- English proof (translation)
The claim follows from `Formalism.L2.GlobalTheoryTheory.TraceIntegrality.msCount_of_frames D 90 (by norm_num) fun u => ⟨fun i hi => ⟨(Formalism.L2.GlobalTheoryTheory.TraceIntegrality.shortFrame_record D u).1 i hi, (Formalism.L2.GlobalTheoryTheory.TraceIntegrality.coordCount_record D u 90 (by norm_num)). …`.
-/
theorem msCount_holds (D : D7) : MsCount D 90 :=
  Formalism.L2.GlobalTheoryTheory.TraceIntegrality.msCount_of_frames D 90 (by norm_num) fun u =>
    ⟨fun i hi => ⟨(Formalism.L2.GlobalTheoryTheory.TraceIntegrality.shortFrame_record D u).1 i hi,
        (Formalism.L2.GlobalTheoryTheory.TraceIntegrality.coordCount_record D u 90 (by norm_num)).1 i hi⟩,
      ⟨(Formalism.L2.GlobalTheoryTheory.TraceIntegrality.shortFrame_record D u).2,
        (Formalism.L2.GlobalTheoryTheory.TraceIntegrality.coordCount_record D u 90 (by norm_num)).2⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun _ _ _ _ => msCount_holds _⟩`.
-/
theorem msCountF_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : MsCountF Fm 90 :=
  ⟨0, fun _ _ _ _ => msCount_holds _⟩

/- English proof (translation)
The claim follows from `familyMass_of_massCount Fm 90 (by norm_num) (msCountF_holds Fm)`.
-/
theorem family_mass_count_bound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ConclusionF1 Fm :=
  familyMass_of_massCount Fm 90 (by norm_num) (msCountF_holds Fm)

/- English proof (translation)
The claim follows from `familyOpNorm_of_theta_mass Fm a2 (family_mass_count_bound Fm)`.
-/
theorem family_first_bound_of_theta {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (a2 : admF2 Fm) : ConclusionF2 Fm :=
  familyOpNorm_of_theta_mass Fm a2 (family_mass_count_bound Fm)

/- English proof (translation)
The claim follows from `Formalism.L2.GlobalTheoryTheory.TraceIntegrality.branching_link_all_families eps Fm`.
-/
theorem theorem_three_family_large_constant {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ConclusionF3 Fm := Formalism.L2.GlobalTheoryTheory.TraceIntegrality.branching_link_all_families eps Fm

/- English proof (translation)
The claim follows from `familyPropZ_first_of_admissible Fm a1 a2 (family_first_bound_of_theta Fm a2) (stmtFP_holds Fm a6)`.
-/
theorem family_bound_of_period_theta_lowering {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (a1 : admF1 Fm) (a2 : admF2 Fm) (a6 : admF6 Fm) : FamilyEstimateFour Fm :=
  familyPropZ_first_of_admissible Fm a1 a2 (family_first_bound_of_theta Fm a2) (stmtFP_holds Fm a6)

/- English proof (translation)
The claim follows from `familySlopeLower_of_open Fm (familySlopeLowerOpen_of_std stdSlopeLow_holds hookBound_holds Fm h)`.
-/
theorem family_second_bound_of_column_slope {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : fam0 Fm ColSlopeEq) : ConclusionF5 Fm :=
  familySlopeLower_of_open Fm (familySlopeLowerOpen_of_std stdSlopeLow_holds hookBound_holds Fm h)

/- English proof (translation)
The claim follows from `familySlopeMax_of_open Fm 4 (family_slope_bound_of_max_slope hookBound_holds Fm h)`.
-/
theorem family_third_bound_of_max_slope {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : fam0 Fm SlopeMaxGiven) : ConclusionF6 Fm :=
  familySlopeMax_of_open Fm 4 (family_slope_bound_of_max_slope hookBound_holds Fm h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨msCount_holds D, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.branching_link_all D, slopeLowerOpen_of_std_hook stdSlopeLow_holds hookBound_holds D h1, slope_bound_of_max_slope hookBound_holds D h2⟩`.
-/
theorem open_of_col (D : D7) (h1 : ColSlopeEq D) (h2 : SlopeMaxGiven D) : Open D 90 4 :=
  ⟨msCount_holds D, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.branching_link_all D, slopeLowerOpen_of_std_hook stdSlopeLow_holds hookBound_holds D h1,
    slope_bound_of_max_slope hookBound_holds D h2⟩

/- English proof (translation)
The claim follows from `stmtF_of_open Fm 90 4 (by norm_num) ⟨msCountF_holds Fm, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.branching_link_all_families eps Fm, familySlopeLowerOpen_of_std stdSlopeLow_holds hookBound_holds Fm h1, family_slope_bound_of_max_slope hookBound_holds Fm h2⟩`.
-/
theorem stmtF_of_col {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h1 : fam0 Fm ColSlopeEq) (h2 : fam0 Fm SlopeMaxGiven) :
    KudlaFamilyStatement Fm :=
  stmtF_of_open Fm 90 4 (by norm_num)
    ⟨msCountF_holds Fm, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.branching_link_all_families eps Fm,
      familySlopeLowerOpen_of_std stdSlopeLow_holds hookBound_holds Fm h1, family_slope_bound_of_max_slope hookBound_holds Fm h2⟩

/- English proof (translation)
The claim follows from `stmtF_of_open Fm 90 4 (by norm_num) ⟨msCountF_holds Fm, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.branching_link_all_families eps Fm, familySlopeLowerOpen_of_std stdSlopeLow_holds hookBound_holds Fm ⟨0, fun _ _ _ _ => colSlopeEq_of_abs hA _⟩, familySlopeMaxOpen_of_hook hoo …`.
-/
theorem stmtF_of_abs (hA : ColSlopeAbs) (hB : SlopeMaxAbs) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : KudlaFamilyStatement Fm :=
  stmtF_of_open Fm 90 4 (by norm_num)
    ⟨msCountF_holds Fm, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.branching_link_all_families eps Fm,
      familySlopeLowerOpen_of_std stdSlopeLow_holds hookBound_holds Fm ⟨0, fun _ _ _ _ => colSlopeEq_of_abs hA _⟩,
      familySlopeMaxOpen_of_hook hookBound_holds Fm ⟨0, fun _ _ _ _ => slopeMaxC_of_abs hB _⟩⟩

end Fin23

end Formalism.MainNotions.flipTwoThree
