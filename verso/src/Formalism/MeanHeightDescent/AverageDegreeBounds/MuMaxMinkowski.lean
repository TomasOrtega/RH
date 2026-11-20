import Mathlib
import Formalism.MeanHeightDescent.MuMaxMinkowski
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu

open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

section

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `h1 : ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 = ∑ i, ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2`. Introduce `v`. Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm`. Conclude with `Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))`. Simplify using `only [h1]`.

Unfold `Formalism.HermitianLatticesTheory.realize Formalism.HermitianLatticesTheory.realizeRaw`. Rewrite using `[PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[Fintype.sum_prod_type]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[Fin.sum_univ_two]`. Simplify using `[Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mink_norm_sq_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  have h1 : ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 = ∑ i, ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2 := by
    intro v
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))
  simp only [h1]
  unfold Formalism.HermitianLatticesTheory.realize Formalism.HermitianLatticesTheory.realizeRaw
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm`. Apply `Real.sqrt_pos.mpr` to reduce the goal to its premises. Establish `hne : Formalism.HermitianLatticesTheory.fcoord b X v x ≠ 0`. Unfold `Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt`. Introduce `h0`.

Establish `h1 : (fun i => v.embedding (b.repr x i)) = 0`. Establish `h3` using `congrArg (fun w => (X v).mulVec w) h0`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec, Matrix.mulVec_zero] at h3`. Conclude with `h3`. Apply `hx` to reduce the goal to its premises.

Establish `h2 : b.repr x = 0`. Use extensionality with `i`. Establish `h4` using `congrFun h1 i`. Simplify using `only [Pi.zero_apply] at h4`. Rewrite using `[Finsupp.zero_apply]`.

Conclude with `(map_eq_zero v.embedding).mp h4`. Conclude with `b.repr.map_eq_zero_iff.mp h2`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hne`. Establish `hpos : 0 < ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2` using `pow_pos (norm_pos_iff.mpr hi) 2`. Conclude with `lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j => ‖Formalism.HermitianLatticesTheory.fcoord b X v x j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))`.
-/
theorem mink_normAt_pos (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (x : V) (hx : x ≠ 0) :
    0 < Formalism.HermitianLatticesTheory.normAt b X v x := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  apply Real.sqrt_pos.mpr
  have hne : Formalism.HermitianLatticesTheory.fcoord b X v x ≠ 0 := by
    unfold Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
    intro h0
    have h1 : (fun i => v.embedding (b.repr x i)) = 0 := by
      have h3 := congrArg (fun w => (X v).mulVec w) h0
      simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec,
        Matrix.mulVec_zero] at h3
      exact h3
    apply hx
    have h2 : b.repr x = 0 := by
      ext i
      have h4 := congrFun h1 i
      simp only [Pi.zero_apply] at h4
      rw [Finsupp.zero_apply]
      exact (map_eq_zero v.embedding).mp h4
    exact b.repr.map_eq_zero_iff.mp h2
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hpos : 0 < ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j => ‖Formalism.HermitianLatticesTheory.fcoord b X v x j‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i))

/- English proof (translation)
Use `set n : ℝ := (Fintype.card σ : ℝ) with hn_def`. Establish `hn : 0 < n` using `Nat.cast_pos.mpr Fintype.card_pos`. Establish `hw : ∑ _v : σ, (1 / n) = 1`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, mul_one_div_cancel hn.ne']`. Establish `hJ` using `convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ => 1 / n) (p := fun v => 2 * Real.log (a v)) (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)`.

Simplify using `only [smul_eq_mul] at hJ`. Establish `hexp : ∀ v, Real.exp (2 * Real.log (a v)) = a v ^ 2` using `fun v => by`. Rewrite using `[two_mul, Real.exp_add, Real.exp_log (ha v)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hL : ∑ v, 1 / n * (2 * Real.log (a v)) = 2 * (1 / n * ∑ v, Real.log (a v))`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `v _`. Expand and normalize the polynomial expressions, which then agree. Establish `hR : ∑ v, 1 / n * Real.exp (2 * Real.log (a v)) = 1 / n * ∑ v, a v ^ 2`.

Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[hexp v]`. Rewrite `hJ` using `[hL, hR]`.

Establish `h3 : n * (1 / n * ∑ v, a v ^ 2) = ∑ v, a v ^ 2`. Rewrite using `[← mul_assoc, mul_one_div_cancel hn.ne', one_mul]`. Conclude with `(mul_le_mul_of_nonneg_left hJ hn.le).trans_eq h3`.
-/
theorem mink_am_gm {σ : Type} [Fintype σ] [Nonempty σ] (a : σ → ℝ) (ha : ∀ v, 0 < a v) :
    (Fintype.card σ : ℝ) * Real.exp (2 * ((1 / (Fintype.card σ : ℝ)) * ∑ v, Real.log (a v))) ≤
      ∑ v, a v ^ 2 := by
  set n : ℝ := (Fintype.card σ : ℝ) with hn_def
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∑ _v : σ, (1 / n) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, mul_one_div_cancel hn.ne']
  have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ => 1 / n)
    (p := fun v => 2 * Real.log (a v)) (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  have hexp : ∀ v, Real.exp (2 * Real.log (a v)) = a v ^ 2 := fun v => by
    rw [two_mul, Real.exp_add, Real.exp_log (ha v)]
    ring
  have hL : ∑ v, 1 / n * (2 * Real.log (a v)) = 2 * (1 / n * ∑ v, Real.log (a v)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hR : ∑ v, 1 / n * Real.exp (2 * Real.log (a v)) = 1 / n * ∑ v, a v ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [hexp v]
  rw [hL, hR] at hJ
  have h3 : n * (1 / n * ∑ v, a v ^ 2) = ∑ v, a v ^ 2 := by
    rw [← mul_assoc, mul_one_div_cancel hn.ne', one_mul]
  exact (mul_le_mul_of_nonneg_left hJ hn.le).trans_eq h3

end

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX B La hBfg hB0 hshort`. Use `set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ`. Take `⟨hlat, hrk, -⟩` from `place_lattice_structure K V ι b X hX B hBfg`. Establish `hinj : Function.Injective ρ` using `PlaceLattice.realize_injective b X hX`. Establish `hnf` using `sizeMu_finrank_eq K`.

Establish `hf : (0 : ℝ) < (nPl K : ℝ)`. Establish `: 0 < nPl K` using `Fintype.card_pos`. Conclude with `this` after adjusting the coercions. Establish `hj : (0 : ℝ) < (rkK B : ℝ)`. Establish `: Module.Finite K V` using `Module.Finite.of_basis b`.

Establish `h : Submodule.span K (B : Set V) ≠ ⊥`. Introduce `h`. Apply `hB0` to reduce the goal to its premises. Rewrite `h` using `[Submodule.span_eq_bot]`. Conclude with `(Submodule.eq_bot_iff _).2 (fun x hx => h x hx)`.

Establish `: 0 < rkK (K` using `K) B := Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)`. Conclude with `this` after adjusting the coercions. Establish `hdisc : DiscreteTopology (zl ρ B)` using `hlat.2`. Establish `hne : ∀ N : Submodule (𝓞 K) V, N ≠ ⊥ → zl ρ N ≠ ⊥`. Introduce `N hN h`.

Apply `hN` to reduce the goal to its premises. Use `(Submodule.eq_bot_iff _).2 fun x hx => ?_` and prove the remaining obligations. Establish `hm : ρ x ∈ zl ρ N` using `⟨x, hx, rfl⟩`. Rewrite `hm` using `[h, Submodule.mem_bot]`. Conclude with `hinj (by rw [hm, map_zero])`.

Establish `hmono : ∀ N : Submodule (𝓞 K) V, N ≤ B → zl ρ N ≤ zl ρ B`. Introduce and unpack `N hN y ⟨x, hx, rfl⟩`. Conclude with `⟨x, hN hx, rfl⟩`. Use `set r : ℝ := Real.sqrt (nPl K : ℝ) * Real.exp (-La) with hr`. Establish `hr0 : 0 < r` using `mul_pos (Real.sqrt_pos.2 hf) (Real.exp_pos _)`.

Establish `hmin : ∀ y ∈ zl ρ B, y ≠ 0 → r ≤ ‖y‖`. Introduce and unpack `y ⟨x, hx, rfl⟩ hy`. Establish `hx0 : x ≠ 0` using `fun h => hy (by rw [h]; exact map_zero ρ)`. Establish `h1` using `hshort x hx hx0`. Establish `h2` using `mink_am_gm (fun v => Formalism.HermitianLatticesTheory.normAt b X v x) (fun v => mink_normAt_pos b X hX v x hx0)`.

Establish `h3 : ‖ρ x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2` using `mink_norm_sq_realize b X x`. Establish `h4 : r ^ 2 ≤ ‖ρ x‖ ^ 2`. Rewrite using `[h3, hr, mul_pow, Real.sq_sqrt hf.le]`. Use `le_trans (mul_le_mul_of_nonneg_left ?_ hf.le) h2` and prove the remaining obligations. Rewrite using `[← Real.exp_nat_mul]`.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `: (1 / (nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) = (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x)` using `rfl`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(pow_le_pow_iff_left₀ hr0.le (norm_nonneg _) (by norm_num)).1 h4`.

Establish `hM` using `Formalism.F.muMaxLeMin _ (zl ρ B) hdisc (hne B hB0) r hr0 hmin`. Establish `hle : muMax ρ B ≤ Formalism.F.muMax (zl ρ B)`. Use `csSup_le ⟨_, B, le_rfl, hB0, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `t ⟨N, hN, hN0, rfl⟩`. Conclude with `Formalism.F.slopeLeMuMax _ (zl ρ B) (zl ρ N) hdisc (hmono N hN) (hne N hN0)`.

Establish `hrkR : (Formalism.F.rk (zl ρ B) : ℝ) = 2 * (nPl K : ℝ) * (rkK B : ℝ)`. Establish `: Formalism.F.rk (zl ρ B) = 2 * nPl K * rkK B` using `by rw [← hnf]; exact hrk`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hlogr : Real.log r = Real.log (nPl K : ℝ) / 2 - La`. Rewrite using `[hr, Real.log_mul (Real.sqrt_pos.2 hf).ne' (Real.exp_pos _).ne', Real.log_sqrt hf.le, Real.log_exp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlogrk : Real.log (Formalism.F.rk (zl ρ B) : ℝ) = Real.log 2 + Real.log (nPl K : ℝ) + Real.log (rkK B : ℝ)`. Rewrite using `[hrkR, Real.log_mul (by positivity) hj.ne', Real.log_mul (by norm_num) hf.ne']`.

Rewrite `hM` using `[hlogr, hlogrk]`. Unfold `muMaxDef`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem max_slope_minkowski : MuMaxMinkowski := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX B La hBfg hB0 hshort
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  obtain ⟨hlat, hrk, -⟩ := place_lattice_structure K V ι b X hX B hBfg
  have hinj : Function.Injective ρ := PlaceLattice.realize_injective b X hX
  have hnf := sizeMu_finrank_eq K
  have hf : (0 : ℝ) < (nPl K : ℝ) := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hj : (0 : ℝ) < (rkK B : ℝ) := by
    have : Module.Finite K V := Module.Finite.of_basis b
    have h : Submodule.span K (B : Set V) ≠ ⊥ := by
      intro h
      apply hB0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    have : 0 < rkK (K := K) B :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
    exact_mod_cast this
  have hdisc : DiscreteTopology (zl ρ B) := hlat.2

  have hne : ∀ N : Submodule (𝓞 K) V, N ≠ ⊥ → zl ρ N ≠ ⊥ := by
    intro N hN h
    apply hN
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have hm : ρ x ∈ zl ρ N := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact hinj (by rw [hm, map_zero])
  have hmono : ∀ N : Submodule (𝓞 K) V, N ≤ B → zl ρ N ≤ zl ρ B := by
    rintro N hN y ⟨x, hx, rfl⟩
    exact ⟨x, hN hx, rfl⟩

  set r : ℝ := Real.sqrt (nPl K : ℝ) * Real.exp (-La) with hr
  have hr0 : 0 < r := mul_pos (Real.sqrt_pos.2 hf) (Real.exp_pos _)
  have hmin : ∀ y ∈ zl ρ B, y ≠ 0 → r ≤ ‖y‖ := by
    rintro y ⟨x, hx, rfl⟩ hy
    have hx0 : x ≠ 0 := fun h => hy (by rw [h]; exact map_zero ρ)
    have h1 := hshort x hx hx0
    have h2 := mink_am_gm (fun v => Formalism.HermitianLatticesTheory.normAt b X v x)
      (fun v => mink_normAt_pos b X hX v x hx0)
    have h3 : ‖ρ x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := mink_norm_sq_realize b X x
    have h4 : r ^ 2 ≤ ‖ρ x‖ ^ 2 := by
      rw [h3, hr, mul_pow, Real.sq_sqrt hf.le]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hf.le) h2
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have : (1 / (nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) =
          (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := rfl
      push_cast
      linarith
    exact (pow_le_pow_iff_left₀ hr0.le (norm_nonneg _) (by norm_num)).1 h4
  have hM := Formalism.F.muMaxLeMin _ (zl ρ B) hdisc (hne B hB0) r hr0 hmin

  have hle : muMax ρ B ≤ Formalism.F.muMax (zl ρ B) := by
    refine csSup_le ⟨_, B, le_rfl, hB0, rfl⟩ ?_
    rintro t ⟨N, hN, hN0, rfl⟩
    exact Formalism.F.slopeLeMuMax _ (zl ρ B) (zl ρ N) hdisc (hmono N hN) (hne N hN0)
  have hrkR : (Formalism.F.rk (zl ρ B) : ℝ) = 2 * (nPl K : ℝ) * (rkK B : ℝ) := by
    have : Formalism.F.rk (zl ρ B) = 2 * nPl K * rkK B := by rw [← hnf]; exact hrk
    rw [this]; push_cast; ring
  have hlogr : Real.log r = Real.log (nPl K : ℝ) / 2 - La := by
    rw [hr, Real.log_mul (Real.sqrt_pos.2 hf).ne' (Real.exp_pos _).ne', Real.log_sqrt hf.le,
      Real.log_exp]
    ring
  have hlogrk : Real.log (Formalism.F.rk (zl ρ B) : ℝ) =
      Real.log 2 + Real.log (nPl K : ℝ) + Real.log (rkK B : ℝ) := by
    rw [hrkR, Real.log_mul (by positivity) hj.ne', Real.log_mul (by norm_num) hf.ne']
  rw [hlogr, hlogrk] at hM
  unfold muMaxDef
  linarith

end Formalism.ExtensionFiltration
