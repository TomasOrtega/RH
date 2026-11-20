import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FirstCountableBlockMatrices

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
Introduce `m n ε c t p q e sL ρ hL _ _ W hW hWρ ν κ hν hκ ha hb P hP`. Use `hν` as an intermediate fact. Use `hW` as an intermediate fact. Set `sK` to `secK sL hL.cont`. Set `V : Submodule ℂ C(KR n, ℂ)` to `W.map sK`.

Set `κC : C(KR n, ℂ)` to `⟨κ, hκ⟩`. Establish `hF0c` using `continuous_weight_factor (n := n) hD p q e`. Establish `hflat : ∀ y : GR n, ∃ Q ∈ W, ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y'`. Introduce `y`. Take `⟨Q, hQW, hQ⟩` from `hb 0 (fun g => F0 p q e (g * y)) (hF0c.comp (continuous_id.mul continuous_const)) (fun y0 g hy0 => by`.

Simplify using `only [Complex.cpow_zero, one_mul]`. Rewrite using `[mul_assoc, ((hM n p q e).2 y0 (g * y) hy0).1])`. Conclude with `⟨Q, hQW, fun y' => by simpa using hQ y'⟩`. Use `choose QF hQFW hQF using hflat`. Set `v : GR n → V` to `fun y => ⟨sK (QF y), Submodule.mem_map_of_mem (hQFW y)⟩`.

Establish `hpi_v : ∀ y (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → piL ν κC h = sK (QF y)`. Introduce `y h hh`. Use extensionality with `k'`. Rewrite using `[piL_apply, secK_apply, ← hQF y (k' : GR n)]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[hh]`. Simplify using `[κC, mul_assoc]`. Establish `hpi_W : ∀ Q ∈ W, piL ν κC (sK Q) = sK Q`. Introduce `Q hQ`.

Use extensionality with `k'`. Rewrite using `[piL_apply, secK_apply, ← ha Q hQ (k' : GR n)]`. Both sides reduce to the same expression. Establish `hspan : Submodule.span ℂ (range v) = ⊤`. Assume the negation of the conclusion as `hne`.

Establish `hlt : Submodule.span ℂ (range v) < ⊤` using `lt_top_iff_ne_top.2 hne`. Take `⟨ℓ, hℓ0, hℓS⟩` from `Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance`. Take `⟨pr, hpr⟩` from `Submodule.ClosedComplemented.of_finiteDimensional V`. Set `ℓc : V →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap ℓ`. Set `L : C(KR n, ℂ) →L[ℂ] ℂ` to `ℓc.comp (pr.comp (piL ν κC))`.

Establish `hLv : ∀ (y : GR n) (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → L h = 0`. Introduce `y h hh`. Establish `e1 : L h = ℓ (pr (piL ν κC h))` using `rfl`. Rewrite using `[e1, hpi_v y h hh]`. Establish `e2 : pr (sK (QF y)) = v y` using `hpr (v y)`.

Rewrite using `[e2]`. Establish `hmem : v y ∈ Submodule.span ℂ (range v)` using `Submodule.subset_span ⟨y, rfl⟩`. Establish `: ℓ (v y) ∈ (Submodule.span ℂ (range v)).map ℓ` using `Submodule.mem_map_of_mem hmem`. Rewrite `this` using `[hℓS]`. Simplify using `using this`.

Apply `hℓ0` to reduce the goal to its premises. Use extensionality with `⟨x, hx⟩`. Take `⟨Q, hQ, rfl⟩` from `hx`. Establish `h0` using `hC m n ε c t p q e sL ρ hL L hLv Q (sK Q) (fun k => rfl)`. Establish `e1 : L (sK Q) = ℓ (pr (piL ν κC (sK Q)))` using `rfl`.

Rewrite `h0` using `[e1, hpi_W Q hQ]`. Establish `e2 : pr (sK Q) = ⟨sK Q, Submodule.mem_map_of_mem hQ⟩` using `hpr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩`. Rewrite `h0` using `[e2]`. Simplify using `using h0`. Take `⟨s, hs_sub, hs_span, hs_li⟩` from `exists_linearIndependent ℂ (range v)`.

Establish `hs_top : ⊤ ≤ Submodule.span ℂ (range ((↑) : s → V))`. Rewrite using `[Subtype.range_coe, hs_span, hspan]`. Set `bV` to `Module.Basis.mk hs_li hs_top`. Establish `: Finite s` using `Module.Finite.finite_basis bV`. Establish `: Fintype s` using `Fintype.ofFinite s`.

Set `N` to `Fintype.card s`. Set `b : Module.Basis (Fin N) ℂ V` to `bV.reindex (Fintype.equivFin s)`. Establish `hbv : ∀ i, ∃ y, v y = b i`. Introduce `i`. Establish `hb' : (b i : V) = ((Fintype.equivFin s).symm i : V)`.

Simplify using `[b, bV]`. Rewrite using `[hb']`. Conclude with `hs_sub ((Fintype.equivFin s).symm i).2`. Use `choose yy hyy using hbv`. Set `QQ : Fin N → PX m n` to `fun i => QF (yy i)`.

Establish `hQQ : ∀ i (k : KR n), ((b i : V) : C(KR n, ℂ)) k = sL (QQ i) (k : GR n)`. Introduce `i k`. Rewrite using `[← hyy i]`. Both sides reduce to the same expression. Establish `hcoord : ∀ Q (hQ : Q ∈ W) (k : KR n), sL Q (k : GR n) = ∑ j, b.repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩ j * sL (QQ j) (k : GR n)`.

Introduce `Q hQ k`. Establish `h` using `congrArg (fun x : V => ((x : C(KR n, ℂ)) k)) (b.sum_repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ] at h`. Rewrite using `[h]`. Both sides reduce to the same expression.

Establish `hsum_sL : ∀ (d : Fin N → ℂ) (y : GR n), sL (∑ j, d j • QQ j) y = ∑ j, d j * sL (QQ j) y`. Introduce `d y`. Simplify using `[map_sum, map_smul, Finset.sum_apply]`. Set `cc : Fin N → ℂ` to `fun j => b.repr ⟨sK P, Submodule.mem_map_of_mem hP⟩ j`. Establish `hPsum : ∀ y, sL P y = ∑ j, cc j * sL (QQ j) y`.

Introduce `y`. Rewrite using `[flatEq_of hI m n ε c t p q e sL ρ hL P (∑ j, cc j • QQ j) (fun k hk => by`. Rewrite using `[hcoord P hP ⟨k, hk⟩, hsum_sL]) y, hsum_sL]`. Set `f : Fin N → KR n → ℂ` to `fun j k => sL (QQ j) (k : GR n)`. Establish `hfli : LinearIndependent ℂ f`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h2 : ∑ j, g j • b j = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `k`.

Use `congrFun hg k` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, f] at this`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ, Submodule.coe_zero, ContinuousMap.zero_apply]`. Conclude with `this`. Conclude with `Fintype.linearIndependent_iff.1 b.linearIndependent g h2`.

Take `⟨kk, hkk⟩` from `exists_pts N f hfli`. Set `A : Matrix (Fin N) (Fin N) ℂ` to `Matrix.of fun j l => f j (kk l)`. Establish `hA : IsUnit A.det` using `isUnit_iff_ne_zero.2 hkk`. Set `Ev : ℂ → Matrix (Fin N) (Fin N) ℂ` to `fun w => Matrix.of fun i l => ∫ k, κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i)) ∂ν`. Set `M : ℂ → Matrix (Fin N) (Fin N) ℂ` to `fun w => Ev w * A⁻¹`.

Establish `hEv0 : Ev 0 = A`. Use extensionality with `i l`. Simplify using `only [Ev, A, f, Matrix.of_apply, Complex.cpow_zero, one_mul]`. Conclude with `hQF (yy i) (kk l)`. Establish `hM0 : M 0 = 1` using `by show Ev 0 * A⁻¹ = 1`.

Rewrite using `[hEv0]`. Conclude with `Matrix.mul_nonsing_inv A hA`. Establish `hEvd : ∀ i l, Differentiable ℂ (fun w => Ev w i l)`. Introduce `i l`. Establish `hcg : Continuous (fun k : KR n => (kk l : GR n) * (k : GR n) * yy i)` using `(continuous_const.mul continuous_subtype_val).mul continuous_const`.

Establish `hpos : ∀ k : KR n, 0 < hLoc ((kk l : GR n) * (k : GR n) * yy i)` using `fun k => hLoc_pos hD _`. Establish `h` using `(hH (KR n) ν univ isCompact_univ (by simp) univ (fun k w => κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i))) isOpen_univ ?_ ?_).1`. Conclude with `differentiableOn_univ.1 h`. Use `Continuous.continuousOn ?_` and prove the remaining obligations. Use `(hκ.comp continuous_fst).mul (Continuous.mul ?_ (hF0c.comp (hcg.comp continuous_fst)))` and prove the remaining obligations.

Conclude with `Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp (hcg.comp continuous_fst))) continuous_snd (fun y => Complex.ofReal_mem_slitPlane.2 (hpos y.1))`. Introduce `k _`. Establish `hne : ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (hpos k).ne'`. Conclude with `((((differentiable_id.const_cpow (Or.inl hne)).mul_const _).const_mul _)).differentiableOn`. Establish `hMd : ∀ i j, Differentiable ℂ (fun w => M w i j)`.

Introduce `i j`. Use `show Differentiable ℂ (fun w => (Ev w * A⁻¹) i j)`. Simplify using `only [Matrix.mul_apply]`. Conclude with `Differentiable.fun_sum fun l _ => (hEvd i l).mul_const _`. Use `⟨N, yy, QQ, cc, M, fun j => hQFW (yy j), hPsum, hM0, hMd, fun i y' => hQF (yy i) y', ?_⟩` and prove the remaining obligations.

Introduce `w i y'`. Set `fw : GR n → ℂ` to `fun g => (hLoc (g * yy i) : ℂ) ^ w * F0 p q e (g * yy i)`. Establish `hfwc : Continuous fw`. Establish `hg : Continuous (fun g : GR n => g * yy i)` using `continuous_id.mul continuous_const`. Use `Continuous.mul ?_ (hF0c.comp hg)` and prove the remaining obligations.

Conclude with `Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp hg)) continuous_const (fun g => Complex.ofReal_mem_slitPlane.2 (hLoc_pos hD _))`. Establish `hfwlaw : ∀ (y0 g : GR n), (mR y0).toBlocks₂₁ = 0 → fw (y0 * g) = (hLoc y0 : ℂ) ^ w * F0 p q e y0 * fw g`. Introduce `y0 g hy0`. Simplify using `only [fw]`. Rewrite using `[mul_assoc y0 g (yy i)]`.

Take `⟨h1, h2⟩` from `(hM n p q e).2 y0 (g * yy i) hy0`. Rewrite using `[h1, h2]`. Use `push_cast`. Rewrite using `[Complex.mul_cpow_ofReal_nonneg (hLoc_pos hD y0).le (hLoc_pos hD _).le]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨Qw, hQwW, hQw⟩` from `hb w fw hfwc hfwlaw`. Set `a` to `b.repr ⟨sK Qw, Submodule.mem_map_of_mem hQwW⟩`. Establish `hEva : ∀ l, Ev w i l = ∑ j, a j * A j l`. Introduce `l`. Establish `h1` using `hQw (kk l : GR n)`.

Rewrite `h1` using `[hLoc_K hM _ (kk l).2]`. Simplify using `only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h1`. Rewrite `h1` using `[hcoord Qw hQwW (kk l)]`. Simplify using `only [Ev, A, f, Matrix.of_apply]`. Rewrite using `[← h1]`.

Establish `hrow : (fun l => Ev w i l) = Matrix.vecMul a A`. Use function extensionality and compare the values at `l`. Rewrite using `[hEva l]`. Simplify using `[Matrix.vecMul, dotProduct]`. Establish `hMa : ∀ j, M w i j = a j`.

Introduce `j`. Establish `e1 : M w i j = Matrix.vecMul (fun l => Ev w i l) A⁻¹ j`. Simplify using `[M, Matrix.mul_apply, Matrix.vecMul, dotProduct]`. Rewrite using `[e1, hrow, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hA, Matrix.vecMul_one]`. Establish `hflatw : ∀ y, sL Qw y = ∑ j, M w i j * sL (QQ j) y`.

Introduce `y`. Rewrite using `[flatEq_of hI m n ε c t p q e sL ρ hL Qw (∑ j, M w i j • QQ j) (fun k hk => by`. Rewrite using `[hcoord Qw hQwW ⟨k, hk⟩, hsum_sL]`. Simplify using `only [hMa]`. Use the proof step `rfl) y, hsum_sL]`.

Rewrite using `[show (∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e (y' * (k : GR n) * yy i)) ∂ν) = ∫ k, κ k * fw (y' * (k : GR n)) ∂ν from rfl, hQw y', hflatw]`.
-/
theorem basis_of (hI : Iwa) (hD : CayleyBlocksInvertible) (hM : Mult) (hC : CycSec) (hH : HolParam) : Basis := by
  intro m n ε c t p q e sL ρ hL _ _ W hW hWρ ν κ hν hκ ha hb P hP
  have := hν
  have := hW
  let sK := secK sL hL.cont
  let V : Submodule ℂ C(KR n, ℂ) := W.map sK
  let κC : C(KR n, ℂ) := ⟨κ, hκ⟩
  have hF0c := continuous_weight_factor (n := n) hD p q e

  have hflat : ∀ y : GR n, ∃ Q ∈ W, ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y' := by
    intro y
    obtain ⟨Q, hQW, hQ⟩ := hb 0 (fun g => F0 p q e (g * y)) (hF0c.comp (continuous_id.mul continuous_const))
      (fun y0 g hy0 => by
        simp only [Complex.cpow_zero, one_mul]
        rw [mul_assoc, ((hM n p q e).2 y0 (g * y) hy0).1])
    exact ⟨Q, hQW, fun y' => by simpa using hQ y'⟩
  choose QF hQFW hQF using hflat
  let v : GR n → V := fun y => ⟨sK (QF y), Submodule.mem_map_of_mem (hQFW y)⟩
  have hpi_v : ∀ y (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → piL ν κC h = sK (QF y) := by
    intro y h hh
    ext k'
    rw [piL_apply, secK_apply, ← hQF y (k' : GR n)]
    congr 1; funext k
    rw [hh]; simp [κC, mul_assoc]
  have hpi_W : ∀ Q ∈ W, piL ν κC (sK Q) = sK Q := by
    intro Q hQ
    ext k'
    rw [piL_apply, secK_apply, ← ha Q hQ (k' : GR n)]
    rfl

  have hspan : Submodule.span ℂ (range v) = ⊤ := by
    by_contra hne
    have hlt : Submodule.span ℂ (range v) < ⊤ := lt_top_iff_ne_top.2 hne
    obtain ⟨ℓ, hℓ0, hℓS⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    obtain ⟨pr, hpr⟩ := Submodule.ClosedComplemented.of_finiteDimensional V
    let ℓc : V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap ℓ
    let L : C(KR n, ℂ) →L[ℂ] ℂ := ℓc.comp (pr.comp (piL ν κC))
    have hLv : ∀ (y : GR n) (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → L h = 0 := by
      intro y h hh
      have e1 : L h = ℓ (pr (piL ν κC h)) := rfl
      rw [e1, hpi_v y h hh]
      have e2 : pr (sK (QF y)) = v y := hpr (v y)
      rw [e2]
      have hmem : v y ∈ Submodule.span ℂ (range v) := Submodule.subset_span ⟨y, rfl⟩
      have : ℓ (v y) ∈ (Submodule.span ℂ (range v)).map ℓ := Submodule.mem_map_of_mem hmem
      rw [hℓS] at this
      simpa using this
    apply hℓ0
    ext ⟨x, hx⟩
    obtain ⟨Q, hQ, rfl⟩ := hx
    have h0 := hC m n ε c t p q e sL ρ hL L hLv Q (sK Q) (fun k => rfl)
    have e1 : L (sK Q) = ℓ (pr (piL ν κC (sK Q))) := rfl
    rw [e1, hpi_W Q hQ] at h0
    have e2 : pr (sK Q) = ⟨sK Q, Submodule.mem_map_of_mem hQ⟩ := hpr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩
    rw [e2] at h0
    simpa using h0

  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℂ (range v)
  have hs_top : ⊤ ≤ Submodule.span ℂ (range ((↑) : s → V)) := by
    rw [Subtype.range_coe, hs_span, hspan]
  let bV := Module.Basis.mk hs_li hs_top
  have : Finite s := Module.Finite.finite_basis bV
  have : Fintype s := Fintype.ofFinite s
  let N := Fintype.card s
  let b : Module.Basis (Fin N) ℂ V := bV.reindex (Fintype.equivFin s)
  have hbv : ∀ i, ∃ y, v y = b i := by
    intro i
    have hb' : (b i : V) = ((Fintype.equivFin s).symm i : V) := by
      simp [b, bV]
    rw [hb']
    exact hs_sub ((Fintype.equivFin s).symm i).2
  choose yy hyy using hbv
  let QQ : Fin N → PX m n := fun i => QF (yy i)
  have hQQ : ∀ i (k : KR n), ((b i : V) : C(KR n, ℂ)) k = sL (QQ i) (k : GR n) := by
    intro i k; rw [← hyy i]; rfl
  have hcoord : ∀ Q (hQ : Q ∈ W) (k : KR n), sL Q (k : GR n) =
      ∑ j, b.repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩ j * sL (QQ j) (k : GR n) := by
    intro Q hQ k
    have h := congrArg (fun x : V => ((x : C(KR n, ℂ)) k)) (b.sum_repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ] at h
    rw [h]; rfl
  have hsum_sL : ∀ (d : Fin N → ℂ) (y : GR n), sL (∑ j, d j • QQ j) y = ∑ j, d j * sL (QQ j) y := by
    intro d y
    simp [map_sum, map_smul, Finset.sum_apply]
  let cc : Fin N → ℂ := fun j => b.repr ⟨sK P, Submodule.mem_map_of_mem hP⟩ j
  have hPsum : ∀ y, sL P y = ∑ j, cc j * sL (QQ j) y := by
    intro y
    rw [flatEq_of hI m n ε c t p q e sL ρ hL P (∑ j, cc j • QQ j) (fun k hk => by
      rw [hcoord P hP ⟨k, hk⟩, hsum_sL]) y, hsum_sL]

  let f : Fin N → KR n → ℂ := fun j k => sL (QQ j) (k : GR n)
  have hfli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 : ∑ j, g j • b j = 0 := by
      apply Subtype.ext
      ext k
      have := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, f] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ, Submodule.coe_zero, ContinuousMap.zero_apply]
      exact this
    exact Fintype.linearIndependent_iff.1 b.linearIndependent g h2
  obtain ⟨kk, hkk⟩ := exists_pts N f hfli
  let A : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun j l => f j (kk l)
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 hkk
  let Ev : ℂ → Matrix (Fin N) (Fin N) ℂ := fun w => Matrix.of fun i l =>
    ∫ k, κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i)) ∂ν
  let M : ℂ → Matrix (Fin N) (Fin N) ℂ := fun w => Ev w * A⁻¹
  have hEv0 : Ev 0 = A := by
    ext i l
    simp only [Ev, A, f, Matrix.of_apply, Complex.cpow_zero, one_mul]
    exact hQF (yy i) (kk l)
  have hM0 : M 0 = 1 := by
    show Ev 0 * A⁻¹ = 1
    rw [hEv0]; exact Matrix.mul_nonsing_inv A hA
  have hEvd : ∀ i l, Differentiable ℂ (fun w => Ev w i l) := by
    intro i l
    have hcg : Continuous (fun k : KR n => (kk l : GR n) * (k : GR n) * yy i) :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have hpos : ∀ k : KR n, 0 < hLoc ((kk l : GR n) * (k : GR n) * yy i) := fun k => hLoc_pos hD _
    have h := (hH (KR n) ν univ isCompact_univ (by simp) univ
      (fun k w => κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i)))
      isOpen_univ ?_ ?_).1
    · exact differentiableOn_univ.1 h
    · refine Continuous.continuousOn ?_
      refine (hκ.comp continuous_fst).mul (Continuous.mul ?_ (hF0c.comp (hcg.comp continuous_fst)))
      exact Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp (hcg.comp continuous_fst)))
        continuous_snd (fun y => Complex.ofReal_mem_slitPlane.2 (hpos y.1))
    · intro k _
      have hne : ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos k).ne'
      exact ((((differentiable_id.const_cpow (Or.inl hne)).mul_const _).const_mul _)).differentiableOn
  have hMd : ∀ i j, Differentiable ℂ (fun w => M w i j) := by
    intro i j
    show Differentiable ℂ (fun w => (Ev w * A⁻¹) i j)
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun l _ => (hEvd i l).mul_const _
  refine ⟨N, yy, QQ, cc, M, fun j => hQFW (yy j), hPsum, hM0, hMd, fun i y' => hQF (yy i) y', ?_⟩
  intro w i y'
  let fw : GR n → ℂ := fun g => (hLoc (g * yy i) : ℂ) ^ w * F0 p q e (g * yy i)
  have hfwc : Continuous fw := by
    have hg : Continuous (fun g : GR n => g * yy i) := continuous_id.mul continuous_const
    refine Continuous.mul ?_ (hF0c.comp hg)
    exact Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp hg)) continuous_const
      (fun g => Complex.ofReal_mem_slitPlane.2 (hLoc_pos hD _))
  have hfwlaw : ∀ (y0 g : GR n), (mR y0).toBlocks₂₁ = 0 → fw (y0 * g) = (hLoc y0 : ℂ) ^ w * F0 p q e y0 * fw g := by
    intro y0 g hy0
    simp only [fw]
    rw [mul_assoc y0 g (yy i)]
    obtain ⟨h1, h2⟩ := (hM n p q e).2 y0 (g * yy i) hy0
    rw [h1, h2]
    push_cast
    rw [Complex.mul_cpow_ofReal_nonneg (hLoc_pos hD y0).le (hLoc_pos hD _).le]
    ring
  obtain ⟨Qw, hQwW, hQw⟩ := hb w fw hfwc hfwlaw
  let a := b.repr ⟨sK Qw, Submodule.mem_map_of_mem hQwW⟩
  have hEva : ∀ l, Ev w i l = ∑ j, a j * A j l := by
    intro l
    have h1 := hQw (kk l : GR n)
    rw [hLoc_K hM _ (kk l).2] at h1
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h1
    rw [hcoord Qw hQwW (kk l)] at h1
    simp only [Ev, A, f, Matrix.of_apply]
    rw [← h1]
  have hrow : (fun l => Ev w i l) = Matrix.vecMul a A := by
    funext l; rw [hEva l]; simp [Matrix.vecMul, dotProduct]
  have hMa : ∀ j, M w i j = a j := by
    intro j
    have e1 : M w i j = Matrix.vecMul (fun l => Ev w i l) A⁻¹ j := by
      simp [M, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [e1, hrow, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hA, Matrix.vecMul_one]
  have hflatw : ∀ y, sL Qw y = ∑ j, M w i j * sL (QQ j) y := by
    intro y
    rw [flatEq_of hI m n ε c t p q e sL ρ hL Qw (∑ j, M w i j • QQ j) (fun k hk => by
      rw [hcoord Qw hQwW ⟨k, hk⟩, hsum_sL]
      simp only [hMa]; rfl) y, hsum_sL]
  rw [show (∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e (y' * (k : GR n) * yy i)) ∂ν) =
      ∫ k, κ k * fw (y' * (k : GR n)) ∂ν from rfl, hQw y', hflatw]

end PositivityTheory.Rg.Sw.AbsSt.BasisPf

namespace PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
The claim follows from `BasisPf.basis_of hI hD hM hC hH`.
-/
theorem basis (hI : Iwa) (hD : CayleyBlocksInvertible) (hM : Mult) (hC : CycSec) (hH : HolParam) : Basis :=
  BasisPf.basis_of hI hD hM hC hH

end PositivityTheory.Rg.Sw.AbsSt
