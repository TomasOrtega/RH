import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCycleExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockFnField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.TwoLeKrullDimOfRelevantPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace TwoBlockModuleFinite

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

/- English proof (translation)
The claim follows from `aeval_X _ _`.
-/
theorem cone_X (x x' : Ix κ → Ω) (p : Σ k, FinTwoTypeFamily κ k) :
    mConeMap (pair x x') (X p : MRing (FinTwoTypeFamily κ)) = MvPolynomial.C (pair x x' p) * X p.1 :=
  aeval_X _ _

/- English proof (translation)
Simplify using `only [twoBlockNum, map_sum, map_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Take `⟨⟨⟩, j⟩` from `j`. Rewrite using `[cone_X]`. Simplify using `[mConeMap, pair, mul_assoc]`.
-/
theorem cone_num (x x' : Ix κ → Ω) (l : Ix κ → ℤ) :
    mConeMap (pair x x') (twoBlockNum l) = MvPolynomial.C (∑ j, (l j : Ω) * x' j) * X 1 := by
  simp only [twoBlockNum, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨⟨⟩, j⟩ := j
  rw [cone_X]
  simp [mConeMap, pair, mul_assoc]

/- English proof (translation)
Simplify using `only [map_sum, map_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Take `⟨⟨⟩, i⟩` from `i`. Rewrite using `[cone_X]`. Simplify using `[mConeMap, pair, mul_assoc]`.
-/
theorem coneMap_firstBlock_linearForm (x x' : Ix κ → Ω) (n : Ix κ → ℤ) :
    mConeMap (pair x x') (∑ i : Ix κ, MvPolynomial.C (n i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ))) =
      MvPolynomial.C (∑ i, (n i : Ω) * x i) * X 0 := by
  simp only [map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨⟩, i⟩ := i
  rw [cone_X]
  simp [mConeMap, pair, mul_assoc]

/- English proof (translation)
The claim follows from `RingHom.mem_ker`.
-/
theorem mem_twoBlockIdeal (x x' : Ix κ → Ω) (f : MRing (FinTwoTypeFamily κ)) :
    f ∈ twoBlockIdeal x x' ↔ mConeMap (pair x x') f = 0 :=
  RingHom.mem_ker

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`. Consider the case `coe b`. Establish `h' : ((b + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `h`. Rewrite `h'` using `[WithBot.coe_le_coe]`.

Express the relevant statement in the definitionally equal form `((b : ℕ∞) : WithBot ℕ∞) ≤ (((n : ℕ) : ℕ∞) : WithBot ℕ∞)`. Rewrite using `[WithBot.coe_le_coe]`. Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top => exact absurd h' (by simp)`. Consider the case `coe m`.

Establish `: m + 1 ≤ n + 1` using `by exact_mod_cast h'`. Conclude with `(by omega : m ≤ n)` after adjusting the coercions.
-/
theorem le_of_add_one_le' {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    have h' : ((b + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
    rw [WithBot.coe_le_coe] at h'
    change ((b : ℕ∞) : WithBot ℕ∞) ≤ (((n : ℕ) : ℕ∞) : WithBot ℕ∞)
    rw [WithBot.coe_le_coe]
    induction b using ENat.recTopCoe with
    | top => exact absurd h' (by simp)
    | coe m =>
      have : m + 1 ≤ n + 1 := by exact_mod_cast h'
      exact_mod_cast (by omega : m ≤ n)

end TwoBlockModuleFinite

open TwoBlockModuleFinite in

/- English proof (translation)
Establish `hA` using `CoordArithOfFnField.proof`. Establish `hF` using `TwoBlockFnField.proof`. Introduce `D Ω _ _ κ _ x B c l hx hli hB hspan hxc`. Take `⟨hFp, -⟩` from `hF Ω κ x B hB`. Use `set x' := matAct B x with hx'def`.

Establish `hxA : IsArithVar (mCoordIdeal (ι` using `GlobalTheory κ) x) (D + 1) := by`. Rewrite using `[← coordIdeal_eq_mCoordIdeal]`. Conclude with `hx`. Establish `hxc0 : x ⟨(), c⟩ ≠ 0` using `hli.ne_zero _`. Establish `hx'0 : ∃ j, x' ⟨(), j⟩ ≠ 0`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hxc0` to reduce the goal to its premises. Rewrite using `[hxc]`. Conclude with `Finset.sum_eq_zero fun j _ => by`.

Take `⟨⟨⟩, j⟩` from `j`. Rewrite using `[h j, mul_zero]`. Take `⟨i₁, hi₁⟩` from `hx'0`. Establish `hpA : IsArithVar (twoBlockIdeal x x') (D + 1)` using `hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x x') (D + 1) ⟨0⟩ (fun k => by fin_cases k`. Conclude with `⟨c, by simpa [pair] using hxc0⟩`.

Conclude with `⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA`. Take `⟨S, hS, hPS⟩` from `hpA.2.1.2.1`. Establish `hL : ∀ i : κ, ∃ L : Ix κ → ℤ, x ⟨(), i⟩ = ∑ j, (L j : Ω) * x' j`. Introduce `i`. Establish `hmem : x ⟨(), i⟩ ∈ Submodule.span ℤ (Set.range x')` using `hspan (Submodule.subset_span ⟨_, rfl⟩)`.

Take `⟨L, hL⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem`. Conclude with `⟨L, by rw [← hL]; simp [zsmul_eq_mul]⟩`. Use `choose L hL using hL`. Use `set N : ℕ := ∏ p : Ix κ × Ix κ, (B p.1 p.2).den with hN`. Establish `hN0 : 0 < N` using `Finset.prod_pos fun p _ => (B p.1 p.2).den_pos`.

Establish `hn : ∀ j i, ∃ z : ℤ, (z : ℚ) = N * B j i`. Introduce `j i`. Take `⟨M, hM⟩ : (B j i).den ∣ N` from `Finset.dvd_prod_of_mem (fun p : Ix κ × Ix κ => (B p.1 p.2).den) (Finset.mem_univ (j, i))`. Use `⟨M * (B j i).num, ?_⟩` and prove the remaining obligations. Rewrite using `[hM]`.

Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num]`. Expand and normalize the polynomial expressions, which then agree. Use `choose n hn using hn`. Establish `hNx' : ∀ j : κ, (N : Ω) * x' ⟨(), j⟩ = ∑ i, (n ⟨(), j⟩ i : Ω) * x i`.

Introduce `j`. Simplify using `only [hx'def, matAct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Use `congr 1`.

Establish `h` using `congrArg (fun q : ℚ => (q : Ω)) (hn ⟨(), j⟩ i)`. Move the coercions through the operations in `at h`. Rewrite using `[h]`. Establish `hPO : twoBlockIdeal x x' ≤ twoBlockMOuter x x' c` using `le_sup_left`. Establish `hPI : twoBlockIdeal x x' ≤ twoBlockMInner x x' l` using `le_sup_left`.

Establish `hgO : ∀ j : κ, twoBlockDen c * X ⟨1, j⟩ ∈ twoBlockMOuter x x' c` using `fun j => Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)`. Establish `hgI : ∀ i : κ, twoBlockNum l * X ⟨0, i⟩ ∈ twoBlockMInner x x' l` using `fun i => Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)`. Establish `hlx : ∑ j, (l j : Ω) * x' j = x ⟨(), c⟩` using `hxc.symm`. Use `⟨?_, ?_, ?_, ⟨N, hN0, ?_⟩, ?_⟩` and prove the remaining obligations. Use `⟨S ∪ Set.range fun j : κ => twoBlockDen c * X ⟨1, j⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `f (hf | ⟨j, rfl⟩)`. Conclude with `hS f hf`. Conclude with `⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (TwoBlockCycleExpand.isMultiHomog_twoBlockDen c) (ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X _)⟩`. Rewrite using `[twoBlockMOuter, hPS, Ideal.span_union]`. Use `⟨S ∪ Set.range fun i : κ => twoBlockNum l * X ⟨0, i⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `f (hf | ⟨i, rfl⟩)`. Conclude with `hS f hf`. Conclude with `⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (TwoBlockCycleExpand.isMultiHomog_twoBlockNum l) (ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X _)⟩`. Rewrite using `[twoBlockMInner, hPS, Ideal.span_union]`. Rewrite using `[twoBlockMInner, sup_le_iff]`.

Use `⟨hPO, Ideal.span_le.mpr ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hd : twoBlockNum l * X ⟨0, i⟩ - twoBlockDen c * twoBlockNum (L i) ∈ twoBlockIdeal x x'`. Rewrite using `[mem_twoBlockIdeal, map_sub, map_mul, map_mul, cone_num, cone_num, twoBlockDen, cone_X, cone_X, hlx, ← hL i]`. Simplify using `[pair]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hs : twoBlockDen c * twoBlockNum (L i) ∈ twoBlockMOuter x x' c`. Rewrite using `[twoBlockNum, Finset.mul_sum]`. Conclude with `Ideal.sum_mem _ fun j _ => by`. Rewrite using `[mul_left_comm]`.

Conclude with `Ideal.mul_mem_left _ _ (hgO j.2)`. Establish `h` using `Ideal.add_mem _ (hPO hd) hs`. Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce `f hf`. Rewrite `hf` using `[twoBlockMOuter, Submodule.mem_sup]`.

Take `⟨p, hp, s, hs, rfl⟩` from `hf`. Rewrite using `[mul_add]`. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hPI hp)) ?_` and prove the remaining obligations. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem g hg`.

Take `⟨j, rfl⟩` from `hg`. Establish `hd : (N : MRing (FinTwoTypeFamily κ)) * (twoBlockDen c * X ⟨1, j⟩) - twoBlockNum l * ∑ i : Ix κ, MvPolynomial.C (n ⟨(), j⟩ i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ)) ∈ twoBlockIdeal x x'`. Rewrite using `[mem_twoBlockIdeal, map_sub, map_mul, map_mul, map_mul, map_natCast, cone_num, coneMap_firstBlock_linearForm, twoBlockDen, cone_X, cone_X, hlx, ← hNx' j]`. Simplify using `[pair]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hs : twoBlockNum l * ∑ i : Ix κ, MvPolynomial.C (n ⟨(), j⟩ i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ)) ∈ twoBlockMInner x x' l`. Rewrite using `[Finset.mul_sum]`. Conclude with `Ideal.sum_mem _ fun i _ => by`. Rewrite using `[mul_left_comm]`. Conclude with `Ideal.mul_mem_left _ _ (hgI i.2)`.

Establish `h` using `Ideal.add_mem _ (hPI hd) hs`. Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Rewrite using `[mul_add]`.

Conclude with `Ideal.add_mem _ ha hb`. Consider the case `smul r a _ ha`. Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `Ideal.mul_mem_left _ _ ha`. Introduce `W hW hIW _`.

Establish `: (twoBlockIdeal x x').IsPrime` using `hpA.2.1.1`. Use `hW` as an intermediate fact. Establish `hlt : twoBlockIdeal x x' < W`. Use `lt_of_le_of_ne (hPI.trans hIW) fun h => ?_` and prove the remaining obligations. Establish `hm : twoBlockNum l * X ⟨0, c⟩ ∈ twoBlockIdeal x x'`.

Rewrite using `[h]`. Conclude with `hIW (hgI c)`. Rewrite `hm` using `[mem_twoBlockIdeal, map_mul, cone_num, cone_X, hlx]`. Simplify using `[pair, hxc0] at hm`. Establish `h` using `krullDim_quotient_add_one_le hlt`.

Rewrite `h` using `[hpA.2.2.2, Fintype.card_fin, show D + 1 + 2 = D + 2 + 1 by omega]`. Rewrite using `[Fintype.card_fin]`. Conclude with `le_of_add_one_le' h`.
-/
theorem TwoBlockModuleFinite.proof : TwoBlockModuleFinite.Statement := by
  classical
  have hA := CoordArithOfFnField.proof
  have hF := TwoBlockFnField.proof
  intro D Ω _ _ κ _ x B c l hx hli hB hspan hxc
  obtain ⟨hFp, -⟩ := hF Ω κ x B hB
  set x' := matAct B x with hx'def
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx
  have hxc0 : x ⟨(), c⟩ ≠ 0 := hli.ne_zero _
  have hx'0 : ∃ j, x' ⟨(), j⟩ ≠ 0 := by
    by_contra h
    push Not at h
    apply hxc0
    rw [hxc]
    exact Finset.sum_eq_zero fun j _ => by
      obtain ⟨⟨⟩, j⟩ := j
      rw [h j, mul_zero]
  obtain ⟨i₁, hi₁⟩ := hx'0
  have hpA : IsArithVar (twoBlockIdeal x x') (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x x') (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨c, by simpa [pair] using hxc0⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  obtain ⟨S, hS, hPS⟩ := hpA.2.1.2.1

  have hL : ∀ i : κ, ∃ L : Ix κ → ℤ, x ⟨(), i⟩ = ∑ j, (L j : Ω) * x' j := by
    intro i
    have hmem : x ⟨(), i⟩ ∈ Submodule.span ℤ (Set.range x') := hspan (Submodule.subset_span ⟨_, rfl⟩)
    obtain ⟨L, hL⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
    exact ⟨L, by rw [← hL]; simp [zsmul_eq_mul]⟩
  choose L hL using hL

  set N : ℕ := ∏ p : Ix κ × Ix κ, (B p.1 p.2).den with hN
  have hN0 : 0 < N := Finset.prod_pos fun p _ => (B p.1 p.2).den_pos
  have hn : ∀ j i, ∃ z : ℤ, (z : ℚ) = N * B j i := by
    intro j i
    obtain ⟨M, hM⟩ : (B j i).den ∣ N :=
      Finset.dvd_prod_of_mem (fun p : Ix κ × Ix κ => (B p.1 p.2).den) (Finset.mem_univ (j, i))
    refine ⟨M * (B j i).num, ?_⟩
    rw [hM]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose n hn using hn
  have hNx' : ∀ j : κ, (N : Ω) * x' ⟨(), j⟩ = ∑ i, (n ⟨(), j⟩ i : Ω) * x i := by
    intro j
    simp only [hx'def, matAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    congr 1
    have h := congrArg (fun q : ℚ => (q : Ω)) (hn ⟨(), j⟩ i)
    push_cast at h
    rw [h]
  have hPO : twoBlockIdeal x x' ≤ twoBlockMOuter x x' c := le_sup_left
  have hPI : twoBlockIdeal x x' ≤ twoBlockMInner x x' l := le_sup_left
  have hgO : ∀ j : κ, twoBlockDen c * X ⟨1, j⟩ ∈ twoBlockMOuter x x' c := fun j =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
  have hgI : ∀ i : κ, twoBlockNum l * X ⟨0, i⟩ ∈ twoBlockMInner x x' l := fun i =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hlx : ∑ j, (l j : Ω) * x' j = x ⟨(), c⟩ := hxc.symm
  refine ⟨?_, ?_, ?_, ⟨N, hN0, ?_⟩, ?_⟩
  ·
    refine ⟨S ∪ Set.range fun j : κ => twoBlockDen c * X ⟨1, j⟩, ?_, ?_⟩
    · rintro f (hf | ⟨j, rfl⟩)
      · exact hS f hf
      · exact ⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (TwoBlockCycleExpand.isMultiHomog_twoBlockDen c)
          (ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X _)⟩
    · rw [twoBlockMOuter, hPS, Ideal.span_union]
  ·
    refine ⟨S ∪ Set.range fun i : κ => twoBlockNum l * X ⟨0, i⟩, ?_, ?_⟩
    · rintro f (hf | ⟨i, rfl⟩)
      · exact hS f hf
      · exact ⟨_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (TwoBlockCycleExpand.isMultiHomog_twoBlockNum l)
          (ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X _)⟩
    · rw [twoBlockMInner, hPS, Ideal.span_union]
  ·
    rw [twoBlockMInner, sup_le_iff]
    refine ⟨hPO, Ideal.span_le.mpr ?_⟩
    rintro _ ⟨i, rfl⟩
    have hd : twoBlockNum l * X ⟨0, i⟩ - twoBlockDen c * twoBlockNum (L i) ∈ twoBlockIdeal x x' := by
      rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, cone_num, cone_num, twoBlockDen, cone_X, cone_X, hlx,
        ← hL i]
      simp [pair]
      ring
    have hs : twoBlockDen c * twoBlockNum (L i) ∈ twoBlockMOuter x x' c := by
      rw [twoBlockNum, Finset.mul_sum]
      exact Ideal.sum_mem _ fun j _ => by
        rw [mul_left_comm]
        exact Ideal.mul_mem_left _ _ (hgO j.2)
    have h := Ideal.add_mem _ (hPO hd) hs
    rwa [sub_add_cancel] at h
  ·
    intro f hf
    rw [twoBlockMOuter, Submodule.mem_sup] at hf
    obtain ⟨p, hp, s, hs, rfl⟩ := hf
    rw [mul_add]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hPI hp)) ?_
    induction hs using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      have hd : (N : MRing (FinTwoTypeFamily κ)) * (twoBlockDen c * X ⟨1, j⟩) -
          twoBlockNum l * ∑ i : Ix κ, MvPolynomial.C (n ⟨(), j⟩ i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ)) ∈
            twoBlockIdeal x x' := by
        rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, map_mul, map_natCast, cone_num, coneMap_firstBlock_linearForm, twoBlockDen, cone_X,
          cone_X, hlx, ← hNx' j]
        simp [pair]
        ring
      have hs : twoBlockNum l * ∑ i : Ix κ, MvPolynomial.C (n ⟨(), j⟩ i) * (X ⟨0, i.2⟩ : MRing (FinTwoTypeFamily κ)) ∈
          twoBlockMInner x x' l := by
        rw [Finset.mul_sum]
        exact Ideal.sum_mem _ fun i _ => by
          rw [mul_left_comm]
          exact Ideal.mul_mem_left _ _ (hgI i.2)
      have h := Ideal.add_mem _ (hPI hd) hs
      rwa [sub_add_cancel] at h
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Ideal.add_mem _ ha hb
    | smul r a _ ha =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ ha
  ·
    intro W hW hIW _
    have : (twoBlockIdeal x x').IsPrime := hpA.2.1.1
    have := hW
    have hlt : twoBlockIdeal x x' < W := by
      refine lt_of_le_of_ne (hPI.trans hIW) fun h => ?_
      have hm : twoBlockNum l * X ⟨0, c⟩ ∈ twoBlockIdeal x x' := by
        rw [h]
        exact hIW (hgI c)
      rw [mem_twoBlockIdeal, map_mul, cone_num, cone_X, hlx] at hm
      simp [pair, hxc0] at hm
    have h := krullDim_quotient_add_one_le hlt
    rw [hpA.2.2.2, Fintype.card_fin, show D + 1 + 2 = D + 2 + 1 by omega] at h
    rw [Fintype.card_fin]
    exact le_of_add_one_le' h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
