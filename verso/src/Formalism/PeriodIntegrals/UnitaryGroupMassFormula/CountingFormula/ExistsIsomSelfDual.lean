import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsIsomMove
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOrthogonalUnitVector

open NumberField Module

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

section Abs

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}

def PairUnit (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ w y : V, h y w = 1 → h w w ∈ S → h y y ∈ S →
    ∃ c ∈ S, ∃ d ∈ S, IsUnitIn S (h (c • w + d • y) (c • w + d • y))

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc j`. Use `congrArg (h (x j)) hc` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero, Finset.sum_eq_single j]`. Rewrite `this` using `[map_smul, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 this).resolve_right (hx0 j)`. Introduce `i _ hij`. Rewrite using `[map_smul, hxo j i (Ne.symm hij), smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem linIndep_orth {ι : Type} [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hx0 : ∀ i, h (x i) (x i) ≠ 0) : LinearIndependent K x := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := congrArg (h (x j)) hc
  rw [map_sum, map_zero, Finset.sum_eq_single j] at this
  · rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (hx0 j)
  · intro i _ hij
    rw [map_smul, hxo j i (Ne.symm hij), smul_zero]
  · simp

/- English proof (translation)
Rewrite using `[map_sub, map_sum, Finset.sum_eq_single j]`. Rewrite using `[map_smul, smul_eq_mul, mul_right_comm, inv_mul_cancel₀ (hx0 j), one_mul, sub_self]`. Introduce `i _ hij`. Rewrite using `[map_smul, hxo j i (Ne.symm hij), smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem orth_sub_proj {ι : Type} [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hx0 : ∀ i, h (x i) (x i) ≠ 0) (v : V) (j : ι) :
    h (x j) (v - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i) = 0 := by
  classical
  rw [map_sub, map_sum, Finset.sum_eq_single j]
  · rw [map_smul, smul_eq_mul, mul_right_comm, inv_mul_cancel₀ (hx0 j), one_mul, sub_self]
  · intro i _ hij
    rw [map_smul, hxo j i (Ne.symm hij), smul_zero]
  · simp

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit hS hs hnd hPU hL`.
-/
theorem exists_ortho_unit [FiniteDimensional K V] (hS : IsHermSemilocal S) (hs : h.IsSymm)
    (hnd : h.Nondegenerate) (hPU : PairUnit S h) {L : AddSubgroup V} (hL : IsSelfDualMod S h L) :
    ∃ x : Fin (finrank K V) → V, (∀ i, x i ∈ L) ∧ (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
      ∀ i, IsUnitIn S (h (x i) (x i)) :=
  _root_.UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit hS hs hnd hPU hL

/- English proof (translation)
Establish `P : ∀ k, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, i.val < k → g (x i) ∈ M`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Conclude with `⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩`.

Consider the case `succ k ih`. Introduce `hk`. Take `⟨g, hg, hgM⟩` from `ih (by omega)`. Establish `hg' : ∀ a b, h (g a) (g b) = h a b` using `hg`. Establish `hne : ∀ i : Fin n, i.val < k → i ≠ ⟨k, hk⟩`.

Introduce `i hi e`. Rewrite `hi` using `[e]`. Conclude with `lt_irrefl _ hi`. Set `y : {i : Fin n // i.val < k} → V` to `fun i => g (x i.1)`. Establish `hyo : ∀ i j : {i : Fin n // i.val < k}, i ≠ j → h (y i) (y j) = 0`.

Introduce `i j hij`. Simplify using `only [y]`. Rewrite using `[hg']`. Conclude with `hxo _ _ (fun e => hij (Subtype.ext e))`. Establish `hyu : ∀ i : {i : Fin n // i.val < k}, IsUnitIn S (h (y i) (y i))`.

Introduce `i`. Simplify using `only [y]`. Rewrite using `[hg']`. Conclude with `hxu _`. Establish `hyM : ∀ i : {i : Fin n // i.val < k}, y i ∈ M` using `fun i => hgM i.1 i.2`.

Establish `hu` using `hxu ⟨k, hk⟩`. Establish `hus : star (h (x ⟨k, hk⟩) (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩)` using `star_h hs _ _`. Establish `hrr : h (g (x ⟨k, hk⟩)) (g (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩)` using `hg' _ _`. Establish `hrx : ∀ i : {i : Fin n // i.val < k}, h (y i) (g (x ⟨k, hk⟩)) = 0`. Introduce `i`.

Simplify using `only [y]`. Rewrite using `[hg']`. Conclude with `hxo _ _ (hne i.1 i.2)`. Take `⟨z, hzM, hzz, hzo⟩` from `exists_of_ref hS hs hM y hyo hyu hyM hu hus hrr hrx`. Take `⟨τ, hτ, hτr, hτfix⟩` from `exists_isom_move hS hs hu.1 hus hrr hzz`.

Use `⟨τ * g, mul_mem hτ hg, fun i hi => ?_⟩` and prove the remaining obligations. Use `show τ (g (x i)) ∈ M`. Break down `Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1` into its components or cases. Rewrite using `[hτfix]`. Conclude with `hgM i h1`.

Rewrite using `[hg']`. Conclude with `hxo _ _ (fun e => hne i h1 e.symm)`. Rewrite using `[← star_h hs]`. Use `hzo ⟨i, h1⟩` as an intermediate fact. Simplify using `only [y] at this`.

Rewrite using `[this, star_zero]`. Establish `: i = ⟨k, hk⟩` using `Fin.ext h1`. Rewrite using `[this, hτr]`. Conclude with `hzM`. Take `⟨g, hg, hgM⟩` from `P n le_rfl`.

Conclude with `⟨g, hg, fun i => hgM i i.isLt⟩`.
-/
theorem exists_isom_frameU (hS : IsHermSemilocal S) (hs : h.IsSymm) {M : AddSubgroup V}
    (hM : IsSelfDualMod S h M) {n : ℕ} (x : Fin n → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hxu : ∀ i, IsUnitIn S (h (x i) (x i))) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (x i) ∈ M := by
  classical
  have P : ∀ k, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, i.val < k → g (x i) ∈ M := by
    intro k
    induction k with
    | zero => intro _; exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgM⟩ := ih (by omega)
      have hg' : ∀ a b, h (g a) (g b) = h a b := hg
      have hne : ∀ i : Fin n, i.val < k → i ≠ ⟨k, hk⟩ := by
        intro i hi e
        rw [e] at hi
        exact lt_irrefl _ hi
      let y : {i : Fin n // i.val < k} → V := fun i => g (x i.1)
      have hyo : ∀ i j : {i : Fin n // i.val < k}, i ≠ j → h (y i) (y j) = 0 := by
        intro i j hij
        simp only [y]
        rw [hg']
        exact hxo _ _ (fun e => hij (Subtype.ext e))
      have hyu : ∀ i : {i : Fin n // i.val < k}, IsUnitIn S (h (y i) (y i)) := by
        intro i
        simp only [y]
        rw [hg']
        exact hxu _
      have hyM : ∀ i : {i : Fin n // i.val < k}, y i ∈ M := fun i => hgM i.1 i.2
      have hu := hxu ⟨k, hk⟩
      have hus : star (h (x ⟨k, hk⟩) (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩) := star_h hs _ _
      have hrr : h (g (x ⟨k, hk⟩)) (g (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩) := hg' _ _
      have hrx : ∀ i : {i : Fin n // i.val < k}, h (y i) (g (x ⟨k, hk⟩)) = 0 := by
        intro i
        simp only [y]
        rw [hg']
        exact hxo _ _ (hne i.1 i.2)
      obtain ⟨z, hzM, hzz, hzo⟩ := exists_of_ref hS hs hM y hyo hyu hyM hu hus hrr hrx
      obtain ⟨τ, hτ, hτr, hτfix⟩ := exists_isom_move hS hs hu.1 hus hrr hzz
      refine ⟨τ * g, mul_mem hτ hg, fun i hi => ?_⟩
      show τ (g (x i)) ∈ M
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
      · rw [hτfix]
        · exact hgM i h1
        · rw [hg']
          exact hxo _ _ (fun e => hne i h1 e.symm)
        · rw [← star_h hs]
          have := hzo ⟨i, h1⟩
          simp only [y] at this
          rw [this, star_zero]
      · have : i = ⟨k, hk⟩ := Fin.ext h1
        rw [this, hτr]
        exact hzM
  obtain ⟨g, hg, hgM⟩ := P n le_rfl
  exact ⟨g, hg, fun i => hgM i i.isLt⟩

/- English proof (translation)
Take `⟨x, hxL, hxo, hxu⟩` from `exists_ortho_unit hS hs hnd hPU hL`. Take `⟨g, hg, hgM⟩` from `exists_isom_frameU hS hs hM x hxo hxu`. Establish `hg' : ∀ a b, h (g a) (g b) = h a b` using `hg`. Establish `hli` using `linIndep_orth x hxo (fun i => (hxu i).1)`. Establish `hspan : Submodule.span K (Set.range x) = ⊤`.

Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[finrank_span_eq_card hli, Fintype.card_fin]`. Establish `hexp : ∀ v, v = ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i`. Introduce `v`. Establish `hxv'` using `orth_sub_proj x hxo (fun i => (hxu i).1) v`.

Establish `hall : ∀ y, h y (v - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i) = 0`. Introduce `y`. Establish `hy : y ∈ Submodule.span K (Set.range x)` using `by rw [hspan]; trivial`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem a ha`.

Take `⟨j, rfl⟩` from `ha`. Conclude with `hxv' j`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp [ha, hb]`. Consider the case `smul c a _ ha => simp [ha]`.

Conclude with `sub_eq_zero.1 (hnd.2 _ hall)`. Establish `hfwd : ∀ v, v ∈ L → g v ∈ M`. Introduce `v hv`. Rewrite using `[hexp v, map_sum]`. Use `M.sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul]`. Conclude with `hM.smul_mem _ (S.mul_mem (hxu i).2.2 (hL.int _ (hxL i) _ hv)) _ (hgM i)`. Use `⟨g, hg, fun v => ⟨hfwd v, fun hv => hL.dual v fun m hm => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hg']`. Conclude with `hM.int _ (hfwd m hm) _ hv`.
-/
theorem exists_isom_selfDual [FiniteDimensional K V] (hS : IsHermSemilocal S) (hs : h.IsSymm)
    (hnd : h.Nondegenerate) (hPU : PairUnit S h) {L M : AddSubgroup V} (hL : IsSelfDualMod S h L)
    (hM : IsSelfDualMod S h M) : ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ v, v ∈ L ↔ g v ∈ M := by
  classical
  obtain ⟨x, hxL, hxo, hxu⟩ := exists_ortho_unit hS hs hnd hPU hL
  obtain ⟨g, hg, hgM⟩ := exists_isom_frameU hS hs hM x hxo hxu
  have hg' : ∀ a b, h (g a) (g b) = h a b := hg
  have hli := linIndep_orth x hxo (fun i => (hxu i).1)
  have hspan : Submodule.span K (Set.range x) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hexp : ∀ v, v = ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i := by
    intro v
    have hxv' := orth_sub_proj x hxo (fun i => (hxu i).1) v
    have hall : ∀ y, h y (v - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i) = 0 := by
      intro y
      have hy : y ∈ Submodule.span K (Set.range x) := by rw [hspan]; trivial
      induction hy using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨j, rfl⟩ := ha
        exact hxv' j
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul c a _ ha => simp [ha]
    exact sub_eq_zero.1 (hnd.2 _ hall)
  have hfwd : ∀ v, v ∈ L → g v ∈ M := by
    intro v hv
    rw [hexp v, map_sum]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul]
    exact hM.smul_mem _ (S.mul_mem (hxu i).2.2 (hL.int _ (hxL i) _ hv)) _ (hgM i)
  refine ⟨g, hg, fun v => ⟨hfwd v, fun hv => hL.dual v fun m hm => ?_⟩⟩
  rw [← hg']
  exact hM.int _ (hfwd m hm) _ hv

end Abs

end PI.UnitaryGroupMassFormula.CntFormula.UG
