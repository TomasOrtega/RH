import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge

open Polynomial

/- English proof (translation)
Distinguish the cases in `h0 : g = 0`. Simplify using `[h0]`. Establish `hprod : (∏ s, (X - C (b s))) = ((Finset.univ.val.map b).map (fun t => X - C t)).prod`. Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression.

Rewrite using `[hprod, Multiset.prod_X_sub_C_dvd_iff_le_roots h0]`. Rewrite using `[Multiset.le_iff_subset (Multiset.Nodup.map hb Finset.univ.nodup)]`. Introduce `t ht`. Take `⟨s, -, rfl⟩` from `Multiset.mem_map.1 ht`. Conclude with `(mem_roots h0).2 (hg s)`.
-/
theorem prod_X_sub_C_dvd_of_eval_zero {O S : Type} [CommRing O] [IsDomain O] [Fintype S]
    (b : S → O) (hb : Function.Injective b) (g : O[X]) (hg : ∀ s, g.eval (b s) = 0) :
    (∏ s, (X - C (b s))) ∣ g := by
  by_cases h0 : g = 0
  · simp [h0]
  have hprod : (∏ s, (X - C (b s))) = ((Finset.univ.val.map b).map (fun t => X - C t)).prod := by
    rw [Multiset.map_map]; rfl
  rw [hprod, Multiset.prod_X_sub_C_dvd_iff_le_roots h0]
  rw [Multiset.le_iff_subset (Multiset.Nodup.map hb Finset.univ.nodup)]
  intro t ht
  obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 ht
  exact (mem_roots h0).2 (hg s)

/- English proof (translation)
Introduce `ha`. Establish `hinj : Function.Injective (liftA hv a)`. Introduce `s t hst`. Apply `ha` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use `congrArg (fun u : Int0 v => (u : C)) hst` as an intermediate fact. Conclude with `this`. Establish `key : ∀ x : Fin N → RS (liftA hv a), evalVec (liftA hv a) N x = 0 → x = 0`. Introduce `x hx`. Use function extensionality and compare the values at `i`.

Take `⟨g, hg⟩` from `AdjoinRoot.mk_surjective (x i)`. Rewrite using `[Pi.zero_apply, ← hg, AdjoinRoot.mk_eq_zero]`. Apply `prod_X_sub_C_dvd_of_eval_zero _ hinj` to reduce the goal to its premises. Introduce `s`. Establish `h1` using `congrFun (congrFun hx s) i`.

Simplify using `only [evalVec, Pi.zero_apply, ← hg] at h1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[show ((0 : Int0 v) : C) = 0 from rfl, ← h1]`. Use `congr 1`. Introduce `x y hxy`.

Use `key (x - y) (by rw [evalVec_sub, hxy, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem evalVec_injective_of_injective (C : Type) [Field C] (w : Valuation C ℝ≥0)
    (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring)
    (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) :
    Function.Injective a → Function.Injective (evalVec (liftA hv a) N) := by
  intro ha
  have hinj : Function.Injective (liftA hv a) := by
    intro s t hst
    apply ha
    apply Subtype.ext
    have := congrArg (fun u : Int0 v => (u : C)) hst
    exact this
  have key : ∀ x : Fin N → RS (liftA hv a), evalVec (liftA hv a) N x = 0 → x = 0 := by
    intro x hx
    funext i
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x i)
    rw [Pi.zero_apply, ← hg, AdjoinRoot.mk_eq_zero]
    apply prod_X_sub_C_dvd_of_eval_zero _ hinj
    intro s
    have h1 := congrFun (congrFun hx s) i
    simp only [evalVec, Pi.zero_apply, ← hg] at h1
    apply Subtype.ext
    rw [show ((0 : Int0 v) : C) = 0 from rfl, ← h1]
    congr 1
  intro x y hxy
  have := key (x - y) (by rw [evalVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 this

end GlobalTheory.HerbrandBridge
