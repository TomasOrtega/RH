import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomKillHighOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

/- English proof (translation)
Establish `hX : ∀ n i, evA k (y n) (hy n) (X i) = y n i`. Introduce `n i`. Express the relevant statement in the definitionally equal form `constantCoeff (substAlgHom (R := k) (a := fun i => (C (y n i) : MvPowerSeries Empty (B n))) (hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hy n i) (X i)) = _`. Rewrite using `[substAlgHom_X, constantCoeff_C]`. Establish `hres : ∀ n f, r n (evA k (y (n + 1)) (hy (n + 1)) f) = evA k (y n) (hy n) f` using `fun n f => (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ (B (n + 1))).2 (B n) (r n) _ _ _ _ (hr n) f`.

Establish `hdown : ∀ n m, n ≤ m → ∀ f, evA k (y m) (hy m) f = b m → evA k (y n) (hy n) f = b n`. Introduce `n m h`. Proceed by induction on `m, h using Nat.le_induction with`. Consider the case `base => exact fun _ h => h`. Consider the case `succ m _ ih`.

Introduce `f hf`. Conclude with `ih f (by rw [← hres, hf, hb])`. Use `choose F hF using fun n => hP.1 n (b n)`. Use `choose ν hν using hP.2`. Establish `hcoef : ∀ (α : σ →₀ ℕ) (g g' : MvPowerSeries σ k), evA k (y _) (hy (ν (α.degree + 1))) g = b _ → evA k (y _) (hy (ν (α.degree + 1))) g' = b _ → coeff α g = coeff α g'`.

Introduce `α g g' h h'`. Use `hν (α.degree + 1) (g - g') (by rw [map_sub, h, h', sub_self]) α (Nat.lt_succ_self _)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Set `f : MvPowerSeries σ k` to `fun α => coeff α (F (ν (α.degree + 1)))`. Establish `hf : ∀ α, coeff α f = coeff α (F (ν (α.degree + 1)))` using `fun _ => rfl`.

Use `⟨f, fun n => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨N, hN⟩` from `GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ (B n) (evA k (y n) (hy n)) fun i => by`. Rewrite using `[hX]`. Conclude with `hy n i`. Set `m` to `max n ((Finset.range (N + 1)).sup ν)`.

Establish `h0` using `hN (f - F m) fun α hα => by`. Rewrite using `[map_sub, hf, sub_eq_zero]`. Use `hcoef α _ _ (hF _) (hdown _ m ?_ _ (hF m))` and prove the remaining obligations. Conclude with `le_max_of_le_right (Finset.le_sup (f := ν) (Finset.mem_range.2 (by omega)))`. Rewrite `h0` using `[map_sub, sub_eq_zero]`.

Rewrite using `[h0]`. Conclude with `hdown n m (le_max_left _ _) _ (hF m)`. Use extensionality with `α`. Rewrite using `[hf]`. Conclude with `hcoef α _ _ (hg _) (hF _)`.
-/
theorem existsUnique_evA_eq_of_presents (k : Type) [CommRing k] (σ : Type) [Finite σ]
    (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, Algebra k (B n)] (y : ∀ n, σ → B n)
    (hy : ∀ n i, IsNilpotent (y n i)) (r : ∀ n, B (n + 1) →ₐ[k] B n)
    (hr : ∀ n i, r n (y (n + 1) i) = y n i) (hP : Presents k y hy) (b : ∀ n, B n)
    (hb : ∀ n, r n (b (n + 1)) = b n) :
    ∃! f : MvPowerSeries σ k, ∀ n, evA k (y n) (hy n) f = b n := by
  classical
  have hX : ∀ n i, evA k (y n) (hy n) (X i) = y n i := by
    intro n i
    change constantCoeff (substAlgHom (R := k) (a := fun i => (C (y n i) : MvPowerSeries Empty (B n)))
      (hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hy n i) (X i)) = _
    rw [substAlgHom_X, constantCoeff_C]
  have hres : ∀ n f, r n (evA k (y (n + 1)) (hy (n + 1)) f) = evA k (y n) (hy n) f := fun n f =>
    (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ (B (n + 1))).2 (B n) (r n) _ _ _ _ (hr n) f
  have hdown : ∀ n m, n ≤ m → ∀ f, evA k (y m) (hy m) f = b m → evA k (y n) (hy n) f = b n := by
    intro n m h
    induction m, h using Nat.le_induction with
    | base => exact fun _ h => h
    | succ m _ ih =>
      intro f hf
      exact ih f (by rw [← hres, hf, hb])
  choose F hF using fun n => hP.1 n (b n)
  choose ν hν using hP.2
  have hcoef : ∀ (α : σ →₀ ℕ) (g g' : MvPowerSeries σ k),
      evA k (y _) (hy (ν (α.degree + 1))) g = b _ → evA k (y _) (hy (ν (α.degree + 1))) g' = b _ →
      coeff α g = coeff α g' := by
    intro α g g' h h'
    have := hν (α.degree + 1) (g - g') (by rw [map_sub, h, h', sub_self]) α (Nat.lt_succ_self _)
    rwa [map_sub, sub_eq_zero] at this
  let f : MvPowerSeries σ k := fun α => coeff α (F (ν (α.degree + 1)))
  have hf : ∀ α, coeff α f = coeff α (F (ν (α.degree + 1))) := fun _ => rfl
  refine ⟨f, fun n => ?_, fun g hg => ?_⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ (B n) (evA k (y n) (hy n)) fun i => by
      rw [hX]; exact hy n i
    let m := max n ((Finset.range (N + 1)).sup ν)
    have h0 := hN (f - F m) fun α hα => by
      rw [map_sub, hf, sub_eq_zero]
      refine hcoef α _ _ (hF _) (hdown _ m ?_ _ (hF m))
      exact le_max_of_le_right (Finset.le_sup (f := ν) (Finset.mem_range.2 (by omega)))
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    exact hdown n m (le_max_left _ _) _ (hF m)
  · ext α
    rw [hf]
    exact hcoef α _ _ (hg _) (hF _)

end Katz

end GlobalTheory
