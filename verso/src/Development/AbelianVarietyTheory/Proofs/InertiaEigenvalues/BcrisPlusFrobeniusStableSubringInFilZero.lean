import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.CrisPlus

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

/- English proof (translation)
Take `⟨N, x, hx⟩` from `h`. Use `⟨N, GlobalTheory.MemLoc.phiA l x, ?_⟩` and prove the remaining obligations. Establish `e : (l : P.R.B) ^ N * P.φB b = P.φB ((l : P.R.B) ^ N * b)`. Rewrite using `[map_mul, map_pow, map_natCast]`. Rewrite using `[e, T.frob, hx]`.

Conclude with `GlobalTheory.CrisMaps.φB_phiA l x`.
-/
theorem plus_phi {b : P.R.B} (h : Plus T b) : Plus T (P.φB b) := by
  obtain ⟨N, x, hx⟩ := h
  refine ⟨N, GlobalTheory.MemLoc.phiA l x, ?_⟩
  have e : (l : P.R.B) ^ N * P.φB b = P.φB ((l : P.R.B) ^ N * b) := by
    rw [map_mul, map_pow, map_natCast]
  rw [e, T.frob, hx]
  exact GlobalTheory.CrisMaps.φB_phiA l x

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact h`. Consider the case `succ j ih => rw [Function.iterate_succ_apply']`. Conclude with `plus_phi T ih`.
-/
theorem plus_iterate {b : P.R.B} (h : Plus T b) (j : ℕ) : Plus T (P.φB^[j] b) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact plus_phi T ih

/- English proof (translation)
Take `⟨N, x, hx⟩` from `ha`. Take `⟨M, y, hy⟩` from `hb`. Use `⟨⟨N + M, (l : Formalism.Per.Acris l) ^ M * x + (l : Formalism.Per.Acris l) ^ N * y, ?_⟩, ⟨N + M, x * y, ?_⟩⟩` and prove the remaining obligations. Establish `e : (l : P.R.B) ^ (N + M) * (a + b) = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * a) + (l : P.R.B) ^ N * ((l : P.R.B) ^ M * b)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, map_add, map_mul T.eB ((l : P.R.B) ^ M) ((l : P.R.B) ^ N * a), map_mul T.eB ((l : P.R.B) ^ N) ((l : P.R.B) ^ M * b), hx, hy]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Establish `e : (l : P.R.B) ^ (N + M) * (a * b) = ((l : P.R.B) ^ N * a) * ((l : P.R.B) ^ M * b)` using `by ring`. Rewrite using `[e, map_mul, hx, hy, map_mul]`.
-/
theorem plus_add_mul {a b : P.R.B} (ha : Plus T a) (hb : Plus T b) : Plus T (a + b) ∧ Plus T (a * b) := by
  obtain ⟨N, x, hx⟩ := ha
  obtain ⟨M, y, hy⟩ := hb
  refine ⟨⟨N + M, (l : Formalism.Per.Acris l) ^ M * x + (l : Formalism.Per.Acris l) ^ N * y, ?_⟩, ⟨N + M, x * y, ?_⟩⟩
  · have e : (l : P.R.B) ^ (N + M) * (a + b) = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * a) + (l : P.R.B) ^ N * ((l : P.R.B) ^ M * b) := by
      ring
    rw [e, map_add, map_mul T.eB ((l : P.R.B) ^ M) ((l : P.R.B) ^ N * a),
      map_mul T.eB ((l : P.R.B) ^ N) ((l : P.R.B) ^ M * b), hx, hy]
    simp only [map_add, map_mul, map_pow, map_natCast]
  · have e : (l : P.R.B) ^ (N + M) * (a * b) = ((l : P.R.B) ^ N * a) * ((l : P.R.B) ^ M * b) := by ring
    rw [e, map_mul, hx, hy, map_mul]

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Take `⟨N, hN⟩` from `pow_unbounded_of_one_lt ‖q‖ hl`. Establish `hz : ‖(l : ℚ_[l]) ^ N * q‖ ≤ 1`. Rewrite using `[norm_mul, Padic.norm_p_pow]`. Establish `hp : (0 : ℝ) < (l : ℝ) ^ N` using `by positivity`.

Rewrite using `[zpow_neg, zpow_natCast]`. Rewrite using `[inv_mul_le_iff₀ hp, mul_one]`. Conclude with `hN.le`. Set `z : ℤ_[l]` to `⟨(l : ℚ_[l]) ^ N * q, hz⟩`. Use `⟨N, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.zA l z), ?_⟩` and prove the remaining obligations.

Establish `e : (l : P.R.B) ^ N * algebraMap ℚ_[l] P.R.B q = algebraMap ℚ_[l] P.R.B (z : ℚ_[l])`. Express the relevant statement in the definitionally equal form `_ = algebraMap ℚ_[l] P.R.B ((l : ℚ_[l]) ^ N * q)`. Rewrite using `[map_mul, map_pow, map_natCast]`. Rewrite using `[e, T.zB, GlobalTheory.RingIface.zB_eq_aB_zA l z, GlobalTheory.RingIface.aB_eq_alg l]`.
-/
theorem plus_alg (q : ℚ_[l]) : Plus T (algebraMap ℚ_[l] P.R.B q) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖q‖ hl
  have hz : ‖(l : ℚ_[l]) ^ N * q‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow]
    have hp : (0 : ℝ) < (l : ℝ) ^ N := by positivity
    rw [zpow_neg, zpow_natCast]
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact hN.le
  let z : ℤ_[l] := ⟨(l : ℚ_[l]) ^ N * q, hz⟩
  refine ⟨N, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.zA l z), ?_⟩
  have e : (l : P.R.B) ^ N * algebraMap ℚ_[l] P.R.B q = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
    change _ = algebraMap ℚ_[l] P.R.B ((l : ℚ_[l]) ^ N * q)
    rw [map_mul, map_pow, map_natCast]
  rw [e, T.zB, GlobalTheory.RingIface.zB_eq_aB_zA l z, GlobalTheory.RingIface.aB_eq_alg l]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) x, by rw [pow_zero, one_mul, RingEquiv.apply_symm_apply]; exact GlobalTheory.RingIface.aB_eq_alg l x⟩`.
-/
theorem plus_ainf (x : Formalism.Per.Ainf l) : Plus T (T.eB.symm (Formalism.Per.aB l x)) :=
  ⟨0, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) x, by rw [pow_zero, one_mul, RingEquiv.apply_symm_apply]; exact GlobalTheory.RingIface.aB_eq_alg l x⟩

/- English proof (translation)
Take `⟨C, hC⟩` from `GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T`. Conclude with `⟨0, C.t, by rw [pow_zero, one_mul, hC.t]; rfl⟩`.
-/
theorem plus_alt : Plus T P.tB := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  exact ⟨0, C.t, by rw [pow_zero, one_mul, hC.t]; rfl⟩

/- English proof (translation)
Take `⟨C, hC⟩` from `GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T`. Take `⟨N, x, hx⟩` from `h`. Take `⟨u, hu⟩` from `(GlobalTheory.MemLoc.isUnit_l_BdRp l).exists_left_inv`. Establish `e1 : T.eD (P.ιB ((l : P.R.B) ^ N * b)) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (C.j x)`. Rewrite using `[hC.ι, hx, C.ι_j]`.

Simplify using `only [map_mul, map_pow, map_natCast] at e1`. Establish `e2 : T.eD (P.ιB b) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N * C.j x)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_natCast (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)) l, ← map_mul, hu, map_one, one_pow, one_mul]`. Use `_ = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N) * ((l : Formalism.Per.BdR l) ^ N * T.eD (P.ιB b)) := by`.

Rewrite using `[map_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [e1, ← map_mul]`. Use `show P.ιB b ∈ (P.PD (botExt l)).Fil 0`. Use `(T.fil (botExt l) 0 _).2 ?_` and prove the remaining obligations.

Rewrite using `[e2]`. Conclude with `GlobalTheory.RingIface.alg_mem_FilD_zero l _`.
-/
theorem plus_fil {b : P.R.B} (h : Plus T b) : P.ιB b ∈ Fil P 0 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨N, x, hx⟩ := h
  obtain ⟨u, hu⟩ := (GlobalTheory.MemLoc.isUnit_l_BdRp l).exists_left_inv
  have e1 : T.eD (P.ιB ((l : P.R.B) ^ N * b)) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (C.j x) := by
    rw [hC.ι, hx, C.ι_j]
  simp only [map_mul, map_pow, map_natCast] at e1
  have e2 : T.eD (P.ιB b) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N * C.j x) := by
    calc T.eD (P.ιB b)
        = (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) u * (l : Formalism.Per.BdR l)) ^ N * T.eD (P.ιB b) := by
          rw [← map_natCast (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)) l, ← map_mul, hu, map_one, one_pow, one_mul]
      _ = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N) * ((l : Formalism.Per.BdR l) ^ N * T.eD (P.ιB b)) := by
          rw [map_pow]; ring
      _ = _ := by rw [e1, ← map_mul]
  show P.ιB b ∈ (P.PD (botExt l)).Fil 0
  refine (T.fil (botExt l) 0 _).2 ?_
  rw [e2]
  exact GlobalTheory.RingIface.alg_mem_FilD_zero l _

/- English proof (translation)
Introduce `l _ P AI T`. Conclude with `⟨fun b h => plus_phi T h, fun b h j => plus_fil T (plus_iterate T h j), fun a b ha hb => plus_add_mul T ha hb, plus_alg T, plus_ainf T, plus_alt T⟩`.
-/
theorem plus_props : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    (∀ b, Plus T b → Plus T (P.φB b)) ∧ (∀ b, Plus T b → ∀ j, ev P j b ∈ Fil P 0) ∧
    (∀ a b, Plus T a → Plus T b → Plus T (a + b) ∧ Plus T (a * b)) ∧
    (∀ q : ℚ_[l], Plus T (algebraMap ℚ_[l] P.R.B q)) ∧
    (∀ x : Formalism.Per.Ainf l, Plus T (T.eB.symm (Formalism.Per.aB l x))) ∧ Plus T P.tB := by
  intro l _ P AI T
  exact ⟨fun b h => plus_phi T h, fun b h j => plus_fil T (plus_iterate T h j), fun a b ha hb => plus_add_mul T ha hb,
    plus_alg T, plus_ainf T, plus_alt T⟩

end GlobalTheory.PMon.CrisPlus
