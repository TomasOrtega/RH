import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSumPowOfCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntryMemSubringOfTraceGramUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTracePowGramNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfPowBddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesOfIsCompactClosureZpowersUnitaryStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodCpt

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> simp [O.one_mem, O.zero_mem]`. Consider the case `succ k ih`. Introduce `i j`.

Rewrite using `[pow_succ, Matrix.mul_apply]`. Conclude with `O.sum_mem fun m _ => O.mul_mem (ih i m) (hM m j)`.
-/
theorem pow_mem_of_mem {K : Type} [Field K] (O : Subring K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : ∀ i j, M i j ∈ O) : ∀ k : ℕ, ∀ i j, (M ^ k) i j ∈ O := by
  intro k
  induction k with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> simp [O.one_mem, O.zero_mem]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact O.sum_mem fun m _ => O.mul_mem (ih i m) (hM m j)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, ← Matrix.map_pow, Matrix.trace, Matrix.trace, map_sum]`. Both sides reduce to the same expression.
-/
theorem gram_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (g : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun i j : Fin n => ((g.map f) ^ ((i : ℕ) + j)).trace) =
      (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f := by
  ext i j
  rw [Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, ← Matrix.map_pow, Matrix.trace, Matrix.trace, map_sum]
  rfl

/- English proof (translation)
Introduce `E _ _ _ hU n γ hs`. Use `set g : Matrix (Fin n) (Fin n) E := γ.1.val with hgdef`. Use `set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace with hGdef`. Establish `hd : G.det ≠ 0` using `GlobalTheory.T.det_trace_pow_matrix_ne_zero_of_separable g hs`. Establish `h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E (g i j) ≤ 1`.

Simplify using `only [Filter.eventually_all]`. Conclude with `fun i j => GlobalTheory.LocRatPt.eventually_valuation_le_one _`. Use `filter_upwards [h1, GlobalTheory.LocRatPt.eventually_valuation_le_one (E := E) G.det⁻¹] with w hg hdi`. Use `set f : E →+* w.adicCompletion E := algebraMap E (w.adicCompletion E)`. Use `set gw : Matrix (Fin n) (Fin n) (w.adicCompletion E) := g.map f with hgw`.

Establish `hgwO : ∀ i j, gw i j ∈ Ov E w` using `fun i j => GlobalTheory.LocRatPt.algebraMap_mem_Ov (hg i j)`. Establish `hsep : gw.charpoly.Separable` using `by rw [hgw, Matrix.charpoly_map]; exact hs.map`. Establish `hGw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace) = G.map f` using `gram_map f g`. Establish `hdet : (G.map f).det = f G.det` using `(RingHom.map_det f G).symm`. Establish `hdw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det ≠ 0`.

Rewrite using `[hGw, hdet]`. Conclude with `(map_ne_zero f).2 hd`. Establish `hdwi : ((Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ Ov E w`. Rewrite using `[hGw, hdet, ← map_inv₀]`. Conclude with `GlobalTheory.LocRatPt.algebraMap_mem_Ov hdi`.

Establish `hloc : (locPt w γ).1.1 = gw` using `by rw [GlobalTheory.LocRatPt.locPt_val hU]; rfl`. Establish `key : ∀ s : UL n w, s * locPt w γ = locPt w γ * s → (∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (s ^ k).1.1 i j ∈ Ov E w) → ∀ i j, s.1.1 i j ∈ Ov E w`. Introduce and unpack `s hs' ⟨a, ha, hb⟩`. Use `set x : Matrix (Fin n) (Fin n) (w.adicCompletion E) := s.1.1 with hx`. Establish `hxc : x * gw = gw * x`.

Use `congrArg (fun u : UL n w => u.1.1) hs'` as an intermediate fact. Simplify `this` using `[hloc]`. Establish `hpow : ∀ k : ℕ, (s ^ (k : ℤ)).1.1 = x ^ k`. Introduce `k`. Rewrite using `[zpow_natCast]`.

Simplify using `[hx]`. Take `⟨c, hcx⟩` from `GlobalTheory.T.exists_eq_sum_smul_pow_of_commute_of_separable gw x hsep hxc`. Use `GlobalTheory.T.entry_mem_subring_of_trace_gram_unit (Ov E w) gw x c hcx hgwO (fun j => ?_) hdw hdwi` and prove the remaining obligations. Use `GlobalTheory.T.trace_mem_of_mul_pow_entries_mem E w n _ a ha fun k i l => ?_` and prove the remaining obligations. Establish `hcm : Commute x (gw ^ (j : ℕ))` using `(Commute.pow_right hxc (j : ℕ))`.

Rewrite using `[hcm.mul_pow, ← pow_mul, Matrix.mul_apply, Finset.mul_sum]`. Use `(Ov E w).sum_mem fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← hpow]`. Conclude with `(Ov E w).mul_mem (hb _ i m) (pow_mem_of_mem _ gw hgwO _ m l)`. Rewrite using `[cptPart, Subgroup.closure_le]`.

Introduce and unpack `t ⟨ht, hc⟩`. Establish `ht' : t * locPt w γ = locPt w γ * t` using `ht`. Take `⟨a, ha, hb⟩` from `GlobalTheory.T.bounded_entries_of_isCompact_closure_zpowers_unitary E n w t hc`. Establish `e1` using `key t ht' ⟨a, ha, hb⟩`. Establish `e2` using `key t⁻¹ ((show Commute t (locPt w γ) from ht').inv_left).eq ⟨a, ha, fun k i j => by rw [_root_.inv_zpow']; exact hb (-k) i j⟩`.

Rewrite using `[SetLike.mem_coe, KL, Subgroup.mem_subgroupOf]`. Conclude with `GlobalTheory.LocRatPt.mem_GLint_of_entries e1 (fun i j => by simpa using e2 i j)`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, cptPart (twCent (MonoidHom.id (UL n w)) (locPt w γ)) ≤ KL n w := by
  intro E _ _ _ hU n γ hs
  set g : Matrix (Fin n) (Fin n) E := γ.1.val with hgdef
  set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace with hGdef
  have hd : G.det ≠ 0 := GlobalTheory.T.det_trace_pow_matrix_ne_zero_of_separable g hs
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E (g i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => GlobalTheory.LocRatPt.eventually_valuation_le_one _
  filter_upwards [h1, GlobalTheory.LocRatPt.eventually_valuation_le_one (E := E) G.det⁻¹] with w hg hdi
  set f : E →+* w.adicCompletion E := algebraMap E (w.adicCompletion E)
  set gw : Matrix (Fin n) (Fin n) (w.adicCompletion E) := g.map f with hgw
  have hgwO : ∀ i j, gw i j ∈ Ov E w := fun i j => GlobalTheory.LocRatPt.algebraMap_mem_Ov (hg i j)
  have hsep : gw.charpoly.Separable := by rw [hgw, Matrix.charpoly_map]; exact hs.map
  have hGw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace) = G.map f := gram_map f g
  have hdet : (G.map f).det = f G.det := (RingHom.map_det f G).symm
  have hdw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
    rw [hGw, hdet]; exact (map_ne_zero f).2 hd
  have hdwi : ((Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ Ov E w := by
    rw [hGw, hdet, ← map_inv₀]; exact GlobalTheory.LocRatPt.algebraMap_mem_Ov hdi
  have hloc : (locPt w γ).1.1 = gw := by rw [GlobalTheory.LocRatPt.locPt_val hU]; rfl
  have key : ∀ s : UL n w, s * locPt w γ = locPt w γ * s →
      (∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (s ^ k).1.1 i j ∈ Ov E w) →
      ∀ i j, s.1.1 i j ∈ Ov E w := by
    rintro s hs' ⟨a, ha, hb⟩
    set x : Matrix (Fin n) (Fin n) (w.adicCompletion E) := s.1.1 with hx
    have hxc : x * gw = gw * x := by
      have := congrArg (fun u : UL n w => u.1.1) hs'
      simpa [hloc] using this
    have hpow : ∀ k : ℕ, (s ^ (k : ℤ)).1.1 = x ^ k := by
      intro k; rw [zpow_natCast]; simp [hx]
    obtain ⟨c, hcx⟩ := GlobalTheory.T.exists_eq_sum_smul_pow_of_commute_of_separable gw x hsep hxc
    refine GlobalTheory.T.entry_mem_subring_of_trace_gram_unit (Ov E w) gw x c hcx hgwO (fun j => ?_) hdw hdwi
    refine GlobalTheory.T.trace_mem_of_mul_pow_entries_mem E w n _ a ha fun k i l => ?_
    have hcm : Commute x (gw ^ (j : ℕ)) := (Commute.pow_right hxc (j : ℕ))
    rw [hcm.mul_pow, ← pow_mul, Matrix.mul_apply, Finset.mul_sum]
    refine (Ov E w).sum_mem fun m _ => ?_
    rw [← mul_assoc, ← hpow]
    exact (Ov E w).mul_mem (hb _ i m) (pow_mem_of_mem _ gw hgwO _ m l)
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, hc⟩
  have ht' : t * locPt w γ = locPt w γ * t := ht
  obtain ⟨a, ha, hb⟩ := GlobalTheory.T.bounded_entries_of_isCompact_closure_zpowers_unitary E n w t hc
  have e1 := key t ht' ⟨a, ha, hb⟩
  have e2 := key t⁻¹ ((show Commute t (locPt w γ) from ht').inv_left).eq
    ⟨a, ha, fun k i j => by rw [_root_.inv_zpow']; exact hb (-k) i j⟩
  rw [SetLike.mem_coe, KL, Subgroup.mem_subgroupOf]
  exact GlobalTheory.LocRatPt.mem_GLint_of_entries e1 (fun i j => by simpa using e2 i j)

end GlobalTheory.BCT.GoodCpt
