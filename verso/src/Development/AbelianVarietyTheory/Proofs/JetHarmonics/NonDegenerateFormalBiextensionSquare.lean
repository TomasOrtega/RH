import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.RowLawSquare ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.NonDegSquare

section Series

variable {C : Type} [Field C] {σ τ : Type} {dd : ℕ}

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_eq_constantCoeff_apply, hf]`.
-/
theorem cc_kill (e : σ ↪ τ) {f : MvPowerSeries τ C} (hf : constantCoeff f = 0) :
    constantCoeff (killCompl e f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
    coeff_zero_eq_constantCoeff_apply, hf]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[coeff_killCompl, coeff_subst (hasSubst_of_constantCoeff_zero ha), coeff_subst (hasSubst_of_constantCoeff_zero fun k => cc_kill e (ha k))]`. Use `finsum_congr fun d => ?_` and prove the remaining obligations. Rewrite using `[← coeff_killCompl, map_finsuppProd]`. Simplify using `only [map_pow]`.
-/
theorem kill_subst {κ : Type} [Finite κ] (e : σ ↪ τ) {a : κ → MvPowerSeries τ C}
    (ha : Zc a) (H : MvPowerSeries κ C) :
    killCompl e (subst a H) = subst (fun k => killCompl e (a k)) H := by
  ext x
  rw [coeff_killCompl, coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero fun k => cc_kill e (ha k))]
  refine finsum_congr fun d => ?_
  rw [← coeff_killCompl, map_finsuppProd]
  simp only [map_pow]

def kp (e : σ ↪ τ) {κ : Type} (a : κ → MvPowerSeries τ C) : κ → MvPowerSeries σ C := fun k => killCompl e (a k)

/- English proof (translation)
Introduce `k` and use `cc_kill e (ha k)`.
-/
theorem zc_kp (e : σ ↪ τ) {κ : Type} {a : κ → MvPowerSeries τ C} (ha : Zc a) : Zc (kp e a) :=
  fun k => cc_kill e (ha k)

/- English proof (translation)
Unfold `sb`. Rewrite using `[kill_subst e (a := fun p : Fin 2 × Fin dd => ![a, b] p.1 p.2) (fun p => zc2 ha hb p.1 p.2)]`. Use `congr 1`. Use function extensionality and compare the values at `⟨j, i⟩`. Apply the tactic sequence `fin_cases j <;> rfl`.
-/
theorem killCompl_substPointsPowerSeries_two (e : σ ↪ τ) {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (f : PS C 2 dd) :
    killCompl e (sb ![a, b] f) = sb ![kp e a, kp e b] f := by
  unfold sb
  rw [kill_subst e (a := fun p : Fin 2 × Fin dd => ![a, b] p.1 p.2) (fun p => zc2 ha hb p.1 p.2)]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> rfl

/- English proof (translation)
Introduce `_` and use `map_zero _`.
-/
theorem zc_zero {κ : Type} : Zc (0 : κ → MvPowerSeries τ C) := fun _ => map_zero _

/- English proof (translation)
Use `sb_sub ha 0 0` as an intermediate fact. Rewrite `this` using `[sub_self, sub_self]`. Then use the resulting hypothesis.
-/
theorem sb_zero {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) :
    sb a (0 : PS C n dd) = 0 := by
  have := sb_sub ha 0 0
  rwa [sub_self, sub_self] at this

/- English proof (translation)
The claim follows from `funext fun _ => sb_zero ha`.
-/
theorem sb_zero' {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) :
    (fun i => sb a ((0 : Pt C n dd) i)) = 0 := funext fun _ => sb_zero ha

def emb (dd : ℕ) {n : ℕ} (s : Fin n → Fin 2) : Fin n × Fin dd ↪ Fin n × (Fin 2 × Fin dd) :=
  ⟨fun q => (q.1, (s q.1, q.2)), fun q q' h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.2⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `killCompl_X (e := emb dd s) (j, i)`. Use `killCompl_X_eq_zero ?_` and prove the remaining obligations.

Introduce and unpack `⟨⟨j', i'⟩, hq⟩`. Express the relevant statement in the definitionally equal form `(j', (s j', i')) = (j, (k, i)) at hq`. Simplify using `only [Prod.mk.injEq] at hq`. Take `⟨rfl, h2, _⟩` from `hq`. Conclude with `h h2`.
-/
theorem kp_gp {n : ℕ} (s : Fin n → Fin 2) (j : Fin n) (k : Fin 2) :
    kp (emb dd s) (colOf (gp C (Fin 2 × Fin dd) j) k) = if s j = k then pt C dd j else 0 := by
  funext i
  split_ifs with h
  · subst h
    exact killCompl_X (e := emb dd s) (j, i)
  · refine killCompl_X_eq_zero ?_
    rintro ⟨⟨j', i'⟩, hq⟩
    change (j', (s j', i')) = (j, (k, i)) at hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, h2, _⟩ := hq
    exact h h2

/- English proof (translation)
Establish `h0 : constantCoeff D = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Conclude with `hD 0 (by simp)`. Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), finsum_eq_single _ 1]`. Simplify using `[PowerSeries.coeff_exp]`.

Introduce `k hk`. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Rewrite using `[pow_zero, coeff_one, if_neg, smul_zero]`. Introduce and unpack `rfl`. Simplify using `at hm`.

Rewrite using `[coeff_eq_zero_of_lt_weightedOrder w, smul_zero]`. Use `lt_of_lt_of_le ?_ (le_weightedOrder_pow w k)` and prove the remaining obligations. Establish `h1` using `nat_le_weightedOrder w hD`. Use `lt_of_lt_of_le ?_ (nsmul_le_nsmul_right h1 k)` and prove the remaining obligations. Rewrite using `[hm, nsmul_eq_mul, ← Nat.cast_mul]`.

Conclude with `(by omega : 1 < k * 1)` after adjusting the coercions.
-/
theorem coeff_exp_lin [CharZero C] (w : τ → ℕ) {D : MvPowerSeries τ C}
    (hD : ∀ m, Finsupp.weight w m < 1 → coeff m D = 0) {m : τ →₀ ℕ} (hm : Finsupp.weight w m = 1) :
    coeff m (PowerSeries.subst D (PowerSeries.exp C)) = coeff m D := by
  classical
  have h0 : constantCoeff D = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hD 0 (by simp)
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), finsum_eq_single _ 1]
  · simp [PowerSeries.coeff_exp]
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, coeff_one, if_neg, smul_zero]
      rintro rfl
      simp at hm
    · rw [coeff_eq_zero_of_lt_weightedOrder w, smul_zero]
      refine lt_of_lt_of_le ?_ (le_weightedOrder_pow w k)
      have h1 := nat_le_weightedOrder w hD
      refine lt_of_lt_of_le ?_ (nsmul_le_nsmul_right h1 k)
      rw [hm, nsmul_eq_mul, ← Nat.cast_mul]
      exact_mod_cast (by omega : 1 < k * 1)

def inj (col : Fin 2) (a : Fin dd → MvPowerSeries τ C) : Fin 2 × Fin dd → MvPowerSeries τ C :=
  fun x => (if col = x.1 then a else 0) x.2

/- English proof (translation)
Introduce `x` and use `by unfold inj split_ifs exacts [ha _, map_zero _]`.
-/
theorem zc_inj (col : Fin 2) {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) : Zc (inj col a) := fun x => by
  unfold inj
  split_ifs
  exacts [ha _, map_zero _]

/- English proof (translation)
Establish `h` using `zc1 ha`. Use `show subst _ _ = _`. Rewrite using `[subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (zc_inj col (zc_pt _))) (hasSubst_sb h)]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Unfold `inj`. Use `split_ifs`. Conclude with `sb_pt h 0 x.2`. Conclude with `sb_zero h`.
-/
theorem ev_inj {n : ℕ} (col : Fin 2) {a : Pt C n dd} (ha : Zc a) (b : MvPowerSeries (Fin 2 × Fin dd) C) :
    ev ![a] (subst (inj col (pt C dd (0 : Fin 1))) b) = subst (inj col a) b := by
  have h := zc1 ha
  show subst _ _ = _
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (zc_inj col (zc_pt _))) (hasSubst_sb h)]
  congr 1
  funext x
  unfold inj
  split_ifs
  · exact sb_pt h 0 x.2
  · exact sb_zero h

end Series

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {σ τ : Type}

/- English proof (translation)
Establish `h` using `zc1 hb`. Establish `e` using `congrArg (sb ![b]) Y.gauge.ax0`. Rewrite `e` using `[substPointsPowerSeries_eval_two h zc_zero (zc_pt _), sb_zero' h, sb_pt' h, sb_zero h]`. Then use the resulting hypothesis.
-/
theorem h_zero_left {b : Fin dd → MvPowerSeries τ C} (hb : Zc b) : sb ![0, b] Y.h = 0 := by
  have h := zc1 hb
  have e := congrArg (sb ![b]) Y.gauge.ax0
  rwa [substPointsPowerSeries_eval_two h zc_zero (zc_pt _), sb_zero' h, sb_pt' h, sb_zero h] at e

/- English proof (translation)
Establish `h` using `zc1 hb`. Establish `e` using `congrArg (sb ![b]) Y.gauge.ax1`. Rewrite `e` using `[substPointsPowerSeries_eval_two h (zc_pt _) zc_zero, sb_zero' h, sb_pt' h, sb_zero h]`. Then use the resulting hypothesis.
-/
theorem h_zero_right {b : Fin dd → MvPowerSeries τ C} (hb : Zc b) : sb ![b, 0] Y.h = 0 := by
  have h := zc1 hb
  have e := congrArg (sb ![b]) Y.gauge.ax1
  rwa [substPointsPowerSeries_eval_two h (zc_pt _) zc_zero, sb_zero' h, sb_pt' h, sb_zero h] at e

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h` using `zc1 (zc_zero (C := C) (τ := τ) (κ := Fin dd))`. Establish `e` using `congrArg (sb ![(0 : Fin dd → MvPowerSeries τ C)]) (Y.B.G.unit i)`. Rewrite `e` using `[substPointsPowerSeries_eval_two h zc_zero (zc_pt _), sb_zero' h, sb_pt' h]`. Conclude with `e.trans (sb_pt h 0 i)`.
-/
theorem law_zero : law Y (0 : Fin dd → MvPowerSeries τ C) 0 = 0 := by
  funext i
  have h := zc1 (zc_zero (C := C) (τ := τ) (κ := Fin dd))
  have e := congrArg (sb ![(0 : Fin dd → MvPowerSeries τ C)]) (Y.B.G.unit i)
  rw [substPointsPowerSeries_eval_two h zc_zero (zc_pt _), sb_zero' h, sb_pt' h] at e
  exact e.trans (sb_pt h 0 i)

def dfc (a b c : Fin dd → MvPowerSeries τ C) : MvPowerSeries τ C :=
  sb ![a, b] Y.h + sb ![a, c] Y.h - sb ![a, law Y b c] Y.h

/- English proof (translation)
The claim follows from `funext fun _ => killCompl_substPointsPowerSeries_two e ha hb _`.
-/
theorem kp_law (e : σ ↪ τ) {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) :
    kp e (law Y a b) = law Y (kp e a) (kp e b) := funext fun _ => killCompl_substPointsPowerSeries_two e ha hb _

/- English proof (translation)
Unfold `dfc`. Rewrite using `[map_sub, map_add, killCompl_substPointsPowerSeries_two e ha hb, killCompl_substPointsPowerSeries_two e ha hc, killCompl_substPointsPowerSeries_two e ha (zc_law Y hb hc), kp_law Y e hb hc]`.
-/
theorem kill_dfc (e : σ ↪ τ) {a b c : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (hc : Zc c) :
    killCompl e (dfc Y a b c) = dfc Y (kp e a) (kp e b) (kp e c) := by
  unfold dfc
  rw [map_sub, map_add, killCompl_substPointsPowerSeries_two e ha hb, killCompl_substPointsPowerSeries_two e ha hc, killCompl_substPointsPowerSeries_two e ha (zc_law Y hb hc), kp_law Y e hb hc]

/- English proof (translation)
Unfold `dfc`. Rewrite using `[h_zero_left Y hb, h_zero_left Y hc, h_zero_left Y (zc_law Y hb hc), add_zero, sub_zero]`.
-/
theorem dfc_left {b c : Fin dd → MvPowerSeries τ C} (hb : Zc b) (hc : Zc c) : dfc Y 0 b c = 0 := by
  unfold dfc
  rw [h_zero_left Y hb, h_zero_left Y hc, h_zero_left Y (zc_law Y hb hc), add_zero, sub_zero]

/- English proof (translation)
Unfold `dfc`. Rewrite using `[law_zero, h_zero_right Y ha, add_zero, sub_zero]`.
-/
theorem dfc_right {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) : dfc Y a 0 0 = 0 := by
  unfold dfc
  rw [law_zero, h_zero_right Y ha, add_zero, sub_zero]

/- English proof (translation)
Establish `e` using `Y.gauge.ph2`. Rewrite `e` using `[FB.toK, map_self, FK_self]`. Conclude with `e`.
-/
theorem ph2_eq_subst_exp : Y.B.ph2 = PowerSeries.subst (dfc Y (pt C dd (0 : Fin 3)) (pt C dd 1) (pt C dd 2))
    (PowerSeries.exp C) := by
  have e := Y.gauge.ph2
  rw [FB.toK, map_self, FK_self] at e
  exact e

/- English proof (translation)
Use `Van.subst {s : Fin 2 × Fin dd | s.1 = 0} (fun s => zc2 ha hb s.1 s.2) ?_ (h_axes Y 0)` and prove the remaining obligations. Introduce and unpack `⟨j, i⟩ hs`. Take `rfl : j = 0` from `hs`. Conclude with `hT i`.
-/
theorem van_h {T : Set τ} {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (hT : ∀ i, Van T (a i)) :
    Van T (sb ![a, b] Y.h) := by
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = 0} (fun s => zc2 ha hb s.1 s.2) ?_ (h_axes Y 0)
  rintro ⟨j, i⟩ hs
  obtain rfl : j = 0 := hs
  exact hT i

/- English proof (translation)
Rewrite using `[ph2_eq_subst_exp]`. Use `coeff_exp_lin (fun q : Fin 3 × Fin dd => if q.1 = 0 then 1 else 0) ?_ ?_` and prove the remaining obligations. Introduce `m hm`. Establish `hs : ∀ s ∈ m.support, s ∉ {s : Fin 3 × Fin dd | s.1 = 0}`. Introduce `s hs h0`.

Establish `h0' : s.1 = 0` using `h0`. Rewrite `hm` using `[Nat.lt_one_iff, Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff]`. Use `hm s hs` as an intermediate fact. Simplify using `only [h0', if_true, smul_eq_mul, mul_one] at this`. Conclude with `Finsupp.mem_support_iff.1 hs this`.

Establish `hx : ∀ i, Van {s : Fin 3 × Fin dd | s.1 = 0} (pt C dd (0 : Fin 3) i)`. Introduce `i ν hν`. Rewrite using `[pt, coeff_X, if_neg]`. Introduce and unpack `rfl`. Conclude with `hν (0, i) (by simp) rfl`.

Unfold `dfc`. Rewrite using `[map_sub, map_add, van_h Y (zc_pt _) (zc_pt _) hx m hs, van_h Y (zc_pt _) (zc_pt _) hx m hs, van_h Y (zc_pt _) (zc_law Y (zc_pt _) (zc_pt _)) hx m hs, add_zero, sub_zero]`. Rewrite using `[map_add, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_smul _ _ _), Finsupp.weight_single]`. Simplify using `[Finsupp.sum, Fin.succ_ne_zero]`.
-/
theorem coeff_formalBiextensionChart_secondPhase (μ : Fin 2 × Fin dd →₀ ℕ) (i : Fin dd) :
    coeff (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2 =
      coeff (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1)
        (dfc Y (pt C dd (0 : Fin 3)) (pt C dd 1) (pt C dd 2)) := by
  classical
  rw [ph2_eq_subst_exp]
  refine coeff_exp_lin (fun q : Fin 3 × Fin dd => if q.1 = 0 then 1 else 0) ?_ ?_
  · intro m hm
    have hs : ∀ s ∈ m.support, s ∉ {s : Fin 3 × Fin dd | s.1 = 0} := by
      intro s hs h0
      have h0' : s.1 = 0 := h0
      rw [Nat.lt_one_iff, Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at hm
      have := hm s hs
      simp only [h0', if_true, smul_eq_mul, mul_one] at this
      exact Finsupp.mem_support_iff.1 hs this
    have hx : ∀ i, Van {s : Fin 3 × Fin dd | s.1 = 0} (pt C dd (0 : Fin 3) i) := by
      intro i ν hν
      rw [pt, coeff_X, if_neg]
      rintro rfl
      exact hν (0, i) (by simp) rfl
    unfold dfc
    rw [map_sub, map_add, van_h Y (zc_pt _) (zc_pt _) hx m hs, van_h Y (zc_pt _) (zc_pt _) hx m hs,
      van_h Y (zc_pt _) (zc_law Y (zc_pt _) (zc_pt _)) hx m hs, add_zero, sub_zero]
  · rw [map_add, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_smul _ _ _),
      Finsupp.weight_single]
    simp [Finsupp.sum, Fin.succ_ne_zero]

variable {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

/- English proof (translation)
Rewrite using `[hAt_eq Y p ha hb, hAt_eq Y p ha hc, hAt_eq Y p ha (zc_addP Y p hb hc), col_addP Y p hb hc, col_addP Y p hb hc, add_add_add_comm, add_sub_add_comm, Fin.sum_univ_two]`. Both sides reduce to the same expression.
-/
theorem dfc_square {a b c : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (hc : Zc c) :
    hAt (Y.rawSelf p) a b + hAt (Y.rawSelf p) a c - hAt (Y.rawSelf p) a (addP (Y.rawSelf p) b c) =
      ∑ k, dfc Y (colOf a k) (colOf b k) (colOf c k) := by
  rw [hAt_eq Y p ha hb, hAt_eq Y p ha hc, hAt_eq Y p ha (zc_addP Y p hb hc), col_addP Y p hb hc,
    col_addP Y p hb hc, add_add_add_comm, add_sub_add_comm, Fin.sum_univ_two]
  rfl

/- English proof (translation)
Rewrite using `[kill_dfc Y _ (zc_col (zc_gp _) _) (zc_col (zc_gp _) _) (zc_col (zc_gp _) _), kp_gp, kp_gp, kp_gp]`. Use `show dfc Y (if c = k then _ else _) (if col = k then _ else _) (if col = k then _ else _) = _`. Distinguish the cases in `h : col = k`. Substitute `h` using the available equality. Distinguish the cases in `h' : c = col`.

Simplify using `[h']`. Simplify using `[h', dfc_left Y (zc_pt _) (zc_pt _)]`. Distinguish the cases in `h' : c = k`. Simplify using `[h, h', dfc_right Y (zc_pt _)]`. Simplify using `[h, h', dfc_right Y zc_zero]`.
-/
theorem kill_dfc_gp (c col k : Fin 2) :
    killCompl (emb dd ![c, col, col]) (dfc Y (colOf (gp C (Fin 2 × Fin dd) (0 : Fin 3)) k)
      (colOf (gp C (Fin 2 × Fin dd) 1) k) (colOf (gp C (Fin 2 × Fin dd) 2) k)) =
      if col = k ∧ c = col then dfc Y (pt C dd (0 : Fin 3)) (pt C dd 1) (pt C dd 2) else 0 := by
  rw [kill_dfc Y _ (zc_col (zc_gp _) _) (zc_col (zc_gp _) _) (zc_col (zc_gp _) _), kp_gp, kp_gp, kp_gp]
  show dfc Y (if c = k then _ else _) (if col = k then _ else _) (if col = k then _ else _) = _
  by_cases h : col = k
  · subst h
    by_cases h' : c = col
    · simp [h']
    · simp [h', dfc_left Y (zc_pt _) (zc_pt _)]
  · by_cases h' : c = k
    · simp [h, h', dfc_right Y (zc_pt _)]
    · simp [h, h', dfc_right Y zc_zero]

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[coeff_killCompl]`. Use `show ∑ x : Fin 2 × Fin dd, u x * _ = ∑ i, u (col, i) * _`. Establish `key : ∀ (c : Fin 2) (i : Fin dd), (Finsupp.embDomain (emb dd fun _ : Fin 2 => col) μ).mapDomain (fun q : Fin 2 × (Fin 2 × Fin dd) => (q.1.succ, q.2)) + Finsupp.single ((0 : Fin 3), (c, i)) 1 = Finsupp.embDomain (emb dd ![c, col, col]) (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1. …`. Introduce `c i`.

Rewrite using `[Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_add, Finsupp.mapDomain_single, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]`. Use `congr 2`. Use function extensionality and compare the values at `⟨j, i⟩`. Apply the tactic sequence `fin_cases j <;> rfl`. Rewrite using `[dfc_square Y p (zc_gp _) (zc_gp _) (zc_gp _), Fintype.sum_prod_type]`.

Simplify using `only [key, ← coeff_killCompl, map_sum, coeff_formalBiextensionChart_secondPhase]`. Rewrite using `[Finset.sum_eq_single col]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single col]`. Rewrite using `[kill_dfc_gp, if_pos ⟨rfl, rfl⟩]`.

Introduce `k _ hk`. Rewrite using `[kill_dfc_gp, if_neg fun h => hk h.1.symm, map_zero]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_zero, mul_zero]`. Introduce `k _`. Rewrite using `[kill_dfc_gp, if_neg fun h => hc h.2, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem killCompl_formalGroupCocycleLinearTerm_column (col : Fin 2) (u : Fin 2 × Fin dd → C) :
    killCompl (emb dd fun _ => col) (c2 (Y.rawSelf p) u) = Y.chartLinearTerm fun i => u (col, i) := by
  ext μ
  rw [coeff_killCompl]
  show ∑ x : Fin 2 × Fin dd, u x * _ = ∑ i, u (col, i) * _
  have key : ∀ (c : Fin 2) (i : Fin dd),
      (Finsupp.embDomain (emb dd fun _ : Fin 2 => col) μ).mapDomain
          (fun q : Fin 2 × (Fin 2 × Fin dd) => (q.1.succ, q.2)) + Finsupp.single ((0 : Fin 3), (c, i)) 1 =
        Finsupp.embDomain (emb dd ![c, col, col])
          (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) := by
    intro c i
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 2
    funext ⟨j, i⟩
    fin_cases j <;> rfl
  rw [dfc_square Y p (zc_gp _) (zc_gp _) (zc_gp _), Fintype.sum_prod_type]
  simp only [key, ← coeff_killCompl, map_sum, coeff_formalBiextensionChart_secondPhase]
  rw [Finset.sum_eq_single col]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single col]
    · rw [kill_dfc_gp, if_pos ⟨rfl, rfl⟩]
    · intro k _ hk
      rw [kill_dfc_gp, if_neg fun h => hk h.1.symm, map_zero]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_eq_zero, mul_zero]
    intro k _
    rw [kill_dfc_gp, if_neg fun h => hc h.2, map_zero]
  · simp

omit [CharZero C] in
/- English proof (translation)
The claim follows from `funext fun x => congrFun (kp_gp (fun _ => col) j x.1) x.2`.
-/
theorem kp_gp_inj (col j : Fin 2) :
    kp (emb dd fun _ => col) (gp C (Fin 2 × Fin dd) j) = inj col (pt C dd j) :=
  funext fun x => congrFun (kp_gp (fun _ => col) j x.1) x.2

/- English proof (translation)
Rewrite using `[ev_inj col (zc_addOf Y _ _), ev_inj col (zc_pt _), ev_inj col (zc_pt _), cob, map_sub, map_sub, kill_subst _ (zc_addP Y p (zc_gp _) (zc_gp _)), kill_subst _ (zc_gp _), kill_subst _ (zc_gp _), ← kp_gp_inj, ← kp_gp_inj]`. Use `congr 3`. Use function extensionality and compare the values at `x`. Establish `e` using `congrFun (kp_law Y (emb dd fun _ : Fin 2 => col) (zc_col (zc_gp (0 : Fin 2)) x.1) (zc_col (zc_gp (1 : Fin 2)) x.1)) x.2`. Rewrite `e` using `[kp_gp, kp_gp]`.

Rewrite using `[formalAdd_eq Y p (zc_gp _) (zc_gp _)]`. Use `e.trans ?_` and prove the remaining obligations. Unfold `inj`. Use `split_ifs`. Both sides reduce to the same expression.

Rewrite using `[law_zero]`.
-/
theorem kill_cob (col : Fin 2) (b : MvPowerSeries (Fin 2 × Fin dd) C) :
    killCompl (emb dd fun _ => col) (cob (Y.rawSelf p) b) =
      ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (subst (inj col (pt C dd (0 : Fin 1))) b) -
        ev (n := 2) ![pt C dd 0] (subst (inj col (pt C dd (0 : Fin 1))) b) -
        ev (n := 2) ![pt C dd 1] (subst (inj col (pt C dd (0 : Fin 1))) b) := by
  rw [ev_inj col (zc_addOf Y _ _), ev_inj col (zc_pt _), ev_inj col (zc_pt _), cob, map_sub, map_sub,
    kill_subst _ (zc_addP Y p (zc_gp _) (zc_gp _)), kill_subst _ (zc_gp _), kill_subst _ (zc_gp _),
    ← kp_gp_inj, ← kp_gp_inj]
  congr 3
  funext x
  have e := congrFun (kp_law Y (emb dd fun _ : Fin 2 => col) (zc_col (zc_gp (0 : Fin 2)) x.1)
    (zc_col (zc_gp (1 : Fin 2)) x.1)) x.2
  rw [kp_gp, kp_gp] at e
  rw [formalAdd_eq Y p (zc_gp _) (zc_gp _)]
  refine e.trans ?_
  unfold inj
  split_ifs
  · rfl
  · rw [law_zero]

end Chart

/- English proof (translation)
Introduce and unpack `γ hγ ⟨⟨col, i0⟩, hi0⟩ hadd ⟨b, hb, hcob⟩`. Establish `hz : ∀ s : Fin 2, Zc (fun j => cvAt (X s) (γ j))` using `fun s j => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) (hγ j).1`. Use `hY (fun i => γ (col, i)) (fun i => hγ _) ⟨i0, hi0⟩ (fun i μ h0 h1 => ?_) ⟨subst (inj col (pt C dd (0 : Fin 1))) b, intS_subst V (zc_inj col (zc_pt _)) (fun x => ?_) hb, fun μ => ?_⟩` and prove the remaining obligations. Establish `h` using `hadd (col, i) μ h0 h1`. Rewrite `h` using `[formalAdd_eq Y p (hz 0) (hz 1)]`.

Use `h using 4` and compare the differences between its conclusion and the goal. Unfold `law sb`. Use `congr 1`. Use function extensionality and compare the values at `⟨j, x⟩`. Apply the tactic sequence `fin_cases j <;> rfl`.

Unfold `inj split_ifs`. Conclude with `intS_X V _`. Conclude with `(intSer V _).zero_mem`. Establish `h` using `hcob (Finsupp.embDomain (emb dd fun _ => col) μ)`. Rewrite `h` using `[← coeff_killCompl, map_sub, killCompl_formalGroupCocycleLinearTerm_column, kill_cob]`. Then use the resulting hypothesis.
-/
theorem nonDeg_rawSelf (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0) (hY : NDG Y) :
    NonDeg (Y.rawSelf p) V := by
  rintro γ hγ ⟨⟨col, i0⟩, hi0⟩ hadd ⟨b, hb, hcob⟩
  have hz : ∀ s : Fin 2, Zc (fun j => cvAt (X s) (γ j)) := fun s j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hγ j).1
  refine hY (fun i => γ (col, i)) (fun i => hγ _) ⟨i0, hi0⟩ (fun i μ h0 h1 => ?_)
    ⟨subst (inj col (pt C dd (0 : Fin 1))) b, intS_subst V (zc_inj col (zc_pt _)) (fun x => ?_) hb, fun μ => ?_⟩
  · have h := hadd (col, i) μ h0 h1
    rw [formalAdd_eq Y p (hz 0) (hz 1)] at h
    convert h using 4
    unfold law sb
    congr 1
    funext ⟨j, x⟩
    fin_cases j <;> rfl
  · unfold inj
    split_ifs
    · exact intS_X V _
    · exact (intSer V _).zero_mem
  · have h := hcob (Finsupp.embDomain (emb dd fun _ => col) μ)
    rwa [← coeff_killCompl, map_sub, killCompl_formalGroupCocycleLinearTerm_column, kill_cob] at h

end GlobalTheory.NonDegSquare
