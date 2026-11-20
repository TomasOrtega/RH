import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqM2

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

open PartialDerivEval RowTiePCEqM

namespace RowTiePCEqEx

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

/- English proof (translation)
Unfold `ev`. Rewrite using `[Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) f q, Fintype.sum_prod_type, Fin.sum_univ_one]`.
-/
theorem pderiv_eval_single {n : ℕ} {a : Fin 1 → Pt C n dd} (ha : Z0 a) (f : PS C 1 dd) (q : Fin n × Fin dd) :
    pderiv C q (ev a f) = ∑ j, ev a (pderiv C ((0 : Fin 1), j) f) * pderiv C q (a 0 j) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) f q,
    Fintype.sum_prod_type, Fin.sum_univ_one]

/- English proof (translation)
Unfold `ev`. Establish `: (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X`. Use function extensionality and compare the values at `p`. Take `⟨k, j⟩` from `p`. Use `fin_cases k`.

Both sides reduce to the same expression. Rewrite using `[this, subst_self]`. Both sides reduce to the same expression.
-/
theorem germEval_oneStandardPoint_self (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0] f = f := by
  unfold ev
  have : (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [this, subst_self]
  rfl

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_pderiv {σ : Type} (q : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv C q f) = coeff (Finsupp.single q 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
  simp

/- English proof (translation)
Establish `hZ : Z0 (![0] : Fin 1 → Pt C n dd)`. Introduce `k i`. Use `fin_cases k`. Simplify using the standard rewrite rules. Establish `h1 : f = MvPowerSeries.C (constantCoeff f) + (f - MvPowerSeries.C (constantCoeff f))` using `by ring`.

Use `conv_lhs => rw [h1]`. Rewrite using `[ev_add hZ, ev_C]`. Establish `h2 : ev (n` using `n) (![0] : Fin 1 → Pt C n dd) (f - MvPowerSeries.C (constantCoeff f)) = 0 := by`. Unfold `ev`. Establish `e : (fun p : Fin 1 × Fin dd => (![0] : Fin 1 → Pt C n dd) p.1 p.2) = fun _ => 0`.

Use function extensionality and compare the values at `p`. Take `⟨k, j⟩` from `p`. Use `fin_cases k`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `RowTiePCEqSum.subst_zero_const _ (by simp)`. Rewrite using `[h2, add_zero]`.
-/
theorem ev_zero_pt {n : ℕ} (f : PS C 1 dd) : ev (n := n) (![0] : Fin 1 → Pt C n dd) f = MvPowerSeries.C (constantCoeff f) := by
  have hZ : Z0 (![0] : Fin 1 → Pt C n dd) := by
    intro k i; fin_cases k; simp
  have h1 : f = MvPowerSeries.C (constantCoeff f) + (f - MvPowerSeries.C (constantCoeff f)) := by ring
  conv_lhs => rw [h1]
  rw [ev_add hZ, ev_C]
  have h2 : ev (n := n) (![0] : Fin 1 → Pt C n dd) (f - MvPowerSeries.C (constantCoeff f)) = 0 := by
    unfold ev
    have e : (fun p : Fin 1 × Fin dd => (![0] : Fin 1 → Pt C n dd) p.1 p.2) = fun _ => 0 := by
      funext p
      obtain ⟨k, j⟩ := p
      fin_cases k
      rfl
    rw [e]
    exact RowTiePCEqSum.subst_zero_const _ (by simp)
  rw [h2, add_zero]

/- English proof (translation)
Establish `hZ : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd)` using `z0_1 _ Y.ex_const`. Establish `h : constantCoeff (pderiv C ((0 : Fin 1), i) (comp1 Y.lg Y.ex m)) = constantCoeff (pderiv C ((0 : Fin 1), i) (pt C (n` using `1) dd 0 m)) := by`. Rewrite using `[Y.lg_ex]`. Unfold `comp1 at h`. Rewrite `h` using `[pderiv_eval_single hZ, map_sum]`.

Simplify using `only [map_mul, constantCoeff_ev hZ, constantCoeff_pderiv] at h`. Establish `hl : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) (Y.lg m) = if k = m then 1 else 0`. Introduce `k`. Rewrite using `[Y.lg_lin m _ (by simp), coeff_X]`. Distinguish the cases in `hk : k = m`.

Rewrite using `[if_pos hk, if_pos (by rw [hk])]`. Rewrite using `[if_neg hk, if_neg]`. Introduce `e`. Conclude with `hk (Prod.mk.inj (Finsupp.single_left_injective one_ne_zero e)).2`. Simplify using `only [hl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`.

Rewrite `h` using `[← constantCoeff_pderiv]`. Express the relevant statement in the definitionally equal form `constantCoeff (pderiv C ((0 : Fin 1), i) (Y.ex m)) = coeff (Finsupp.single ((0 : Fin 1), i) 1) (X ((0 : Fin 1), m) : PS C 1 dd) at h`. Rewrite using `[h, coeff_X]`. Distinguish the cases in `him : i = m`. Rewrite using `[if_pos him, if_pos (by rw [him])]`.

Rewrite using `[if_neg him, if_neg]`. Introduce `e`. Conclude with `him (Prod.mk.inj (Finsupp.single_left_injective one_ne_zero e)).2`.
-/
theorem ex_lin (Y : FBChart C V O dd) (i m : Fin dd) :
    constantCoeff (pderiv C ((0 : Fin 1), i) (Y.ex m)) = if i = m then 1 else 0 := by
  have hZ : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd) := z0_1 _ Y.ex_const
  have h : constantCoeff (pderiv C ((0 : Fin 1), i) (comp1 Y.lg Y.ex m)) =
      constantCoeff (pderiv C ((0 : Fin 1), i) (pt C (n := 1) dd 0 m)) := by
    rw [Y.lg_ex]
  unfold comp1 at h
  rw [pderiv_eval_single hZ, map_sum] at h
  simp only [map_mul, constantCoeff_ev hZ, constantCoeff_pderiv] at h
  have hl : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) (Y.lg m) = if k = m then 1 else 0 := by
    intro k
    rw [Y.lg_lin m _ (by simp), coeff_X]
    by_cases hk : k = m
    · rw [if_pos hk, if_pos (by rw [hk])]
    · rw [if_neg hk, if_neg]
      intro e
      exact hk (Prod.mk.inj (Finsupp.single_left_injective one_ne_zero e)).2
  simp only [hl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [← constantCoeff_pderiv] at h
  change constantCoeff (pderiv C ((0 : Fin 1), i) (Y.ex m)) =
    coeff (Finsupp.single ((0 : Fin 1), i) 1) (X ((0 : Fin 1), m) : PS C 1 dd) at h
  rw [h, coeff_X]
  by_cases him : i = m
  · rw [if_pos him, if_pos (by rw [him])]
  · rw [if_neg him, if_neg]
    intro e
    exact him (Prod.mk.inj (Finsupp.single_left_injective one_ne_zero e)).2

end RowTiePCEqEx

namespace RowTiePCEqEx

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

/- English proof (translation)
Establish `hA0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n` using `2) dd 0) m) = 0 := fun m => const_ev (z0_1 _ (z0_pt 0)) (Y.ex_const m)`. Establish `hB0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n` using `2) dd 1) m) = 0 := fun m => const_ev (z0_1 _ (z0_pt 1)) (Y.ex_const m)`. Establish `hAB : Z0 (![comp1 Y.ex (pt C (n` using `2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := by`. Introduce `k i`. Use `fin_cases k`.

Conclude with `hA0 i`. Conclude with `hB0 i`. Establish `hZex : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd)` using `z0_1 _ Y.ex_const`. Establish `hlgk : ∀ (k : Fin 2) m, ev (n` using `2) ![comp1 Y.ex (pt C (n := 2) dd k)] (Y.lg m) = pt C dd k m := by`. Introduce `k m`.

Establish `e : ev (n` using `2) ![comp1 Y.ex (pt C (n := 2) dd k)] (Y.lg m) = ev (n := 2) ![pt C dd k] (ev (n := 1) ![Y.ex] (Y.lg m)) := by`. Rewrite using `[ev_ev hZex (z0_1 _ (z0_pt k))]`. Use `congr 1`. Use function extensionality and compare the values at `k' i`. Use `fin_cases k'`.

Both sides reduce to the same expression. Rewrite using `[e, show ev (n := 1) ![Y.ex] (Y.lg m) = comp1 Y.lg Y.ex m from rfl, Y.lg_ex, show (pt C (n := 1) dd 0 m) = X ((0 : Fin 1), m) from rfl, ev_X (z0_1 _ (z0_pt k))]`. Both sides reduce to the same expression. Use `set P : Pt C 2 dd := fun j => ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] (Y.B.G.F j) with hP`. Establish `hP0 : ∀ m, constantCoeff (P m) = 0` using `fun m => const_ev hAB (Y.B.G.const m)`.

Establish `hZP : Z0 (![P] : Fin 1 → Pt C 2 dd)` using `z0_1 _ hP0`. Establish `hPl : ∀ m, ev (n` using `2) ![P] (Y.lg m) = pt C (n := 2) dd 0 m + pt C dd 1 m := by`. Introduce `m`. Establish `e1 : ev (n` using `2) ![P] (Y.lg m) = ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] (ev (n := 2) ![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1)] (Y.lg m)) := by`. Rewrite using `[ev_ev (z0_1 _ (const_addOf Y 0 1)) hAB]`.

Use `congr 1`. Use function extensionality and compare the values at `k i`. Use `fin_cases k`. Use `show P i = _`. Rewrite using `[hP]`.

Conclude with `congrArg _ (addOf_pts Y.B.G.F i).symm`. Rewrite using `[e1, Y.lg_add m, ev_add hAB, ev_ev (z0_1 _ (z0_pt 0)) hAB, ev_ev (z0_1 _ (z0_pt 1)) hAB]`. Establish `e2 : ∀ k : Fin 2, (fun k' i => ev (n` using `2) (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) k' i)) = ![comp1 Y.ex (pt C (n := 2) dd k)] := by`. Introduce `k`. Use function extensionality and compare the values at `k' i`.

Use `fin_cases k'`. Use `show ev (n := 2) _ (X (k, i) : PS C 2 dd) = _`. Rewrite using `[ev_X hAB]`. Apply the tactic sequence `fin_cases k <;> rfl`. Rewrite using `[e2 0, e2 1, hlgk 0, hlgk 1]`.

Establish `hPS : ∀ j, P j = ev (n` using `2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j) := by`. Introduce `j`. Establish `e1 : ev (n` using `2) ![P] (comp1 Y.ex Y.lg j) = P j := by`. Rewrite using `[Y.ex_lg, show (pt C (n := 1) dd 0 j) = X ((0 : Fin 1), j) from rfl, ev_X hZP]`. Both sides reduce to the same expression.

Rewrite using `[← e1]`. Unfold `comp1`. Rewrite using `[ev_ev (z0_1 _ Y.lg_const) hZP]`. Use `congr 1`. Use function extensionality and compare the values at `k i`.

Use `fin_cases k`. Conclude with `hPl i`. Conclude with `(hPS j).symm`.
-/
theorem ex_add (Y : FBChart C V O dd) (j : Fin dd) :
    ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j) =
      ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] (Y.B.G.F j) := by
  have hA0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 0) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 0)) (Y.ex_const m)
  have hB0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 1) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 1)) (Y.ex_const m)
  have hAB : Z0 (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := by
    intro k i; fin_cases k
    · exact hA0 i
    · exact hB0 i
  have hZex : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd) := z0_1 _ Y.ex_const
  have hlgk : ∀ (k : Fin 2) m, ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd k)] (Y.lg m) = pt C dd k m := by
    intro k m
    have e : ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd k)] (Y.lg m) =
        ev (n := 2) ![pt C dd k] (ev (n := 1) ![Y.ex] (Y.lg m)) := by
      rw [ev_ev hZex (z0_1 _ (z0_pt k))]
      congr 1
      funext k' i
      fin_cases k'
      rfl
    rw [e, show ev (n := 1) ![Y.ex] (Y.lg m) = comp1 Y.lg Y.ex m from rfl, Y.lg_ex,
      show (pt C (n := 1) dd 0 m) = X ((0 : Fin 1), m) from rfl, ev_X (z0_1 _ (z0_pt k))]
    rfl
  set P : Pt C 2 dd := fun j => ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)]
    (Y.B.G.F j) with hP
  have hP0 : ∀ m, constantCoeff (P m) = 0 := fun m => const_ev hAB (Y.B.G.const m)
  have hZP : Z0 (![P] : Fin 1 → Pt C 2 dd) := z0_1 _ hP0
  have hPl : ∀ m, ev (n := 2) ![P] (Y.lg m) = pt C (n := 2) dd 0 m + pt C dd 1 m := by
    intro m
    have e1 : ev (n := 2) ![P] (Y.lg m) =
        ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)]
          (ev (n := 2) ![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1)] (Y.lg m)) := by
      rw [ev_ev (z0_1 _ (const_addOf Y 0 1)) hAB]
      congr 1
      funext k i
      fin_cases k
      show P i = _
      rw [hP]
      exact congrArg _ (addOf_pts Y.B.G.F i).symm
    rw [e1, Y.lg_add m, ev_add hAB, ev_ev (z0_1 _ (z0_pt 0)) hAB, ev_ev (z0_1 _ (z0_pt 1)) hAB]
    have e2 : ∀ k : Fin 2, (fun k' i => ev (n := 2)
        (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd)
        ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) k' i)) = ![comp1 Y.ex (pt C (n := 2) dd k)] := by
      intro k
      funext k' i
      fin_cases k'
      show ev (n := 2) _ (X (k, i) : PS C 2 dd) = _
      rw [ev_X hAB]
      fin_cases k <;> rfl
    rw [e2 0, e2 1, hlgk 0, hlgk 1]
  have hPS : ∀ j, P j = ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j) := by
    intro j
    have e1 : ev (n := 2) ![P] (comp1 Y.ex Y.lg j) = P j := by
      rw [Y.ex_lg, show (pt C (n := 1) dd 0 j) = X ((0 : Fin 1), j) from rfl, ev_X hZP]
      rfl
    rw [← e1]
    unfold comp1
    rw [ev_ev (z0_1 _ Y.lg_const) hZP]
    congr 1
    funext k i
    fin_cases k
    exact hPl i
  exact (hPS j).symm

end RowTiePCEqEx

open RowTiePCEqEx in

/- English proof (translation)
Introduce `v j`. Establish `hZex : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd)` using `z0_1 _ Y.ex_const`. Establish `hQ : Z0 ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd))` using `z0_p0 _ (z0_pt 0)`. Establish `hS0 : ∀ m, constantCoeff (pt C (n` using `2) dd 0 m + pt C dd 1 m) = 0 := fun m => by`. Rewrite using `[map_add, z0_pt, z0_pt, add_zero]`.

Establish `hZS : Z0 (![fun m => pt C (n` using `2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) := z0_1 _ hS0`. Establish `hA0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n` using `2) dd 0) m) = 0 := fun m => const_ev (z0_1 _ (z0_pt 0)) (Y.ex_const m)`. Establish `hB0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n` using `2) dd 1) m) = 0 := fun m => const_ev (z0_1 _ (z0_pt 1)) (Y.ex_const m)`. Establish `hAB : Z0 (![comp1 Y.ex (pt C (n` using `2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := by`. Introduce `k i`.

Use `fin_cases k`. Conclude with `hA0 i`. Conclude with `hB0 i`. Establish `hdk : ∀ (k : Fin 2) (i m : Fin dd), pderiv C ((1 : Fin 2), i) (comp1 Y.ex (pt C (n` using `2) dd k) m) = if k = 1 then ev (n := 2) ![pt C dd 1] (pderiv C ((0 : Fin 1), i) (Y.ex m)) else 0 := by`. Introduce `k i m`.

Use `show pderiv C _ (ev (n := 2) ![pt C (n := 2) dd k] (Y.ex m)) = _`. Rewrite using `[pderiv_eval_single (z0_1 _ (z0_pt k))]`. Use `split_ifs with hk`. Substitute `hk` using the available equality. Conclude with `sum_pderiv_pt 1 i _`.

Conclude with `Finset.sum_eq_zero fun l _ => by`. Rewrite using `[show ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) 0 l) = pt C dd k l from rfl, pderiv_pt_ne hk i l, mul_zero]`. Establish `hpt1 : ∀ k : Fin 2, (fun k' l => ev (n` using `1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) k' l)) = ![((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)) k] := by`. Introduce `k`. Use function extensionality and compare the values at `k' l`.

Use `fin_cases k'`. Conclude with `ev_X hQ k l`. Establish `hL : ∀ i, ev (n` using `1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (pderiv C ((1 : Fin 2), i) (ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j))) = pderiv C ((0 : Fin 1), i) (Y.ex j) := by`. Introduce `i`. Rewrite using `[pderiv_eval_single hZS]`.

Establish `e0 : ∀ m, pderiv C ((1 : Fin 2), i) ((![fun m => pt C (n` using `2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) 0 m) = pderiv C ((1 : Fin 2), i) (pt C (n := 2) dd 1 m) := fun m => by show pderiv C _ (pt C (n := 2) dd 0 m + pt C dd 1 m) = _`. Rewrite using `[map_add, pderiv_pt_ne (by decide) i m, zero_add]`. Simplify using `only [e0]`. Rewrite using `[sum_pderiv_pt 1 i, ev_ev hZS hQ]`. Establish `e : (fun k m => ev (n` using `1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) k m)) = ![pt C (n := 1) dd 0] := by`.

Use function extensionality and compare the values at `k m`. Use `fin_cases k`. Use `show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((X ((0 : Fin 2), m) : PS C 2 dd) + X ((1 : Fin 2), m)) = pt C dd 0 m`. Rewrite using `[ev_add hQ, ev_X hQ, ev_X hQ]`. Use `show pt C dd 0 m + 0 = pt C dd 0 m`.

Rewrite using `[add_zero]`. Rewrite using `[e, germEval_oneStandardPoint_self]`. Establish `eB : ∀ g : PS C 1 dd, ev (n` using `1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 1] g) = MvPowerSeries.C (constantCoeff g) := by`. Introduce `g`. Rewrite using `[ev_ev (z0_1 _ (z0_pt 1)) hQ, hpt1 1]`.

Conclude with `ev_zero_pt g`. Establish `eAB : ∀ f : PS C 2 dd, ev (n` using `1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] f) = ev (n := 1) ![Y.ex, 0] f := by`. Introduce `f`. Rewrite using `[ev_ev hAB hQ]`. Use `congr 1`.

Use function extensionality and compare the values at `k m`. Use `fin_cases k`. Use `show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 0] (Y.ex m)) = Y.ex m`. Rewrite using `[ev_ev (z0_1 _ (z0_pt 0)) hQ, hpt1 0]`. Conclude with `germEval_oneStandardPoint_self _`.

Use `show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 1] (Y.ex m)) = 0`. Rewrite using `[eB, Y.ex_const, map_zero]`. Establish `hR : ∀ i, ev (n` using `1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (pderiv C ((1 : Fin 2), i) (ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] (Y.B.G.F j))) = ev (n := 1) ![Y.ex] (ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) := by`. Introduce `i`. Rewrite using `[pderiv_ev_snd _ _ hA0 hB0 _ (fun m => by rw [hdk 0 i m, if_neg (by decide)]) _]`.

Simplify using `only [hdk 1 i, if_pos]`. Rewrite using `[ev_sum hQ]`. Simplify using `only [ev_mul hQ, eAB, eB, ex_lin]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[if_pos rfl, map_one, mul_one, ev_ev (z0_p0 _ (z0_pt 0)) hZex]`.

Use `congr 1`. Use function extensionality and compare the values at `k m`. Use `fin_cases k`. Conclude with `(ev_X hZex 0 m).symm`. Conclude with `(ev_zero hZex).symm`.

Introduce `m _ hm`. Rewrite using `[if_neg (Ne.symm hm), map_zero, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Establish `key : ∀ i, pderiv C ((0 : Fin 1), i) (Y.ex j) = ev (n` using `1) ![Y.ex] (ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) := by`.

Introduce `i`. Rewrite using `[← hL i, ex_add Y j, hR i]`. Unfold `FBChart.dF`. Rewrite using `[ev_sum hZex]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[ev_mul hZex, ev_C, key i]`.
-/
theorem exDer_holds {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) : ExDerSt Y := by
  intro v j
  have hZex : Z0 (![Y.ex] : Fin 1 → Pt C 1 dd) := z0_1 _ Y.ex_const
  have hQ : Z0 ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)) := z0_p0 _ (z0_pt 0)
  have hS0 : ∀ m, constantCoeff (pt C (n := 2) dd 0 m + pt C dd 1 m) = 0 := fun m => by
    rw [map_add, z0_pt, z0_pt, add_zero]
  have hZS : Z0 (![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) := z0_1 _ hS0
  have hA0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 0) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 0)) (Y.ex_const m)
  have hB0 : ∀ m, constantCoeff (comp1 Y.ex (pt C (n := 2) dd 1) m) = 0 := fun m =>
    const_ev (z0_1 _ (z0_pt 1)) (Y.ex_const m)
  have hAB : Z0 (![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := by
    intro k i; fin_cases k
    · exact hA0 i
    · exact hB0 i
  have hdk : ∀ (k : Fin 2) (i m : Fin dd), pderiv C ((1 : Fin 2), i) (comp1 Y.ex (pt C (n := 2) dd k) m) =
      if k = 1 then ev (n := 2) ![pt C dd 1] (pderiv C ((0 : Fin 1), i) (Y.ex m)) else 0 := by
    intro k i m
    show pderiv C _ (ev (n := 2) ![pt C (n := 2) dd k] (Y.ex m)) = _
    rw [pderiv_eval_single (z0_1 _ (z0_pt k))]
    split_ifs with hk
    · subst hk
      exact sum_pderiv_pt 1 i _
    · exact Finset.sum_eq_zero fun l _ => by
        rw [show ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) 0 l) = pt C dd k l from rfl, pderiv_pt_ne hk i l,
          mul_zero]
  have hpt1 : ∀ k : Fin 2, (fun k' l => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((![pt C (n := 2) dd k] : Fin 1 → Pt C 2 dd) k' l)) =
      ![((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)) k] := by
    intro k
    funext k' l
    fin_cases k'
    exact ev_X hQ k l
  have hL : ∀ i, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (pderiv C ((1 : Fin 2), i)
      (ev (n := 2) ![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] (Y.ex j))) = pderiv C ((0 : Fin 1), i) (Y.ex j) := by
    intro i
    rw [pderiv_eval_single hZS]
    have e0 : ∀ m, pderiv C ((1 : Fin 2), i)
        ((![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) 0 m) =
        pderiv C ((1 : Fin 2), i) (pt C (n := 2) dd 1 m) := fun m => by
      show pderiv C _ (pt C (n := 2) dd 0 m + pt C dd 1 m) = _
      rw [map_add, pderiv_pt_ne (by decide) i m, zero_add]
    simp only [e0]
    rw [sum_pderiv_pt 1 i, ev_ev hZS hQ]
    have e : (fun k m => ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
        ((![fun m => pt C (n := 2) dd 0 m + pt C dd 1 m] : Fin 1 → Pt C 2 dd) k m)) = ![pt C (n := 1) dd 0] := by
      funext k m
      fin_cases k
      show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) ((X ((0 : Fin 2), m) : PS C 2 dd) + X ((1 : Fin 2), m)) = pt C dd 0 m
      rw [ev_add hQ, ev_X hQ, ev_X hQ]
      show pt C dd 0 m + 0 = pt C dd 0 m
      rw [add_zero]
    rw [e, germEval_oneStandardPoint_self]
  have eB : ∀ g : PS C 1 dd, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 1] g) = MvPowerSeries.C (constantCoeff g) := by
    intro g
    rw [ev_ev (z0_1 _ (z0_pt 1)) hQ, hpt1 1]
    exact ev_zero_pt g
  have eAB : ∀ f : PS C 2 dd, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd)
      (ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] f) =
      ev (n := 1) ![Y.ex, 0] f := by
    intro f
    rw [ev_ev hAB hQ]
    congr 1
    funext k m
    fin_cases k
    · show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 0] (Y.ex m)) = Y.ex m
      rw [ev_ev (z0_1 _ (z0_pt 0)) hQ, hpt1 0]
      exact germEval_oneStandardPoint_self _
    · show ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (ev (n := 2) ![pt C dd 1] (Y.ex m)) = 0
      rw [eB, Y.ex_const, map_zero]
  have hR : ∀ i, ev (n := 1) (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) (pderiv C ((1 : Fin 2), i)
      (ev (n := 2) ![comp1 Y.ex (pt C (n := 2) dd 0), comp1 Y.ex (pt C (n := 2) dd 1)] (Y.B.G.F j))) =
      ev (n := 1) ![Y.ex] (ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) := by
    intro i
    rw [pderiv_ev_snd _ _ hA0 hB0 _ (fun m => by rw [hdk 0 i m, if_neg (by decide)]) _]
    simp only [hdk 1 i, if_pos]
    rw [ev_sum hQ]
    simp only [ev_mul hQ, eAB, eB, ex_lin]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, map_one, mul_one, ev_ev (z0_p0 _ (z0_pt 0)) hZex]
      congr 1
      funext k m
      fin_cases k
      · exact (ev_X hZex 0 m).symm
      · exact (ev_zero hZex).symm
    · intro m _ hm
      rw [if_neg (Ne.symm hm), map_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : ∀ i, pderiv C ((0 : Fin 1), i) (Y.ex j) =
      ev (n := 1) ![Y.ex] (ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) := by
    intro i
    rw [← hL i, ex_add Y j, hR i]
  unfold FBChart.dF
  rw [ev_sum hZex]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_mul hZex, ev_C, key i]

end Formalism.L2.FormalSeriesBounds
