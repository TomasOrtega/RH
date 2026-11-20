import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmall

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

/- English proof (translation)
Establish `h0 : a = 0` using `funext ha`. Substitute `h0` using the available equality. Establish `hs : MvPowerSeries.HasSubst (0 : σ → MvPowerSeries τ C)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)`. Use extensionality with `e`. Rewrite using `[MvPowerSeries.coeff_subst hs, map_zero]`.

Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `d`. Distinguish the cases in `hd : d = 0`. Substitute `hd` using the available equality. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hsd⟩ : ∃ s, d s ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hd (Finsupp.ext hcon)`. Establish `hp : (d.prod fun s n => (0 : σ → MvPowerSeries τ C) s ^ n) = 0`.

Apply `Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hsd)` to reduce the goal to its premises. Simplify using `[zero_pow hsd]`. Rewrite using `[hp, map_zero, smul_zero]`.
-/
theorem subst_zero_of {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, a s = 0)
    {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) : MvPowerSeries.subst a f = 0 := by
  have h0 : a = 0 := funext ha
  subst h0
  have hs : MvPowerSeries.HasSubst (0 : σ → MvPowerSeries τ C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  ext e
  rw [MvPowerSeries.coeff_subst hs, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hsd⟩ : ∃ s, d s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd (Finsupp.ext hcon)
    have hp : (d.prod fun s n => (0 : σ → MvPowerSeries τ C) s ^ n) = 0 := by
      apply Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hsd)
      simp [zero_pow hsd]
    rw [hp, map_zero, smul_zero]

/- English proof (translation)
Rewrite using `[← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ev_eq_alg ha, ev_eq_alg ha, map_smul]`.
-/
private theorem ev_C_mul' {m n : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a) (c : C) (f : PS C m dd) :
    ev a (MvPowerSeries.C c * f) = MvPowerSeries.C c * ev a f := by
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ev_eq_alg ha, ev_eq_alg ha, map_smul]

/- English proof (translation)
Establish `hk : ∀ i, Y.B.A.act (k : O) i = ev ![fun j' => MvPowerSeries.C (k : C) * Y.lg j'] (Y.ex i)`. Introduce `i`. Establish `h` using `ex_lg_comp Y (Y.B.A.act (k : O)) (Y.B.A.const _) i`. Simplify using `only [lg_act_nat] at h`. Conclude with `h.symm`.

Establish `hw : Z0 ![Y.B.A.act w]`. Introduce `k' i'`. Use `fin_cases k'`. Simplify using `[Y.B.A.const]`. Establish `hb : Z0 ![fun j' => MvPowerSeries.C (k : C) * Y.lg j']`.

Introduce `k' i'`. Use `fin_cases k'`. Simplify using `[lg_const]`. Rewrite using `[Y.B.A.mul_act]`. Use `show ev ![Y.B.A.act w] (Y.B.A.act (k : O) j) = _`.

Rewrite using `[hk, ev_ev hb hw]`. Use `congr 1`. Use function extensionality and compare the values at `k' i'`. Use `fin_cases k'`. Use `show ev ![Y.B.A.act w] (MvPowerSeries.C (k : C) * Y.lg i') = MvPowerSeries.C (k : C) * ev ![Y.B.A.act w] (Y.lg i')`.

Conclude with `ev_C_mul' hw _ _`.
-/
theorem act_nat_mul (Y : FBChart C V O dd) (k : ℕ) (w : O) (j : Fin dd) :
    Y.B.A.act ((k : O) * w) j =
      ev ![fun j' => MvPowerSeries.C (k : C) * ev ![Y.B.A.act w] (Y.lg j')] (Y.ex j) := by
  have hk : ∀ i, Y.B.A.act (k : O) i = ev ![fun j' => MvPowerSeries.C (k : C) * Y.lg j'] (Y.ex i) := by
    intro i
    have h := ex_lg_comp Y (Y.B.A.act (k : O)) (Y.B.A.const _) i
    simp only [lg_act_nat] at h
    exact h.symm
  have hw : Z0 ![Y.B.A.act w] := by
    intro k' i'
    fin_cases k'
    simp [Y.B.A.const]
  have hb : Z0 ![fun j' => MvPowerSeries.C (k : C) * Y.lg j'] := by
    intro k' i'
    fin_cases k'
    simp [lg_const]
  rw [Y.B.A.mul_act]
  show ev ![Y.B.A.act w] (Y.B.A.act (k : O) j) = _
  rw [hk, ev_ev hb hw]
  congr 1
  funext k' i'
  fin_cases k'
  show ev ![Y.B.A.act w] (MvPowerSeries.C (k : C) * Y.lg i') = MvPowerSeries.C (k : C) * ev ![Y.B.A.act w] (Y.lg i')
  exact ev_C_mul' hw _ _

/- English proof (translation)
Apply `tends_of_nat` to reduce the goal to its premises. Introduce `N`. Use `⟨N, fun n hn => ?_⟩` and prove the remaining obligations. Use `show ((N : ℝ) : WithTop ℝ) ≤ V.v (0 - ((V.l ^ (n + 1) : ℕ) : C))`. Rewrite using `[zero_sub, AddValuation.map_neg, Nat.cast_pow, AddValuation.map_pow, V.v_l, nsmul_one]`.

Establish `h2 : ((N : ℝ) : WithTop ℝ) ≤ (((n + 1 : ℕ) : ℝ) : WithTop ℝ)`. Rewrite using `[WithTop.coe_le_coe]`. Conclude with `(by omega : N ≤ n + 1)` after adjusting the coercions. Simplify using `using h2`.
-/
theorem tends_lpow : Tends V (fun n => ((V.l ^ (n + 1) : ℕ) : C)) 0 := by
  apply tends_of_nat
  intro N
  refine ⟨N, fun n hn => ?_⟩
  show ((N : ℝ) : WithTop ℝ) ≤ V.v (0 - ((V.l ^ (n + 1) : ℕ) : C))
  rw [zero_sub, AddValuation.map_neg, Nat.cast_pow, AddValuation.map_pow, V.v_l, nsmul_one]
  have h2 : ((N : ℝ) : WithTop ℝ) ≤ (((n + 1 : ℕ) : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_le_coe]
    exact_mod_cast (by omega : N ≤ n + 1)
  simpa using h2

/- English proof (translation)
Introduce `C _ _ V O _ _ dd Y x x' hx N i μ`. Establish `hx' : ∀ n, ∃ c, x n - x' n = (V.l : O) ^ (n + 1) * c` using `fun n => hx n`. Use `choose y hy using hx'`. Establish `hsmall : ∀ (z : ℕ → O) (j : Fin dd), TendsS V (fun n => Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * z n) j) 0`. Introduce `z j`.

Establish `hw : ∀ n, Z0 ![Y.B.A.act (z n)]`. Introduce `n k' i'`. Use `fin_cases k'`. Simplify using `[Y.B.A.const]`. Establish `hg : ∀ s2 : Fin dd, BddS V (fun n => ev ![Y.B.A.act (z n)] (Y.lg s2))`.

Introduce `s2`. Conclude with `BddS.subst (a := fun n (p : Fin 1 × Fin dd) => (![Y.B.A.act (z n)] p.1) p.2) (f := fun _ => Y.lg s2) (by`. Introduce and unpack `n ⟨t1, t2⟩`. Use `fin_cases t1`. Simplify using `[Y.B.A.const])`.

Use the proof step `(by`. Introduce and unpack `⟨t1, t2⟩`. Use `fin_cases t1`. Conclude with `BddS.of_int (fun n => Y.intAct _ _))`. Use the proof step `(BddS.const _)`.

Establish `hcl` using `Close.subst (V := V) (a := fun n (p : Fin 1 × Fin dd) => (![fun j' => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg j')] p.1) p.2) (b := fun _ _ => 0) (by`. Introduce and unpack `n ⟨s1, s2⟩`. Use `fin_cases s1`. Simplify using `[const_ev (hw n) (lg_const Y s2)])`. Use the proof step `(by intros; simp)`.

Use the proof step `(by`. Introduce and unpack `⟨s1, s2⟩`. Use `fin_cases s1`. Use `show BddS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2))`. Apply `BddS.mul _ (hg s2)` to reduce the goal to its premises.

Introduce `ν`. Use `⟨0, fun n => ?_⟩` and prove the remaining obligations. Use `show V.Ge 0 (MvPowerSeries.coeff ν (MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C))))`. Rewrite using `[MvPowerSeries.coeff_C]`. Use `split_ifs`.

Conclude with `ge_natCast _`. Use `show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0 simp)`. Use the proof step `(fun _ => BddS.const 0)`. Use the proof step `(by`. Introduce and unpack `⟨s1, s2⟩`.

Use `fin_cases s1`. Use `show TendsS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2) - 0) 0`. Simplify using `only [sub_zero]`. Simplify using `only [mul_comm (MvPowerSeries.C _)]`. Apply `TendsS.mul_bdd (hg s2)` to reduce the goal to its premises.

Introduce `ν`. Simplify using `only [MvPowerSeries.coeff_C, map_zero]`. Use `split_ifs`. Conclude with `tends_lpow`. Conclude with `tends_const 0)`.

Use the proof step `(Y.ex j)`. Establish `h0 : MvPowerSeries.subst (fun _ : Fin 1 × Fin dd => (0 : MvPowerSeries (Fin 1 × Fin dd) C)) (Y.ex j) = 0` using `subst_zero_of (fun _ => rfl) (Y.ex_const j)`. Introduce `ν`. Establish `h1` using `hcl ν`. Simplify using `only [h0, sub_zero] at h1`.

Simplify using `only [act_nat_mul]`. Conclude with `h1`. Establish `heq : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2) (Y.B.G.F i) = Y.B.A.act (x n) i`. Introduce `n`. Establish `hxn : x n = x' n + ((V.l ^ (n + 1) : ℕ) : O) * y n`.

Rewrite using `[Nat.cast_pow, ← hy n]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hxn, Y.B.A.add_act]`. Both sides reduce to the same expression. Establish `heq' : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2) (Y.B.G.F i) = Y.B.A.act (x' n) i`.

Introduce `n`. Establish `hxn : Y.B.A.act (x' n) i = Y.B.A.act (x' n + ((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n) i`. Simplify using the standard rewrite rules. Rewrite using `[hxn, Y.B.A.add_act]`. Both sides reduce to the same expression.

Establish `hcl` using `Close.subst (V := V) (a := fun n (p : Fin 2 × Fin dd) => (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2) (b := fun n (p : Fin 2 × Fin dd) => (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2) (by`. Introduce and unpack `n ⟨s1, s2⟩`. Apply the tactic sequence `fin_cases s1 <;> simp [Y.B.A.const])`. Use the proof step `(by`. Introduce and unpack `n ⟨s1, s2⟩`.

Apply the tactic sequence `fin_cases s1 <;> simp [Y.B.A.const])`. Use the proof step `(by`. Introduce and unpack `⟨s1, s2⟩`. Apply the tactic sequence `fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))`. Use the proof step `(by`.

Introduce and unpack `⟨s1, s2⟩`. Apply the tactic sequence `fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))`. Use the proof step `(by`. Introduce and unpack `⟨s1, s2⟩`. Use `fin_cases s1`.

Conclude with `Close.refl (fun n => Y.B.A.act (x' n) s2)`. Introduce `ν`. Establish `h1` using `hsmall y s2 ν`. Establish `h2` using `hsmall (fun _ => 0) s2 ν`. Establish `h3` using `h1.sub h2`.

Simplify using `only [map_zero, sub_zero] at h3`. Rewrite using `[map_zero]`. Simplify using `only [map_sub]`. Conclude with `h3)`. Use the proof step `(Y.B.G.F i)`.

Take `⟨n0, hn0⟩` from `hcl μ (N : ℝ)`. Use `⟨n0, fun n hn => ?_⟩` and prove the remaining obligations. Establish `h4` using `hn0 n hn`. Simplify using `only [heq, heq', map_zero, zero_sub, map_sub] at h4`. Use `show ((N : ℝ) : WithTop ℝ) ≤ V.v _`.

Establish `h5 : ((N : ℝ) : WithTop ℝ) ≤ V.v (-(MvPowerSeries.coeff μ (Y.B.A.act (x n) i) - MvPowerSeries.coeff μ (Y.B.A.act (x' n) i)))` using `h4`. Rewrite `h5` using `[AddValuation.map_neg]`. Then use the resulting hypothesis.
-/
theorem lSmall_holds : LSmallSt := by
  intro C _ _ V O _ _ dd Y x x' hx N i μ
  have hx' : ∀ n, ∃ c, x n - x' n = (V.l : O) ^ (n + 1) * c := fun n => hx n
  choose y hy using hx'
  have hsmall : ∀ (z : ℕ → O) (j : Fin dd),
      TendsS V (fun n => Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * z n) j) 0 := by
    intro z j
    have hw : ∀ n, Z0 ![Y.B.A.act (z n)] := by
      intro n k' i'
      fin_cases k'
      simp [Y.B.A.const]
    have hg : ∀ s2 : Fin dd, BddS V (fun n => ev ![Y.B.A.act (z n)] (Y.lg s2)) := by
      intro s2
      exact BddS.subst (a := fun n (p : Fin 1 × Fin dd) => (![Y.B.A.act (z n)] p.1) p.2)
        (f := fun _ => Y.lg s2)
        (by
          rintro n ⟨t1, t2⟩
          fin_cases t1
          simp [Y.B.A.const])
        (by
          rintro ⟨t1, t2⟩
          fin_cases t1
          exact BddS.of_int (fun n => Y.intAct _ _))
        (BddS.const _)
    have hcl := Close.subst (V := V)
      (a := fun n (p : Fin 1 × Fin dd) =>
        (![fun j' => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg j')] p.1) p.2)
      (b := fun _ _ => 0)
      (by
        rintro n ⟨s1, s2⟩
        fin_cases s1
        simp [const_ev (hw n) (lg_const Y s2)])
      (by intros; simp)
      (by
        rintro ⟨s1, s2⟩
        fin_cases s1
        show BddS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2))
        apply BddS.mul _ (hg s2)
        intro ν
        refine ⟨0, fun n => ?_⟩
        show V.Ge 0 (MvPowerSeries.coeff ν (MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C))))
        rw [MvPowerSeries.coeff_C]
        split_ifs
        · exact ge_natCast _
        · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
          simp)
      (fun _ => BddS.const 0)
      (by
        rintro ⟨s1, s2⟩
        fin_cases s1
        show TendsS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2) - 0) 0
        simp only [sub_zero]
        simp only [mul_comm (MvPowerSeries.C _)]
        apply TendsS.mul_bdd (hg s2)
        intro ν
        simp only [MvPowerSeries.coeff_C, map_zero]
        split_ifs
        · exact tends_lpow
        · exact tends_const 0)
      (Y.ex j)
    have h0 : MvPowerSeries.subst (fun _ : Fin 1 × Fin dd => (0 : MvPowerSeries (Fin 1 × Fin dd) C)) (Y.ex j) = 0 :=
      subst_zero_of (fun _ => rfl) (Y.ex_const j)
    intro ν
    have h1 := hcl ν
    simp only [h0, sub_zero] at h1
    simp only [act_nat_mul]
    exact h1
  have heq : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2) (Y.B.G.F i) =
        Y.B.A.act (x n) i := by
    intro n
    have hxn : x n = x' n + ((V.l ^ (n + 1) : ℕ) : O) * y n := by
      rw [Nat.cast_pow, ← hy n]
      ring
    rw [hxn, Y.B.A.add_act]
    rfl
  have heq' : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2) (Y.B.G.F i) =
        Y.B.A.act (x' n) i := by
    intro n
    have hxn : Y.B.A.act (x' n) i =
        Y.B.A.act (x' n + ((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n) i := by
      simp
    rw [hxn, Y.B.A.add_act]
    rfl
  have hcl := Close.subst (V := V)
    (a := fun n (p : Fin 2 × Fin dd) =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2)
    (b := fun n (p : Fin 2 × Fin dd) =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2)
    (by
      rintro n ⟨s1, s2⟩
      fin_cases s1 <;> simp [Y.B.A.const])
    (by
      rintro n ⟨s1, s2⟩
      fin_cases s1 <;> simp [Y.B.A.const])
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1
      · exact Close.refl (fun n => Y.B.A.act (x' n) s2)
      · intro ν
        have h1 := hsmall y s2 ν
        have h2 := hsmall (fun _ => 0) s2 ν
        have h3 := h1.sub h2
        simp only [map_zero, sub_zero] at h3
        rw [map_zero]
        simp only [map_sub]
        exact h3)
    (Y.B.G.F i)
  obtain ⟨n0, hn0⟩ := hcl μ (N : ℝ)
  refine ⟨n0, fun n hn => ?_⟩
  have h4 := hn0 n hn
  simp only [heq, heq', map_zero, zero_sub, map_sub] at h4
  show ((N : ℝ) : WithTop ℝ) ≤ V.v _
  have h5 : ((N : ℝ) : WithTop ℝ) ≤ V.v (-(MvPowerSeries.coeff μ (Y.B.A.act (x n) i) -
      MvPowerSeries.coeff μ (Y.B.A.act (x' n) i))) := h4
  rwa [AddValuation.map_neg] at h5

end Main

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
