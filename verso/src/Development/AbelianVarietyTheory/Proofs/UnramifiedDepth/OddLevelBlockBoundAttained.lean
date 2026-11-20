import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubstSame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockOfNormalForm
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SumEqOfIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockValueOnRowsEqStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataMainTermNormalFormAndLevelOneStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MainTermImpliesRowHypothesisStatement

noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.MinorShiftJet

variable {K : Type} [Field K] {V : VF K} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

/- English proof (translation)
Establish `hpar : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val`. Rewrite using `[ZMod.val_add, ZMod.val_natCast]`. Take `⟨r, hr⟩` from `h.1`. Establish `h2 : 2 ∣ d` using `⟨r, by omega⟩`. Rewrite using `[Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2, Nat.add_mod, Nat.mod_mod_of_dvd _ h2, Nat.odd_iff.1 hi]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[X.big_compl]`. Establish `h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b` using `fun b => by simpa using X.big_compl 0 b`. Use `fin_cases g`. Simplify using `only [Fin.zero_eta] at ha ⊢`.

Rewrite `ha`, the goal using `[h.2]`. Rewrite using `[hpar]`. Conclude with `fun h' => h' ha`. Simplify using `only [Fin.mk_one] at ha ⊢`. Rewrite `ha`, the goal using `[h1, h.2]`.

Rewrite using `[hpar]`. Conclude with `fun h' => h' ha`.
-/
theorem big_shift (X : RowData K V d I J) (h : X.Alt) {g : Fin 2} {a : ZMod d} (ha : X.big g a) {i : ℕ}
    (hi : Odd i) : X.big (1 - g) (a + (i : ZMod d)) := by
  have hpar : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    rw [ZMod.val_add, ZMod.val_natCast]
    obtain ⟨r, hr⟩ := h.1
    have h2 : 2 ∣ d := ⟨r, by omega⟩
    rw [Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2, Nat.add_mod, Nat.mod_mod_of_dvd _ h2,
      Nat.odd_iff.1 hi]
    omega
  rw [X.big_compl]
  have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
  fin_cases g
  · simp only [Fin.zero_eta] at ha ⊢
    rw [h.2] at ha ⊢
    rw [hpar]; exact fun h' => h' ha
  · simp only [Fin.mk_one] at ha ⊢
    rw [h1, h.2] at ha ⊢
    rw [hpar]; exact fun h' => h' ha

omit [∀ g, Fintype (I g)] in
/- English proof (translation)
Rewrite using `[minorK, dif_pos ⟨le_rfl, hN⟩, AlgHom.map_det, letterDet]`. Use `congr 1`. Use `Matrix.ext fun b c => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem rename_minor {n N : ℕ} (hN : n ≤ N) (g : Fin 2) (en : Fin N → I g) :
    MvPolynomial.rename (fun x : Fin n × Fin N => (x.1, (⟨g, en x.2⟩ : WV I))) (minorK K n N n) =
      letterDet K g fun c => en (Fin.castLE hN c) := by
  rw [minorK, dif_pos ⟨le_rfl, hN⟩, AlgHom.map_det, letterDet]
  congr 1
  refine Matrix.ext fun b c => ?_
  simp

/- English proof (translation)
Establish `h01 : ∀ (P : Prop) [Decidable P], V.Ge 0 (if P then (1 : K) else 0)`. Introduce `P _`. Use `split_ifs`. Use `exacts [VF.Ge.one, VF.Ge.zero _]`. Use `⟨⟨fun c x => h01 _, fun x c => if x = p c then 1 else 0, fun x c => h01 _, fun c c' => ?_⟩, fun c x hx => if_neg fun h => hx (by rw [h, hty])⟩` and prove the remaining obligations.

Simplify using `[hp.eq_iff, eq_comm]`.
-/
theorem satIn_single (X : RowData K V d I J) (g : Fin 2) (a : ZMod d) {N : ℕ} (p : Fin N → I g)
    (hp : Function.Injective p) (hty : ∀ c, (X.G g).ty (Sum.inl (p c)) = a) :
    X.SatIn g a fun b x => if x = p b then 1 else 0 := by
  have h01 : ∀ (P : Prop) [Decidable P], V.Ge 0 (if P then (1 : K) else 0) := by
    intro P _; split_ifs
    exacts [VF.Ge.one, VF.Ge.zero _]
  refine ⟨⟨fun c x => h01 _, fun x c => if x = p c then 1 else 0, fun x c => h01 _, fun c c' => ?_⟩,
    fun c x hx => if_neg fun h => hx (by rw [h, hty])⟩
  simp [hp.eq_iff, eq_comm]

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Express the relevant statement in the definitionally equal form `∑ j ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), coeff 0 (x ^ j) / (j.factorial : K) = 1`. Simplify using the standard rewrite rules.
-/
theorem cc_mvExp' {σ : Type} (x : MvPowerSeries σ K) : constantCoeff (mvExp x) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  change ∑ j ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), coeff 0 (x ^ j) / (j.factorial : K) = 1
  simp

/- English proof (translation)
Rewrite using `[← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', jetAt0_monomial]`. Simplify using `[mfact]`.
-/
theorem jetAt0_one' {σ : Type} (G : MvPowerSeries σ K) : jetAt0 1 G = constantCoeff G := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', jetAt0_monomial]
  simp [mfact]

/- English proof (translation)
Unfold `S0`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (by omega : 1 < l)`. Establish `hn' : (n0 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `h0 : 0 ≤ Real.logb l ((n0 : ℝ) + 1)` using `Real.logb_nonneg hl1 (by linarith [Nat.cast_nonneg (α := ℝ) n0])`. Establish `h1 : Real.logb l ((n0 : ℝ) + 1) ≤ Real.logb l ((n : ℝ) + 1)` using `Real.logb_le_logb_of_le hl1 (by positivity) (by linarith)`.

Use `Nat.ceil_mono ?_` and prove the remaining obligations. Use `gcongr`.
-/
theorem mono_resι_var {l i n0 n : ℕ} (hl : 5 ≤ l) (hn : n0 ≤ n) : S0 l i n0 ≤ S0 l i n := by
  unfold S0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ Real.logb l ((n0 : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith [Nat.cast_nonneg (α := ℝ) n0])
  have h1 : Real.logb l ((n0 : ℝ) + 1) ≤ Real.logb l ((n : ℝ) + 1) :=
    Real.logb_le_logb_of_le hl1 (by positivity) (by linarith)
  refine Nat.ceil_mono ?_
  gcongr

/- English proof (translation)
Unfold `S0`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (by omega : 1 < l)`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `h0 : 0 ≤ Real.logb l ((n : ℝ) + 1)` using `Real.logb_nonneg hl1 (by linarith)`. Use `Nat.ceil_pos.2 ?_` and prove the remaining obligations.

Check the signs of the components of the expression.
-/
theorem sum_positive_of_five_le {l i n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) : 0 < S0 l i n := by
  unfold S0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ Real.logb l ((n : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith)
  refine Nat.ceil_pos.2 ?_
  positivity

/- English proof (translation)
Use `X.charZero` as an intermediate fact. Take `⟨n0, e, v', Φ, hM, -⟩` from `(GlobalTheory.T.rowData_mainTerm_normalForm_and_levelOne K V d I J X).1 hA hl g a ha i hi hid _ _ (satIn_single X g a p hp hty) (satIn_single X (1 - g) _ p' hp' hty')`. Establish `hn : n0 ≤ X.n` using `hM.1.2`. Take `⟨hR, hH1, hH2, -⟩` from `GlobalTheory.T.mainTerm_implies_rowHypothesis K V d I J X g a i _ _ n0 e v' Φ hM hn`. Take `⟨S, t, hSt, hr, tt, tt', hB, hy⟩` from `block_of_normal_form X g a i p p' hp hp' n0 e v' Φ hM hn _ hR`.

Establish `hrank : X.n - n0 ≤ (i + 1) * X.m`. Establish `h1` using `hM.1.1`. Establish `h2 : (i + 1) * X.m = (i + 1) * X.j' + X.j + i * X.j` using `by unfold RowData.m; ring`. Use linear arithmetic over natural numbers and integers. Establish `hgood : ∀ y : ℕ, V.v (jetAt0 (detL K X.n ^ (V.l ^ i * y) * detR K X.n ^ y) (BiF V.l i n0 X.n y hr tt tt')) ≤ (((bdP V.l i X.n X.n y + ((i : ℝ) + 1) * X.m * ((V.l : ℝ) ^ i + 1) * y / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ) ∨ y = 0 → ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ …`.

Introduce `y h`. Take `⟨gr, hgr, hv⟩` from `hy y`. Use `⟨gr, hgr, hv.trans ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : y = 0`. Substitute `h0` using the available equality.

Simplify using `only [blockBd, if_true, mul_zero, pow_zero, mul_one, jetAt0_one', BiF, ite_self, one_mul, map_prod, cc_mvExp', Finset.prod_const_one, V.v.map_one]`. Both sides reduce to the same expression. Rewrite using `[blockBd, if_neg h0]`. Conclude with `h.resolve_right h0`. Use `⟨⟨S, t, hSt, hgood 0 (Or.inr rfl)⟩, fun Y0 => ?_⟩` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos n0 with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Use `⟨Y0, ⟨S, t, hSt, hgood Y0 (Or.inl ?_)⟩, le_rfl, Nat.lt_add_of_pos_right (sum_positive_of_five_le hl hn1)⟩` and prove the remaining obligations. Establish `hl1 : (1 : ℝ) < V.l` using `by exact_mod_cast (by omega : 1 < V.l)`. Rewrite using `[GlobalTheory.T.blockValue_on_rows_eq K V.l i 0 X.n hn hr tt tt' _ hB Y0]`.

Use `(GlobalTheory.OddBlock.content_and_window.1 K V.v V.l V.l_prime hl V.v_l i X.n 0 Y0 hi hn1 hn _ ?_).trans ?_` and prove the remaining obligations. Establish `: LamP K V.l i 0 (X.restrictedCurveSystemSeries g a i hn e v') Y0 = 1`. Simplify using `[LamP, detL, detR, jetAt0_one', cc_mvExp']`. Rewrite using `[this, V.v.map_one]`. Establish `hn' : (1 : ℝ) ≤ X.n` using `by exact_mod_cast hn1`.

Establish `h0 : 0 ≤ Real.logb V.l (X.n : ℝ)` using `Real.logb_nonneg hl1 hn'`. Establish `: 0 ≤ bdP V.l i 0 X.n Y0`. Simplify using `only [bdP, Nat.cast_zero, zero_mul, zero_add]`. Check the signs of the components of the expression. Conclude with `this` after adjusting the coercions.

Rewrite using `[WithTop.coe_le_coe]`. Establish `h3 : ((X.n : ℝ) - ((0 : ℕ) : ℝ)) ≤ ((i : ℝ) + 1) * X.m`. Rewrite using `[Nat.cast_zero, sub_zero]`. Conclude with `hrank` after adjusting the coercions. Establish `: (0 : ℝ) < (V.l : ℝ) - 1` using `by linarith`.

Use `gcongr`. Take `⟨y, h1, h2, h3⟩` from `GlobalTheory.OddBlock.content_and_window.2 K V.v V.l V.l_prime hl V.v_l i hi n0 X.n X.m hn h0 hrank hr tt tt' _ hB hH1 hH2 Y0`. Conclude with `⟨y, ⟨S, t, hSt, hgood y (Or.inl h3)⟩, h1, h2.trans_le (Nat.add_le_add_left (mono_resι_var hl hn) _)⟩`.
-/
theorem window_letterDet (X : RowData K V d I J) (hA : X.Alt) (hl : 5 ≤ V.l) (hn1 : 1 ≤ X.n)
    (g : Fin 2) (a : ZMod d) (ha : X.big g a) (i : ℕ) (hi : Odd i) (hid : i < d)
    (p : Fin X.n → I g) (p' : Fin X.n → I (1 - g)) (hp : Function.Injective p) (hp' : Function.Injective p')
    (hty : ∀ c, (X.G g).ty (Sum.inl (p c)) = a)
    (hty' : ∀ c, (X.G (1 - g)).ty (Sum.inl (p' c)) = a + (i : ZMod d)) :
    Windows (S0 V.l i X.n) {y | ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) K),
      (∀ g, (S g).IsT (t g)) ∧ ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (letterDet K g p ^ (V.l ^ i * y) * letterDet K (1 - g) p' ^ y)
          (fun _ => some (g, a, a + (i : ZMod d))) gr) ≤ ((blockBd V.l X.n X.m i y : ℝ) : WithTop ℝ)} := by
  have := X.charZero
  obtain ⟨n0, e, v', Φ, hM, -⟩ := (GlobalTheory.T.rowData_mainTerm_normalForm_and_levelOne K V d I J X).1 hA hl g a ha i hi hid _ _
    (satIn_single X g a p hp hty) (satIn_single X (1 - g) _ p' hp' hty')
  have hn : n0 ≤ X.n := hM.1.2
  obtain ⟨hR, hH1, hH2, -⟩ := GlobalTheory.T.mainTerm_implies_rowHypothesis K V d I J X g a i _ _ n0 e v' Φ hM hn
  obtain ⟨S, t, hSt, hr, tt, tt', hB, hy⟩ :=
    block_of_normal_form X g a i p p' hp hp' n0 e v' Φ hM hn _ hR
  have hrank : X.n - n0 ≤ (i + 1) * X.m := by
    have h1 := hM.1.1
    have h2 : (i + 1) * X.m = (i + 1) * X.j' + X.j + i * X.j := by unfold RowData.m; ring
    omega
  have hgood : ∀ y : ℕ, V.v (jetAt0 (detL K X.n ^ (V.l ^ i * y) * detR K X.n ^ y)
      (BiF V.l i n0 X.n y hr tt tt')) ≤ (((bdP V.l i X.n X.n y + ((i : ℝ) + 1) * X.m * ((V.l : ℝ) ^ i + 1) * y /
        ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ) ∨ y = 0 →
      ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (letterDet K g p ^ (V.l ^ i * y) * letterDet K (1 - g) p' ^ y)
          (fun _ => some (g, a, a + (i : ZMod d))) gr) ≤ ((blockBd V.l X.n X.m i y : ℝ) : WithTop ℝ) := by
    intro y h
    obtain ⟨gr, hgr, hv⟩ := hy y
    refine ⟨gr, hgr, hv.trans ?_⟩
    by_cases h0 : y = 0
    · subst h0
      simp only [blockBd, if_true, mul_zero, pow_zero, mul_one, jetAt0_one', BiF, ite_self, one_mul, map_prod,
        cc_mvExp', Finset.prod_const_one, V.v.map_one]
      rfl
    · rw [blockBd, if_neg h0]
      exact h.resolve_right h0
  refine ⟨⟨S, t, hSt, hgood 0 (Or.inr rfl)⟩, fun Y0 => ?_⟩
  rcases Nat.eq_zero_or_pos n0 with h0 | h0
  · subst h0
    refine ⟨Y0, ⟨S, t, hSt, hgood Y0 (Or.inl ?_)⟩, le_rfl, Nat.lt_add_of_pos_right (sum_positive_of_five_le hl hn1)⟩
    have hl1 : (1 : ℝ) < V.l := by exact_mod_cast (by omega : 1 < V.l)
    rw [GlobalTheory.T.blockValue_on_rows_eq K V.l i 0 X.n hn hr tt tt' _ hB Y0]
    refine (GlobalTheory.OddBlock.content_and_window.1 K V.v V.l V.l_prime hl V.v_l i X.n 0 Y0 hi hn1 hn _ ?_).trans ?_
    · have : LamP K V.l i 0 (X.restrictedCurveSystemSeries g a i hn e v') Y0 = 1 := by
        simp [LamP, detL, detR, jetAt0_one', cc_mvExp']
      rw [this, V.v.map_one]
      have hn' : (1 : ℝ) ≤ X.n := by exact_mod_cast hn1
      have h0 : 0 ≤ Real.logb V.l (X.n : ℝ) := Real.logb_nonneg hl1 hn'
      have : 0 ≤ bdP V.l i 0 X.n Y0 := by
        simp only [bdP, Nat.cast_zero, zero_mul, zero_add]; positivity
      exact_mod_cast this
    · rw [WithTop.coe_le_coe]
      have h3 : ((X.n : ℝ) - ((0 : ℕ) : ℝ)) ≤ ((i : ℝ) + 1) * X.m := by
        rw [Nat.cast_zero, sub_zero]; exact_mod_cast hrank
      have : (0 : ℝ) < (V.l : ℝ) - 1 := by linarith
      gcongr
  · obtain ⟨y, h1, h2, h3⟩ := GlobalTheory.OddBlock.content_and_window.2 K V.v V.l V.l_prime hl V.v_l i hi n0 X.n X.m hn h0 hrank hr tt tt' _
      hB hH1 hH2 Y0
    exact ⟨y, ⟨S, t, hSt, hgood y (Or.inl h3)⟩, h1, h2.trans_le (Nat.add_le_add_left (mono_resι_var hl hn) _)⟩

end GlobalTheory.MinorShiftJet

namespace GlobalTheory

open MinorShiftJet

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid`. Establish `h1 : X.n ≤ X.rk g a` using `(Nat.le_add_right _ _).trans (X.rk_big g a ha).ge`. Establish `h2 : X.n ≤ X.rk (1 - g) (a + (i : ZMod d))` using `(Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge`. Establish `key` using `window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c)) (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c)) ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2)) (fun c => F.en_ty _ _ _) (fun c => F.en_t …`.

Rewrite `key` using `[← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))]`. Conclude with `key`. Introduce `K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid`. Establish `h1 : X.n ≤ X.rkF g a` using `(Nat.le_add_right _ _).trans (X.rk_big g a ha).ge`. Establish `h2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d))` using `(Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge`.

Establish `key` using `window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c)) (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c)) ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2)) (fun c => F.en_ty _ _ _) (fun c => F.en_t …`. Rewrite `key` using `[← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))]`. Conclude with `key`.
-/
theorem oddBlock_supply : BiSupply ∧ RF.BiSupply := by
  constructor
  · intro K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid
    have h1 : X.n ≤ X.rk g a := (Nat.le_add_right _ _).trans (X.rk_big g a ha).ge
    have h2 : X.n ≤ X.rk (1 - g) (a + (i : ZMod d)) :=
      (Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge
    have key := window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c))
      (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c))
      ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2))
      (fun c => F.en_ty _ _ _) (fun c => F.en_ty _ _ _)
    rw [← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))] at key
    exact key
  · intro K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid
    have h1 : X.n ≤ X.rkF g a := (Nat.le_add_right _ _).trans (X.rk_big g a ha).ge
    have h2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d)) :=
      (Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge
    have key := window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c))
      (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c))
      ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2))
      (fun c => F.en_ty _ _ _) (fun c => F.en_ty _ _ _)
    rw [← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))] at key
    exact key

end GlobalTheory
