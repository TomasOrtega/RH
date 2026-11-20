import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.CharBlock

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries

variable {C : Type} [Field C]

def IsExp {σ : Type} (y : σ → C) (F : MvPowerSeries σ C) : Prop :=
  constantCoeff F = 1 ∧ ∀ w, pderiv C w F = y w • F

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp, fun w => by simp⟩`.
-/
theorem IsExp.one {σ : Type} : IsExp (fun _ : σ => (0 : C)) 1 := ⟨by simp, fun w => by simp⟩

/- English proof (translation)
Use `⟨by rw [map_mul, h.1, h'.1, one_mul], fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, h.2, h'.2]`. Simplify using `only [smul_eq_mul, add_smul, mul_smul_comm]`. Rewrite using `[add_comm, mul_comm F' F]`.
-/
theorem IsExp.mul {σ : Type} {y y' : σ → C} {F F' : MvPowerSeries σ C} (h : IsExp y F)
    (h' : IsExp y' F') : IsExp (fun w => y w + y' w) (F * F') := by
  refine ⟨by rw [map_mul, h.1, h'.1, one_mul], fun w => ?_⟩
  rw [Derivation.leibniz, h.2, h'.2]
  simp only [smul_eq_mul, add_smul, mul_smul_comm]
  rw [add_comm, mul_comm F' F]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using IsExp.one`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `(h a).mul ih`.
-/
theorem IsExp.prod {σ α : Type} (s : Finset α) {y : α → σ → C} {F : α → MvPowerSeries σ C}
    (h : ∀ i, IsExp (y i) (F i)) : IsExp (fun w => ∑ i ∈ s, y i w) (∏ i ∈ s, F i) := by
  induction s using Finset.induction_on with
  | empty => simpa using IsExp.one
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a).mul ih

/- English proof (translation)
Establish `hs : HasSubst (fun j => (X (e j) : MvPowerSeries τ C))` using `hasSubst_of_constantCoeff_zero (by simp)`. Prove the components needed by the constructor for the conclusion. Use `rename_eq_subst (R := C) (f := e) (p := F)` as an intermediate fact. Establish `h2` using `constantCoeff_rename (R := C) (f := e) F`. Rewrite `h2` using `[this, h.1]`.

Conclude with `h2`. Introduce `w`. Rewrite using `[Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h.2, subst_smul hs]`.

Distinguish the cases in `hj : e j = w`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj, pderiv_X_of_ne hj]`.
-/
theorem IsExp.subst {σ τ : Type} [Fintype σ] [Finite τ] {y : σ → C} {F : MvPowerSeries σ C}
    (h : IsExp y F) (e : σ → τ) :
    IsExp (fun t => ∑ j, if e j = t then y j else 0)
      (F.subst fun j => (X (e j) : MvPowerSeries τ C)) := by
  have hs : HasSubst (fun j => (X (e j) : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  constructor
  · have := rename_eq_subst (R := C) (f := e) (p := F)
    have h2 := constantCoeff_rename (R := C) (f := e) F
    rw [this, h.1] at h2
    exact h2
  · intro w
    rw [Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h.2, subst_smul hs]
    by_cases hj : e j = w
    · subst hj; simp
    · simp [hj, pderiv_X_of_ne hj]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `m hm`. Rewrite `hm` using `[Finsupp.degree_eq_zero_iff]`.

Substitute `hm` using the available equality. Simplify using `[mfact, h.1]`. Consider the case `succ n ih`. Introduce `m hm`. Establish `hne : m ≠ 0` using `by rintro rfl; simp at hm`.

Take `⟨w, hw⟩` from `Finsupp.ne_iff.1 hne`. Choose the witnesses or unpack the hypotheses as in `⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by`. Use `⟨m - Finsupp.single w 1, ?_⟩` and prove the remaining obligations. Rewrite using `[tsub_add_cancel_of_le]`. Rewrite using `[Finsupp.single_le_iff]`.

Simplify using `at hw`. Use linear arithmetic over natural numbers and integers. Establish `hd : m'.degree = n`. Rewrite `hm` using `[map_add, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `congrArg (MvPowerSeries.coeff m') (h.2 w)`. Rewrite `h1` using `[coeff_pderiv, coeff_smul]`. Establish `h2 : mfact (m' + Finsupp.single w 1) = (m' w + 1) * mfact m'`. Unfold `mfact`. Establish `e1` using `Finsupp.mul_prod_erase' (m' + Finsupp.single w 1) w (fun _ k => k.factorial) (by simp)`.

Establish `e2` using `Finsupp.mul_prod_erase' m' w (fun _ k => k.factorial) (by simp)`. Rewrite using `[← e1, ← e2, Finsupp.erase_add, Finsupp.erase_single, add_zero]`. Simplify using `[Nat.factorial_succ, mul_assoc]`. Rewrite using `[Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), ← ih m' hd, h2, Finsupp.prod_single_index (by simp)]`. Use `push_cast`.

Take the linear combination `(mfact m' : C) * h1`.
-/
theorem IsExp.coeff {σ : Type} {y : σ → C} {F : MvPowerSeries σ C} (h : IsExp y F) :
    ∀ (n : ℕ) (m : σ →₀ ℕ), m.degree = n →
      (mfact m : C) * coeff m F = m.prod fun s k => y s ^ k := by
  intro n
  induction n with
  | zero =>
    intro m hm
    rw [Finsupp.degree_eq_zero_iff] at hm
    subst hm
    simp [mfact, h.1]
  | succ n ih =>
    intro m hm
    have hne : m ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hne
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
      refine ⟨m - Finsupp.single w 1, ?_⟩
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      simp at hw; omega
    have hd : m'.degree = n := by
      rw [map_add, Finsupp.degree_single] at hm; omega
    have h1 := congrArg (MvPowerSeries.coeff m') (h.2 w)
    rw [coeff_pderiv, coeff_smul] at h1
    have h2 : mfact (m' + Finsupp.single w 1) = (m' w + 1) * mfact m' := by
      unfold mfact
      have e1 := Finsupp.mul_prod_erase' (m' + Finsupp.single w 1) w (fun _ k => k.factorial) (by simp)
      have e2 := Finsupp.mul_prod_erase' m' w (fun _ k => k.factorial) (by simp)
      rw [← e1, ← e2, Finsupp.erase_add, Finsupp.erase_single, add_zero]
      simp [Nat.factorial_succ, mul_assoc]
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), ← ih m' hd, h2,
      Finsupp.prod_single_index (by simp)]
    push_cast
    linear_combination (mfact m' : C) * h1

/- English proof (translation)
Unfold `jetAt0`. Rewrite using `[MvPolynomial.eval_eq]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, h.coeff _ m rfl]`. Both sides reduce to the same expression.
-/
theorem IsExp.jet {σ : Type} {y : σ → C} {F : MvPowerSeries σ C} (h : IsExp y F)
    (P : MvPolynomial σ C) : jetAt0 P F = MvPolynomial.eval y P := by
  unfold jetAt0
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, h.coeff _ m rfl]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_mvExp {σ : Type} (h : MvPowerSeries σ C) (m : σ →₀ ℕ) :
    coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) := rfl

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_mvExp, Finset.sum_range_succ']`. Simplify using the standard rewrite rules.
-/
theorem mvExp_zero {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  rw [coeff_mvExp, Finset.sum_range_succ']
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_mvExp]`. Simplify using the standard rewrite rules. Introduce `w`. Use extensionality with `m`.

Establish `hL : pderiv C w (∑ x, y x • (X x : MvPowerSeries σ C)) = MvPowerSeries.C (y w)`. Rewrite using `[map_sum, Finset.sum_eq_single w]`. Simplify using `[smul_eq_C_mul]`. Introduce `b _ hb`. Simplify using `[pderiv_X_of_ne hb]`.

Simplify using the standard rewrite rules. Rewrite using `[coeff_pderiv, coeff_smul, coeff_mvExp, coeff_mvExp, map_add, Finsupp.degree_single, Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]`. Establish `h0 : MvPowerSeries.coeff (m + Finsupp.single w 1) ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ 0) = 0`. Rewrite using `[pow_zero, coeff_one, if_neg]`. Introduce `h`.

Use `DFunLike.congr_fun h w` as an intermediate fact. Simplify using `at this`. Rewrite using `[h0, zero_div, zero_mul, add_zero]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h1` using `coeff_pderiv (i := w) ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ (k + 1)) m`.

Rewrite `h1` using `[pderiv_pow, hL, Nat.add_sub_cancel, ← map_natCast (MvPowerSeries.C (σ := σ) (R := C)), coeff_mul_C, coeff_C_mul]`. Establish `hk : (k.factorial : C) ≠ 0` using `by exact_mod_cast k.factorial_ne_zero`. Establish `hk1 : ((k + 1 : ℕ) : C) ≠ 0` using `by exact_mod_cast k.succ_ne_zero`. Rewrite using `[div_mul_eq_mul_div, ← h1, Nat.factorial_succ]`. Move the coercions through the operations in `at hk1 ⊢`.

Clear the denominators using the available nonvanishing facts.
-/
theorem isExp_mvExp [CharZero C] {σ : Type} [Fintype σ] (y : σ → C) :
    IsExp y (mvExp (∑ x, y x • (X x : MvPowerSeries σ C))) := by
  constructor
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mvExp]; simp
  · intro w
    ext m
    have hL : pderiv C w (∑ x, y x • (X x : MvPowerSeries σ C)) = MvPowerSeries.C (y w) := by
      rw [map_sum, Finset.sum_eq_single w]
      · simp [smul_eq_C_mul]
      · intro b _ hb; simp [pderiv_X_of_ne hb]
      · simp
    rw [coeff_pderiv, coeff_smul, coeff_mvExp, coeff_mvExp, map_add, Finsupp.degree_single,
      Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
    have h0 : MvPowerSeries.coeff (m + Finsupp.single w 1)
        ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ 0) = 0 := by
      rw [pow_zero, coeff_one, if_neg]
      intro h
      have := DFunLike.congr_fun h w
      simp at this
    rw [h0, zero_div, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := coeff_pderiv (i := w) ((∑ x, y x • (X x : MvPowerSeries σ C)) ^ (k + 1)) m
    rw [pderiv_pow, hL, Nat.add_sub_cancel, ← map_natCast (MvPowerSeries.C (σ := σ) (R := C)),
      coeff_mul_C, coeff_C_mul] at h1
    have hk : (k.factorial : C) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hk1 : ((k + 1 : ℕ) : C) ≠ 0 := by exact_mod_cast k.succ_ne_zero
    rw [div_mul_eq_mul_div, ← h1, Nat.factorial_succ]
    push_cast at hk1 ⊢
    field_simp

variable {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def stdSys {I J : Type} [Fintype I] [Fintype J] (X : Cart V d I J) : Sys X where
  tan := fun c => Pi.single c 1
  cur := fun c => X.std c
  curve := fun c => X.std_spec c
  unimod := by
    have : (Matrix.of fun c : I => (Pi.single c 1 : I → C)) = 1 := by
      ext a b
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one, AddValuation.map_one]

/- English proof (translation)
Unfold `ValOf`. Establish `h0 : ∀ ρ : Fin n, mvExp (rowCopy ρ (0 : MvPowerSeries (WV I) C)) = 1`. Introduce `ρ`. Establish `: rowCopy ρ (0 : MvPowerSeries (WV I) C) = 0`. Unfold `rowCopy`.

Establish `hs : HasSubst (fun w : WV I => (X (ρ, w) : MvPowerSeries (Fin n × WV I) C))` using `hasSubst_of_constantCoeff_zero (by simp)`. Rewrite using `[← coe_substAlgHom hs, map_zero]`. Rewrite using `[this, mvExp_zero]`. Simplify using `only [h0, mul_one]`. Establish `h1` using `IsExp.prod Finset.univ fun ρ : Fin n => ((isExp_mvExp (y ρ)).subst fun x : I g => (⟨g, x⟩ : WV I)).subst fun w : WV I => ((ρ, w) : Fin n × WV I)`.

Use `(h1.jet _).trans ?_` and prove the remaining obligations. Rewrite using `[map_pow, MvPolynomial.eval_rename, minorK, dif_pos ⟨le_rfl, hn⟩, RingHom.map_det]`. Use `congr 2`. Use extensionality with `ρ c`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X, Function.comp_apply, Fin.castLE_refl, Prod.mk.injEq]`.

Rewrite using `[Finset.sum_eq_single ρ, Finset.sum_eq_single (⟨g, en (Fin.castLE hn c)⟩ : WV I), Finset.sum_eq_single (en (Fin.castLE hn c))]`. Apply the tactic sequence `all_goals simp +contextual`.
-/
theorem val_eq [CharZero C] (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (g : Fin 2)
    {n r : ℕ} (hn : n ≤ r) (en : Fin r → I g) (y : Fin n → I g → C) (u : ℕ) :
    ValOf hL (MvPolynomial.rename (fun x : Fin n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin n × WV I))
        (minorK C n r n) ^ u) (fun _ => none)
      (fun ρ => upG g (mvExp (∑ x : I g, y ρ x • (X x : MvPowerSeries (I g) C)))) =
    (Matrix.of fun ρ c : Fin n => y ρ (en (Fin.castLE hn c))).det ^ u := by
  unfold ValOf
  have h0 : ∀ ρ : Fin n, mvExp (rowCopy ρ (0 : MvPowerSeries (WV I) C)) = 1 := by
    intro ρ
    have : rowCopy ρ (0 : MvPowerSeries (WV I) C) = 0 := by
      unfold rowCopy
      have hs : HasSubst (fun w : WV I => (X (ρ, w) : MvPowerSeries (Fin n × WV I) C)) :=
        hasSubst_of_constantCoeff_zero (by simp)
      rw [← coe_substAlgHom hs, map_zero]
    rw [this, mvExp_zero]
  simp only [h0, mul_one]
  have h1 := IsExp.prod Finset.univ fun ρ : Fin n =>
    ((isExp_mvExp (y ρ)).subst fun x : I g => (⟨g, x⟩ : WV I)).subst
      fun w : WV I => ((ρ, w) : Fin n × WV I)
  refine (h1.jet _).trans ?_
  rw [map_pow, MvPolynomial.eval_rename, minorK, dif_pos ⟨le_rfl, hn⟩, RingHom.map_det]
  congr 2
  ext ρ c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
    Function.comp_apply, Fin.castLE_refl, Prod.mk.injEq]
  rw [Finset.sum_eq_single ρ, Finset.sum_eq_single (⟨g, en (Fin.castLE hn c)⟩ : WV I),
    Finset.sum_eq_single (en (Fin.castLE hn c))]
  all_goals simp +contextual

/- English proof (translation)
Use `haveI := X.charZero`. Use `choose t ht _ using fun g => tExistsUnique (X.G g) (stdSys (X.G g))`. Establish `hint : ∀ (c x : I g), V.Ge 0 ((Pi.single c 1 : I g → C) x)`. Introduce `c x`. Rewrite using `[Pi.single_apply]`.

Use `split_ifs`. Conclude with `VF.Ge.one`. Conclude with `VF.Ge.zero 0`. Take `⟨y, -, hy, h1, h2⟩` from `X.CH g a ha (fun c => Pi.single (en (Fin.castLE hn c)) 1) ⟨fun c x => hint _ _, fun x c => (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x, fun x c => hint _ _, fun c c' => by`. Simplify using `[Pi.single_apply, hinj.eq_iff, (Fin.castLE_injective hn).eq_iff, eq_comm]⟩`.

Use the proof step `(fun c x hx => Pi.single_eq_of_ne (fun h => hx (by rw [h]; exact hty _)) _)`. Establish `key : ∀ b : ℝ, V.v (Matrix.of fun ρ c : Fin X.n => ∑ x, y ρ x * (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x).det ≤ (b : WithTop ℝ) → V.v ((Matrix.of fun ρ c : Fin X.n => y ρ (en (Fin.castLE hn c))).det ^ u) ≤ (((u : ℝ) * b : ℝ) : WithTop ℝ)`. Introduce `b hb`. Simplify using `only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hb`. Rewrite using `[AddValuation.map_pow, ← nsmul_eq_mul, WithTop.coe_nsmul]`.

Conclude with `nsmul_le_nsmul_right hb u`. Use `⟨fun g => stdSys (X.G g), t, ht, _, hy _ t ht, fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[val_eq X.hL g hn en y u]`. Simplify `key _ (h1 h)` using `[RowData.m]`. Rewrite using `[val_eq X.hL g hn en y u]`.

Simplify `key _ (h2 h)` using `[RowData.m]`.
-/
theorem core (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (ha : X.big g a) {r : ℕ}
    (hn : X.n ≤ r) (en : Fin r → I g) (hinj : Function.Injective en)
    (hty : ∀ c, (X.G g).ty (Sum.inl (en c)) = a) (u : ℕ) :
    ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
      ∃ gr : Fin X.n → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        (X.Alt → V.v (ValOf X.hL (MvPolynomial.rename
          (fun x : Fin X.n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin X.n × WV I))
          (minorK C X.n r X.n) ^ u) (fun _ => none) gr) ≤
          (((u : ℝ) * (X.n * gam V.l + X.m / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ)) ∧
        ((∀ a, X.big g a) → V.v (ValOf X.hL (MvPolynomial.rename
          (fun x : Fin X.n × Fin r => ((x.1, ⟨g, en x.2⟩) : Fin X.n × WV I))
          (minorK C X.n r X.n) ^ u) (fun _ => none) gr) ≤
          (((u : ℝ) * (X.m / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ)) := by
  haveI := X.charZero
  choose t ht _ using fun g => tExistsUnique (X.G g) (stdSys (X.G g))
  have hint : ∀ (c x : I g), V.Ge 0 ((Pi.single c 1 : I g → C) x) := by
    intro c x
    rw [Pi.single_apply]
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  obtain ⟨y, -, hy, h1, h2⟩ := X.CH g a ha (fun c => Pi.single (en (Fin.castLE hn c)) 1)
    ⟨fun c x => hint _ _, fun x c => (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x,
      fun x c => hint _ _, fun c c' => by
        simp [Pi.single_apply, hinj.eq_iff, (Fin.castLE_injective hn).eq_iff, eq_comm]⟩
    (fun c x hx => Pi.single_eq_of_ne (fun h => hx (by rw [h]; exact hty _)) _)
  have key : ∀ b : ℝ, V.v (Matrix.of fun ρ c : Fin X.n =>
        ∑ x, y ρ x * (Pi.single (en (Fin.castLE hn c)) 1 : I g → C) x).det ≤ (b : WithTop ℝ) →
      V.v ((Matrix.of fun ρ c : Fin X.n => y ρ (en (Fin.castLE hn c))).det ^ u) ≤
        (((u : ℝ) * b : ℝ) : WithTop ℝ) := by
    intro b hb
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hb
    rw [AddValuation.map_pow, ← nsmul_eq_mul, WithTop.coe_nsmul]
    exact nsmul_le_nsmul_right hb u
  refine ⟨fun g => stdSys (X.G g), t, ht, _, hy _ t ht, fun h => ?_, fun h => ?_⟩
  · rw [val_eq X.hL g hn en y u]
    simpa [RowData.m] using key _ (h1 h)
  · rw [val_eq X.hL g hn en y u]
    simpa [RowData.m] using key _ (h2 h)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `C _ V d _ I J _ _ X F g a ha u`. Establish `hn : X.n ≤ X.rk g a`. Unfold `RowData.rk`. Rewrite using `[X.rk_big g a ha]`.

Use linear arithmetic over natural numbers and integers. Take `⟨S, t, ht, gr, hgr, h1, h2⟩` from `core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u`. Conclude with `⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩`. Introduce `C _ V d _ I J _ _ X F g a ha u`. Establish `hn : X.n ≤ X.rkF g a`.

Unfold `RowData.rkF`. Rewrite using `[X.rk_big g a ha]`. Use linear arithmetic over natural numbers and integers. Take `⟨S, t, ht, gr, hgr, h1, h2⟩` from `core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u`. Conclude with `⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩`.
-/
theorem chSupply : CHSupply ∧ RF.CHSupply := by
  constructor
  · intro C _ V d _ I J _ _ X F g a ha u
    have hn : X.n ≤ X.rk g a := by
      unfold RowData.rk; rw [X.rk_big g a ha]; omega
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ := core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u
    exact ⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩
  · intro C _ V d _ I J _ _ X F g a ha u
    have hn : X.n ≤ X.rkF g a := by
      unfold RowData.rkF; rw [X.rk_big g a ha]; omega
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ := core X g a ha hn (F.en g a) (F.en_inj g a) (F.en_ty g a) u
    exact ⟨fun h => ⟨S, t, ht, gr, hgr, h1 h⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩

end GlobalTheory.CharBlock
