import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ProdFactorialDiag
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound

noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.MonBlock

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries GlobalTheory.MinorGerm

variable {C : Type} [Field C]

def Tan {σ : Type} (x : σ) (F : MvPowerSeries σ C) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree ≤ 1 → coeff m F = coeff m (X x : MvPowerSeries σ C)

/- English proof (translation)
Introduce `m hm`. Establish `h1 : rename e F = F.subst fun j => (X (e j) : MvPowerSeries τ C)` using `rename_eq_subst e F`. Rewrite using `[← h1, ← rename_X e x, coeff_rename, coeff_rename]`. Use `Finset.sum_congr rfl fun y hy => h y ?_` and prove the remaining obligations. Establish `: Finsupp.mapDomain e y = m` using `by simpa using hy`.

Rewrite `hm` using `[← this, Finsupp.degree_mapDomain]`. Conclude with `hm`.
-/
theorem Tan.subst {σ τ : Type} [Finite σ] {x : σ} {F : MvPowerSeries σ C} (h : Tan x F) (e : σ → τ) :
    Tan (e x) (F.subst fun j => (X (e j) : MvPowerSeries τ C)) := by
  intro m hm
  have h1 : rename e F = F.subst fun j => (X (e j) : MvPowerSeries τ C) := rename_eq_subst e F
  rw [← h1, ← rename_X e x, coeff_rename, coeff_rename]
  refine Finset.sum_congr rfl fun y hy => h y ?_
  have : Finsupp.mapDomain e y = m := by simpa using hy
  rw [← this, Finsupp.degree_mapDomain] at hm
  exact hm

variable {V : VF C} {d : ℕ}

/- English proof (translation)
Introduce `m hm`. Establish `h` using `ht.2 x m`. Rewrite `h` using `[Sys.eqn_eq]`. Establish `h2 : (GlobalTheory.CharBlock.stdSys X).Rr t x m = 0`. Unfold `Sys.Rr`.

Use `Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Establish `h3` using `le_order_pow_of_constantCoeff_eq_zero (V.l ^ (s + 1)) (ht.1 c)`. Establish `h4` using `Sys.two_le_pow (V := V) s`. Rewrite using `[coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (by omega)) h3), mul_zero]`. Establish `h5 : (GlobalTheory.CharBlock.stdSys X).Mt = 1`.

Use extensionality with `a b`. Simplify using `[Sys.Mt, GlobalTheory.CharBlock.stdSys, Matrix.one_apply, Pi.single_apply, eq_comm]`. Rewrite `h` using `[h2, h5, Matrix.vecMul_one, add_zero]`. Rewrite using `[coeff_X]`. Use `h` and compare the differences between its conclusion and the goal.
-/
theorem tan_std {I J : Type} [Fintype I] [Fintype J] (X : Cart V d I J)
    {t : I → MvPowerSeries I C} (ht : (GlobalTheory.CharBlock.stdSys X).IsT t) (x : I) : Tan x (t x) := by
  intro m hm
  have h := ht.2 x m
  rw [Sys.eqn_eq] at h
  have h2 : (GlobalTheory.CharBlock.stdSys X).Rr t x m = 0 := by
    unfold Sys.Rr
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun c _ => ?_
    have h3 := le_order_pow_of_constantCoeff_eq_zero (V.l ^ (s + 1)) (ht.1 c)
    have h4 := Sys.two_le_pow (V := V) s
    rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (by omega)) h3), mul_zero]
  have h5 : (GlobalTheory.CharBlock.stdSys X).Mt = 1 := by
    ext a b
    simp [Sys.Mt, GlobalTheory.CharBlock.stdSys, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h2, h5, Matrix.vecMul_one, add_zero] at h
  rw [coeff_X]
  convert h

variable {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

/- English proof (translation)
Establish `h1 : rename (fun x : I g => (⟨g, x⟩ : WV I)) F = upG g F` using `rename_eq_subst _ F`. Rewrite using `[← h1, constantCoeff_rename]`.
-/
theorem cc_upG (g : Fin 2) (F : MvPowerSeries (I g) C) :
    constantCoeff (upG g F) = constantCoeff F := by
  have h1 : rename (fun x : I g => (⟨g, x⟩ : WV I)) F = upG g F := rename_eq_subst _ F
  rw [← h1, constantCoeff_rename]

def IsMon (t : ∀ g, I g → MvPowerSeries (I g) C) (F : MvPowerSeries (WV I) C) : Prop :=
  ∃ m : WV I →₀ ℕ, F = subst (fun w : WV I => upG w.1 (t w.1 w.2)) (monomial m (1 : C))

section
variable {t : ∀ g, I g → MvPowerSeries (I g) C} (h0 : ∀ g c, constantCoeff (t g c) = 0)
include h0

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun w => by rw [cc_upG, h0]`.
-/
theorem hasSubst_upG_curveSystem : HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
  hasSubst_of_constantCoeff_zero fun w => by rw [cc_upG, h0]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by rw [← coe_substAlgHom (hasSubst_upG_curveSystem h0)]; exact (map_one _).symm⟩`.
-/
theorem isMon_one : IsMon t 1 :=
  ⟨0, by rw [← coe_substAlgHom (hasSubst_upG_curveSystem h0)]; exact (map_one _).symm⟩

/- English proof (translation)
Take `⟨m, rfl⟩` from `hF`. Take `⟨m', rfl⟩` from `hG`. Use `⟨m + m', ?_⟩` and prove the remaining obligations. Rewrite using `[← subst_mul (hasSubst_upG_curveSystem h0), monomial_mul_monomial, one_mul]`.
-/
theorem IsMon.mul {F G : MvPowerSeries (WV I) C} (hF : IsMon t F) (hG : IsMon t G) :
    IsMon t (F * G) := by
  obtain ⟨m, rfl⟩ := hF
  obtain ⟨m', rfl⟩ := hG
  refine ⟨m + m', ?_⟩
  rw [← subst_mul (hasSubst_upG_curveSystem h0), monomial_mul_monomial, one_mul]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using isMon_one h0`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Use `ih.mul h0 ⟨Finsupp.single ⟨g, c⟩ 1, ?_⟩` and prove the remaining obligations.

Conclude with `(subst_X (hasSubst_upG_curveSystem h0) (⟨g, c⟩ : WV I)).symm`.
-/
theorem isMon_pow (g : Fin 2) (c : I g) (n : ℕ) : IsMon t (upG g (t g c) ^ n) := by
  induction n with
  | zero => simpa using isMon_one h0
  | succ n ih =>
    rw [pow_succ]
    refine ih.mul h0 ⟨Finsupp.single ⟨g, c⟩ 1, ?_⟩
    exact (subst_X (hasSubst_upG_curveSystem h0) (⟨g, c⟩ : WV I)).symm

/- English proof (translation)
The claim follows from `Finset.prod_induction _ _ (fun _ _ => IsMon.mul h0) (isMon_one h0) fun i _ => h i`.
-/
theorem isMon_prod {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries (WV I) C)
    (h : ∀ i, IsMon t (F i)) : IsMon t (∏ i ∈ s, F i) :=
  Finset.prod_induction _ _ (fun _ _ => IsMon.mul h0) (isMon_one h0) fun i _ => h i

omit h0 in
/- English proof (translation)
Take `⟨m, rfl⟩` from `hF`. Use `⟨_, fun μ => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[coeff_monomial]`. Use `split_ifs`. Conclude with `VF.Ge.one`.

Conclude with `VF.Ge.zero 0`.
-/
theorem IsMon.mem {F : MvPowerSeries (WV I) C} (hF : IsMon t F) : F ∈ IntGerm V t := by
  obtain ⟨m, rfl⟩ := hF
  refine ⟨_, fun μ => ?_, rfl⟩
  rw [coeff_monomial]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

end

/- English proof (translation)
Rewrite using `[← sum_monAl, Fin.sum_univ_eq_sum_range (fun ρ => monAl N N' e ρ) N, dg, map_sum]`. Use `Finset.sum_congr rfl fun ρ hρ => ?_` and prove the remaining obligations. Unfold `dgOne`. Use `split_ifs with h`. Simplify using the standard rewrite rules.

Rewrite using `[monAl_eq_zero e fun h' => h ⟨Finset.mem_range.1 hρ, h'⟩, map_zero]`.
-/
theorem degree_dg {σ : Type} {N N' : ℕ} (j : Fin N × Fin N' → σ) (e : ℕ → ℕ) :
    (dg j (monAl N N' e)).degree = monDeg N N' e := by
  rw [← sum_monAl, Fin.sum_univ_eq_sum_range (fun ρ => monAl N N' e ρ) N, dg, map_sum]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  unfold dgOne
  split_ifs with h
  · simp
  · rw [monAl_eq_zero e fun h' => h ⟨Finset.mem_range.1 hρ, h'⟩, map_zero]

variable [NeZero d]

/- English proof (translation)
Use `choose t ht _ using fun g => tExistsUnique (X.G g) (GlobalTheory.CharBlock.stdSys (X.G g))`. Establish `h0 : ∀ g c, constantCoeff (t g c) = 0` using `fun g => (ht g).1`. Set `j : ∀ a, Fin N × Fin (r a) → Fin N × WV I` to `fun a x => (x.1, ⟨g, en a x.2⟩)`. Establish `hj : ∀ a a' y y', j a y = j a' y' → a = a'`. Introduce `a a' y y' h`.

Establish `h1 : en a y.2 = en a' y'.2` using `eq_of_heq (Sigma.mk.inj (Prod.mk.inj h).2).2`. Rewrite using `[← hty a y.2, h1, hty]`. Establish `hj' : ∀ a, Function.Injective (j a)`. Introduce `a y y' h`. Conclude with `Prod.ext (Prod.mk.inj h).1 (hinj a (eq_of_heq (Sigma.mk.inj (Prod.mk.inj h).2).2))`.

Set `T : Fin N × WV I → MvPowerSeries (Fin N × WV I) C` to `fun x => rowCopy x.1 (upG x.2.1 (t x.2.1 x.2.2))`. Establish `hT : TangentId T` using `fun x => ((tan_std _ (ht x.2.1) x.2.2).subst (fun c : I x.2.1 => (⟨x.2.1, c⟩ : WV I))).subst fun w : WV I => (x.1, w)`. Set `gr : Fin N → MvPowerSeries (WV I) C` to `fun ρ => ∏ a : ZMod d, if h : ρ.val < r a then upG g (t g (en a ⟨ρ.val, h⟩)) ^ monAl N (r a) (e a) ρ.val else 1`. Establish `hgr : ∀ ρ, gr ρ ∈ IntGerm V t` using `fun ρ => IsMon.mem <| isMon_prod h0 _ _ fun a => by split_ifs`. Conclude with `isMon_pow h0 _ _ _`.

Conclude with `isMon_one h0`. Establish `hlead` using `lead_prod (C := C) (p := fun x : Fin N × WV I => ∃ a y, x = j a y ∧ y.1.val = y.2.val) Finset.univ _ _ fun a _ => lead_monP (j a) (fun b c => ⟨fun ⟨a', y, h1, h2⟩ => by`. Take `rfl` from `hj _ _ _ _ h1`. Take `rfl` from `hj' _ h1`. Conclude with `h2, fun h => ⟨a, (b, c), rfl, h⟩⟩) (e a)`.

Establish `hlow` using `low_prod Finset.univ _ _ fun a _ => low_monG (j a) hT (e a)`. Establish `hval : ValOf X.hL (∏ a : ZMod d, MvPolynomial.rename (j a) (monP C N (r a) (e a))) (fun _ => none) gr = (mfact (∑ a, dg (j a) (monAl N (r a) (e a))) : C)`. Rewrite using `[← jet_eq hlead hlow]`. Unfold `ValOf`. Use `congr 1`.

Establish `hs : ∀ ρ : Fin N, HasSubst (fun w : WV I => (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WV I) C))` using `fun ρ => hasSubst_of_constantCoeff_zero (by simp)`. Unfold `monG`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Establish `hc : ∀ F, rowCopy ρ F = substAlgHom (hs ρ) F` using `fun F => by`.

Rewrite using `[coe_substAlgHom]`. Both sides reduce to the same expression. Rewrite using `[hc, hc, map_zero, GlobalTheory.CharBlock.mvExp_zero, mul_one, map_prod]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Rewrite using `[map_pow, ← hc]`. Rewrite using `[map_one]`. Use `⟨fun g => GlobalTheory.CharBlock.stdSys (X.G g), t, ht, gr, hgr, ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[hval, GlobalTheory.LegendreFacts.mfact_eq_prod, val_nat V.v V.l_prime V.v_l (Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _), WithTop.coe_le_coe, GlobalTheory.LegendreBounds.padicValNat_prod_factorial V.l V.l_prime]`. Establish `hd : ∑ a, monDeg N (r a) (e a) = ∑ x, (∑ a, dg (j a) (monAl N (r a) (e a))) x`.

Rewrite using `[← Finsupp.degree_eq_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => (degree_dg _ _).symm`. Rewrite using `[hd, Nat.cast_sum, Finset.sum_div]`. Conclude with `Finset.sum_le_sum fun ρ _ => GlobalTheory.LegendreBounds.upper V.l V.l_prime _`. Rewrite using `[hval, GlobalTheory.LegendreFacts.mfact_eq_prod]`.

Use `le_of_eq (val_coprime V.v V.l_prime V.v_l fun hd => ?_)` and prove the remaining obligations. Take `⟨x, -, hx⟩` from `(Prime.dvd_finset_prod_iff V.l_prime.prime _).1 hd`. Use `absurd ((V.l_prime.dvd_factorial).1 hx) (not_le.2 ?_)` and prove the remaining obligations. Rewrite using `[Finsupp.finset_sum_apply]`. Distinguish the cases in `hx' : ∃ a y, x = j a y`.

Take `⟨a, y, rfl⟩` from `hx'`. Rewrite using `[Finset.sum_eq_single a, dg_apply (j a) (hj' a) _ y.1 y.2]`. Use `split_ifs`. Conclude with `h _ _`. Conclude with `V.l_prime.pos`.

Introduce `a' _ ha`. Conclude with `dg_apply_of_notMem _ _ _ fun y' h' => ha (hj _ _ _ _ h').symm`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_zero fun a _ => dg_apply_of_notMem _ _ _ fun y' h' => hx' ⟨a, y', h'⟩]`. Conclude with `V.l_prime.pos`.
-/
theorem core (X : RowData C V d I J) (g : Fin 2) (r : ZMod d → ℕ) (en : ∀ a, Fin (r a) → I g)
    (hinj : ∀ a, Function.Injective (en a)) (hty : ∀ a c, (X.G g).ty (Sum.inl (en a c)) = a)
    (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
      ∃ gr : Fin N → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (∏ a : ZMod d, MvPolynomial.rename
          (fun x : Fin N × Fin (r a) => ((x.1, ⟨g, en a x.2⟩) : Fin N × WV I))
          (monP C N (r a) (e a))) (fun _ => none) gr) ≤
          (((((∑ a, monDeg N (r a) (e a) : ℕ) : ℝ) / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ) ∧
        ((∀ a ρ, monAl N (r a) (e a) ρ < V.l) → V.v (ValOf X.hL (∏ a : ZMod d, MvPolynomial.rename
          (fun x : Fin N × Fin (r a) => ((x.1, ⟨g, en a x.2⟩) : Fin N × WV I))
          (monP C N (r a) (e a))) (fun _ => none) gr) ≤ ((0 : ℝ) : WithTop ℝ)) := by
  choose t ht _ using fun g => tExistsUnique (X.G g) (GlobalTheory.CharBlock.stdSys (X.G g))
  have h0 : ∀ g c, constantCoeff (t g c) = 0 := fun g => (ht g).1
  let j : ∀ a, Fin N × Fin (r a) → Fin N × WV I := fun a x => (x.1, ⟨g, en a x.2⟩)
  have hj : ∀ a a' y y', j a y = j a' y' → a = a' := by
    intro a a' y y' h
    have h1 : en a y.2 = en a' y'.2 := eq_of_heq (Sigma.mk.inj (Prod.mk.inj h).2).2
    rw [← hty a y.2, h1, hty]
  have hj' : ∀ a, Function.Injective (j a) := by
    intro a y y' h
    exact Prod.ext (Prod.mk.inj h).1 (hinj a (eq_of_heq (Sigma.mk.inj (Prod.mk.inj h).2).2))
  let T : Fin N × WV I → MvPowerSeries (Fin N × WV I) C :=
    fun x => rowCopy x.1 (upG x.2.1 (t x.2.1 x.2.2))
  have hT : TangentId T := fun x =>
    ((tan_std _ (ht x.2.1) x.2.2).subst (fun c : I x.2.1 => (⟨x.2.1, c⟩ : WV I))).subst
      fun w : WV I => (x.1, w)
  let gr : Fin N → MvPowerSeries (WV I) C := fun ρ => ∏ a : ZMod d,
    if h : ρ.val < r a then upG g (t g (en a ⟨ρ.val, h⟩)) ^ monAl N (r a) (e a) ρ.val else 1
  have hgr : ∀ ρ, gr ρ ∈ IntGerm V t := fun ρ => IsMon.mem <| isMon_prod h0 _ _ fun a => by
    split_ifs
    · exact isMon_pow h0 _ _ _
    · exact isMon_one h0
  have hlead := lead_prod (C := C)
    (p := fun x : Fin N × WV I => ∃ a y, x = j a y ∧ y.1.val = y.2.val) Finset.univ _ _
    fun a _ => lead_monP (j a) (fun b c => ⟨fun ⟨a', y, h1, h2⟩ => by
      obtain rfl := hj _ _ _ _ h1
      obtain rfl := hj' _ h1
      exact h2, fun h => ⟨a, (b, c), rfl, h⟩⟩) (e a)
  have hlow := low_prod Finset.univ _ _ fun a _ => low_monG (j a) hT (e a)
  have hval : ValOf X.hL (∏ a : ZMod d, MvPolynomial.rename (j a) (monP C N (r a) (e a)))
      (fun _ => none) gr = (mfact (∑ a, dg (j a) (monAl N (r a) (e a))) : C) := by
    rw [← jet_eq hlead hlow]
    unfold ValOf
    congr 1
    have hs : ∀ ρ : Fin N, HasSubst
        (fun w : WV I => (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WV I) C)) :=
      fun ρ => hasSubst_of_constantCoeff_zero (by simp)
    unfold monG
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    have hc : ∀ F, rowCopy ρ F = substAlgHom (hs ρ) F := fun F => by
      rw [coe_substAlgHom]; rfl
    rw [hc, hc, map_zero, GlobalTheory.CharBlock.mvExp_zero, mul_one, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    split_ifs
    · rw [map_pow, ← hc]
    · rw [map_one]
  refine ⟨fun g => GlobalTheory.CharBlock.stdSys (X.G g), t, ht, gr, hgr, ?_, fun h => ?_⟩
  · rw [hval, GlobalTheory.LegendreFacts.mfact_eq_prod,
      val_nat V.v V.l_prime V.v_l (Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _),
      WithTop.coe_le_coe, GlobalTheory.LegendreBounds.padicValNat_prod_factorial V.l V.l_prime]
    have hd : ∑ a, monDeg N (r a) (e a) = ∑ x, (∑ a, dg (j a) (monAl N (r a) (e a))) x := by
      rw [← Finsupp.degree_eq_sum, map_sum]
      exact Finset.sum_congr rfl fun a _ => (degree_dg _ _).symm
    rw [hd, Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum fun ρ _ => GlobalTheory.LegendreBounds.upper V.l V.l_prime _
  · rw [hval, GlobalTheory.LegendreFacts.mfact_eq_prod]
    refine le_of_eq (val_coprime V.v V.l_prime V.v_l fun hd => ?_)
    obtain ⟨x, -, hx⟩ := (Prime.dvd_finset_prod_iff V.l_prime.prime _).1 hd
    refine absurd ((V.l_prime.dvd_factorial).1 hx) (not_le.2 ?_)
    rw [Finsupp.finset_sum_apply]
    by_cases hx' : ∃ a y, x = j a y
    · obtain ⟨a, y, rfl⟩ := hx'
      rw [Finset.sum_eq_single a, dg_apply (j a) (hj' a) _ y.1 y.2]
      · split_ifs
        · exact h _ _
        · exact V.l_prime.pos
      · intro a' _ ha
        exact dg_apply_of_notMem _ _ _ fun y' h' => ha (hj _ _ _ _ h').symm
      · simp
    · rw [Finset.sum_eq_zero fun a _ => dg_apply_of_notMem _ _ _ fun y' h' => hx' ⟨a, y', h'⟩]
      exact V.l_prime.pos

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `C _ V d _ I J _ _ X F g e N`. Take `⟨S, t, ht, gr, hgr, h1, h2⟩` from `core X g (X.rk g) (F.en g) (F.en_inj g) (F.en_ty g) e N`. Conclude with `⟨⟨S, t, ht, gr, hgr, h1⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩`. Introduce `C _ V d _ I J _ _ X F g e N`.

Take `⟨S, t, ht, gr, hgr, h1, h2⟩` from `core X g (X.rkF g) (F.en g) (F.en_inj g) (F.en_ty g) e N`. Conclude with `⟨⟨S, t, ht, gr, hgr, h1⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩`.
-/
theorem monSupply : MONSupply ∧ RF.MONSupply := by
  constructor
  · intro C _ V d _ I J _ _ X F g e N
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ :=
      core X g (X.rk g) (F.en g) (F.en_inj g) (F.en_ty g) e N
    exact ⟨⟨S, t, ht, gr, hgr, h1⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩
  · intro C _ V d _ I J _ _ X F g e N
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ :=
      core X g (X.rkF g) (F.en g) (F.en_inj g) (F.en_ty g) e N
    exact ⟨⟨S, t, ht, gr, hgr, h1⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩

end GlobalTheory.MonBlock
