import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrCombAny

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

/- English proof (translation)
Use extensionality with `i j`. Conclude with `GlobalTheory.ThetaClosed.finPart_eInf_smul (x i j)`.
-/
theorem real_part {S T : HSp D} (x : WO S T) : (GlobalTheory.FinTranslate.eInf D • x : WO S T).map (finPart D) = 0 := by
  ext i j; exact GlobalTheory.ThetaClosed.finPart_eInf_smul (x i j)

/- English proof (translation)
Use extensionality with `i j`. Conclude with `GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (x i j)`.
-/
theorem fin_part {S T : HSp D} (x : WO S T) : ((1 - GlobalTheory.FinTranslate.eInf D) • x : WO S T).map (infPart D) = 0 := by
  ext i j; exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (x i j)

/- English proof (translation)
Establish `hx : x = GlobalTheory.FinTranslate.eInf D • x + (1 - GlobalTheory.FinTranslate.eInf D) • x`. Rewrite using `[← add_smul, add_sub_cancel, one_smul]`. Use `conv_lhs => rw [hx]`. Rewrite using `[GlobalTheory.FinTranslate.symplOH_add_right, GlobalTheory.FinTranslate.symplOH_fin_real hw (real_part x), zero_add]`.
-/
theorem psi_fin_eq {S T : HSp D} {w : WO S T} (hw : w.map (infPart D) = 0) (x : WO S T) :
    ψ (symplOH S T w x) = ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) := by
  have hx : x = GlobalTheory.FinTranslate.eInf D • x + (1 - GlobalTheory.FinTranslate.eInf D) • x := by
    rw [← add_smul, add_sub_cancel, one_smul]
  conv_lhs => rw [hx]
  rw [GlobalTheory.FinTranslate.symplOH_add_right, GlobalTheory.FinTranslate.symplOH_fin_real hw (real_part x), zero_add]

/- English proof (translation)
Set `U : AddSubgroup (WO S T)` to `{ carrier := {w | ∀ x ∈ s, ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1} zero_mem' := fun x _ => by rw [GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one] add_mem' := fun {a b} ha hb x hx => by`. Rewrite using `[GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]`. Use the proof step `neg_mem' := fun {a} ha x hx => by`. Use `AddChar.map_add_eq_mul ψ (symplOH S T a ((1 - GlobalTheory.FinTranslate.eInf D) • x)) (symplOH S T (-a) ((1 - GlobalTheory.FinTranslate.eInf D) • x))` as an intermediate fact. Rewrite `this` using `[← GlobalTheory.FinTranslate.symplOH_add_left, add_neg_cancel, GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one, ha x hx, one_mul]`.

Conclude with `this.symm }`. Use `⟨U, ?_, fun w hw hw' x hx => (psi_fin_eq hw' x).trans (hw x hx)⟩` and prove the remaining obligations. Establish `e : (U : Set (WO S T)) = ⋂ x ∈ s, {w | ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1}`. Use extensionality with `w`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `isOpen_biInter_finset fun x _ => GlobalTheory.FrComb.isOpen_ker hψ (fin_part x)`.
-/
theorem exists_orth_any {S T : HSp D} (hψ : IsStdChar D ψ (-1)) (s : Finset (WO S T)) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ w ∈ U, w.map (infPart D) = 0 → ∀ x ∈ s, ψ (symplOH S T w x) = 1 := by
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∀ x ∈ s, ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1}
      zero_mem' := fun x _ => by rw [GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb x hx => by
        rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, ha x hx, hb x hx, one_mul]
      neg_mem' := fun {a} ha x hx => by
        have := AddChar.map_add_eq_mul ψ (symplOH S T a ((1 - GlobalTheory.FinTranslate.eInf D) • x))
          (symplOH S T (-a) ((1 - GlobalTheory.FinTranslate.eInf D) • x))
        rw [← GlobalTheory.FinTranslate.symplOH_add_left, add_neg_cancel, GlobalTheory.FinTranslate.symplOH_zero_left, ψ.map_zero_eq_one,
          ha x hx, one_mul] at this
        exact this.symm }
  refine ⟨U, ?_, fun w hw hw' x hx => (psi_fin_eq hw' x).trans (hw x hx)⟩
  have e : (U : Set (WO S T)) = ⋂ x ∈ s, {w | ψ (symplOH S T w ((1 - GlobalTheory.FinTranslate.eInf D) • x)) = 1} := by
    ext w
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  exact isOpen_biInter_finset fun x _ => GlobalTheory.FrComb.isOpen_ker hψ (fin_part x)

/- English proof (translation)
Take `⟨lam, hl, hlam⟩` from `GlobalTheory.WeilVacMove.exists_log hψ`. Set `φ : (Fin n → ℝ) →+ ℂ` to `{ toFun := fun t => lam (symplOH S T (L t) x) map_zero' := by rw [map_zero L, GlobalTheory.FinTranslate.symplOH_zero_left, map_zero] map_add' := fun a b => by rw [map_add L, GlobalTheory.FinTranslate.symplOH_add_left, map_add] }`. Establish `hφ` using `GlobalTheory.WeilVacMove.contDiff_additive φ (hl.comp ((GlobalTheory.FinTranslate.continuous_symplOH S T x).comp hL))`. Establish `e : (fun t => ψ (symplOH S T (L t) x)) = fun t => Complex.exp (φ t)`. Use function extensionality and compare the values at `fun t => hlam _ (GlobalTheory.WeilVacMove.snd_symplOH S T (L t) x (Or.inl (hLf t)))`.

Rewrite using `[e]`. Conclude with `hφ.cexp`.
-/
theorem contDiff_psi {S T : HSp D} (hψ : IsStdChar D ψ (-1)) {n : ℕ} {L : (Fin n → ℝ) →+ WO S T} (hL : Continuous L)
    (hLf : ∀ t, (L t).map (finPart D) = 0) (x : WO S T) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => ψ (symplOH S T (L t) x) := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  let φ : (Fin n → ℝ) →+ ℂ :=
    { toFun := fun t => lam (symplOH S T (L t) x)
      map_zero' := by rw [map_zero L, GlobalTheory.FinTranslate.symplOH_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L, GlobalTheory.FinTranslate.symplOH_add_left, map_add] }
  have hφ := GlobalTheory.WeilVacMove.contDiff_additive φ (hl.comp ((GlobalTheory.FinTranslate.continuous_symplOH S T x).comp hL))
  have e : (fun t => ψ (symplOH S T (L t) x)) = fun t => Complex.exp (φ t) :=
    funext fun t => hlam _ (GlobalTheory.WeilVacMove.snd_symplOH S T (L t) x (Or.inl (hLf t)))
  rw [e]
  exact hφ.cexp

/- English proof (translation)
Establish `e : (fun u v => comb ψ A S c (fun u' => K u' v) u) = fun u v => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * K (u + x) v)`. Use function extensionality and compare the values at `u v`. Conclude with `GlobalTheory.FrComb.comb_apply c _ u`. Use `⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [GlobalTheory.FrComb.comb_apply]`.

Conclude with `continuous_finset_sum _ fun x _ => continuous_const.mul ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH A S x).comp continuous_fst)).mul (hK.cont.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)))`. Introduce `n L L' hL hL' hLf hL'f u v`. Rewrite using `[e]`. Establish `e2 : (fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S (u + L t) x) * K (u + L t + x) (v + L' t))) = fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * (ψ (symplOH A S (L t) x) * K (u + x + L t) (v + L' t)))`. Use function extensionality and compare the values at `t`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]`. Simplify using `only []`. Rewrite using `[e2]`. Conclude with `ContDiff.sum fun x _ => contDiff_const.mul (contDiff_const.mul ((contDiff_psi hψ hL hLf x).mul (hK.smooth n L L' hL hL' hLf hL'f (u + x) v)))`.

Simplify using `only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[add_assoc, hK.quasiL, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]`. Establish `key : ψ (symplOH A S (ratW S A γ) x + symplOH A S u x) * ψ (-(symplOH A S (ratW S A γ) u + symplOH A S (ratW S A γ) x)) = ψ (-(symplOH A S (ratW S A γ) u)) * ψ (symplOH A S u x)`. Rewrite using `[← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(c x * K (u + x) v) * key`. Simplify using `only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[hK.quasiR]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨U, hU, hUf⟩` from `hK.levL`. Take `⟨V, hV, hVf⟩` from `exists_orth_any hψ c.support`. Use `⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' v)`. Take `⟨U, hU, hUf⟩` from `hK.levR`. Use `⟨U, hU, fun a ha ha' u => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Simplify using `only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Establish `e3` using `congrFun (hUf a ha ha' (u + x)) v`. Simplify using `only [heisO] at e3`. Rewrite using `[← e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem biTheta_combL {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) (c : WO A S →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ A S c (fun u' => K u' v) u) := by
  have e : (fun u v => comb ψ A S c (fun u' => K u' v) u) =
      fun u v => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * K (u + x) v) := by
    funext u v; exact GlobalTheory.FrComb.comb_apply c _ u
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply]
    exact continuous_finset_sum _ fun x _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH A S x).comp continuous_fst)).mul
        (hK.cont.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S (u + L t) x) * K (u + L t + x) (v + L' t))) =
        fun t => ∑ x ∈ c.support, c x * (ψ (symplOH A S u x) * (ψ (symplOH A S (L t) x) * K (u + x + L t) (v + L' t))) := by
      funext t
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_const.mul
      ((contDiff_psi hψ hL hLf x).mul (hK.smooth n L L' hL hL' hLf hL'f (u + x) v)))
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc, hK.quasiL, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH A S (ratW S A γ) x + symplOH A S u x) * ψ (-(symplOH A S (ratW S A γ) u + symplOH A S (ratW S A γ) x)) =
        ψ (-(symplOH A S (ratW S A γ) u)) * ψ (symplOH A S u x) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c x * K (u + x) v) * key
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hK.quasiR]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    obtain ⟨V, hV, hVf⟩ := exists_orth_any hψ c.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' v)
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    refine ⟨U, hU, fun a ha ha' u => ?_⟩
    funext v
    simp only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e3 := congrFun (hUf a ha ha' (u + x)) v
    simp only [heisO] at e3
    rw [← e3]
    ring

/- English proof (translation)
Establish `e : (fun u v => comb ψ S A' c (K u) v) = fun u v => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * K u (v + y))`. Use function extensionality and compare the values at `u v`. Conclude with `GlobalTheory.FrComb.comb_apply c _ v`. Use `⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [GlobalTheory.FrComb.comb_apply]`.

Conclude with `continuous_finset_sum _ fun y _ => continuous_const.mul ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH S A' y).comp continuous_snd)).mul (hK.cont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))))`. Introduce `n L L' hL hL' hLf hL'f u v`. Rewrite using `[e]`. Establish `e2 : (fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' (v + L' t) y) * K (u + L t) (v + L' t + y))) = fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * (ψ (symplOH S A' (L' t) y) * K (u + L t) (v + y + L' t)))`. Use function extensionality and compare the values at `t`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm v, mul_assoc]`. Simplify using `only []`. Rewrite using `[e2]`. Conclude with `ContDiff.sum fun y _ => contDiff_const.mul (contDiff_const.mul ((contDiff_psi hψ hL' hL'f y).mul (hK.smooth n L L' hL hL' hLf hL'f u (v + y))))`.

Simplify using `only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[hK.quasiL]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[add_assoc, hK.quasiR, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]`. Establish `key : ψ (symplOH S A' (ratW A' S γ) y + symplOH S A' v y) * ψ (-(symplOH S A' (ratW A' S γ) v + symplOH S A' (ratW A' S γ) y)) = ψ (-(symplOH S A' (ratW A' S γ) v)) * ψ (symplOH S A' v y)`. Rewrite using `[← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(c y * K u (v + y)) * key`. Take `⟨U, hU, hUf⟩` from `hK.levL`. Use `⟨U, hU, fun a ha ha' v => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `u`.

Simplify using `only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Establish `e3` using `congrFun (hUf a ha ha' (v + y)) u`. Simplify using `only [heisO] at e3`. Rewrite using `[← e3]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨U, hU, hUf⟩` from `hK.levR`. Take `⟨V, hV, hVf⟩` from `exists_orth_any hψ c.support`. Use `⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' u)`.
-/
theorem biTheta_combR {A S A' : HSp D} (hψ : IsStdChar D ψ (-1)) {K : WO A S → WO S A' → ℂ}
    (hK : IsBiTheta ψ A S A' K) (c : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ S A' c (K u) v) := by
  have e : (fun u v => comb ψ S A' c (K u) v) =
      fun u v => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * K u (v + y)) := by
    funext u v; exact GlobalTheory.FrComb.comb_apply c _ v
  refine ⟨?_, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply]
    exact continuous_finset_sum _ fun y _ => continuous_const.mul
      ((hψ.1.1.comp ((GlobalTheory.FinTranslate.continuous_symplOH S A' y).comp continuous_snd)).mul
        (hK.cont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))))
  · intro n L L' hL hL' hLf hL'f u v
    rw [e]
    have e2 : (fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' (v + L' t) y) * K (u + L t) (v + L' t + y))) =
        fun t => ∑ y ∈ c.support, c y * (ψ (symplOH S A' v y) * (ψ (symplOH S A' (L' t) y) * K (u + L t) (v + y + L' t))) := by
      funext t
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm v, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun y _ => contDiff_const.mul (contDiff_const.mul
      ((contDiff_psi hψ hL' hL'f y).mul (hK.smooth n L L' hL hL' hLf hL'f u (v + y))))
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hK.quasiL]
    ring
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [add_assoc, hK.quasiR, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH S A' (ratW A' S γ) y + symplOH S A' v y) * ψ (-(symplOH S A' (ratW A' S γ) v + symplOH S A' (ratW A' S γ) y)) =
        ψ (-(symplOH S A' (ratW A' S γ) v)) * ψ (symplOH S A' v y) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (c y * K u (v + y)) * key
  · obtain ⟨U, hU, hUf⟩ := hK.levL
    refine ⟨U, hU, fun a ha ha' v => ?_⟩
    funext u
    simp only [heisO, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e3 := congrFun (hUf a ha ha' (v + y)) u
    simp only [heisO] at e3
    rw [← e3]
    ring
  · obtain ⟨U, hU, hUf⟩ := hK.levR
    obtain ⟨V, hV, hVf⟩ := exists_orth_any hψ c.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha' u)

/- English proof (translation)
Introduce `D ψ hψ A S A' C hC c c'`. Conclude with `biTheta_combL hψ (biTheta_combR hψ hC c') c`.
-/
theorem biTheta_biComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (C : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' C → ∀ (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ), IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) := by
  intro D ψ hψ A S A' C hC c c'
  exact biTheta_combL hψ (biTheta_combR hψ hC c') c

end GlobalTheory.FrCombAny

end
