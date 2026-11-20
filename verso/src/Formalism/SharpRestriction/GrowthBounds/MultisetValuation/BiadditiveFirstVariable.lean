import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntegralExpParamOfEquivZero

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF Gser IsLawOfLog cob at1 in3 d1 swap2 DivAB BetaHyp)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf sx_charZero

variable (p : ℕ) [hp : Fact p.Prime]

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ (K0 p))` using `PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`. Take `⟨g, hg⟩` from `PowerSeries.X_dvd_iff.2 (sx_logF_const p)`. Unfold `sx_lX`. Rewrite using `[hg, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, map_mul, MvPowerSeries.constantCoeff_X, zero_mul]`.
-/
theorem sx_lX_const {σ : Type} (i : σ) : MvPowerSeries.constantCoeff (sx_lX p i) = 0 := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (sx_logF_const p)
  unfold sx_lX
  rw [hg, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, map_mul, MvPowerSeries.constantCoeff_X, zero_mul]

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ (K0 p))` using `PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`. Take `⟨g, hg⟩` from `PowerSeries.X_dvd_iff.2 (sx_logF_const p)`. Use `⟨PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) g, ?_⟩` and prove the remaining obligations. Unfold `sx_lX`. Rewrite using `[hg, PowerSeries.subst_mul hs, PowerSeries.subst_X hs]`.
-/
theorem sx_X_dvd_lX {σ : Type} (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) ∣ sx_lX p i := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (sx_logF_const p)
  refine ⟨PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) g, ?_⟩
  unfold sx_lX
  rw [hg, PowerSeries.subst_mul hs, PowerSeries.subst_X hs]

/- English proof (translation)
Introduce `n hn`. Establish `hdvd : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p)) ∣ inParam p be`. Introduce `i`. Establish `hb : (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p)) ∣ be`. Rewrite using `[MvPowerSeries.X_dvd_iff]`.

Introduce `m hm`. Assume the negation of the conclusion as `hne`. Use `h.ab m hne` as an intermediate fact. Use `fin_cases i`. Simplify using `only [Fin.zero_eta, Fin.isValue] at hm`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Fin.mk_one, Fin.isValue] at hm`. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg⟩` from `hb`. Rewrite using `[hg, sx_inParam_mul, sx_inParam_X]`.

Conclude with `Dvd.dvd.mul_right (sx_X_dvd_lX p i) _`. Break down `hn with h0 | h1` into its components or cases. Conclude with `MvPowerSeries.X_dvd_iff.1 (hdvd 0) n h0`. Conclude with `MvPowerSeries.X_dvd_iff.1 (hdvd 1) n h1`.
-/
theorem sx_divAB {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeProp p be) : DivAB (inParam p be) := by
  intro n hn
  have hdvd : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p)) ∣ inParam p be := by
    intro i
    have hb : (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p)) ∣ be := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      by_contra hne
      have := h.ab m hne
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue] at hm
        omega
      · simp only [Fin.mk_one, Fin.isValue] at hm
        omega
    obtain ⟨g, hg⟩ := hb
    rw [hg, sx_inParam_mul, sx_inParam_X]
    exact Dvd.dvd.mul_right (sx_X_dvd_lX p i) _
  rcases hn with h0 | h1
  · exact MvPowerSeries.X_dvd_iff.1 (hdvd 0) n h0
  · exact MvPowerSeries.X_dvd_iff.1 (hdvd 1) n h1

variable {p}

/- English proof (translation)
Introduce `i`. Use `fin_cases i`. Conclude with `h0`. Conclude with `h1`.
-/
theorem sx_two {τ : Type} {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1

/- English proof (translation)
Establish `hs : MvPowerSeries.HasSubst ![u, v]` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨hu, hv⟩)`. Establish `hc : PowerSeries.subst F (lgF (K0 p) p) = at1 0 (lgF (K0 p) p) + at1 1 (lgF (K0 p) p)`. Establish `h0` using `hF.2.2`. Unfold `cob at h0`. Take the linear combination `h0`.

Establish `e` using `congrArg (MvPowerSeries.subst ![u, v]) hc`. Rewrite `e` using `[sx_subst_ps p hs hF.1, MvPowerSeries.subst_add hs, at1, at1, sx_subst_ps p hs (MvPowerSeries.constantCoeff_X 0), sx_subst_ps p hs (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]`. Rewrite using `[sx_logF_eq]`. Simplify using `using e`.
-/
theorem sx_log_law {F : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) {τ : Type} (u v : MvPowerSeries τ (K0 p))
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![u, v] F) (logF p) =
      PowerSeries.subst u (logF p) + PowerSeries.subst v (logF p) := by
  have hs : MvPowerSeries.HasSubst ![u, v] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨hu, hv⟩)
  have hc : PowerSeries.subst F (lgF (K0 p) p) = at1 0 (lgF (K0 p) p) + at1 1 (lgF (K0 p) p) := by
    have h0 := hF.2.2
    unfold cob at h0
    linear_combination h0
  have e := congrArg (MvPowerSeries.subst ![u, v]) hc
  rw [sx_subst_ps p hs hF.1, MvPowerSeries.subst_add hs, at1, at1,
    sx_subst_ps p hs (MvPowerSeries.constantCoeff_X 0), sx_subst_ps p hs (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs] at e
  rw [sx_logF_eq]
  simpa using e

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨hu, hv⟩)) (Fin.forall_fin_two.2 ⟨hu, hv⟩) hF.1`.
-/
theorem sx_law_const {F : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) {τ : Type} (u v : MvPowerSeries τ (K0 p))
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![u, v] F) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨hu, hv⟩))
    (Fin.forall_fin_two.2 ⟨hu, hv⟩) hF.1

/- English proof (translation)
Use `show inParam p (MvPowerSeries.subst ![x, y] be) = _`. Apply `sx_inParam_subst` to reduce the goal to its premises. Introduce `i fin_cases i`. Simplify using `using hx`. Simplify using `using hy`.

Introduce `i fin_cases i`. Simplify using `using hx'`. Simplify using `using hy'`. Introduce `i fin_cases i`. Simplify using `using ex`.

Simplify using `using ey`.
-/
theorem param_substitution_pair {τ : Type} [Finite τ] (be : MvPowerSeries (Fin 2) (K0 p)) (x y x' y' : MvPowerSeries τ (K0 p))
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (hx' : MvPowerSeries.constantCoeff x' = 0) (hy' : MvPowerSeries.constantCoeff y' = 0)
    (ex : PowerSeries.subst x' (logF p) = inParam p x) (ey : PowerSeries.subst y' (logF p) = inParam p y) :
    inParam p (sub2 p be x y) = MvPowerSeries.subst ![x', y'] (inParam p be) := by
  show inParam p (MvPowerSeries.subst ![x, y] be) = _
  apply sx_inParam_subst
  · intro i
    fin_cases i
    · simpa using hx
    · simpa using hy
  · intro i
    fin_cases i
    · simpa using hx'
    · simpa using hy'
  · intro i
    fin_cases i
    · simpa using ex
    · simpa using ey

/- English proof (translation)
Rewrite using `[sx_inParam_X]`. Both sides reduce to the same expression.
-/
theorem sx_eX {τ : Type} [Finite τ] (i : τ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries τ (K0 p)) (logF p) = inParam p (MvPowerSeries.X i) := by
  rw [sx_inParam_X]
  rfl

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_X i`.
-/
theorem sx_cX {τ : Type} (i : τ) : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries τ (K0 p)) = 0 :=
  MvPowerSeries.constantCoeff_X i

/- English proof (translation)
Establish `hX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) (K0 p)) = 0` using `fun i => MvPowerSeries.constantCoeff_X i`. Establish `hin3 : MvPowerSeries.constantCoeff (in3 F) = 0` using `sx_law_const hF _ _ (hX 0) (hX 1)`. Establish `h01 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) (K0 p)) = 0`. Rewrite using `[map_add, hX 0, hX 1, add_zero]`. Establish `ex : PowerSeries.subst (in3 F) (logF p) = inParam p (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) (K0 p))`.

Rewrite using `[in3, sx_log_law hF _ _ (hX 0) (hX 1), sx_inParam_add, ← sx_eX, ← sx_eX]`. Establish `e1` using `param_substitution_pair be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) (in3 F) (MvPowerSeries.X 2) h01 (hX 2) hin3 (hX 2) ex (sx_eX 2)`. Establish `e2` using `param_substitution_pair be (MvPowerSeries.X 0) (MvPowerSeries.X 2) (MvPowerSeries.X 0) (MvPowerSeries.X 2) (hX 0) (hX 2) (hX 0) (hX 2) (sx_eX 0) (sx_eX 2)`. Establish `e3` using `param_substitution_pair be (MvPowerSeries.X 1) (MvPowerSeries.X 2) (MvPowerSeries.X 1) (MvPowerSeries.X 2) (hX 1) (hX 2) (hX 1) (hX 2) (sx_eX 1) (sx_eX 2)`. Establish `key : d1 F (inParam p be) = inParam p (sub2 p be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) - sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 2) - sub2 p be (MvPowerSeries.X 1) (MvPowerSeries.X 2))`.

Rewrite using `[th_inParam_sub, th_inParam_sub, e1, e2, e3]`. Both sides reduce to the same expression. Rewrite using `[key]`. Use `first`. Consider the case `exact equiv_zero_of_integralExp p (integralExp_param_of_equiv_zero p h.add1)`.

Consider the case `exact equiv_zero_of_integralExp (integralExp_param_of_equiv_zero p h.add1)`.
-/
theorem biadditive_first_variable {F be : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) (h : BeProp p be) :
    Formalism.InvariantFactorPaths.G7.Simeq (d1 F (inParam p be)) 0 := by
  have hX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) (K0 p)) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hin3 : MvPowerSeries.constantCoeff (in3 F) = 0 := sx_law_const hF _ _ (hX 0) (hX 1)
  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) (K0 p)) = 0 := by
    rw [map_add, hX 0, hX 1, add_zero]
  have ex : PowerSeries.subst (in3 F) (logF p) =
      inParam p (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) (K0 p)) := by
    rw [in3, sx_log_law hF _ _ (hX 0) (hX 1), sx_inParam_add, ← sx_eX, ← sx_eX]
  have e1 := param_substitution_pair be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) (in3 F) (MvPowerSeries.X 2)
    h01 (hX 2) hin3 (hX 2) ex (sx_eX 2)
  have e2 := param_substitution_pair be (MvPowerSeries.X 0) (MvPowerSeries.X 2) (MvPowerSeries.X 0) (MvPowerSeries.X 2)
    (hX 0) (hX 2) (hX 0) (hX 2) (sx_eX 0) (sx_eX 2)
  have e3 := param_substitution_pair be (MvPowerSeries.X 1) (MvPowerSeries.X 2) (MvPowerSeries.X 1) (MvPowerSeries.X 2)
    (hX 1) (hX 2) (hX 1) (hX 2) (sx_eX 1) (sx_eX 2)
  have key : d1 F (inParam p be) = inParam p
      (sub2 p be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) -
        sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 2) -
        sub2 p be (MvPowerSeries.X 1) (MvPowerSeries.X 2)) := by
    rw [th_inParam_sub, th_inParam_sub, e1, e2, e3]
    rfl
  rw [key]
  first
    | exact equiv_zero_of_integralExp p (integralExp_param_of_equiv_zero p h.add1)
    | exact equiv_zero_of_integralExp (integralExp_param_of_equiv_zero p h.add1)

end Formalism.MainNotions.FormalGroupSystem.Pf
