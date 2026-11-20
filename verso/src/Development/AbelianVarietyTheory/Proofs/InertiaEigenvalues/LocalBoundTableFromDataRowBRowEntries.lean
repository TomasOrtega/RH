import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowBSize

open Classical

/- English proof (translation)
Unfold `Formalism.MainNotions.N.ratIn`. Rewrite using `[dif_pos h]`. Conclude with `(exists_rat_btwn h).choose_spec.2`.
-/
theorem ratIn_lt {x y : ℝ} (h : x < y) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) < y := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dif_pos h]
  exact (exists_rat_btwn h).choose_spec.2

/- English proof (translation)
Unfold `Formalism.MainNotions.N.ratIn`. Rewrite using `[dif_neg h]`.
-/
theorem ratIn_of_not_lt {x y : ℝ} (h : ¬ x < y) : Formalism.MainNotions.N.ratIn x y = 0 := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dif_neg h]

/- English proof (translation)
Combine the linear relations using `[L.sc.one_lt_alt]`.
-/
theorem x_pos' {D : D7} (L : SizeData₂ D) : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]

/- English proof (translation)
Unfold `Scale.b`. Apply `Real.one_le_exp` to reduce the goal to its premises. Unfold `Scale.L`. Conclude with `Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _`.
-/
theorem one_le_b' {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

/- English proof (translation)
Unfold `Formalism.MainNotions.TwistedPlaces.large₂ Scale.L`. Conclude with `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`.
-/
theorem one_le_Lg {D : D7} (L : SizeData₂ D) : 1 ≤ Formalism.MainNotions.TwistedPlaces.large₂ L := by
  unfold Formalism.MainNotions.TwistedPlaces.large₂ Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

/- English proof (translation)
Unfold `Formalism.MainNotions.TwistedPlaces.hB`. Use `one_le_b' L` as an intermediate fact. Use `L.Sc_pos` as an intermediate fact. Use `L.etaSz_pos` as an intermediate fact. Establish `: (0 : ℝ) ≤ D.R.t` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L := by
  unfold Formalism.MainNotions.TwistedPlaces.hB
  have := one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

/- English proof (translation)
Establish `hb : 0 < L.sc.b'`. Unfold `Scale.b' Scale.a Scale.X'`. Use `x_pos' L` as an intermediate fact. Use `one_le_b' L` as an intermediate fact. Check the signs of the components of the expression.

Establish `h1 : 0 ≤ L.sc.w'' D.R.n`. Unfold `Scale.w''`. Use `x_pos' L` as an intermediate fact. Check the signs of the components of the expression. Unfold `Formalism.MainNotions.TwistedPlaces.GP Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.eta₃ Formalism.MainNotions.TwistedPlaces.wB`.

Establish `h2` using `L.etaSz_pos`. Establish `h3` using `L.Sc_pos`. Establish `h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz) ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz)` using `le_max_left _ _`. Establish `h5 : (0:ℝ) ≤ D.R.t` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem GP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.GP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := x_pos' L
    have := one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := x_pos' L
    positivity
  unfold Formalism.MainNotions.TwistedPlaces.GP Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.eta₃ Formalism.MainNotions.TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h3 := L.Sc_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

/- English proof (translation)
Unfold `Formalism.MainNotions.N.coreB`. Establish `hr : (0:ℝ) < D.R.r`. Establish `: 0 < D.R.r` using `by unfold Ranks.r; have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hl1 : (0:ℝ) < (l : ℝ) - 1`.

Establish `: (2:ℝ) ≤ l` using `by exact_mod_cast hl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hh : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1)`. Conclude with `div_nonneg (hB_nonneg L) (pow_nonneg hl1.le _)`. Establish `hg : 0 ≤ (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1)`.

Use `GP_nonneg L` as an intermediate fact. Check the signs of the components of the expression. Establish `hL` using `one_le_Lg L`. Establish `hin : 0 < Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) + (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L` using `by linarith`. Establish `hn : (0:ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1` using `by positivity`.

Check the signs of the components of the expression.
-/
theorem coreB_pos {D : D7} (L : SizeData₂ D) {l : ℕ} (hl : 2 ≤ l) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 < Formalism.MainNotions.N.coreB L l lam := by
  unfold Formalism.MainNotions.N.coreB
  have hr : (0:ℝ) < D.R.r := by
    have : 0 < D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hl1 : (0:ℝ) < (l : ℝ) - 1 := by
    have : (2:ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hh : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) := by
    exact div_nonneg (hB_nonneg L) (pow_nonneg hl1.le _)
  have hg : 0 ≤ (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) := by
    have := GP_nonneg L; positivity
  have hL := one_le_Lg L
  have hin : 0 < Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) +
      (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L := by linarith
  have hn : (0:ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1 := by positivity
  positivity

/- English proof (translation)
Establish `hc` using `coreB_pos L hl lam`. Unfold `Formalism.MainNotions.N.lenRowB`. Establish `hlt : 3 * C₂ * Formalism.MainNotions.N.coreB L l lam < (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam` using `by nlinarith`. Use `ratIn_lt hlt` as an intermediate fact. Establish `: (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam ≤ C * Formalism.MainNotions.N.coreB L l lam` using `mul_le_mul_of_nonneg_right hC hc.le`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lenRowB_le {D : D7} (L : SizeData₂ D) {C₂ C : ℝ} (hC : 3 * C₂ + 1 ≤ C) {l : ℕ} (hl : 2 ≤ l)
    (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    ((Formalism.MainNotions.N.lenRowB L C₂ l lam : ℚ) : ℝ) ≤ C * Formalism.MainNotions.N.coreB L l lam := by
  have hc := coreB_pos L hl lam
  unfold Formalism.MainNotions.N.lenRowB
  have hlt : 3 * C₂ * Formalism.MainNotions.N.coreB L l lam < (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam := by nlinarith
  have := ratIn_lt hlt
  have : (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam ≤ C * Formalism.MainNotions.N.coreB L l lam :=
    mul_le_mul_of_nonneg_right hC hc.le
  linarith

end GlobalTheory.NLink.RowBSize

/- English proof (translation)
Introduce `D L P HW X R C hD hR`. Introduce `i _ hrow lam _`. Take `⟨hI, hA, hO, _⟩` from `hrow`. Establish `hl2 : 2 ≤ D.nd.l i` using `(D.nd.lPrime i).out.two_le`. Establish `hC1 : (1:ℝ) ≤ C` using `hR.2.2.2.2.1`.

Establish `hC3 : 3 * R.C₂ + 1 ≤ C` using `hR.2.2.2.2.2.1`. Establish `hrowB` using `hD.rowB i hI ⟨hA, hO⟩`. Establish `key : (tabX L X).len i lam = KillingConditions.supZ i (fun _ => ((Formalism.MainNotions.N.lenRowB L R.C₂ (D.nd.l i) lam : ℚ) : ℝ))` using `by show KillingConditions.lenR X.len0 i lam = _`. Unfold `KillingConditions.lenR`. Use `congr 1`.

Use function extensionality and compare the values at `π`. Rewrite using `[hD.len0I i hI π lam, hrowB]`. Establish `hcore : C * ((TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) + (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + TwistedPlaces.large₂ L) = C * Formalism.MainNotions.N.coreB L (D.nd …`. Unfold `Formalism.MainNotions.N.coreB`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key, hcore]`. Unfold `KillingConditions.supZ`. Use `split_ifs with hne`. Rewrite using `[Finset.sup'_const]`. Conclude with `GlobalTheory.NLink.RowBSize.lenRowB_le L hC3 hl2 lam`.

Use `GlobalTheory.NLink.RowBSize.coreB_pos L hl2 lam` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem GlobalTheory.NLink.localBoundTableFromData_rowB_rowEntries : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admB L (tabX L X) C := by
  intro D L P HW X R C hD hR
  intro i _ hrow lam _
  obtain ⟨hI, hA, hO, _⟩ := hrow
  have hl2 : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
  have hC1 : (1:ℝ) ≤ C := hR.2.2.2.2.1
  have hC3 : 3 * R.C₂ + 1 ≤ C := hR.2.2.2.2.2.1
  have hrowB := hD.rowB i hI ⟨hA, hO⟩
  have key : (tabX L X).len i lam = KillingConditions.supZ i (fun _ => ((Formalism.MainNotions.N.lenRowB L R.C₂ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hrowB]
  have hcore : C * ((TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) +
      (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + TwistedPlaces.large₂ L) = C * Formalism.MainNotions.N.coreB L (D.nd.l i) lam := by
    unfold Formalism.MainNotions.N.coreB; ring
  rw [key, hcore]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    exact GlobalTheory.NLink.RowBSize.lenRowB_le L hC3 hl2 lam
  · have := GlobalTheory.NLink.RowBSize.coreB_pos L hl2 lam
    positivity
