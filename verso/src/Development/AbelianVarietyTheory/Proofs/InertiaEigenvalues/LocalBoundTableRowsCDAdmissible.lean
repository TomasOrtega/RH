import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableFromDataRowBRowEntries
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowCDSize

open Classical

/- English proof (translation)
Distinguish the cases in `h : x < y`. Conclude with `(RowBSize.ratIn_lt h).le.trans hy`. Rewrite using `[RowBSize.ratIn_of_not_lt h]`. Simplify using `using hc`.
-/
theorem ratIn_le {x y c : ℝ} (hy : y ≤ c) (hc : 0 ≤ c) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) ≤ c := by
  by_cases h : x < y
  · exact (RowBSize.ratIn_lt h).le.trans hy
  · rw [RowBSize.ratIn_of_not_lt h]; simpa using hc

/- English proof (translation)
Unfold `TwistedPlaces.hB`. Use `RowBSize.one_le_b' L` as an intermediate fact. Use `L.Sc_pos` as an intermediate fact. Use `L.etaSz_pos` as an intermediate fact. Establish `: (0 : ℝ) ≤ D.R.t` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_hB {D : D7} (L : SizeData₂ D) : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := RowBSize.one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

/- English proof (translation)
Unfold `TwistedPlaces.eta₃`. Use `L.etaSz_pos` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem etaP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.eta₃ L := by
  unfold TwistedPlaces.eta₃
  have := L.etaSz_pos
  positivity

/- English proof (translation)
Establish `hb : 0 < L.sc.b'`. Unfold `Scale.b' Scale.a Scale.X'`. Use `RowBSize.x_pos' L` as an intermediate fact. Use `RowBSize.one_le_b' L` as an intermediate fact. Check the signs of the components of the expression.

Establish `h1 : 0 ≤ L.sc.w'' D.R.n`. Unfold `Scale.w''`. Use `RowBSize.x_pos' L` as an intermediate fact. Check the signs of the components of the expression. Unfold `TwistedPlaces.wP TwistedPlaces.wB`.

Establish `h2` using `L.etaSz_pos`. Establish `h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz) ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz)` using `le_max_left _ _`. Establish `h5 : (0:ℝ) ≤ D.R.t` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem placeWeight_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.wP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := RowBSize.x_pos' L
    have := RowBSize.one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := RowBSize.x_pos' L
    positivity
  unfold TwistedPlaces.wP TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

/- English proof (translation)
Unfold `coreE`. Establish `h1 : 0 ≤ TwistedPlaces.hB L / l` using `div_nonneg (by linarith [one_le_hB L]) (by positivity)`. Establish `h2 : 0 ≤ Real.logb l (TwistedPlaces.hB L)`. Unfold `Real.logb`. Conclude with `div_nonneg (Real.log_nonneg (one_le_hB L)) (Real.log_natCast_nonneg l)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coreE_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) : 0 ≤ coreE L l := by
  unfold coreE
  have h1 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith [one_le_hB L]) (by positivity)
  have h2 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg (one_le_hB L)) (Real.log_natCast_nonneg l)
  linarith

/- English proof (translation)
Unfold `flat`. Use `placeWeight_nonneg L` as an intermediate fact. Use `etaP_nonneg L` as an intermediate fact. Use `L.Sc_pos` as an intermediate fact. Use `RowBSize.one_le_Lg L` as an intermediate fact.

Establish `h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l` using `by positivity`. Apply the tactic sequence `have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if bd then (1:ℝ) else 0) := by split_ifs <;> simp [*]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem flat_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 ≤ flat L bd l := by
  unfold flat
  have := placeWeight_nonneg L
  have := etaP_nonneg L
  have := L.Sc_pos
  have := RowBSize.one_le_Lg L
  have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := by positivity
  have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if bd then (1:ℝ) else 0) := by split_ifs <;> simp [*]
  linarith

/- English proof (translation)
Unfold `coreH`. Use `RowBSize.hB_nonneg L` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem coreH_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreH L l lam := by
  unfold coreH
  have := RowBSize.hB_nonneg L
  positivity

/- English proof (translation)
Unfold `coreF`. Use `flat_nonneg L bd l` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem coreF_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreF L bd l lam := by
  unfold coreF
  have := flat_nonneg L bd l
  positivity

/- English proof (translation)
Unfold `coreM`. Use `coreE_nonneg L l` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem coreM_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreM L l lam := by
  unfold coreM
  have := coreE_nonneg L l
  positivity

/- English proof (translation)
Take `⟨-, -, -, -, hC1, -, h1, h2, h3, -⟩` from `hR`. Establish `hH` using `coreH_nonneg L (D.nd.l i) lam`. Establish `hF` using `coreF_nonneg L (X.band i lam) (D.nd.l i) lam`. Establish `hM` using `coreM_nonneg L (D.nd.l i) lam`. Establish `hC0 : (0:ℝ) ≤ C` using `by linarith`.

Establish `h0 : 0 ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam + C * C * coreM L (D.nd.l i) lam` using `by positivity`. Establish `key : (tabX L X).len i lam = KillingConditions.supZ i (fun _ => ((lenRowCD L (X.band i) R.K₁ R.K₂ R.K₃ (D.nd.l i) lam : ℚ) : ℝ))` using `by show KillingConditions.lenR X.len0 i lam = _`. Unfold `KillingConditions.lenR`. Use `congr 1`. Use function extensionality and compare the values at `π`.

Rewrite using `[hD.len0I i hI π lam, hD.rowCD i hI hB]`. Rewrite using `[key]`. Unfold `KillingConditions.supZ`. Use `split_ifs with hne`. Rewrite using `[Finset.sup'_const]`.

Unfold `lenRowCD`. Use `ratIn_le ?_ h0` and prove the remaining obligations. Unfold `bdCD`. Establish `h4 : R.K₃ ≤ C * C` using `by nlinarith`. Use `mul_le_mul_of_nonneg_right h1 hH` as an intermediate fact.

Use `mul_le_mul_of_nonneg_right h2 hF` as an intermediate fact. Use `mul_le_mul_of_nonneg_right h4 hM` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h0`.
-/
theorem len_le {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ)
    (hD : KillingConditions.DataAD L HW X R) (hR : R.Le C) (i : D.nd.Loc) (hI : TwistedPlaces.InertK D (D.nd.l i))
    (hB : ¬ KillingConditions.IsRowB L (D.nd.l i)) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    (tabX L X).len i lam ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by
  obtain ⟨-, -, -, -, hC1, -, h1, h2, h3, -⟩ := hR
  have hH := coreH_nonneg L (D.nd.l i) lam
  have hF := coreF_nonneg L (X.band i lam) (D.nd.l i) lam
  have hM := coreM_nonneg L (D.nd.l i) lam
  have hC0 : (0:ℝ) ≤ C := by linarith
  have h0 : 0 ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by positivity
  have key : (tabX L X).len i lam = KillingConditions.supZ i
      (fun _ => ((lenRowCD L (X.band i) R.K₁ R.K₂ R.K₃ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hD.rowCD i hI hB]
  rw [key]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenRowCD
    refine ratIn_le ?_ h0
    unfold bdCD
    have h4 : R.K₃ ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hH
    have := mul_le_mul_of_nonneg_right h2 hF
    have := mul_le_mul_of_nonneg_right h4 hM
    linarith
  · exact h0

end GlobalTheory.NLink.RowCDSize

/- English proof (translation)
Introduce `D L P HW X R C hD hR`. Establish `hfl : ∀ i lam l, TwistedPlaces.flatCD L (tabX L X) i lam l = flat L (X.band i lam) l` using `fun _ _ _ => rfl`. Establish `he : ∀ l, TwistedPlaces.eP L C l = C * coreE L l` using `fun _ => rfl`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `i - ⟨hI, hA, -, -⟩ lam -`.

Establish `h` using `GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.1 (not_lt.2 hA)) lam`. Rewrite using `[hfl, he]`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Unfold `coreH coreF coreM`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `i - ⟨hI, -, hO, -⟩ lam -`. Establish `h` using `GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.2 (not_lt.2 hO)) lam`. Rewrite using `[hfl, he]`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Unfold `coreH coreF coreM`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.NLink.localBoundTable_rowsCD_admissible : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C := by
  intro D L P HW X R C hD hR
  have hfl : ∀ i lam l, TwistedPlaces.flatCD L (tabX L X) i lam l = flat L (X.band i lam) l := fun _ _ _ => rfl
  have he : ∀ l, TwistedPlaces.eP L C l = C * coreE L l := fun _ => rfl
  constructor
  · rintro i - ⟨hI, hA, -, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.1 (not_lt.2 hA)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring
  · rintro i - ⟨hI, -, hO, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.2 (not_lt.2 hO)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring

end
