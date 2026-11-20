import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.ExistsDs
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.NonVanishing
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpaces
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.ContinuousUmInv
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.EmbRow

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

/- English proof (translation)
Introduce `a b hab` and use `hh.trans (hg a b hab)`.
-/
theorem gap_mono {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {h h' : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : h' ≤ h) :
    Formalism.QuantumDeterminants.GapAtLeast ε lam h' := fun a b hab => hh.trans (hg a b hab)

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hMod hOf _ hDec n ε lam ε' mu e hG j hG' hwall hOcc`. Use `(hMod n ε lam ε' (mu - Pi.single j 1) e hG').1 ?_` and prove the remaining obligations. Take `⟨N, rfl⟩ : ∃ N, n = N + 1` from `⟨n - 1, by have := hG.two; omega⟩`. Establish `hN1 : 1 ≤ N + 1` using `by omega`. Establish `hc1 : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Establish `gG : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((N + 2 : ℕ) : ℝ) ^ 3)`. Establish `h` using `hG.gap`. Use `gap_mono h (le_of_eq ?_)` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `gH : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((N + 1 : ℕ) : ℝ) ^ 3)` using `gap_mono hG.gap' (by have : ((N + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) + 1 := by linarith`. Use `pow_le_pow_left₀ hc1 this 3` as an intermediate fact. Use the proof step `linarith)`. Take `⟨H, i1, i2, π, hπ⟩` from `exists_ds ε lam (by omega) hG.hc gG`. Take `⟨H', i3, i4, σ, hσ⟩` from `exists_ds ε' mu hN1 hG.hc' gH`.

Use `haveI : CompleteSpace H := hπ.1`. Use `haveI : CompleteSpace H' := hσ.1`. Take `⟨j0, hj0, hj0m⟩` from `hOcc H H' π σ hπ hσ`. Take `⟨P, hP, hP0⟩` from `exists_P hG.fits hπ hσ hj0 hj0m`. Take `⟨S, E, hS⟩` from `hSmMod (N + 2) ε H π hπ.2.2.1`.

Take `⟨S', E', hS'⟩` from `hSmMod (N + 1) ε' H' σ hσ.2.2.1`. Take `⟨X, hXS, hXκ⟩` from `hDec (N + 1) ε' mu H' σ (signs hG).1 (signs hG).2 hG.hc' hσ gH`. Establish `hj : j ∈ X.S` using `(hXS j).2 hG'.hc'`. Establish `hσ'` using `(X.ds j hj).2`. Take `⟨η₀, hη₀, hne⟩` from `WordSpanNonVanishing.nonvan hKey hG hπ hσ hS hS' hP hP0 X hXκ j hj hwall`.

Take `⟨R, hR, hRe⟩` from `WordSpaces.pj_words hG hπ hσ hS hS' hP X hXκ j hj`. Establish `hUπ` using `hπ.2.2.1`. Establish `hUσ` using `hσ.2.2.1`. Establish `hden : Dense (S : Set H)` using `dense_sm (by omega) hG.hc hπ (gap_mono gG (by have : (0 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) ^ 3 := by positivity linarith)) hS`. Establish `hφ₀` using `(hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₀ hη₀).1`.

Establish `hx₀` using `X.p_sm j hj _ hφ₀`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, X.p j (phi E e P η₀) l ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (funext h)`.

Establish `hy` using `smT_single (hx₀ l) l`. Establish `hform` using `X.form j hj _ hφ₀ _ hy`. Rewrite `hform` using `[formT_single]`. Establish `hprod : X.c j * ⟪X.pr j (Pi.single l (X.p j (phi E e P η₀) l)), X.pr j (phi E e P η₀)⟫_ℂ ≠ 0`. Rewrite using `[← hform]`.

Apply the tactic sequence `refine mul_ne_zero (by split_ifs <;> norm_num) ?_`. Rewrite using `[inner_self_ne_zero]`. Conclude with `hl`. Establish `hcj : X.c j ≠ 0` using `left_ne_zero_of_mul hprod`. Establish `hpr2` using `right_ne_zero_of_mul hprod`.

Establish `hpry : X.pr j (Pi.single l (X.p j (phi E e P η₀) l)) ≠ 0` using `fun h0 => hpr2 (by rw [h0, inner_zero_left])`. Establish `hprφ : X.pr j (phi E e P η₀) ≠ 0` using `fun h0 => hpr2 (by rw [h0, inner_zero_right])`. Take `⟨w', hw', hw'1⟩` from `exists_low hσ'`. Establish `hw'0 : w' ≠ 0` using `fun h0 => by rw [h0, norm_zero] at hw'1; exact zero_ne_one hw'1`. Take `⟨h₁, hh₁⟩` from `hIrr (N + 1) ε' _ (X.πs j) hσ'.2.2.1 hσ'.2.2.2.1 _ w' hprφ hw'0`.

Take `⟨h₂, hh₂⟩` from `hIrr (N + 1) ε' _ (X.πs j) hσ'.2.2.1 hσ'.2.2.2.1 _ w' hpry hw'0`. Use `set y := (Pi.single l (X.p j (phi E e P η₀) l) : Fin (N + 1) → H') with hyd`. Establish `hmem : ∀ h : UJ ε', emb e (um h) ∈ UJset ε` using `fun h => Formalism.MainNotions.BridgeCSchur.umat_mem (embU hG.fits h)`. Use `set η₁ := π (emb e (um h₁)) η₀ with hη₁d`. Establish `hη₁ : η₁ ∈ S` using `hS.stab _ (hmem h₁) η₀ hη₀`.

Establish `hφ₁e` using `(hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₀ hη₀).2 h₁`. Establish `hφ₁` using `(hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₁ hη₁).1`. Establish `hprφ₁ : X.pr j (phi E e P η₁) = X.πs j (um h₁) (X.pr j (phi E e P η₀))`. Rewrite using `[hφ₁e]`. Conclude with `X.pr_act j hj h₁ _ hφ₀`.

Use `set y₂ := actT σ (um h₂) y with hy₂d`. Establish `hy₂ : y₂ ∈ SmT ε' σ` using `smT_act hUσ h₂ hy`. Establish `hpry₂ : X.pr j y₂ = X.πs j (um h₂) (X.pr j y)` using `X.pr_act j hj h₂ _ hy`. Establish `hA : ⟪X.pr j y₂, w'⟫_ℂ ≠ 0`. Rewrite using `[hpry₂, ← inner_conj_symm]`.

Conclude with `(map_ne_zero _).2 hh₂`. Establish `hB : ⟪w', X.pr j (phi E e P η₁)⟫_ℂ ≠ 0` using `by rw [hprφ₁]; exact hh₁`. Take `⟨κ', hκ', hsch⟩` from `schur_haar hσ' (muG ε')`. Take `⟨hcont, C, hCb⟩` from `decay_low hN1 hG'.hc' hσ' hG'.gap' hw' hw'1`. Assume the negation of the conclusion as `hnot`.

Establish `hall : ∀ a b : H, ∫ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * ⟪b, π (emb e (um h)) a⟫_ℂ ∂(muG ε') = 0`. Introduce `a b`. Assume the negation of the conclusion as `hab`. Take `⟨j1, hj1, hj1m⟩` from `hOf (N + 1) ε lam ε' (mu - Pi.single j 1) e hG' H (X.Hs j) π (X.πs j) (muG ε') inferInstance hπ hσ' w' hw' hw'1 a b hab`. Conclude with `hnot ⟨H, X.Hs j, inferInstance, inferInstance, inferInstance, inferInstance, π, X.πs j, hπ, hσ', j1, hj1, hj1m⟩`.

Establish `hZl` using `fun l' => hZ (N + 1) ε ε' e H π S E hG.fits hN1 hS hUπ hden (muG ε') inferInstance (fun h : UJ ε' => conj ⟪w', X.πs j (um h) w'⟫_ℂ) (N + 1) C hcont hCb hall (R l') (hR l') ⟨η₁, hη₁⟩ (ContinuousLinearMap.adjoint P (y₂ l'))`. Establish `hpt : ∀ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) = ∑ l', (if ε' l' then 1 else -1) * (conj ⟪w', X.πs j (um h) w'⟫_ℂ * ⟪ContinuousLinearMap.adjoint P (y₂ l'), ap (R l') (π (emb e (um h)) η₁)⟫_ℂ)`. Introduce `h`. Establish `e2 : ∀ l', X.p j (phi E e P (π (emb e (um h)) η₁)) l' = P (ap (R l') (π (emb e (um h)) η₁))` using `hRe _ (hS.stab _ (hmem h) η₁ hη₁)`. Simplify using `only [formT, e2, ← ContinuousLinearMap.adjoint_inner_left, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun l' _ => by ring`. Establish `hpt2 : ∀ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) = X.c j * (⟪X.pr j y₂, X.πs j (um h) (X.pr j (phi E e P η₁))⟫_ℂ * conj ⟪w', X.πs j (um h) w'⟫_ℂ)`. Introduce `h`. Establish `e1` using `(hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₁ hη₁).2 h`. Rewrite using `[e1, X.form j hj _ (smT_act hUσ h hφ₁) _ hy₂, X.pr_act j hj h _ hφ₁]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hI0 : ∫ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) ∂(muG ε') = 0`. Rewrite using `[integral_congr_ae (.of_forall hpt), integral_finsetSum _ fun l' _ => (hZl l').1.const_mul _]`. Conclude with `Finset.sum_eq_zero fun l' _ => by rw [integral_const_mul, (hZl l').2, mul_zero]`. Rewrite `hI0` using `[integral_congr_ae (.of_forall hpt2), integral_const_mul, (hsch _ _ _ _).2]`.

Establish `hκ0 : (κ' : ℂ) ≠ 0` using `by exact_mod_cast hκ'.ne'`. Conclude with `mul_ne_zero hcj (mul_ne_zero hκ0 (mul_ne_zero hB hA)) hI0`.
-/
theorem stepM_of (hKey : KeyId) (hZ : Zero) (hPhi : PhiEq) (hIrr : Irr) :
    Models → OfInt → Seed → DecEx2 → StepM := by
  intro hMod hOf _ hDec n ε lam ε' mu e hG j hG' hwall hOcc
  refine (hMod n ε lam ε' (mu - Pi.single j 1) e hG').1 ?_
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by have := hG.two; omega⟩
  have hN1 : 1 ≤ N + 1 := by omega
  have hc1 : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have gG : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((N + 2 : ℕ) : ℝ) ^ 3) := by
    have h := hG.gap
    refine gap_mono h (le_of_eq ?_)
    push_cast; ring
  have gH : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((N + 1 : ℕ) : ℝ) ^ 3) :=
    gap_mono hG.gap' (by have : ((N + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) + 1 := by linarith
                         have := pow_le_pow_left₀ hc1 this 3; linarith)
  obtain ⟨H, i1, i2, π, hπ⟩ := exists_ds ε lam (by omega) hG.hc gG
  obtain ⟨H', i3, i4, σ, hσ⟩ := exists_ds ε' mu hN1 hG.hc' gH
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  obtain ⟨j0, hj0, hj0m⟩ := hOcc H H' π σ hπ hσ
  obtain ⟨P, hP, hP0⟩ := exists_P hG.fits hπ hσ hj0 hj0m
  obtain ⟨S, E, hS⟩ := hSmMod (N + 2) ε H π hπ.2.2.1
  obtain ⟨S', E', hS'⟩ := hSmMod (N + 1) ε' H' σ hσ.2.2.1
  obtain ⟨X, hXS, hXκ⟩ := hDec (N + 1) ε' mu H' σ (signs hG).1 (signs hG).2 hG.hc' hσ gH
  have hj : j ∈ X.S := (hXS j).2 hG'.hc'
  have hσ' := (X.ds j hj).2
  obtain ⟨η₀, hη₀, hne⟩ := WordSpanNonVanishing.nonvan hKey hG hπ hσ hS hS' hP hP0 X hXκ j hj hwall
  obtain ⟨R, hR, hRe⟩ := WordSpaces.pj_words hG hπ hσ hS hS' hP X hXκ j hj
  have hUπ := hπ.2.2.1
  have hUσ := hσ.2.2.1
  have hden : Dense (S : Set H) :=
    dense_sm (by omega) hG.hc hπ (gap_mono gG (by have : (0 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) ^ 3 := by positivity
                                                  linarith)) hS

  have hφ₀ := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₀ hη₀).1
  have hx₀ := X.p_sm j hj _ hφ₀
  obtain ⟨l, hl⟩ : ∃ l, X.p j (phi E e P η₀) l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hy := smT_single (hx₀ l) l
  have hform := X.form j hj _ hφ₀ _ hy
  rw [formT_single] at hform
  have hprod : X.c j * ⟪X.pr j (Pi.single l (X.p j (phi E e P η₀) l)), X.pr j (phi E e P η₀)⟫_ℂ ≠ 0 := by
    rw [← hform]
    refine mul_ne_zero (by split_ifs <;> norm_num) ?_
    rw [inner_self_ne_zero]; exact hl
  have hcj : X.c j ≠ 0 := left_ne_zero_of_mul hprod
  have hpr2 := right_ne_zero_of_mul hprod
  have hpry : X.pr j (Pi.single l (X.p j (phi E e P η₀) l)) ≠ 0 := fun h0 => hpr2 (by rw [h0, inner_zero_left])
  have hprφ : X.pr j (phi E e P η₀) ≠ 0 := fun h0 => hpr2 (by rw [h0, inner_zero_right])
  obtain ⟨w', hw', hw'1⟩ := exists_low hσ'
  have hw'0 : w' ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw'1; exact zero_ne_one hw'1
  obtain ⟨h₁, hh₁⟩ := hIrr (N + 1) ε' _ (X.πs j) hσ'.2.2.1 hσ'.2.2.2.1 _ w' hprφ hw'0
  obtain ⟨h₂, hh₂⟩ := hIrr (N + 1) ε' _ (X.πs j) hσ'.2.2.1 hσ'.2.2.2.1 _ w' hpry hw'0
  set y := (Pi.single l (X.p j (phi E e P η₀) l) : Fin (N + 1) → H') with hyd
  have hmem : ∀ h : UJ ε', emb e (um h) ∈ UJset ε := fun h => Formalism.MainNotions.BridgeCSchur.umat_mem (embU hG.fits h)
  set η₁ := π (emb e (um h₁)) η₀ with hη₁d
  have hη₁ : η₁ ∈ S := hS.stab _ (hmem h₁) η₀ hη₀
  have hφ₁e := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₀ hη₀).2 h₁
  have hφ₁ := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₁ hη₁).1
  have hprφ₁ : X.pr j (phi E e P η₁) = X.πs j (um h₁) (X.pr j (phi E e P η₀)) := by
    rw [hφ₁e]; exact X.pr_act j hj h₁ _ hφ₀
  set y₂ := actT σ (um h₂) y with hy₂d
  have hy₂ : y₂ ∈ SmT ε' σ := smT_act hUσ h₂ hy
  have hpry₂ : X.pr j y₂ = X.πs j (um h₂) (X.pr j y) := X.pr_act j hj h₂ _ hy
  have hA : ⟪X.pr j y₂, w'⟫_ℂ ≠ 0 := by
    rw [hpry₂, ← inner_conj_symm]; exact (map_ne_zero _).2 hh₂
  have hB : ⟪w', X.pr j (phi E e P η₁)⟫_ℂ ≠ 0 := by rw [hprφ₁]; exact hh₁
  obtain ⟨κ', hκ', hsch⟩ := schur_haar hσ' (muG ε')
  obtain ⟨hcont, C, hCb⟩ := decay_low hN1 hG'.hc' hσ' hG'.gap' hw' hw'1
  by_contra hnot
  have hall : ∀ a b : H, ∫ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * ⟪b, π (emb e (um h)) a⟫_ℂ ∂(muG ε') = 0 := by
    intro a b
    by_contra hab
    obtain ⟨j1, hj1, hj1m⟩ := hOf (N + 1) ε lam ε' (mu - Pi.single j 1) e hG' H (X.Hs j) π (X.πs j) (muG ε') inferInstance
      hπ hσ' w' hw' hw'1 a b hab
    exact hnot ⟨H, X.Hs j, inferInstance, inferInstance, inferInstance, inferInstance, π, X.πs j, hπ, hσ', j1, hj1, hj1m⟩
  have hZl := fun l' => hZ (N + 1) ε ε' e H π S E hG.fits hN1 hS hUπ hden (muG ε') inferInstance
    (fun h : UJ ε' => conj ⟪w', X.πs j (um h) w'⟫_ℂ) (N + 1) C hcont hCb hall (R l') (hR l') ⟨η₁, hη₁⟩
    (ContinuousLinearMap.adjoint P (y₂ l'))
  have hpt : ∀ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) =
      ∑ l', (if ε' l' then 1 else -1) * (conj ⟪w', X.πs j (um h) w'⟫_ℂ *
        ⟪ContinuousLinearMap.adjoint P (y₂ l'), ap (R l') (π (emb e (um h)) η₁)⟫_ℂ) := by
    intro h
    have e2 : ∀ l', X.p j (phi E e P (π (emb e (um h)) η₁)) l' = P (ap (R l') (π (emb e (um h)) η₁)) :=
      hRe _ (hS.stab _ (hmem h) η₁ hη₁)
    simp only [formT, e2, ← ContinuousLinearMap.adjoint_inner_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l' _ => by ring
  have hpt2 : ∀ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) =
      X.c j * (⟪X.pr j y₂, X.πs j (um h) (X.pr j (phi E e P η₁))⟫_ℂ * conj ⟪w', X.πs j (um h) w'⟫_ℂ) := by
    intro h
    have e1 := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₁ hη₁).2 h
    rw [e1, X.form j hj _ (smT_act hUσ h hφ₁) _ hy₂, X.pr_act j hj h _ hφ₁]
    ring
  have hI0 : ∫ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) ∂(muG ε') = 0 := by
    rw [integral_congr_ae (.of_forall hpt), integral_finsetSum _ fun l' _ => (hZl l').1.const_mul _]
    exact Finset.sum_eq_zero fun l' _ => by rw [integral_const_mul, (hZl l').2, mul_zero]
  rw [integral_congr_ae (.of_forall hpt2), integral_const_mul, (hsch _ _ _ _).2] at hI0
  have hκ0 : (κ' : ℂ) ≠ 0 := by exact_mod_cast hκ'.ne'
  exact mul_ne_zero hcj (mul_ne_zero hκ0 (mul_ne_zero hB hA)) hI0

end PositivityTheory.RgHe.SM

namespace PositivityTheory.RgHe.SM

/- English proof (translation)
The claim follows from `stepM_of keyId zero_proof phiEq irr`.
-/
theorem model_walk_of_inputs : Models → OfInt → Seed → DecEx2 → StepM := stepM_of keyId zero_proof phiEq irr

end PositivityTheory.RgHe.SM
