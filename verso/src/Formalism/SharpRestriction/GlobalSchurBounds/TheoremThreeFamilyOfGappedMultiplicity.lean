import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HCFdegRGap
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesExistence.LowKMultOneG

noncomputable section

open MeasureTheory

namespace Formalism.MainNotions.GappedMultiplicityBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.StandardLattice PI.UnitaryGroupMassFormula.HCFdegRGap

/- English proof (translation)
Establish `h0 : (0 : ℝ) ≤ (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) * ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)` using `by positivity`. Use `show (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) * ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 1 < h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thrDS_lt {N : ℕ} (ε : Fin N → Bool) {h : ℝ}
    (hh : 32 * (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 2 < h) :
    Formalism.MainNotions.GapDS.thrDS ε < h := by
  have h0 : (0 : ℝ) ≤ (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) := by positivity
  show (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 1 < h
  linarith

/- English proof (translation)
Take `⟨S, hS⟩` from `hDS.2.2.2.2.2.1`. Establish `hset : {S' : Submodule ℂ H | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = {S}`. Use extensionality with `S'`. Prove the components needed by the constructor for the conclusion. Introduce `hS'`.

Conclude with `hL N ε lam H σ hlam hDS h hg hthr S' S hS' hS`. Introduce `hS'`. Rewrite `hS'` using `[Set.mem_singleton_iff]`. Rewrite using `[hS']`. Conclude with `hS`.

Establish `hsub : lowKSub ε lam σ = S` using `by show sSup {S' : Submodule ℂ H | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = S`. Rewrite using `[hset, sSup_singleton]`. Establish `hKU : Formalism.REAL.Kset ε ⊆ UJset ε`. Introduce `g hg`. Establish `hg' : g ∈ Matrix.unitaryGroup (Fin N) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g` using `hg`.

Take `⟨hu, hc⟩` from `hg'`. Establish `h1 : star g * g = 1` using `by first`. Consider the case `exact unitary.star_mul_self_of_mem hu`. Consider the case `exact Unitary.star_mul_self_of_mem hu`. Consider the case `exact (Matrix.mem_unitaryGroup_iff').mp hu`.

Rewrite `h1` using `[Matrix.star_eq_conjTranspose]`. Use `show Matrix.conjTranspose g * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε`. Rewrite using `[mul_assoc, ← hc, ← mul_assoc, h1, one_mul]`. Establish `hU` using `hDS.2.2.1`. Establish `hK : IsURepOn (Formalism.REAL.Kset ε) σ`.

Unfold `IsURepOn Formalism.QuantumDeterminants.IsCRepOn`. Conclude with `⟨⟨hU.1.1, fun a ha b hb => hU.1.2 a (hKU ha) b (hKU hb)⟩, fun g hg v => hU.2.1 g (hKU hg) v, fun v => (hU.2.2 v).mono hKU⟩`. Establish `hpt : ∀ a, (Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) a = lam a + StandardLattice.rhoN ε a`. Introduce `a`. Simplify using `only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, sub_add_cancel]`.

Both sides reduce to the same expression. Rewrite using `[hsub, hW N ε (Formalism.QuantumDeterminants.lowK ε lam) H σ S hK hS]`. Simplify using `only [hpt]`. Both sides reduce to the same expression.
-/
theorem finrank_lowK_eqG (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOneG) {N : ℕ} (ε : Fin N → Bool)
    (lam : Fin N → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (hDS : IsDS ε lam σ) (h : ℝ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hthr : Formalism.MainNotions.GapDS.thrDS ε < h) :
    ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℝ) = StandardLattice.dTau ε lam := by

  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  have hset : {S' : Submodule ℂ H | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = {S} := by
    ext S'
    constructor
    · intro hS'
      exact hL N ε lam H σ hlam hDS h hg hthr S' S hS' hS
    · intro hS'
      rw [Set.mem_singleton_iff] at hS'
      rw [hS']
      exact hS
  have hsub : lowKSub ε lam σ = S := by
    show sSup {S' : Submodule ℂ H | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = S
    rw [hset, sSup_singleton]

  have hKU : Formalism.REAL.Kset ε ⊆ UJset ε := by
    intro g hg
    have hg' : g ∈ Matrix.unitaryGroup (Fin N) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := hg
    obtain ⟨hu, hc⟩ := hg'
    have h1 : star g * g = 1 := by
      first
        | exact unitary.star_mul_self_of_mem hu
        | exact Unitary.star_mul_self_of_mem hu
        | exact (Matrix.mem_unitaryGroup_iff').mp hu
    rw [Matrix.star_eq_conjTranspose] at h1
    show Matrix.conjTranspose g * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
    rw [mul_assoc, ← hc, ← mul_assoc, h1, one_mul]
  have hU := hDS.2.2.1
  have hK : IsURepOn (Formalism.REAL.Kset ε) σ := by
    unfold IsURepOn Formalism.QuantumDeterminants.IsCRepOn
    exact ⟨⟨hU.1.1, fun a ha b hb => hU.1.2 a (hKU ha) b (hKU hb)⟩,
      fun g hg v => hU.2.1 g (hKU hg) v, fun v => (hU.2.2 v).mono hKU⟩
  have hpt : ∀ a, (Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) a = lam a + StandardLattice.rhoN ε a := by
    intro a
    simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, sub_add_cancel]
    rfl
  rw [hsub, hW N ε (Formalism.QuantumDeterminants.lowK ε lam) H σ S hK hS]
  simp only [hpt]
  rfl

/- English proof (translation)
Introduce `N ε lam ep0 h0 H _ _ σ w p q hp hq hlam hgap he1 he2 hh0 hDS hw`. Establish `hNpq : (N : ℝ) = p + q`. Use `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun a => ε a = true)` as an intermediate fact. Establish `h' : (Finset.univ.filter (fun a => ε a = true)).card + (Finset.univ.filter (fun a => ε a = false)).card = N` using `by simpa using this`. Use `show (N : ℝ) = ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) + ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)`.

Establish `h''` using `congrArg (fun x : ℕ => (x : ℝ)) h'`. Move the coercions through the operations in `at h''`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbig : 32 * (N : ℝ) * p * q + 2 < h0` using `gap_big hp hq hNpq he1 he2 hh0`. Establish `hp' : 1 ≤ (Finset.univ.filter (fun a => ε a = true)).card`.

Establish `h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = true)).card : ℝ)` using `hp`. Conclude with `h` after adjusting the coercions. Establish `hq' : 1 ≤ (Finset.univ.filter (fun a => ε a = false)).card`. Establish `h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)` using `hq`. Conclude with `h` after adjusting the coercions.

Establish `hfw` using `hf N ε lam h0 hp' hq' hlam hgap hbig H σ w hDS hw`. Establish `hτ` using `finrank_lowK_eqG hW hL ε lam hlam σ hDS h0 hgap (thrDS_lt ε hbig)`. Establish `hep : 0 < ep0` using `lt_of_lt_of_le (Real.exp_pos _) he1`. Establish `hnn` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_nonneg lam hlam`. Rewrite using `[hfw, hτ]`.

Use `⟨by nlinarith, ?_⟩` and prove the remaining obligations. Establish `hle` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau ε lam hlam`. Establish `hτ0 : 0 < StandardLattice.dTau ε lam` using `StandardLattice.formalDegreeFactor_pos_of_strictAnti ε lam hlam.1`. Establish `hexp : p * q = ((StandardLattice.nPlus ε * StandardLattice.nMinus ε : ℕ) : ℝ)` using `by push_cast; rfl`. Rewrite using `[hexp, Real.rpow_natCast]`.

Establish `hp1 : 1 ≤ StandardLattice.nPlus ε`. Establish `h : (1 : ℝ) ≤ ((StandardLattice.nPlus ε : ℕ) : ℝ)` using `hp`. Conclude with `h` after adjusting the coercions. Establish `hq1 : 1 ≤ StandardLattice.nMinus ε`. Establish `h : (1 : ℝ) ≤ ((StandardLattice.nMinus ε : ℕ) : ℝ)` using `hq`.

Conclude with `h` after adjusting the coercions. Establish `hN` using `StandardLattice.count_plus_add_count_minus N ε`. Establish `hL1` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.lamAbs_ge_one lam hlam (by omega)`. Establish `hpq : (1 : ℝ) ≤ 3 * p * q` using `by nlinarith`. Establish `hX : StandardLattice.lamAbs lam ≤ 3 * p * q * StandardLattice.lamAbs lam` using `by nlinarith`.

Establish `hpow : StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) ≤ (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε)` using `pow_le_pow_left₀ (by linarith) hX _`. Establish `hpos : 0 ≤ (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε)` using `pow_nonneg (by nlinarith) _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem theorem_three_of_gap_bound (s : (n : ℕ) → (Fin n → Bool) → NNReal)
    (hf : ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ),
      1 ≤ (Finset.univ.filter (fun a => ε a = true)).card →
      1 ≤ (Finset.univ.filter (fun a => ε a = false)).card →
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      32 * (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
        ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 2 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam)
    (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOneG) : Formalism.MainNotions.RT.DiscreteSeriesDegreeBoundsAtScale s := by
  intro N ε lam ep0 h0 H _ _ σ w p q hp hq hlam hgap he1 he2 hh0 hDS hw
  have hNpq : (N : ℝ) = p + q := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun a => ε a = true)
    have h' : (Finset.univ.filter (fun a => ε a = true)).card +
        (Finset.univ.filter (fun a => ε a = false)).card = N := by simpa using this
    show (N : ℝ) = ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) +
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)
    have h'' := congrArg (fun x : ℕ => (x : ℝ)) h'
    push_cast at h''
    linarith
  have hbig : 32 * (N : ℝ) * p * q + 2 < h0 := gap_big hp hq hNpq he1 he2 hh0
  have hp' : 1 ≤ (Finset.univ.filter (fun a => ε a = true)).card := by
    have h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) := hp
    exact_mod_cast h
  have hq' : 1 ≤ (Finset.univ.filter (fun a => ε a = false)).card := by
    have h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) := hq
    exact_mod_cast h
  have hfw := hf N ε lam h0 hp' hq' hlam hgap hbig H σ w hDS hw
  have hτ := finrank_lowK_eqG hW hL ε lam hlam σ hDS h0 hgap (thrDS_lt ε hbig)
  have hep : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) he1
  have hnn := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_nonneg lam hlam
  rw [hfw, hτ]
  refine ⟨by nlinarith, ?_⟩
  have hle := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau ε lam hlam
  have hτ0 : 0 < StandardLattice.dTau ε lam := StandardLattice.formalDegreeFactor_pos_of_strictAnti ε lam hlam.1
  have hexp : p * q = ((StandardLattice.nPlus ε * StandardLattice.nMinus ε : ℕ) : ℝ) := by push_cast; rfl
  rw [hexp, Real.rpow_natCast]
  have hp1 : 1 ≤ StandardLattice.nPlus ε := by
    have h : (1 : ℝ) ≤ ((StandardLattice.nPlus ε : ℕ) : ℝ) := hp
    exact_mod_cast h
  have hq1 : 1 ≤ StandardLattice.nMinus ε := by
    have h : (1 : ℝ) ≤ ((StandardLattice.nMinus ε : ℕ) : ℝ) := hq
    exact_mod_cast h
  have hN := StandardLattice.count_plus_add_count_minus N ε
  have hL1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.lamAbs_ge_one lam hlam (by omega)
  have hpq : (1 : ℝ) ≤ 3 * p * q := by nlinarith
  have hX : StandardLattice.lamAbs lam ≤ 3 * p * q * StandardLattice.lamAbs lam := by nlinarith
  have hpow : StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) ≤
      (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
    pow_le_pow_left₀ (by linarith) hX _
  have hpos : 0 ≤ (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
    pow_nonneg (by nlinarith) _
  calc Formalism.QuantumDeterminants.fdegHC lam ≤ StandardLattice.dTau ε lam * StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := hle
    _ ≤ StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
        mul_le_mul_of_nonneg_left hpow hτ0.le
    _ ≤ 4 * StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := by nlinarith

/- English proof (translation)
Introduce `cd s hc` and use `theorem_three_of_gap_bound s (PI.UnitaryGroupMassFormula.HCFdegRGap.hCFdegRGap_holds cd s hc) hW hL`.
-/
theorem theorem_three_of_weyl_gapped_multiplicity (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOneG) : Formalism.MainNotions.RT.DiscreteSeriesDegreeBoundsAllScales :=
  fun cd s hc => theorem_three_of_gap_bound s (PI.UnitaryGroupMassFormula.HCFdegRGap.hCFdegRGap_holds cd s hc) hW hL

/- English proof (translation)
The claim follows from `theorem_three_of_weyl_gapped_multiplicity weylForK_closed Formalism.MainNotions.BesselDiscreteSeries.lowest_K_type_mult_one_of_gaps`.
-/
theorem explicit_bound_all_scales : Formalism.MainNotions.RT.DiscreteSeriesDegreeBoundsAllScales :=
  theorem_three_of_weyl_gapped_multiplicity weylForK_closed Formalism.MainNotions.BesselDiscreteSeries.lowest_K_type_mult_one_of_gaps

/- English proof (translation)
Establish `hAll : StandardLattice.DiscreteSeriesDegreeBoundsOfGap D` using `Formalism.MainNotions.RT.theorem_three_under_scale_of_general (theorem_three_of_weyl_gapped_multiplicity hW hL) D hc`. Introduce `ep0 he1 he2 ρ hgap`. Establish `hHC` using `line_param_harish_chandra D ρ`. Establish `hp : ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = (pY D : ℝ)`. Establish `: (Finset.univ.filter (fun a => epsSH D.R a = true)).card = nPlus (epsSH D.R)` using `rfl`.

Rewrite using `[this, sign_vector_eq_line_sign, count_plus_finCast, count_plus_line_sign]`. Establish `hq : ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = (qY D : ℝ)`. Establish `: (Finset.univ.filter (fun a => epsSH D.R a = false)).card = nMinus (epsSH D.R)` using `rfl`. Rewrite using `[this, sign_vector_eq_line_sign, count_minus_finCast, count_minus_line_sign]`. Establish `hN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ)` using `by rw [dimS_eq]`.

Establish `hg' : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc ρ)) (spectralGapLowerBound D ep0)`. Rewrite using `[sign_vector_eq_line_sign, param_vector_eq_line_param]`. Conclude with `gapAtLeast_finCast _ _ _ _ hgap`. Establish `hp1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ)`. Rewrite using `[hp]`.

Conclude with `(signature_counts_ge_one D).1` after adjusting the coercions. Establish `hq1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ)`. Rewrite using `[hq]`. Conclude with `(signature_counts_ge_one D).2` after adjusting the coercions. Establish `hsum : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) + ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ)`.

Establish `h'` using `congrArg (fun x : ℕ => (x : ℝ)) (card_add_card (epsSH D.R))`. Move the coercions through the operations in `at h' ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbig` using `gap_big (h0 := spectralGapLowerBound D ep0) hp1 hq1 hsum (by rw [hN]; exact he1) he2 (le_of_eq (by rw [hp, hq, hN]; unfold spectralGapLowerBound; rw [Nat.cast_min]))`. Establish `hq0 : ((ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℕ) : ℝ) ≤ ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ)`.

Establish `: ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) ≤ (Finset.univ.filter (fun a => epsSH D.R a = true)).card` using `min_le_left _ _`. Conclude with `this` after adjusting the coercions. Establish `hmax : max (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ)) (8 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ)) < spectralGapLowerBound D ep0`. Generalize the expression as in `((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = p at *`. Generalize the expression as in `((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = q at *`.

Generalize the expression as in `((ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℕ) : ℝ) = r at *`. Generalize the expression as in `((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = n at *`. Establish `hpq : 1 ≤ p * q` using `by nlinarith`. Establish `hn : 1 ≤ n` using `by linarith`. Establish `hrpq : r ≤ p * q` using `by nlinarith`.

Rewrite using `[max_lt_iff]`. Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `hEx` using `dsigEx_at D hdt ρ (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap _ (epsSH D.R) _ hHC (spectralGapLowerBound D ep0) hg' (Or.inr hmax))`.

Take `⟨H, i1, i2, σ, hDS, hF⟩` from `hEx`. Establish `hcs : CompleteSpace H` using `hDS.1`. Establish `hnt : Nontrivial H` using `hDS.2.1`. Take `⟨w, hw⟩` from `exists_ne (0 : H)`. Establish `hdt'` using `finrank_lowK_eqG hW hL (epsSH D.R) (lamSH D.R (D.hc ρ)) hHC σ hDS (spectralGapLowerBound D ep0) hg' (thrDS_lt (epsSH D.R) hbig)`.

Establish `key` using `hAll _ (epsSH D.R) (lamSH D.R (D.hc ρ)) ep0 (spectralGapLowerBound D ep0) H σ w (by rw [hp]; exact_mod_cast (signature_counts_ge_one D).1) (by rw [hq]; exact_mod_cast (signature_counts_ge_one D).2) hHC hg' (by rw [hN]; exact he1) he2 (by rw [hp, hq, hN]; unfold spectralGapLowerBo …`. Rewrite `key` using `[formal_degree_of_eq _ σ _ hF w hw, hp, hq, hdt']`. Rewrite `key` using `[← dimV_eq_fdegHC _ hHC.1]`. Rewrite `key` using `[sign_vector_eq_line_sign, param_vector_eq_line_param, dim_weyl_finCast, formal_degree_finCast, abs_param_sup_finCast]`. Use `⟨key.1, ?_⟩` and prove the remaining obligations.

Establish `e : ((pY D : ℝ) * (qY D : ℝ)) = ((pY D * qY D : ℕ) : ℝ)` using `by push_cast; rfl`. Rewrite `key` using `[e, Real.rpow_natCast]`. Conclude with `key.2`.
-/
theorem theorem_three_rows_of_real_place (D : D7) (hc : cdScaleTie D) (hdt : dsigTie D) (hW : DiscreteSeriesWeylDimension.WeylForK)
    (hL : DiscreteSeriesWeylDimension.LowKMultOneG) : StandardLattice.SigmaDegreeTwoSidedBoundOfGap D := by
  have hAll : StandardLattice.DiscreteSeriesDegreeBoundsOfGap D := Formalism.MainNotions.RT.theorem_three_under_scale_of_general (theorem_three_of_weyl_gapped_multiplicity hW hL) D hc
  intro ep0 he1 he2 ρ hgap
  have hHC := line_param_harish_chandra D ρ
  have hp : ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = (pY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = true)).card = nPlus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_plus_finCast, count_plus_line_sign]
  have hq : ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = (qY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = false)).card = nMinus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_minus_finCast, count_minus_line_sign]
  have hN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]
  have hg' : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc ρ)) (spectralGapLowerBound D ep0) := by
    rw [sign_vector_eq_line_sign, param_vector_eq_line_param]; exact gapAtLeast_finCast _ _ _ _ hgap
  have hp1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) := by
    rw [hp]; exact_mod_cast (signature_counts_ge_one D).1
  have hq1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) := by
    rw [hq]; exact_mod_cast (signature_counts_ge_one D).2
  have hsum : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) =
      ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) +
        ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) := by
    have h' := congrArg (fun x : ℕ => (x : ℝ)) (card_add_card (epsSH D.R))
    push_cast at h' ⊢
    linarith
  have hbig := gap_big (h0 := spectralGapLowerBound D ep0) hp1 hq1 hsum (by rw [hN]; exact he1) he2
    (le_of_eq (by rw [hp, hq, hN]; unfold spectralGapLowerBound; rw [Nat.cast_min]))
  have hq0 : ((ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) ≤ (Finset.univ.filter (fun a => epsSH D.R a = true)).card :=
      min_le_left _ _
    exact_mod_cast this
  have hmax : max (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ))
      (8 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ)) < spectralGapLowerBound D ep0 := by
    generalize ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = p at *
    generalize ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = q at *
    generalize ((ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℕ) : ℝ) = r at *
    generalize ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = n at *
    have hpq : 1 ≤ p * q := by nlinarith
    have hn : 1 ≤ n := by linarith
    have hrpq : r ≤ p * q := by nlinarith
    rw [max_lt_iff]
    constructor
    · nlinarith
    · nlinarith
  have hEx := dsigEx_at D hdt ρ
    (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap _ (epsSH D.R) _ hHC (spectralGapLowerBound D ep0) hg' (Or.inr hmax))
  obtain ⟨H, i1, i2, σ, hDS, hF⟩ := hEx
  have hcs : CompleteSpace H := hDS.1
  have hnt : Nontrivial H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hdt' := finrank_lowK_eqG hW hL (epsSH D.R) (lamSH D.R (D.hc ρ)) hHC σ hDS (spectralGapLowerBound D ep0) hg'
    (thrDS_lt (epsSH D.R) hbig)
  have key := hAll _ (epsSH D.R) (lamSH D.R (D.hc ρ)) ep0 (spectralGapLowerBound D ep0) H σ w
    (by rw [hp]; exact_mod_cast (signature_counts_ge_one D).1) (by rw [hq]; exact_mod_cast (signature_counts_ge_one D).2) hHC hg'
    (by rw [hN]; exact he1) he2
    (by rw [hp, hq, hN]; unfold spectralGapLowerBound; rw [Nat.cast_min]) hDS hw
  rw [formal_degree_of_eq _ σ _ hF w hw, hp, hq, hdt'] at key
  rw [← dimV_eq_fdegHC _ hHC.1] at key
  rw [sign_vector_eq_line_sign, param_vector_eq_line_param, dim_weyl_finCast, formal_degree_finCast, abs_param_sup_finCast] at key
  refine ⟨key.1, ?_⟩
  have e : ((pY D : ℝ) * (qY D : ℝ)) = ((pY D * qY D : ℕ) : ℝ) := by push_cast; rfl
  rw [e, Real.rpow_natCast] at key
  exact key.2

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun x _ _ i => theorem_three_rows_of_real_place (Fm.D x i) (Fm.ties x i).cdScale_tie (Fm.ties x i).dsig_tie weylForK_closed hL⟩`.
-/
theorem theorem_three_family_of_gapped_multiplicity {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hL : DiscreteSeriesWeylDimension.LowKMultOneG) :
    Formalism.MainNotions.flipTwoThree.fam0 Fm Formalism.MainNotions.StandardLattice.SigmaDegreeTwoSidedBoundOfGap :=
  ⟨0, fun x _ _ i => theorem_three_rows_of_real_place (Fm.D x i) (Fm.ties x i).cdScale_tie (Fm.ties x i).dsig_tie
    weylForK_closed hL⟩

/- English proof (translation)
The claim follows from `theorem_three_family_of_gapped_multiplicity Fm Formalism.MainNotions.BesselDiscreteSeries.lowest_K_type_mult_one_of_gaps`.
-/
theorem explicit_bound_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.flipTwoThree.fam0 Fm Formalism.MainNotions.StandardLattice.SigmaDegreeTwoSidedBoundOfGap :=
  theorem_three_family_of_gapped_multiplicity Fm Formalism.MainNotions.BesselDiscreteSeries.lowest_K_type_mult_one_of_gaps

/- English proof (translation)
Introduce `x i`. Conclude with `theorem_three_rows_of_real_place (Fm.D x i) (Fm.ties x i).cdScale_tie (Fm.ties x i).dsig_tie weylForK_closed Formalism.MainNotions.BesselDiscreteSeries.lowest_K_type_mult_one_of_gaps`.
-/
theorem theorem_three_rows_family_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : StandardLattice.FamilySigmaDegreeTwoSidedBound Fm := by
  intro x i
  exact theorem_three_rows_of_real_place (Fm.D x i) (Fm.ties x i).cdScale_tie (Fm.ties x i).dsig_tie
    weylForK_closed Formalism.MainNotions.BesselDiscreteSeries.lowest_K_type_mult_one_of_gaps

/- English proof (translation)
Unfold `StandardLattice.dTau`. Apply `div_nonneg` to reduce the goal to its premises. Apply `Finset.prod_nonneg` to reduce the goal to its premises. Introduce `a _`. Apply `Finset.prod_nonneg` to reduce the goal to its premises.

Introduce `b hb`. Rewrite `hb` using `[Finset.mem_filter]`. Take `⟨_, hab, hs⟩` from `hb`. Establish `h1 : L b < L a` using `hL hab`. Establish `h2 : StandardLattice.rhoN S b ≤ StandardLattice.rhoN S a`.

Unfold `StandardLattice.rhoN`. Establish `c1 : ((Finset.univ.filter (fun x => b < x ∧ S x ≠ S b)).card : ℝ) ≤ ((Finset.univ.filter (fun x => a < x ∧ S x ≠ S a)).card : ℝ)`. Conclude with `Finset.card_le_card (by` after adjusting the coercions. Introduce `x hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`.

Conclude with `⟨lt_trans hab hx.1, by rw [hs]; exact hx.2⟩)`. Establish `c2 : ((Finset.univ.filter (fun x => x < a ∧ S x ≠ S a)).card : ℝ) ≤ ((Finset.univ.filter (fun x => x < b ∧ S x ≠ S b)).card : ℝ)`. Conclude with `Finset.card_le_card (by` after adjusting the coercions. Introduce `x hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`.

Conclude with `⟨lt_trans hx.1 hab, by rw [← hs]; exact hx.2⟩)`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Apply `mul_nonneg` to reduce the goal to its premises. Unfold `StandardLattice.facProd`.

Conclude with `Finset.prod_nonneg (fun i _ => by positivity)`. Unfold `StandardLattice.facProd`. Conclude with `Finset.prod_nonneg (fun i _ => by positivity)`.
-/
private theorem dTau_nonneg_of_strictAnti {N : ℕ} (S : Fin N → Bool) (L : Fin N → ℝ) (hL : StrictAnti L) :
    0 ≤ StandardLattice.dTau S L := by
  unfold StandardLattice.dTau
  apply div_nonneg
  · apply Finset.prod_nonneg
    intro a _
    apply Finset.prod_nonneg
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨_, hab, hs⟩ := hb
    have h1 : L b < L a := hL hab
    have h2 : StandardLattice.rhoN S b ≤ StandardLattice.rhoN S a := by
      unfold StandardLattice.rhoN
      have c1 : ((Finset.univ.filter (fun x => b < x ∧ S x ≠ S b)).card : ℝ) ≤
          ((Finset.univ.filter (fun x => a < x ∧ S x ≠ S a)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨lt_trans hab hx.1, by rw [hs]; exact hx.2⟩)
      have c2 : ((Finset.univ.filter (fun x => x < a ∧ S x ≠ S a)).card : ℝ) ≤
          ((Finset.univ.filter (fun x => x < b ∧ S x ≠ S b)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨lt_trans hx.1 hab, by rw [← hs]; exact hx.2⟩)
      linarith
    linarith
  · apply mul_nonneg
    · unfold StandardLattice.facProd
      exact Finset.prod_nonneg (fun i _ => by positivity)
    · unfold StandardLattice.facProd
      exact Finset.prod_nonneg (fun i _ => by positivity)

/- English proof (translation)
Unfold `StandardLattice.FamilyTheoremThree`. Introduce `x i`. Unfold `StandardLattice.PointsLemma`. Establish `h` using `theorem_three_rows_family_holds Fm x i`. Unfold `StandardLattice.SigmaDegreeTwoSidedBoundOfGap at h`.

Introduce `ep0 h1 h2 ρ hg`. Establish `hr : (1 : ℝ) ≤ ((Fm.D x i).R.r : ℝ)`. Break down `Nat.eq_zero_or_pos (Fm.D x i).R.r with h0 | h0` into its components or cases. Rewrite `h1` using `[h0]`. Simplify using `at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h0` after adjusting the coercions. Establish `h8 : (8192 : ℝ) ≤ C3 * ((Fm.D x i).R.r : ℝ)` using `by nlinarith`. Establish `hM : 0 ≤ ((min (pY (Fm.D x i)) (qY (Fm.D x i)) : ℕ) : ℝ) * (((pY (Fm.D x i) : ℕ) : ℝ) * ((qY (Fm.D x i) : ℕ) : ℝ)) ^ 3 * Real.log ((Fm.D x i).R.r : ℝ)`. Use `Real.log_natCast_nonneg (Fm.D x i).R.r` as an intermediate fact.

Check the signs of the components of the expression. Establish `key : StandardLattice.spectralGapLowerBound (Fm.D x i) ep0 ≤ StandardLattice.gap3 (Fm.D x i) C3 ep0` using `by clear h hg h1 h2`. Unfold `StandardLattice.spectralGapLowerBound StandardLattice.gap3`. Use `gcongr ?_ / _`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 h8) hM]`.

Take `⟨hl, hu⟩` from `h ep0 h1 h2 ρ (fun a b hab => le_trans key (hg a b hab))`. Use `⟨hl, le_trans hu ?_⟩` and prove the remaining obligations. Establish `hT` using `dTau_nonneg_of_strictAnti (rowSgn (Fm.D x i)) (rowLam (Fm.D x i) ρ) (StandardLattice.line_param_strictAnti (Fm.D x i) ρ)`. Establish `hA : 0 ≤ lamAbs (rowLam (Fm.D x i) ρ)` using `Real.iSup_nonneg (fun a => Real.iSup_nonneg (fun b => abs_nonneg _))`. Establish `h3 : (3 : ℝ) ≤ C3 * ((Fm.D x i).R.r : ℝ)` using `by linarith`.

Establish `hP : 0 ≤ ((pY (Fm.D x i) : ℕ) : ℝ) * ((qY (Fm.D x i) : ℕ) : ℝ) * lamAbs (rowLam (Fm.D x i) ρ)`. Check the signs of the components of the expression. Use `mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hT)` and prove the remaining obligations. Use `gcongr ?_ ^ _`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 h3) hP]`.
-/
theorem theorem_three_family_large_constant {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C3 : ℝ) (hC3 : 8192 ≤ C3) : StandardLattice.FamilyTheoremThree Fm C3 := by
  unfold StandardLattice.FamilyTheoremThree
  intro x i
  unfold StandardLattice.PointsLemma
  have h := theorem_three_rows_family_holds Fm x i
  unfold StandardLattice.SigmaDegreeTwoSidedBoundOfGap at h
  intro ep0 h1 h2 ρ hg
  have hr : (1 : ℝ) ≤ ((Fm.D x i).R.r : ℝ) := by
    rcases Nat.eq_zero_or_pos (Fm.D x i).R.r with h0 | h0
    · rw [h0] at h1
      simp at h1
      linarith
    · exact_mod_cast h0
  have h8 : (8192 : ℝ) ≤ C3 * ((Fm.D x i).R.r : ℝ) := by nlinarith
  have hM : 0 ≤ ((min (pY (Fm.D x i)) (qY (Fm.D x i)) : ℕ) : ℝ) *
      (((pY (Fm.D x i) : ℕ) : ℝ) * ((qY (Fm.D x i) : ℕ) : ℝ)) ^ 3 * Real.log ((Fm.D x i).R.r : ℝ) := by
    have := Real.log_natCast_nonneg (Fm.D x i).R.r
    positivity
  have key : StandardLattice.spectralGapLowerBound (Fm.D x i) ep0 ≤ StandardLattice.gap3 (Fm.D x i) C3 ep0 := by
    clear h hg h1 h2
    unfold StandardLattice.spectralGapLowerBound StandardLattice.gap3
    gcongr ?_ / _
    nlinarith [mul_nonneg (sub_nonneg.2 h8) hM]
  obtain ⟨hl, hu⟩ := h ep0 h1 h2 ρ (fun a b hab => le_trans key (hg a b hab))
  refine ⟨hl, le_trans hu ?_⟩
  have hT := dTau_nonneg_of_strictAnti (rowSgn (Fm.D x i)) (rowLam (Fm.D x i) ρ) (StandardLattice.line_param_strictAnti (Fm.D x i) ρ)
  have hA : 0 ≤ lamAbs (rowLam (Fm.D x i) ρ) :=
    Real.iSup_nonneg (fun a => Real.iSup_nonneg (fun b => abs_nonneg _))
  have h3 : (3 : ℝ) ≤ C3 * ((Fm.D x i).R.r : ℝ) := by linarith
  have hP : 0 ≤ ((pY (Fm.D x i) : ℕ) : ℝ) * ((qY (Fm.D x i) : ℕ) : ℝ) * lamAbs (rowLam (Fm.D x i) ρ) := by
    positivity
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hT)
  gcongr ?_ ^ _
  nlinarith [mul_nonneg (sub_nonneg.2 h3) hP]

end Formalism.MainNotions.GappedMultiplicityBounds

end
