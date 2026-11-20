import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.LocalToGlobal.GlobalTheory.GL5.TheoremThreeAllUnitary
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.NonvanishingBesselPeriod
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S MeasureTheory Matrix

def DiscreteSeriesDegreeBoundsOfScaleAgreement (D : D7) : Prop := cdScaleTie D → StandardLattice.DiscreteSeriesDegreeBoundsOfGap D

def DsigExT (D : D7) : Prop := dsigTie D → StandardLattice.DsigEx D

def cdScaleTieR (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((s n ε : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem cdScaleTie_iff (D : D7) : cdScaleTie D ↔ cdScaleTieR D.cd D.s.cdScale := Iff.rfl

def DiscreteSeriesDegreeBoundsAtScale (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    let p : ℝ := (Finset.univ.filter (fun a => ε a = true)).card
    let q : ℝ := (Finset.univ.filter (fun a => ε a = false)).card
    1 ≤ p → 1 ≤ q →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h0 →
    Real.exp (-(N : ℝ)) ≤ ep0 → ep0 < 1 / 2 →
    8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0 →
    IsDS ε lam σ → w ≠ 0 →
    (1 - ep0) * Formalism.QuantumDeterminants.fdegHC lam ≤ fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ∧
    fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
      4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) * (3 * p * q * StandardLattice.lamAbs lam) ^ (p * q)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem theorem_three_explicit_iff_scale (D : D7) : StandardLattice.DiscreteSeriesDegreeBoundsOfGap D ↔ DiscreteSeriesDegreeBoundsAtScale D.s.cdScale := Iff.rfl

def HCFdegR : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), cdScaleTieR cd s →
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
      fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam

/- English proof (translation)
Introduce `hT` and use `h D.cd D.s.cdScale ((cdScaleTie_iff D).mp hT)`.
-/
theorem hcFormalDegree_of_R (h : HCFdegR) (D : D7) : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree D := fun hT => h D.cd D.s.cdScale ((cdScaleTie_iff D).mp hT)

def DiscreteSeriesDegreeBoundsAllScales : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), cdScaleTieR cd s → DiscreteSeriesDegreeBoundsAtScale s

/- English proof (translation)
Take `⟨-, -, hURep, -, -, ⟨S, hS⟩, -⟩` from `id hDS`. Establish `hsub : lowKSub ε lam σ = S`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `sSup_le fun S' hS' => (hL N ε lam H σ hlam hDS S' S hS' hS).le`. Conclude with `le_sSup hS`.

Establish `hKsub : Formalism.REAL.Kset ε ⊆ UJset ε`. Introduce `g hg`. Take `⟨hu, hc⟩` from `hg`. Use `show Formalism.REAL.inUJ ε g`. Unfold `Formalism.REAL.inUJ`.

Rewrite `hu` using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Rewrite using `[Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu, Matrix.one_mul]`. Establish `hU : IsURepOn (Formalism.REAL.Kset ε) σ`. Take `⟨⟨h1, hmul⟩, hnorm, hcont⟩` from `hURep`. Unfold `IsURepOn Formalism.QuantumDeterminants.IsCRepOn`.

Conclude with `⟨⟨h1, fun a ha b hb => hmul a (hKsub ha) b (hKsub hb)⟩, fun g hg v => hnorm g (hKsub hg) v, fun v => (hcont v).mono hKsub⟩`. Establish `hrho : ∀ a, (Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) a = lam a + StandardLattice.rhoN ε a`. Introduce `a`. Establish `e : Formalism.REAL.rhoN ε a = StandardLattice.rhoN ε a` using `rfl`. Simplify using `only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply]`.

Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsub, hW N ε (Formalism.QuantumDeterminants.lowK ε lam) H σ S hU hS]`. Unfold `StandardLattice.dTau`. Simplify using `only [hrho]`.

Both sides reduce to the same expression.
-/
theorem finrank_lowK_eq (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOne) {N : ℕ} (ε : Fin N → Bool)
    (lam : Fin N → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (hDS : IsDS ε lam σ) :
    ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℝ) = StandardLattice.dTau ε lam := by
  obtain ⟨-, -, hURep, -, -, ⟨S, hS⟩, -⟩ := id hDS
  have hsub : lowKSub ε lam σ = S := by
    apply le_antisymm
    · exact sSup_le fun S' hS' => (hL N ε lam H σ hlam hDS S' S hS' hS).le
    · exact le_sSup hS
  have hKsub : Formalism.REAL.Kset ε ⊆ UJset ε := by
    intro g hg
    obtain ⟨hu, hc⟩ := hg
    show Formalism.REAL.inUJ ε g
    unfold Formalism.REAL.inUJ
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hU : IsURepOn (Formalism.REAL.Kset ε) σ := by
    obtain ⟨⟨h1, hmul⟩, hnorm, hcont⟩ := hURep
    unfold IsURepOn Formalism.QuantumDeterminants.IsCRepOn
    exact ⟨⟨h1, fun a ha b hb => hmul a (hKsub ha) b (hKsub hb)⟩, fun g hg v => hnorm g (hKsub hg) v,
      fun v => (hcont v).mono hKsub⟩
  have hrho : ∀ a, (Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) a = lam a + StandardLattice.rhoN ε a := by
    intro a
    have e : Formalism.REAL.rhoN ε a = StandardLattice.rhoN ε a := rfl
    simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply]
    rw [e]
    ring
  rw [hsub, hW N ε (Formalism.QuantumDeterminants.lowK ε lam) H σ S hU hS]
  unfold StandardLattice.dTau
  simp only [hrho]
  rfl

/- English proof (translation)
Unfold `DiscreteSeriesDegreeBoundsAtScale`. Introduce `N ε lam ep0 h0 H _ _ σ w p q hp hq hlam _ hep hep2 _ hDS hw`. Establish `hF` using `hf N ε lam hlam H σ w hDS hw`. Establish `hK` using `finrank_lowK_eq hW hL ε lam hlam σ hDS`. Rewrite using `[hF, hK]`.

Establish `hFn : 0 ≤ Formalism.QuantumDeterminants.fdegHC lam` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_nonneg lam hlam`. Establish `hep0 : 0 < ep0` using `lt_of_lt_of_le (Real.exp_pos _) hep`. Use `⟨by nlinarith [mul_nonneg hep0.le hFn], ?_⟩` and prove the remaining obligations. Establish `hp' : p = (StandardLattice.nPlus ε : ℝ)` using `rfl`. Establish `hq' : q = (StandardLattice.nMinus ε : ℝ)` using `rfl`.

Establish `hdT : 0 ≤ StandardLattice.dTau ε lam` using `by rw [← hK]; exact Nat.cast_nonneg _`. Establish `hN : 2 ≤ N`. Establish `h1r : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = true)).card : ℝ)` using `hp`. Establish `h2r : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)` using `hq`. Establish `h1 : 1 ≤ (Finset.univ.filter (fun a => ε a = true)).card` using `by exact_mod_cast h1r`.

Establish `h2 : 1 ≤ (Finset.univ.filter (fun a => ε a = false)).card` using `by exact_mod_cast h2r`. Take `⟨a, ha⟩` from `Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a => ε a = true)).card)`. Take `⟨b, hb⟩` from `Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a => ε a = false)).card)`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb`. Establish `hab : a.val ≠ b.val`.

Introduce `h`. Establish `: a = b` using `Fin.ext h`. Rewrite `ha` using `[this, hb]`. Conclude with `Bool.noConfusion ha`. Use `a.isLt` as an intermediate fact.

Use `b.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hL1` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.lamAbs_ge_one lam hlam hN`. Establish `hle` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau ε lam hlam`. Establish `hpq : p * q = ((StandardLattice.nPlus ε * StandardLattice.nMinus ε : ℕ) : ℝ)` using `by rw [hp', hq']; push_cast; ring`.

Rewrite using `[hpq, Real.rpow_natCast]`. Establish `h3 : (1 : ℝ) ≤ 3 * p * q` using `by nlinarith`. Establish `hbase : StandardLattice.lamAbs lam ≤ 3 * p * q * StandardLattice.lamAbs lam`. Use `mul_le_mul_of_nonneg_right h3 (show (0 : ℝ) ≤ StandardLattice.lamAbs lam by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Apply the tactic sequence `have hpow : StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) ≤ (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := by gcongr <;> linarith`. Establish `hnn : 0 ≤ StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε)` using `mul_nonneg hdT (pow_nonneg (by linarith) _)`. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem theorem_three_at_scale_of_degree (s : (n : ℕ) → (Fin n → Bool) → NNReal)
    (hf : ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam)
    (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOne) : DiscreteSeriesDegreeBoundsAtScale s := by
  unfold DiscreteSeriesDegreeBoundsAtScale
  intro N ε lam ep0 h0 H _ _ σ w p q hp hq hlam _ hep hep2 _ hDS hw
  have hF := hf N ε lam hlam H σ w hDS hw
  have hK := finrank_lowK_eq hW hL ε lam hlam σ hDS
  rw [hF, hK]
  have hFn : 0 ≤ Formalism.QuantumDeterminants.fdegHC lam := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_nonneg lam hlam
  have hep0 : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) hep
  refine ⟨by nlinarith [mul_nonneg hep0.le hFn], ?_⟩
  have hp' : p = (StandardLattice.nPlus ε : ℝ) := rfl
  have hq' : q = (StandardLattice.nMinus ε : ℝ) := rfl
  have hdT : 0 ≤ StandardLattice.dTau ε lam := by rw [← hK]; exact Nat.cast_nonneg _
  have hN : 2 ≤ N := by
    have h1r : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) := hp
    have h2r : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) := hq
    have h1 : 1 ≤ (Finset.univ.filter (fun a => ε a = true)).card := by exact_mod_cast h1r
    have h2 : 1 ≤ (Finset.univ.filter (fun a => ε a = false)).card := by exact_mod_cast h2r
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a => ε a = true)).card)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a => ε a = false)).card)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hab : a.val ≠ b.val := by
      intro h
      have : a = b := Fin.ext h
      rw [this, hb] at ha
      exact Bool.noConfusion ha
    have := a.isLt
    have := b.isLt
    omega
  have hL1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.lamAbs_ge_one lam hlam hN
  have hle := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau ε lam hlam
  have hpq : p * q = ((StandardLattice.nPlus ε * StandardLattice.nMinus ε : ℕ) : ℝ) := by rw [hp', hq']; push_cast; ring
  rw [hpq, Real.rpow_natCast]
  have h3 : (1 : ℝ) ≤ 3 * p * q := by nlinarith
  have hbase : StandardLattice.lamAbs lam ≤ 3 * p * q * StandardLattice.lamAbs lam := by
    have := mul_le_mul_of_nonneg_right h3 (show (0 : ℝ) ≤ StandardLattice.lamAbs lam by linarith)
    linarith
  have hpow : StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) ≤
      (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := by
    gcongr <;> linarith
  have hnn : 0 ≤ StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
    mul_nonneg hdT (pow_nonneg (by linarith) _)
  calc Formalism.QuantumDeterminants.fdegHC lam ≤ StandardLattice.dTau ε lam * StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := hle
    _ ≤ StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
        mul_le_mul_of_nonneg_left hpow hdT
    _ ≤ 4 * StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := by
        nlinarith

/- English proof (translation)
Introduce `cd s hs` and use `theorem_three_at_scale_of_degree s (hHC cd s hs) hW hL`.
-/
theorem explicit_bound_all_scales_of_formal_degree (hHC : HCFdegR) (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOne) : DiscreteSeriesDegreeBoundsAllScales := fun cd s hs => theorem_three_at_scale_of_degree s (hHC cd s hs) hW hL

/- English proof (translation)
Introduce `hT` and use `(theorem_three_explicit_iff_scale D).mpr (h D.cd D.s.cdScale ((cdScaleTie_iff D).mp hT))`.
-/
theorem theorem_three_under_scale_of_general (h : DiscreteSeriesDegreeBoundsAllScales) (D : D7) : DiscreteSeriesDegreeBoundsOfScaleAgreement D := fun hT => (theorem_three_explicit_iff_scale D).mpr (h D.cd D.s.cdScale ((cdScaleTie_iff D).mp hT))

/- English proof (translation)
Introduce `hT` and use `(theorem_three_explicit_iff_scale D).mpr (theorem_three_at_scale_of_degree D.s.cdScale (hHC hT) hW hL)`.
-/
theorem theorem_three_under_scale_of_degree (D : D7) (hHC : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HCFormalDegree D) (hW : DiscreteSeriesWeylDimension.WeylForK)
    (hL : DiscreteSeriesWeylDimension.LowKMultOne) : DiscreteSeriesDegreeBoundsOfScaleAgreement D := fun hT => (theorem_three_explicit_iff_scale D).mpr (theorem_three_at_scale_of_degree D.s.cdScale (hHC hT) hW hL)

/- English proof (translation)
Introduce `hT`. Unfold `StandardLattice.DsigEx`. Introduce `τ`. Unfold `dsigTie at hT`. Take `⟨H, i1, i2, σ, hσ⟩` from `hE _ (epsSH D.R) (lamSH D.R (D.hc τ)) (Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc τ))`.

Take `⟨hC, -⟩` from `id hσ`. Take `⟨d, hd⟩` from `Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ σ hσ`. Establish `hc` using `D.s.cdScale_pos (2 * D.R.rS + D.R.k + 1) (epsSH D.R)`. Establish `h3` using `Formalism.MainNotions.StandardLattice.isFormalDegree_smul_measure _ σ d _ hc hd`. Establish `h4` using `hT τ H σ _ hσ h3`.

Use `⟨H, i1, i2, σ, hσ, ?_⟩` and prove the remaining obligations. Rewrite using `[← h4]`. Conclude with `h3`.
-/
theorem dsigExT_of (D : D7) (hE : DiscreteSeriesWeylDimension.DiscreteSeriesExists) : DsigExT D := by
  intro hT
  unfold StandardLattice.DsigEx
  intro τ
  unfold dsigTie at hT
  obtain ⟨H, i1, i2, σ, hσ⟩ := hE _ (epsSH D.R) (lamSH D.R (D.hc τ))
    (Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc τ))
  obtain ⟨hC, -⟩ := id hσ
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ σ hσ
  have hc := D.s.cdScale_pos (2 * D.R.rS + D.R.k + 1) (epsSH D.R)
  have h3 := Formalism.MainNotions.StandardLattice.isFormalDegree_smul_measure _ σ d _ hc hd
  have h4 := hT τ H σ _ hσ h3
  refine ⟨H, i1, i2, σ, hσ, ?_⟩
  rw [← h4]
  exact h3

variable {eps : ℝ}

/- English proof (translation)
Use `⟨0, fun x _ _ i => ?_⟩` and prove the remaining obligations. Establish `ht` using `Fm.ties x i`. Conclude with `StandardLattice.theorem_three_sigma_holds _ (h3 _ ht.cdScale_tie) (DiscreteSeriesWeylDimension.lowest_K_type_count_of_weyl _ hW hL) (hDs _ ht.dsig_tie)`.
-/
theorem fam0_theoremThreeSigmaExplicit_of_weyl (Fm : FamP eps) (h3 : ∀ D, DiscreteSeriesDegreeBoundsOfScaleAgreement D) (hDs : ∀ D, DsigExT D) (hW : DiscreteSeriesWeylDimension.WeylForK)
    (hL : DiscreteSeriesWeylDimension.LowKMultOne) : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap := by
  refine ⟨0, fun x _ _ i => ?_⟩
  have ht := Fm.ties x i
  exact StandardLattice.theorem_three_sigma_holds _ (h3 _ ht.cdScale_tie) (DiscreteSeriesWeylDimension.lowest_K_type_count_of_weyl _ hW hL) (hDs _ ht.dsig_tie)

/- English proof (translation)
The claim follows from `linkGLOBAL7_min Fm Cabs CH C0 C5 hCabs hCH hC0 h2b h2v (fam0_theoremThreeSigmaExplicit_of_weyl Fm h3 hDs hWK hLK) hZa hZb tCV hW hμ hI hR hB`.
-/
theorem linkGLOBAL7_tied3 (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)
    (h2b : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂) (h2v : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass)
    (h3 : ∀ D, DiscreteSeriesDegreeBoundsOfScaleAgreement D) (hDs : ∀ D, DsigExT D) (hWK : DiscreteSeriesWeylDimension.WeylForK) (hLK : DiscreteSeriesWeylDimension.LowKMultOne)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine)
    (hI : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  linkGLOBAL7_min Fm Cabs CH C0 C5 hCabs hCH hC0 h2b h2v (fam0_theoremThreeSigmaExplicit_of_weyl Fm h3 hDs hWK hLK) hZa hZb tCV hW hμ hI hR hB

/- English proof (translation)
The claim follows from `linkGLOBAL7_tied3 Fm Cabs CH C0 C5 hCabs hCH hC0 h2b h2v (fun D => theorem_three_under_scale_of_general (explicit_bound_all_scales_of_formal_degree hHC hWK hLK) D) (fun D => dsigExT_of D hE) hWK hLK hZa hZb tCV hW hμ hI hR hB`.
-/
theorem linkGLOBAL7_tied3src (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)
    (h2b : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂) (h2v : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass)
    (hHC : HCFdegR) (hE : DiscreteSeriesWeylDimension.DiscreteSeriesExists) (hWK : DiscreteSeriesWeylDimension.WeylForK) (hLK : DiscreteSeriesWeylDimension.LowKMultOne)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine)
    (hI : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  linkGLOBAL7_tied3 Fm Cabs CH C0 C5 hCabs hCH hC0 h2b h2v (fun D => theorem_three_under_scale_of_general (explicit_bound_all_scales_of_formal_degree hHC hWK hLK) D)
    (fun D => dsigExT_of D hE) hWK hLK hZa hZb tCV hW hμ hI hR hB

end Formalism.MainNotions.RT

end
