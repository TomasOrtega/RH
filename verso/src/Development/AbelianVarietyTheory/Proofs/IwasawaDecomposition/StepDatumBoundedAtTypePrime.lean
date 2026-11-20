import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnfoldingIsGoodCyclotomicInvariantReferenceLatti

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.BddG

open GlobalTheory.LastSteps GlobalTheory.ColPeriod

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Simplify by unfolding definitions. Apply the first step, then apply the next step to every resulting obligation. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Simplify by unfolding definitions. Apply the first step, then apply the next step to every resulting obligation. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem homBdd_of_good {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
    {n' c' n c m : ℕ} (hc' : c' ≤ m) (hc : c + 1 ≤ m) {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ) :
    HomBdd P m Φ := by
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  refine ⟨fun x hx => (intHom_iff _).2 fun s l => ?_, fun x y hy => ?_⟩
  · have h1 := mem_homS_sclLat.1 (h.1 x hx) l s
    have hs := s.2
    have e : 0 ≤ (m : ℤ) - (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
      unfold LocE.scE
      dsimp only
      split_ifs <;> omega
    convert h1.mul (intAt_zpow e) using 1
    rw [mul_assoc, ← zpow_add₀ hq, add_sub_cancel, zpow_natCast, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  · have h1 : ((qOf P : E) ^ ((m : ℤ) - 1)) • y ∈
        homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1) := by
      refine mem_homS_sclLat.2 fun l s => ?_
      have hl := l.2
      have e : 0 ≤ (m : ℤ) - 1 + (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
        unfold LocE.scE
        dsimp only
        split_ifs <;> omega
      convert ((intHom_iff _).1 hy s l).mul (intAt_zpow e) using 1
      rw [zpow_add₀ hq, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 := h.2.1 x _ h1
    rwa [smul_smul, zpow_sub_one₀ hq, mul_comm _ (qOf P : E)⁻¹, mul_inv_cancel_left₀ hq, zpow_natCast] at h2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem good_omPhi_two {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    {hal : AutY X R i} {h : AutY X R (i + 1)} (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    Good P.1 (homS (LocE.lamY P.1 (qOf P.1) (R.N i) (cOf R i) fun i => i + 1)
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1)) (omPhi Ch sel mu cst i P hal h) := by
  have h1 : R.k ≤ R.N i := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (i + 1) := Nat.le_add_right _ _
  have h3 : R.r + (i + 1 - 1) * R.t = R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    rw [Nat.add_sub_cancel, mul_add i]
    omega
  have h4 : R.N i + cOf R i ≤ R.N (i + 1) + cOf R (i + 1) := by
    unfold Ranks.N cOf
    rw [add_mul i]
    omega
  unfold lamYat at ha hb
  rw [if_pos hP] at ha hb
  refine good_om_two ?_ _ _ _ ha hb
  unfold PhiAt
  rw [if_pos hP]
  split_ifs
  · exact good_PhiGS _ _ h1 h2 h3 h4
  · exact good_PhiG _ _ h1 h2 h3 h4

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem omPhi_bdd_type {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    (hal : AutY X R i) (h : AutY X R (i + 1)) (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧
      ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) * Loc.chArg x) := by
  have hg := good_omPhi_two Ch sel mu cst i P hi hP ha hb
  refine ⟨homBdd_of_good (by unfold cOf; omega) (by unfold cOf; omega) hg, fun x hx => ?_⟩
  have := GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (chArg_int (hg.1 x hx))
  rwa [mul_neg, neg_neg] at this

end GlobalTheory.Mem.Col2.BddG

end
