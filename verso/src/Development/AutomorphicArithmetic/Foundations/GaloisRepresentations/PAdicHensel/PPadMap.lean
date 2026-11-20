import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatInt

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.G1.pPadMap :
    PadMap := by
  intro F _ _ w
  set u : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.under (𝓞 ℚ) w with hu
  set v : HeightOneSpectrum ℤ := GlobalTheory.NormLevelCompare.primeCorr.symm u with hv
  have hw : HeightOneSpectrum.under (𝓞 ℚ) w = GlobalTheory.NormLevelCompare.primeCorr v := by
    rw [hv, Equiv.apply_symm_apply]
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let f₁ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.toRingHom
  let f₂ := (Padic.adicCompletionEquiv (𝓞 ℚ)
    (Rat.HeightOneSpectrum.primesEquiv v)).toAlgEquiv.toRingEquiv.toRingHom
  refine ⟨v, ((GlobalTheory.LFun.complMap (F := ℚ) (E := F) hw).comp f₂).comp f₁, ?_⟩
  intro q hq
  have hgen : Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator u := by
    change (Rat.HeightOneSpectrum.primesEquiv v).1 = (Rat.HeightOneSpectrum.primesEquiv u).1
    simp [hv, GlobalTheory.NormLevelCompare.primeCorr]
  set p := Rat.HeightOneSpectrum.natGenerator u with hp
  have hdvd : (p : ℤ) ∣ q := by
    have hfix : Rat.IsIntegralClosure.intEquiv ℤ q = q := by
      simpa using map_intCast (Rat.IsIntegralClosure.intEquiv ℤ) q
    have hmem : q ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) := by
      rw [← hfix]
      exact (Ideal.apply_mem_of_equiv_iff).2 hq
    rw [← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, hgen] at hmem
    exact hmem
  have hpu : ((p : ℕ) : 𝓞 ℚ) ∈ u.asIdeal := by
    have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff u (n := p)).1 dvd_rfl
    rw [← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) p] at h
    exact (Ideal.apply_mem_of_equiv_iff).1 h
  have hpw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
    have h : algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ w.asIdeal := hpu
    simpa using h
  obtain ⟨k, rfl⟩ := hdvd
  push_cast
  exact Ideal.mul_mem_right _ _ (by exact_mod_cast hpw)
