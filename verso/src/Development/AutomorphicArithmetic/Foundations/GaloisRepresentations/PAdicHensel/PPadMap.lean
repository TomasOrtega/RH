import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatInt

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

/- English proof (translation)
Introduce `F _ _ w`. Use `set u : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.under (𝓞 ℚ) w with hu`. Use `set v : HeightOneSpectrum ℤ := GlobalTheory.NormLevelCompare.primeCorr.symm u with hv`. Establish `hw : HeightOneSpectrum.under (𝓞 ℚ) w = GlobalTheory.NormLevelCompare.primeCorr v`. Rewrite using `[hv, Equiv.apply_symm_apply]`.

Use `haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩`. Set `f₁` to `(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.toRingHom`. Set `f₂` to `(Padic.adicCompletionEquiv (𝓞 ℚ) (Rat.HeightOneSpectrum.primesEquiv v)).toAlgEquiv.toRingEquiv.toRingHom`. Use `⟨v, ((GlobalTheory.LFun.complMap (F := ℚ) (E := F) hw).comp f₂).comp f₁, ?_⟩` and prove the remaining obligations. Introduce `q hq`.

Establish `hgen : Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator u`. Express the relevant statement in the definitionally equal form `(Rat.HeightOneSpectrum.primesEquiv v).1 = (Rat.HeightOneSpectrum.primesEquiv u).1`. Simplify using `[hv, GlobalTheory.NormLevelCompare.primeCorr]`. Use `set p := Rat.HeightOneSpectrum.natGenerator u with hp`. Establish `hdvd : (p : ℤ) ∣ q`.

Establish `hfix : Rat.IsIntegralClosure.intEquiv ℤ q = q`. Simplify using `using map_intCast (Rat.IsIntegralClosure.intEquiv ℤ) q`. Establish `hmem : q ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ)`. Rewrite using `[← hfix]`. Conclude with `(Ideal.apply_mem_of_equiv_iff).2 hq`.

Rewrite `hmem` using `[← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, hgen]`. Conclude with `hmem`. Establish `hpu : ((p : ℕ) : 𝓞 ℚ) ∈ u.asIdeal`. Establish `h` using `(Rat.HeightOneSpectrum.natGenerator_dvd_iff u (n := p)).1 dvd_rfl`. Rewrite `h` using `[← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) p]`.

Conclude with `(Ideal.apply_mem_of_equiv_iff).1 h`. Establish `hpw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal`. Establish `h : algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ w.asIdeal` using `hpu`. Simplify using `using h`. Take `⟨k, rfl⟩` from `hdvd`.

Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ (by exact_mod_cast hpw)`.
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
