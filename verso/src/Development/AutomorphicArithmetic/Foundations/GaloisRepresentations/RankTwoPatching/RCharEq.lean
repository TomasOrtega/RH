import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioWOfHasSat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RatioWOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Adelise
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.QbarInst

attribute [local instance] UpperTheory.V.QbarInst.charZero UpperTheory.V.QbarInst.torsionFree UpperTheory.V.QbarInst.algClosure

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd

noncomputable section

namespace UpperTheory.V.Br.CharacterEquality

/- English proof (translation)
Introduce `v w h` and use `HeightOneSpectrum.ext (by rw [(places v).2.1, (places w).2.1, show normV v = normV w from h])`.
-/
private theorem normV_inj : Function.Injective fun w : Pl ℚ => normV w := fun v w h =>
  HeightOneSpectrum.ext (by rw [(places v).2.1, (places w).2.1, show normV v = normV w from h])

/- English proof (translation)
Establish `h0 : Prime ((p : ℕ) : 𝓞 ℚ)`. Establish `h : Prime ((p : ℕ) : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ)` using `by simp`. Rewrite using `[e]`. Conclude with `(MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h`.

Set `w : Pl ℚ` to `⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0, by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩`. Use `⟨w, (places w).2.2.1.symm.trans ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p`. Rewrite using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank]`. Simplify using the standard rewrite rules.
-/
private theorem normV_surj {p : ℕ} (hp : p.Prime) : ∃ w : Pl ℚ, normV w = p := by
  have h0 : Prime ((p : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  let w : Pl ℚ := ⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩
  refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
  change Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp

/- English proof (translation)
Rewrite `h` using `[Matrix.charpoly_fin_two]`. Establish `h0` using `congrArg (Polynomial.coeff · 0) h`. Establish `h1` using `congrArg (Polynomial.coeff · 1) h`. Simplify using `at h0 h1`. Conclude with `⟨h1, h0⟩`.
-/
private theorem tr_det {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.trace = a ∧ ι A.det = d := by
  rw [Matrix.charpoly_fin_two] at h
  have h0 := congrArg (Polynomial.coeff · 0) h
  have h1 := congrArg (Polynomial.coeff · 1) h
  simp at h0 h1
  exact ⟨h1, h0⟩

/- English proof (translation)
Simplify using `[Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem two_det {K : Type} [CommRing K] (A : Matrix (Fin 2) (Fin 2) K) :
    2 * A.det = A.trace ^ 2 - (A * A).trace := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

end UpperTheory.V.Br.CharacterEquality
