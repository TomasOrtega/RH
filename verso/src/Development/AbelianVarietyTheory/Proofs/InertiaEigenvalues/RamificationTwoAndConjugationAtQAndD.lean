import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ImageMemOfGens
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.PrimesQD

open Formalism.FrobeniusOrbits Formalism.MainNotions.EmbeddingTypeJumps
open scoped Pointwise

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Establish `hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) v.asIdeal`. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]`. Simplify `hv` using `[placesOver]`.

Conclude with `hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) hle`.
-/
theorem liesOver_span {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) v.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa [placesOver] using hv
  exact hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) hle

/- English proof (translation)
Establish `hgal` using `D.host.hostE_isGalois`. Establish `: IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E)` using `IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E`. Use `liesOver_span hl hv` as an intermediate fact. Use `v.isPrime` as an intermediate fact. Establish `: Fact l.Prime` using `⟨hl⟩`.

Establish `hp : (Ideal.span {(l : ℤ)}).IsPrime` using `(PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime`. Establish `hIn : Nat.card (v.asIdeal.inertia Gal(D.host.E/ℚ)) = 2`. Establish `e1 : (v.asIdeal.inertia Gal(D.host.E/ℚ)) ≃ (({1, g} : Set (D.R.GG)))` using `Equiv.subtypeEquiv (D.host.gal).toEquiv (fun σ => by`. Rewrite using `[show σ ∈ v.asIdeal.inertia Gal(D.host.E/ℚ) ↔ σ ∈ ineG D v from Iff.rfl, hin σ]`. Simplify using `[Formalism.HC.HostRaw.galE])`.

Rewrite using `[Nat.card_congr e1, Nat.card_coe_set_eq, Set.ncard_pair hg.symm]`. Rewrite using `[← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal Gal(D.host.E/ℚ), ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (Ideal.span {(l : ℤ)}) v.asIdeal, hIn]`.
-/
theorem ramIdx_eq_two (D : D7) {l : ℕ} (hl : l.Prime) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∈ placesOver D.host.E l) (g : D.R.GG) (hg : g ≠ 1)
    (hin : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ∈ ineG D v ↔
      (D.host.galE σ = 1 ∨ D.host.galE σ = g)) :
    v.asIdeal.ramificationIdx ℤ = 2 := by
  have hgal := D.host.hostE_isGalois
  have : IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  have := liesOver_span hl hv
  have := v.isPrime
  have : Fact l.Prime := ⟨hl⟩
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hIn : Nat.card (v.asIdeal.inertia Gal(D.host.E/ℚ)) = 2 := by
    have e1 : (v.asIdeal.inertia Gal(D.host.E/ℚ)) ≃ (({1, g} : Set (D.R.GG))) :=
      Equiv.subtypeEquiv (D.host.gal).toEquiv (fun σ => by
        rw [show σ ∈ v.asIdeal.inertia Gal(D.host.E/ℚ) ↔ σ ∈ ineG D v from Iff.rfl, hin σ]
        simp [Formalism.HC.HostRaw.galE])
    rw [Nat.card_congr e1, Nat.card_coe_set_eq, Set.ncard_pair hg.symm]
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal Gal(D.host.E/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (Ideal.span {(l : ℤ)}) v.asIdeal, hIn]

/- English proof (translation)
The claim follows from `D.host.sqd_sq`.
-/
theorem bE_sq (D : D7) : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq

/- English proof (translation)
Use `set z := φ (D.host.sqd)`. Use `set s : ℂ := (Real.sqrt D.host.d : ℂ)`. Establish `hd0 : (0 : ℝ) < Real.sqrt D.host.d` using `Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)`. Establish `hs : s ^ 2 = (D.host.d : ℂ)`. Simplify using `only [s, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`.

Simplify using the standard rewrite rules. Establish `hz : z ^ 2 = -(D.host.d : ℂ)`. Simplify using `only [z, ← map_pow, bE_sq, map_neg, map_natCast]`. Establish `hs0 : Complex.I * s ≠ 0` using `mul_ne_zero Complex.I_ne_zero (by simpa [s] using hd0.ne')`. Establish `hfac : (z - Complex.I * s) * (z + Complex.I * s) = 0`.

Establish `: (z - Complex.I * s) * (z + Complex.I * s) = z ^ 2 - Complex.I ^ 2 * s ^ 2` using `by ring`. Rewrite using `[this, hz, hs, Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce `h1 h2`.

Apply `hs0` to reduce the goal to its premises. Establish `: (2 : ℂ) * (Complex.I * s) = 0` using `by linear_combination -(h1 + h2)`. Simplify using `using this`. Introduce `h`. Break down `mul_eq_zero.1 hfac with h1 | h1` into its components or cases.

Conclude with `absurd (sub_eq_zero.1 h1) h`. Take the linear combination `-h1`.
-/
theorem neg_mem_iff (D : D7) (φ : D.host.E →+* ℂ) :
    (-φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ)) ↔
      ¬ φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := by
  set z := φ (D.host.sqd)
  set s : ℂ := (Real.sqrt D.host.d : ℂ)
  have hd0 : (0 : ℝ) < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hs : s ^ 2 = (D.host.d : ℂ) := by
    simp only [s, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hz : z ^ 2 = -(D.host.d : ℂ) := by
    simp only [z, ← map_pow, bE_sq, map_neg, map_natCast]
  have hs0 : Complex.I * s ≠ 0 := mul_ne_zero Complex.I_ne_zero
    (by simpa [s] using hd0.ne')
  have hfac : (z - Complex.I * s) * (z + Complex.I * s) = 0 := by
    have : (z - Complex.I * s) * (z + Complex.I * s) = z ^ 2 - Complex.I ^ 2 * s ^ 2 := by ring
    rw [this, hz, hs, Complex.I_sq]; ring
  constructor
  · intro h1 h2
    apply hs0
    have : (2 : ℂ) * (Complex.I * s) = 0 := by linear_combination -(h1 + h2)
    simpa using this
  · intro h
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) h
    · linear_combination -h1

/- English proof (translation)
Introduce `D`. Establish `hH` using `D.host.hyp`. Take `⟨hq, hd, hq8, hd16, -⟩` from `hH`. Introduce `l hl`. Establish `hl' : l = D.host.q ∨ l = D.host.d` using `by simpa using hl`.

Apply the tactic sequence `have hlp : l.Prime := by rcases hl' with rfl | rfl <;> assumption`. Apply the tactic sequence `refine ⟨by rcases hl' with rfl | rfl <;> omega, ?_⟩`. Introduce `v hv`. Establish `hlo` using `liesOver_span hlp hv`. Use `v.isPrime` as an intermediate fact.

Establish `hmemI : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ∈ ineG D v ↔ ∀ x : 𝓞 D.host.E, σ • x - x ∈ v.asIdeal` using `fun σ => AddSubgroup.mem_inertia`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Break down `hl' with rfl | rfl` into its components or cases. Take `⟨g, hg, hin⟩` from `UpperTheory.Small.inertia_q D.host`. Conclude with `ramIdx_eq_two D hlp v hv g hg fun σ => (hmemI σ).trans (hin v.asIdeal σ)`.

Use `ramIdx_eq_two D hlp v hv D.R.iod (fun h => ?_) fun σ => (hmemI σ).trans (D.host.der.inertia_d v.asIdeal σ)` and prove the remaining obligations. Establish `h'` using `congrArg (fun g : D.R.GG => g.1.2) h`. Conclude with `absurd (show (-1 : ℤˣ) = 1 from h') (by decide)`. Introduce `h`. Use `D.host.der.decompConj l hlp ?_ v.asIdeal (MulAction.mem_stabilizer_iff.mpr h)` and prove the remaining obligations.

Break down `hl' with rfl | rfl` into its components or cases. Conclude with `(dvd_mul_left _ _).mul_right _`. Conclude with `dvd_mul_left _ _`. Introduce and unpack `rfl σ hσ φ`. Establish `hb : σ (D.host.sqd) = D.host.sqd` using `(D.host.galE_mem_Psi_iff σ).1 (D.host.der.decomp_typeI _ hlp (dvd_mul_left _ _) v.asIdeal σ hσ)`.

Simplify using `only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = D.host.sqd from hb]`. Introduce and unpack `rfl σ hσ hσ1 φ`. Establish `h2` using `(D.host.der.inertia_d v.asIdeal σ).1 ((hmemI σ).1 hσ)`. Establish `hg : D.host.galE σ = D.R.iod` using `h2.resolve_left fun h => hσ1 ((D.host.galE_eq_one_iff σ).1 h)`.

Establish `hb : σ (D.host.sqd) = -D.host.sqd`. Rewrite using `[D.host.galE_bE σ, hg, show D.R.iod.1.2 = -1 from rfl]`. Simplify using the standard rewrite rules. Simplify using `only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = -D.host.sqd from hb, map_neg]`.

Conclude with `neg_mem_iff D φ`.
-/
theorem ramification_two_and_conjugation_at_q_and_d : ∀ D : D7, EmbeddingTypeJumps.Conclusion1 D := by
  intro D
  have hH := D.host.hyp
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH
  intro l hl
  have hl' : l = D.host.q ∨ l = D.host.d := by simpa using hl
  have hlp : l.Prime := by rcases hl' with rfl | rfl <;> assumption
  refine ⟨by rcases hl' with rfl | rfl <;> omega, ?_⟩
  intro v hv
  have hlo := liesOver_span hlp hv
  have := v.isPrime
  have hmemI : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, σ ∈ ineG D v ↔ ∀ x : 𝓞 D.host.E, σ • x - x ∈ v.asIdeal :=
    fun σ => AddSubgroup.mem_inertia
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rcases hl' with rfl | rfl
    · obtain ⟨g, hg, hin⟩ := UpperTheory.Small.inertia_q D.host
      exact ramIdx_eq_two D hlp v hv g hg fun σ => (hmemI σ).trans (hin v.asIdeal σ)
    · refine ramIdx_eq_two D hlp v hv D.R.iod (fun h => ?_)
        fun σ => (hmemI σ).trans (D.host.der.inertia_d v.asIdeal σ)
      have h' := congrArg (fun g : D.R.GG => g.1.2) h
      exact absurd (show (-1 : ℤˣ) = 1 from h') (by decide)
  ·
    intro h
    refine D.host.der.decompConj l hlp ?_ v.asIdeal (MulAction.mem_stabilizer_iff.mpr h)
    rcases hl' with rfl | rfl
    · exact (dvd_mul_left _ _).mul_right _
    · exact dvd_mul_left _ _
  ·
    rintro rfl σ hσ φ
    have hb : σ (D.host.sqd) = D.host.sqd :=
      (D.host.galE_mem_Psi_iff σ).1 (D.host.der.decomp_typeI _ hlp (dvd_mul_left _ _) v.asIdeal σ hσ)
    simp only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]
    rw [show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = D.host.sqd from hb]
  ·
    rintro rfl σ hσ hσ1 φ
    have h2 := (D.host.der.inertia_d v.asIdeal σ).1 ((hmemI σ).1 hσ)
    have hg : D.host.galE σ = D.R.iod := h2.resolve_left fun h => hσ1 ((D.host.galE_eq_one_iff σ).1 h)
    have hb : σ (D.host.sqd) = -D.host.sqd := by
      rw [D.host.galE_bE σ, hg, show D.R.iod.1.2 = -1 from rfl]
      simp
    simp only [InPhi, Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.coe_comp, Function.comp_apply]
    rw [show ((σ : D.host.E →+* D.host.E) (D.host.sqd)) = -D.host.sqd from hb,
      map_neg]
    exact neg_mem_iff D φ

end GlobalTheory.PrimesQD
