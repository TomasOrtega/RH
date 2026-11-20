import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver

noncomputable section

open scoped TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.FrameIntegral

/- English proof (translation)
Establish `hinjEL : Function.Injective (algebraMap (𝓞 E) (𝓞 L))` using `FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L)`. Take `⟨W, -, hWp, hWQ⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) Q ⊥ (by rw [Ideal.comap_bot_of_injective _ hinjEL]; exact bot_le)`. Establish `hWb : W ≠ ⊥`. Introduce `h0`. Apply `hQb` to reduce the goal to its premises.

Rewrite using `[← hWQ, h0, Ideal.comap_bot_of_injective _ hinjEL]`. Establish `hpW : ((p : ℕ) : 𝓞 L) ∈ W`. Establish `: algebraMap (𝓞 E) (𝓞 L) ((p : ℕ) : 𝓞 E) ∈ W`. Rewrite using `[← Ideal.mem_comap, hWQ]`. Conclude with `hpQ'`.

Simplify using `using this`. Take `⟨h1, h2⟩` from `hall ⟨W, hWp, hWb⟩ hpW`. Establish `: W.LiesOver Q` using `⟨hWQ.symm⟩`. Establish `h1' : W.ramificationIdx ℤ = 1` using `h1`. Establish `h2' : W.inertiaDeg ℤ = 1` using `h2`.

Rewrite `h1'` using `[Ideal.ramificationIdx_tower (R := ℤ) Q W]`. Rewrite `h2'` using `[Ideal.inertiaDeg_tower (R := ℤ) Q W]`. Conclude with `⟨(mul_eq_one.mp h1').1, (mul_eq_one.mp h2').1⟩`.
-/
theorem ef_one_of_split (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] (p : ℕ)
    (hall : ∀ W : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1)
    (Q : Ideal (𝓞 E)) (hQp : Q.IsPrime) (hQb : Q ≠ ⊥) (hpQ' : ((p : ℕ) : 𝓞 E) ∈ Q) :
    Q.ramificationIdx ℤ = 1 ∧ Q.inertiaDeg ℤ = 1 := by
  have hinjEL : Function.Injective (algebraMap (𝓞 E) (𝓞 L)) :=
    FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L)
  obtain ⟨W, -, hWp, hWQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) Q ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinjEL]; exact bot_le)
  have hWb : W ≠ ⊥ := by
    intro h0; apply hQb; rw [← hWQ, h0, Ideal.comap_bot_of_injective _ hinjEL]
  have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
    have : algebraMap (𝓞 E) (𝓞 L) ((p : ℕ) : 𝓞 E) ∈ W := by
      rw [← Ideal.mem_comap, hWQ]; exact hpQ'
    simpa using this
  obtain ⟨h1, h2⟩ := hall ⟨W, hWp, hWb⟩ hpW
  have : W.LiesOver Q := ⟨hWQ.symm⟩
  have h1' : W.ramificationIdx ℤ = 1 := h1
  have h2' : W.inertiaDeg ℤ = 1 := h2
  rw [Ideal.ramificationIdx_tower (R := ℤ) Q W] at h1'
  rw [Ideal.inertiaDeg_tower (R := ℤ) Q W] at h2'
  exact ⟨(mul_eq_one.mp h1').1, (mul_eq_one.mp h2').1⟩

/- English proof (translation)
Establish `key : ∀ I : Ideal (𝓞 K), I ∣ differentIdeal ℤ (𝓞 K) → ¬ p ∣ Ideal.absNorm I`. Introduce `I`. Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁`. Introduce `h`.

Conclude with `absurd (zero_dvd_iff.1 h) (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))`. Consider the case `h₂ x hx`. Introduce `_`. Rewrite using `[Ideal.isUnit_iff.1 hx, Ideal.absNorm_top]`. Conclude with `hp.not_dvd_one`.

Consider the case `h₃ a P ha hP ih`. Introduce `hdvd hpd`. Rewrite `hpd` using `[map_mul]`. Break down `(Nat.Prime.dvd_mul hp).1 hpd with h | h` into its components or cases. Establish `hPp : P.IsPrime` using `Ideal.isPrime_of_prime hP`.

Establish `hPb : P ≠ ⊥` using `hP.ne_zero`. Establish `hPm : P.IsMaximal` using `Ideal.IsPrime.isMaximal hPp hPb`. Establish `hfin : Finite (𝓞 K ⧸ P)` using `Ideal.finiteQuotientOfFreeOfNeBot P hPb`. Establish `hcard : Ideal.absNorm P = Nat.card (𝓞 K ⧸ P)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Rewrite `h` using `[hcard]`. Establish `: Fact p.Prime` using `⟨hp⟩`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' p h`. Set `_ : Field (𝓞 K ⧸ P)` to `Ideal.Quotient.field P`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hx` using `[addOrderOf_zero]`. Conclude with `hp.one_lt.ne hx`. Establish `hpx : (p : 𝓞 K ⧸ P) * x = 0`. Rewrite using `[← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]`.

Establish `hp0 : (p : 𝓞 K ⧸ P) = 0` using `(mul_eq_zero.1 hpx).resolve_right hx0`. Establish `hpP : ((p : ℕ) : 𝓞 K) ∈ P`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `hp0`. Establish `he` using `hram P hPp hPb hpP`.

Establish `hun : Algebra.IsUnramifiedAt ℤ P` using `Ideal.ramificationIdx_eq_one_iff.mp he`. Conclude with `(not_dvd_differentIdeal_iff.2 hun) (dvd_of_mul_right_dvd hdvd)`. Conclude with `ih (dvd_of_mul_left_dvd hdvd) h`. Conclude with `key _ dvd_rfl`.
-/
theorem not_dvd_absNorm_different (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (hram : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1) :
    ¬ p ∣ Ideal.absNorm (differentIdeal ℤ (𝓞 K)) := by
  have key : ∀ I : Ideal (𝓞 K), I ∣ differentIdeal ℤ (𝓞 K) → ¬ p ∣ Ideal.absNorm I := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro h
      exact absurd (zero_dvd_iff.1 h) (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))
    | h₂ x hx =>
      intro _
      rw [Ideal.isUnit_iff.1 hx, Ideal.absNorm_top]
      exact hp.not_dvd_one
    | h₃ a P ha hP ih =>
      intro hdvd hpd
      rw [map_mul] at hpd
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
      · have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
        have hPb : P ≠ ⊥ := hP.ne_zero
        have hPm : P.IsMaximal := Ideal.IsPrime.isMaximal hPp hPb
        have hfin : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPb
        have hcard : Ideal.absNorm P = Nat.card (𝓞 K ⧸ P) := by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
        rw [hcard] at h
        have : Fact p.Prime := ⟨hp⟩
        obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
        let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
        have hx0 : x ≠ 0 := by
          rintro rfl; rw [addOrderOf_zero] at hx; exact hp.one_lt.ne hx
        have hpx : (p : 𝓞 K ⧸ P) * x = 0 := by
          rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
        have hp0 : (p : 𝓞 K ⧸ P) = 0 := (mul_eq_zero.1 hpx).resolve_right hx0
        have hpP : ((p : ℕ) : 𝓞 K) ∈ P := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hp0
        have he := hram P hPp hPb hpP
        have hun : Algebra.IsUnramifiedAt ℤ P := Ideal.ramificationIdx_eq_one_iff.mp he
        exact (not_dvd_differentIdeal_iff.2 hun) (dvd_of_mul_right_dvd hdvd)
      · exact ih (dvd_of_mul_left_dvd hdvd) h
  exact key _ dvd_rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Establish `hall : ∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal → W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1` using `fun W hW => (GlobalTheory.unramified_degree_one_of_ncard_placesOver D.host.E _ (D.host.g_prime i) (D.nd.g_split i) W hW).2`. Use `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (D.host.g_prime i)).2 ?_)` and prove the remaining obligations. Use `not_dvd_absNorm_different D.host.F _ (D.host.g_prime i) fun P hPp hPb hpP => ?_` and prove the remaining obligations. Conclude with `(ef_one_of_split D.host.F D.host.E _ hall P hPp hPb hpP).1`.
-/
theorem coprime_gi (i : Fin 2) : Nat.Coprime (Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F))) (D.host.g i) := by
  have hall : ∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1 := fun W hW =>
    (GlobalTheory.unramified_degree_one_of_ncard_placesOver D.host.E _ (D.host.g_prime i) (D.nd.g_split i) W hW).2
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (D.host.g_prime i)).2 ?_)
  refine not_dvd_absNorm_different D.host.F _ (D.host.g_prime i) fun P hPp hPb hpP => ?_
  exact (ef_one_of_split D.host.F D.host.E _ hall P hPp hPb hpP).1

end GlobalTheory.FrameIntegral
