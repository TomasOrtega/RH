import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj

noncomputable section

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo GlobalTheory.CongL

namespace UpperTheory.Gal.G1

def CjMem : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (w : HeightOneSpectrum (𝓞 E)) (y : 𝓞 E),
  y ∈ (CertificateRingHomMap.cj w).asIdeal ↔ A.bar y ∈ w.asIdeal

def DiscInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (y : 𝓞 E),
  (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} →
  ∃ a b : ℤ, ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y = (a : 𝓞 E) + (b : 𝓞 E) * A.ω

def BarAdj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (y : 𝓞 E),
  (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} → ((A.bar y : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)}

def KeyK : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (q : ℕ), q.Prime →
  ¬ (q : ℤ) ∣ A.tr ^ 2 - 4 * A.nm → ∀ (r : ℤ) (u w : HeightOneSpectrum (𝓞 E)), (q : 𝓞 E) ∈ u.asIdeal → (q : 𝓞 E) ∈ w.asIdeal →
  A.ω - (r : 𝓞 E) ∈ u.asIdeal → A.ω - (r : 𝓞 E) ∈ w.asIdeal →
  ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} → (y ∈ u.asIdeal ↔ y ∈ w.asIdeal)

/- English proof (translation)
Establish `hf' : (f : E) ≠ 0` using `by exact_mod_cast hf`. Prove the components needed by the constructor for the conclusion. Establish `e : (A.ω : E) = ((A.tr : E) + (f : E) * x) / 2` using `by rw [← h]; ring`. Rewrite using `[e]`. Conclude with `div_mem (add_mem (intCast_mem _ _) (mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ x))) (ofNat_mem _ 2)`.

Establish `e : x = (2 * (A.ω : E) - (A.tr : E)) / (f : E)` using `by rw [h]; field_simp`. Rewrite using `[e]`. Conclude with `div_mem (sub_mem (mul_mem (ofNat_mem _ 2) (IntermediateField.mem_adjoin_simple_self ℚ _)) (intCast_mem _ _)) (SubfieldClass.ratCast_mem _ _)`.
-/
theorem gen_of {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (x : E) (f : ℚ) (hf : f ≠ 0)
    (h : 2 * (A.ω : E) - (A.tr : E) = (f : E) * x) : Pl.Gen A x := by
  have hf' : (f : E) ≠ 0 := by exact_mod_cast hf
  constructor
  · have e : (A.ω : E) = ((A.tr : E) + (f : E) * x) / 2 := by rw [← h]; ring
    rw [e]
    exact div_mem (add_mem (intCast_mem _ _) (mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.mem_adjoin_simple_self ℚ x)))
      (ofNat_mem _ 2)
  · have e : x = (2 * (A.ω : E) - (A.tr : E)) / (f : E) := by rw [h]; field_simp
    rw [e]
    exact div_mem (sub_mem (mul_mem (ofNat_mem _ 2) (IntermediateField.mem_adjoin_simple_self ℚ _)) (intCast_mem _ _))
      (SubfieldClass.ratCast_mem _ _)

/- English proof (translation)
Introduce `E _ _ _ l _ n d hn hd x hx Q hQ`. Take `⟨τ₀⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Take `⟨A, -, ⟨f, hf, hfx⟩, hs, hg⟩` from `h2 E d hd.1.1 x hx τ₀ Q hQ`. Take `⟨e, he, hc⟩` from `h5 E A`. Establish `hgood : ∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → ¬ q ∣ e → A.Good q` using `fun q hq' hq hqe => ⟨hs q hq, hc q ((Nat.Prime.coprime_iff_not_dvd hq'.out).2 hqe).symm⟩`.

Use `⟨A, hd.1.1, gen_of A x f hf hfx, hg, ⟨e, he, hgood⟩, fun X => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, hb, hsq⟩` from `h1 d hd.1.1 (max e (X.sup id))`. Establish `hpX : p ∉ X` using `fun h => by`. Establish `: p ≤ X.sup id` using `Finset.le_sup (f := id) h`. Use linear arithmetic over natural numbers and integers.

Take `⟨S⟩` from `h3 E A n p hn.pos (hgood p hsq fun h => by have := Nat.le_of_dvd he h; omega)`. Conclude with `⟨p, hp, S, hpX, h4 E hd.2.2.1 A n p S hn⟩`.
-/
theorem datEx_of (h1 : AuxiliaryInertOddPrime) (h2 : ArithK) (h3 : SetupEx) (h4 : ScOf) (h5 : PerfCof) : Pl.DatEx := by
  intro E _ _ _ l _ n d hn hd x hx Q hQ
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨A, -, ⟨f, hf, hfx⟩, hs, hg⟩ := h2 E d hd.1.1 x hx τ₀ Q hQ
  obtain ⟨e, he, hc⟩ := h5 E A
  have hgood : ∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → ¬ q ∣ e → A.Good q := fun q hq' hq hqe =>
    ⟨hs q hq, hc q ((Nat.Prime.coprime_iff_not_dvd hq'.out).2 hqe).symm⟩
  refine ⟨A, hd.1.1, gen_of A x f hf hfx, hg, ⟨e, he, hgood⟩, fun X => ?_⟩
  obtain ⟨p, hp, hb, hsq⟩ := h1 d hd.1.1 (max e (X.sup id))
  have hpX : p ∉ X := fun h => by
    have : p ≤ X.sup id := Finset.le_sup (f := id) h
    omega
  obtain ⟨S⟩ := h3 E A n p hn.pos (hgood p hsq fun h => by have := Nat.le_of_dvd he h; omega)
  exact ⟨p, hp, S, hpX, h4 E hd.2.2.1 A n p S hn⟩

end UpperTheory.Gal.G1
