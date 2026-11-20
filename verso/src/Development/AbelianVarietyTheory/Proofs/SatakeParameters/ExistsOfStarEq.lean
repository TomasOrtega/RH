import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDivsOfMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Formalism.L2.Host (HChar atFin upF aboveF IsUnitAt ordF)
open GlobalTheory.CharVal (valuation_conjP conjP_conjP')

namespace GlobalTheory.NormOneUnit

section Local

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Apply `h (atFin P y)` to reduce the goal to its premises. Use `show Valued.v ((algebraMap E (P.adicCompletion E)) (y : E)) = 1`. Rewrite using `[show (algebraMap E (P.adicCompletion E)) (y : E) = ((y : E) : P.adicCompletion E) from rfl, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]`.
-/
theorem locK_unr {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt P) {y : Eˣ} (hy : P.valuation E (y : E) = 1) :
    χ.locK P y = 1 := by
  apply h (atFin P y)
  show Valued.v ((algebraMap E (P.adicCompletion E)) (y : E)) = 1
  rw [show (algebraMap E (P.adicCompletion E)) (y : E) = ((y : E) : P.adicCompletion E) from rfl,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]

/- English proof (translation)
Establish `hc : ∀ a : E, Valued.v ((algebraMap E (P.adicCompletion E)) a) = P.valuation E a` using `fun a => IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) P a`. Establish `hk1 : P.valuation E (k : E) = 1`. Establish `e : (k : E) = ((k : E) - y) + y` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_right _ (by rw [hy]; exact hk), hy]`. Establish `key : χ.locK P (k * y⁻¹) = 1`.

Apply `h (atFin P (k * y⁻¹))` to reduce the goal to its premises. Use `show Valued.v ((algebraMap E (P.adicCompletion E)) ((k * y⁻¹ : Eˣ) : E)) = 1`. Rewrite using `[hc, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hk1, hy, one_mul, inv_one]`. Use `show Valued.v ((algebraMap E (P.adicCompletion E)) ((k * y⁻¹ : Eˣ) : E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))`. Rewrite using `[← map_one (algebraMap E (P.adicCompletion E)), ← map_sub, hc]`.

Establish `e : ((k * y⁻¹ : Eˣ) : E) - 1 = ((k : E) - y) * (y : E)⁻¹`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, _root_.sub_mul, mul_inv_cancel₀ y.ne_zero]`. Rewrite using `[e, map_mul, map_inv₀, hy, inv_one, mul_one]`. Use `(WithZero.lt_mul_exp_iff_le (x := P.valuation E ((k : E) - y)) (y := WithZero.exp (-1)) WithZero.exp_ne_zero).1` as an intermediate fact. Apply `this` to reduce the goal to its premises.

Rewrite using `[← WithZero.exp_add]`. Simplify using `using hk`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem locK_tame {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} (h : χ.TameAt P) {y k : Eˣ} (hy : P.valuation E (y : E) = 1)
    (hk : P.valuation E ((k : E) - y) < 1) : χ.locK P k = χ.locK P y := by
  have hc : ∀ a : E, Valued.v ((algebraMap E (P.adicCompletion E)) a) = P.valuation E a := fun a =>
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) P a
  have hk1 : P.valuation E (k : E) = 1 := by
    have e : (k : E) = ((k : E) - y) + y := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hy]; exact hk), hy]
  have key : χ.locK P (k * y⁻¹) = 1 := by
    apply h (atFin P (k * y⁻¹))
    · show Valued.v ((algebraMap E (P.adicCompletion E)) ((k * y⁻¹ : Eˣ) : E)) = 1
      rw [hc, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hk1, hy, one_mul, inv_one]
    · show Valued.v ((algebraMap E (P.adicCompletion E)) ((k * y⁻¹ : Eˣ) : E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))
      rw [← map_one (algebraMap E (P.adicCompletion E)), ← map_sub, hc]
      have e : ((k * y⁻¹ : Eˣ) : E) - 1 = ((k : E) - y) * (y : E)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, _root_.sub_mul, mul_inv_cancel₀ y.ne_zero]
      rw [e, map_mul, map_inv₀, hy, inv_one, mul_one]
      have := (WithZero.lt_mul_exp_iff_le (x := P.valuation E ((k : E) - y)) (y := WithZero.exp (-1)) WithZero.exp_ne_zero).1
      apply this
      rw [← WithZero.exp_add]
      simpa using hk
  calc χ.locK P k = χ.locK P (k * y⁻¹ * y) := by rw [inv_mul_cancel_right]
    _ = χ.locK P y := by rw [map_mul, key, one_mul]

variable [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E]

omit [NumberField E] [NumberField F] in

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_eq_succ hr`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨a, ha⟩` from `hc`. Apply `ha` to reduce the goal to its premises.

Establish `li : LinearIndependent F ![(1 : E), x]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality.

Use `⟨?_, rfl⟩` and prove the remaining obligations. Simplify using `using hst`. It suffices to derive a contradiction. Establish `htE : algebraMap F E t ≠ 0` using `(map_ne_zero (algebraMap F E)).2 ht`. Apply `hne (-(s / t))` to reduce the goal to its premises.

Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Rewrite using `[map_neg, map_div₀, neg_eq_iff_eq_neg, div_eq_iff htE]`. Take the linear combination `hst`. Establish `hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤` using `li.span_eq_top_of_card_eq_finrank (by simp [hr])`. Establish `ha' : a ∈ Submodule.span F (Set.range ![(1 : E), x])` using `by rw [hspan]; exact Submodule.mem_top`.

Take `⟨c, hcab⟩` from `(Submodule.mem_span_range_iff_exists_fun F).1 ha'`. Rewrite using `[← hcab]`. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one, star_add, star_mul, hF, hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_of_star_eq (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {x : E} (hx : star x = x) : ∃ k : F, algebraMap F E k = x := by
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hr
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hc
  apply ha
  have li : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    · exfalso
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero (algebraMap F E)).2 ht
      apply hne (-(s / t))
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      rw [map_neg, map_div₀, neg_eq_iff_eq_neg, div_eq_iff htE]
      linear_combination hst
  have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank (by simp [hr])
  have ha' : a ∈ Submodule.span F (Set.range ![(1 : E), x]) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hcab⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 ha'
  rw [← hcab]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one,
    star_add, star_mul, hF, hx]
  ring

/- English proof (translation)
Establish `hcoe : ∀ c : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E) = algebraMap F E (c : F)`. Introduce `c`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `hQP`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨hQ1, hQ2⟩` from `hne`. Establish `nle : ∀ {A B : HeightOneSpectrum (𝓞 E)}, A ≠ B → ∃ b ∈ A.asIdeal, b ∉ B.asIdeal`. Introduce `A B hAB`.

Assume the negation of the conclusion as `hc'`. Use `push Not at hc'`. Conclude with `hAB (HeightOneSpectrum.ext (A.isMaximal.eq_of_le B.isPrime.ne_top hc'))`. Take `⟨b1, hb1Q, hb1P⟩` from `nle hQ1`. Take `⟨b2, hb2Q, hb2C⟩` from `nle hQ2`.

Establish `hex : ∃ b ∈ Q.asIdeal, b ∉ P.asIdeal ∧ b ∉ (conjPrime₂ P).asIdeal`. Distinguish the cases in `h1 : b1 ∈ (conjPrime₂ P).asIdeal`. Distinguish the cases in `h2 : b2 ∈ P.asIdeal`. Use `⟨b1 + b2, Q.asIdeal.add_mem hb1Q hb2Q, ?_, ?_⟩` and prove the remaining obligations. Introduce `hs; exact hb1P (by simpa using P.asIdeal.sub_mem hs h2)`.

Introduce `hs; exact hb2C (by simpa using (conjPrime₂ P).asIdeal.sub_mem hs h1)`. Conclude with `⟨b2, hb2Q, h2, hb2C⟩`. Conclude with `⟨b1, hb1Q, hb1P, h1⟩`. Take `⟨b, hbQ, hbP, hbC⟩` from `hex`. Take `⟨k, hk⟩` from `exists_of_star_eq hF hr hc (x := (b : E) * star (b : E)) (by rw [star_mul, star_star, mul_comm])`.

Establish `hbi : IsIntegral ℤ ((b : E) * star (b : E))` using `(RingOfIntegers.isIntegral_coe b).mul ((RingOfIntegers.isIntegral_coe b).map (starRingEnd E).toIntAlgHom)`. Establish `hki : IsIntegral ℤ k` using `(isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 (by rw [← hk] at hbi; exact hbi)`. Set `c : 𝓞 F` to `⟨k, hki⟩`. Establish `hc1 : algebraMap (𝓞 F) (𝓞 E) c = b * cO E b`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[hcoe]`. Conclude with `hk`. Establish `hmem : algebraMap (𝓞 F) (𝓞 E) c ∈ P.asIdeal`. Establish `h0 : c ∈ (Q.under (𝓞 F)).asIdeal` using `by show algebraMap (𝓞 F) (𝓞 E) c ∈ Q.asIdeal`. Rewrite using `[hc1]`.

Conclude with `Q.asIdeal.mul_mem_right _ hbQ`. Rewrite `h0` using `[hQP]`. Conclude with `h0`. Rewrite `hmem` using `[hc1]`. Break down `P.isPrime.mem_or_mem hmem with h | h` into its components or cases.

Conclude with `hbP h`. Conclude with `hbC h`. Introduce and unpack `(rfl | rfl)`. Both sides reduce to the same expression. Apply `HeightOneSpectrum.ext show Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Ideal.comap (cO E) P.asIdeal) = Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) P.asIdeal` to reduce the goal to its premises.

Rewrite using `[Ideal.comap_comap]`. Use `congr 1`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `c`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Use `show star (((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E)) = ((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E)`. Rewrite using `[hcoe, hF]`.
-/
theorem under_eq_iff (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) (P Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = P.under (𝓞 F) ↔ (Q = P ∨ Q = conjPrime₂ P) := by
  have hcoe : ∀ c : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E) = algebraMap F E (c : F) := by
    intro c
    rfl
  constructor
  · intro hQP
    by_contra hne
    push Not at hne
    obtain ⟨hQ1, hQ2⟩ := hne
    have nle : ∀ {A B : HeightOneSpectrum (𝓞 E)}, A ≠ B → ∃ b ∈ A.asIdeal, b ∉ B.asIdeal := by
      intro A B hAB
      by_contra hc'
      push Not at hc'
      exact hAB (HeightOneSpectrum.ext (A.isMaximal.eq_of_le B.isPrime.ne_top hc'))
    obtain ⟨b1, hb1Q, hb1P⟩ := nle hQ1
    obtain ⟨b2, hb2Q, hb2C⟩ := nle hQ2
    have hex : ∃ b ∈ Q.asIdeal, b ∉ P.asIdeal ∧ b ∉ (conjPrime₂ P).asIdeal := by
      by_cases h1 : b1 ∈ (conjPrime₂ P).asIdeal
      · by_cases h2 : b2 ∈ P.asIdeal
        · refine ⟨b1 + b2, Q.asIdeal.add_mem hb1Q hb2Q, ?_, ?_⟩
          · intro hs; exact hb1P (by simpa using P.asIdeal.sub_mem hs h2)
          · intro hs; exact hb2C (by simpa using (conjPrime₂ P).asIdeal.sub_mem hs h1)
        · exact ⟨b2, hb2Q, h2, hb2C⟩
      · exact ⟨b1, hb1Q, hb1P, h1⟩
    obtain ⟨b, hbQ, hbP, hbC⟩ := hex
    obtain ⟨k, hk⟩ := exists_of_star_eq hF hr hc (x := (b : E) * star (b : E))
      (by rw [star_mul, star_star, mul_comm])
    have hbi : IsIntegral ℤ ((b : E) * star (b : E)) :=
      (RingOfIntegers.isIntegral_coe b).mul ((RingOfIntegers.isIntegral_coe b).map (starRingEnd E).toIntAlgHom)
    have hki : IsIntegral ℤ k :=
      (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 (by rw [← hk] at hbi; exact hbi)
    let c : 𝓞 F := ⟨k, hki⟩
    have hc1 : algebraMap (𝓞 F) (𝓞 E) c = b * cO E b := by
      apply RingOfIntegers.ext
      rw [hcoe]
      exact hk
    have hmem : algebraMap (𝓞 F) (𝓞 E) c ∈ P.asIdeal := by
      have h0 : c ∈ (Q.under (𝓞 F)).asIdeal := by
        show algebraMap (𝓞 F) (𝓞 E) c ∈ Q.asIdeal
        rw [hc1]
        exact Q.asIdeal.mul_mem_right _ hbQ
      rw [hQP] at h0
      exact h0
    rw [hc1] at hmem
    rcases P.isPrime.mem_or_mem hmem with h | h
    · exact hbP h
    · exact hbC h
  · rintro (rfl | rfl)
    · rfl
    · apply HeightOneSpectrum.ext
      show Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Ideal.comap (cO E) P.asIdeal) =
        Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) P.asIdeal
      rw [Ideal.comap_comap]
      congr 1
      apply RingHom.ext
      intro c
      apply RingOfIntegers.ext
      show star (((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E)) = ((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E)
      rw [hcoe, hF]

omit [StarRing E] in

/- English proof (translation)
Establish `: Algebra.IsQuadraticExtension F E` using `{ finrank_eq_two' := hr }`. Set `_ : MulSemiringAction Gal(E/F) (𝓞 E)` to `IsIntegralClosure.MulSemiringAction (𝓞 F) F E (𝓞 E)`. Use `IsGaloisGroup.of_isFractionRing Gal(E/F) (𝓞 F) (𝓞 E) F E` as an intermediate fact. Establish `hv0 : (Q.under (𝓞 F)).asIdeal ≠ ⊥` using `(Q.under (𝓞 F)).ne_bot`. Establish `: Q.asIdeal.LiesOver (Q.under (𝓞 F)).asIdeal` using `⟨rfl⟩`.

Establish `he : Q.asIdeal.ramificationIdx (𝓞 F) = 1`. Rewrite using `[← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)).asIdeal Q.asIdeal Gal(E/F)]`. Conclude with `hu _`. Establish `he' : (Q.under (𝓞 F)).asIdeal.ramificationIdx' Q.asIdeal = 1`. Rewrite using `[Ideal.ramificationIdx'_eq_ramificationIdx (p := (Q.under (𝓞 F)).asIdeal) (q := Q.asIdeal) hv0]`.

Conclude with `he`. Establish `hwv` using `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver (K := F) E (Q.under (𝓞 F)) Q x`. Rewrite `hwv` using `[he', pow_one]`. Conclude with `hwv.symm`.
-/
theorem valuation_up (hr : Module.finrank F E = 2)
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal.ramificationIdxIn (𝓞 E) = 1) (Q : HeightOneSpectrum (𝓞 E)) (x : F) :
    Q.valuation E (algebraMap F E x) = (Q.under (𝓞 F)).valuation F x := by
  classical
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hr }
  let _ : MulSemiringAction Gal(E/F) (𝓞 E) := IsIntegralClosure.MulSemiringAction (𝓞 F) F E (𝓞 E)
  have := IsGaloisGroup.of_isFractionRing Gal(E/F) (𝓞 F) (𝓞 E) F E
  have hv0 : (Q.under (𝓞 F)).asIdeal ≠ ⊥ := (Q.under (𝓞 F)).ne_bot
  have : Q.asIdeal.LiesOver (Q.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have he : Q.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)).asIdeal Q.asIdeal Gal(E/F)]
    exact hu _
  have he' : (Q.under (𝓞 F)).asIdeal.ramificationIdx' Q.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := (Q.under (𝓞 F)).asIdeal) (q := Q.asIdeal) hv0]
    exact he
  have hwv := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver (K := F) E (Q.under (𝓞 F)) Q x
  rw [he', pow_one] at hwv
  exact hwv.symm

/- English proof (translation)
Establish `hvc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : E), (conjPrime₂ W).valuation E x = W.valuation E (star x)` using `fun W x => valuation_conjP W x`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, b, hb, hab⟩ : ∃ a ∈ P.asIdeal, ∃ b ∈ (conjPrime₂ P).asIdeal, a + b = 1 := by`. Establish `hne : P.asIdeal ≠ (conjPrime₂ P).asIdeal` using `fun h => hP (HeightOneSpectrum.ext h)`. Establish `htop` using `Ideal.IsMaximal.coprime_of_ne P.isMaximal (conjPrime₂ P).isMaximal hne`. Establish `h1' : (1 : 𝓞 E) ∈ P.asIdeal ⊔ (conjPrime₂ P).asIdeal` using `by rw [htop]; exact Submodule.mem_top`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp h1'`. Conclude with `⟨a, ha, b, hb, hab⟩`. Establish `hs1 : P.valuation E (algebraMap (𝓞 E) E b - 1) < 1`. Establish `: algebraMap (𝓞 E) E b - 1 = algebraMap (𝓞 E) E (-a)`. Rewrite using `[map_neg, ← map_one (algebraMap (𝓞 E) E), ← hab, map_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, HeightOneSpectrum.valuation_lt_one_iff_mem]`. Conclude with `P.asIdeal.neg_mem ha`. Establish `hs2 : P.valuation E (star (algebraMap (𝓞 E) E b)) < 1`. Rewrite using `[← hvc, HeightOneSpectrum.valuation_lt_one_iff_mem]`.

Conclude with `hb`. Establish `hyb : P.valuation E (star (y : E)) = 1` using `by rw [← hvc]; exact h2`. Establish `hk1 : P.valuation E ((algebraMap (𝓞 E) E b * star (y : E) + star (algebraMap (𝓞 E) E b) * (y : E)) - star (y : E)) < 1`. Establish `: (algebraMap (𝓞 E) E b * star (y : E) + star (algebraMap (𝓞 E) E b) * (y : E)) - star (y : E) = (algebraMap (𝓞 E) E b - 1) * star (y : E) + star (algebraMap (𝓞 E) E b) * (y : E)` using `by ring`. Rewrite using `[this]`.

Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[map_mul, hyb, mul_one]`. Conclude with `hs1`. Rewrite using `[map_mul, h1, mul_one]`. Conclude with `hs2`.

Generalize the expression as in `hkdef : algebraMap (𝓞 E) E b * star (y : E) + star (algebraMap (𝓞 E) E b) * (y : E) = k at hk1`. Establish `hkstar : star k = k`. Rewrite using `[← hkdef, star_add, star_mul, star_mul, star_star, star_star]`. Expand and normalize the polynomial expressions, which then agree. Establish `hk2 : (conjPrime₂ P).valuation E (k - (y : E)) < 1`.

Rewrite using `[hvc, star_sub, hkstar]`. Conclude with `hk1`. Establish `hkv : P.valuation E k = 1`. Establish `: k = star (y : E) + (k - star (y : E))` using `by ring`. Rewrite using `[this, Valuation.map_add_eq_of_lt_left _ (by rw [hyb]; exact hk1), hyb]`.

Establish `hk0 : k ≠ 0` using `by intro h; rw [h, map_zero] at hkv; exact zero_ne_one hkv`. Establish `hyb0 : star (y : E) ≠ 0` using `by rw [ne_eq, star_eq_zero]; exact y.ne_zero`. Take `⟨kF, hkF⟩` from `exists_of_star_eq hF hr ‹∃ a : E, star a ≠ a› hkstar`. Establish `hkF0 : kF ≠ 0` using `by rintro rfl; rw [map_zero] at hkF; exact hk0 hkF.symm`. Establish `hPK : χ.locK P (Units.mk0 k hk0) = χ.locK P (Units.mk0 (star (y : E)) hyb0)` using `locK_tame (ht P) (y := Units.mk0 (star (y : E)) hyb0) (k := Units.mk0 k hk0) hyb hk1`.

Establish `hQK : χ.locK (conjPrime₂ P) (Units.mk0 k hk0) = χ.locK (conjPrime₂ P) y` using `locK_tame (ht (conjPrime₂ P)) (y := y) (k := Units.mk0 k hk0) h2 hk2`. Establish `hab2 : aboveF (L` using `E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by`. Use extensionality with `W`. Simplify using `only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton]`. Conclude with `under_eq_iff hF hr ‹∃ a : E, star a ≠ a› P W`.

Establish `htriv : (∏ R ∈ aboveF (L` using `E) F (P.under (𝓞 F)), (χ.locK R).comp (upF F)) (Units.mk0 kF hkF0) = 1 := hχ.1 (P.under (𝓞 F)) (Units.mk0 kF hkF0)`. Establish `hup : upF F (Units.mk0 kF hkF0) = Units.mk0 k hk0` using `by ext; simp [upF, hkF]`. Rewrite `htriv` using `[MonoidHom.finsetProd_apply, hab2, Finset.prod_pair hP, MonoidHom.comp_apply, MonoidHom.comp_apply, hup]`. Establish `hz : z = y * (Units.mk0 (star (y : E)) hyb0)⁻¹`. Use `ext`.

Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ hyb0]`. Conclude with `hyz.symm`. Rewrite using `[hz, map_mul, map_inv, ← hPK, inv_eq_of_mul_eq_one_right htriv, hQK]`.
-/
theorem split_prod (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P ≠ conjPrime₂ P) {y z : Eˣ} (hyz : (y : E) = z * star (y : E)) (h1 : P.valuation E (y : E) = 1)
    (h2 : (conjPrime₂ P).valuation E (y : E) = 1) : χ.locK P y * χ.locK (conjPrime₂ P) y = χ.locK P z := by
  classical
  have hvc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : E), (conjPrime₂ W).valuation E x = W.valuation E (star x) :=
    fun W x => valuation_conjP W x
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ P.asIdeal, ∃ b ∈ (conjPrime₂ P).asIdeal, a + b = 1 := by
    have hne : P.asIdeal ≠ (conjPrime₂ P).asIdeal := fun h => hP (HeightOneSpectrum.ext h)
    have htop := Ideal.IsMaximal.coprime_of_ne P.isMaximal (conjPrime₂ P).isMaximal hne
    have h1' : (1 : 𝓞 E) ∈ P.asIdeal ⊔ (conjPrime₂ P).asIdeal := by rw [htop]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1'
    exact ⟨a, ha, b, hb, hab⟩
  have hs1 : P.valuation E (algebraMap (𝓞 E) E b - 1) < 1 := by
    have : algebraMap (𝓞 E) E b - 1 = algebraMap (𝓞 E) E (-a) := by
      rw [map_neg, ← map_one (algebraMap (𝓞 E) E), ← hab, map_add]; ring
    rw [this, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact P.asIdeal.neg_mem ha
  have hs2 : P.valuation E (star (algebraMap (𝓞 E) E b)) < 1 := by
    rw [← hvc, HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hb
  have hyb : P.valuation E (star (y : E)) = 1 := by rw [← hvc]; exact h2
  have hk1 : P.valuation E ((algebraMap (𝓞 E) E b * star (y : E) + star (algebraMap (𝓞 E) E b) * (y : E))
      - star (y : E)) < 1 := by
    have : (algebraMap (𝓞 E) E b * star (y : E) + star (algebraMap (𝓞 E) E b) * (y : E)) - star (y : E) =
        (algebraMap (𝓞 E) E b - 1) * star (y : E) + star (algebraMap (𝓞 E) E b) * (y : E) := by ring
    rw [this]
    apply Valuation.map_add_lt
    · rw [map_mul, hyb, mul_one]; exact hs1
    · rw [map_mul, h1, mul_one]; exact hs2
  generalize hkdef : algebraMap (𝓞 E) E b * star (y : E) + star (algebraMap (𝓞 E) E b) * (y : E) = k at hk1
  have hkstar : star k = k := by
    rw [← hkdef, star_add, star_mul, star_mul, star_star, star_star]; ring
  have hk2 : (conjPrime₂ P).valuation E (k - (y : E)) < 1 := by
    rw [hvc, star_sub, hkstar]; exact hk1
  have hkv : P.valuation E k = 1 := by
    have : k = star (y : E) + (k - star (y : E)) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hyb]; exact hk1), hyb]
  have hk0 : k ≠ 0 := by intro h; rw [h, map_zero] at hkv; exact zero_ne_one hkv
  have hyb0 : star (y : E) ≠ 0 := by rw [ne_eq, star_eq_zero]; exact y.ne_zero
  obtain ⟨kF, hkF⟩ := exists_of_star_eq hF hr ‹∃ a : E, star a ≠ a› hkstar
  have hkF0 : kF ≠ 0 := by rintro rfl; rw [map_zero] at hkF; exact hk0 hkF.symm
  have hPK : χ.locK P (Units.mk0 k hk0) = χ.locK P (Units.mk0 (star (y : E)) hyb0) :=
    locK_tame (ht P) (y := Units.mk0 (star (y : E)) hyb0) (k := Units.mk0 k hk0) hyb hk1
  have hQK : χ.locK (conjPrime₂ P) (Units.mk0 k hk0) = χ.locK (conjPrime₂ P) y :=
    locK_tame (ht (conjPrime₂ P)) (y := y) (k := Units.mk0 k hk0) h2 hk2
  have hab2 : aboveF (L := E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by
    ext W
    simp only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_insert,
      Finset.mem_singleton]
    exact under_eq_iff hF hr ‹∃ a : E, star a ≠ a› P W
  have htriv : (∏ R ∈ aboveF (L := E) F (P.under (𝓞 F)), (χ.locK R).comp (upF F)) (Units.mk0 kF hkF0) = 1 :=
    hχ.1 (P.under (𝓞 F)) (Units.mk0 kF hkF0)
  have hup : upF F (Units.mk0 kF hkF0) = Units.mk0 k hk0 := by
    ext; simp [upF, hkF]
  rw [MonoidHom.finsetProd_apply, hab2, Finset.prod_pair hP, MonoidHom.comp_apply, MonoidHom.comp_apply, hup] at htriv
  have hz : z = y * (Units.mk0 (star (y : E)) hyb0)⁻¹ := by
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [eq_mul_inv_iff_mul_eq₀ hyb0]; exact hyz.symm
  rw [hz, map_mul, map_inv, ← hPK, inv_eq_of_mul_eq_one_right htriv, hQK]

open Classical in

/- English proof (translation)
Establish `hvc : ∀ (W : HeightOneSpectrum (𝓞 E)) (t : E), (conjPrime₂ W).valuation E t = W.valuation E (star t)` using `fun W t => valuation_conjP W t`. Establish `hcc : ∀ W : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ W) = W` using `fun W => conjP_conjP' W`. Establish `hund : ∀ W : HeightOneSpectrum (𝓞 E), (conjPrime₂ W).under (𝓞 F) = W.under (𝓞 F)` using `fun W => (under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W (conjPrime₂ W)).mpr (Or.inr rfl)`. Establish `habv : ∀ W : HeightOneSpectrum (𝓞 E), aboveF (L` using `E) F (W.under (𝓞 F)) = {W, conjPrime₂ W} := by`. Introduce `W`.

Use extensionality with `R`. Simplify using `only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton]`. Conclude with `under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R`. Establish `hxstar : ∀ W : HeightOneSpectrum (𝓞 E), (conjPrime₂ W).valuation E (x : E) = W.valuation E (x : E)`. Introduce `W`.

Rewrite using `[hvc]`. Use `conv_rhs => rw [hxz, map_mul, hz W, one_mul]`. Establish `Hsh : ∀ W : HeightOneSpectrum (𝓞 E), ∃ pu : Eˣ, ∃ m : ℤ, W.valuation E ((x * pu ^ m : Eˣ) : E) = 1 ∧ (conjPrime₂ W).valuation E ((x * pu ^ m : Eˣ) : E) = 1 ∧ ((x * pu ^ m : Eˣ) : E) = z * star ((x * pu ^ m : Eˣ) : E) ∧ ∏ R ∈ ({W, conjPrime₂ W} : Finset (HeightOneSpectrum (𝓞 E))), …`. Introduce `W`. Take `⟨π, hπ⟩` from `(W.under (𝓞 F)).valuation_exists_uniformizer F`.

Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`. Establish `hp0 : algebraMap F E π ≠ 0`.

Rewrite using `[ne_eq, map_eq_zero_iff _ (algebraMap F E).injective]`. Conclude with `hπ0`. Take `⟨pu, hpu⟩ : ∃ pu : Eˣ, (pu : E) = algebraMap F E π` from `⟨Units.mk0 _ hp0, rfl⟩`. Establish `hpQ : W.valuation E (algebraMap F E π) = WithZero.exp (-1 : ℤ)`. Rewrite using `[valuation_up hr hu]`.

Conclude with `hπ`. Establish `hpQ' : (conjPrime₂ W).valuation E (algebraMap F E π) = WithZero.exp (-1 : ℤ)`. Rewrite using `[valuation_up hr hu, hund]`. Conclude with `hπ`. Establish `hx0 : W.valuation E (x : E) ≠ 0` using `(Valuation.ne_zero_iff _).mpr x.ne_zero`.

Take `⟨m, hm⟩ : ∃ m : ℤ, W.valuation E (x : E) = WithZero.exp m` from `⟨_, (WithZero.exp_log hx0).symm⟩`. Establish `hcalc : WithZero.exp m * WithZero.exp (-1 : ℤ) ^ m = 1`. Rewrite using `[← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul, mul_neg_one, add_neg_cancel, WithZero.exp_zero]`. Use `⟨pu, m, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hpu, hpQ, hm]`.

Conclude with `hcalc`. Rewrite using `[Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hpu, hpQ', hxstar, hm]`. Conclude with `hcalc`. Rewrite using `[Units.val_mul, Units.val_zpow_eq_zpow_val, hpu, star_mul, star_zpow₀, hF] conv_lhs => rw [hxz]`. Expand and normalize the polynomial expressions, which then agree.

Establish `htriv : (∏ R ∈ aboveF (L` using `E) F (W.under (𝓞 F)), (χ.locK R).comp (upF F)) (Units.mk0 π hπ0) = 1 := hχ.1 (W.under (𝓞 F)) (Units.mk0 π hπ0)`. Establish `hup : upF F (Units.mk0 π hπ0) = pu` using `by ext; simp [upF, hpu]`. Rewrite `htriv` using `[MonoidHom.finsetProd_apply, habv W]`. Simplify `htriv` using `only [MonoidHom.comp_apply, hup]`. Establish `Hcore : ∀ W : HeightOneSpectrum (𝓞 E), W ≠ conjPrime₂ W → χ.locK W x * χ.locK (conjPrime₂ W) x = χ.locK W z`.

Introduce `W hQ`. Take `⟨pu, m, h1, h2, h3, h4⟩` from `Hsh W`. Establish `hs` using `split_prod hF hr ‹∃ a : E, star a ≠ a› hχ ht hQ h3 h1 h2`. Rewrite `h4` using `[Finset.prod_pair hQ]`. Rewrite `hs` using `[map_mul, map_mul, map_zpow, map_zpow, mul_mul_mul_comm, ← mul_zpow, h4, one_zpow, mul_one]`.

Conclude with `hs`. Distinguish the cases in `hv : ∃ W : HeightOneSpectrum (𝓞 E), W.under (𝓞 F) = v`. Use `swap`. Use `push Not at hv`. Establish `h1 : aboveF (L` using `E) F v = ∅ := by`.

Use extensionality with `R`. Simplify using `only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.notMem_empty, iff_false]`. Conclude with `hv R`. Rewrite using `[h1, Finset.prod_empty, Finset.filter_false_of_mem (fun R _ => hv R), Finset.prod_empty]`. Take `⟨W, rfl⟩` from `hv`.

Rewrite using `[habv W]`. Distinguish the cases in `hQ : W = conjPrime₂ W`. Establish `hQT : W ∉ T` using `fun h => hT W h (hQ ▸ h)`. Rewrite using `[Finset.filter_false_of_mem (fun R hR hRu => by`. Break down `(under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R).mp hRu with rfl | rfl` into its components or cases.

Conclude with `hQT hR`. Conclude with `hQT (hQ ▸ hR)), Finset.prod_empty]`. Rewrite using `[← hQ, Finset.insert_eq_of_mem (Finset.mem_singleton_self W), Finset.prod_singleton]`. Take `⟨pu, m, h1, -, -, h4⟩` from `Hsh W`. Rewrite `h4` using `[← hQ, Finset.insert_eq_of_mem (Finset.mem_singleton_self W), Finset.prod_singleton]`.

Establish `hunr : χ.UnrAt W` using `hun W hQT (hQ ▸ hQT)`. Establish `hx1` using `locK_unr hunr h1`. Rewrite `hx1` using `[map_mul, map_zpow, h4, one_zpow, mul_one]`. Conclude with `hx1`. Rewrite using `[Finset.prod_pair hQ]`.

Distinguish the cases in `hQT : W ∈ T`. Establish `hf : T.filter (fun R => R.under (𝓞 F) = W.under (𝓞 F)) = {W}`. Use extensionality with `R`. Simplify using `only [Finset.mem_filter, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hR, hRu⟩`. Break down `(under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R).mp hRu with rfl | rfl` into its components or cases. Both sides reduce to the same expression. Conclude with `absurd hR (hT W hQT)`. Introduce and unpack `rfl`.

Conclude with `⟨hQT, rfl⟩`. Rewrite using `[hf, Finset.prod_singleton]`. Conclude with `Hcore W hQ`. Distinguish the cases in `hQT' : conjPrime₂ W ∈ T`. Establish `hf : T.filter (fun R => R.under (𝓞 F) = W.under (𝓞 F)) = {conjPrime₂ W}`.

Use extensionality with `R`. Simplify using `only [Finset.mem_filter, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hR, hRu⟩`. Break down `(under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R).mp hRu with rfl | rfl` into its components or cases.

Conclude with `absurd hR hQT`. Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `⟨hQT', hund W⟩`. Rewrite using `[hf, Finset.prod_singleton, mul_comm]`.

Establish `hne : conjPrime₂ W ≠ conjPrime₂ (conjPrime₂ W)`. Rewrite using `[hcc]`. Conclude with `fun h => hQ h.symm`. Use `Hcore (conjPrime₂ W) hne` as an intermediate fact. Rewrite `this` using `[hcc]`.

Conclude with `this`. Rewrite using `[Finset.filter_false_of_mem (fun R hR hRu => by`. Break down `(under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R).mp hRu with rfl | rfl` into its components or cases. Conclude with `hQT hR`. Conclude with `hQT' hR), Finset.prod_empty, Hcore W hQ]`.

Conclude with `locK_unr (hun W hQT hQT') (hz W)`.
-/
theorem place_prod (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) (hu : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal.ramificationIdxIn (𝓞 E) = 1)
    {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (hT : ∀ P ∈ T, conjPrime₂ P ∉ T) (hun : ∀ P, P ∉ T → conjPrime₂ P ∉ T → χ.UnrAt P) {x z : Eˣ} (hxz : (x : E) = z * star (x : E))
    (hz : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (z : E) = 1) (v : HeightOneSpectrum (𝓞 F)) :
    ∏ P ∈ aboveF (L := E) F v, χ.locK P x = ∏ P ∈ T with P.under (𝓞 F) = v, χ.locK P z := by
  classical
  have hvc : ∀ (W : HeightOneSpectrum (𝓞 E)) (t : E), (conjPrime₂ W).valuation E t = W.valuation E (star t) :=
    fun W t => valuation_conjP W t
  have hcc : ∀ W : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ W) = W := fun W => conjP_conjP' W
  have hund : ∀ W : HeightOneSpectrum (𝓞 E), (conjPrime₂ W).under (𝓞 F) = W.under (𝓞 F) :=
    fun W => (under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W (conjPrime₂ W)).mpr (Or.inr rfl)
  have habv : ∀ W : HeightOneSpectrum (𝓞 E), aboveF (L := E) F (W.under (𝓞 F)) = {W, conjPrime₂ W} := by
    intro W; ext R
    simp only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_insert,
      Finset.mem_singleton]
    exact under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R
  have hxstar : ∀ W : HeightOneSpectrum (𝓞 E), (conjPrime₂ W).valuation E (x : E) = W.valuation E (x : E) := by
    intro W
    rw [hvc]
    conv_rhs => rw [hxz, map_mul, hz W, one_mul]

  have Hsh : ∀ W : HeightOneSpectrum (𝓞 E), ∃ pu : Eˣ, ∃ m : ℤ,
      W.valuation E ((x * pu ^ m : Eˣ) : E) = 1 ∧ (conjPrime₂ W).valuation E ((x * pu ^ m : Eˣ) : E) = 1 ∧
      ((x * pu ^ m : Eˣ) : E) = z * star ((x * pu ^ m : Eˣ) : E) ∧
      ∏ R ∈ ({W, conjPrime₂ W} : Finset (HeightOneSpectrum (𝓞 E))), χ.locK R pu = 1 := by
    intro W
    obtain ⟨π, hπ⟩ := (W.under (𝓞 F)).valuation_exists_uniformizer F
    have hπ0 : π ≠ 0 := by
      rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
    have hp0 : algebraMap F E π ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (algebraMap F E).injective]; exact hπ0
    obtain ⟨pu, hpu⟩ : ∃ pu : Eˣ, (pu : E) = algebraMap F E π := ⟨Units.mk0 _ hp0, rfl⟩
    have hpQ : W.valuation E (algebraMap F E π) = WithZero.exp (-1 : ℤ) := by
      rw [valuation_up hr hu]; exact hπ
    have hpQ' : (conjPrime₂ W).valuation E (algebraMap F E π) = WithZero.exp (-1 : ℤ) := by
      rw [valuation_up hr hu, hund]; exact hπ
    have hx0 : W.valuation E (x : E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
    obtain ⟨m, hm⟩ : ∃ m : ℤ, W.valuation E (x : E) = WithZero.exp m := ⟨_, (WithZero.exp_log hx0).symm⟩
    have hcalc : WithZero.exp m * WithZero.exp (-1 : ℤ) ^ m = 1 := by
      rw [← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul, mul_neg_one, add_neg_cancel, WithZero.exp_zero]
    refine ⟨pu, m, ?_, ?_, ?_, ?_⟩
    · rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hpu, hpQ, hm]; exact hcalc
    · rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hpu, hpQ', hxstar, hm]; exact hcalc
    · rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hpu, star_mul, star_zpow₀, hF]
      conv_lhs => rw [hxz]
      ring
    · have htriv : (∏ R ∈ aboveF (L := E) F (W.under (𝓞 F)), (χ.locK R).comp (upF F)) (Units.mk0 π hπ0) = 1 :=
        hχ.1 (W.under (𝓞 F)) (Units.mk0 π hπ0)
      have hup : upF F (Units.mk0 π hπ0) = pu := by
        ext; simp [upF, hpu]
      rw [MonoidHom.finsetProd_apply, habv W] at htriv
      simpa only [MonoidHom.comp_apply, hup] using htriv
  have Hcore : ∀ W : HeightOneSpectrum (𝓞 E), W ≠ conjPrime₂ W → χ.locK W x * χ.locK (conjPrime₂ W) x = χ.locK W z := by
    intro W hQ
    obtain ⟨pu, m, h1, h2, h3, h4⟩ := Hsh W
    have hs := split_prod hF hr ‹∃ a : E, star a ≠ a› hχ ht hQ h3 h1 h2
    rw [Finset.prod_pair hQ] at h4
    rw [map_mul, map_mul, map_zpow, map_zpow, mul_mul_mul_comm, ← mul_zpow, h4, one_zpow, mul_one] at hs
    exact hs
  by_cases hv : ∃ W : HeightOneSpectrum (𝓞 E), W.under (𝓞 F) = v
  swap
  · push Not at hv
    have h1 : aboveF (L := E) F v = ∅ := by
      ext R
      simp only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.notMem_empty, iff_false]
      exact hv R
    rw [h1, Finset.prod_empty, Finset.filter_false_of_mem (fun R _ => hv R), Finset.prod_empty]
  obtain ⟨W, rfl⟩ := hv
  rw [habv W]
  by_cases hQ : W = conjPrime₂ W
  · have hQT : W ∉ T := fun h => hT W h (hQ ▸ h)
    rw [Finset.filter_false_of_mem (fun R hR hRu => by
      rcases (under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R).mp hRu with rfl | rfl
      · exact hQT hR
      · exact hQT (hQ ▸ hR)), Finset.prod_empty]
    rw [← hQ, Finset.insert_eq_of_mem (Finset.mem_singleton_self W), Finset.prod_singleton]
    obtain ⟨pu, m, h1, -, -, h4⟩ := Hsh W
    rw [← hQ, Finset.insert_eq_of_mem (Finset.mem_singleton_self W), Finset.prod_singleton] at h4
    have hunr : χ.UnrAt W := hun W hQT (hQ ▸ hQT)
    have hx1 := locK_unr hunr h1
    rw [map_mul, map_zpow, h4, one_zpow, mul_one] at hx1
    exact hx1
  · rw [Finset.prod_pair hQ]
    by_cases hQT : W ∈ T
    · have hf : T.filter (fun R => R.under (𝓞 F) = W.under (𝓞 F)) = {W} := by
        ext R
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hR, hRu⟩
          rcases (under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R).mp hRu with rfl | rfl
          · rfl
          · exact absurd hR (hT W hQT)
        · rintro rfl; exact ⟨hQT, rfl⟩
      rw [hf, Finset.prod_singleton]
      exact Hcore W hQ
    by_cases hQT' : conjPrime₂ W ∈ T
    · have hf : T.filter (fun R => R.under (𝓞 F) = W.under (𝓞 F)) = {conjPrime₂ W} := by
        ext R
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hR, hRu⟩
          rcases (under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R).mp hRu with rfl | rfl
          · exact absurd hR hQT
          · rfl
        · rintro rfl; exact ⟨hQT', hund W⟩
      rw [hf, Finset.prod_singleton, mul_comm]
      have hne : conjPrime₂ W ≠ conjPrime₂ (conjPrime₂ W) := by
        rw [hcc]; exact fun h => hQ h.symm
      have := Hcore (conjPrime₂ W) hne
      rw [hcc] at this
      exact this
    · rw [Finset.filter_false_of_mem (fun R hR hRu => by
        rcases (under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W R).mp hRu with rfl | rfl
        · exact hQT hR
        · exact hQT' hR), Finset.prod_empty, Hcore W hQ]
      exact locK_unr (hun W hQT hQT') (hz W)

/- English proof (translation)
Establish `hund : ∀ W : HeightOneSpectrum (𝓞 E), (conjPrime₂ W).under (𝓞 F) = W.under (𝓞 F)` using `fun W => (under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W (conjPrime₂ W)).mpr (Or.inr rfl)`. Establish `hmem : ∀ (w : HeightOneSpectrum (𝓞 F)) (U : HeightOneSpectrum (𝓞 E)), U ∈ aboveF (L` using `E) F w ↔ U.under (𝓞 F) = w := by`. Introduce `w U`. Simplify using `only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]`. Take `⟨V, hV⟩ : ∃ V : Finset (HeightOneSpectrum (𝓞 F)), V = (T ∪ (GlobalTheory.HeckeProduct.finite_ordF x).toFinset).image (fun U => U.under (𝓞 F))` from `⟨_, rfl⟩`.

Take `⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 E)), S = V.biUnion (fun w => aboveF (L` from `E) F w) := ⟨_, rfl⟩`. Establish `hmemS : ∀ U, U ∈ S ↔ U.under (𝓞 F) ∈ V`. Introduce `U`. Rewrite using `[hS, Finset.mem_biUnion]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, hw, hU⟩`. Rewrite `hU` using `[hmem]`. Rewrite using `[hU]`. Conclude with `hw`. Introduce `h`.

Conclude with `⟨_, h, (hmem _ _).mpr rfl⟩`. Establish `hTV : ∀ U ∈ T, U.under (𝓞 F) ∈ V` using `fun U hU => by`. Rewrite using `[hV]`. Conclude with `Finset.mem_image_of_mem _ (Finset.mem_union_left _ hU)`. Establish `hunr : ∀ U, U ∉ S → χ.UnrAt U`.

Introduce `U hU`. Rewrite `hU` using `[hmemS]`. Apply `hun U` to reduce the goal to its premises. Conclude with `fun h => hU (hTV U h)`. Introduce `h`.

Apply `hU` to reduce the goal to its premises. Rewrite using `[← hund U]`. Conclude with `hTV _ h`. Establish `hord : ∀ U, U ∉ S → ordF U x = 0`. Introduce `U hU`.

Assume the negation of the conclusion as `h`. Rewrite `hU` using `[hmemS, hV]`. Conclude with `hU (Finset.mem_image_of_mem _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)))`. Establish `hPR` using `GlobalTheory.HeckeProduct.productRule χ S hunr x`. Establish `hfin : (∏ᶠ (U : HeightOneSpectrum (𝓞 E)) (_ : U ∉ S), χ.val U ^ ordF U x) = 1`.

Apply `finprod_eq_one_of_forall_eq_one` to reduce the goal to its premises. Introduce `U`. Rewrite using `[finprod_eq_if]`. Use `split_ifs with hU`. Both sides reduce to the same expression.

Rewrite using `[hord U hU, zpow_zero]`. Establish `hprod : ∏ U ∈ S, χ.locK U x = ∏ U ∈ T, χ.locK U z`. Rewrite using `[hS, Finset.prod_biUnion]`. Rewrite using `[← Finset.prod_fiberwise_of_maps_to hTV]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `w _`. Conclude with `place_prod hF hr ‹∃ a : E, star a ≠ a› hu hχ ht hT hun hxz hz w`. Introduce `w₁ _ w₂ _ hne`. Rewrite using `[Function.onFun, Finset.disjoint_left]`. Introduce `U h₁ h₂`.

Rewrite `h₁`, `h₂` using `[hmem]`. Conclude with `hne (h₁.symm.trans h₂)`. Rewrite `hPR` using `[hfin, mul_one, hprod]`. Conclude with `hPR`.
-/
theorem inf_mul_prod (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) (hu : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal.ramificationIdxIn (𝓞 E) = 1)
    {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (hT : ∀ P ∈ T, conjPrime₂ P ∉ T) (hun : ∀ P, P ∉ T → conjPrime₂ P ∉ T → χ.UnrAt P) {x z : Eˣ} (hxz : (x : E) = z * star (x : E))
    (hz : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (z : E) = 1) :
    χ.inf x * ∏ P ∈ T, χ.locK P z = 1 := by
  classical
  have hund : ∀ W : HeightOneSpectrum (𝓞 E), (conjPrime₂ W).under (𝓞 F) = W.under (𝓞 F) :=
    fun W => (under_eq_iff hF hr ‹∃ a : E, star a ≠ a› W (conjPrime₂ W)).mpr (Or.inr rfl)
  have hmem : ∀ (w : HeightOneSpectrum (𝓞 F)) (U : HeightOneSpectrum (𝓞 E)),
      U ∈ aboveF (L := E) F w ↔ U.under (𝓞 F) = w := by
    intro w U; simp only [aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  obtain ⟨V, hV⟩ : ∃ V : Finset (HeightOneSpectrum (𝓞 F)),
      V = (T ∪ (GlobalTheory.HeckeProduct.finite_ordF x).toFinset).image (fun U => U.under (𝓞 F)) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 E)), S = V.biUnion (fun w => aboveF (L := E) F w) :=
    ⟨_, rfl⟩
  have hmemS : ∀ U, U ∈ S ↔ U.under (𝓞 F) ∈ V := by
    intro U; rw [hS, Finset.mem_biUnion]; constructor
    · rintro ⟨w, hw, hU⟩; rw [hmem] at hU; rw [hU]; exact hw
    · intro h; exact ⟨_, h, (hmem _ _).mpr rfl⟩
  have hTV : ∀ U ∈ T, U.under (𝓞 F) ∈ V := fun U hU => by
    rw [hV]; exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ hU)
  have hunr : ∀ U, U ∉ S → χ.UnrAt U := by
    intro U hU
    rw [hmemS] at hU
    apply hun U
    · exact fun h => hU (hTV U h)
    · intro h; apply hU; rw [← hund U]; exact hTV _ h
  have hord : ∀ U, U ∉ S → ordF U x = 0 := by
    intro U hU
    by_contra h
    rw [hmemS, hV] at hU
    exact hU (Finset.mem_image_of_mem _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)))
  have hPR := GlobalTheory.HeckeProduct.productRule χ S hunr x
  have hfin : (∏ᶠ (U : HeightOneSpectrum (𝓞 E)) (_ : U ∉ S), χ.val U ^ ordF U x) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro U
    rw [finprod_eq_if]
    split_ifs with hU
    · rfl
    · rw [hord U hU, zpow_zero]
  have hprod : ∏ U ∈ S, χ.locK U x = ∏ U ∈ T, χ.locK U z := by
    rw [hS, Finset.prod_biUnion]
    · rw [← Finset.prod_fiberwise_of_maps_to hTV]
      apply Finset.prod_congr rfl
      intro w _
      exact place_prod hF hr ‹∃ a : E, star a ≠ a› hu hχ ht hT hun hxz hz w
    · intro w₁ _ w₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro U h₁ h₂
      rw [hmem] at h₁ h₂
      exact hne (h₁.symm.trans h₂)
  rw [hfin, mul_one, hprod] at hPR
  exact hPR

end Local

section Res

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.ReadEx GlobalTheory.Mem.LocTriv ReciprocityTheory.Neutral.Bridge.HCFR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h : ((toRInt F E b : RInt F E) : AfE F E) = ((b : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))` using `by rfl`. Use `show afIso F E _ P = _`. Rewrite using `[h, afIso_tmul_one]`. Both sides reduce to the same expression.
-/
theorem evP_toRInt (P : HeightOneSpectrum (𝓞 E)) (b : 𝓞 E) :
    evP F P (toRInt F E b : AfE F E) = algebraMap E (P.adicCompletion E) (b : E) := by
  have h : ((toRInt F E b : RInt F E) : AfE F E) = ((b : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) := by rfl
  show afIso F E _ P = _
  rw [h, afIso_tmul_one]
  rfl

/- English proof (translation)
Establish `key : ∀ z ∈ P.asIdeal.map (toRInt F E), Valued.v (evP F P (z : AfE F E)) < 1`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨p, hp, rfl⟩` from `hx`.

Rewrite using `[evP_toRInt, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `(IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem P p).mpr hp`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[Subring.coe_add, map_add]`.

Conclude with `lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt hx hy)`. Consider the case `smul r x _ hx`. Rewrite using `[smul_eq_mul, Subring.coe_mul, map_mul, map_mul]`. Establish `hr : Valued.v (evP F P (r : AfE F E)) ≤ 1` using `(mem_rInt_iff F E _).mp r.2 P`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `key w h`.
-/
theorem valued_lt_of_mem {P : HeightOneSpectrum (𝓞 E)} {w : RInt F E} (h : w ∈ P.asIdeal.map (toRInt F E)) :
    Valued.v (evP F P (w : AfE F E)) < 1 := by
  have key : ∀ z ∈ P.asIdeal.map (toRInt F E), Valued.v (evP F P (z : AfE F E)) < 1 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      rw [evP_toRInt, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem P p).mpr hp
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Subring.coe_add, map_add]
      exact lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt hx hy)
    | smul r x _ hx =>
      rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
      have hr : Valued.v (evP F P (r : AfE F E)) ≤ 1 := (mem_rInt_iff F E _).mp r.2 P
      calc Valued.v (evP F P (r : AfE F E)) * Valued.v (evP F P (x : AfE F E))
          ≤ 1 * Valued.v (evP F P (x : AfE F E)) := by gcongr
        _ < 1 := by rw [one_mul]; exact hx
  exact key w h

/- English proof (translation)
Conclude with `(IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem P).mpr hb`.
-/
theorem val_eq_one {P : HeightOneSpectrum (𝓞 E)} {b : 𝓞 E} (hb : b ∉ P.asIdeal) : P.valuation E (b : E) = 1 := by
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem P).mpr hb

/- English proof (translation)
Establish `e : a = (a - c) + c` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_right _ (by rw [hc]; exact h), hc]`.
-/
private theorem valued_eq_one_of_valued_sub_lt_one_of_eq_one {Q : HeightOneSpectrum (𝓞 E)} {a c : Q.adicCompletion E}
    (hc : Valued.v c = 1) (h : Valued.v (a - c) < 1) : Valued.v a = 1 := by
  have e : a = (a - c) + c := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hc]; exact h), hc]

/- English proof (translation)
Establish `e` using `congrArg (fun r : FiniteAdeleRing (𝓞 E) E => r Q) (congrArg (afIso F E) (Units.inv_mul z))`. Simplify using `only [map_mul, map_one] at e`. Conclude with `e`.
-/
private theorem afIso_units_inv_mul_self_eq_one (z : (AfE F E)ˣ) (Q : HeightOneSpectrum (𝓞 E)) :
    afIso F E ((z⁻¹ : (AfE F E)ˣ) : AfE F E) Q * afIso F E (z : AfE F E) Q = 1 := by
  have e := congrArg (fun r : FiniteAdeleRing (𝓞 E) E => r Q) (congrArg (afIso F E) (Units.inv_mul z))
  simp only [map_mul, map_one] at e
  exact e

/- English proof (translation)
Rewrite using `[intU, Submonoid.mem_units_iff]`. Use `⟨(mem_rInt_iff F E _).mpr fun Q => (hz Q).le, (mem_rInt_iff F E _).mpr fun Q => ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg Valued.v (afIso_units_inv_mul_self_eq_one z Q)`. Rewrite `e` using `[map_mul, hz Q, mul_one, map_one]`. Conclude with `e.le`.
-/
private theorem mem_intU_of_forall_valued_afIso_eq_one {z : (AfE F E)ˣ}
    (hz : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (afIso F E (z : AfE F E) Q) = 1) : z ∈ intU F E := by
  rw [intU, Submonoid.mem_units_iff]
  refine ⟨(mem_rInt_iff F E _).mpr fun Q => (hz Q).le, (mem_rInt_iff F E _).mpr fun Q => ?_⟩
  have e := congrArg Valued.v (afIso_units_inv_mul_self_eq_one z Q)
  rw [map_mul, hz Q, mul_one, map_one] at e
  exact e.le

variable {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr F E K} {ξ : HChar E}

/- English proof (translation)
Establish `hb1 : Valued.v (algebraMap E (P.adicCompletion E) (b : E)) = 1`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `val_eq_one hb`. Establish `hP : Valued.v (evP F P (u : AfE F E) - algebraMap E (P.adicCompletion E) (b : E)) < 1`. Use `valued_lt_of_mem h1` as an intermediate fact.

Rewrite `this` using `[AddSubgroupClass.coe_sub, map_sub, evP_toRInt, hy]`. Then use the resulting hypothesis. Establish `hQ : ∀ Q, Q ≠ P → Valued.v (evP F Q (u : AfE F E) - 1) < 1`. Introduce `Q hQ`. Use `valued_lt_of_mem (h2 Q hQ)` as an intermediate fact. Rewrite `this` using `[AddSubgroupClass.coe_sub, OneMemClass.coe_one, map_sub, map_one, hy]`. Then use the resulting hypothesis.

Establish `hu : ∀ Q, Valued.v (afIso F E (u : AfE F E) Q) = 1`. Introduce `Q`. Distinguish the cases in `hQP : Q = P`. Substitute `hQP` using the available equality. Conclude with `valued_eq_one_of_valued_sub_lt_one_of_eq_one hb1 hP`.

Conclude with `valued_eq_one_of_valued_sub_lt_one_of_eq_one (map_one _) (hQ Q hQP)`. Establish `huI : u ∈ intU F E` using `mem_intU_of_forall_valued_afIso_eq_one hu`. Use `⟨huI, ?_⟩` and prove the remaining obligations. Use `set a := Neutral.B1.localIdele E P (atFin P x) with ha`. Use `set w : (AfE F E)ˣ := finAf F E a with hw`.

Establish `hwP : afIso F E (w : AfE F E) P = algebraMap E (P.adicCompletion E) (b : E)`. Rewrite using `[hw, afIso_finAf, ha, GlobalTheory.HeckeProduct.localIdele_snd_self, ← hx]`. Both sides reduce to the same expression. Establish `hwQ : ∀ Q, Q ≠ P → afIso F E (w : AfE F E) Q = 1`. Introduce `Q hQ`.

Rewrite using `[hw, afIso_finAf, ha, GlobalTheory.HeckeProduct.localIdele_snd_ne E P Q hQ]`. Establish `hwI : w ∈ intU F E`. Use `mem_intU_of_forall_valued_afIso_eq_one fun Q => ?_` and prove the remaining obligations. Distinguish the cases in `hQP : Q = P`. Substitute `hQP` using the available equality.

Rewrite using `[hwP]`. Conclude with `hb1`. Rewrite using `[hwQ Q hQP]`. Conclude with `map_one _`. Use `set t : (AfE F E)ˣ := u * w⁻¹ with ht_def`.

Establish `hut : u = t * w` using `by rw [ht_def, inv_mul_cancel_right]`. Establish `htI : t ∈ intU F E` using `Subgroup.mul_mem _ huI (Subgroup.inv_mem _ hwI)`. Establish `hcomp : ∀ Q, afIso F E (t : AfE F E) Q * afIso F E (w : AfE F E) Q = afIso F E (u : AfE F E) Q`. Introduce `Q`. Establish `e` using `congrArg (fun r : FiniteAdeleRing (𝓞 E) E => r Q) (congrArg (afIso F E) (congrArg Units.val hut))`.

Simplify using `only [Units.val_mul, map_mul] at e`. Conclude with `e.symm`. Establish `hlt : ∀ Q, Valued.v (evP F Q ((t : AfE F E) - 1)) < 1`. Introduce `Q`. Rewrite using `[map_sub, map_one]`.

Distinguish the cases in `hQP : Q = P`. Substitute `hQP` using the available equality. Establish `e : (evP F Q (t : AfE F E) - 1) * algebraMap E (Q.adicCompletion E) (b : E) = evP F Q (u : AfE F E) - algebraMap E (Q.adicCompletion E) (b : E)`. Rewrite using `[_root_.sub_mul, one_mul]`. Use `show afIso F E (t : AfE F E) Q * algebraMap E (Q.adicCompletion E) (b : E) - _ = afIso F E (u : AfE F E) Q - _`.

Rewrite using `[← hwP, hcomp]`. Establish `e2` using `congrArg Valued.v e`. Rewrite `e2` using `[map_mul, hb1, mul_one]`. Rewrite using `[e2]`. Conclude with `hP`.

Establish `e : evP F Q (t : AfE F E) = evP F Q (u : AfE F E)` using `by show afIso F E (t : AfE F E) Q = afIso F E (u : AfE F E) Q`. Rewrite using `[← hcomp, hwQ Q hQP, mul_one]`. Rewrite using `[e]`. Conclude with `hQ Q hQP`. Establish `ht1 : ξ.1 (toIdl F E t) = 1` using `map_toIdl_eq_one ht htI fun Q _ => le_exp_neg_one (hlt Q)`.

Establish `hσt : σ ((μ t : Kˣ) : K) = 1`. Rewrite using `[← h.apply (toIdl F E t) t (toIdl_snd t).symm, ht1]`. Both sides reduce to the same expression. Establish `hσw : σ ((μ w : Kˣ) : K) = ((ξ.1 a : ℂˣ) : ℂ)` using `(h.apply a w (afIso_finAf F E a)).symm`. Rewrite using `[hut, map_mul, Units.val_mul, map_mul, hσt, one_mul, hσw]`.

Both sides reduce to the same expression.
-/
theorem value_of_congr (h : Reads σ μ ξ) (ht : ∀ P, ξ.TameAt P) {P : HeightOneSpectrum (𝓞 E)} {u : (AfE F E)ˣ} {y : RInt F E}
    (hy : (y : AfE F E) = u) {b : 𝓞 E} (hb : b ∉ P.asIdeal) {x : Eˣ} (hx : (x : E) = b)
    (h1 : y - toRInt F E b ∈ P.asIdeal.map (toRInt F E))
    (h2 : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → y - 1 ∈ Q.asIdeal.map (toRInt F E)) :
    u ∈ intU F E ∧ σ ((μ u : Kˣ) : K) = ((ξ.locK P x : ℂˣ) : ℂ) := by

  have hb1 : Valued.v (algebraMap E (P.adicCompletion E) (b : E)) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact val_eq_one hb
  have hP : Valued.v (evP F P (u : AfE F E) - algebraMap E (P.adicCompletion E) (b : E)) < 1 := by
    have := valued_lt_of_mem h1
    rwa [AddSubgroupClass.coe_sub, map_sub, evP_toRInt, hy] at this
  have hQ : ∀ Q, Q ≠ P → Valued.v (evP F Q (u : AfE F E) - 1) < 1 := by
    intro Q hQ
    have := valued_lt_of_mem (h2 Q hQ)
    rwa [AddSubgroupClass.coe_sub, OneMemClass.coe_one, map_sub, map_one, hy] at this
  have hu : ∀ Q, Valued.v (afIso F E (u : AfE F E) Q) = 1 := by
    intro Q
    by_cases hQP : Q = P
    · subst hQP
      exact valued_eq_one_of_valued_sub_lt_one_of_eq_one hb1 hP
    · exact valued_eq_one_of_valued_sub_lt_one_of_eq_one (map_one _) (hQ Q hQP)
  have huI : u ∈ intU F E := mem_intU_of_forall_valued_afIso_eq_one hu
  refine ⟨huI, ?_⟩

  set a := Neutral.B1.localIdele E P (atFin P x) with ha
  set w : (AfE F E)ˣ := finAf F E a with hw
  have hwP : afIso F E (w : AfE F E) P = algebraMap E (P.adicCompletion E) (b : E) := by
    rw [hw, afIso_finAf, ha, GlobalTheory.HeckeProduct.localIdele_snd_self, ← hx]
    rfl
  have hwQ : ∀ Q, Q ≠ P → afIso F E (w : AfE F E) Q = 1 := by
    intro Q hQ
    rw [hw, afIso_finAf, ha, GlobalTheory.HeckeProduct.localIdele_snd_ne E P Q hQ]
  have hwI : w ∈ intU F E := by
    refine mem_intU_of_forall_valued_afIso_eq_one fun Q => ?_
    by_cases hQP : Q = P
    · subst hQP
      rw [hwP]
      exact hb1
    · rw [hwQ Q hQP]
      exact map_one _

  set t : (AfE F E)ˣ := u * w⁻¹ with ht_def
  have hut : u = t * w := by rw [ht_def, inv_mul_cancel_right]
  have htI : t ∈ intU F E := Subgroup.mul_mem _ huI (Subgroup.inv_mem _ hwI)
  have hcomp : ∀ Q, afIso F E (t : AfE F E) Q * afIso F E (w : AfE F E) Q = afIso F E (u : AfE F E) Q := by
    intro Q
    have e := congrArg (fun r : FiniteAdeleRing (𝓞 E) E => r Q) (congrArg (afIso F E) (congrArg Units.val hut))
    simp only [Units.val_mul, map_mul] at e
    exact e.symm
  have hlt : ∀ Q, Valued.v (evP F Q ((t : AfE F E) - 1)) < 1 := by
    intro Q
    rw [map_sub, map_one]
    by_cases hQP : Q = P
    · subst hQP
      have e : (evP F Q (t : AfE F E) - 1) * algebraMap E (Q.adicCompletion E) (b : E) =
          evP F Q (u : AfE F E) - algebraMap E (Q.adicCompletion E) (b : E) := by
        rw [_root_.sub_mul, one_mul]
        show afIso F E (t : AfE F E) Q * algebraMap E (Q.adicCompletion E) (b : E) - _ = afIso F E (u : AfE F E) Q - _
        rw [← hwP, hcomp]
      have e2 := congrArg Valued.v e
      rw [map_mul, hb1, mul_one] at e2
      rw [e2]
      exact hP
    · have e : evP F Q (t : AfE F E) = evP F Q (u : AfE F E) := by
        show afIso F E (t : AfE F E) Q = afIso F E (u : AfE F E) Q
        rw [← hcomp, hwQ Q hQP, mul_one]
      rw [e]
      exact hQ Q hQP
  have ht1 : ξ.1 (toIdl F E t) = 1 := map_toIdl_eq_one ht htI fun Q _ => le_exp_neg_one (hlt Q)
  have hσt : σ ((μ t : Kˣ) : K) = 1 := by
    rw [← h.apply (toIdl F E t) t (toIdl_snd t).symm, ht1]
    rfl
  have hσw : σ ((μ w : Kˣ) : K) = ((ξ.1 a : ℂˣ) : ℂ) := (h.apply a w (afIso_finAf F E a)).symm
  rw [hut, map_mul, Units.val_mul, map_mul, hσt, one_mul, hσw]
  rfl

/- English proof (translation)
Establish `hne : ∀ b : 𝓞 E, b ∉ P.asIdeal → ((b : 𝓞 E) : E) ≠ 0`. Introduce `b hb h0`. Apply `hb` to reduce the goal to its premises. Establish `hb0 : b = 0` using `by exact_mod_cast h0`. Rewrite using `[hb0]`.

Conclude with `P.asIdeal.zero_mem`. Establish `hnm : ∀ (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a → b ∉ P.asIdeal`. Introduce `a b hb hmem`. Establish `h0 : Ideal.Quotient.mk P.asIdeal b = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hmem`. Conclude with `a.ne_zero (hb ▸ h0)`.

Use `choose lift hlift using fun a : (𝓞 E ⧸ P.asIdeal)ˣ => Ideal.Quotient.mk_surjective (a : 𝓞 E ⧸ P.asIdeal)`. Set `xl : (𝓞 E ⧸ P.asIdeal)ˣ → Eˣ` to `fun a => Units.mk0 _ (hne (lift a) (hnm a _ (hlift a)))`. Set `f : (𝓞 E ⧸ P.asIdeal)ˣ → Kˣ` to `fun a => μ (finAf F E (Neutral.B1.localIdele E P (atFin P (xl a))))`. Establish `hf : ∀ a, σ ((f a : Kˣ) : K) = ((ξ.locK P (xl a) : ℂˣ) : ℂ)` using `fun a => (h (Neutral.B1.localIdele E P (atFin P (xl a)))).symm`. Establish `hwd : ∀ (x y : Eˣ) (b c : 𝓞 E), (x : E) = b → (y : E) = c → c ∉ P.asIdeal → b - c ∈ P.asIdeal → ξ.locK P x = ξ.locK P y`.

Introduce `x y b c hx hy hc hbc`. Apply `locK_tame (ht P)` to reduce the goal to its premises. Rewrite using `[hy]`. Conclude with `val_eq_one hc`. Rewrite using `[hx, hy]`.

Establish `hsub : ((b : E) - (c : E)) = ((b - c : 𝓞 E) : E)` using `by push_cast; ring`. Rewrite using `[hsub]`. Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem P (b - c)).mpr hbc`. Establish `key : ∀ (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E) (x : Eˣ), Ideal.Quotient.mk P.asIdeal b = a → (x : E) = b → σ ((f a : Kˣ) : K) = ((ξ.locK P x : ℂˣ) : ℂ)`. Introduce `a b x hb hx`.

Rewrite using `[hf a, hwd x (xl a) b (lift a) hx rfl (hnm a _ (hlift a)) (Ideal.Quotient.eq.mp (hb.trans (hlift a).symm))]`. Set `χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ` to `{ toFun := f map_one' := by`. Apply `Units.ext` to reduce the goal to its premises. Apply `σ.injective` to reduce the goal to its premises. Establish `h1` using `key 1 1 1 (by simp) (by simp)`.

Rewrite `h1` using `[map_one, Units.val_one]`. Rewrite using `[h1, Units.val_one, map_one]`. Use the proof step `map_mul' := by`. Introduce `a c`. Apply `Units.ext` to reduce the goal to its premises.

Apply `σ.injective` to reduce the goal to its premises. Establish `h1` using `key (a * c) (lift a * lift c) (xl a * xl c) (by rw [map_mul, hlift a, hlift c]; rfl) (by simp [xl])`. Rewrite `h1` using `[map_mul, Units.val_mul]`. Rewrite using `[Units.val_mul, map_mul, h1, hf, hf] }`. Use `⟨χ, ?_⟩` and prove the remaining obligations.

Introduce `v hv u a b hb hs h1 h2`. Establish `hbP` using `hnm a b hb`. Establish `hv2` using `(value_of_congr h ht (u := Units.map (RInt F E).subtype.toMonoidHom u) (y := (u : RInt F E)) rfl hbP (x := Units.mk0 _ (hne b hbP)) rfl h1 h2).2`. Apply `Units.ext` to reduce the goal to its premises. Apply `σ.injective` to reduce the goal to its premises.

Rewrite using `[hv2]`. Conclude with `(key a b _ hb rfl).symm`.
-/
theorem exists_isResChar (h : Reads σ μ ξ) (ht : ∀ P, ξ.TameAt P) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ χ, IsResChar μ P χ := by
  classical
  have hne : ∀ b : 𝓞 E, b ∉ P.asIdeal → ((b : 𝓞 E) : E) ≠ 0 := by
    intro b hb h0
    apply hb
    have hb0 : b = 0 := by exact_mod_cast h0
    rw [hb0]
    exact P.asIdeal.zero_mem
  have hnm : ∀ (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a → b ∉ P.asIdeal := by
    intro a b hb hmem
    have h0 : Ideal.Quotient.mk P.asIdeal b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact a.ne_zero (hb ▸ h0)
  choose lift hlift using fun a : (𝓞 E ⧸ P.asIdeal)ˣ => Ideal.Quotient.mk_surjective (a : 𝓞 E ⧸ P.asIdeal)
  let xl : (𝓞 E ⧸ P.asIdeal)ˣ → Eˣ := fun a => Units.mk0 _ (hne (lift a) (hnm a _ (hlift a)))
  let f : (𝓞 E ⧸ P.asIdeal)ˣ → Kˣ := fun a => μ (finAf F E (Neutral.B1.localIdele E P (atFin P (xl a))))
  have hf : ∀ a, σ ((f a : Kˣ) : K) = ((ξ.locK P (xl a) : ℂˣ) : ℂ) := fun a => (h (Neutral.B1.localIdele E P (atFin P (xl a)))).symm
  have hwd : ∀ (x y : Eˣ) (b c : 𝓞 E), (x : E) = b → (y : E) = c → c ∉ P.asIdeal → b - c ∈ P.asIdeal →
      ξ.locK P x = ξ.locK P y := by
    intro x y b c hx hy hc hbc
    apply locK_tame (ht P)
    · rw [hy]
      exact val_eq_one hc
    · rw [hx, hy]
      have hsub : ((b : E) - (c : E)) = ((b - c : 𝓞 E) : E) := by push_cast; ring
      rw [hsub]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem P (b - c)).mpr hbc
  have key : ∀ (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E) (x : Eˣ), Ideal.Quotient.mk P.asIdeal b = a → (x : E) = b →
      σ ((f a : Kˣ) : K) = ((ξ.locK P x : ℂˣ) : ℂ) := by
    intro a b x hb hx
    rw [hf a, hwd x (xl a) b (lift a) hx rfl (hnm a _ (hlift a)) (Ideal.Quotient.eq.mp (hb.trans (hlift a).symm))]
  let χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ :=
    { toFun := f
      map_one' := by
        apply Units.ext
        apply σ.injective
        have h1 := key 1 1 1 (by simp) (by simp)
        rw [map_one, Units.val_one] at h1
        rw [h1, Units.val_one, map_one]
      map_mul' := by
        intro a c
        apply Units.ext
        apply σ.injective
        have h1 := key (a * c) (lift a * lift c) (xl a * xl c) (by rw [map_mul, hlift a, hlift c]; rfl) (by simp [xl])
        rw [map_mul, Units.val_mul] at h1
        rw [Units.val_mul, map_mul, h1, hf, hf] }
  refine ⟨χ, ?_⟩
  intro v hv u a b hb hs h1 h2
  have hbP := hnm a b hb
  have hv2 := (value_of_congr h ht (u := Units.map (RInt F E).subtype.toMonoidHom u) (y := (u : RInt F E)) rfl hbP
    (x := Units.mk0 _ (hne b hbP)) rfl h1 h2).2
  apply Units.ext
  apply σ.injective
  rw [hv2]
  exact (key a b _ hb rfl).symm

/- English proof (translation)
Establish `p1 : ∀ c : 𝓞 E, ((toRInt F E c : RInt F E) : AfE F E) = ((c : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))`. Introduce `c`. Both sides reduce to the same expression. Establish `p2 : ∀ (y : E) (Q : HeightOneSpectrum (𝓞 E)), afIso F E (y ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) Q = algebraMap E (Q.adicCompletion E) y`. Introduce `y Q`.

Rewrite using `[afIso_tmul_one]`. Both sides reduce to the same expression. Establish `p3 : ∀ (z : (P.adicCompletion E)ˣ), afIso F E (finAf F E (Neutral.B1.localIdele E P z) : AfE F E) P = z`. Introduce `z`. Rewrite using `[afIso_finAf]`.

Conclude with `Pi.mulSingle_eq_same (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (z : P.adicCompletion E)`. Establish `p4 : ∀ (z : (P.adicCompletion E)ˣ) (Q : HeightOneSpectrum (𝓞 E)), Q ≠ P → afIso F E (finAf F E (Neutral.B1.localIdele E P z) : AfE F E) Q = 1`. Introduce `z Q hQ`. Rewrite using `[afIso_finAf]`. Conclude with `Pi.mulSingle_eq_of_ne (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) hQ (z : P.adicCompletion E)`.

Establish `hM : ∀ (Q : HeightOneSpectrum (𝓞 E)) (z : RInt F E), afIso F E (z : AfE F E) Q = 0 → z ∈ Q.asIdeal.map (toRInt F E)`. Introduce `Q z hz`. Establish `hQ0 : (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `Q.ne_bot`.

Establish `hone : (1 : E) ∈ (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹`. Rewrite using `[FractionalIdeal.coe_ideal_mul_inv Q.asIdeal Q.ne_bot]`. Conclude with `(FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩`. Establish `hval : ∀ q ∈ (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹, ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q → Q'.valuation E q ≤ 1`. Introduce `q hq Q' hQ'`.

Establish `hnle : ¬ Q.asIdeal ≤ Q'.asIdeal`. Introduce `hle`. Apply `hQ'` to reduce the goal to its premises. Conclude with `HeightOneSpectrum.ext ((Q.isMaximal.eq_of_le Q'.isPrime.ne_top hle).symm)`. Take `⟨y, hyQ, hyQ'⟩` from `Set.not_subset.mp hnle`.

Establish `hqy` using `(FractionalIdeal.mem_inv_iff hQ0).mp hq (algebraMap (𝓞 E) E y) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hyQ, rfl⟩)`. Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).mp hqy`. Establish `h1 : Q'.valuation E (q * algebraMap (𝓞 E) E y) ≤ 1`. Rewrite using `[← hr]`. Conclude with `HeightOneSpectrum.valuation_le_one Q' r`.

Establish `h2 : Q'.valuation E (algebraMap (𝓞 E) E y) = 1` using `val_eq_one hyQ'`. Rewrite `h1` using `[map_mul, h2, mul_one]`. Conclude with `h1`. Establish `hint : ∀ q ∈ (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹, (q ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * (z : AfE F E) ∈ RInt F E`. Introduce `q hq`.

Rewrite using `[mem_rInt_iff]`. Introduce `Q'`. Establish `hmul : afIso F E ((q ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * (z : AfE F E)) Q' = afIso F E (q ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) Q' * afIso F E (z : AfE F E) Q'`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.

Rewrite using `[hmul, p2, map_mul]`. Distinguish the cases in `hQ' : Q' = Q`. Substitute `hQ'` using the available equality. Rewrite using `[hz, map_zero, mul_zero]`. Conclude with `zero_le`.

Establish `hz1` using `(mem_rInt_iff F E (z : AfE F E)).mp z.2 Q'`. Establish `hc : Valued.v ((algebraMap E (Q'.adicCompletion E)) q) = Q'.valuation E q` using `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) Q' q`. Rewrite using `[hc]`. Conclude with `mul_le_one' (hval q hq Q' hQ') hz1`. Establish `key : ∀ t ∈ (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹, ∃ w ∈ Q.asIdeal.map (toRInt F E), (w : AfE F E) = (t ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * (z : AfE F E)`.

Introduce `t ht'`. Use `FractionalIdeal.mul_induction_on ht' ?_ ?_` and prove the remaining obligations. Introduce `i hi j hj`. Take `⟨i', hi', rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hi`. Use `⟨toRInt F E i' * ⟨_, hint j hj⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hi'), ?_⟩` and prove the remaining obligations.

Rewrite using `[Subring.coe_mul, p1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Introduce and unpack `x y ⟨w1, hw1, e1⟩ ⟨w2, hw2, e2⟩`. Use `⟨w1 + w2, Ideal.add_mem _ hw1 hw2, ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.coe_add, e1, e2, TensorProduct.add_tmul, add_mul]`. Take `⟨w, hw, ew⟩` from `key 1 hone`.

Establish `hwz : w = z`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[ew, ← Algebra.TensorProduct.one_def, one_mul]`. Conclude with `hwz ▸ hw`. Establish `hbP : b ∉ P.asIdeal`.

Introduce `hmem`. Establish `h0 : Ideal.Quotient.mk P.asIdeal b = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hmem`. Conclude with `a.ne_zero (hb ▸ h0)`. Establish `hux : Formalism.L2.Host.IsUnitAt P (atFin P x)` using `by show Valued.v (algebraMap E (P.adicCompletion E) (x : E)) = 1`. Establish `hc : Valued.v ((algebraMap E (P.adicCompletion E)) (x : E)) = P.valuation E (x : E)` using `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) P (x : E)`.

Rewrite using `[hc, hx]`. Conclude with `val_eq_one hbP`. Establish `hyU : finAf F E (Neutral.B1.localIdele E P (atFin P x)) ∈ intU F E` using `(GlobalTheory.Mem.ReadTwist.finAf_mem_intU_iff _).mpr (GlobalTheory.Mem.ReadTwist.local_mem_unitIdl hux)`. Set `u : (RInt F E)ˣ` to `Submonoid.unitsEquivUnitsType _ ⟨_, hyU⟩`. Establish `hu : ((u : RInt F E) : AfE F E) = (finAf F E (Neutral.B1.localIdele E P (atFin P x)) : AfE F E)` using `rfl`.

Establish `hs : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E (P.under (𝓞 F))` using `GlobalTheory.Mem.ReadTwist.local_mem_suppAt P _`. Establish `hA : (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E)`. Apply `hM` to reduce the goal to its premises. Rewrite using `[AddSubgroupClass.coe_sub, map_sub, hu, p1]`. Use `show afIso F E _ P - afIso F E _ P = 0`.

Rewrite using `[p3, p2]`. Use `show algebraMap E (P.adicCompletion E) (x : E) - _ = 0`. Rewrite using `[hx, sub_self]`. Establish `hB : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → (u : RInt F E) - 1 ∈ Q.asIdeal.map (toRInt F E)`. Introduce `Q hQ`.

Apply `hM` to reduce the goal to its premises. Rewrite using `[AddSubgroupClass.coe_sub, map_sub, hu, OneMemClass.coe_one, map_one]`. Use `show afIso F E _ Q - 1 = 0`. Rewrite using `[p4 _ Q hQ, sub_self]`. Establish `hex` using `exists_isResChar h ht P`.

Establish `hIs` using `hex.choose_spec (P.under (𝓞 F)) rfl u a b hb hs hA hB`. Establish `hv` using `(value_of_congr h ht (u := Units.map (RInt F E).subtype.toMonoidHom u) (y := (u : RInt F E)) rfl hbP hx hA hB).2`. Rewrite using `[Formalism.L2.DIV.resChar, dif_pos hex, ← hIs]`. Conclude with `hv`.
-/
theorem resChar_eq (h : Reads σ μ ξ) (ht : ∀ P, ξ.TameAt P) (P : HeightOneSpectrum (𝓞 E)) (a : (𝓞 E ⧸ P.asIdeal)ˣ)
    (b : 𝓞 E) (x : Eˣ) (hx : (x : E) = b) (hb : Ideal.Quotient.mk P.asIdeal b = a) :
    σ ((resChar μ P a : Kˣ) : K) = ((ξ.locK P x : ℂˣ) : ℂ) := by
  classical
  have p1 : ∀ c : 𝓞 E, ((toRInt F E c : RInt F E) : AfE F E) = ((c : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) := by
    intro c
    rfl
  have p2 : ∀ (y : E) (Q : HeightOneSpectrum (𝓞 E)), afIso F E (y ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) Q = algebraMap E (Q.adicCompletion E) y := by
    intro y Q
    rw [afIso_tmul_one]
    rfl
  have p3 : ∀ (z : (P.adicCompletion E)ˣ), afIso F E (finAf F E (Neutral.B1.localIdele E P z) : AfE F E) P = z := by
    intro z
    rw [afIso_finAf]
    exact Pi.mulSingle_eq_same (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) P (z : P.adicCompletion E)
  have p4 : ∀ (z : (P.adicCompletion E)ˣ) (Q : HeightOneSpectrum (𝓞 E)), Q ≠ P → afIso F E (finAf F E (Neutral.B1.localIdele E P z) : AfE F E) Q = 1 := by
    intro z Q hQ
    rw [afIso_finAf]
    exact Pi.mulSingle_eq_of_ne (M := fun Q : HeightOneSpectrum (𝓞 E) => Q.adicCompletion E) hQ (z : P.adicCompletion E)

  have hM : ∀ (Q : HeightOneSpectrum (𝓞 E)) (z : RInt F E), afIso F E (z : AfE F E) Q = 0 → z ∈ Q.asIdeal.map (toRInt F E) := by
    intro Q z hz
    have hQ0 : (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
      exact Q.ne_bot
    have hone : (1 : E) ∈ (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ := by
      rw [FractionalIdeal.coe_ideal_mul_inv Q.asIdeal Q.ne_bot]
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩

    have hval : ∀ q ∈ (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹, ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q →
        Q'.valuation E q ≤ 1 := by
      intro q hq Q' hQ'
      have hnle : ¬ Q.asIdeal ≤ Q'.asIdeal := by
        intro hle
        apply hQ'
        exact HeightOneSpectrum.ext ((Q.isMaximal.eq_of_le Q'.isPrime.ne_top hle).symm)
      obtain ⟨y, hyQ, hyQ'⟩ := Set.not_subset.mp hnle
      have hqy := (FractionalIdeal.mem_inv_iff hQ0).mp hq (algebraMap (𝓞 E) E y) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hyQ, rfl⟩)
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp hqy
      have h1 : Q'.valuation E (q * algebraMap (𝓞 E) E y) ≤ 1 := by
        rw [← hr]
        exact HeightOneSpectrum.valuation_le_one Q' r
      have h2 : Q'.valuation E (algebraMap (𝓞 E) E y) = 1 := val_eq_one hyQ'
      rw [map_mul, h2, mul_one] at h1
      exact h1
    have hint : ∀ q ∈ (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹,
        (q ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * (z : AfE F E) ∈ RInt F E := by
      intro q hq
      rw [mem_rInt_iff]
      intro Q'
      have hmul : afIso F E ((q ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * (z : AfE F E)) Q' =
          afIso F E (q ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) Q' * afIso F E (z : AfE F E) Q' := by
        rw [map_mul]
        rfl
      rw [hmul, p2, map_mul]
      by_cases hQ' : Q' = Q
      · subst hQ'
        rw [hz, map_zero, mul_zero]
        exact zero_le
      · have hz1 := (mem_rInt_iff F E (z : AfE F E)).mp z.2 Q'
        have hc : Valued.v ((algebraMap E (Q'.adicCompletion E)) q) = Q'.valuation E q :=
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) Q' q
        rw [hc]
        exact mul_le_one' (hval q hq Q' hQ') hz1
    have key : ∀ t ∈ (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * (Q.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹,
        ∃ w ∈ Q.asIdeal.map (toRInt F E), (w : AfE F E) = (t ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * (z : AfE F E) := by
      intro t ht'
      refine FractionalIdeal.mul_induction_on ht' ?_ ?_
      · intro i hi j hj
        obtain ⟨i', hi', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hi
        refine ⟨toRInt F E i' * ⟨_, hint j hj⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hi'), ?_⟩
        rw [Subring.coe_mul, p1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      · rintro x y ⟨w1, hw1, e1⟩ ⟨w2, hw2, e2⟩
        refine ⟨w1 + w2, Ideal.add_mem _ hw1 hw2, ?_⟩
        rw [Subring.coe_add, e1, e2, TensorProduct.add_tmul, add_mul]
    obtain ⟨w, hw, ew⟩ := key 1 hone
    have hwz : w = z := by
      apply Subtype.ext
      rw [ew, ← Algebra.TensorProduct.one_def, one_mul]
    exact hwz ▸ hw
  have hbP : b ∉ P.asIdeal := by
    intro hmem
    have h0 : Ideal.Quotient.mk P.asIdeal b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact a.ne_zero (hb ▸ h0)
  have hux : Formalism.L2.Host.IsUnitAt P (atFin P x) := by
    show Valued.v (algebraMap E (P.adicCompletion E) (x : E)) = 1
    have hc : Valued.v ((algebraMap E (P.adicCompletion E)) (x : E)) = P.valuation E (x : E) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) P (x : E)
    rw [hc, hx]
    exact val_eq_one hbP
  have hyU : finAf F E (Neutral.B1.localIdele E P (atFin P x)) ∈ intU F E :=
    (GlobalTheory.Mem.ReadTwist.finAf_mem_intU_iff _).mpr (GlobalTheory.Mem.ReadTwist.local_mem_unitIdl hux)
  let u : (RInt F E)ˣ := Submonoid.unitsEquivUnitsType _ ⟨_, hyU⟩
  have hu : ((u : RInt F E) : AfE F E) = (finAf F E (Neutral.B1.localIdele E P (atFin P x)) : AfE F E) := rfl
  have hs : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E (P.under (𝓞 F)) :=
    GlobalTheory.Mem.ReadTwist.local_mem_suppAt P _
  have hA : (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) := by
    apply hM
    rw [AddSubgroupClass.coe_sub, map_sub, hu, p1]
    show afIso F E _ P - afIso F E _ P = 0
    rw [p3, p2]
    show algebraMap E (P.adicCompletion E) (x : E) - _ = 0
    rw [hx, sub_self]
  have hB : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → (u : RInt F E) - 1 ∈ Q.asIdeal.map (toRInt F E) := by
    intro Q hQ
    apply hM
    rw [AddSubgroupClass.coe_sub, map_sub, hu, OneMemClass.coe_one, map_one]
    show afIso F E _ Q - 1 = 0
    rw [p4 _ Q hQ, sub_self]
  have hex := exists_isResChar h ht P
  have hIs := hex.choose_spec (P.under (𝓞 F)) rfl u a b hb hs hA hB
  have hv := (value_of_congr h ht (u := Units.map (RInt F E).subtype.toMonoidHom u) (y := (u : RInt F E)) rfl hbP hx hA hB).2
  rw [Formalism.L2.DIV.resChar, dif_pos hex, ← hIs]
  exact hv

/- English proof (translation)
Establish `h1 : ∀ (w : InfinitePlace E) (y : (w.Completion)ˣ), finAf F E (infIdele E w y) = 1`. Introduce `w y`. Apply `Units.ext` to reduce the goal to its premises. Apply `(afIso F E).injective` to reduce the goal to its premises. Rewrite using `[afIso_finAf, Units.val_one, map_one]`.

Both sides reduce to the same expression. Establish `hfin : finAf F E (Formalism.L2.Host.infDiag x) = 1`. Rewrite using `[Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply, map_prod]`. Conclude with `Finset.prod_eq_one fun w _ => h1 w _`. Apply `Units.ext` to reduce the goal to its premises.

Use `h (Formalism.L2.Host.infDiag x)` as an intermediate fact. Rewrite `this` using `[hfin, map_one, Units.val_one, map_one]`. Conclude with `this`.
-/
theorem inf_eq_one (h : Reads σ μ ξ) (x : Eˣ) : ξ.inf x = 1 := by
  have h1 : ∀ (w : InfinitePlace E) (y : (w.Completion)ˣ), finAf F E (infIdele E w y) = 1 := by
    intro w y
    apply Units.ext
    apply (afIso F E).injective
    rw [afIso_finAf, Units.val_one, map_one]
    rfl
  have hfin : finAf F E (Formalism.L2.Host.infDiag x) = 1 := by
    rw [Formalism.L2.Host.infDiag, MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun w _ => h1 w _
  apply Units.ext
  have := h (Formalism.L2.Host.infDiag x)
  rw [hfin, map_one, Units.val_one, map_one] at this
  exact this

end Res

section Main

variable {X : Fields} {Pr : Primes X}

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace X.E))`. Apply `InfinitePlace.not_isReal_iff_isComplex.mpr (hX.cplxE.isComplex w)` to reduce the goal to its premises. Rewrite using `[InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, hne]`.
-/
theorem exists_star_ne (hX : X.Ok) : ∃ a : X.E, star a ≠ a := by
  by_contra hne
  push Not at hne
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace X.E))
  apply InfinitePlace.not_isReal_iff_isComplex.mpr (hX.cplxE.isComplex w)
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, hne]

/- English proof (translation)
Establish `key : ∀ a : E, z * star (a + z * star a) = a + z * star a`. Introduce `a`. Rewrite using `[star_add, star_mul, star_star]`. Take the linear combination `a * hz`. Distinguish the cases in `h1 : (1 : E) + z * star 1 = 0`.

Take `⟨a, ha⟩` from `hc`. Establish `hz1 : z = -1`. Rewrite `h1` using `[star_one, mul_one]`. Take the linear combination `h1`. Establish `h0 : a + z * star a ≠ 0`.

Rewrite using `[hz1]`. Introduce `h0`. Apply `ha` to reduce the goal to its premises. Take the linear combination `-h0`. Conclude with `⟨Units.mk0 _ h0, (key a).symm⟩`.

Conclude with `⟨Units.mk0 _ h1, (key 1).symm⟩`.
-/
theorem exists_quot {E : Type} [Field E] [CharZero E] [StarRing E] (hc : ∃ a : E, star a ≠ a) {z : E} (hz : z * star z = 1) :
    ∃ x : Eˣ, (x : E) = z * star (x : E) := by
  have key : ∀ a : E, z * star (a + z * star a) = a + z * star a := by
    intro a
    rw [star_add, star_mul, star_star]
    linear_combination a * hz
  by_cases h1 : (1 : E) + z * star 1 = 0
  · obtain ⟨a, ha⟩ := hc
    have hz1 : z = -1 := by
      rw [star_one, mul_one] at h1
      linear_combination h1
    have h0 : a + z * star a ≠ 0 := by
      rw [hz1]
      intro h0
      apply ha
      linear_combination -h0
    exact ⟨Units.mk0 _ h0, (key a).symm⟩
  · exact ⟨Units.mk0 _ h1, (key 1).symm⟩

/- English proof (translation)
Unfold `Primes.vGs at h`. Break down `Finset.mem_union.mp h with h | h` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations. Unfold `Primes.vG divs at h`. Use `split_ifs at h with hf`.

Conclude with `hf.mem_toFinset.mp h`. Simplify using `at h`. Use `⟨1, ?_⟩` and prove the remaining obligations. Unfold `Primes.vG divs at h`. Use `split_ifs at h with hf`.

Conclude with `hf.mem_toFinset.mp h`. Simplify using `at h`.
-/
theorem mem_vGs {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) : ∃ i, X.conjO (Pr.piG i) ∈ P.asIdeal := by
  classical
  unfold Primes.vGs at h
  rcases Finset.mem_union.mp h with h | h
  · refine ⟨0, ?_⟩
    unfold Primes.vG divs at h
    split_ifs at h with hf
    · exact hf.mem_toFinset.mp h
    · simp at h
  · refine ⟨1, ?_⟩
    unfold Primes.vG divs at h
    split_ifs at h with hf
    · exact hf.mem_toFinset.mp h
    · simp at h

/- English proof (translation)
Introduce `hc`. Take `⟨i, hi⟩` from `mem_vGs h`. Take `⟨j, hj⟩` from `mem_vGs hc`. Rewrite `hj` using `[mem_conjP]`. Establish `hcc : cO X.E (X.conjO (Pr.piG j)) = Pr.piG j` using `RingOfIntegers.ext (by simp [cO, Fields.conjO, RingOfIntegers.mapRingHom_apply])`.

Rewrite `hj` using `[hcc]`. Establish `hone : ∀ a b : 𝓞 X.E, IsCoprime a b → a ∈ P.asIdeal → b ∈ P.asIdeal → False`. Introduce `a b hab ha hb`. Take `⟨u, v, huv⟩` from `hab`. Apply `P.isPrime.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one, ← huv]`. Conclude with `P.asIdeal.add_mem (P.asIdeal.mul_mem_left u ha) (P.asIdeal.mul_mem_left v hb)`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Conclude with `hone _ _ (hPr.piG_cop i) hj hi`.

Establish `hgi : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal`. Rewrite using `[← hPr.piG_norm i]`. Conclude with `P.asIdeal.mul_mem_left _ hi`. Establish `hgj : ((Pr.g j : ℕ) : 𝓞 X.E) ∈ P.asIdeal`. Rewrite using `[← hPr.piG_norm j]`.

Conclude with `P.asIdeal.mul_mem_right _ hj`. Establish `hne : Pr.g i ≠ Pr.g j`. Establish `h01` using `hPr.g_ne`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all [eq_comm]`. Establish `hcop : IsCoprime ((Pr.g i : ℕ) : 𝓞 X.E) ((Pr.g j : ℕ) : 𝓞 X.E)`.

Establish `hz : IsCoprime ((Pr.g i : ℕ) : ℤ) ((Pr.g j : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).mpr hne)`. Simplify using `using hz.map (Int.castRingHom (𝓞 X.E))`. Conclude with `hone _ _ hcop hgi hgj`.
-/
theorem conjP_notMem_vGs (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) : conjPrime₂ P ∉ Pr.vGs := by
  intro hc
  obtain ⟨i, hi⟩ := mem_vGs h
  obtain ⟨j, hj⟩ := mem_vGs hc
  rw [mem_conjP] at hj
  have hcc : cO X.E (X.conjO (Pr.piG j)) = Pr.piG j :=
    RingOfIntegers.ext (by simp [cO, Fields.conjO, RingOfIntegers.mapRingHom_apply])
  rw [hcc] at hj
  have hone : ∀ a b : 𝓞 X.E, IsCoprime a b → a ∈ P.asIdeal → b ∈ P.asIdeal → False := by
    intro a b hab ha hb
    obtain ⟨u, v, huv⟩ := hab
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left u ha) (P.asIdeal.mul_mem_left v hb)
  by_cases hij : i = j
  · subst hij
    exact hone _ _ (hPr.piG_cop i) hj hi
  · have hgi : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
      rw [← hPr.piG_norm i]
      exact P.asIdeal.mul_mem_left _ hi
    have hgj : ((Pr.g j : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
      rw [← hPr.piG_norm j]
      exact P.asIdeal.mul_mem_right _ hj
    have hne : Pr.g i ≠ Pr.g j := by
      have h01 := hPr.g_ne
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    have hcop : IsCoprime ((Pr.g i : ℕ) : 𝓞 X.E) ((Pr.g j : ℕ) : 𝓞 X.E) := by
      have hz : IsCoprime ((Pr.g i : ℕ) : ℤ) ((Pr.g j : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).mpr hne)
      simpa using hz.map (Int.castRingHom (𝓞 X.E))
    exact hone _ _ hcop hgi hgj

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} (mu : Tup X.F X.E X.K S)

/- English proof (translation)
Unfold `QE at h`. Use `split_ifs at h with hfin`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.mp h`. Establish `hu : HeightOneSpectrum.under (𝓞 X.F) (sel v) = v` using `HeightOneSpectrum.ext (hsel v)`. Rewrite using `[hu]`.

Use `⟨rfl, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hg`. Establish `hv' : v ∈ Qprime (mu : Chr X.F X.E X.K)` using `hfin.mem_toFinset.mp hv`. Apply `hv'` to reduce the goal to its premises. Establish `hm` using `mu.2`.

Simplify using `only [tupGrp, Subgroup.mem_inf, Subgroup.mem_iInf] at hm`. Conclude with `mem_kills.mp (hm.2 v hg)`. Simplify using `at h`.
-/
theorem mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    sel (P.under (𝓞 X.F)) = P ∧ GoodPl X.E S (P.under (𝓞 X.F)) := by
  classical
  unfold QE at h
  split_ifs at h with hfin
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    have hu : HeightOneSpectrum.under (𝓞 X.F) (sel v) = v := HeightOneSpectrum.ext (hsel v)
    rw [hu]
    refine ⟨rfl, ?_⟩
    by_contra hg
    have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := hfin.mem_toFinset.mp hv
    apply hv'
    have hm := mu.2
    simp only [tupGrp, Subgroup.mem_inf, Subgroup.mem_iInf] at hm
    exact mem_kills.mp (hm.2 v hg)
  · simp at h

/- English proof (translation)
Introduce `hc`. Take `⟨h1, h2⟩` from `mem_QE mu hsel h`. Take `⟨h3, -⟩` from `mem_QE mu hsel hc`. Establish `hcx` using `exists_star_ne hX`. Establish `hu : (conjPrime₂ P).under (𝓞 X.F) = P.under (𝓞 X.F)` using `(under_eq_iff hX.star_F hX.rankE hcx P (conjPrime₂ P)).mpr (Or.inr rfl)`.

Establish `hPP : conjPrime₂ P = P` using `by rw [← h3, hu, h1]`. Take `⟨⟨P1, P2, hne, hmap⟩, -, -⟩` from `h2`. Establish `key : ∀ Q : HeightOneSpectrum (𝓞 X.E), Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) (P.under (𝓞 X.F)).asIdeal ≤ Q.asIdeal → Q = P`. Introduce `Q hQ`. Establish `hQu : Q.under (𝓞 X.F) = P.under (𝓞 X.F)`.

Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Conclude with `((P.under (𝓞 X.F)).isMaximal.eq_of_le (Q.under (𝓞 X.F)).isPrime.ne_top (Ideal.map_le_iff_le_comap.mp hQ)).symm`. Break down `(under_eq_iff hX.star_F hX.rankE hcx P Q).mp hQu with hq | hq` into its components or cases. Conclude with `hq`. Rewrite using `[hq, hPP]`.

Conclude with `hne ((key P1 (hmap ▸ Ideal.mul_le_inf.trans inf_le_left)).trans (key P2 (hmap ▸ Ideal.mul_le_inf.trans inf_le_right)).symm)`.
-/
theorem conjP_notMem_QE (hX : X.Ok) (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)}
    (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) : conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) := by
  intro hc
  obtain ⟨h1, h2⟩ := mem_QE mu hsel h
  obtain ⟨h3, -⟩ := mem_QE mu hsel hc
  have hcx := exists_star_ne hX
  have hu : (conjPrime₂ P).under (𝓞 X.F) = P.under (𝓞 X.F) :=
    (under_eq_iff hX.star_F hX.rankE hcx P (conjPrime₂ P)).mpr (Or.inr rfl)
  have hPP : conjPrime₂ P = P := by rw [← h3, hu, h1]
  obtain ⟨⟨P1, P2, hne, hmap⟩, -, -⟩ := h2
  have key : ∀ Q : HeightOneSpectrum (𝓞 X.E),
      Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) (P.under (𝓞 X.F)).asIdeal ≤ Q.asIdeal → Q = P := by
    intro Q hQ
    have hQu : Q.under (𝓞 X.F) = P.under (𝓞 X.F) := by
      apply HeightOneSpectrum.ext
      exact ((P.under (𝓞 X.F)).isMaximal.eq_of_le (Q.under (𝓞 X.F)).isPrime.ne_top
        (Ideal.map_le_iff_le_comap.mp hQ)).symm
    rcases (under_eq_iff hX.star_F hX.rankE hcx P Q).mp hQu with hq | hq
    · exact hq
    · rw [hq, hPP]
  exact hne ((key P1 (hmap ▸ Ideal.mul_le_inf.trans inf_le_left)).trans (key P2 (hmap ▸ Ideal.mul_le_inf.trans inf_le_right)).symm)

/- English proof (translation)
Rewrite using `[Finset.disjoint_left]`. Introduce `P hP hQ`. Take `⟨-, -, -, hplc⟩` from `mem_QE mu hsel hQ`. Take `⟨i, hi⟩` from `mem_vGs hP`. Apply `hplc` to reduce the goal to its premises.

Establish `hgE : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal`. Rewrite using `[← hPr.piG_norm i]`. Conclude with `P.asIdeal.mul_mem_left _ hi`. Establish `hgF : ((Pr.g i : ℕ) : 𝓞 X.F) ∈ (P.under (𝓞 X.F)).asIdeal` using `by show _ ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) P.asIdeal`. Rewrite using `[Ideal.mem_comap, map_natCast]`.

Conclude with `hgE`. Establish `hchar : ringChar (𝓞 X.F ⧸ (P.under (𝓞 X.F)).asIdeal) = Pr.g i`. Establish `hz : ((Pr.g i : ℕ) : 𝓞 X.F ⧸ (P.under (𝓞 X.F)).asIdeal) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hgF`.

Establish `hd` using `(ringChar.spec (𝓞 X.F ⧸ (P.under (𝓞 X.F)).asIdeal) (Pr.g i)).mp hz`. Break down `(hPr.g_prime i).eq_one_or_self_of_dvd _ hd with h1 | h1` into its components or cases. It suffices to derive a contradiction. Use `(ringChar.spec (𝓞 X.F ⧸ (P.under (𝓞 X.F)).asIdeal) 1).mpr (by rw [h1])` as an intermediate fact. Simplify using `at this`.

Conclude with `h1`. Unfold `Formalism.EigenvalueLevelCeiling.plc`. Rewrite using `[hchar]`. Conclude with `hS i`.
-/
theorem disjoint_vGs_QE (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) :
    Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)) := by
  rw [Finset.disjoint_left]
  intro P hP hQ
  obtain ⟨-, -, -, hplc⟩ := mem_QE mu hsel hQ
  obtain ⟨i, hi⟩ := mem_vGs hP
  apply hplc
  have hgE : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
    rw [← hPr.piG_norm i]
    exact P.asIdeal.mul_mem_left _ hi
  have hgF : ((Pr.g i : ℕ) : 𝓞 X.F) ∈ (P.under (𝓞 X.F)).asIdeal := by
    show _ ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) P.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hgE
  have hchar : ringChar (𝓞 X.F ⧸ (P.under (𝓞 X.F)).asIdeal) = Pr.g i := by
    have hz : ((Pr.g i : ℕ) : 𝓞 X.F ⧸ (P.under (𝓞 X.F)).asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
      exact hgF
    have hd := (ringChar.spec (𝓞 X.F ⧸ (P.under (𝓞 X.F)).asIdeal) (Pr.g i)).mp hz
    rcases (hPr.g_prime i).eq_one_or_self_of_dvd _ hd with h1 | h1
    · exfalso
      have := (ringChar.spec (𝓞 X.F ⧸ (P.under (𝓞 X.F)).asIdeal) 1).mpr (by rw [h1])
      simp at this
    · exact h1
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [hchar]
  exact hS i

/- English proof (translation)
Establish `hmu` using `(mu : Tup X.F X.E X.K S).2`. Take `⟨⟨⟨⟨⟨_, hopen⟩, _⟩, hid⟩, hwild⟩, _⟩` from `hmu`. Establish `hw : ∀ v, Formalism.L2.DIV.wildAt X.E v ≤ (mu : Chr X.F X.E X.K).ker` using `fun v => Formalism.L2.DIV.mem_kills.mp (Subgroup.mem_iInf.mp hwild v)`. Establish `hid' : (Formalism.L2.DIV.idF X.F X.E).range ≤ (mu : Chr X.F X.E X.K).ker` using `Formalism.L2.DIV.mem_kills.mp hid`. Establish `ht : ∀ P, ξ.TameAt P` using `GlobalTheory.Mem.ReadTwist.tameAt h hw`.

Establish `hF : ξ.TrivOn X.F` using `GlobalTheory.Mem.ReadTwist.trivOn h hid'`. Establish `hfin : (Qprime (mu : Chr X.F X.E X.K)).Finite`. Use `((GlobalTheory.Mem.UnrAe.finite_ramified ξ).image (fun P => P.under (𝓞 X.F))).subset ?_` and prove the remaining obligations. Introduce `v hv`. Take `⟨P, hP, hn⟩` from `(GlobalTheory.Mem.ReadTwist.mem_qprime_iff h v).mp hv`.

Conclude with `⟨P, hn, hP⟩`. Establish `hc` using `exists_star_ne hX`. Establish `hun : ∀ P, P ∉ QE sel (mu : Chr X.F X.E X.K) → conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) → ξ.UnrAt P`. Introduce `P h1 h2`. Assume the negation of the conclusion as `hn`.

Establish `hq : P.under (𝓞 X.F) ∈ Qprime (mu : Chr X.F X.E X.K)` using `(GlobalTheory.Mem.ReadTwist.mem_qprime_iff h _).mpr ⟨P, rfl, hn⟩`. Establish `hs : sel (P.under (𝓞 X.F)) ∈ QE sel (mu : Chr X.F X.E X.K)` using `by classical`. Unfold `QE`. Rewrite using `[dif_pos hfin]`. Conclude with `Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr hq, rfl⟩`.

Establish `hu' : (sel (P.under (𝓞 X.F))).under (𝓞 X.F) = P.under (𝓞 X.F)`. Conclude with `HeightOneSpectrum.ext (hsel _)`. Break down `(under_eq_iff hX.star_F hX.rankE hc P (sel _)).mp hu' with h3 | h3` into its components or cases. Conclude with `h1 (h3 ▸ hs)`. Conclude with `h2 (h3 ▸ hs)`.

Establish `key` using `inf_mul_prod hX.star_F hX.rankE hc hu hF ht (fun P hP => conjP_notMem_QE mu hX hsel hP) hun hxz hz`. Rewrite `key` using `[inf_eq_one h x, one_mul]`. Then use the resulting hypothesis.
-/
theorem prod_twist (hX : X.Ok) (hsel : IsSel X sel)
    (hu : ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1) {σ₀ : X.K →+* ℂ} {ξ : HChar X.E}
    (h : GlobalTheory.Mem.Col2.Reads σ₀ (mu : Chr X.F X.E X.K) ξ) {x z : X.Eˣ} (hxz : (x : X.E) = z * star (x : X.E))
    (hz : ∀ P : HeightOneSpectrum (𝓞 X.E), P.valuation X.E (z : X.E) = 1) :
    ∏ P ∈ QE sel (mu : Chr X.F X.E X.K), ξ.locK P z = 1 := by
  have hmu := (mu : Tup X.F X.E X.K S).2
  obtain ⟨⟨⟨⟨⟨_, hopen⟩, _⟩, hid⟩, hwild⟩, _⟩ := hmu
  have hw : ∀ v, Formalism.L2.DIV.wildAt X.E v ≤ (mu : Chr X.F X.E X.K).ker := fun v =>
    Formalism.L2.DIV.mem_kills.mp (Subgroup.mem_iInf.mp hwild v)
  have hid' : (Formalism.L2.DIV.idF X.F X.E).range ≤ (mu : Chr X.F X.E X.K).ker := Formalism.L2.DIV.mem_kills.mp hid
  have ht : ∀ P, ξ.TameAt P := GlobalTheory.Mem.ReadTwist.tameAt h hw
  have hF : ξ.TrivOn X.F := GlobalTheory.Mem.ReadTwist.trivOn h hid'
  have hfin : (Qprime (mu : Chr X.F X.E X.K)).Finite := by
    refine ((GlobalTheory.Mem.UnrAe.finite_ramified ξ).image (fun P => P.under (𝓞 X.F))).subset ?_
    intro v hv
    obtain ⟨P, hP, hn⟩ := (GlobalTheory.Mem.ReadTwist.mem_qprime_iff h v).mp hv
    exact ⟨P, hn, hP⟩
  have hc := exists_star_ne hX
  have hun : ∀ P, P ∉ QE sel (mu : Chr X.F X.E X.K) → conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) → ξ.UnrAt P := by
    intro P h1 h2
    by_contra hn
    have hq : P.under (𝓞 X.F) ∈ Qprime (mu : Chr X.F X.E X.K) :=
      (GlobalTheory.Mem.ReadTwist.mem_qprime_iff h _).mpr ⟨P, rfl, hn⟩
    have hs : sel (P.under (𝓞 X.F)) ∈ QE sel (mu : Chr X.F X.E X.K) := by
      classical
      unfold QE
      rw [dif_pos hfin]
      exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr hq, rfl⟩
    have hu' : (sel (P.under (𝓞 X.F))).under (𝓞 X.F) = P.under (𝓞 X.F) := by
      exact HeightOneSpectrum.ext (hsel _)
    rcases (under_eq_iff hX.star_F hX.rankE hc P (sel _)).mp hu' with h3 | h3
    · exact h1 (h3 ▸ hs)
    · exact h2 (h3 ▸ hs)
  have key := inf_mul_prod hX.star_F hX.rankE hc hu hF ht (fun P hP => conjP_notMem_QE mu hX hsel hP) hun hxz hz
  rwa [inf_eq_one h x, one_mul] at key

end Main

open Classical in

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cs σ₀ e m0 eta hX hPr hsel hS hu hT j z hz hzi`. Establish `hzs : IsIntegral ℤ (star z)` using `hzi.map (starRingEnd X.E).toIntAlgHom`. Establish `hbb : (⟨z, hzi⟩ : 𝓞 X.E) * ⟨star z, hzs⟩ = 1` using `by ext1`. Conclude with `hz`. Establish `hunit : ∀ P : HeightOneSpectrum (𝓞 X.E), IsUnit (redP P z)`.

Introduce `P`. Establish `h1 : redP P z = Ideal.Quotient.mk P.asIdeal (⟨z, hzi⟩ : 𝓞 X.E)` using `reduction_coe P ⟨z, hzi⟩`. Establish `hm : Ideal.Quotient.mk P.asIdeal (⟨z, hzi⟩ : 𝓞 X.E) * Ideal.Quotient.mk P.asIdeal ⟨star z, hzs⟩ = 1` using `(map_mul (Ideal.Quotient.mk P.asIdeal) _ _).symm.trans ((congrArg _ hbb).trans (map_one _))`. Rewrite using `[h1]`. Conclude with `⟨⟨_, _, hm, (mul_comm _ _).trans hm⟩, rfl⟩`.

Establish `hmv : ∀ P : rowSG Pr sel mu, muAt Ch sel mu cs j.1 P z = (((if P.1 ∈ Pr.vGs then chiP Ch P.1 j.1 else (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹) (hunit P.1).unit : X.Kˣ) : X.K)`. Introduce `P`. Unfold `muAt`. Rewrite using `[GlobalTheory.LastSteps.locChar_unit _ _ (hunit P.1)]`. Unfold `LocE.unitV`.

Rewrite using `[dif_pos (hunit P.1)]`. Establish `hdis` using `disjoint_vGs_QE mu hPr hsel hS`. Establish `hsplit : σ₀ (∏ P : rowSG Pr sel mu, muAt Ch sel mu cs j.1 P z) = (∏ w ∈ Pr.vGs, σ₀ ((chiP Ch w j.1 (hunit w).unit : X.Kˣ) : X.K)) * ∏ P ∈ QE sel (mu : Chr X.F X.E X.K), σ₀ (((resChar (mu : Chr X.F X.E X.K) P)⁻¹ (hunit P).unit : X.Kˣ) : X.K)`. Rewrite using `[map_prod, Finset.prod_congr rfl (fun P _ => by rw [hmv P])]`. Rewrite using `[Finset.prod_coe_sort (rowSG Pr sel mu) (fun P => σ₀ ((((if P ∈ Pr.vGs then chiP Ch P j.1 else (resChar (mu : Chr X.F X.E X.K) P)⁻¹) (hunit P).unit : X.Kˣ) : X.K)))]`.

Rewrite using `[show rowSG Pr sel mu = Pr.vGs ∪ QE sel (mu : Chr X.F X.E X.K) from rfl, Finset.prod_union hdis]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl (fun w hw => by rw [if_pos hw])`. Conclude with `Finset.prod_congr rfl (fun P hP => by rw [if_neg (Finset.disjoint_right.mp hdis hP)])`. Establish `hzu : z * star z = 1` using `hz`.

Set `zu : X.Eˣ` to `⟨z, star z, hz, (mul_comm _ _).trans hz⟩`. Establish `hmu0` using `hT.mu0 j`. Establish `hG : ∀ w ∈ Pr.vGs, σ₀ ((chiP Ch w j.1 (hunit w).unit : X.Kˣ) : X.K) = (((m0 j).locK w zu : ℂˣ) : ℂ)⁻¹`. Introduce `w hw`. Establish `ha` using `hmu0.atg ⟨w, hw⟩ zu ⟨z, hzi⟩ (hunit w).unit rfl (by rw [IsUnit.unit_spec]; exact reduction_coe w ⟨z, hzi⟩)`.

Rewrite using `[ha]`. Simplify using `only [chiP, chiAt, extChi, dif_pos hw, dif_pos j.2, Fin.eta, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]`. Establish `hbP : ∀ P : HeightOneSpectrum (𝓞 X.E), (⟨z, hzi⟩ : 𝓞 X.E) ∉ P.asIdeal` using `fun P hb => P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hb ⟨⟨_, _, hbb, (mul_comm _ _).trans hbb⟩, rfl⟩)`. Establish `hzv : ∀ P : HeightOneSpectrum (𝓞 X.E), P.valuation X.E (zu : X.E) = 1` using `fun P => val_eq_one (b := (⟨z, hzi⟩ : 𝓞 X.E)) (hbP P)`. Take `⟨x, hx⟩` from `exists_quot (exists_star_ne hX) hz`.

Establish `hunr : ∀ P, P ∉ Pr.vGs → conjPrime₂ P ∉ Pr.vGs → (m0 j).UnrAt P` using `fun P h1 h2 => hmu0.unr P (fun i => GlobalTheory.MuConj.g_notMem hPr P h1 h2 i)`. Establish `key` using `inf_mul_prod hX.star_F hX.rankE (exists_star_ne hX) hu hmu0.triv hmu0.tame (fun P hP => conjP_notMem_vGs hPr hP) hunr (x := x) (z := zu) hx hzv`. Take `⟨⟨⟨⟨⟨hrat, hopen⟩, _⟩, _⟩, hwild⟩, _⟩` from `(mu : Tup X.F X.E X.K S).2`. Take `⟨ξ, hξ⟩` from `GlobalTheory.Mem.ReadEx.exists_reads σ₀ (mu : Chr X.F X.E X.K) (Formalism.L2.DIV.mem_kills.mp hrat) hopen`. Establish `htξ : ∀ P, ξ.TameAt P` using `GlobalTheory.Mem.ReadTwist.tameAt hξ (fun v => Formalism.L2.DIV.mem_kills.mp (Subgroup.mem_iInf.mp hwild v))`.

Establish `htw` using `prod_twist mu hX hsel hu hξ hx hzv`. Establish `hQ : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), σ₀ (((resChar (mu : Chr X.F X.E X.K) P)⁻¹ (hunit P).unit : X.Kˣ) : X.K) = (((ξ.locK P zu : ℂˣ) : ℂ))⁻¹`. Introduce `P _`. Rewrite using `[MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, resChar_eq hξ htξ P _ ⟨z, hzi⟩ zu rfl (by rw [IsUnit.unit_spec]; exact (reduction_coe P ⟨z, hzi⟩).symm)]`. Establish `hQ1 : ∏ P ∈ QE sel (mu : Chr X.F X.E X.K), (((ξ.locK P zu : ℂˣ) : ℂ))⁻¹ = 1`.

Rewrite using `[Finset.prod_inv_distrib, ← Units.coe_prod, htw, Units.val_one, inv_one]`. Establish `hG1 : ∏ w ∈ Pr.vGs, (((m0 j).locK w zu : ℂˣ) : ℂ)⁻¹ = (((m0 j).inf x : ℂˣ) : ℂ)`. Rewrite using `[Finset.prod_inv_distrib, ← Units.coe_prod, eq_inv_of_mul_eq_one_right key, Units.val_inv_eq_inv_val, inv_inv]`. Rewrite using `[hsplit, Finset.prod_congr rfl hG, Finset.prod_congr rfl hQ, hQ1, mul_one, hG1]`. Take `⟨n, hn, hinf⟩` from `hmu0.inf`.

Rewrite using `[hinf x]`. Use `Finset.prod_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Establish `hn' : n τ = 2 * -(e j τ)`. Establish `h3` using `hn τ`. Simplify using `only at h3`.

Conclude with `h3` after adjusting the coercions. Establish `ha : (X.embC σ₀ τ) (x : X.E) ≠ 0` using `(map_ne_zero _).mpr x.ne_zero`. Establish `hc0 : starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E)) ≠ 0` using `(map_ne_zero _).mpr ha`. Establish `hcj : (X.embC σ₀ τ) (star (x : X.E)) = starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E))` using `hX.conjE _ _`. Establish `hzφ : (X.embC σ₀ τ) z = (X.embC σ₀ τ) (x : X.E) / starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E))`.

Establish `h2 : (X.embC σ₀ τ) (x : X.E) = (X.embC σ₀ τ) z * starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E))`. Rewrite using `[← hcj, ← map_mul, ← hx]`. Rewrite using `[eq_div_iff hc0, ← h2]`. Establish `hsq : ((X.embC σ₀ τ) (x : X.E) / ((‖(X.embC σ₀ τ) (x : X.E)‖ : ℝ) : ℂ)) ^ (2 : ℤ) = (X.embC σ₀ τ) (x : X.E) / starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E))`. Establish `hnorm : ((‖(X.embC σ₀ τ) (x : X.E)‖ : ℝ) : ℂ) ^ 2 = (X.embC σ₀ τ) (x : X.E) * starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E))`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[zpow_two, div_mul_div_comm, ← pow_two, ← pow_two, hnorm, div_eq_div_iff (mul_ne_zero ha hc0) hc0]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hn', zpow_mul, hsq, ← hzφ]`.
-/
theorem prod_muAt : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (e : Fin R.m → X.Tau → ℤ) (m0 : Fin R.m → Formalism.L2.Host.HChar X.E) (eta : Formalism.L2.Host.HChar X.E), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1) → Ch.Tied σ₀ (fun j τ => (e j τ : ℚ)) m0 eta → ∀ (j : Fin R.m) (z : X.E), z * star z = 1 → IsIntegral ℤ z → σ₀ (∏ P : rowSG Pr sel mu, muAt Ch sel mu cst j.1 P z) = ∏ τ, X.embC σ₀ τ z ^ (-(e j τ)) := by
  intro X Pr R Ch sel S mu cs σ₀ e m0 eta hX hPr hsel hS hu hT j z hz hzi
  have hzs : IsIntegral ℤ (star z) := hzi.map (starRingEnd X.E).toIntAlgHom
  have hbb : (⟨z, hzi⟩ : 𝓞 X.E) * ⟨star z, hzs⟩ = 1 := by
    ext1
    exact hz
  have hunit : ∀ P : HeightOneSpectrum (𝓞 X.E), IsUnit (redP P z) := by
    intro P
    have h1 : redP P z = Ideal.Quotient.mk P.asIdeal (⟨z, hzi⟩ : 𝓞 X.E) := reduction_coe P ⟨z, hzi⟩
    have hm : Ideal.Quotient.mk P.asIdeal (⟨z, hzi⟩ : 𝓞 X.E) * Ideal.Quotient.mk P.asIdeal ⟨star z, hzs⟩ = 1 :=
      (map_mul (Ideal.Quotient.mk P.asIdeal) _ _).symm.trans ((congrArg _ hbb).trans (map_one _))
    rw [h1]
    exact ⟨⟨_, _, hm, (mul_comm _ _).trans hm⟩, rfl⟩
  have hmv : ∀ P : rowSG Pr sel mu, muAt Ch sel mu cs j.1 P z =
      (((if P.1 ∈ Pr.vGs then chiP Ch P.1 j.1 else (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹)
        (hunit P.1).unit : X.Kˣ) : X.K) := by
    intro P
    unfold muAt
    rw [GlobalTheory.LastSteps.locChar_unit _ _ (hunit P.1)]
    unfold LocE.unitV
    rw [dif_pos (hunit P.1)]
  have hdis := disjoint_vGs_QE mu hPr hsel hS
  have hsplit : σ₀ (∏ P : rowSG Pr sel mu, muAt Ch sel mu cs j.1 P z) =
      (∏ w ∈ Pr.vGs, σ₀ ((chiP Ch w j.1 (hunit w).unit : X.Kˣ) : X.K)) *
      ∏ P ∈ QE sel (mu : Chr X.F X.E X.K),
        σ₀ (((resChar (mu : Chr X.F X.E X.K) P)⁻¹ (hunit P).unit : X.Kˣ) : X.K) := by
    rw [map_prod, Finset.prod_congr rfl (fun P _ => by rw [hmv P])]
    rw [Finset.prod_coe_sort (rowSG Pr sel mu) (fun P => σ₀ ((((if P ∈ Pr.vGs then chiP Ch P j.1
      else (resChar (mu : Chr X.F X.E X.K) P)⁻¹) (hunit P).unit : X.Kˣ) : X.K)))]
    rw [show rowSG Pr sel mu = Pr.vGs ∪ QE sel (mu : Chr X.F X.E X.K) from rfl, Finset.prod_union hdis]
    congr 1
    · exact Finset.prod_congr rfl (fun w hw => by rw [if_pos hw])
    · exact Finset.prod_congr rfl (fun P hP => by rw [if_neg (Finset.disjoint_right.mp hdis hP)])
  have hzu : z * star z = 1 := hz
  let zu : X.Eˣ := ⟨z, star z, hz, (mul_comm _ _).trans hz⟩
  have hmu0 := hT.mu0 j
  have hG : ∀ w ∈ Pr.vGs, σ₀ ((chiP Ch w j.1 (hunit w).unit : X.Kˣ) : X.K) =
      (((m0 j).locK w zu : ℂˣ) : ℂ)⁻¹ := by
    intro w hw
    have ha := hmu0.atg ⟨w, hw⟩ zu ⟨z, hzi⟩ (hunit w).unit rfl
      (by rw [IsUnit.unit_spec]; exact reduction_coe w ⟨z, hzi⟩)
    rw [ha]
    simp only [chiP, chiAt, extChi, dif_pos hw, dif_pos j.2, Fin.eta, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
  have hbP : ∀ P : HeightOneSpectrum (𝓞 X.E), (⟨z, hzi⟩ : 𝓞 X.E) ∉ P.asIdeal := fun P hb =>
    P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hb ⟨⟨_, _, hbb, (mul_comm _ _).trans hbb⟩, rfl⟩)
  have hzv : ∀ P : HeightOneSpectrum (𝓞 X.E), P.valuation X.E (zu : X.E) = 1 := fun P =>
    val_eq_one (b := (⟨z, hzi⟩ : 𝓞 X.E)) (hbP P)
  obtain ⟨x, hx⟩ := exists_quot (exists_star_ne hX) hz
  have hunr : ∀ P, P ∉ Pr.vGs → conjPrime₂ P ∉ Pr.vGs → (m0 j).UnrAt P := fun P h1 h2 =>
    hmu0.unr P (fun i => GlobalTheory.MuConj.g_notMem hPr P h1 h2 i)
  have key := inf_mul_prod hX.star_F hX.rankE (exists_star_ne hX) hu hmu0.triv hmu0.tame
    (fun P hP => conjP_notMem_vGs hPr hP) hunr (x := x) (z := zu) hx hzv
  obtain ⟨⟨⟨⟨⟨hrat, hopen⟩, _⟩, _⟩, hwild⟩, _⟩ := (mu : Tup X.F X.E X.K S).2
  obtain ⟨ξ, hξ⟩ := GlobalTheory.Mem.ReadEx.exists_reads σ₀ (mu : Chr X.F X.E X.K) (Formalism.L2.DIV.mem_kills.mp hrat) hopen
  have htξ : ∀ P, ξ.TameAt P := GlobalTheory.Mem.ReadTwist.tameAt hξ (fun v =>
    Formalism.L2.DIV.mem_kills.mp (Subgroup.mem_iInf.mp hwild v))
  have htw := prod_twist mu hX hsel hu hξ hx hzv
  have hQ : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K),
      σ₀ (((resChar (mu : Chr X.F X.E X.K) P)⁻¹ (hunit P).unit : X.Kˣ) : X.K) = (((ξ.locK P zu : ℂˣ) : ℂ))⁻¹ := by
    intro P _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀,
      resChar_eq hξ htξ P _ ⟨z, hzi⟩ zu rfl (by rw [IsUnit.unit_spec]; exact (reduction_coe P ⟨z, hzi⟩).symm)]
  have hQ1 : ∏ P ∈ QE sel (mu : Chr X.F X.E X.K), (((ξ.locK P zu : ℂˣ) : ℂ))⁻¹ = 1 := by
    rw [Finset.prod_inv_distrib, ← Units.coe_prod, htw, Units.val_one, inv_one]
  have hG1 : ∏ w ∈ Pr.vGs, (((m0 j).locK w zu : ℂˣ) : ℂ)⁻¹ = (((m0 j).inf x : ℂˣ) : ℂ) := by
    rw [Finset.prod_inv_distrib, ← Units.coe_prod, eq_inv_of_mul_eq_one_right key, Units.val_inv_eq_inv_val, inv_inv]
  rw [hsplit, Finset.prod_congr rfl hG, Finset.prod_congr rfl hQ, hQ1, mul_one, hG1]
  obtain ⟨n, hn, hinf⟩ := hmu0.inf
  rw [hinf x]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  have hn' : n τ = 2 * -(e j τ) := by
    have h3 := hn τ
    simp only at h3
    exact_mod_cast h3
  have ha : (X.embC σ₀ τ) (x : X.E) ≠ 0 := (map_ne_zero _).mpr x.ne_zero
  have hc0 : starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E)) ≠ 0 := (map_ne_zero _).mpr ha
  have hcj : (X.embC σ₀ τ) (star (x : X.E)) = starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E)) := hX.conjE _ _
  have hzφ : (X.embC σ₀ τ) z = (X.embC σ₀ τ) (x : X.E) / starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E)) := by
    have h2 : (X.embC σ₀ τ) (x : X.E) = (X.embC σ₀ τ) z * starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E)) := by
      rw [← hcj, ← map_mul, ← hx]
    rw [eq_div_iff hc0, ← h2]
  have hsq : ((X.embC σ₀ τ) (x : X.E) / ((‖(X.embC σ₀ τ) (x : X.E)‖ : ℝ) : ℂ)) ^ (2 : ℤ) =
      (X.embC σ₀ τ) (x : X.E) / starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E)) := by
    have hnorm : ((‖(X.embC σ₀ τ) (x : X.E)‖ : ℝ) : ℂ) ^ 2 =
        (X.embC σ₀ τ) (x : X.E) * starRingEnd ℂ ((X.embC σ₀ τ) (x : X.E)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [zpow_two, div_mul_div_comm, ← pow_two, ← pow_two, hnorm, div_eq_div_iff (mul_ne_zero ha hc0) hc0]
    ring
  rw [hn', zpow_mul, hsq, ← hzφ]

end GlobalTheory.NormOneUnit
