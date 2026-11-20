import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.MemMaxVAIff
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittFN
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittHS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCharpolyPreservingHermitianFormCMStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.IntUnitaryPoly

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_matrix_charpoly_preserving_hermitian_form_CM`.
-/
theorem lemGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := GlobalTheory.T.exists_matrix_charpoly_preserving_hermitian_form_CM

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q hU hq n H hint hdet hH`. Establish `hv` using `hU.2.1`. Use `set O := Formalism.IndefR.LocBrg.VA L`. Use `set s := Formalism.IndefR.LocBrg.sigA σ hv`. Establish `hs : ∀ x, s (s x) = x` using `Formalism.IndefR.LocBrg.sigA_inv σ hv hU.1`.

Establish `h2 : IsUnit (2 : O)` using `Formalism.IndefR.LocBrg.two_unit_VA hU hq`. Establish `hτ : ∃ τ : O, τ + s τ = 1`. Take `⟨u, hu⟩` from `h2`. Use `⟨((u⁻¹ : Oˣ) : O), ?_⟩` and prove the remaining obligations. Establish `hs2 : s 2 = 2` using `map_ofNat s 2`.

Establish `hfix : s ((u⁻¹ : Oˣ) : O) = ((u⁻¹ : Oˣ) : O)`. Establish `e : s ((u⁻¹ : Oˣ) : O) * 2 = 1` using `by rw [← hs2, ← map_mul, ← hu, Units.inv_mul, map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hfix, ← two_mul, ← hu, Units.mul_inv]`. Establish `hn : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u` using `fun u hu hsu => Formalism.IndefR.LocBrg.normSurj Formalism.IndefR.LocBrg.finNormSurj Formalism.IndefR.LocBrg.henselSqrt hU hq u hsu hu`.

Use `set Q : Matrix (Fin n) (Fin n) O := fun i j => ⟨H i j, Formalism.IndefR.LocBrg.mem_VA.2 (Formalism.IndefR.LocBrg.mem_intL.1 (hint i j))⟩ with hQdef`. Establish `hmap : Q.map O.subtype = H` using `by ext i j; rfl`. Establish `hQ : cT s Q = Q`. Use extensionality with `i j`. Conclude with `congrFun (congrFun hH i) j`.

Establish `hQu : IsUnit Q`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Formalism.IndefR.LocBrg.isUnit_VA_iff]`. Establish `e : ((Q.det : O) : L) = H.det` using `by rw [← hmap]; exact RingHom.map_det O.subtype Q`. Rewrite using `[e]`. Conclude with `hdet`.

Take `⟨a, ha⟩` from `GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing O s hs hτ hn n Q hQ hQu`. Set `ι : O →+* intL L` to `O.subtype.codRestrict (intL L) (fun x => Formalism.IndefR.LocBrg.mem_intL.2 (Formalism.IndefR.LocBrg.mem_VA.1 x.2))`. Use `⟨bc (n := Fin n) (intL L).subtype (bc (n := Fin n) ι a), ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hR : ((bc (n` using `Fin n) (intL L).subtype (bc (n := Fin n) ι a) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) O).map O.subtype := by ext i j; rfl`. Rewrite using `[hR, ← hmap]`.

Establish `hc : cT σ ((a : Matrix (Fin n) (Fin n) O).map O.subtype) = (cT s (a : Matrix (Fin n) (Fin n) O)).map O.subtype`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[hc, ← Matrix.map_mul, ← Matrix.map_mul, ha, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem lemLocal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) L), (∀ i j, H i j ∈ intL L) →
      Valued.v H.det = 1 → cT σ H = H →
      ∃ R ∈ GLint (Fin n) (intL L), cT σ ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * H * ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
  intro L _ _ _ ϖ σ q hU hq n H hint hdet hH
  have hv := hU.2.1
  set O := Formalism.IndefR.LocBrg.VA L
  set s := Formalism.IndefR.LocBrg.sigA σ hv
  have hs : ∀ x, s (s x) = x := Formalism.IndefR.LocBrg.sigA_inv σ hv hU.1
  have h2 : IsUnit (2 : O) := Formalism.IndefR.LocBrg.two_unit_VA hU hq
  have hτ : ∃ τ : O, τ + s τ = 1 := by
    obtain ⟨u, hu⟩ := h2
    refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
    have hs2 : s 2 = 2 := map_ofNat s 2
    have hfix : s ((u⁻¹ : Oˣ) : O) = ((u⁻¹ : Oˣ) : O) := by
      have e : s ((u⁻¹ : Oˣ) : O) * 2 = 1 := by rw [← hs2, ← map_mul, ← hu, Units.inv_mul, map_one]
      calc s ((u⁻¹ : Oˣ) : O) = s ((u⁻¹ : Oˣ) : O) * (2 * ((u⁻¹ : Oˣ) : O)) := by rw [← hu, Units.mul_inv, mul_one]
        _ = ((u⁻¹ : Oˣ) : O) := by rw [← mul_assoc, e, one_mul]
    rw [hfix, ← two_mul, ← hu, Units.mul_inv]
  have hn : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u := fun u hu hsu =>
    Formalism.IndefR.LocBrg.normSurj Formalism.IndefR.LocBrg.finNormSurj Formalism.IndefR.LocBrg.henselSqrt hU hq u hsu hu
  set Q : Matrix (Fin n) (Fin n) O := fun i j =>
    ⟨H i j, Formalism.IndefR.LocBrg.mem_VA.2 (Formalism.IndefR.LocBrg.mem_intL.1 (hint i j))⟩ with hQdef
  have hmap : Q.map O.subtype = H := by ext i j; rfl
  have hQ : cT s Q = Q := by
    ext i j; exact congrFun (congrFun hH i) j
  have hQu : IsUnit Q := by
    rw [Matrix.isUnit_iff_isUnit_det, Formalism.IndefR.LocBrg.isUnit_VA_iff]
    have e : ((Q.det : O) : L) = H.det := by rw [← hmap]; exact RingHom.map_det O.subtype Q
    rw [e]; exact hdet
  obtain ⟨a, ha⟩ := GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing O s hs hτ hn n Q hQ hQu
  let ι : O →+* intL L := O.subtype.codRestrict (intL L)
    (fun x => Formalism.IndefR.LocBrg.mem_intL.2 (Formalism.IndefR.LocBrg.mem_VA.1 x.2))
  refine ⟨bc (n := Fin n) (intL L).subtype (bc (n := Fin n) ι a), ⟨_, rfl⟩, ?_⟩
  have hR : ((bc (n := Fin n) (intL L).subtype (bc (n := Fin n) ι a) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (a : Matrix (Fin n) (Fin n) O).map O.subtype := by ext i j; rfl
  rw [hR, ← hmap]
  have hc : cT σ ((a : Matrix (Fin n) (Fin n) O).map O.subtype) = (cT s (a : Matrix (Fin n) (Fin n) O)).map O.subtype := by
    ext i j; rfl
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, ha, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Introduce `L _ _ ϖ σ q hU h2`. Use `set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring`. Establish `hcard : Nat.card (IsLocalRing.ResidueField V) = q ^ 2` using `hU.2.2.2.2.2.2`. Establish `hq0 : q ≠ 0` using `by have := hU.2.2.2.2.2.1; omega`. Use `haveI : Finite (IsLocalRing.ResidueField V) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hq0)`.

Establish `h20 : (2 : L) ≠ 0` using `fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2`. Establish `hu : IsUnit (2 : V)`. Establish `hmem : (2 : L)⁻¹ ∈ V` using `(Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h2, inv_one])`. Establish `hmul : (2 : V) * ⟨(2 : L)⁻¹, hmem⟩ = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `first`. Consider the case `exact mul_inv_cancel₀ h20`. Consider the case `(show (2 : L) * (2 : L)⁻¹ = 1; exact mul_inv_cancel₀ h20)`. Consider the case `(push_cast; exact mul_inv_cancel₀ h20)`. Conclude with `⟨⟨2, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩`.

Establish `h2V : (2 : IsLocalRing.ResidueField V) ≠ 0`. Introduce `h`. Establish `hm : (2 : V) ∈ IsLocalRing.maximalIdeal V`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_ofNat]`. Conclude with `h`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hm hu`. Assume the negation of the conclusion as `hodd`. Establish `heven : Even q` using `Nat.not_odd_iff_even.1 hodd`. Establish `hdvd : 2 ∣ Nat.card (IsLocalRing.ResidueField V)`. Rewrite using `[hcard]`.

Conclude with `dvd_pow (even_iff_two_dvd.1 heven) two_ne_zero`. Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' 2 hdvd`. Establish `hx0 : x ≠ 0` using `by intro h; rw [h, addOrderOf_zero] at hx; norm_num at hx`. Establish `hmul : (2 : IsLocalRing.ResidueField V) * x = 0`.

Rewrite using `[two_mul, ← two_nsmul, ← hx, addOrderOf_nsmul_eq_zero]`. Conclude with `h2V ((mul_eq_zero.1 hmul).resolve_right hx0)`.
-/
theorem lemOdd : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → Odd q := by
  intro L _ _ ϖ σ q hU h2
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hcard : Nat.card (IsLocalRing.ResidueField V) = q ^ 2 := hU.2.2.2.2.2.2
  have hq0 : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  haveI : Finite (IsLocalRing.ResidueField V) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hq0)
  have h20 : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
  have hu : IsUnit (2 : V) := by
    have hmem : (2 : L)⁻¹ ∈ V := (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h2, inv_one])
    have hmul : (2 : V) * ⟨(2 : L)⁻¹, hmem⟩ = 1 := by
      apply Subtype.ext
      first
        | exact mul_inv_cancel₀ h20
        | (show (2 : L) * (2 : L)⁻¹ = 1; exact mul_inv_cancel₀ h20)
        | (push_cast; exact mul_inv_cancel₀ h20)
    exact ⟨⟨2, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have h2V : (2 : IsLocalRing.ResidueField V) ≠ 0 := by
    intro h
    have hm : (2 : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_ofNat]; exact h
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu
  by_contra hodd
  have heven : Even q := Nat.not_odd_iff_even.1 hodd
  have hdvd : 2 ∣ Nat.card (IsLocalRing.ResidueField V) := by
    rw [hcard]; exact dvd_pow (even_iff_two_dvd.1 heven) two_ne_zero
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' 2 hdvd
  have hx0 : x ≠ 0 := by intro h; rw [h, addOrderOf_zero] at hx; norm_num at hx
  have hmul : (2 : IsLocalRing.ResidueField V) * x = 0 := by
    rw [two_mul, ← two_nsmul, ← hx, addOrderOf_nsmul_eq_zero]
  exact h2V ((mul_eq_zero.1 hmul).resolve_right hx0)

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x`.
-/
theorem val_alg {E : Type} [Field E] [NumberField E] (w : Pl E) (x : E) :
    Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

/- English proof (translation)
Use `filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) (K := E) x).eventually_cofinite_notMem] with w hw`. Establish `hw' : ¬ 1 < w.valuation E x` using `hw`. Rewrite using `[val_alg]`. Conclude with `not_lt.1 hw'`.
-/
theorem ae_int {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) (K := E) x).eventually_cofinite_notMem] with w hw
  have hw' : ¬ 1 < w.valuation E x := hw
  rw [val_alg]
  exact not_lt.1 hw'

/- English proof (translation)
Use `filter_upwards [ae_int x, ae_int x⁻¹] with w h1 h2`. Rewrite `h2` using `[map_inv₀, map_inv₀]`. Establish `h0 : Valued.v (algebraMap E (w.adicCompletion E) x) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `(_root_.map_ne_zero _).2 hx`.

Conclude with `le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)`.
-/
theorem ae_unit {E : Type} [Field E] [NumberField E] {x : E} (hx : x ≠ 0) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), Valued.v (algebraMap E (w.adicCompletion E) x) = 1 := by
  filter_upwards [ae_int x, ae_int x⁻¹] with w h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h0 : Valued.v (algebraMap E (w.adicCompletion E) x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (_root_.map_ne_zero _).2 hx
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)

/- English proof (translation)
Set `A : Matrix (Fin n) (Fin n) O` to `fun i j => ⟨_, h1 i j⟩`. Set `B : Matrix (Fin n) (Fin n) O` to `fun i j => ⟨_, h2 i j⟩`. Establish `hA : A.map O.subtype = (g : Matrix (Fin n) (Fin n) L)` using `by ext i j; rfl`. Establish `hB : B.map O.subtype = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)` using `by ext i j; rfl`. Establish `inj : ∀ M N : Matrix (Fin n) (Fin n) O, M.map O.subtype = N.map O.subtype → M = N` using `fun M N h => by`.

Use extensionality with `i j`. Conclude with `congrFun (congrFun h i) j`. Establish `hAB : A * B = 1` using `inj _ _ (by`. Rewrite using `[Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])`. Establish `hBA : B * A = 1` using `inj _ _ (by`.

Rewrite using `[Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])`. Use `⟨⟨A, B, hAB, hBA⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem mem_GLint {L : Type} [Field L] {O : Subring L} {n : ℕ} (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) :
    g ∈ GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h2 i j⟩
  have hA : A.map O.subtype = (g : Matrix (Fin n) (Fin n) L) := by ext i j; rfl
  have hB : B.map O.subtype = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by ext i j; rfl
  have inj : ∀ M N : Matrix (Fin n) (Fin n) O, M.map O.subtype = N.map O.subtype → M = N := fun M N h => by
    ext i j; exact congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj _ _ (by
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hBA : B * A = 1 := inj _ _ (by
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext i j; rfl

/- English proof (translation)
Use extensionality with `x`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans (Valuation.mem_integer_iff _ _).symm`.
-/
theorem Ov_eq {E : Type} [Field E] [NumberField E] (w : Pl E) :
    (w.adicCompletionIntegers E).toSubring = intL (w.adicCompletion E) := by
  ext x
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans (Valuation.mem_integer_iff _ _).symm

/- English proof (translation)
Introduce `E _ _ _ hU n P hP`. Take `⟨C, H, hC, hCd, hHd, hHh, hCH⟩` from `lemGlobal E n P hP`. Use `set Ci := C⁻¹ with hCi`. Establish `hCCi : C * Ci = 1` using `Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hCd)`. Establish `hCiC : Ci * C = 1` using `Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.2 hCd)`.

Set `f : ∀ w : Pl E, E →+* w.adicCompletion E` to `fun w => algebraMap E (w.adicCompletion E)`. Set `Cw : ∀ w : Pl E, GLw n w` to `fun w => ⟨C.map (f w), Ci.map (f w), by rw [← Matrix.map_mul, hCCi, Matrix.map_one _ (map_zero _) (map_one _)], by rw [← Matrix.map_mul, hCiC, Matrix.map_one _ (map_zero _) (map_one _)]⟩`. Establish `hCwv : ∀ w, ((Cw w : GLw n w) : Matrix (Fin n) (Fin n) _) = C.map (f w)` using `fun w => rfl`. Establish `hCwi : ∀ w, (((Cw w)⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) = Ci.map (f w)` using `fun w => rfl`. Establish `hchar : ∀ w, (C.map (f w)).charpoly = atPl w P` using `fun w => by`.

Rewrite using `[Matrix.charpoly_map, hC]`. Use `⟨?_, fun w hs => ⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, hchar w⟩⟩` and prove the remaining obligations. Establish `hall : ∀ M : Matrix (Fin n) (Fin n) E, ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, Valued.v (f w (M i j)) ≤ 1` using `fun M => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ae_int (M i j)`. Use `filter_upwards [hall C, hall Ci, hall H, ae_unit hHd, ae_unit (two_ne_zero : (2 : E) ≠ 0)] with w h1 h2 h3 h4 h5`. Establish `hO : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 → x ∈ (w.adicCompletionIntegers E).toSubring` using `fun x hx => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx`.

Establish `hK : Cw w ∈ GlobalTheory.LFun.KGL w n` using `mem_GLint _ (fun i j => hO _ (h1 i j)) (fun i j => hO _ (h2 i j))`. Distinguish the cases in `hs : IsSplitAt w`. Conclude with `⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, Subgroup.mem_subgroupOf.2 hK, hchar w⟩`. Take `⟨-, -, -, hns, -⟩` from `GlobalTheory.ConjAtPlace.main E hU w`. Take `⟨hext, ⟨ϖ, q, hUI, -⟩, -, -⟩` from `hns hs`.

Establish `h2v : Valued.v (2 : w.adicCompletion E) = 1`. Establish `e : f w 2 = 2` using `map_ofNat _ 2`. Rewrite using `[← e]`. Conclude with `h5`. Establish `hq` using `lemOdd _ ϖ (cj w) q hUI h2v`.

Use `set Hw := H.map (f w) with hHwdef`. Establish `hHw1 : ∀ i j, Hw i j ∈ intL (w.adicCompletion E)` using `fun i j => (Valuation.mem_integer_iff _ _).2 (h3 i j)`. Establish `hHw2 : Valued.v Hw.det = 1`. Rewrite using `[show Hw.det = f w H.det from (RingHom.map_det (f w) H).symm]`. Conclude with `h4`.

Establish `hmapc : ∀ M : Matrix (Fin n) (Fin n) E, cT (cj w) (M.map (f w)) = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (f w)`. Introduce `M`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [cT, Matrix.map_apply, Matrix.transpose_apply]`. Conclude with `hext (M j i)`.

Establish `hHw3 : cT (cj w) Hw = Hw` using `by rw [hmapc, hHh]`. Establish `hCHw : cT (cj w) (C.map (f w)) * Hw * C.map (f w) = Hw`. Rewrite using `[hmapc, hHwdef, ← Matrix.map_mul, ← Matrix.map_mul, hCH]`. Take `⟨R, hR, hRH⟩` from `lemLocal (w.adicCompletion E) ϖ (cj w) q hUI hq n Hw hHw1 hHw2 hHw3`. Establish `hRK : R ∈ GlobalTheory.LFun.KGL w n`.

Establish `e : GlobalTheory.LFun.KGL w n = GLint (Fin n) (intL (w.adicCompletion E))` using `by show GLint (Fin n) (w.adicCompletionIntegers E).toSubring = _`. Rewrite using `[Ov_eq]`. Rewrite using `[e]`. Conclude with `hR`. Use `⟨⟨R⁻¹ * Cw w * R, ?_⟩, Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem (inv_mem hRK) hK) hRK), ?_⟩` and prove the remaining obligations.

Rewrite using `[UL, if_neg hs] show cT (cj w) ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 * ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) = 1`. Rewrite using `[Units.val_mul, Units.val_mul, hCwv]`. Use `set r := ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Use `set ri := (((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Establish `hri : r * ri = 1` using `Units.mul_inv R`.

Establish `hH' : Hw = cT (cj w) ri * ri`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_one, cT_mul, cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = 1 := by rw [← hH', hCHw, hRH]`. Establish `hinv : ((((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))⁻¹ = ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Rewrite using `[← Matrix.coe_units_inv, inv_inv]`. Establish `e` using `Matrix.charpoly_units_conj (R⁻¹ : GLw n w) (C.map (f w))`. Rewrite `e` using `[hinv]`.

Establish `key : ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly = atPl w P`. Rewrite using `[Units.val_mul, Units.val_mul, hCwv, e, hchar]`. Conclude with `key`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n →
    (∀ᶠ w in (cofinite : Filter (Pl E)), ∃ y : UL n w, y ∈ KL n w ∧ y.1.val.charpoly = atPl w P) ∧
      ∀ w : Pl E, IsSplitAt w → ∃ y : UL n w, y.1.val.charpoly = atPl w P := by
  intro E _ _ _ hU n P hP
  obtain ⟨C, H, hC, hCd, hHd, hHh, hCH⟩ := lemGlobal E n P hP
  set Ci := C⁻¹ with hCi
  have hCCi : C * Ci = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hCd)
  have hCiC : Ci * C = 1 := Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.2 hCd)
  let f : ∀ w : Pl E, E →+* w.adicCompletion E := fun w => algebraMap E (w.adicCompletion E)
  let Cw : ∀ w : Pl E, GLw n w := fun w =>
    ⟨C.map (f w), Ci.map (f w), by rw [← Matrix.map_mul, hCCi, Matrix.map_one _ (map_zero _) (map_one _)],
      by rw [← Matrix.map_mul, hCiC, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hCwv : ∀ w, ((Cw w : GLw n w) : Matrix (Fin n) (Fin n) _) = C.map (f w) := fun w => rfl
  have hCwi : ∀ w, (((Cw w)⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) = Ci.map (f w) := fun w => rfl
  have hchar : ∀ w, (C.map (f w)).charpoly = atPl w P := fun w => by
    rw [Matrix.charpoly_map, hC]
  refine ⟨?_, fun w hs => ⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, hchar w⟩⟩
  have hall : ∀ M : Matrix (Fin n) (Fin n) E, ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, Valued.v (f w (M i j)) ≤ 1 :=
    fun M => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ae_int (M i j)
  filter_upwards [hall C, hall Ci, hall H, ae_unit hHd, ae_unit (two_ne_zero : (2 : E) ≠ 0)] with w h1 h2 h3 h4 h5
  have hO : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 → x ∈ (w.adicCompletionIntegers E).toSubring :=
    fun x hx => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx
  have hK : Cw w ∈ GlobalTheory.LFun.KGL w n :=
    mem_GLint _ (fun i j => hO _ (h1 i j)) (fun i j => hO _ (h2 i j))
  by_cases hs : IsSplitAt w
  · exact ⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, Subgroup.mem_subgroupOf.2 hK, hchar w⟩
  · obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨hext, ⟨ϖ, q, hUI, -⟩, -, -⟩ := hns hs
    have h2v : Valued.v (2 : w.adicCompletion E) = 1 := by
      have e : f w 2 = 2 := map_ofNat _ 2
      rw [← e]; exact h5
    have hq := lemOdd _ ϖ (cj w) q hUI h2v
    set Hw := H.map (f w) with hHwdef
    have hHw1 : ∀ i j, Hw i j ∈ intL (w.adicCompletion E) := fun i j => (Valuation.mem_integer_iff _ _).2 (h3 i j)
    have hHw2 : Valued.v Hw.det = 1 := by
      rw [show Hw.det = f w H.det from (RingHom.map_det (f w) H).symm]; exact h4
    have hmapc : ∀ M : Matrix (Fin n) (Fin n) E,
        cT (cj w) (M.map (f w)) = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (f w) := by
      intro M; refine Matrix.ext fun i j => ?_; simp only [cT, Matrix.map_apply, Matrix.transpose_apply]; exact hext (M j i)
    have hHw3 : cT (cj w) Hw = Hw := by rw [hmapc, hHh]
    have hCHw : cT (cj w) (C.map (f w)) * Hw * C.map (f w) = Hw := by
      rw [hmapc, hHwdef, ← Matrix.map_mul, ← Matrix.map_mul, hCH]
    obtain ⟨R, hR, hRH⟩ := lemLocal (w.adicCompletion E) ϖ (cj w) q hUI hq n Hw hHw1 hHw2 hHw3
    have hRK : R ∈ GlobalTheory.LFun.KGL w n := by
      have e : GlobalTheory.LFun.KGL w n = GLint (Fin n) (intL (w.adicCompletion E)) := by
        show GLint (Fin n) (w.adicCompletionIntegers E).toSubring = _
        rw [Ov_eq]
      rw [e]; exact hR
    refine ⟨⟨R⁻¹ * Cw w * R, ?_⟩, Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem (inv_mem hRK) hK) hRK), ?_⟩
    · rw [UL, if_neg hs]
      show cT (cj w) ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 *
        ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) = 1
      rw [Units.val_mul, Units.val_mul, hCwv]
      set r := ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      set ri := (((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      have hri : r * ri = 1 := Units.mul_inv R
      have hH' : Hw = cT (cj w) ri * ri := by
        calc Hw = cT (cj w) (r * ri) * Hw * (r * ri) := by rw [hri, cT_one, Matrix.one_mul, Matrix.mul_one]
          _ = cT (cj w) ri * (cT (cj w) r * Hw * r) * ri := by rw [cT_mul]; simp only [Matrix.mul_assoc]
          _ = cT (cj w) ri * ri := by rw [hRH, Matrix.mul_one]
      rw [Matrix.mul_one, cT_mul, cT_mul]
      calc cT (cj w) r * (cT (cj w) (C.map (f w)) * cT (cj w) ri) * (ri * C.map (f w) * r)
          = cT (cj w) r * (cT (cj w) (C.map (f w)) * (cT (cj w) ri * ri) * C.map (f w)) * r := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [← hH', hCHw, hRH]
    · have hinv : ((((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))⁻¹ =
          ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
        rw [← Matrix.coe_units_inv, inv_inv]
      have e := Matrix.charpoly_units_conj (R⁻¹ : GLw n w) (C.map (f w))
      rw [hinv] at e
      have key : ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly = atPl w P := by
        rw [Units.val_mul, Units.val_mul, hCwv, e, hchar]
      exact key

end GlobalTheory.IntUnitaryPoly
