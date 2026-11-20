import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRatConstMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplit

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Host

namespace GlobalTheory.SplitIdeleModulus

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (φ : E →+* v.adicCompletion F) (P : HeightOneSpectrum (𝓞 E))
  (hφ : ∀ t : F, φ (algebraMap F E t) = algebraMap F (v.adicCompletion F) t)
  (hP : ∀ x : 𝓞 E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1)

include hφ hP in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `y hy hyv`. Establish `hyP : y ∉ P.asIdeal`. Rewrite using `[← HeightOneSpectrum.intValuation_lt_one_iff_mem, hyv]`.

Simplify using the standard rewrite rules. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_zero, neg_zero, WithZero.exp_zero]`. Conclude with `GlobalTheory.SplitUnif.map_mem v φ y`. Rewrite using `[Nat.cast_zero, neg_zero, WithZero.exp_zero]`.

Conclude with `not_lt.1 (mt (hP y).2 hyP)`. Consider the case `succ n ih`. Introduce `y hy hyv`. Take `⟨ϖ, hϖ⟩` from `P.intValuation_exists_uniformizer`. Establish `hϖ0 : ϖ ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hϖ` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hϖ.symm`. Establish `hϖ1 : ϖ ∈ P.asIdeal`. Rewrite using `[← HeightOneSpectrum.intValuation_lt_one_iff_mem, hϖ]`.

Conclude with `WithZero.exp_lt_exp.2 (by omega) |>.trans_eq WithZero.exp_zero`. Establish `hϖ2 : ϖ ∉ P.asIdeal ^ 2`. Rewrite using `[← HeightOneSpectrum.intValuation_le_pow_iff_mem, hϖ, WithZero.exp_le_exp]`. Evaluate the numerical expressions. Establish `hE0 : ((ϖ : 𝓞 E) : E) ≠ 0`.

Introduce `h`. Conclude with `hϖ0 (Subtype.ext h)`. Establish `hx : P.valuation E ((y : E) / ϖ) ≤ 1`. Rewrite using `[map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hyv, hϖ, ← WithZero.exp_sub]`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Take `⟨m, d, h⟩` from `P.exists_primeCompl_mul_eq_of_integer _ hx`. Establish `h3 : (y : E) * ((d : 𝓞 E) : E) = (m : E) * ϖ`. Establish `h' : (y : E) / ϖ * ((d : 𝓞 E) : E) = (m : E)` using `h`. Rewrite using `[← h']`.

Clear the denominators using the available nonvanishing facts. Establish `h3' : y * (d : 𝓞 E) = m * ϖ`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `push_cast`. Conclude with `h3`.

Establish `hdv : P.intValuation (d : 𝓞 E) = 1`. Use `le_antisymm (P.intValuation_le_one _) ?_` and prove the remaining obligations. Conclude with `not_lt.1 (mt (HeightOneSpectrum.intValuation_lt_one_iff_mem P _).1 d.2)`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`.

Rewrite `h3'` using `[zero_mul, mul_eq_zero]`. Break down `h3' with h0 | h0` into its components or cases. Conclude with `hy h0`. Conclude with `d.2 (h0 ▸ zero_mem _)`. Establish `hmv : P.intValuation m = WithZero.exp (-(n : ℤ))`.

Establish `h4` using `congrArg P.intValuation h3'`. Rewrite `h4` using `[map_mul, map_mul, hdv, mul_one, hyv, hϖ]`. Establish `h5 : P.intValuation m ≠ 0` using `P.intValuation_ne_zero m hm0`. Rewrite `h4` using `[← WithZero.exp_log h5, ← WithZero.exp_add, WithZero.exp_inj]`. Rewrite using `[← WithZero.exp_log h5, WithZero.exp_inj]`.

Move the coercions through the operations in `at h4`. Use linear arithmetic over natural numbers and integers. Establish `hd : Valued.v (φ ((d : 𝓞 E) : E)) = 1` using `le_antisymm (GlobalTheory.SplitUnif.map_mem v φ d) (not_lt.1 (mt (hP d).2 d.2))`. Establish `h4` using `congrArg (fun z => Valued.v (φ z)) h3`. Simplify using `only [map_mul] at h4`.

Rewrite `h4` using `[hd, mul_one, ih m hm0 hmv, GlobalTheory.SplitUnif.valued_unif v φ P hφ hP ϖ hϖ1 hϖ2, ← WithZero.exp_add]`. Rewrite using `[h4]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem splitEmbedding_valued_eq_intValuation_integer (n : ℕ) : ∀ y : 𝓞 E, y ≠ 0 → P.intValuation y = WithZero.exp (-(n : ℤ)) →
    Valued.v (φ y) = WithZero.exp (-(n : ℤ)) := by
  induction n with
  | zero =>
    intro y hy hyv
    have hyP : y ∉ P.asIdeal := by
      rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, hyv]
      simp
    refine le_antisymm ?_ ?_
    · rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact GlobalTheory.SplitUnif.map_mem v φ y
    · rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact not_lt.1 (mt (hP y).2 hyP)
  | succ n ih =>
    intro y hy hyv
    obtain ⟨ϖ, hϖ⟩ := P.intValuation_exists_uniformizer
    have hϖ0 : ϖ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hϖ
      exact WithZero.exp_ne_zero hϖ.symm
    have hϖ1 : ϖ ∈ P.asIdeal := by
      rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, hϖ]
      exact WithZero.exp_lt_exp.2 (by omega) |>.trans_eq WithZero.exp_zero
    have hϖ2 : ϖ ∉ P.asIdeal ^ 2 := by
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, hϖ, WithZero.exp_le_exp]
      norm_num
    have hE0 : ((ϖ : 𝓞 E) : E) ≠ 0 := by
      intro h; exact hϖ0 (Subtype.ext h)
    have hx : P.valuation E ((y : E) / ϖ) ≤ 1 := by
      rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hyv, hϖ,
        ← WithZero.exp_sub]
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    obtain ⟨m, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hx
    have h3 : (y : E) * ((d : 𝓞 E) : E) = (m : E) * ϖ := by
      have h' : (y : E) / ϖ * ((d : 𝓞 E) : E) = (m : E) := h
      rw [← h']
      field_simp
    have h3' : y * (d : 𝓞 E) = m * ϖ := by
      apply RingOfIntegers.coe_injective
      push_cast
      exact h3
    have hdv : P.intValuation (d : 𝓞 E) = 1 := by
      refine le_antisymm (P.intValuation_le_one _) ?_
      exact not_lt.1 (mt (HeightOneSpectrum.intValuation_lt_one_iff_mem P _).1 d.2)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_mul, mul_eq_zero] at h3'
      rcases h3' with h0 | h0
      · exact hy h0
      · exact d.2 (h0 ▸ zero_mem _)
    have hmv : P.intValuation m = WithZero.exp (-(n : ℤ)) := by
      have h4 := congrArg P.intValuation h3'
      rw [map_mul, map_mul, hdv, mul_one, hyv, hϖ] at h4
      have h5 : P.intValuation m ≠ 0 := P.intValuation_ne_zero m hm0
      rw [← WithZero.exp_log h5, ← WithZero.exp_add, WithZero.exp_inj] at h4
      rw [← WithZero.exp_log h5, WithZero.exp_inj]
      push_cast at h4
      omega
    have hd : Valued.v (φ ((d : 𝓞 E) : E)) = 1 :=
      le_antisymm (GlobalTheory.SplitUnif.map_mem v φ d) (not_lt.1 (mt (hP d).2 d.2))
    have h4 := congrArg (fun z => Valued.v (φ z)) h3
    simp only [map_mul] at h4
    rw [hd, mul_one, ih m hm0 hmv, GlobalTheory.SplitUnif.valued_unif v φ P hφ hP ϖ hϖ1 hϖ2, ← WithZero.exp_add] at h4
    rw [h4]
    congr 1
    push_cast
    ring

include hφ hP in
/- English proof (translation)
Establish `h0 : P.intValuation y ≠ 0` using `P.intValuation_ne_zero y hy`. Establish `hle : WithZero.log (P.intValuation y) ≤ 0`. Use `P.intValuation_le_one y` as an intermediate fact. Rewrite `this` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Conclude with `this`.

Establish `key : P.intValuation y = WithZero.exp (-((WithZero.log (P.intValuation y)).natAbs : ℤ))`. Rewrite using `[← WithZero.exp_log h0]`. Use `congr 1`. Rewrite using `[WithZero.log_exp]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[key]`. Conclude with `splitEmbedding_valued_eq_intValuation_integer v φ P hφ hP _ y hy key`.
-/
theorem valued_eq_intValuation (y : 𝓞 E) (hy : y ≠ 0) : Valued.v (φ y) = P.intValuation y := by
  have h0 : P.intValuation y ≠ 0 := P.intValuation_ne_zero y hy
  have hle : WithZero.log (P.intValuation y) ≤ 0 := by
    have := P.intValuation_le_one y
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    exact this
  have key : P.intValuation y = WithZero.exp (-((WithZero.log (P.intValuation y)).natAbs : ℤ)) := by
    rw [← WithZero.exp_log h0]
    congr 1
    rw [WithZero.log_exp]
    omega
  rw [key]
  exact splitEmbedding_valued_eq_intValuation_integer v φ P hφ hP _ y hy key

end General

end GlobalTheory.SplitIdeleModulus

namespace GlobalTheory.SplitIdeleModulus

open GlobalTheory.SplitHecke
open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

/- English proof (translation)
Establish `e1 : incA D (algebraMap D.host.F D.host.E t) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t)`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `(Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t`. Use `show π (incA D _) = _`. Rewrite using `[e1, hc.2.2.1, AlgHom.commutes, AlgHom.commutes]`.
-/
theorem chart_incA_algebraMap {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hc : Chart e v π) (t : D.host.F) :
    (π.comp (incA D)) (algebraMap D.host.F D.host.E t) = algebraMap D.host.F (v.adicCompletion D.host.F) t := by
  have e1 : incA D (algebraMap D.host.F D.host.E t) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t
  show π (incA D _) = _
  rw [e1, hc.2.2.1, AlgHom.commutes, AlgHom.commutes]

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using the standard rewrite rules. Establish `hx0 : Valued.v ((π.comp (incA D)) x) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff, map_ne_zero]`. Conclude with `fun h => hx (Subtype.ext h)`.

Rewrite using `[he.2 x hx, hc.2.2.2, isInt_Ov]`. Use `show ¬ Valued.v ((π.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1 ↔ _`. Rewrite using `[map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]`.
-/
theorem chart_incA_mem {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (he : IsIdemAt e P) (hc : Chart e v π) (x : 𝓞 D.host.E) :
    x ∈ P.asIdeal ↔ Valued.v ((π.comp (incA D)) x) < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx0 : Valued.v ((π.comp (incA D)) x) ≠ 0 := by
      rw [Valuation.ne_zero_iff, map_ne_zero]
      exact fun h => hx (Subtype.ext h)
    rw [he.2 x hx, hc.2.2.2, isInt_Ov]
    show ¬ Valued.v ((π.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1 ↔ _
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]

/- English proof (translation)
Take `⟨v, π, hπ⟩` from `GlobalTheory.SplitChart.exists_chart e he.1`. Take `⟨w, ρ, hρ⟩` from `GlobalTheory.SplitChart.exists_chart f hf.1`. Establish `hee : e * e = e` using `he.1.1`. Establish `hff : f * f = f` using `hf.1.1`. Establish `hg : (e * f) * (e * f) = e * f`.

Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `hne`. Establish `h1 : e = e * f`. Establish `hi : IsIdempotentElem (π (e * f))`. Unfold `IsIdempotentElem`.

Rewrite using `[← map_mul, hg]`. Break down `IsIdempotentElem.iff_eq_zero_or_one.1 hi with h0 | h0` into its components or cases. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Use `(hπ.2.1 (e * f)).1 h0` as an intermediate fact.

Rewrite `this` using `[← mul_assoc, hee]`. Then use the resulting hypothesis. Establish `h2 : π (e - e * f) = 0`. Rewrite using `[map_sub, h0, GlobalTheory.SplitLinear.chart_e hee hπ, sub_self]`. Use `(hπ.2.1 _).1 h2` as an intermediate fact. Rewrite `this` using `[mul_sub, ← mul_assoc, hee, sub_eq_zero]`.

Conclude with `this`. Establish `h2 : f = e * f`. Establish `hi : IsIdempotentElem (ρ (e * f))`. Unfold `IsIdempotentElem`. Rewrite using `[← map_mul, hg]`.

Break down `IsIdempotentElem.iff_eq_zero_or_one.1 hi with h0 | h0` into its components or cases. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Use `(hρ.2.1 (e * f)).1 h0` as an intermediate fact. Rewrite `this` using `[mul_comm e f, ← mul_assoc, hff, mul_comm]`.

Conclude with `this`. Establish `h2 : ρ (f - e * f) = 0`. Rewrite using `[map_sub, h0, GlobalTheory.SplitLinear.chart_e hff hρ, sub_self]`. Use `(hρ.2.1 _).1 h2` as an intermediate fact. Rewrite `this` using `[mul_sub, mul_comm e f, ← mul_assoc, hff, sub_eq_zero]`.

Conclude with `this.trans (mul_comm f e)`. Establish `hef : e = f` using `h1.trans h2.symm`. Apply `hPQ` to reduce the goal to its premises. Use extensionality with `x`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[he.2 x hx, hf.2 x hx, hef]`.
-/
theorem idemAt_mul_eq_zero {e f : AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)} (he : IsIdemAt e P)
    (hf : IsIdemAt f Q) (hPQ : P ≠ Q) : e * f = 0 := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he.1
  obtain ⟨w, ρ, hρ⟩ := GlobalTheory.SplitChart.exists_chart f hf.1
  have hee : e * e = e := he.1.1
  have hff : f * f = f := hf.1.1
  have hg : (e * f) * (e * f) = e * f := by
    calc (e * f) * (e * f) = (e * e) * (f * f) := by ring
      _ = e * f := by rw [hee, hff]
  by_contra hne

  have h1 : e = e * f := by
    have hi : IsIdempotentElem (π (e * f)) := by
      unfold IsIdempotentElem; rw [← map_mul, hg]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hi with h0 | h0
    · exfalso; apply hne
      have := (hπ.2.1 (e * f)).1 h0
      rwa [← mul_assoc, hee] at this
    · have h2 : π (e - e * f) = 0 := by
        rw [map_sub, h0, GlobalTheory.SplitLinear.chart_e hee hπ, sub_self]
      have := (hπ.2.1 _).1 h2
      rw [mul_sub, ← mul_assoc, hee, sub_eq_zero] at this
      exact this
  have h2 : f = e * f := by
    have hi : IsIdempotentElem (ρ (e * f)) := by
      unfold IsIdempotentElem; rw [← map_mul, hg]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hi with h0 | h0
    · exfalso; apply hne
      have := (hρ.2.1 (e * f)).1 h0
      rw [mul_comm e f, ← mul_assoc, hff, mul_comm] at this
      exact this
    · have h2 : ρ (f - e * f) = 0 := by
        rw [map_sub, h0, GlobalTheory.SplitLinear.chart_e hff hρ, sub_self]
      have := (hρ.2.1 _).1 h2
      rw [mul_sub, mul_comm e f, ← mul_assoc, hff, sub_eq_zero] at this
      exact this.trans (mul_comm f e)
  have hef : e = f := h1.trans h2.symm
  apply hPQ
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [he.2 x hx, hf.2 x hx, hef]

/- English proof (translation)
Take `⟨v, π, hπ⟩` from `GlobalTheory.SplitChart.exists_chart e he.1`. Establish `hee : e * e = e` using `he.1.1`. Establish `hu1 : (1 - e) * (u : AE D) = 1 - e`. Rewrite using `[hu]`. Establish `: (1 - e) * e = 0` using `by rw [sub_mul, one_mul, hee, sub_self]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[GlobalTheory.SplitLinear.absFin_split D e v π he.1 hπ u hu1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]`. Establish `hφ` using `chart_incA_algebraMap hπ`. Establish `hP` using `chart_incA_mem he hπ`. Establish `hN : Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal`.

Rewrite using `[← GlobalTheory.SplitDetValue.card_residue_eq]`. Conclude with `GlobalTheory.SplitUnif.card_residueField v _ P hφ hP`. Establish `hm' : ((m : 𝓞 D.host.E)) ≠ 0`. Introduce `h`. Apply `hm` to reduce the goal to its premises.

Use `congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h` as an intermediate fact. Simplify using `using this`. Establish `hval : Valued.v (π (u : AE D)) = P.valuation D.host.E (m : D.host.E)`. Establish `e1 : π (u : AE D) = (π.comp (incA D)) (((m : 𝓞 D.host.E)) : D.host.E)`. Rewrite using `[hu, map_add, map_mul, map_sub, map_one, GlobalTheory.SplitLinear.chart_e hee hπ, one_mul, sub_self, add_zero]`.

Simplify using the standard rewrite rules. Rewrite using `[e1, valued_eq_intValuation v _ P hφ hP _ hm', ← P.valuation_of_algebraMap (K := D.host.E)]`. Simplify using the standard rewrite rules. Establish `e2 : ((Units.map π.toMonoidHom u : (Fv D.host.F v)ˣ) : Fv D.host.F v) = π (u : AE D)` using `rfl`. Rewrite using `[e2, hval, hN, Formalism.L2.Host.ordF, Units.val_mk0, neg_neg]`.
-/
theorem absFin_idemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsIdemAt e P) (m : ℕ)
    (hm : (m : D.host.E) ≠ 0) (u : (AE D)ˣ) (hu : (u : AE D) = e * (m : AE D) + (1 - e)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D u =
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(Formalism.L2.Host.ordF P (Units.mk0 (m : D.host.E) hm))) := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he.1
  have hee : e * e = e := he.1.1
  have hu1 : (1 - e) * (u : AE D) = 1 - e := by
    rw [hu]
    have : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
    calc (1 - e) * (e * (m : AE D) + (1 - e)) = ((1 - e) * e) * (m : AE D) + (1 - e) - ((1 - e) * e) := by ring
      _ = 1 - e := by rw [this]; ring
  rw [GlobalTheory.SplitLinear.absFin_split D e v π he.1 hπ u hu1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  have hφ := chart_incA_algebraMap hπ
  have hP := chart_incA_mem he hπ
  have hN : Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
    rw [← GlobalTheory.SplitDetValue.card_residue_eq]
    exact GlobalTheory.SplitUnif.card_residueField v _ P hφ hP
  have hm' : ((m : 𝓞 D.host.E)) ≠ 0 := by
    intro h; apply hm
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h
    simpa using this
  have hval : Valued.v (π (u : AE D)) = P.valuation D.host.E (m : D.host.E) := by
    have e1 : π (u : AE D) = (π.comp (incA D)) (((m : 𝓞 D.host.E)) : D.host.E) := by
      rw [hu, map_add, map_mul, map_sub, map_one, GlobalTheory.SplitLinear.chart_e hee hπ, one_mul, sub_self, add_zero]
      simp
    rw [e1, valued_eq_intValuation v _ P hφ hP _ hm', ← P.valuation_of_algebraMap (K := D.host.E)]
    simp
  have e2 : ((Units.map π.toMonoidHom u : (Fv D.host.F v)ˣ) : Fv D.host.F v) = π (u : AE D) := rfl
  rw [e2, hval, hN, Formalism.L2.Host.ordF, Units.val_mk0, neg_neg]

end GlobalTheory.SplitIdeleModulus

namespace GlobalTheory.SplitIdeleModulus

open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

/- English proof (translation)
Take the linear combination `(c * c' - c - c' + 1) * hee + e * hcc`.
-/
theorem unit_aux {e c c' : AE D} (hee : e * e = e) (hcc : c * c' = 1) :
    (e * c + (1 - e)) * (e * c' + (1 - e)) = 1 := by
  linear_combination (c * c' - c - c' + 1) * hee + e * hcc

/- English proof (translation)
Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using the standard rewrite rules. Consider the case `insert Q s hQ ih`.

Introduce `hs`. Establish `hs' : s ⊆ P1` using `(Finset.subset_insert Q s).trans hs`. Establish `hQS : es Q * ∑ PP ∈ s, es PP = 0`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_eq_zero fun PP hPP => ?_` and prove the remaining obligations.

Conclude with `idemAt_mul_eq_zero (hes Q (hs (Finset.mem_insert_self Q s))) (hes PP (hs' hPP)) (fun h => hQ (h ▸ hPP))`. Rewrite using `[Finset.prod_insert hQ, Finset.sum_insert hQ, ih hs']`. Take the linear combination `(c - 1) ^ 2 * hQS`.
-/
theorem prod_idem {P1 : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ P1, IsIdemAt (es PP) PP) (c : AE D) :
    ∀ s ⊆ P1, ∏ PP ∈ s, (es PP * c + (1 - es PP)) = (∑ PP ∈ s, es PP) * c + (1 - ∑ PP ∈ s, es PP) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert Q s hQ ih =>
    intro hs
    have hs' : s ⊆ P1 := (Finset.subset_insert Q s).trans hs
    have hQS : es Q * ∑ PP ∈ s, es PP = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun PP hPP => ?_
      exact idemAt_mul_eq_zero (hes Q (hs (Finset.mem_insert_self Q s))) (hes PP (hs' hPP))
        (fun h => hQ (h ▸ hPP))
    rw [Finset.prod_insert hQ, Finset.sum_insert hQ, ih hs']
    linear_combination (c - 1) ^ 2 * hQS

/- English proof (translation)
Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]`.
-/
theorem absFin_one' : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]

/- English proof (translation)
Introduce `D P1 a ha m hm x hx`. Take `⟨⟨es, hes, hae⟩, -⟩` from `ha`. Establish `hcc : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1`. Rewrite using `[← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ hm, map_one]`. Set `u : {PP // PP ∈ P1} → (AE D)ˣ` to `fun PP => { val := es PP.1 * (m : AE D) + (1 - es PP.1) inv := es PP.1 * incA D ((m : D.host.E)⁻¹) + (1 - es PP.1) val_inv := unit_aux (hes PP.1 PP.2).1.1 hcc inv_val := unit_aux (hes PP.1 PP.2).1.1 (by rw [mul_comm]; exact hcc) }`.

Establish `hx' : x = ∏ PP ∈ P1.attach, u PP`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hx, Units.coe_prod]`. Express the relevant statement in the definitionally equal form `_ = ∏ PP ∈ P1.attach, (fun PP => es PP * (m : AE D) + (1 - es PP)) PP.1`. Rewrite using `[Finset.prod_attach P1 (fun PP => es PP * (m : AE D) + (1 - es PP)), prod_idem hes _ P1 subset_rfl, hae]`.

Set `A : (AE D)ˣ →* ℝ` to `⟨⟨GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D, absFin_one'⟩, GlobalTheory.SplitLinear.absFin_mul⟩`. Establish `hA : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = A x` using `rfl`. Rewrite using `[hA, hx', map_prod, ← Finset.prod_attach P1]`. Conclude with `Finset.prod_congr rfl fun PP _ => absFin_idemAt (hes PP.1 PP.2) m hm (u PP) rfl`.
-/
theorem absFin_idemSum : ∀ (D : D7) (P1 : Finset (Formalism.L2.DIV.Pl D.host.E)) (a : AE D), IsIdemSum a P1 → ∀ (m : ℕ) (hm : (m : D.host.E) ≠ 0) (x : (AE D)ˣ), (x : AE D) = a * (m : AE D) + (1 - a) → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = ∏ PP ∈ P1, ((Ideal.absNorm PP.asIdeal : ℕ) : ℝ) ^ (-(Formalism.L2.Host.ordF PP (Units.mk0 (m : D.host.E) hm))) := by
  intro D P1 a ha m hm x hx
  obtain ⟨⟨es, hes, hae⟩, -⟩ := ha
  have hcc : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
    rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ hm, map_one]
  let u : {PP // PP ∈ P1} → (AE D)ˣ := fun PP =>
    { val := es PP.1 * (m : AE D) + (1 - es PP.1)
      inv := es PP.1 * incA D ((m : D.host.E)⁻¹) + (1 - es PP.1)
      val_inv := unit_aux (hes PP.1 PP.2).1.1 hcc
      inv_val := unit_aux (hes PP.1 PP.2).1.1 (by rw [mul_comm]; exact hcc) }
  have hx' : x = ∏ PP ∈ P1.attach, u PP := by
    apply Units.ext
    rw [hx, Units.coe_prod]
    change _ = ∏ PP ∈ P1.attach, (fun PP => es PP * (m : AE D) + (1 - es PP)) PP.1
    rw [Finset.prod_attach P1 (fun PP => es PP * (m : AE D) + (1 - es PP)), prod_idem hes _ P1 subset_rfl, hae]
  let A : (AE D)ˣ →* ℝ := ⟨⟨GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D, absFin_one'⟩, GlobalTheory.SplitLinear.absFin_mul⟩
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D x = A x := rfl
  rw [hA, hx', map_prod, ← Finset.prod_attach P1]
  exact Finset.prod_congr rfl fun PP _ => absFin_idemAt (hes PP.1 PP.2) m hm (u PP) rfl

end GlobalTheory.SplitIdeleModulus

end
