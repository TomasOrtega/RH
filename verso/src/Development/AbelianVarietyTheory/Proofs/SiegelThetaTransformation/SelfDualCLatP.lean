import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsClassicalLevelDataCoverSelfDual
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsHomDivMulRefine
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.LocalRingCardinality.ConjSqrtMinusD

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.Base

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.SW.Lev

variable {D : D7}

/- English proof (translation)
Rewrite using `[cc_eq_conj]`. Conclude with `D.host.conj_sqrtMinusD`.
-/
theorem cc_sqrt (D : D7) : cc D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  rw [cc_eq_conj]; exact D.host.conj_sqrtMinusD

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem star_eq_cc (x : D.host.E) : star x = cc x := rfl

/- English proof (translation)
Establish `hd : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`. Establish `hs` using `D.host.sqrtMinusD_sq`. Establish `hi : IsIntegral ℤ D.host.sqrtMinusD`. Use `IsIntegral.of_pow (n := 2) two_pos ?_` and prove the remaining obligations. Rewrite using `[hs]`.

Conclude with `(isIntegral_natCast _).neg`. Set `s : 𝓞 D.host.E` to `⟨_, hi⟩`. Establish `hb : bar (2 + s) = 2 - s`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[map_add, map_ofNat, sub_eq_add_neg]`.

Simplify using `only [map_add, map_neg]`. Use `congr 1`. Conclude with `(coe_bar s).trans (cc_sqrt D)`. Establish `hs2 : s ^ 2 = -(D.host.d : 𝓞 D.host.E)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Simplify using `only [map_pow, map_neg, map_natCast]`. Conclude with `hs`. Establish `hn : (2 + s) * (2 - s) = ((4 + D.host.d : ℕ) : 𝓞 D.host.E)`. Use `push_cast`. Take the linear combination `-hs2`.

Establish `hm : ((4 + D.host.d : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {2 + s}` using `hn ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Take `⟨k, hk⟩ : ∃ k, D.host.d = 16 * k + 7` from `⟨D.host.d / 16, by omega⟩`. Use `⟨Ideal.span {2 + s}, fun h => ?_, fun h => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `Ideal.span_singleton_eq_top.1 h`. Establish `h2` using `h1.mul (h1.map bar)`.

Rewrite `h2` using `[hb, hn]`. Establish `h3 : IsUnit (algebraMap ℤ (𝓞 D.host.E) ((4 + D.host.d : ℕ) : ℤ))` using `by rwa [map_natCast]`. Establish `h4` using `Int.isUnit_iff.1 (isUnit_of_map_unit _ _ h3)`. Use linear arithmetic over natural numbers and integers. Rewrite `hm` using `[h, Ideal.mem_bot, Nat.cast_eq_zero]`.

Use linear arithmetic over natural numbers and integers. Establish `h1 : 2 - s ∈ conjI (Ideal.span {2 + s})`. Rewrite using `[mem_conjI, ← hb, bar_bar]`. Conclude with `Ideal.mem_span_singleton_self _`. Use `Ideal.isCoprime_iff_exists.2 ⟨3 * ((4 + D.host.d : ℕ) : 𝓞 D.host.E) - (12 * k + 8) * (2 + s), sub_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)), -(12 * k + 8) * (2 - s), Ideal.mul_mem_left _ _ h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `GlobalTheory.LevelTied.cop_of_nat (a := 4 + D.host.d) (b := 2) (Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))) hm (Ideal.mem_span_singleton_self _)`.
-/
theorem exists_ideal (D : D7) : ∃ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊤ ∧ 𝔪 ≠ ⊥ ∧ IsCoprime 𝔪 (conjI 𝔪) ∧
    IsCoprime 𝔪 (Ideal.span {2}) := by
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hs := D.host.sqrtMinusD_sq
  have hi : IsIntegral ℤ D.host.sqrtMinusD := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hs]
    exact (isIntegral_natCast _).neg
  let s : 𝓞 D.host.E := ⟨_, hi⟩
  have hb : bar (2 + s) = 2 - s := by
    apply RingOfIntegers.ext
    rw [map_add, map_ofNat, sub_eq_add_neg]
    simp only [map_add, map_neg]
    congr 1
    exact (coe_bar s).trans (cc_sqrt D)
  have hs2 : s ^ 2 = -(D.host.d : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    simp only [map_pow, map_neg, map_natCast]
    exact hs
  have hn : (2 + s) * (2 - s) = ((4 + D.host.d : ℕ) : 𝓞 D.host.E) := by
    push_cast
    linear_combination -hs2
  have hm : ((4 + D.host.d : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {2 + s} :=
    hn ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨k, hk⟩ : ∃ k, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  refine ⟨Ideal.span {2 + s}, fun h => ?_, fun h => ?_, ?_, ?_⟩
  · have h1 := Ideal.span_singleton_eq_top.1 h
    have h2 := h1.mul (h1.map bar)
    rw [hb, hn] at h2
    have h3 : IsUnit (algebraMap ℤ (𝓞 D.host.E) ((4 + D.host.d : ℕ) : ℤ)) := by rwa [map_natCast]
    have h4 := Int.isUnit_iff.1 (isUnit_of_map_unit _ _ h3)
    omega
  · rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hm
    omega
  · have h1 : 2 - s ∈ conjI (Ideal.span {2 + s}) := by
      rw [mem_conjI, ← hb, bar_bar]
      exact Ideal.mem_span_singleton_self _
    refine Ideal.isCoprime_iff_exists.2 ⟨3 * ((4 + D.host.d : ℕ) : 𝓞 D.host.E) - (12 * k + 8) * (2 + s),
      sub_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)),
      -(12 * k + 8) * (2 - s), Ideal.mul_mem_left _ _ h1, ?_⟩
    rw [hk]
    push_cast
    ring
  · exact GlobalTheory.LevelTied.cop_of_nat (a := 4 + D.host.d) (b := 2)
      (Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))) hm (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Take `⟨𝔪, h1, h2, h3, h4⟩` from `exists_ideal D`. Take `⟨β, hβ, hβ'⟩` from `GlobalTheory.LevelTied.exists_frame X 𝔪 h2`. Establish `hd : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`. Take `⟨w1, w2, w3, -, k, hk⟩` from `GlobalTheory.quadratic_refinement.2 (D.host.d : ℤ) D.host.sqrtMinusD (by omega) (by rw [Int.cast_natCast]; exact D.host.sqrtMinusD_sq) (cc_sqrt D)`. Use `⟨⟨𝔪, h1, h2, h3, h4, β, hβ, hβ', ⊤, 1, (1 + D.host.sqrtMinusD) / 2, w1, w2⟩, k, isIntegral_intCast k, ?_⟩` and prove the remaining obligations.

Use `w3.trans ?_` and prove the remaining obligations. Rewrite using `[hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_level {r : ℕ} (X : Data D.host.E r) : ∃ Lv : GlobalTheory.SW.Level X, IdemTwo Lv.w := by
  obtain ⟨𝔪, h1, h2, h3, h4⟩ := exists_ideal D
  obtain ⟨β, hβ, hβ'⟩ := GlobalTheory.LevelTied.exists_frame X 𝔪 h2
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨w1, w2, w3, -, k, hk⟩ := GlobalTheory.quadratic_refinement.2 (D.host.d : ℤ) D.host.sqrtMinusD (by omega)
    (by rw [Int.cast_natCast]; exact D.host.sqrtMinusD_sq) (cc_sqrt D)
  refine ⟨⟨𝔪, h1, h2, h3, h4, β, hβ, hβ', ⊤, 1, (1 + D.host.sqrtMinusD) / 2, w1, w2⟩, k,
    isIntegral_intCast k, ?_⟩
  refine w3.trans ?_
  rw [hk]
  push_cast
  ring

/- English proof (translation)
Establish `hB : IsUnit B.det`. Establish `: (s * (Bᴴ * G)) * B = 1` using `by rw [Matrix.mul_assoc, h, hs]`. Conclude with `Matrix.isUnit_det_of_left_inverse this`. Establish `e1` using `Matrix.mul_nonsing_inv B hB`. Establish `e2` using `Matrix.nonsing_inv_mul B hB`.

Generalize the expression as in `B⁻¹ = A at e1 e2`. Establish `e3 : Aᴴ * Bᴴ = 1` using `by rw [← conjTranspose_mul, e1, conjTranspose_one]`. Establish `hG : G = Aᴴ * s * A`. Rewrite using `[← h]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hGs : G * (B * s * A) = Aᴴ * A`. Rewrite using `[hG]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, hGs, conjTranspose_mul, conjTranspose_mul, hs', hG]`. Establish `e4 : Bᴴ * Aᴴ = 1` using `by rw [← conjTranspose_mul, e2, conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hGs]`. Conclude with `Matrix.PosDef.conjTranspose_mul_self A (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse e1)))`.
-/
theorem cartan_of_on {k : ℕ} {G B s : Matrix (Fin k) (Fin k) ℂ} (hs : s * s = 1) (hs' : sᴴ = s)
    (h : Bᴴ * G * B = s) : IsCartanInv G (B * s * B⁻¹) := by
  have hB : IsUnit B.det := by
    have : (s * (Bᴴ * G)) * B = 1 := by rw [Matrix.mul_assoc, h, hs]
    exact Matrix.isUnit_det_of_left_inverse this
  have e1 := Matrix.mul_nonsing_inv B hB
  have e2 := Matrix.nonsing_inv_mul B hB
  generalize B⁻¹ = A at e1 e2
  have e3 : Aᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, e1, conjTranspose_one]
  have hG : G = Aᴴ * s * A := by
    rw [← h]
    calc G = (Aᴴ * Bᴴ) * G * (B * A) := by rw [e1, e3, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hGs : G * (B * s * A) = Aᴴ * A := by
    rw [hG]
    calc _ = Aᴴ * (s * (A * B) * s) * A := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e2, Matrix.mul_one, hs, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc _ = B * (s * (A * B) * s) * A := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e2, Matrix.mul_one, hs, Matrix.mul_one, e1]
  · rw [Matrix.mul_assoc, hGs, conjTranspose_mul, conjTranspose_mul, hs', hG]
    have e4 : Bᴴ * Aᴴ = 1 := by rw [← conjTranspose_mul, e2, conjTranspose_one]
    calc _ = Aᴴ * (s * (Bᴴ * Aᴴ)) * A := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e4, Matrix.mul_one]
  · rw [hGs]
    exact Matrix.PosDef.conjTranspose_mul_self A
      (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2
        (Matrix.isUnit_det_of_left_inverse e1)))

/- English proof (translation)
Rewrite using `[sgnM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sgnM_sq {r : ℕ} (X : Data D.host.E r) : sgnM X * sgnM X = 1 := by
  rw [sgnM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[sgnM, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.
-/
theorem sgnM_herm {r : ℕ} (X : Data D.host.E r) : (sgnM X)ᴴ = sgnM X := by
  rw [sgnM, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0)]`. Prove the components needed by the constructor for the conclusion. Introduce `h c`. Take `⟨m, hm⟩` from `h (c : D.host.E) ((FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mpr ⟨c, rfl⟩)`. Conclude with `⟨m, by rw [← Algebra.traceForm_apply, ← hm]; rfl⟩`.

Introduce and unpack `h a ha`. Take `⟨c, rfl⟩` from `(FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mp ha`. Take `⟨m, hm⟩` from `h c`. Conclude with `⟨m, by rw [Algebra.traceForm_apply]; exact hm.symm⟩`.
-/
theorem mem_Dinv {z : D.host.E} : z ∈ Dinv D ↔ ∀ c : 𝓞 D.host.E, ∃ m : ℤ, Algebra.trace ℚ D.host.E (z * c) = m := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0)]
  constructor
  · intro h c
    obtain ⟨m, hm⟩ := h (c : D.host.E) ((FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mpr ⟨c, rfl⟩)
    exact ⟨m, by rw [← Algebra.traceForm_apply, ← hm]; rfl⟩
  · rintro h a ha
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff (S := nonZeroDivisors (𝓞 D.host.E))).mp ha
    obtain ⟨m, hm⟩ := h c
    exact ⟨m, by rw [Algebra.traceForm_apply]; exact hm.symm⟩

/- English proof (translation)
Establish `e : ∀ u v, EF X u v = -Algebra.trace ℚ D.host.E (D.host.xi0 * herm X.Gm u v)` using `fun u v => by`. Rewrite using `[EF_def, hk, mul_div_cancel_left₀ _ two_ne_zero, neg_mul, map_neg]`. Prove the components needed by the constructor for the conclusion. Introduce `hy z hz`. Use `mem_Dinv.2 fun c => ?_` and prove the remaining obligations.

Take `⟨m, hm⟩` from `(hL.2 _).1 (L.smul_mem c hy) z hz`. Rewrite `hm` using `[e, O_smul, herm_smul_left]`. Use `⟨-m, ?_⟩` and prove the remaining obligations. Rewrite using `[Int.cast_neg, ← hm, neg_neg]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Use `(hL.2 _).2 fun z hz => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `mem_Dinv.1 (h z hz) 1`. Use `⟨-m, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, Int.cast_neg, ← hm]`. Simplify using the standard rewrite rules.
-/
theorem dual_of_selfD {r : ℕ} {X : Data D.host.E r} (hk : X.κ0 = 2 * D.host.xi0) {L : Lt D.host.E r}
    (hL : SelfD X L) (y : Fin r → D.host.E) : y ∈ L ↔ ∀ z ∈ L, D.host.xi0 * herm X.Gm y z ∈ Dinv D := by
  have e : ∀ u v, EF X u v = -Algebra.trace ℚ D.host.E (D.host.xi0 * herm X.Gm u v) := fun u v => by
    rw [EF_def, hk, mul_div_cancel_left₀ _ two_ne_zero, neg_mul, map_neg]
  constructor
  · intro hy z hz
    refine mem_Dinv.2 fun c => ?_
    obtain ⟨m, hm⟩ := (hL.2 _).1 (L.smul_mem c hy) z hz
    rw [e, O_smul, herm_smul_left] at hm
    refine ⟨-m, ?_⟩
    rw [Int.cast_neg, ← hm, neg_neg]
    congr 1
    ring
  · intro h
    refine (hL.2 _).2 fun z hz => ?_
    obtain ⟨m, hm⟩ := mem_Dinv.1 (h z hz) 1
    refine ⟨-m, ?_⟩
    rw [e, Int.cast_neg, ← hm]
    simp

/- English proof (translation)
Rewrite using `[herm, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_eq_cc, transpose_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_eq_herm (T : HSp D) (x y : Fin T.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * T.gram i j * y j = herm T.gramᵀ y x := by
  rw [herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_eq_cc, transpose_apply]
  ring

/- English proof (translation)
Establish `hP` using `Formalism.IndefR.Fin.factPrincipalDatum`. Establish `hF` using `dual_of_selfD hk hL`. Rewrite `hF` using `[hG]`. Use `⟨⟨localLattice_fg D L hL.1, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Take `⟨b, hb0, hb⟩` from `FractionalIdeal.exists_ne_zero_mem_isInteger (inv_ne_zero (AA_ne_zero hP D))`.

Establish `hb0' : algebraMap _ D.host.E b ≠ 0` using `by simpa using hb0`. Rewrite using `[eq_top_iff, ← hsp, Submodule.span_le]`. Conclude with `fun v hv => (Submodule.smul_mem_iff _ hb0').1 (Submodule.subset_span (smul_mem_latP hP hb hv))`. Conclude with `⟨⟨_, localLattice_form_integral hP _ L hF hy hx⟩, (sum_eq_herm T x y).symm⟩`. Use `mem_dual_localLattice_of_forall hP _ L hF fun x hx => ?_` and prove the remaining obligations.

Take `⟨b, hb⟩` from `h x hx`. Rewrite using `[← sum_eq_herm, ← hb]`. Conclude with `b.2`.
-/
theorem selfDualC_latP {T : HSp D} {X : Data D.host.E T.rank} (hG : X.Gm = T.gramᵀ) (hk : X.κ0 = 2 * D.host.xi0)
    {L : Lt D.host.E T.rank} (hL : SelfD X L) (hsp : Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤) :
    IsSelfDualC T (lattice₂ D L) := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hF := dual_of_selfD hk hL
  rw [hG] at hF
  refine ⟨⟨localLattice_fg D L hL.1, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨b, hb0, hb⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (inv_ne_zero (AA_ne_zero hP D))
    have hb0' : algebraMap _ D.host.E b ≠ 0 := by simpa using hb0
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    exact fun v hv => (Submodule.smul_mem_iff _ hb0').1 (Submodule.subset_span (smul_mem_latP hP hb hv))
  · exact ⟨⟨_, localLattice_form_integral hP _ L hF hy hx⟩, (sum_eq_herm T x y).symm⟩
  · refine mem_dual_localLattice_of_forall hP _ L hF fun x hx => ?_
    obtain ⟨b, hb⟩ := h x hx
    rw [← sum_eq_herm, ← hb]
    exact b.2

/- English proof (translation)
The claim follows from `(GlobalTheory.SW.Base.mem_stdL _).2 fun a => int_cc D ((GlobalTheory.SW.Base.mem_stdL _).1 hv a)`.
-/
theorem star_mem_stdL {n : ℕ} {v : Fin n → D.host.E} (hv : v ∈ stdL D.host.E n) : star v ∈ stdL D.host.E n :=
  (GlobalTheory.SW.Base.mem_stdL _).2 fun a => int_cc D ((GlobalTheory.SW.Base.mem_stdL _).1 hv a)

/- English proof (translation)
Establish `e : ∀ x y : Fin S.rank → D.host.E, ∑ i, ∑ j, star (x i) * S.gram i j * y j = ∑ i, star (x i) * y i` using `fun x y => by simp [hS, Matrix.one_apply]`. Use `⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[stdL, Submodule.span_span_of_tower]`. Use `(Pi.basisFun D.host.E (Fin S.rank)).span_eq` as an intermediate fact. Simplify `this` using `only [Pi.basisFun_apply, funext (Pi.basisFun_apply D.host.E (Fin S.rank))]`.

Rewrite using `[e]`. Conclude with `⟨⟨∑ i, star (x i) * y i, IsIntegral.sum _ fun i _ => ((GlobalTheory.SW.Base.mem_stdL _).1 (star_mem_stdL hx) i).mul ((GlobalTheory.SW.Base.mem_stdL _).1 hy i)⟩, rfl⟩`. Use `(GlobalTheory.SW.Base.mem_stdL _).2 fun a => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite `hb` using `[e, Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]`.

Establish `: y a = b` using `by simp [hb]`. Rewrite using `[this]`. Conclude with `b.2`.
-/
theorem selfDualC_stdL {S : HSp D} (hS : S.gram = 1) : IsSelfDualC S (stdL D.host.E S.rank) := by
  have e : ∀ x y : Fin S.rank → D.host.E, ∑ i, ∑ j, star (x i) * S.gram i j * y j = ∑ i, star (x i) * y i :=
    fun x y => by simp [hS, Matrix.one_apply]
  refine ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [stdL, Submodule.span_span_of_tower]
    have := (Pi.basisFun D.host.E (Fin S.rank)).span_eq
    simpa only [Pi.basisFun_apply, funext (Pi.basisFun_apply D.host.E (Fin S.rank))] using this
  · rw [e]
    exact ⟨⟨∑ i, star (x i) * y i, IsIntegral.sum _ fun i _ => ((GlobalTheory.SW.Base.mem_stdL _).1 (star_mem_stdL hx) i).mul ((GlobalTheory.SW.Base.mem_stdL _).1 hy i)⟩, rfl⟩
  · refine (GlobalTheory.SW.Base.mem_stdL _).2 fun a => ?_
    obtain ⟨b, hb⟩ := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [e, Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)] at hb
    have : y a = b := by simp [hb]
    rw [this]
    exact b.2

/- English proof (translation)
Establish `key : ∀ y ∈ tens (stdL D.host.E S.rank) L, yᵀ ∈ GlobalTheory.LatVac.latRat S T (stdL D.host.E S.rank) (lattice₂ D L)`. Introduce `y hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨v, hv, u, hu, rfl⟩` from `hy`.

Rewrite `hu` using `[lat_eq_span Formalism.IndefR.Fin.factPrincipalDatum L]`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨a, ha, t, ht, rfl⟩` from `hu`. Use `AddSubgroup.subset_closure ⟨a, ha, _, star_mem_stdL hv, t, ht, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using `[GlobalTheory.LatVac.genMap, hS, Matrix.one_apply, vecMulVec_apply, mul_comm, mul_left_comm]`. Consider the case `zero => simp`. Consider the case `add u u' _ _ h h' => rw [vecMulVec_add, transpose_add]`. Conclude with `add_mem h h'`.

Consider the case `smul c u _ h`. Rewrite using `[O_smul, vecMulVec_smul, transpose_smul]`. Conclude with `GlobalTheory.LatVac.smul_mem_latRat c h`. Consider the case `zero => exact zero_mem _`. Consider the case `add _ _ _ _ h h' => rw [transpose_add]`.

Conclude with `add_mem h h'`. Consider the case `neg _ _ h => rw [transpose_neg]`. Conclude with `neg_mem h`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨α, hα, y, hy, rfl⟩`.

Conclude with `GlobalTheory.LatVac.finTens_mem_latO hα (key y hy)`.
-/
theorem hatA_le {S T : HSp D} (hS : S.gram = 1) (L : Lt D.host.E T.rank) :
    hatA S T (tens (stdL D.host.E S.rank) L) ≤ latO S T (stdL D.host.E S.rank) (lattice₂ D L) fun _ => True := by
  have key : ∀ y ∈ tens (stdL D.host.E S.rank) L,
      yᵀ ∈ GlobalTheory.LatVac.latRat S T (stdL D.host.E S.rank) (lattice₂ D L) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u, hu, rfl⟩ := hy
      rw [lat_eq_span Formalism.IndefR.Fin.factPrincipalDatum L] at hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hu
        refine AddSubgroup.subset_closure ⟨a, ha, _, star_mem_stdL hv, t, ht, ?_⟩
        ext i j
        simp [GlobalTheory.LatVac.genMap, hS, Matrix.one_apply, vecMulVec_apply, mul_comm, mul_left_comm]
      | zero => simp
      | add u u' _ _ h h' => rw [vecMulVec_add, transpose_add]; exact add_mem h h'
      | smul c u _ h =>
        rw [O_smul, vecMulVec_smul, transpose_smul]
        exact GlobalTheory.LatVac.smul_mem_latRat c h
    | zero => exact zero_mem _
    | add _ _ _ _ h h' => rw [transpose_add]; exact add_mem h h'
    | neg _ _ h => rw [transpose_neg]; exact neg_mem h
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, y, hy, rfl⟩
  exact GlobalTheory.LatVac.finTens_mem_latO hα (key y hy)

/- English proof (translation)
Establish `hsd : SelfD C.X (Lv.sh C.X.Λ)` using `selfD_idq Lv.ne_bot Lv.proper Lv.cop (selfD_of_sympl C.sympl)`. Establish `hsp : Submodule.span D.host.E (Lv.sh C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤`. Take `⟨p, hp, hp0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot Lv.ne_bot`. Establish `hp0' : (p : D.host.E) ≠ 0` using `by simpa using hp0`. Rewrite using `[eq_top_iff, ← C.X.Λ_span, Submodule.span_le]`.

Conclude with `fun v hv => (Submodule.smul_mem_iff _ hp0').1 (Submodule.subset_span (smul_le_idq _ _ _ (Submodule.smul_mem_smul hp hv)))`. Take `⟨f, f0, hf⟩` from `GlobalTheory.VacuumO.exists_ne_zero C.ψ C.θ C.std C.inf S T (fun _ => 1) (C.sB B) (fun τ => by`. Establish `: gramAt D S τ = 1` using `by rw [gramAt, C.m.gS]; exact Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite using `[this]`. Conclude with `⟨Matrix.one_mul _, by simp, by rw [Matrix.one_mul]; exact Matrix.PosDef.one⟩)`.

Use the proof step `(fun τ => cartan_of_on (sgnM_sq _) (sgnM_herm _) (hB τ)) _ _ (selfDualC_stdL C.m.gS)`. Use the proof step `(selfDualC_latP C.m.gT C.m.ka hsd hsp)`. Establish `h1` using `hf 1`. Simplify using `only [one_mul] at h1`. Establish `hle` using `hatA_le C.m.gS (Lv.sh C.X.Λ)`.

Conclude with `⟨f, h1.1, f0, h1.2.2, fun u hu => h1.2.1.1 u (hle hu), fun e he u hu => h1.2.1.2 e he u (hle hu)⟩`.
-/
theorem exists_base {S T : HSp D} (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas) (hB : C.IsB B) :
    ∃ f', C.IsBase Lv B f' := by
  have hsd : SelfD C.X (Lv.sh C.X.Λ) := selfD_idq Lv.ne_bot Lv.proper Lv.cop (selfD_of_sympl C.sympl)
  have hsp : Submodule.span D.host.E (Lv.sh C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ := by
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Lv.ne_bot
    have hp0' : (p : D.host.E) ≠ 0 := by simpa using hp0
    rw [eq_top_iff, ← C.X.Λ_span, Submodule.span_le]
    exact fun v hv => (Submodule.smul_mem_iff _ hp0').1
      (Submodule.subset_span (smul_le_idq _ _ _ (Submodule.smul_mem_smul hp hv)))
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero C.ψ C.θ C.std C.inf S T (fun _ => 1) (C.sB B)
    (fun τ => by
      have : gramAt D S τ = 1 := by rw [gramAt, C.m.gS]; exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [this]
      exact ⟨Matrix.one_mul _, by simp, by rw [Matrix.one_mul]; exact Matrix.PosDef.one⟩)
    (fun τ => cartan_of_on (sgnM_sq _) (sgnM_herm _) (hB τ)) _ _ (selfDualC_stdL C.m.gS)
    (selfDualC_latP C.m.gT C.m.ka hsd hsp)
  have h1 := hf 1
  simp only [one_mul] at h1
  have hle := hatA_le C.m.gS (Lv.sh C.X.Λ)
  exact ⟨f, h1.1, f0, h1.2.2, fun u hu => h1.2.1.1 u (hle hu), fun e he u hu => h1.2.1.2 e he u (hle hu)⟩

/- English proof (translation)
Use `⟨⟨0, 0, fun _ => ?_⟩, fun u _ z w => by simp⟩` and prove the remaining obligations. Rewrite using `[map_one]`. Use `Harm.mem_rowHighest_iff.2 ⟨Harm.isHarmonic_C 1, fun t a => ?_, fun t b => ?_, fun _ _ _ _ _ => map_one _, fun _ _ _ _ _ => map_one _⟩` and prove the remaining obligations. Simplify `MvPolynomial.isWeightedHomogeneous_one ℂ _` using `[Harm.partOf]`. Simplify `MvPolynomial.isWeightedHomogeneous_one ℂ _` using `[Harm.partOf]`.
-/
theorem isFam_one {S T : HSp D} (C : Ctx S T) : C.IsFam (fun _ : Fin 1 => 1) := by
  refine ⟨⟨0, 0, fun _ => ?_⟩, fun u _ z w => by simp⟩
  rw [map_one]
  refine Harm.mem_rowHighest_iff.2 ⟨Harm.isHarmonic_C 1, fun t a => ?_, fun t b => ?_,
    fun _ _ _ _ _ => map_one _, fun _ _ _ _ _ => map_one _⟩
  · simpa [Harm.partOf] using MvPolynomial.isWeightedHomogeneous_one ℂ _
  · simpa [Harm.partOf] using MvPolynomial.isWeightedHomogeneous_one ℂ _

/- English proof (translation)
Introduce `_ _ _ C` and use `⟨exists_level C.X, exists_base C, isFam_one C⟩`.
-/
theorem level_base_fam : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ Lv : GlobalTheory.SW.Level C.X, IdemTwo Lv.w) ∧ (∀ (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas), C.IsB B → ∃ f', C.IsBase Lv B f') ∧ C.IsFam (fun _ : Fin 1 => 1) :=
  fun _ _ _ C => ⟨exists_level C.X, exists_base C, isFam_one C⟩

end GlobalTheory.Ker.Base

end
