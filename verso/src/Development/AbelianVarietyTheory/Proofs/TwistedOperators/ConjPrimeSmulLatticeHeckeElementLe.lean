import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeConjPart

open Formalism.L2.NTheta GlobalTheory.SplitPlace IsDedekindDomain

variable {D : D7}

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Conclude with `zero_le'`. Take `⟨u, rfl⟩` from `WithZero.ne_zero_iff_exists.1 hx`. Rewrite `h` using `[← WithZero.coe_one, WithZero.coe_lt_coe]`. Rewrite using `[WithZero.coe_le_coe]`.

Rewrite `h` using `[← Multiplicative.toAdd_lt, toAdd_one]`. Rewrite using `[← Multiplicative.toAdd_le, toAdd_ofAdd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_unif {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
  rw [WithZero.coe_le_coe]
  rw [← Multiplicative.toAdd_lt, toAdd_one] at h
  rw [← Multiplicative.toAdd_le, toAdd_ofAdd]
  omega

/- English proof (translation)
Take `⟨v, π, s, h1, h2, h3, h4, h5⟩` from `GlobalTheory.SplitCoord.exists_coord e he.1`. Establish `hu` using `isUnif he h4 h5 ϖ hP hP2`. Establish `hϖ0 : (ϖ : D.host.E) ≠ 0`. Introduce `h0`. Apply `hP2` to reduce the goal to its premises.

Rewrite using `[show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]`. Conclude with `zero_mem _`. Use `set φ : D.host.E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v := (π.comp (finPart D)).comp (incA D) with hφ`. Use `set q : D.host.E := (y : D.host.E) / (ϖ : D.host.E)`. Use `⟨finPart D e * finPart D (incA D q), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[h4]`. Express the relevant statement in the definitionally equal form `Valued.v (φ q) ≤ 1`. Rewrite using `[map_div₀, map_div₀]`. Break down `eq_or_ne y 0 with rfl | hy0` into its components or cases. Simplify using the standard rewrite rules.

Establish `hn` using `(he.2 y hy0).1 hy`. Rewrite `hn` using `[map_mul, h4]`. Express the relevant statement in the definitionally equal form `¬ Valued.v (φ ((y : D.host.E)⁻¹)) ≤ 1 at hn`. Rewrite `hn` using `[map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 fun h0 => hy0 (RingOfIntegers.coe_eq_zero_iff.1 h0))))]`. Establish `hϖv : Valued.v (φ ϖ) = _` using `hu`.

Establish `h6` using `le_unif hn`. Rewrite `h6` using `[← hϖv]`. Rewrite using `[div_le_one₀ (by rw [hϖv]; exact zero_lt_iff.2 WithZero.coe_ne_zero)]`. Conclude with `h6`. Establish `hee : finPart D e * finPart D e = finPart D e` using `by rw [← map_mul, he.1.1]`.

Establish `hq : q * (ϖ : D.host.E) = y` using `div_mul_cancel₀ _ hϖ0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hee, ← map_mul (finPart D) (incA D q), ← map_mul (incA D) q, hq]`. Use `_ = _ := mul_mul_mul_comm _ _ _ _`.
-/
theorem ratio_int {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {y : 𝓞 D.host.E} (hy : y ∈ P.asIdeal) :
    ∃ t ∈ intAE D, finPart D e * finPart D (incA D (y : D.host.E)) =
      t * (finPart D e * finPart D (incA D (ϖ : D.host.E))) := by
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  have hu := isUnif he h4 h5 ϖ hP hP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0
    apply hP2
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _
  set φ : D.host.E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v := (π.comp (finPart D)).comp (incA D) with hφ
  set q : D.host.E := (y : D.host.E) / (ϖ : D.host.E)
  refine ⟨finPart D e * finPart D (incA D q), ?_, ?_⟩
  · rw [h4]
    change Valued.v (φ q) ≤ 1
    rw [map_div₀, map_div₀]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have hn := (he.2 y hy0).1 hy
    rw [map_mul, h4] at hn
    change ¬ Valued.v (φ ((y : D.host.E)⁻¹)) ≤ 1 at hn
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 fun h0 => hy0 (RingOfIntegers.coe_eq_zero_iff.1 h0))))] at hn
    have hϖv : Valued.v (φ ϖ) = _ := hu
    have h6 := le_unif hn
    rw [← hϖv] at h6
    rw [div_le_one₀ (by rw [hϖv]; exact zero_lt_iff.2 WithZero.coe_ne_zero)]
    exact h6
  · have hee : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
    have hq : q * (ϖ : D.host.E) = y := div_mul_cancel₀ _ hϖ0
    calc finPart D e * finPart D (incA D (y : D.host.E))
        = (finPart D e * finPart D e) * (finPart D (incA D q) * finPart D (incA D (ϖ : D.host.E))) := by
          rw [hee, ← map_mul (finPart D) (incA D q), ← map_mul (incA D) q, hq]
      _ = _ := mul_mul_mul_comm _ _ _ _

open scoped Matrix

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `z hz`. Establish `hee : e * e = e` using `he.1.1`. Establish `hint : finPart D (incA D (x : D.host.E)) ∈ intAE D` using `AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩`. Establish `hc` using `hecke_conj hee ha`. Establish `hce : cA D e * cA D e = cA D e` using `by rw [← map_mul, hee]`.

Establish `h4` using `(lower_iff hce V _ a₀⁻¹).1 hc.2.2.2.1`. Rewrite `h4` using `[inv_inv]`. Take `⟨t, ht, hteq⟩` from `ratio_int he hP hP2 ((Formalism.L2.Col.mem_conjP P x).1 hx)`. Establish `hteq'` using `congrArg (cf D) hteq`. Rewrite `hteq'` using `[map_mul, map_mul, map_mul, ← fin_cA, ← fin_cA, ← fin_cA, cA_incA, cA_incA]`.

Establish `hsx : star ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E)`. Express the relevant statement in the definitionally equal form `star (star (x : D.host.E)) = _`. Conclude with `star_star _`. Rewrite `hteq'` using `[hsx]`. Establish `h6` using `mulVec_parts (finPart D) ((suppAt_iff e V a₀).1 ha.2.1) z`.

Rewrite `h6` using `[← fm_eq V a₀]`. Rewrite using `[h6, RingHom.map_add, add_smul, smul_sub, smul_add, smul_add]`. Establish `hi1` using `idem_mem hee`. Establish `hi2` using `idem_mem hce`. Use `sub_mem (add_mem (add_mem ?_ ?_) (smul_mem V hint hz)) (smul_mem V hint (smul_mem V (add_mem hi1 hi2) hz))` and prove the remaining obligations.

Conclude with `smul_mem V hint (ha.2.2.1 z hz)`. Rewrite using `[smul_smul, mul_comm, hteq', mul_smul]`. Conclude with `smul_mem V (cf_mem ht) (h4 z hz)`.
-/
theorem keeps {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ z ∈ LamHat V, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z ∈ LamHat V := by
  intro z hz
  have hee : e * e = e := he.1.1
  have hint : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩
  have hc := hecke_conj hee ha
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have h4 := (lower_iff hce V _ a₀⁻¹).1 hc.2.2.2.1
  rw [inv_inv] at h4
  obtain ⟨t, ht, hteq⟩ := ratio_int he hP hP2 ((Formalism.L2.Col.mem_conjP P x).1 hx)
  have hteq' := congrArg (cf D) hteq
  rw [map_mul, map_mul, map_mul, ← fin_cA, ← fin_cA, ← fin_cA, cA_incA, cA_incA] at hteq'
  have hsx : star ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := by
    change star (star (x : D.host.E)) = _
    exact star_star _
  rw [hsx] at hteq'
  have h6 := mulVec_parts (finPart D) ((suppAt_iff e V a₀).1 ha.2.1) z
  rw [← fm_eq V a₀] at h6
  rw [h6, RingHom.map_add, add_smul, smul_sub, smul_add, smul_add]
  have hi1 := idem_mem hee
  have hi2 := idem_mem hce
  refine sub_mem (add_mem (add_mem ?_ ?_) (smul_mem V hint hz))
    (smul_mem V hint (smul_mem V (add_mem hi1 hi2) hz))
  · exact smul_mem V hint (ha.2.2.1 z hz)
  · rw [smul_smul, mul_comm, hteq', mul_smul]
    exact smul_mem V (cf_mem ht) (h4 z hz)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finHom_eq {V : HSp D} (g : GA D V) : (finHom V g).1 = fm V g := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finPart_incA (c : D.host.E) :
    finPart D (incA D c) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c := rfl

/- English proof (translation)
Introduce `y hy`. Rewrite `hy`, the goal using `[GlobalTheory.LevelActionPinned.latGHat_one]`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨c, hc, z, hz, rfl⟩` from `hw`.

Use `AddSubgroup.subset_closure ⟨c, hc, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hz`, the goal using `[GlobalTheory.StdFrameCong.pj_latHat_eq]`. Conclude with `keeps he hP hP2 ha hx z hz`. Rewrite using `[Matrix.mulVec_smul, smul_comm]`. Consider the case `zero => rw [Matrix.mulVec_zero, smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha' hb' => rw [Matrix.mulVec_add, smul_add]`. Conclude with `add_mem ha' hb'`. Consider the case `neg a _ ha' => rw [Matrix.mulVec_neg, smul_neg]`. Conclude with `neg_mem ha'`.
-/
theorem keeps_one {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ y ∈ latGHat V 1, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y ∈ latGHat V 1 := by
  intro y hy
  rw [GlobalTheory.LevelActionPinned.latGHat_one] at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c, hc, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z, ?_, ?_⟩
    · rw [GlobalTheory.StdFrameCong.pj_latHat_eq] at hz ⊢
      exact keeps he hP hP2 ha hx z hz
    · rw [Matrix.mulVec_smul, smul_comm]
  | zero => rw [Matrix.mulVec_zero, smul_zero]; exact zero_mem _
  | add a b _ _ ha' hb' => rw [Matrix.mulVec_add, smul_add]; exact add_mem ha' hb'
  | neg a _ ha' => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem ha'

end GlobalTheory.HeckeConjPart

open scoped Matrix

open GlobalTheory.SplitPlace in

/- English proof (translation)
Introduce `D V P e ϖ k g a₀ he hP hP2 ha`. Rewrite using `[Submodule.smul_le]`. Introduce `x hx v hv`. Establish `spec` using `GlobalTheory.MarkCoset.latG_spec D V`. Rewrite `hv` using `[(spec (g * a₀)).1, (spec (g * a₀)).2]`.

Take `⟨y, hy, hyv⟩` from `hv`. Rewrite using `[(spec g).1, (spec g).2]`. Use `⟨finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y, GlobalTheory.HeckeConjPart.keeps_one he hP hP2 ha hx y hy, ?_⟩` and prove the remaining obligations. Rewrite `hyv`, the goal using `[GlobalTheory.HeckeConjPart.finHom_eq]`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← fm_mul, hyv]`.

Use function extensionality and compare the values at `i`. Simplify using `only [finVec, Pi.smul_apply, smul_eq_mul, GlobalTheory.HeckeConjPart.finPart_incA, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.HeckeConjPart.conj_part : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E)
    (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  intro D V P e ϖ k g a₀ he hP hP2 ha
  rw [Submodule.smul_le]
  intro x hx v hv
  have spec := GlobalTheory.MarkCoset.latG_spec D V
  rw [(spec (g * a₀)).1, (spec (g * a₀)).2] at hv
  obtain ⟨y, hy, hyv⟩ := hv
  rw [(spec g).1, (spec g).2]
  refine ⟨finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y, GlobalTheory.HeckeConjPart.keeps_one he hP hP2 ha hx y hy, ?_⟩
  rw [GlobalTheory.HeckeConjPart.finHom_eq] at hyv ⊢
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← fm_mul, hyv]
  funext i
  simp only [finVec, Pi.smul_apply, smul_eq_mul, GlobalTheory.HeckeConjPart.finPart_incA,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl
