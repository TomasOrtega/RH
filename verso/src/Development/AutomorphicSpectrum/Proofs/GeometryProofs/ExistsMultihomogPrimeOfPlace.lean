import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre

section

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
  {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

/- English proof (translation)
Establish `hT : (∏ k, (X k : MvPolynomial B Ω) ^ e k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)`. Rewrite using `[mCoordIdeal, RingHom.mem_ker]`. Use `show mConeMap y g = 0 ↔ _`. Rewrite using `[GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.mConeMap_form y hg, mul_eq_zero, or_iff_right hT, C_eq_zero]`.
-/
theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) {g : MRing J} {e : B → ℕ}
    (hg : IsMultiHomog g e) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  have hT : (∏ k, (X k : MvPolynomial B Ω) ^ e k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  rw [mCoordIdeal, RingHom.mem_ker]
  show mConeMap y g = 0 ↔ _
  rw [GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.mConeMap_form y hg, mul_eq_zero, or_iff_right hT, C_eq_zero]

variable (v : Place (ZMod p) K) (w : (Σ k, J k) → K) (c : ∀ k, J k)

def ratio (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))
    (q : Σ k, J k) : v.ring :=
  ⟨w q / w ⟨q.1, c q.1⟩, by
    rw [← v.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hle q.1 q.2) zero_le'⟩

variable {v w c}
variable (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))

include hc in
/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)`.
-/
theorem prod_ne_zero (e : B → ℕ) : (∏ k, w ⟨k, c k⟩ ^ e k) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)

/- English proof (translation)
Rewrite using `[← GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue.aeval_div w c g e hg]`. Conclude with `MvPolynomial.comp_aeval_apply (φ := (algebraMap v.ring K).toIntAlgHom) _ g`.
-/
theorem coe_aeval_ratio {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    ((aeval (ratio v w c hc hle) g : v.ring) : K) = aeval w g * (∏ k, w ⟨k, c k⟩ ^ e k)⁻¹ := by
  rw [← GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue.aeval_div w c g e hg]
  exact MvPolynomial.comp_aeval_apply (φ := (algebraMap v.ring K).toIntAlgHom) _ g

/- English proof (translation)
The claim follows from `(MvPolynomial.comp_aeval_apply (φ := (residue v.ring).toIntAlgHom) _ g).symm`.
-/
theorem aeval_residue (g : MRing J) :
    aeval (fun q => residue v.ring (ratio v w c hc hle q)) g =
      residue v.ring (aeval (ratio v w c hc hle) g) :=
  (MvPolynomial.comp_aeval_apply (φ := (residue v.ring).toIntAlgHom) _ g).symm

/- English proof (translation)
Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun k _ => map_pow _ _ _`.
-/
theorem valuation_prod (e : B → ℕ) :
    v.valuation (∏ k, w ⟨k, c k⟩ ^ e k) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => map_pow _ _ _

include hc in
/- English proof (translation)
Rewrite using `[← valuation_prod]`. Conclude with `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (prod_ne_zero hc e))`.
-/
theorem prod_valuation_pos (e : B → ℕ) : 0 < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [← valuation_prod]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (prod_ne_zero hc e))

include hc hle in

/- English proof (translation)
Establish `h` using `(v.valuation_le_one_iff _).2 (aeval (ratio v w c hc hle) g).2`. Rewrite `h` using `[coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod]`. Rewrite `h` using `[mul_inv_le_iff₀ (prod_valuation_pos hc e), one_mul]`. Then use the resulting hypothesis.
-/
theorem valuation_aeval_le {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    v.valuation (aeval w g) ≤ ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  have h := (v.valuation_le_one_iff _).2 (aeval (ratio v w c hc hle) g).2
  rw [coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod] at h
  rwa [mul_inv_le_iff₀ (prod_valuation_pos hc e), one_mul] at h

/- English proof (translation)
Use `(mem_mCoordIdeal_iff _ hg).trans (Iff.trans (Eq.congr_left (aeval_residue hc hle g)) ?_)` and prove the remaining obligations. Rewrite using `[residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, ← v.valuation_lt_one_iff, coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod, mul_inv_lt_iff₀ (prod_valuation_pos hc e), one_mul]`.
-/
theorem mem_iff {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    g ∈ mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)) ↔
      v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  refine (mem_mCoordIdeal_iff _ hg).trans (Iff.trans (Eq.congr_left (aeval_residue hc hle g)) ?_)
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, ← v.valuation_lt_one_iff,
    coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod,
    mul_inv_lt_iff₀ (prod_valuation_pos hc e), one_mul]

end

/- English proof (translation)
Introduce `B _ J _ p _ K _ _ _ w v c hc hle`. Use `⟨mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)), RingHom.ker_isPrime _, GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _, ?_, ?_, ?_, fun e g hg => mem_iff hc hle hg⟩` and prove the remaining obligations. Take `⟨S, hS, hSe⟩` from `GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w`. Establish `hSV : Ideal.span S ≤ mCoordIdeal w` using `hSe.ge`. Rewrite using `[hSe, Ideal.span_le]`.

Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`. Establish `hf0 : aeval w f = 0` using `(mem_mCoordIdeal_iff w ha).1 (hSV (Ideal.subset_span hf))`. Use `(mem_iff hc hle ha).2 ?_` and prove the remaining obligations. Rewrite using `[hf0, map_zero]`.

Conclude with `prod_valuation_pos hc a`. Introduce `k h`. Establish `h1` using `(X_mem_iff _ k (c k)).1 h`. Establish `h2 : ratio v w c hc hle ⟨k, c k⟩ = 1` using `Subtype.ext (div_self (hc k))`. Rewrite `h1` using `[h2, map_one]`.

Conclude with `one_ne_zero h1`. Introduce `e g h hg hh hhW`. Establish `hh' : v.valuation (aeval w h) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k` using `le_antisymm (valuation_aeval_le hc hle hh) (not_lt.1 fun hlt => hhW ((mem_iff hc hle hh).2 hlt))`. Rewrite using `[hh']`. Conclude with `⟨valuation_aeval_le hc hle hg, (mem_iff hc hle hg).1⟩`.
-/
theorem exists_centre : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K)
    (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) →
    (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) →
    ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧
      (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧
      ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e →
        (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  intro B _ J _ p _ K _ _ _ w v c hc hle
  refine ⟨mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)), RingHom.ker_isPrime _,
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _, ?_, ?_, ?_, fun e g hg => mem_iff hc hle hg⟩
  · obtain ⟨S, hS, hSe⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
    have hSV : Ideal.span S ≤ mCoordIdeal w := hSe.ge
    rw [hSe, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have hf0 : aeval w f = 0 := (mem_mCoordIdeal_iff w ha).1 (hSV (Ideal.subset_span hf))
    refine (mem_iff hc hle ha).2 ?_
    rw [hf0, map_zero]
    exact prod_valuation_pos hc a
  · intro k h
    have h1 := (X_mem_iff _ k (c k)).1 h
    have h2 : ratio v w c hc hle ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
    rw [h2, map_one] at h1
    exact one_ne_zero h1
  · intro e g h hg hh hhW
    have hh' : v.valuation (aeval w h) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k :=
      le_antisymm (valuation_aeval_le hc hle hh) (not_lt.1 fun hlt => hhW ((mem_iff hc hle hh).2 hlt))
    rw [hh']
    exact ⟨valuation_aeval_le hc hle hg, (mem_iff hc hle hg).1⟩

end GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre
