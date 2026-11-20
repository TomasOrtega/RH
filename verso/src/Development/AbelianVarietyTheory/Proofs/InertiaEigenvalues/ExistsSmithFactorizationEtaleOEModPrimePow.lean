import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmithFormCoefficientRingImageOrPrimeDvdRowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittCompletedTiltColumnsOfRightInverseModPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.SmithQuot

/- English proof (translation)
Introduce `l _ K bk`. Use `haveI : PerfectRing (Cb l) l := GlobalTheory.OEDvr.perfectRing_Cb`. Take `⟨hdivl, -, -, hfac, -⟩` from `GlobalTheory.OEDvr.main l K bk`. Establish `hlW : Irreducible ((l : ℕ) : WCb l)` using `WittVector.irreducible l (k := Cb l)`. Establish `hlO : (l : WCb l) ∈ bk.OE` using `natCast_mem _ l`.

Use `set π : ↥bk.OE := ⟨(l : WCb l), hlO⟩`. Establish `hπ : ¬ IsUnit π` using `fun h => hlW.not_isUnit (h.map bk.OE.subtype)`. Establish `hfac' : ∀ x : ↥bk.OE, x ≠ 0 → ∃ k : ℕ, Associated (π ^ k) x`. Introduce `x hx`. Take `⟨k, v, v', hv, hv', hvv, hx'⟩` from `hfac x x.2 (fun h => hx (Subtype.ext h))`.

Use `⟨k, ⟨⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext hvv, Subtype.ext (by rw [mul_comm]; exact hvv)⟩, ?_⟩⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[π, hx']`. Establish `hunit : ∀ x : ↥bk.OE, IsUnit (x : WCb l) → IsUnit x`. Introduce `x hx`.

Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hx`. Take `⟨k, hk⟩` from `hfac' x hx0`. Break down `k with _ | k` into its components or cases. Conclude with `hk.isUnit_iff.mp (by rw [pow_zero]; exact isUnit_one)`. It suffices to derive a contradiction.

Take `⟨u, hu⟩` from `hk`. Establish `: (l : WCb l) ∣ (x : WCb l)`. Rewrite using `[← hu]; exact ⟨(l : WCb l) ^ k * (u : ↥bk.OE), by simp [π, pow_succ]; ring⟩`. Conclude with `hlW.not_isUnit (isUnit_of_dvd_unit this hx)`. Establish `hirr : Irreducible π`.

Use `⟨hπ, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Use `hlW.isUnit_or_isUnit (show ((l : ℕ) : WCb l) = (a : WCb l) * (b : WCb l) from congrArg Subtype.val hab)` as an intermediate fact. Conclude with `this.imp (hunit a) (hunit b)`. Conclude with `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, fun {x} hx => hfac' x hx⟩`.
-/
theorem oe_dvr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsDiscreteValuationRing ↥bk.OE := by
  intro l _ K bk
  haveI : PerfectRing (Cb l) l := GlobalTheory.OEDvr.perfectRing_Cb
  obtain ⟨hdivl, -, -, hfac, -⟩ := GlobalTheory.OEDvr.main l K bk
  have hlW : Irreducible ((l : ℕ) : WCb l) := WittVector.irreducible l (k := Cb l)
  have hlO : (l : WCb l) ∈ bk.OE := natCast_mem _ l
  set π : ↥bk.OE := ⟨(l : WCb l), hlO⟩
  have hπ : ¬ IsUnit π := fun h => hlW.not_isUnit (h.map bk.OE.subtype)
  have hfac' : ∀ x : ↥bk.OE, x ≠ 0 → ∃ k : ℕ, Associated (π ^ k) x := by
    intro x hx
    obtain ⟨k, v, v', hv, hv', hvv, hx'⟩ := hfac x x.2 (fun h => hx (Subtype.ext h))
    refine ⟨k, ⟨⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext hvv, Subtype.ext (by rw [mul_comm]; exact hvv)⟩, ?_⟩⟩
    apply Subtype.ext
    simp [π, hx']
  have hunit : ∀ x : ↥bk.OE, IsUnit (x : WCb l) → IsUnit x := by
    intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    obtain ⟨k, hk⟩ := hfac' x hx0
    rcases k with _ | k
    · exact hk.isUnit_iff.mp (by rw [pow_zero]; exact isUnit_one)
    · exfalso
      obtain ⟨u, hu⟩ := hk
      have : (l : WCb l) ∣ (x : WCb l) := by
        rw [← hu]; exact ⟨(l : WCb l) ^ k * (u : ↥bk.OE), by simp [π, pow_succ]; ring⟩
      exact hlW.not_isUnit (isUnit_of_dvd_unit this hx)
  have hirr : Irreducible π := by
    refine ⟨hπ, ?_⟩
    intro a b hab
    have := hlW.isUnit_or_isUnit (show ((l : ℕ) : WCb l) = (a : WCb l) * (b : WCb l) from congrArg Subtype.val hab)
    exact this.imp (hunit a) (hunit b)
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, fun {x} hx => hfac' x hx⟩

/- English proof (translation)
Introduce `l _ K bk d d' n Q P hn hP hS hker`. Take `⟨S, hS⟩` from `hS`. Take `⟨U, Uinv, hU, hUi, h1, h2, hdich⟩` from `GlobalTheory.T.smith_form_coefficientRing_image_or_prime_dvd_row l K bk (oe_dvr l K bk) d' P hP`. Set `J : Finset (Fin d')` to `Finset.univ.filter (fun j => ¬ ∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w)`. Establish `hi : ∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j`.

Introduce `j hj i`. Simplify using `only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj`. Use `(hker (fun i => U i j)).mpr hj i` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hii : ∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j`.

Introduce `v hv j hj`. Take `⟨w, rfl⟩` from `(hker v).mp hv`. Simplify using `only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj`. Establish `hr` using `(hdich j).resolve_left hj`. Rewrite using `[Matrix.mulVec_mulVec]`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Finset.dvd_sum (fun k _ => (hr k).mul_right _)`. Take `⟨e, hunit, hdiv⟩` from `GlobalTheory.T.wittCompletedTilt_columns_of_right_inverse_mod_pow l d d' n Q S U Uinv J hn hS h1 h2 hi hii`. Use `⟨Q * U.submatrix id (fun k => (e k : Fin d')), Uinv.submatrix (fun k => (e k : Fin d')) id, U.submatrix id (fun k => (e k : Fin d')), hunit, fun i j => hUi _ _, fun i j => hU _ _, hdiv, ?_⟩` and prove the remaining obligations. Introduce `i j`.

Simplify using `[Matrix.mul_submatrix_one, Matrix.submatrix]`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (P : Matrix (Fin d') (Fin d') (WCb l)), 1 ≤ n → (∀ i j, P i j ∈ bk.OE) → (∃ S : Matrix (Fin d') (Fin d) (WCb l), (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) ↔ ∃ w, v = P *ᵥ w) → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q * R' - Tn) i j) := by
  intro l _ K bk d d' n Q P hn hP hS hker
  obtain ⟨S, hS⟩ := hS
  obtain ⟨U, Uinv, hU, hUi, h1, h2, hdich⟩ := GlobalTheory.T.smith_form_coefficientRing_image_or_prime_dvd_row l K bk (oe_dvr l K bk) d' P hP
  classical
  let J : Finset (Fin d') := Finset.univ.filter (fun j => ¬ ∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w)
  have hi : ∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j := by
    intro j hj i
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    have := (hker (fun i => U i j)).mpr hj i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hii : ∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j := by
    intro v hv j hj
    obtain ⟨w, rfl⟩ := (hker v).mp hv
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hr := (hdich j).resolve_left hj
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum (fun k _ => (hr k).mul_right _)
  obtain ⟨e, hunit, hdiv⟩ := GlobalTheory.T.wittCompletedTilt_columns_of_right_inverse_mod_pow l d d' n Q S U Uinv J hn hS h1 h2 hi hii
  refine ⟨Q * U.submatrix id (fun k => (e k : Fin d')), Uinv.submatrix (fun k => (e k : Fin d')) id,
    U.submatrix id (fun k => (e k : Fin d')), hunit, fun i j => hUi _ _, fun i j => hU _ _, hdiv, ?_⟩
  intro i j
  simp [Matrix.mul_submatrix_one, Matrix.submatrix]

end GlobalTheory.SmithQuot
