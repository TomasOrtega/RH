import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndep
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Matrix
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

def vol {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : IdE D :=
  Submodule.span (𝓞 D.host.E)
    {x | ∃ U : Matrix (Fin N) (Fin N) D.host.E, (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`.
-/
theorem mulVec_col {N : ℕ} (A U : Matrix (Fin N) (Fin N) D.host.E) (j : Fin N) :
    A *ᵥ (fun i => U i j) = fun i => (A * U) i j := by
  funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

/- English proof (translation)
Unfold `detId vol`. Rewrite using `[Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨A, hA, rfl⟩, _, ⟨U, hU, rfl⟩, rfl⟩`. Use `Submodule.subset_span ⟨A * U, fun j => ?_, (det_mul A U).symm⟩` and prove the remaining obligations. Rewrite using `[← mulVec_col]`.

Conclude with `hA _ (hU j)`.
-/
theorem detId_mul_vol_le {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    detId D L L' * vol D L ≤ vol D L' := by
  unfold detId vol
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨A, hA, rfl⟩, _, ⟨U, hU, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨A * U, fun j => ?_, (det_mul A U).symm⟩
  rw [← mulVec_col]; exact hA _ (hU j)

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[CU.mem_cS]`. Establish `key : ∀ y ∈ Submodule.span (𝓞 D.host.E) S, D.host.conj y ∈ Submodule.span (𝓞 D.host.E) (D.host.conj '' S)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `smul r a _ ha => rw [CU.conj_smul]`.

Conclude with `Submodule.smul_mem _ _ ha`. Use `key _ hx` as an intermediate fact. Rewrite `this` using `[CU.conj_conj]`. Then use the resulting hypothesis.
-/
theorem cS_span_le (S : Set D.host.E) :
    CU.cS D (Submodule.span (𝓞 D.host.E) S) ≤ Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
  intro x hx
  rw [CU.mem_cS] at hx
  have key : ∀ y ∈ Submodule.span (𝓞 D.host.E) S,
      D.host.conj y ∈ Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r a _ ha => rw [CU.conj_smul]; exact Submodule.smul_mem _ _ ha
  have := key _ hx
  rwa [CU.conj_conj] at this

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[CU.mem_cS, CU.mem_cS, CU.conj_conj]`.
-/
theorem cS_cS (𝔞 : IdE D) : CU.cS D (CU.cS D 𝔞) = 𝔞 := by
  ext x; rw [CU.mem_cS, CU.mem_cS, CU.conj_conj]

/- English proof (translation)
Set `_` to `D.host.cmStar`. Use `(mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_` and prove the remaining obligations. Unfold `vol detId`. Rewrite using `[Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩`.

Use `Submodule.subset_span ⟨V * Wᴴ, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ i, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ *ᵥ x) i`. Introduce `i`. Take `⟨r, hr⟩` from `hL x hx _ (hW i)`. Use `⟨r, hr.trans ?_⟩` and prove the remaining obligations.

Simplify using `[stdH, Matrix.mulVec, dotProduct, conjTranspose_apply]`. Use `choose r hr using hc`. Establish `e : (V * Wᴴ) *ᵥ x = ∑ i, r i • (fun k => V k i)`. Rewrite using `[← mulVec_mulVec]`. Use function extensionality and compare the values at `k`.

Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hr i, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hV i)`. Rewrite using `[det_mul, det_conjTranspose, CU.star_conj]`.
-/
theorem vol_mul_cS_le {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    vol D L' * CU.cS D (vol D L) ≤ detId D L L' := by
  let _ := D.host.cmStar
  refine (mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_
  unfold vol detId
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨V * Wᴴ, fun x hx => ?_, ?_⟩
  · have hc : ∀ i, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ *ᵥ x) i := by
      intro i
      obtain ⟨r, hr⟩ := hL x hx _ (hW i)
      refine ⟨r, hr.trans ?_⟩
      simp [stdH, Matrix.mulVec, dotProduct, conjTranspose_apply]
    choose r hr using hc
    have e : (V * Wᴴ) *ᵥ x = ∑ i, r i • (fun k => V k i) := by
      rw [← mulVec_mulVec]
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr i, mul_comm]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hV i)
  · rw [det_mul, det_conjTranspose, CU.star_conj]

/- English proof (translation)
Set `_` to `D.host.cmStar`. Use `(mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_` and prove the remaining obligations. Unfold `vol`. Rewrite using `[Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩`.

Establish `hc : ∀ i j, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ * V) i j`. Introduce `i j`. Take `⟨r, hr⟩` from `hL _ (hV j) _ (hW i)`. Use `⟨r, hr.trans ?_⟩` and prove the remaining obligations. Simplify using `[stdH, Matrix.mul_apply, conjTranspose_apply]`.

Use `choose r hr using hc`. Establish `e : Wᴴ * V = (Matrix.of r).map (algebraMap (𝓞 D.host.E) D.host.E)`. Use extensionality with `i j`. Simplify using `[hr]`. Use `show _ ∈ (1 : IdE D)`.

Rewrite using `[Submodule.mem_one, ← CU.star_conj, ← det_conjTranspose]`. Use `⟨(Matrix.of r).det, ?_⟩` and prove the remaining obligations. Establish `h2 : algebraMap (𝓞 D.host.E) D.host.E (Matrix.of r).det = (Wᴴ * V).det`. Rewrite using `[e, RingHom.map_det]`. Both sides reduce to the same expression.

Rewrite using `[h2, det_mul]`. Conclude with `mul_comm _ _`.
-/
theorem vol_mul_cS_le_one {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    vol D L * CU.cS D (vol D L) ≤ 1 := by
  let _ := D.host.cmStar
  refine (mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_
  unfold vol
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩
  have hc : ∀ i j, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ * V) i j := by
    intro i j
    obtain ⟨r, hr⟩ := hL _ (hV j) _ (hW i)
    refine ⟨r, hr.trans ?_⟩
    simp [stdH, Matrix.mul_apply, conjTranspose_apply]
  choose r hr using hc
  have e : Wᴴ * V = (Matrix.of r).map (algebraMap (𝓞 D.host.E) D.host.E) := by
    ext i j; simp [hr]
  show _ ∈ (1 : IdE D)
  rw [Submodule.mem_one, ← CU.star_conj, ← det_conjTranspose]
  refine ⟨(Matrix.of r).det, ?_⟩
  have h2 : algebraMap (𝓞 D.host.E) D.host.E (Matrix.of r).det = (Wᴴ * V).det := by
    rw [e, RingHom.map_det]; rfl
  rw [h2, det_mul]
  exact mul_comm _ _

/- English proof (translation)
Introduce `x hx w hw` and use `(hL.2.2 x).1 hx w hw`.
-/
theorem sd_int {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  fun x hx w hw => (hL.2.2 x).1 hx w hw

def UnitDisc (D : Car) : Prop :=
  let _ := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsSDLat D.host.E N L →
    1 ≤ vol D L * CU.cS D (vol D L)

/- English proof (translation)
Set `_` to `D.host.cmStar`. Introduce `N L L' _ hL hL'`. Establish `e1 : vol D L * CU.cS D (vol D L) = 1` using `le_antisymm (vol_mul_cS_le_one D L (sd_int D hL)) (hU N L hL)`. Establish `e2 : vol D L' * CU.cS D (vol D L') = 1` using `le_antisymm (vol_mul_cS_le_one D L' (sd_int D hL')) (hU N L' hL')`. Establish `hA : detId D L L' = vol D L' * CU.cS D (vol D L)`.

Use `le_antisymm ?_ (vol_mul_cS_le D L L' (sd_int D hL))` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[CU.normOne_ideal_iff_mul_conj, hA, CU.cS_mul, cS_cS]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem determinant_norm_one_of_unit_disc (hU : UnitDisc D) : DetIdealsKernelNormOne D := by
  let _ := D.host.cmStar
  intro N L L' _ hL hL'
  have e1 : vol D L * CU.cS D (vol D L) = 1 :=
    le_antisymm (vol_mul_cS_le_one D L (sd_int D hL)) (hU N L hL)
  have e2 : vol D L' * CU.cS D (vol D L') = 1 :=
    le_antisymm (vol_mul_cS_le_one D L' (sd_int D hL')) (hU N L' hL')
  have hA : detId D L L' = vol D L' * CU.cS D (vol D L) := by
    refine le_antisymm ?_ (vol_mul_cS_le D L L' (sd_int D hL))
    calc detId D L L' = detId D L L' * (vol D L * CU.cS D (vol D L)) := by rw [e1, mul_one]
      _ = detId D L L' * vol D L * CU.cS D (vol D L) := by rw [mul_assoc]
      _ ≤ vol D L' * CU.cS D (vol D L) :=
          mul_le_mul' (detId_mul_vol_le D L L') (le_refl _)
  rw [CU.normOne_ideal_iff_mul_conj, hA, CU.cS_mul, cS_cS]
  calc vol D L' * CU.cS D (vol D L) * (CU.cS D (vol D L') * vol D L)
      = (vol D L' * CU.cS D (vol D L')) * (vol D L * CU.cS D (vol D L)) := by ring
    _ = 1 := by rw [e1, e2, mul_one]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Matrix
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

/- English proof (translation)
Set `_` to `D.host.cmStar`. Use `Submodule.subset_span ⟨(adjugate U)ᴴ * diagonal t, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `(hL.2.2 _).2 fun x hx => ?_` and prove the remaining obligations. Establish `hdet : (U.updateCol i x).det ∈ vol D L`. Use `Submodule.subset_span ⟨U.updateCol i x, fun j => ?_, rfl⟩` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Use `hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Use `hU j using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[hj]`. Establish `hb : star (U.updateCol i x).det ∈ CU.cS D (vol D L)`. Rewrite using `[CU.mem_cS, ← CU.star_conj, star_star]`.

Conclude with `hdet`. Take `⟨r, hr⟩` from `Submodule.mem_one.mp (ht i _ hb)`. Use `⟨r, hr.trans ?_⟩` and prove the remaining obligations. Rewrite using `[← cramer_apply, cramer_eq_adjugate_mulVec]`. Simplify using `only [stdH, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_diagonal, conjTranspose_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[det_mul, det_diagonal, det_conjTranspose, det_adjugate, Fintype.card_fin, star_pow, CU.star_conj]`.
-/
theorem adj_step {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (U : Matrix (Fin N) (Fin N) D.host.E) (hU : ∀ j, (fun i => U i j) ∈ L) (t : Fin N → D.host.E)
    (ht : ∀ i, ∀ b ∈ CU.cS D (vol D L), t i * b ∈ (1 : IdE D)) :
    D.host.conj U.det ^ (N - 1) * ∏ i, t i ∈ vol D L := by
  let _ := D.host.cmStar
  refine Submodule.subset_span ⟨(adjugate U)ᴴ * diagonal t, fun i => ?_, ?_⟩
  · refine (hL.2.2 _).2 fun x hx => ?_
    have hdet : (U.updateCol i x).det ∈ vol D L := by
      refine Submodule.subset_span ⟨U.updateCol i x, fun j => ?_, rfl⟩
      by_cases hj : j = i
      · subst hj; convert hx using 1; funext k; simp
      · convert hU j using 1; funext k; simp [hj]
    have hb : star (U.updateCol i x).det ∈ CU.cS D (vol D L) := by
      rw [CU.mem_cS, ← CU.star_conj, star_star]; exact hdet
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (ht i _ hb)
    refine ⟨r, hr.trans ?_⟩
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp only [stdH, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_diagonal,
      conjTranspose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [det_mul, det_diagonal, det_conjTranspose, det_adjugate, Fintype.card_fin, star_pow,
      CU.star_conj]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Matrix nonZeroDivisors
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

open FractionalIdeal in

/- English proof (translation)
Use `set Q := Submodule.span R ((fun s => s ^ k) '' S)`. Establish `hQle : Q ≤ ((I ^ k : FractionalIdeal R⁰ K) : Submodule R K)`. Rewrite using `[coe_pow, Submodule.span_le]`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `Submodule.pow_mem_pow _ (hIS ▸ Submodule.subset_span hs) k`.

Set `Qf : FractionalIdeal R⁰ K` to `⟨Q, isFractional_of_le hQle⟩`. Establish `hQf : Qf ≤ I ^ k` using `hQle`. Establish `hIk : I ^ k ≠ 0` using `pow_ne_zero _ hI`. It suffices to establish `h : I ^ k ≤ Qf by`. Rewrite using `[← coe_pow]`.

Conclude with `h`. Assume the negation of the conclusion as `hne`. Establish `hb : Qf * (I ^ k)⁻¹ ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨B, hB⟩` from `le_one_iff_exists_coeIdeal.mp hb`.

Establish `hBtop : B ≠ ⊤`. Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises. Establish `h1 : Qf * (I ^ k)⁻¹ = 1` using `by rw [← hB, coeIdeal_top]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨P, hPmax, hBP⟩` from `Ideal.exists_le_maximal B hBtop`. Use `hPmax.isPrime` as an intermediate fact. Establish `hstep : ∀ s ∈ S, s ∈ ((P : FractionalIdeal R⁰ K) * I)`. Introduce `s hs`. Establish `hsI : spanSingleton R⁰ s ≤ I`.

Rewrite using `[spanSingleton_le_iff_mem, ← mem_coe, hIS]`. Conclude with `Submodule.subset_span hs`. Establish `hc : spanSingleton R⁰ s * I⁻¹ ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨C, hC⟩` from `le_one_iff_exists_coeIdeal.mp hc`.

Establish `hCk : C ^ k ≤ P`. Rewrite using `[← coeIdeal_le_coeIdeal K, coeIdeal_pow, hC, mul_pow, spanSingleton_pow, inv_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul' ?_ le_rfl` and prove the remaining obligations. Rewrite using `[spanSingleton_le_iff_mem]`.

Conclude with `Submodule.subset_span ⟨s, hs, rfl⟩`. Use `_ = B := hB.symm`. Use `_ ≤ P := (coeIdeal_le_coeIdeal K).mpr hBP`. Establish `hCP : C ≤ P` using `Ideal.IsPrime.le_of_pow_le hCk`. Establish `h2 : spanSingleton R⁰ s * I⁻¹ ≤ P` using `hC ▸ (coeIdeal_le_coeIdeal K).mpr hCP`.

Establish `h3 : spanSingleton R⁰ s ≤ (P : FractionalIdeal R⁰ K) * I`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, inv_mul_cancel₀ hI, mul_one]`. Use `_ ≤ P * I := mul_le_mul' h2 le_rfl`. Conclude with `spanSingleton_le_iff_mem.mp h3`.

Establish `hIP : I ≤ (P : FractionalIdeal R⁰ K) * I`. Rewrite using `[← coe_le_coe, hIS, Submodule.span_le]`. Introduce `s hs`. Conclude with `mem_coe.mpr (hstep s hs)`. Establish `h1P : (1 : FractionalIdeal R⁰ K) ≤ P`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `h1P` using `[← coeIdeal_top, coeIdeal_le_coeIdeal]`. Conclude with `hPmax.ne_top (top_le_iff.mp h1P)`.
-/
theorem spanPow {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (S : Set K)
    (hIS : (I : Submodule R K) = Submodule.span R S) (k : ℕ) :
    (I : Submodule R K) ^ k ≤ Submodule.span R ((fun s => s ^ k) '' S) := by
  classical
  set Q := Submodule.span R ((fun s => s ^ k) '' S)
  have hQle : Q ≤ ((I ^ k : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [coe_pow, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact Submodule.pow_mem_pow _ (hIS ▸ Submodule.subset_span hs) k
  let Qf : FractionalIdeal R⁰ K := ⟨Q, isFractional_of_le hQle⟩
  have hQf : Qf ≤ I ^ k := hQle
  have hIk : I ^ k ≠ 0 := pow_ne_zero _ hI
  suffices h : I ^ k ≤ Qf by
    rw [← coe_pow]; exact h
  by_contra hne
  have hb : Qf * (I ^ k)⁻¹ ≤ 1 := by
    calc Qf * (I ^ k)⁻¹ ≤ I ^ k * (I ^ k)⁻¹ := mul_le_mul' hQf le_rfl
      _ = 1 := mul_inv_cancel₀ hIk
  obtain ⟨B, hB⟩ := le_one_iff_exists_coeIdeal.mp hb
  have hBtop : B ≠ ⊤ := by
    rintro rfl
    apply hne
    have h1 : Qf * (I ^ k)⁻¹ = 1 := by rw [← hB, coeIdeal_top]
    calc I ^ k = Qf * (I ^ k)⁻¹ * I ^ k := by rw [h1, one_mul]
      _ = Qf := by rw [mul_assoc, inv_mul_cancel₀ hIk, mul_one]
      _ ≤ Qf := le_rfl
  obtain ⟨P, hPmax, hBP⟩ := Ideal.exists_le_maximal B hBtop
  have := hPmax.isPrime
  have hstep : ∀ s ∈ S, s ∈ ((P : FractionalIdeal R⁰ K) * I) := by
    intro s hs
    have hsI : spanSingleton R⁰ s ≤ I := by
      rw [spanSingleton_le_iff_mem, ← mem_coe, hIS]; exact Submodule.subset_span hs
    have hc : spanSingleton R⁰ s * I⁻¹ ≤ 1 := by
      calc spanSingleton R⁰ s * I⁻¹ ≤ I * I⁻¹ := mul_le_mul' hsI le_rfl
        _ = 1 := mul_inv_cancel₀ hI
    obtain ⟨C, hC⟩ := le_one_iff_exists_coeIdeal.mp hc
    have hCk : C ^ k ≤ P := by
      rw [← coeIdeal_le_coeIdeal K, coeIdeal_pow, hC, mul_pow, spanSingleton_pow, inv_pow]
      calc spanSingleton R⁰ (s ^ k) * (I ^ k)⁻¹ ≤ Qf * (I ^ k)⁻¹ := by
            refine mul_le_mul' ?_ le_rfl
            rw [spanSingleton_le_iff_mem]
            exact Submodule.subset_span ⟨s, hs, rfl⟩
        _ = B := hB.symm
        _ ≤ P := (coeIdeal_le_coeIdeal K).mpr hBP
    have hCP : C ≤ P := Ideal.IsPrime.le_of_pow_le hCk
    have h2 : spanSingleton R⁰ s * I⁻¹ ≤ P := hC ▸ (coeIdeal_le_coeIdeal K).mpr hCP
    have h3 : spanSingleton R⁰ s ≤ (P : FractionalIdeal R⁰ K) * I := by
      calc spanSingleton R⁰ s = spanSingleton R⁰ s * I⁻¹ * I := by
            rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
        _ ≤ P * I := mul_le_mul' h2 le_rfl
    exact spanSingleton_le_iff_mem.mp h3
  have hIP : I ≤ (P : FractionalIdeal R⁰ K) * I := by
    rw [← coe_le_coe, hIS, Submodule.span_le]
    intro s hs
    exact mem_coe.mpr (hstep s hs)
  have h1P : (1 : FractionalIdeal R⁰ K) ≤ P := by
    calc (1 : FractionalIdeal R⁰ K) = I * I⁻¹ := (mul_inv_cancel₀ hI).symm
      _ ≤ P * I * I⁻¹ := mul_le_mul' hIP le_rfl
      _ = P := by rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
  rw [← coeIdeal_top, coeIdeal_le_coeIdeal] at h1P
  exact hPmax.ne_top (top_le_iff.mp h1P)

variable (D : Car)

/- English proof (translation)
Use `le_antisymm (cS_span_le D S) ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Rewrite using `[SetLike.mem_coe, CU.mem_cS, CU.conj_conj]`. Conclude with `Submodule.subset_span hs`.
-/
theorem cS_span (S : Set D.host.E) :
    CU.cS D (Submodule.span (𝓞 D.host.E) S) = Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
  refine le_antisymm (cS_span_le D S) ?_
  rw [Submodule.span_le]
  rintro _ ⟨s, hs, rfl⟩
  rw [SetLike.mem_coe, CU.mem_cS, CU.conj_conj]
  exact Submodule.subset_span hs

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Matrix nonZeroDivisors FractionalIdeal
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

/- English proof (translation)
Set `_` to `D.host.cmStar`. Introduce `N L hL`. Take `⟨m, hm0, hup, hlow⟩` from `FL.sd_bounds D L hL`. Use `set G : Set D.host.E := {x | ∃ U : Matrix (Fin N) (Fin N) D.host.E, (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det} with hG`. Establish `hvol : vol D L = Submodule.span (𝓞 D.host.E) G` using `rfl`.

Establish `hmE : (m : D.host.E) ≠ 0` using `Int.cast_ne_zero.mpr hm0`. Use `set c : D.host.E := ((m : D.host.E) ^ N)⁻¹ with hc`. Establish `hcc : D.host.conj c = c` using `by simp [hc, map_inv₀, map_pow, map_intCast]`. Establish `hmN : (m : D.host.E) ^ N ∈ G`. Use `⟨Matrix.diagonal (fun _ => (m : D.host.E)), fun j => ?_, by simp [det_diagonal]⟩` and prove the remaining obligations.

Establish `h1` using `hlow (Pi.single j 1) (fun i => by`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero)` using `[Pi.single_apply, h]`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Establish `hGle : vol D L ≤ Submodule.span (𝓞 D.host.E) {c}`. Rewrite using `[hvol, Submodule.span_le]`. Introduce and unpack `_ ⟨U, hU, rfl⟩`. Establish `hint : ∀ i j, IsIntegral ℤ ((m : D.host.E) * U i j)` using `fun i j => hup _ (hU j) i`.

Set `M' : Matrix (Fin N) (Fin N) (𝓞 D.host.E)` to `Matrix.of fun i j => ⟨_, hint i j⟩`. Establish `e : M'.map (algebraMap (𝓞 D.host.E) D.host.E) = (m : D.host.E) • U`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton]`.

Use `⟨M'.det, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, RingHom.map_det]`. Express the relevant statement in the definitionally equal form `(M'.map (algebraMap _ _)).det * c = U.det`. Rewrite using `[e, det_smul, Fintype.card_fin, hc, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hmE), one_mul]`. Establish `hMle : CU.cS D (vol D L) ≤ Submodule.span (𝓞 D.host.E) {c}`.

Introduce `x hx`. Rewrite `hx` using `[CU.mem_cS]`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.mp (hGle hx)`. Use `Submodule.mem_span_singleton.mpr ⟨CU.conjO D a, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg D.host.conj ha`.

Rewrite `h2` using `[CU.conj_smul, hcc, CU.conj_conj]`. Then use the resulting hypothesis. Set `Lf : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E` to `⟨vol D L, isFractional_of_le (J := spanSingleton _ c) (by rw [coe_spanSingleton]; exact hGle)⟩`. Set `Mf : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E` to `⟨CU.cS D (vol D L), isFractional_of_le (J := spanSingleton _ c) (by rw [coe_spanSingleton]; exact hMle)⟩`. Establish `hmL : (m : D.host.E) ^ N ∈ vol D L` using `Submodule.subset_span hmN`. Establish `hmM : (m : D.host.E) ^ N ∈ CU.cS D (vol D L)`.

Rewrite using `[CU.mem_cS, map_pow, map_intCast]`. Conclude with `hmL`. Establish `hMf0 : Mf ≠ 0`. Introduce `h`. Establish `h1 : (m : D.host.E) ^ N ∈ (Mf : Submodule (𝓞 D.host.E) D.host.E)` using `hmM`.

Rewrite `h1` using `[h, coe_zero, Submodule.mem_bot]`. Conclude with `pow_ne_zero _ hmE h1`. Establish `hMS : (Mf : Submodule (𝓞 D.host.E) D.host.E) = Submodule.span _ (D.host.conj '' G)` using `cS_span D G`. Establish `key : (Mf : Submodule (𝓞 D.host.E) D.host.E) ^ (N - 1) * ((Mf⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ N ≤ vol D L`. Use `(mul_le_mul' (spanPow Mf hMf0 _ hMS (N - 1)) le_rfl).trans ?_` and prove the remaining obligations.

Establish `hp : ((Mf⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ N = ∏ _i : Fin N, Submodule.span (𝓞 D.host.E) (((Mf⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) : Set D.host.E)`. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, Submodule.span_eq]`. Rewrite using `[hp, Submodule.prod_span, Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨_, ⟨_, ⟨U, hU, rfl⟩, rfl⟩, rfl⟩, b, hb, rfl⟩`. Take `⟨g, hg, rfl⟩` from `(Set.mem_fintype_prod _ _).mp hb`.

Use `adj_step D L hL U hU g fun i y hy => ?_` and prove the remaining obligations. Establish `h1` using `(mem_inv_iff hMf0).mp (hg i) y hy`. Rewrite `h1` using `[← mem_coe, coe_one]`. Then use the resulting hypothesis. Establish `key' : Mf ^ (N - 1) * Mf⁻¹ ^ N ≤ Lf`. Rewrite using `[← coe_le_coe, coe_mul, coe_pow, coe_pow]`.

Conclude with `key`. Establish `hfin : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ Lf * Mf`. Break down `N with _ | n` into its components or cases. Establish `h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ Lf`. Simplify using `using key'`.

Establish `h2 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ Mf`. Rewrite using `[FractionalIdeal.one_le, ← mem_coe]`. Establish `h5 : (1 : D.host.E) ∈ CU.cS D (vol D L)` using `by simpa using hmM`. Conclude with `h5`. Combine the equalities or inequalities in the displayed calculation.

Establish `h3 : Mf ^ (n + 1 - 1) * Mf⁻¹ ^ (n + 1) = Mf⁻¹`. Rewrite using `[Nat.add_sub_cancel, inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hMf0), one_mul]`. Rewrite `key'` using `[h3]`. Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `coe_le_coe.mpr hfin`.

Rewrite `h4` using `[coe_one, coe_mul]`. Conclude with `h4`.
-/
theorem unitDisc : UnitDisc D := by
  let _ := D.host.cmStar
  intro N L hL
  obtain ⟨m, hm0, hup, hlow⟩ := FL.sd_bounds D L hL
  set G : Set D.host.E := {x | ∃ U : Matrix (Fin N) (Fin N) D.host.E,
    (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det} with hG
  have hvol : vol D L = Submodule.span (𝓞 D.host.E) G := rfl
  have hmE : (m : D.host.E) ≠ 0 := Int.cast_ne_zero.mpr hm0
  set c : D.host.E := ((m : D.host.E) ^ N)⁻¹ with hc
  have hcc : D.host.conj c = c := by simp [hc, map_inv₀, map_pow, map_intCast]
  have hmN : (m : D.host.E) ^ N ∈ G := by
    refine ⟨Matrix.diagonal (fun _ => (m : D.host.E)), fun j => ?_, by simp [det_diagonal]⟩
    have h1 := hlow (Pi.single j 1) (fun i => by
      by_cases h : i = j
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_apply, h] using isIntegral_zero)
    convert h1 using 1
    funext i
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hGle : vol D L ≤ Submodule.span (𝓞 D.host.E) {c} := by
    rw [hvol, Submodule.span_le]
    rintro _ ⟨U, hU, rfl⟩
    have hint : ∀ i j, IsIntegral ℤ ((m : D.host.E) * U i j) := fun i j => hup _ (hU j) i
    let M' : Matrix (Fin N) (Fin N) (𝓞 D.host.E) := Matrix.of fun i j => ⟨_, hint i j⟩
    have e : M'.map (algebraMap (𝓞 D.host.E) D.host.E) = (m : D.host.E) • U := by
      ext i j; rfl
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨M'.det, ?_⟩
    rw [Algebra.smul_def, RingHom.map_det]
    change (M'.map (algebraMap _ _)).det * c = U.det
    rw [e, det_smul, Fintype.card_fin, hc, mul_comm, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hmE), one_mul]
  have hMle : CU.cS D (vol D L) ≤ Submodule.span (𝓞 D.host.E) {c} := by
    intro x hx
    rw [CU.mem_cS] at hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hGle hx)
    refine Submodule.mem_span_singleton.mpr ⟨CU.conjO D a, ?_⟩
    have h2 := congrArg D.host.conj ha
    rwa [CU.conj_smul, hcc, CU.conj_conj] at h2
  let Lf : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
    ⟨vol D L, isFractional_of_le (J := spanSingleton _ c) (by rw [coe_spanSingleton]; exact hGle)⟩
  let Mf : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
    ⟨CU.cS D (vol D L), isFractional_of_le (J := spanSingleton _ c)
      (by rw [coe_spanSingleton]; exact hMle)⟩
  have hmL : (m : D.host.E) ^ N ∈ vol D L := Submodule.subset_span hmN
  have hmM : (m : D.host.E) ^ N ∈ CU.cS D (vol D L) := by
    rw [CU.mem_cS, map_pow, map_intCast]; exact hmL
  have hMf0 : Mf ≠ 0 := by
    intro h
    have h1 : (m : D.host.E) ^ N ∈ (Mf : Submodule (𝓞 D.host.E) D.host.E) := hmM
    rw [h, coe_zero, Submodule.mem_bot] at h1
    exact pow_ne_zero _ hmE h1
  have hMS : (Mf : Submodule (𝓞 D.host.E) D.host.E) = Submodule.span _ (D.host.conj '' G) :=
    cS_span D G
  have key : (Mf : Submodule (𝓞 D.host.E) D.host.E) ^ (N - 1) *
      ((Mf⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ N ≤
        vol D L := by
    refine (mul_le_mul' (spanPow Mf hMf0 _ hMS (N - 1)) le_rfl).trans ?_
    have hp : ((Mf⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ N =
        ∏ _i : Fin N, Submodule.span (𝓞 D.host.E)
          (((Mf⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) :
            Set D.host.E) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Submodule.span_eq]
    rw [hp, Submodule.prod_span, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨_, ⟨_, ⟨U, hU, rfl⟩, rfl⟩, rfl⟩, b, hb, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ _).mp hb
    refine adj_step D L hL U hU g fun i y hy => ?_
    have h1 := (mem_inv_iff hMf0).mp (hg i) y hy
    rwa [← mem_coe, coe_one] at h1
  have key' : Mf ^ (N - 1) * Mf⁻¹ ^ N ≤ Lf := by
    rw [← coe_le_coe, coe_mul, coe_pow, coe_pow]; exact key
  have hfin : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ Lf * Mf := by
    rcases N with _ | n
    · have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ Lf := by
        simpa using key'
      have h2 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ Mf := by
        rw [FractionalIdeal.one_le, ← mem_coe]
        have h5 : (1 : D.host.E) ∈ CU.cS D (vol D L) := by simpa using hmM
        exact h5
      calc (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 1 * 1 := (one_mul 1).symm
        _ ≤ Lf * Mf := mul_le_mul' h1 h2
    · have h3 : Mf ^ (n + 1 - 1) * Mf⁻¹ ^ (n + 1) = Mf⁻¹ := by
        rw [Nat.add_sub_cancel, inv_pow, pow_succ, mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hMf0), one_mul]
      rw [h3] at key'
      calc (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = Mf⁻¹ * Mf := (inv_mul_cancel₀ hMf0).symm
        _ ≤ Lf * Mf := mul_le_mul' key' le_rfl
  have h4 := coe_le_coe.mpr hfin
  rw [coe_one, coe_mul] at h4
  exact h4

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.DN

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

/- English proof (translation)
The claim follows from `DN.determinant_norm_one_of_unit_disc D (DN.unitDisc D)`.
-/
theorem relative_determinant_norm_one (D : Car) : DetIdealsKernelNormOne D :=
  DN.determinant_norm_one_of_unit_disc D (DN.unitDisc D)

/- English proof (translation)
The claim follows from `chi_unit_of_det_norm_one D (relative_determinant_norm_one D) χ hχ`.
-/
theorem character_unit_on_determinant (D : Car) (χ : IdE D → ℂ) (hχ : IsChi D χ) : ChiUnitDet D χ :=
  chi_unit_of_det_norm_one D (relative_determinant_norm_one D) χ hχ

/- English proof (translation)
The claim follows from `theta_norm_indep_of_det_norm_one hI relative_determinant_norm_one`.
-/
theorem LinkThIndep_of_IopIso
    (hI : ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ)) :
    LinkThIndep :=
  theta_norm_indep_of_det_norm_one hI relative_determinant_norm_one

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
