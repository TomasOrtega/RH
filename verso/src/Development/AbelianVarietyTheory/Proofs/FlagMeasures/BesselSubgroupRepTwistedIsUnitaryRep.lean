import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PiUnitary

open Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

/- English proof (translation)
Unfold `ellA`. Distinguish the cases in `ha : a.val + 1 < r`. Rewrite using `[dif_pos ha, dif_pos ha, dif_pos ha]`. Conclude with `mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by simp only [eI]; omega) (by simp only [eI]; omega) (by simp only [eI]; omega)`. Rewrite using `[dif_neg ha, dif_neg ha, dif_neg ha]`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Distinguish the cases in `hzj : z j = 0`.

Rewrite using `[hzj, mul_zero, mul_zero, mul_zero, add_zero]`. Establish `hjW : r ≤ j.val ∧ j.val ≤ r + k`. Assume the negation of the conclusion as `hc`. Apply `hzj` to reduce the goal to its premises. Apply `hz` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers. Rewrite using `[mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by omega) (by simp only [eI]; omega) (by simp only [eI]; omega), add_mul]`.
-/
theorem ellA_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) {g h : Mat k r}
    (hg : col k r g) (hh : col k r h) (a : Fin r) :
    ellA k r z (g * h) a = ellA k r z g a + ellA k r z h a := by
  unfold ellA
  by_cases ha : a.val + 1 < r
  · rw [dif_pos ha, dif_pos ha, dif_pos ha]
    exact mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by simp only [eI]; omega)
      (by simp only [eI]; omega) (by simp only [eI]; omega)
  · rw [dif_neg ha, dif_neg ha, dif_neg ha]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hzj : z j = 0
    · rw [hzj, mul_zero, mul_zero, mul_zero, add_zero]
    · have hjW : r ≤ j.val ∧ j.val ≤ r + k := by
        by_contra hc
        apply hzj
        apply hz
        omega
      rw [mul_apply_add hg hh _ _ (by simp only [eI]; omega) (by omega)
        (by simp only [eI]; omega) (by simp only [eI]; omega), add_mul]

/- English proof (translation)
Establish `hs : (∑ a, c a * ellA k r z (g * h) a) = (∑ a, c a * ellA k r z g a) + ∑ a, c a * ellA k r z h a`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[ellA_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2 a, mul_add]`.

Unfold `psiGen`. Rewrite using `[hs, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]`.
-/
theorem psiGen_mul_N (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hz : inWb k r z) {g h : Mat k r}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    psiGen k r z c (g * h) = psiGen k r z c g * psiGen k r z c h := by
  have hs : (∑ a, c a * ellA k r z (g * h) a) =
      (∑ a, c a * ellA k r z g a) + ∑ a, c a * ellA k r z h a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [ellA_mul z hz ((nset_iff g).1 hg).2 ((nset_iff h).1 hh).2 a, mul_add]
  unfold psiGen
  rw [hs, Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

/- English proof (translation)
Unfold `psiGen`. Rewrite using `[mul_comm Complex.I]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat k r) :
    ‖psiGen k r z c g‖ = 1 := by
  unfold psiGen
  rw [mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _

/- English proof (translation)
Unfold `ellA`. Establish `hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0` using `fun p => hh.2 _ p (by simp only [eI]; omega)`. Distinguish the cases in `ha : a.val + 1 < r`. Rewrite using `[dif_pos ha, dif_pos ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)), mul_apply_of_row _ _ _ hrow]`. Rewrite using `[dif_neg ha, dif_neg ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec, mulVec_apply_of_row _ _ hrow]`.
-/
theorem ellA_block (z : Fin (2 * r + k + 1) → ℂ) {h h' g : Mat k r}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) (a : Fin r) :
    ellA k r z (h * g * h') a = ellA k r z g a := by
  unfold ellA
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 _ p (by simp only [eI]; omega)
  by_cases ha : a.val + 1 < r
  · rw [dif_pos ha, dif_pos ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)),
      mul_apply_of_row _ _ _ hrow]
  · rw [dif_neg ha, dif_neg ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec,
      mulVec_apply_of_row _ _ hrow]

/- English proof (translation)
Simplify using `only [psiGen, ellA_block z hh hh' hz]`.
-/
theorem psiGen_block (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {h h' g : Mat k r}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    psiGen k r z c (h * g * h') = psiGen k r z c g := by
  simp only [psiGen, ellA_block z hh hh' hz]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ => Matrix.one_apply, fun _ _ _ => Matrix.one_apply⟩`.
-/
theorem block_one : block k r (1 : Mat k r) :=
  ⟨fun _ _ _ => Matrix.one_apply, fun _ _ _ => Matrix.one_apply⟩

/- English proof (translation)
Use `psiGen_block (g := g) z c (uw_block hh) block_one (Matrix.one_mulVec z)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one]`. Then use the resulting hypothesis.
-/
theorem psiGen_uw_mul (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {h g : Mat k r}
    (hh : h ∈ UWset k r z) : psiGen k r z c (h * g) = psiGen k r z c g := by
  have := psiGen_block (g := g) z c (uw_block hh) block_one (Matrix.one_mulVec z)
  rwa [Matrix.mul_one] at this

/- English proof (translation)
Distinguish the cases in `h : a.val + 1 < r`. Establish `e : (fun g : Mat k r => ellA k r z g a) = fun g => g (eI k r a) (eI k r ⟨a.val + 1, h⟩)`. Use function extensionality and compare the values at `g`. Unfold `ellA`. Rewrite using `[dif_pos h]`.

Rewrite using `[e]`. Conclude with `(continuous_apply _).comp (continuous_apply _)`. Establish `e : (fun g : Mat k r => ellA k r z g a) = fun g => (g *ᵥ z) (eI k r a)`. Use function extensionality and compare the values at `g`. Unfold `ellA`.

Rewrite using `[dif_neg h]`. Rewrite using `[e]`. Conclude with `(continuous_apply (eI k r a)).comp (continuous_id.matrix_mulVec continuous_const : Continuous fun g : Mat k r => g *ᵥ z)`.
-/
theorem ellA_continuous (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Continuous (fun g : Mat k r => ellA k r z g a) := by
  by_cases h : a.val + 1 < r
  · have e : (fun g : Mat k r => ellA k r z g a) =
        fun g => g (eI k r a) (eI k r ⟨a.val + 1, h⟩) := by
      funext g; unfold ellA; rw [dif_pos h]
    rw [e]
    exact (continuous_apply _).comp (continuous_apply _)
  · have e : (fun g : Mat k r => ellA k r z g a) = fun g => (g *ᵥ z) (eI k r a) := by
      funext g; unfold ellA; rw [dif_neg h]
    rw [e]
    exact (continuous_apply (eI k r a)).comp
      (continuous_id.matrix_mulVec continuous_const : Continuous fun g : Mat k r => g *ᵥ z)

/- English proof (translation)
Unfold `psiGen`. Conclude with `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (ellA_continuous z a)))))`.
-/
theorem psiGen_continuous (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (psiGen k r z c) := by
  unfold psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ =>
      continuous_const.mul (ellA_continuous z a)))))

/- English proof (translation)
Distinguish the cases in `hj : j.val < r ∨ r + k < j.val`. Conclude with `hh.1 i j hj`. Conclude with `hh.2 i j (by omega)`.
-/
theorem block_entry {h : Mat k r} (hh : block k r h) {i j : Fin (2 * r + k + 1)}
    (H : ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k))) :
    h i j = if i = j then 1 else 0 := by
  by_cases hj : j.val < r ∨ r + k < j.val
  · exact hh.1 i j hj
  · exact hh.2 i j (by omega)

/- English proof (translation)
Establish `hb` using `uw_block hh`. Establish `hc` using `((nset_iff m).1 hm).2`. Use extensionality with `i j`. Unfold `hPart`. Distinguish the cases in `H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)`.

Rewrite using `[if_pos H1]`. Conclude with `block_mul_col hb hc i j H1.2.2 (Or.inr H1.1.1)`. Apply the tactic sequence `rw [if_neg H1, block_entry hb H1]`.
-/
theorem hPart_mul {z : Fin (2 * r + k + 1) → ℂ} {h m : Mat k r} (hh : h ∈ UWset k r z)
    (hm : m ∈ Nset k r) : hPart k r (h * m) = h := by
  have hb := uw_block hh
  have hc := ((nset_iff m).1 hm).2
  ext i j
  unfold hPart
  by_cases H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · rw [if_pos H1]
    exact block_mul_col hb hc i j H1.2.2 (Or.inr H1.1.1)
  · rw [if_neg H1, block_entry hb H1]

/- English proof (translation)
Unfold `PiS`. Rewrite using `[hPart_mul hh hm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hh.1), Matrix.one_mul]`.
-/
theorem PiS_mul {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (ψ : Mat k r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) {z : Fin (2 * r + k + 1) → ℂ} {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) : PiS ψ π (h * m) = ψ m • π h := by
  unfold PiS
  rw [hPart_mul hh hm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hh.1), Matrix.one_mul]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `show Continuous fun s : Mat k r => hPart k r s i j`. Distinguish the cases in `H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)`. Simplify using `only [hPart, if_pos H1]`. Conclude with `(continuous_apply j).comp (continuous_apply i)`.

Simplify using `only [hPart, if_neg H1]`. Conclude with `continuous_const`.
-/
theorem hPart_continuous : Continuous (hPart k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun s : Mat k r => hPart k r s i j
  by_cases H1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · simp only [hPart, if_pos H1]
    exact (continuous_apply j).comp (continuous_apply i)
  · simp only [hPart, if_neg H1]
    exact continuous_const

/- English proof (translation)
Establish `h1 : (ContinuousLinearMap.adjoint A).comp A = 1` using `(A.norm_map_iff_adjoint_comp_self).1 hA`. Use extensionality with `v`. Establish `e1` using `congrArg (fun T : E →L[ℂ] E => T (B v)) h1`. Establish `e2` using `congrArg (fun T : E →L[ℂ] E => T v) hAB`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at e1 e2`.

Rewrite `e1` using `[e2]`. Conclude with `e1`.
-/
theorem adjoint_eq_of_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A B : E →L[ℂ] E) (hA : ∀ v, ‖A v‖ = ‖v‖) (hAB : A.comp B = 1) :
    ContinuousLinearMap.adjoint A = B := by
  have h1 : (ContinuousLinearMap.adjoint A).comp A = 1 := (A.norm_map_iff_adjoint_comp_self).1 hA
  ext v
  have e1 := congrArg (fun T : E →L[ℂ] E => T (B v)) h1
  have e2 := congrArg (fun T : E →L[ℂ] E => T v) hAB
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at e1 e2
  rw [e2] at e1
  exact e1

end GlobalTheory.SgInf.PiUnitary

namespace GlobalTheory.SgInf.PiUnitary

open Formalism.QuantumDeterminants.WeylGroupFacts

/- English proof (translation)
Introduce `k r Wp _ _ _ _ z c π hz _ hπ`. Establish `hchar : ∀ m ∈ Nset k r, ‖(psiGen k r z c) m‖ = 1 ∧ ∀ m' ∈ Nset k r, (psiGen k r z c) (m * m') = (psiGen k r z c) m * (psiGen k r z c) m'` using `fun m hm => ⟨norm_psiGen z c m, fun m' hm' => psiGen_mul_N z c hz hm hm'⟩`. Establish `hpsi1 : (psiGen k r z c) 1 = 1`. Establish `e` using `psiGen_mul_N z c hz (mem_n_one (k := k) (r := r)) (mem_n_one (k := k) (r := r))`. Rewrite `e` using `[Matrix.one_mul]`.

Establish `hne : (psiGen k r z c) 1 ≠ 0`. Introduce `h0`. Use `norm_psiGen (k := k) (r := r) z c 1` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`.

Establish `e' : (psiGen k r z c) 1 * 1 = (psiGen k r z c) 1 * (psiGen k r z c) 1` using `by rw [mul_one]; exact e`. Conclude with `(mul_left_cancel₀ hne e').symm`. Establish `hrep : IsURepOn (Sset k r z) (PiS (psiGen k r z c) π)`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[PiS_one, hpsi1, one_smul]`.

Conclude with `hπ.1.1`. Introduce and unpack `_ ⟨h, hh, m, hm, rfl⟩ _ ⟨h', hh', m', hm', rfl⟩`. Establish `hu'` using `isUnit_of_uh hh'.1`. Establish `hn : h'⁻¹ * m * h' ∈ Nset k r`. Use `(uWNormal k r z hz h'⁻¹ (uw_inv hh') m hm).1` as an intermediate fact.

Rewrite `this` using `[Matrix.nonsing_inv_nonsing_inv _ hu']`. Then use the resulting hypothesis. Establish `e : h * m * (h' * m') = (h * h') * ((h'⁻¹ * m * h') * m')`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc h' h'⁻¹, Matrix.mul_nonsing_inv _ hu', Matrix.one_mul]`. Rewrite using `[e, PiS_mul (psiGen k r z c) π (uw_mul hh hh') (mem_n_mul hn hm'), PiS_mul (psiGen k r z c) π hh hm, PiS_mul (psiGen k r z c) π hh' hm', psiGen_mul_N z c hz hn hm', psiGen_block z c (uw_block (uw_inv hh')) (uw_block hh') hh'.2.2, hπ.1.2 h hh h' hh', ContinuousLinearMap.smul_comp, …`.

Introduce and unpack `_ ⟨h, hh, m, hm, rfl⟩ v`. Rewrite using `[PiS_mul (psiGen k r z c) π hh hm, ContinuousLinearMap.smul_apply, norm_smul, norm_psiGen, one_mul, hπ.2.1 h hh v]`. Introduce `v`. Establish `hmaps : Set.MapsTo (hPart k r) (Sset k r z) (UWset k r z)`. Introduce and unpack `_ ⟨h, hh, m, hm, rfl⟩`.

Rewrite using `[hPart_mul hh hm]`. Conclude with `hh`. Establish `hc : ContinuousOn (fun s => (psiGen k r z c) s • π (hPart k r s) v) (Sset k r z)` using `(psiGen_continuous z c).continuousOn.smul ((hπ.2.2 v).comp hPart_continuous.continuousOn hmaps)`. Use `hc.congr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, hh, m, hm, rfl⟩`.

Use `show PiS (psiGen k r z c) π (h * m) v = (psiGen k r z c) (h * m) • π (hPart k r (h * m)) v`. Rewrite using `[PiS_mul (psiGen k r z c) π hh hm, hPart_mul hh hm, psiGen_uw_mul z c hh, ContinuousLinearMap.smul_apply]`. Establish `hiso : ∀ s ∈ Sset k r z, ∀ v, ‖PiS (psiGen k r z c) π s v‖ = ‖v‖` using `hrep.2.1`. Use `⟨fun h hh m hm => ⟨hPart_mul hh hm, PiS_mul (psiGen k r z c) π hh hm⟩, hrep, fun s hs => ⟨?_, ?_⟩, ?_, hchar⟩` and prove the remaining obligations. Conclude with `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hiso s hs v, one_mul]`.

Apply the tactic sequence `apply adjoint_eq_of_isometry _ _ (hiso s hs)`. Establish `hsU : s ∈ UH (Hpk k r)`. Take `⟨h, hh, m, hm, rfl⟩` from `hs`. Conclude with `uh_mul hh.1 hm.1`. Establish `hsi : s⁻¹ ∈ Sset k r z` using `(sGroup k r z hz).2.2 s hs`.

Rewrite using `[← hrep.1.2 s hs s⁻¹ hsi, Matrix.mul_nonsing_inv _ (isUnit_of_uh hsU)]`. Conclude with `hrep.1.1`. Conclude with `continuousOn_clm_apply.2 hrep.2.2`.
-/
theorem piS_unitary : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → IsURepOn (UWset k r z) π →
    (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, hPart k r (h * m) = h ∧
        PiS (psiGen k r z c) π (h * m) = psiGen k r z c m • π h) ∧
      IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) ∧
      (∀ s ∈ Sset k r z, ‖PiS (psiGen k r z c) π s‖ ≤ 1 ∧
        ContinuousLinearMap.adjoint (PiS (psiGen k r z c) π s) = PiS (psiGen k r z c) π s⁻¹) ∧
      ContinuousOn (PiS (psiGen k r z c) π) (Sset k r z) ∧
      (∀ m ∈ Nset k r, ‖psiGen k r z c m‖ = 1 ∧
        ∀ m' ∈ Nset k r, psiGen k r z c (m * m') = psiGen k r z c m * psiGen k r z c m') := by
  intro k r Wp _ _ _ _ z c π hz _ hπ
  have hchar : ∀ m ∈ Nset k r, ‖(psiGen k r z c) m‖ = 1 ∧ ∀ m' ∈ Nset k r, (psiGen k r z c) (m * m') = (psiGen k r z c) m * (psiGen k r z c) m' :=
    fun m hm => ⟨norm_psiGen z c m, fun m' hm' => psiGen_mul_N z c hz hm hm'⟩
  have hpsi1 : (psiGen k r z c) 1 = 1 := by
    have e := psiGen_mul_N z c hz (mem_n_one (k := k) (r := r)) (mem_n_one (k := k) (r := r))
    rw [Matrix.one_mul] at e
    have hne : (psiGen k r z c) 1 ≠ 0 := by
      intro h0
      have := norm_psiGen (k := k) (r := r) z c 1
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have e' : (psiGen k r z c) 1 * 1 = (psiGen k r z c) 1 * (psiGen k r z c) 1 := by rw [mul_one]; exact e
    exact (mul_left_cancel₀ hne e').symm
  have hrep : IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [PiS_one, hpsi1, one_smul]
      exact hπ.1.1
    · rintro _ ⟨h, hh, m, hm, rfl⟩ _ ⟨h', hh', m', hm', rfl⟩
      have hu' := isUnit_of_uh hh'.1
      have hn : h'⁻¹ * m * h' ∈ Nset k r := by
        have := (uWNormal k r z hz h'⁻¹ (uw_inv hh') m hm).1
        rwa [Matrix.nonsing_inv_nonsing_inv _ hu'] at this
      have e : h * m * (h' * m') = (h * h') * ((h'⁻¹ * m * h') * m') := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc h' h'⁻¹, Matrix.mul_nonsing_inv _ hu', Matrix.one_mul]
      rw [e, PiS_mul (psiGen k r z c) π (uw_mul hh hh') (mem_n_mul hn hm'), PiS_mul (psiGen k r z c) π hh hm, PiS_mul (psiGen k r z c) π hh' hm',
        psiGen_mul_N z c hz hn hm',
        psiGen_block z c (uw_block (uw_inv hh')) (uw_block hh') hh'.2.2, hπ.1.2 h hh h' hh',
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
    · rintro _ ⟨h, hh, m, hm, rfl⟩ v
      rw [PiS_mul (psiGen k r z c) π hh hm, ContinuousLinearMap.smul_apply, norm_smul, norm_psiGen, one_mul,
        hπ.2.1 h hh v]
    · intro v
      have hmaps : Set.MapsTo (hPart k r) (Sset k r z) (UWset k r z) := by
        rintro _ ⟨h, hh, m, hm, rfl⟩
        rw [hPart_mul hh hm]
        exact hh
      have hc : ContinuousOn (fun s => (psiGen k r z c) s • π (hPart k r s) v) (Sset k r z) :=
        (psiGen_continuous z c).continuousOn.smul
          ((hπ.2.2 v).comp hPart_continuous.continuousOn hmaps)
      refine hc.congr ?_
      rintro _ ⟨h, hh, m, hm, rfl⟩
      show PiS (psiGen k r z c) π (h * m) v = (psiGen k r z c) (h * m) • π (hPart k r (h * m)) v
      rw [PiS_mul (psiGen k r z c) π hh hm, hPart_mul hh hm, psiGen_uw_mul z c hh, ContinuousLinearMap.smul_apply]
  have hiso : ∀ s ∈ Sset k r z, ∀ v, ‖PiS (psiGen k r z c) π s v‖ = ‖v‖ := hrep.2.1
  refine ⟨fun h hh m hm => ⟨hPart_mul hh hm, PiS_mul (psiGen k r z c) π hh hm⟩, hrep, fun s hs => ⟨?_, ?_⟩, ?_, hchar⟩
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hiso s hs v, one_mul]
  · apply adjoint_eq_of_isometry _ _ (hiso s hs)
    have hsU : s ∈ UH (Hpk k r) := by
      obtain ⟨h, hh, m, hm, rfl⟩ := hs
      exact uh_mul hh.1 hm.1
    have hsi : s⁻¹ ∈ Sset k r z := (sGroup k r z hz).2.2 s hs
    rw [← hrep.1.2 s hs s⁻¹ hsi, Matrix.mul_nonsing_inv _ (isUnit_of_uh hsU)]
    exact hrep.1.1
  · exact continuousOn_clm_apply.2 hrep.2.2

end GlobalTheory.SgInf.PiUnitary

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf in
/- English proof (translation)
The claim follows from `GlobalTheory.SgInf.PiUnitary.piS_unitary`.
-/
example : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → IsURepOn (UWset k r z) π → (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, hPart k r (h * m) = h ∧ PiS (psiGen k r z c) π (h * m) = psiGen k r z c m • π h) ∧ IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) ∧ (∀ s ∈ Sset k r z, ‖PiS (psiGen k r z c) π s‖ ≤ 1 ∧ ContinuousLinearMap.adjoint (PiS (psiGen k r z c) π s) = PiS (psiGen k r z c) π s⁻¹) ∧ ContinuousOn (PiS (psiGen k r z c) π) (Sset k r z) ∧ (∀ m ∈ Nset k r, ‖psiGen k r z c m‖ = 1 ∧ ∀ m' ∈ Nset k r, psiGen k r z c (m * m') = psiGen k r z c m * psiGen k r z c m') := GlobalTheory.SgInf.PiUnitary.piS_unitary
