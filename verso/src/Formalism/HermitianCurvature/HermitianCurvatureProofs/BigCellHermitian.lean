import Formalism.HermitianCurvature.StatementJF
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.TwoByOneBlock

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Rewrite using `[← emb_mulVec_jV (r := r) μ u]`. Use extensionality with `i`. Simplify using `only [mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`.

Establish `hj1 : ¬ j.val < r` using `by omega`. Establish `e : bigCell k r c μ i j = Formalism.FourierDecayAlt.B2.embWb k r μ i j`. Simplify using `only [bigCell, Formalism.FourierDecayAlt.B2.embWb, dif_neg hj1, dif_pos hj.2]`. Distinguish the cases in `hi : r ≤ i.val ∧ i.val ≤ r + k`. Rewrite using `[dif_pos hi, dif_pos ⟨hi, hj⟩]`.

Rewrite using `[dif_neg hi, dif_neg (fun h => hi h.1)]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨rfl, h2⟩`. Conclude with `h2 hj`. Rewrite using `[e]`.

Establish `h0 : jV k r u j = 0` using `by simp only [jV, dif_neg hj]`. Rewrite using `[h0, mul_zero, mul_zero]`.
-/
lemma bigCell_mulVec_jV (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    bigCell k r c μ *ᵥ jV k r u = jV k r (μ *ᵥ u) := by
  rw [← emb_mulVec_jV (r := r) μ u]
  ext i
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hj1 : ¬ j.val < r := by omega
    have e : bigCell k r c μ i j = Formalism.FourierDecayAlt.B2.embWb k r μ i j := by
      simp only [bigCell, Formalism.FourierDecayAlt.B2.embWb, dif_neg hj1, dif_pos hj.2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dif_pos hi, dif_pos ⟨hi, hj⟩]
      · rw [dif_neg hi, dif_neg (fun h => hi h.1)]
        rw [if_neg]
        rintro ⟨rfl, h2⟩
        exact h2 hj
    rw [e]
  · have h0 : jV k r u j = 0 := by simp only [jV, dif_neg hj]
    rw [h0, mul_zero, mul_zero]

/- English proof (translation)
Use `conv_lhs => rw [← jV_wbPart hz', ← jV_wbPart hz]`. Rewrite using `[bigCell_mulVec_jV, herm_jV]`.
-/
lemma herm_bigCell (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  conv_lhs => rw [← jV_wbPart hz', ← jV_wbPart hz]
  rw [bigCell_mulVec_jV, herm_jV]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Take `⟨hc, hζ⟩` from `hq`. Establish `hsec` using `D.sec.2 q.2 hζ`. Establish `hmin` using `big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem`. Use `⟨big_cell_mem_holds k r q.1 _ hc hsec.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl`.

Establish `h` using `hmin.1 ⟨l.val, by omega⟩`. Establish `hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l` using `Fin.ext rfl`. Use `show Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) l ≠ 0`. Rewrite using `[← hl', h]`. Conclude with `Finset.prod_ne_zero_iff.2 fun a _ => hc a`.

Establish `hz` using `hmin.2.2 hc`. Rewrite `hz` using `[herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2]`. Establish `hr` using `hmin.1 (Fin.last r)`. Use `set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP`. Establish `hP0 : P ≠ 0`.

Establish `: P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a` using `hr`. Rewrite using `[this]`. Conclude with `Finset.prod_ne_zero_iff.2 fun a _ => hc a`. Establish `hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P`. Unfold `zeta at hz`.

Rewrite `hz` using `[← hP]`. Establish `h2` using `div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0`. Rewrite `h2` using `[hz]`. Conclude with `h2.symm`. Use `show 0 < Gf k r D.z D.z' (gq D q)`.

Unfold `Gf gq`. Rewrite using `[hlast, ← hP, Complex.normSq_mul]`. Establish `h1 : 0 < Complex.normSq P` using `Complex.normSq_pos.2 hP0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gqDom (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    gq D q ∈ Om k r D.z D.z' := by
  obtain ⟨hc, hζ⟩ := hq
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  refine ⟨big_cell_mem_holds k r q.1 _ hc hsec.1, ?_, ?_⟩
  · intro l hl
    have h := hmin.1 ⟨l.val, by omega⟩
    have hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l := Fin.ext rfl
    show Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) l ≠ 0
    rw [← hl', h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  · have hz := hmin.2.2 hc
    rw [herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    show 0 < Gf k r D.z D.z' (gq D q)
    unfold Gf gq
    rw [hlast, ← hP, Complex.normSq_mul]
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ D _ hq` and use `gqDom D hq`.
-/
theorem _root_.Formalism.FourierDecayAlt.P.big_cell_domain : GqDom := fun _ _ _ _ _ _ _ _ D _ hq => gqDom D hq

end Formalism.FourierDecayAlt.P.BigCellHermitian
