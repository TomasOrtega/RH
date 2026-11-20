import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesDifferByIsometryAndTriangularOfPeriods

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix ComplexConjugate

noncomputable section

namespace GlobalTheory.PeriodBorelQ

open GlobalTheory.FramePeriod GlobalTheory.PeriodBorel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `he : Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ Data.emb τ v`. Use function extensionality and compare the values at `k`. Simplify using `[Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]`. Establish `hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).map τ`. Unfold `natPer`. Use `split_ifs with hn`. Rewrite using `[he, locPer_apply, locPer_apply] split_ifs`. Conclude with `h.hermC_eq τ (col M ⟨n, hn⟩) _`.

Rewrite using `[Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hu]`. Both sides reduce to the same expression.
-/
theorem natPer_move_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a) (τ : E →+* ℂ) (q : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) (n : ℕ) :
    natPer τ X'.Gm q ((a : Matrix (Fin r) (Fin r) E).map τ * M)
      (Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v)) n = natPer τ X.Gm q M (Data.emb τ v) n := by
  have he : Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ Data.emb τ v := by
    funext k; simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).map τ
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · exact h.hermC_eq τ (col M ⟨n, hn⟩) _
    · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
  · rfl

/- English proof (translation)
Establish `he : Data.emb τ ((N : E) • v) = (N : ℂ) • Data.emb τ v`. Use function extensionality and compare the values at `k`. Simplify using `[Data.emb]`. Unfold `natPer`. Use `split_ifs with hn`.

Rewrite using `[he, locPer_apply, locPer_apply] split_ifs`. Rewrite using `[FD.hermC_smul_right, Complex.conj_natCast]`. Rewrite using `[Matrix.mulVec_smul]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem natPer_natCast_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (N : ℕ) (v : Fin r → E) (n : ℕ) :
    natPer τ G q M (Data.emb τ ((N : E) • v)) n = (N : ℂ) * natPer τ G q M (Data.emb τ v) n := by
  have he : Data.emb τ ((N : E) • v) = (N : ℂ) • Data.emb τ v := by
    funext k; simp [Data.emb]
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · rw [FD.hermC_smul_right, Complex.conj_natCast]
    · rw [Matrix.mulVec_smul]; rfl
  · simp

/- English proof (translation)
Introduce `E _ _ _ r X X' N a h hN0 m hm1 hm2 x hx x' hx' A hA hper`. Establish `hN : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN0.ne'`. Establish `hz` using `h.mem_dom hx`. Use `set z := lact a (castFr h.psi x) with hzd`. Establish `hlat : ∀ w ∈ X'.Λ, ∃ v ∈ X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ v = (N : E) • w`.

Introduce `w hw`. Use `⟨_, h.lat' w hw, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hloc` using `fun τ : X'.Ψ => loc_borel X' τ.1 (mat z τ) (mat x' τ) (hz τ).1 (hx' τ).1 (A τ.1) (A (conjEmb τ.1)) (hA _) (hA _) (fun i hi w hw => by`. Take `⟨v, hv, hav⟩` from `hlat w hw`.

Establish `hm` using `hm1 τ.1 (h.mem τ)`. Rewrite `hm` using `[h.p0]`. Use `mul_left_cancel₀ hN ?_` and prove the remaining obligations. Rewrite using `[← natPer_natCast_smul, ← hav, ← perFr_mem X' x' _ τ.1 τ.2, hper τ.1 i (hm ▸ hi) v hv, hm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[perFr_mem X x v τ.1 (h.mem τ), ← natPer_move_q h, h.p0, hav, natPer_natCast_smul, mul_left_comm]`. Use the proof step `rfl)`. Use the proof step `(fun i hi w hw => by`. Take `⟨v, hv, hav⟩` from `hlat w hw`. Establish `hm` using `hm2 _ (conjEmb_not_mem X (h.mem τ))`.

Rewrite `hm` using `[h.p0]`. Use `mul_left_cancel₀ hN ?_` and prove the remaining obligations. Rewrite using `[← natPer_natCast_smul, ← hav, ← perFr_conj X' x' _ τ.1 τ.2 i hi, hper _ i (hm ▸ hi) v hv, hm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[perFr_conj X x v τ.1 (h.mem τ) j (h.p0 ▸ Finset.mem_range.1 hj), ← natPer_move_q h, h.p0, hav, natPer_natCast_smul, mul_left_comm]`.

Use the proof step `rfl)`. Set `b : Frame X'.Ψ r` to `fun τ => ((mat z τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ)`. Establish `hb : b ∈ Bor X'.Ψ r` using `fun τ => by`. Use `⟨?_, (hloc τ).1⟩` and prove the remaining obligations. Use `show ((mat z τ)⁻¹ * mat x' τ).det ≠ 0`.

Rewrite using `[Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Conclude with `mul_ne_zero (inv_ne_zero (hz τ).1) (hx' τ).1`. Establish `hxb : x' = rmul z b`. Use function extensionality and compare the values at `τ`. Conclude with `(Matrix.mul_nonsing_inv_cancel_left (mat z τ) (mat x' τ) (isUnit_iff_ne_zero.2 (hz τ).1)).symm`.

Use `⟨b, hb, hxb, fun hu hu' => ?_⟩` and prove the remaining obligations. Establish `hbd : ∀ τ i, ‖b τ i i‖ = 1`. Introduce `τ i`. Establish `e` using `FrameDegreeData.ratio_rmul X' z hz hb τ i`. Rewrite `e` using `[← hxb, norm_div, norm_div, hu', hu', hzd, h.dmin_eq, h.dmin_eq, hu, hu, div_one, _root_.mul_one]`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e.symm`. Use `⟨hbd, fun τ i hi => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hτ : τ ∈ X.Ψ`. Rewrite `hi` using `[hm1 τ hτ, h.p0]`. Conclude with `((hloc ⟨τ, h.psi ▸ hτ⟩).2 (hbd _)).1 i hi`.

Rewrite `hi` using `[hm2 τ hτ, h.p0]`. Use `((hloc ⟨conjEmb τ, h.psi ▸ conjEmb_mem X hτ⟩).2 (hbd _)).2 i hi` as an intermediate fact. Rewrite `this` using `[conjEmb_conjEmb]`. Then use the resulting hypothesis.
-/
theorem borel_of_periods_q : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (h : QMatch X X' N a), 0 < N → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * Formalism.L2.PjFree.perFr X x v τ j) → ∃ b ∈ Bor X'.Ψ r, x' = rmul (lact a (castFr h.psi x)) b ∧ (IsUnitFr X x → IsUnitFr X' x' → (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ τ, ∀ i < m τ, ‖A τ i i‖ = 1) := by
  intro E _ _ _ r X X' N a h hN0 m hm1 hm2 x hx x' hx' A hA hper
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have hz := h.mem_dom hx
  set z := lact a (castFr h.psi x) with hzd
  have hlat : ∀ w ∈ X'.Λ, ∃ v ∈ X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ v = (N : E) • w := by
    intro w hw
    refine ⟨_, h.lat' w hw, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hloc := fun τ : X'.Ψ => loc_borel X' τ.1 (mat z τ) (mat x' τ) (hz τ).1 (hx' τ).1 (A τ.1) (A (conjEmb τ.1))
    (hA _) (hA _)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm1 τ.1 (h.mem τ)
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_mem X' x' _ τ.1 τ.2, hper τ.1 i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [perFr_mem X x v τ.1 (h.mem τ), ← natPer_move_q h, h.p0, hav, natPer_natCast_smul, mul_left_comm]
      rfl)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm2 _ (conjEmb_not_mem X (h.mem τ))
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_conj X' x' _ τ.1 τ.2 i hi, hper _ i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [perFr_conj X x v τ.1 (h.mem τ) j (h.p0 ▸ Finset.mem_range.1 hj), ← natPer_move_q h, h.p0, hav,
        natPer_natCast_smul, mul_left_comm]
      rfl)
  let b : Frame X'.Ψ r := fun τ => ((mat z τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ)
  have hb : b ∈ Bor X'.Ψ r := fun τ => by
    refine ⟨?_, (hloc τ).1⟩
    show ((mat z τ)⁻¹ * mat x' τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hz τ).1) (hx' τ).1
  have hxb : x' = rmul z b := by
    funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (mat z τ) (mat x' τ) (isUnit_iff_ne_zero.2 (hz τ).1)).symm
  refine ⟨b, hb, hxb, fun hu hu' => ?_⟩
  have hbd : ∀ τ i, ‖b τ i i‖ = 1 := by
    intro τ i
    have e := FrameDegreeData.ratio_rmul X' z hz hb τ i
    rw [← hxb, norm_div, norm_div, hu', hu', hzd, h.dmin_eq, h.dmin_eq, hu, hu, div_one, _root_.mul_one] at e
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e.symm
  refine ⟨hbd, fun τ i hi => ?_⟩
  by_cases hτ : τ ∈ X.Ψ
  · rw [hm1 τ hτ, h.p0] at hi
    exact ((hloc ⟨τ, h.psi ▸ hτ⟩).2 (hbd _)).1 i hi
  · rw [hm2 τ hτ, h.p0] at hi
    have := ((hloc ⟨conjEmb τ, h.psi ▸ conjEmb_mem X hτ⟩).2 (hbd _)).2 i hi
    rwa [conjEmb_conjEmb] at this

end GlobalTheory.PeriodBorelQ
