import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMapStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointInPointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFrameCompatibilityStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind

/- English proof (translation)
Distinguish the cases in `h : (i : ℕ) + 1 ≤ j`. Use `⟨⟨N - j, by have := i.2; omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `[stepCols, h]`. Use linear arithmetic over natural numbers and integers. Use `⟨⟨0, by have := i.2; omega⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[stepCols, h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem stepCols_nonempty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : (stepCols N j i).Nonempty := by
  by_cases h : (i : ℕ) + 1 ≤ j
  · refine ⟨⟨N - j, by have := i.2; omega⟩, ?_⟩
    simp [stepCols, h]
    omega
  · refine ⟨⟨0, by have := i.2; omega⟩, ?_⟩
    simp [stepCols, h]
    omega

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Introduce `h`. Apply `hX` to reduce the goal to its premises. Establish `h1 : (X q : MRing ι) ∈ mCoordIdeal x` using `by show mConeMap x (X q) = 0`. Rewrite using `[mConeMap, aeval_X, h, map_zero, zero_mul]`. Establish `h2` using `hz.2 _ h1`.

Establish `h3 : z q = 0` using `by simpa using h2`. Use `show mConeMap z (X q) = 0`. Rewrite using `[mConeMap, aeval_X, h3, map_zero, zero_mul]`.
-/
theorem coord_ne {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k}
    (hX : (X q : MRing ι) ∉ mCoordIdeal z) : x q ≠ 0 := by
  intro h
  apply hX
  have h1 : (X q : MRing ι) ∈ mCoordIdeal x := by
    show mConeMap x (X q) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h2 := hz.2 _ h1
  have h3 : z q = 0 := by simpa using h2
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h3, map_zero, zero_mul]

/- English proof (translation)
Introduce `a b h` and use `by show valAt x (A a b) z = 0 rw [hA a b h] exact map_zero (regVal x hz)`.
-/
theorem valMat_blockDiag {N j : ℕ} {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {A : Matrix (Fin N) (Fin N) Ω} (hA : IsBlockDiag j A) : IsBlockDiag j (valMat x z A) := fun a b h => by
  show valAt x (A a b) z = 0
  rw [hA a b h]
  exact map_zero (regVal x hz)

/- English proof (translation)
Establish `e : A⁻¹ * C = (A⁻¹ * B) * (B⁻¹ * C)`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hB)]`. Rewrite using `[e]`. Conclude with `regMat_mul hz h₁ h₂`.
-/
theorem reg_chain {N : ℕ} {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {A B C : Matrix (Fin N) (Fin N) Ω} (hB : B.det ≠ 0)
    (h₁ : ∀ a b, RegAt x (mCoordIdeal z) ((A⁻¹ * B) a b)) (h₂ : ∀ a b, RegAt x (mCoordIdeal z) ((B⁻¹ * C) a b)) :
    (∀ a b, RegAt x (mCoordIdeal z) ((A⁻¹ * C) a b)) ∧
      valMat x z (A⁻¹ * C) = valMat x z (A⁻¹ * B) * valMat x z (B⁻¹ * C) := by
  have e : A⁻¹ * C = (A⁻¹ * B) * (B⁻¹ * C) := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hB)]
  rw [e]
  exact regMat_mul hz h₁ h₂

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

/- English proof (translation)
Establish `hi` using `GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le`. Establish `hz : ∀ I', ¬ IsStepRows N j p.2 I' → minorIJ g I' (stepCols N j p.2) = 0` using `fun I' h => (hi.2.1 g I' hg h).resolve_right (stepCols_nonempty M.j_le p.2).ne_empty`. Establish `hv : ∀ I', IsStepRows N j p.2 I' → ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b = if I = I' then 1 else 0`. Introduce `I' hI'`. Establish `h1` using `hF.2.2.1 p k hk I I' hI hI'`.

Establish `h2` using `(reg_sum hb Finset.univ (fun m : ι k => F.u' I ⟨k, m⟩ * F.u ⟨k, m⟩ I') fun m _ => ValRing.regAt_mul (hG.2.1 _ _).2 (hG.2.1 _ _).1).2`. Rewrite `h2` using `[h1]`. Rewrite using `[Finset.sum_congr rfl fun m _ => (reg_mul hb (hG.2.1 _ _).2 (hG.2.1 _ _).1).2.symm, ← h2]`. Use `split_ifs`. Conclude with `map_one (regVal M.x hb)`.

Conclude with `map_zero (regVal M.x hb)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [plk, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm`.

Use `_ = ∑ I', if I = I' then minorIJ g I' (stepCols N j p.2) else 0 := Finset.sum_congr rfl fun I' _ => by`. Distinguish the cases in `h : IsStepRows N j p.2 I'`. Apply the tactic sequence `rw [hv I' h]; split_ifs <;> simp`. Rewrite using `[hz I' h]`. Simplify using the standard rewrite rules.

Use `_ = minorIJ g I (stepCols N j p.2) := by simp`.
-/
theorem minor_of_plk (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal b)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {I : Finset (Fin N)} (hI : IsStepRows N j p.2 I) {g : Matrix (Fin N) (Fin N) ℂ}
    (hg : IsBlockDiag j g) :
    ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * plk M F b p.2 ⟨k, m⟩ g = minorIJ g I (stepCols N j p.2) := by
  have hi := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hz : ∀ I', ¬ IsStepRows N j p.2 I' → minorIJ g I' (stepCols N j p.2) = 0 := fun I' h =>
    (hi.2.1 g I' hg h).resolve_right (stepCols_nonempty M.j_le p.2).ne_empty
  have hv : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b = if I = I' then 1 else 0 := by
    intro I' hI'
    have h1 := hF.2.2.1 p k hk I I' hI hI'
    have h2 := (reg_sum hb Finset.univ (fun m : ι k => F.u' I ⟨k, m⟩ * F.u ⟨k, m⟩ I') fun m _ =>
      ValRing.regAt_mul (hG.2.1 _ _).2 (hG.2.1 _ _).1).2
    rw [h1] at h2
    rw [Finset.sum_congr rfl fun m _ => (reg_mul hb (hG.2.1 _ _).2 (hG.2.1 _ _).1).2.symm, ← h2]
    split_ifs
    · exact map_one (regVal M.x hb)
    · exact map_zero (regVal M.x hb)
  calc ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * plk M F b p.2 ⟨k, m⟩ g
      = ∑ I', (∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b) *
          minorIJ g I' (stepCols N j p.2) := by
        simp only [plk, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = ∑ I', if I = I' then minorIJ g I' (stepCols N j p.2) else 0 := Finset.sum_congr rfl fun I' _ => by
        by_cases h : IsStepRows N j p.2 I'
        · rw [hv I' h]; split_ifs <;> simp
        · rw [hz I' h]; simp
    _ = minorIJ g I (stepCols N j p.2) := by simp

/- English proof (translation)
Distinguish the cases in `hI : IsStepRows N j p.2 I`. Rewrite using `[← minor_of_plk M hb hF hG hk hI hg, ← minor_of_plk M hb hF hG hk hI hg₂, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[h m]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hi` using `GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le`. Establish `hne` using `(stepCols_nonempty M.j_le p.2).ne_empty`. Rewrite using `[(hi.2.1 g I hg hI).resolve_right hne, (hi.2.1 g₂ I hg₂ hI).resolve_right hne, mul_zero]`.
-/
theorem minor_eq_of_plk (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal b)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {g g₂ : Matrix (Fin N) (Fin N) ℂ} (hg : IsBlockDiag j g) (hg₂ : IsBlockDiag j g₂) {μ : ℂ}
    (h : ∀ m : ι k, plk M F b p.2 ⟨k, m⟩ g = μ * plk M F b p.2 ⟨k, m⟩ g₂) (I : Finset (Fin N)) :
    minorIJ g I (stepCols N j p.2) = μ * minorIJ g₂ I (stepCols N j p.2) := by
  by_cases hI : IsStepRows N j p.2 I
  · rw [← minor_of_plk M hb hF hG hk hI hg, ← minor_of_plk M hb hF hG hk hI hg₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h m]; ring
  · have hi := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
    have hne := (stepCols_nonempty M.j_le p.2).ne_empty
    rw [(hi.2.1 g I hg hI).resolve_right hne, (hi.2.1 g₂ I hg₂ hI).resolve_right hne, mul_zero]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv b F₁' F₂' F₁ F₂ H₁ H₂ hb hF₁' hF₂' hF₁ hF₂ hG₁' hG₂' hG₁ hG₂ hH₁ hH₂ hyp p k hk`. Take `⟨k', hk'⟩` from `exists_blk_cover M' hk`. Take `⟨hbv, hpt⟩` from `GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b hb`. Establish `hi` using `GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le`. Establish `dT₁'` using `(hF₁'.1 p.1).2`.

Establish `dP : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F → ((F.T p.1).map Cv.φ).det ≠ 0` using `fun F hF => by`. Establish `e : ((F.T p.1).map Cv.φ).det = Cv.φ (F.T p.1).det` using `(RingHom.map_det Cv.φ (F.T p.1)).symm`. Rewrite using `[e]`. Conclude with `(map_ne_zero Cv.φ).2 (hF.1 p.1).2`. Establish `r₁₁` using `fun a c => Cv.agree b hb F₁' F₁ hF₁' hF₁ hG₁' hG₁ p.1 a c`.

Establish `r₁₂` using `fun a c => Cv.agree b hb F₁' F₂ hF₁' hF₂ hG₁' hG₂ p.1 a c`. Establish `r₂₁` using `fun a c => Cv.agree b hb F₂' F₁ hF₂' hF₁ hG₂' hG₁ p.1 a c`. Establish `r₂₂` using `fun a c => Cv.agree b hb F₂' F₂ hF₂' hF₂ hG₂' hG₂ p.1 a c`. Establish `c₁` using `reg_chain hb (dP F₁ hF₁) (fun a c => (r₁₁ a c).2) (fun a c => (r₂₁ a c).1)`. Establish `c₂` using `reg_chain hb (dP F₁ hF₁) (fun a c => (r₂₁ a c).2) (fun a c => (r₁₁ a c).1)`.

Establish `c₃` using `reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) (fun a c => (r₁₂ a c).2)`. Establish `c₄` using `reg_chain hb dT₁' (fun a c => (r₁₂ a c).1) (fun a c => (r₁₁ a c).2)`. Establish `c₅` using `reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) c₁.1`. Establish `c₆` using `reg_chain hb (dP F₂ hF₂) c₃.1 (fun a c => (r₂₂ a c).1)`. Establish `eid : ∀ A : Matrix (Fin N) (Fin N) M'.Ω, A.map (RingHom.id M'.Ω) = A` using `fun A => by ext; rfl`.

Take `⟨c', hc'0, hc'⟩` from `GlobalTheory.T.frame_change_under_field_map K' ι' Φ' y' Ψ N j M' (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x (RingHom.id _) b F₁' F₂' hb hF₁' hF₂' (fun k => coord_ne hb (hG₁'.1 k)) (fun k => coord_ne hb (hG₂'.1 k)) p k' hk' (fun m I => ⟨(hG₁'.2.1 _ _).1, (hG₂'.2.1 _ _ …`. Simplify using `only [eid, RingHom.id_apply] at hc'`. Take `⟨a, ha0, hA⟩` from `hyp p k' hk'`. Take `⟨S', hS'⟩ : ∃ S', S' = valMat M'.x b ((F₁'.T p.1)⁻¹ * F₂'.T p.1)` from `⟨_, rfl⟩`. Rewrite `hc'` using `[← hS']`.

Establish `bdS' : IsBlockDiag j S'` using `hS' ▸ valMat_blockDiag hb (((hF₁'.1 p.1).1.inv (isUnit_iff_ne_zero.2 dT₁')).mul (hF₂'.1 p.1).1)`. Take `⟨μ, hμd⟩ : ∃ μ, μ = c' * a⁻¹` from `⟨_, rfl⟩`. Establish `hμ : μ ≠ 0` using `hμd ▸ mul_ne_zero hc'0 (inv_ne_zero ha0)`. Establish `e₁ : ∀ m : ι' k', plk M' F₁' b p.2 ⟨k', m⟩ (S' * H₂ p.1) = μ * plk M' F₁' b p.2 ⟨k', m⟩ (H₁ p.1)` using `fun m => by`. Rewrite using `[hA m, hμd, ← mul_assoc, mul_assoc c', inv_mul_cancel₀ ha0, mul_one]`.

Conclude with `hc' (H₂ p.1) (hH₂ p.1) m`. Establish `e₂` using `minor_eq_of_plk M' hb hF₁' hG₁' hk' (bdS'.mul (hH₂ p.1)) (hH₁ p.1) e₁`. Take `⟨S, hS⟩ : ∃ S, S = valMat M'.x b (((F₁.T p.1).map Cv.φ)⁻¹ * (F₂.T p.1).map Cv.φ)` from `⟨_, rfl⟩`. Establish `eT : Cv.trans F₁' F₁ b p.1 * S' = S * Cv.trans F₂' F₂ b p.1`. Rewrite using `[hS', hS]`.

Conclude with `c₅.2.symm.trans c₆.2`. Establish `e₃ : ∀ I, minorIJ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) I (stepCols N j p.2) = μ⁻¹ * minorIJ (S * (Cv.trans F₂' F₂ b p.1 * H₂ p.1)) I (stepCols N j p.2)` using `fun I => by`. Rewrite using `[← Matrix.mul_assoc S, ← eT, Matrix.mul_assoc, hi.1 _ (S' * H₂ p.1), hi.1 _ (H₁ p.1), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun I' _ => ?_` and prove the remaining obligations. Rewrite using `[e₂ I']`.

Clear the denominators using the available nonvanishing facts. Take `⟨c, hc0, hc⟩` from `GlobalTheory.T.frame_change_under_field_map K ι Φ y Ψ N j M (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x Cv.φ b F₁ F₂ hb hF₁ hF₂ (fun k => coord_ne hbv (hG₁.1 k)) (fun k => coord_ne hbv (hG₂.1 k)) p k hk (fun m I => ⟨(hpt _ (hG₁.2.1 _ _).1).1, (hpt _ (hG₂.2.1 _ _).1).1 …`. Rewrite `hc` using `[← hS]`. Establish `bdT₂` using `(GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b F₂' F₂ hb hF₂' hF₂ hG₂' hG₂ p.1).1`. Establish `hval : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ q I, valAt M'.x (Cv.φ (F.u q I)) b = valAt M.x (F.u q I) (b ∘ Cv.v)` using `fun F hG q I => (hpt _ (hG.2.1 q I).1).2`.

Use `⟨μ⁻¹ * c, mul_ne_zero (inv_ne_zero hμ) hc0, fun m => ?_⟩` and prove the remaining obligations. Establish `h3` using `hc (Cv.trans F₂' F₂ b p.1 * H₂ p.1) (bdT₂.mul (hH₂ p.1)) m`. Simplify using `only [hval F₁ hG₁, hval F₂ hG₂] at h3`. Simplify using `only [plk]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun I _ => by rw [e₃ I]; ring`. Use `_ = _ := by rw [h3, mul_assoc]`.
-/
theorem plk_moved_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F₁' F₂' : FrameData ι' Ψ N M'.Ω M'.blk) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (H₁ H₂ : Ψ → Matrix (Fin N) (Fin N) ℂ), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F₁' → M'.IsFrame F₂' → M.IsFrame F₁ → M.IsFrame F₂ → M'.GoodAt F₁' (mCoordIdeal b) → M'.GoodAt F₂' (mCoordIdeal b) → M.GoodAt F₁ (mCoordIdeal (b ∘ Cv.v)) → M.GoodAt F₂ (mCoordIdeal (b ∘ Cv.v)) → (∀ τ, IsBlockDiag j (H₁ τ)) → (∀ τ, IsBlockDiag j (H₂ τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', CovMap.LocImg.plk M' F₁' b p.2 ⟨k', m'⟩ (H₁ p.1) = a * CovMap.LocImg.plk M' F₂' b p.2 ⟨k', m'⟩ (H₂ p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.plk M F₁ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) = a * CovMap.LocImg.plk M F₂ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₂' F₂ b p.1 * H₂ p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv b F₁' F₂' F₁ F₂ H₁ H₂ hb hF₁' hF₂' hF₁ hF₂ hG₁' hG₂' hG₁ hG₂
    hH₁ hH₂ hyp p k hk
  obtain ⟨k', hk'⟩ := exists_blk_cover M' hk
  obtain ⟨hbv, hpt⟩ := GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b hb
  have hi := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have dT₁' := (hF₁'.1 p.1).2
  have dP : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F → ((F.T p.1).map Cv.φ).det ≠ 0 := fun F hF => by
    have e : ((F.T p.1).map Cv.φ).det = Cv.φ (F.T p.1).det := (RingHom.map_det Cv.φ (F.T p.1)).symm
    rw [e]
    exact (map_ne_zero Cv.φ).2 (hF.1 p.1).2
  have r₁₁ := fun a c => Cv.agree b hb F₁' F₁ hF₁' hF₁ hG₁' hG₁ p.1 a c
  have r₁₂ := fun a c => Cv.agree b hb F₁' F₂ hF₁' hF₂ hG₁' hG₂ p.1 a c
  have r₂₁ := fun a c => Cv.agree b hb F₂' F₁ hF₂' hF₁ hG₂' hG₁ p.1 a c
  have r₂₂ := fun a c => Cv.agree b hb F₂' F₂ hF₂' hF₂ hG₂' hG₂ p.1 a c
  have c₁ := reg_chain hb (dP F₁ hF₁) (fun a c => (r₁₁ a c).2) (fun a c => (r₂₁ a c).1)
  have c₂ := reg_chain hb (dP F₁ hF₁) (fun a c => (r₂₁ a c).2) (fun a c => (r₁₁ a c).1)
  have c₃ := reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) (fun a c => (r₁₂ a c).2)
  have c₄ := reg_chain hb dT₁' (fun a c => (r₁₂ a c).1) (fun a c => (r₁₁ a c).2)
  have c₅ := reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) c₁.1
  have c₆ := reg_chain hb (dP F₂ hF₂) c₃.1 (fun a c => (r₂₂ a c).1)

  have eid : ∀ A : Matrix (Fin N) (Fin N) M'.Ω, A.map (RingHom.id M'.Ω) = A := fun A => by ext; rfl
  obtain ⟨c', hc'0, hc'⟩ := GlobalTheory.T.frame_change_under_field_map K' ι' Φ' y' Ψ N j M' (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x
    (RingHom.id _) b F₁' F₂' hb hF₁' hF₂' (fun k => coord_ne hb (hG₁'.1 k)) (fun k => coord_ne hb (hG₂'.1 k)) p k' hk'
    (fun m I => ⟨(hG₁'.2.1 _ _).1, (hG₂'.2.1 _ _).1, (hG₁'.2.1 _ _).2, (hG₂'.2.1 _ _).2⟩)
    (fun a c => by simp only [eid]; exact ⟨c₁.1 a c, c₂.1 a c⟩)
  simp only [eid, RingHom.id_apply] at hc'
  obtain ⟨a, ha0, hA⟩ := hyp p k' hk'
  obtain ⟨S', hS'⟩ : ∃ S', S' = valMat M'.x b ((F₁'.T p.1)⁻¹ * F₂'.T p.1) := ⟨_, rfl⟩
  rw [← hS'] at hc'
  have bdS' : IsBlockDiag j S' := hS' ▸ valMat_blockDiag hb
    (((hF₁'.1 p.1).1.inv (isUnit_iff_ne_zero.2 dT₁')).mul (hF₂'.1 p.1).1)
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = c' * a⁻¹ := ⟨_, rfl⟩
  have hμ : μ ≠ 0 := hμd ▸ mul_ne_zero hc'0 (inv_ne_zero ha0)
  have e₁ : ∀ m : ι' k', plk M' F₁' b p.2 ⟨k', m⟩ (S' * H₂ p.1) = μ * plk M' F₁' b p.2 ⟨k', m⟩ (H₁ p.1) := fun m => by
    rw [hA m, hμd, ← mul_assoc, mul_assoc c', inv_mul_cancel₀ ha0, mul_one]
    exact hc' (H₂ p.1) (hH₂ p.1) m
  have e₂ := minor_eq_of_plk M' hb hF₁' hG₁' hk' (bdS'.mul (hH₂ p.1)) (hH₁ p.1) e₁

  obtain ⟨S, hS⟩ : ∃ S, S = valMat M'.x b (((F₁.T p.1).map Cv.φ)⁻¹ * (F₂.T p.1).map Cv.φ) := ⟨_, rfl⟩
  have eT : Cv.trans F₁' F₁ b p.1 * S' = S * Cv.trans F₂' F₂ b p.1 := by
    rw [hS', hS]
    exact c₅.2.symm.trans c₆.2
  have e₃ : ∀ I, minorIJ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) I (stepCols N j p.2) =
      μ⁻¹ * minorIJ (S * (Cv.trans F₂' F₂ b p.1 * H₂ p.1)) I (stepCols N j p.2) := fun I => by
    rw [← Matrix.mul_assoc S, ← eT, Matrix.mul_assoc, hi.1 _ (S' * H₂ p.1), hi.1 _ (H₁ p.1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [e₂ I']
    field_simp

  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.frame_change_under_field_map K ι Φ y Ψ N j M (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x Cv.φ b F₁ F₂
    hb hF₁ hF₂ (fun k => coord_ne hbv (hG₁.1 k)) (fun k => coord_ne hbv (hG₂.1 k)) p k hk
    (fun m I => ⟨(hpt _ (hG₁.2.1 _ _).1).1, (hpt _ (hG₂.2.1 _ _).1).1, (hpt _ (hG₁.2.1 _ _).2).1,
      (hpt _ (hG₂.2.1 _ _).2).1⟩)
    (fun a c => ⟨c₃.1 a c, c₄.1 a c⟩)
  rw [← hS] at hc
  have bdT₂ := (GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b F₂' F₂ hb hF₂' hF₂ hG₂' hG₂ p.1).1
  have hval : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ q I,
      valAt M'.x (Cv.φ (F.u q I)) b = valAt M.x (F.u q I) (b ∘ Cv.v) := fun F hG q I => (hpt _ (hG.2.1 q I).1).2
  refine ⟨μ⁻¹ * c, mul_ne_zero (inv_ne_zero hμ) hc0, fun m => ?_⟩
  have h3 := hc (Cv.trans F₂' F₂ b p.1 * H₂ p.1) (bdT₂.mul (hH₂ p.1)) m
  simp only [hval F₁ hG₁, hval F₂ hG₂] at h3
  simp only [plk]
  calc ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) (b ∘ Cv.v) *
        minorIJ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) I (stepCols N j p.2)
      = μ⁻¹ * ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) (b ∘ Cv.v) *
        minorIJ (S * (Cv.trans F₂' F₂ b p.1 * H₂ p.1)) I (stepCols N j p.2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun I _ => by rw [e₃ I]; ring
    _ = _ := by rw [h3, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind
