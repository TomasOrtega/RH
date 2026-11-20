import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDetBottomLeftNeZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.Ux3
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.PBI

section mk

variable {k j ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

open Classical in

def chartCoefficient (b b' : RC k j ρ → ℝ) (Φ : (Fin j → Fin j → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)) (g : B.Mat k (j + ρ)) :
    Wq →L[ℂ] Wp :=
  if DjU k j ρ g ≠ 0 then
    ((b (chart (Matrix.of.symm g)).1.1 * b' (chart (Matrix.of.symm g)).1.2 : ℝ) : ℂ) •
      Φ (chart (Matrix.of.symm g)).2.1 (chart (Matrix.of.symm g)).2.2
  else 0

def psiC (q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ)) : B.Mat k (j + ρ) :=
  (Rn k j ρ q.1.1)⁻¹ * mMap k j ρ (Matrix.of q.2.1) (Matrix.of q.2.2) * Rn k j ρ q.1.2

/- English proof (translation)
Conclude with `Formalism.FourierDecayAlt.P.Ux6.gV_slice q.1.1 q.1.2 _ ((Formalism.FourierDecayAlt.P.Ux2.sliceMem k j ρ).1 _ _ hZ hμ)`.
-/
theorem psiC_mem {q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ)} (hZ : (Matrix.of q.2.1).det ≠ 0)
    (hμ : Matrix.of q.2.2 ∈ B.GV k ρ) : psiC q ∈ B.GV k (j + ρ) := by
  exact Formalism.FourierDecayAlt.P.Ux6.gV_slice q.1.1 q.1.2 _ ((Formalism.FourierDecayAlt.P.Ux2.sliceMem k j ρ).1 _ _ hZ hμ)

/- English proof (translation)
Unfold `DjU psiC`. Rewrite using `[zhSlice]`.
-/
theorem djU_psiC (q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ)) :
    DjU k j ρ (psiC q) = (Matrix.of q.2.1).det := by
  unfold DjU psiC
  rw [zhSlice]

/- English proof (translation)
Establish `hg` using `psiC_mem hZ hμ`. Establish `hD : DjU k j ρ (psiC q) ≠ 0` using `by rw [djU_psiC]; exact hZ`. Take `⟨hZ', hμ', heq⟩` from `chart_spec (psiC q) hg hD`. Take `⟨q0, -, huniq⟩` from `big_cell_bijection k j ρ (psiC q) hg hD`. Establish `e1` using `huniq ((q.1.1, q.1.2), (Matrix.of q.2.1, Matrix.of q.2.2)) ⟨hZ, hμ, rfl⟩`.

Establish `e2` using `huniq ((chX (psiC q), chX' (psiC q)), (chZ (psiC q), chMu (psiC q))) ⟨hZ', hμ', heq⟩`. Establish `e` using `e2.trans e1.symm`. Simplify using `only [Prod.mk.injEq] at e`. Take `⟨⟨h1, h2⟩, h3, h4⟩` from `e`. Unfold `chart`.

Simplify using `only [Equiv.apply_symm_apply, h1, h2, h3, h4]`. Both sides reduce to the same expression.
-/
theorem chart_psiC {q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ)} (hZ : (Matrix.of q.2.1).det ≠ 0)
    (hμ : Matrix.of q.2.2 ∈ B.GV k ρ) : chart (Matrix.of.symm (psiC q)) = q := by
  have hg := psiC_mem hZ hμ
  have hD : DjU k j ρ (psiC q) ≠ 0 := by rw [djU_psiC]; exact hZ
  obtain ⟨hZ', hμ', heq⟩ := chart_spec (psiC q) hg hD
  obtain ⟨q0, -, huniq⟩ := big_cell_bijection k j ρ (psiC q) hg hD
  have e1 := huniq ((q.1.1, q.1.2), (Matrix.of q.2.1, Matrix.of q.2.2)) ⟨hZ, hμ, rfl⟩
  have e2 := huniq ((chX (psiC q), chX' (psiC q)), (chZ (psiC q), chMu (psiC q))) ⟨hZ', hμ', heq⟩
  have e := e2.trans e1.symm
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := e
  unfold chart
  simp only [Equiv.apply_symm_apply, h1, h2, h3, h4]
  rfl

/- English proof (translation)
Unfold `chartCoefficient`. Rewrite using `[if_pos (by rw [djU_psiC]; exact hZ), chart_psiC hZ hμ]`.
-/
theorem chartCoefficient_apply (b b' : RC k j ρ → ℝ) (Φ : (Fin j → Fin j → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp))
    (q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ)) (hZ : (Matrix.of q.2.1).det ≠ 0)
    (hμ : Matrix.of q.2.2 ∈ B.GV k ρ) :
    chartCoefficient b b' Φ (psiC q) = ((b q.1.1 * b' q.1.2 : ℝ) : ℂ) • Φ q.2.1 q.2.2 := by
  unfold chartCoefficient
  rw [if_pos (by rw [djU_psiC]; exact hZ), chart_psiC hZ hμ]

end mk

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P.PBI

section cont

open Formalism.FourierDecayAlt.P.PBI.Sm
open scoped ComplexConjugate

variable {k j ρ : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/- English proof (translation)
Establish `hU : MS (fun y => G.strictUpper (f y).1) x`. Introduce `a b`. Simplify using `only [G.strictUpper, Matrix.of_apply]`. Distinguish the cases in `h : a < b`. Simplify using `only [h, dite_true]`.

Conclude with `contDiffAt_pi.1 hf.fst ⟨(a, b), h⟩`. Simplify using `only [h, dite_false]`. Conclude with `contDiffAt_const`. Establish `hD : MS (fun y => Matrix.diagonal fun i => Complex.I * ((f y).2 i : ℂ)) x`. Introduce `a b`.

Simplify using `only [Matrix.diagonal_apply]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `only [if_true]`. Conclude with `contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_pi.1 hf.snd a))`.

Simplify using `only [h, if_false]`. Conclude with `contDiffAt_const`. Unfold `skewOf`. Conclude with `ms_add (ms_sub hU (ms_conjT hU)) hD`.
-/
theorem ms_skewOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    {f : E → (G.UT j → ℂ) × (Fin j → ℝ)} (hf : ContDiffAt ℝ ∞' f x) : MS (fun y => skewOf (f y)) x := by
  have hU : MS (fun y => G.strictUpper (f y).1) x := by
    intro a b
    simp only [G.strictUpper, Matrix.of_apply]
    by_cases h : a < b
    · simp only [h, dite_true]
      exact contDiffAt_pi.1 hf.fst ⟨(a, b), h⟩
    · simp only [h, dite_false]
      exact contDiffAt_const
  have hD : MS (fun y => Matrix.diagonal fun i => Complex.I * ((f y).2 i : ℂ)) x := by
    intro a b
    simp only [Matrix.diagonal_apply]
    by_cases h : a = b
    · subst h
      simp only [if_true]
      exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_pi.1 hf.snd a))
    · simp only [h, if_false]
      exact contDiffAt_const
  unfold skewOf
  exact ms_add (ms_sub hU (ms_conjT hU)) hD

/- English proof (translation)
Introduce `i j`. Conclude with `contDiffAt_pi.1 (contDiffAt_pi.1 hf i) j`.
-/
theorem ms_ofC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {m n : ℕ}
    {f : E → (Fin m → Fin n → ℂ)} (hf : ContDiffAt ℝ ∞' f x) : MS (fun y => Matrix.of (f y)) x := by
  intro i j
  exact contDiffAt_pi.1 (contDiffAt_pi.1 hf i) j

/- English proof (translation)
Establish `h1 : MS (fun y => Matrix.of (f y).1) x` using `ms_ofC hf.fst`. Establish `h2 : MS (fun y => skewOf (f y).2) x` using `ms_skewOf hf.snd`. Unfold `Rn`. Use `measurable_block_three (ms_const _) ?_ ?_ (ms_const _) (ms_const _) h1 (ms_const _) (ms_const _) (ms_const _)` and prove the remaining obligations. Conclude with `ms_neg (ms_mul (ms_mul (ms_const _) (ms_conjT h1)) (ms_const _))`.

Conclude with `ms_mul (ms_const _) (ms_add (ms_csmul _ (ms_mul (ms_mul (ms_conjT h1) (ms_const _)) h1)) h2)`.
-/
theorem ms_rnC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {f : E → RC k j ρ}
    (hf : ContDiffAt ℝ ∞' f x) : MS (fun y => Rn k j ρ (f y)) x := by
  have h1 : MS (fun y => Matrix.of (f y).1) x := ms_ofC hf.fst
  have h2 : MS (fun y => skewOf (f y).2) x := ms_skewOf hf.snd
  unfold Rn
  refine measurable_block_three (ms_const _) ?_ ?_ (ms_const _) (ms_const _) h1 (ms_const _) (ms_const _) (ms_const _)
  · exact ms_neg (ms_mul (ms_mul (ms_const _) (ms_conjT h1)) (ms_const _))
  · exact ms_mul (ms_const _) (ms_add (ms_csmul _ (ms_mul (ms_mul (ms_conjT h1) (ms_const _)) h1)) h2)

/- English proof (translation)
Conclude with `ms_inv (ms_rnC hf) (Matrix.det_ne_zero_of_left_inverse (rn_inv_mul _))`.
-/
theorem ms_rnC_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {f : E → RC k j ρ}
    (hf : ContDiffAt ℝ ∞' f x) : MS (fun y => (Rn k j ρ (f y))⁻¹) x := by
  exact ms_inv (ms_rnC hf) (Matrix.det_ne_zero_of_left_inverse (rn_inv_mul _))

/- English proof (translation)
Establish `hZ : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => Matrix.of q.2.1) q₀` using `ms_ofC (contDiffAt_fst.comp q₀ contDiffAt_snd)`. Establish `hγ : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => Matrix.of q.2.2) q₀` using `ms_ofC (contDiffAt_snd.comp q₀ contDiffAt_snd)`. Establish `hR1 : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => (Rn k j ρ q.1.1)⁻¹) q₀` using `ms_rnC_inv (contDiffAt_fst.comp q₀ contDiffAt_fst)`. Establish `hR2 : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => Rn k j ρ q.1.2) q₀` using `ms_rnC (contDiffAt_snd.comp q₀ contDiffAt_fst)`. Establish `hZi : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => (Matrix.of q.2.1)ᴴ⁻¹) q₀` using `ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact (star_ne_zero).2 h₀)`.

Establish `hM : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => mMap k j ρ (Matrix.of q.2.1) (Matrix.of q.2.2)) q₀`. Unfold `mMap`. Conclude with `measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hγ (ms_const _) (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)`. Unfold `psiC`. Conclude with `ms_mul (ms_mul hR1 hM) hR2`.
-/
theorem ms_psiC (q₀ : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ)) (h₀ : (Matrix.of q₀.2.1).det ≠ 0) :
    MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => psiC q) q₀ := by
  have hZ : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => Matrix.of q.2.1) q₀ := ms_ofC (contDiffAt_fst.comp q₀ contDiffAt_snd)
  have hγ : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => Matrix.of q.2.2) q₀ := ms_ofC (contDiffAt_snd.comp q₀ contDiffAt_snd)
  have hR1 : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => (Rn k j ρ q.1.1)⁻¹) q₀ := ms_rnC_inv (contDiffAt_fst.comp q₀ contDiffAt_fst)
  have hR2 : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => Rn k j ρ q.1.2) q₀ := ms_rnC (contDiffAt_snd.comp q₀ contDiffAt_fst)
  have hZi : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => (Matrix.of q.2.1)ᴴ⁻¹) q₀ :=
    ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact (star_ne_zero).2 h₀)
  have hM : MS (fun q : (RC k j ρ × RC k j ρ) × ((Fin j → Fin j → ℂ) × Mt k ρ) => mMap k j ρ (Matrix.of q.2.1) (Matrix.of q.2.2)) q₀ := by
    unfold mMap
    exact measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hγ (ms_const _)
      (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)
  unfold psiC
  exact ms_mul (ms_mul hR1 hM) hR2

/- English proof (translation)
Conclude with `continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => (hf i j).continuousAt`.
-/
theorem continuousAt_of_ms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {m n : Type*}
    [Fintype m] [Fintype n] {f : E → Matrix m n ℂ} (hf : MS f x) : ContinuousAt f x := by
  exact continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => (hf i j).continuousAt

end cont

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P.PBI

section cpt

open Formalism.FourierDecayAlt.P.PBI.Sm

variable {k j ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/- English proof (translation)
Unfold `B.gN`. Conclude with `(continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))).sqrt`.
-/
theorem continuous_gN' : Continuous (fun g : B.Mat k (j + ρ) => B.gN g) := by
  unfold B.gN
  exact (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))).sqrt

/- English proof (translation)
Use `set KG : Set ((Fin j → Fin j → ℂ) × Mt k ρ) := K ∩ {q | Matrix.of q.2 ∈ B.GV k ρ} with hKG`. Establish `hKGc : IsCompact KG` using `hK.inter_right (Formalism.FourierDecayAlt.P.B7.isClosed_GV.preimage continuous_snd)`. Use `set C := psiC '' ((tsupport b ×ˢ tsupport b') ×ˢ KG) with hCdef`. Establish `hCc : IsCompact C`. Use `IsCompact.image_of_continuousOn ((hbc.isCompact.prod hb'c.isCompact).prod hKGc) fun q hq => ?_` and prove the remaining obligations.

Conclude with `(continuousAt_of_ms (ms_psiC q (hKpos q.2 hq.2.1).1)).continuousWithinAt`. Establish `hsub : ∀ g ∈ B.GV k (j + ρ), chartCoefficient b b' Φ g ≠ 0 → g ∈ C`. Introduce `g hg hne`. Establish `hD : DjU k j ρ g ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Unfold `chartCoefficient`. Rewrite using `[if_neg (not_not.2 h0)]`. Take `⟨hZ, hμ, heq⟩` from `chart_spec g hg hD`. Unfold `chartCoefficient at hne`.

Rewrite `hne` using `[if_pos hD]`. Establish `hμ' : Matrix.of (chart (Matrix.of.symm g)).2.2 ∈ B.GV k ρ`. Simplify `hμ` using `[chart]`. Take `⟨hc, hΦne⟩` from `smul_ne_zero_iff.1 hne`. Establish `hc' : b (chart (Matrix.of.symm g)).1.1 * b' (chart (Matrix.of.symm g)).1.2 ≠ 0` using `by exact_mod_cast hc`.

Take `⟨hb1, hb2⟩` from `mul_ne_zero_iff.1 hc'`. Establish `hK' : (chart (Matrix.of.symm g)).2 ∈ K`. Assume the negation of the conclusion as `hn`. Conclude with `hΦne (hsupp _ hμ' hn)`. Use `⟨chart (Matrix.of.symm g), ⟨⟨subset_tsupport _ hb1, subset_tsupport _ hb2⟩, hK', hμ'⟩, ?_⟩` and prove the remaining obligations.

Unfold `psiC chart`. Simplify using `only [Equiv.apply_symm_apply]`. Conclude with `heq.symm`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g₀ hg₀`.

Distinguish the cases in `hC : g₀ ∈ C`. Take `⟨q₁, hq₁, rfl⟩` from `hC`. Establish `hdet : (Matrix.of q₁.2.1).det ≠ 0` using `(hKpos _ hq₁.2.1).1`. Establish `hμ₁ : Matrix.of q₁.2.2 ∈ B.GV k ρ` using `hq₁.2.2`. Establish `hch₁` using `chart_psiC hdet hμ₁`.

Take `⟨UΦ, FΦ, hUΦ, hq₁U, hFΦ, hΦF⟩` from `hΦ q₁.2 (hKV hq₁.2.1) hμ₁`. Establish `hOpenD : IsOpen {g : B.Mat k (j + ρ) | (bk31 g).det ≠ 0}` using `isOpen_det_bottom_left_ne_zero`. Establish `hchc : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) => chart (Matrix.of.symm g)) {g : B.Mat k (j + ρ) | (bk31 g).det ≠ 0}` using `chart_contDiffOn`. Use `set U := {g : B.Mat k (j + ρ) | (bk31 g).det ≠ 0} ∩ (fun g : B.Mat k (j + ρ) => (chart (Matrix.of.symm g)).2) ⁻¹' UΦ with hUdef`. Establish `hUo : IsOpen U` using `(hchc.continuousOn.snd).isOpen_inter_preimage hOpenD hUΦ`.

Establish `hD₁ : (bk31 (psiC q₁)).det ≠ 0` using `(djU_ne_iff _).1 (by rw [djU_psiC]; exact hdet)`. Use `⟨U, fun g => ((b (chart (Matrix.of.symm g)).1.1 * b' (chart (Matrix.of.symm g)).1.2 : ℝ) : ℂ) • FΦ (chart (Matrix.of.symm g)).2, hUo, ⟨hD₁, by simp only [Set.mem_preimage, hch₁]; exact hq₁U⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hsub' : U ⊆ {g : B.Mat k (j + ρ) | (bk31 g).det ≠ 0}` using `Set.inter_subset_left`. Establish `hchU` using `hchc.mono hsub'`. Establish `hx : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) => b (chart (Matrix.of.symm g)).1.1) U` using `hb.comp_contDiffOn ((contDiff_fst.comp contDiff_fst).comp_contDiffOn hchU)`.

Establish `hx' : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) => b' (chart (Matrix.of.symm g)).1.2) U` using `hb'.comp_contDiffOn ((contDiff_snd.comp contDiff_fst).comp_contDiffOn hchU)`. Establish `hF : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) => FΦ (chart (Matrix.of.symm g)).2) U` using `hFΦ.comp (contDiff_snd.comp_contDiffOn hchU) (fun g hg => hg.2)`. Establish `hc : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) => ((b (chart (Matrix.of.symm g)).1.1 * b' (chart (Matrix.of.symm g)).1.2 : ℝ) : ℂ)) U` using `Complex.ofRealCLM.contDiff.comp_contDiffOn (hx.mul hx')`. Conclude with `hc.smul hF`. Introduce `g hgU hgG`.

Establish `hD : DjU k j ρ g ≠ 0` using `(djU_ne_iff g).2 hgU.1`. Take `⟨-, hμ, -⟩` from `chart_spec g hgG hD`. Establish `hμ' : Matrix.of (chart (Matrix.of.symm g)).2.2 ∈ B.GV k ρ` using `by simpa [chart] using hμ`. Unfold `chartCoefficient`. Rewrite using `[if_pos hD, hΦF _ hgU.2 hμ']`.

Use `⟨Cᶜ, fun _ => 0, hCc.isClosed.isOpen_compl, hC, contDiffOn_const, fun g hgU hgG => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hgU (hsub g hgG hne)`. Take `⟨R, hR⟩` from `hCc.bddAbove_image continuous_gN'.continuousOn`. Conclude with `⟨R, fun g hg hne => hR ⟨g, hsub g hg hne, rfl⟩⟩`.

Distinguish the cases in `hKe : KG.Nonempty`. Use `set hf : (Fin j → Fin j → ℂ) × Mt k ρ → ℝ := fun q => Complex.normSq (Matrix.of q.1).det * Gf k ρ (lowV k j ρ Bs.z) (lowV k j ρ Bs.z') (Matrix.of q.2) with hfdef`. Establish `hcont : Continuous hf`. Establish `c1 : Continuous (fun q : (Fin j → Fin j → ℂ) × Mt k ρ => (Matrix.of q.1).det)` using `Continuous.matrix_det continuous_fst`. Establish `c2 : Continuous (fun q : (Fin j → Fin j → ℂ) × Mt k ρ => Gf k ρ (lowV k j ρ Bs.z) (lowV k j ρ Bs.z') (Matrix.of q.2))` using `(Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf (k := k) (r := ρ) _ _).continuous.comp continuous_snd`.

Conclude with `(Complex.continuous_normSq.comp c1).mul c2`. Take `⟨q₀, hq₀, hmin⟩` from `hKGc.exists_isMinOn hKe hcont.continuousOn`. Establish `hpos : 0 < hf q₀`. Take `⟨h1, h2⟩` from `hKpos q₀ hq₀.1`. Conclude with `mul_pos (Complex.normSq_pos.2 h1) h2`.

Use `⟨hf q₀, hpos, fun g hg hne => ?_⟩` and prove the remaining obligations. Take `⟨q, hq, rfl⟩` from `hsub g hg hne`. Establish `e` using `level_function_slice k j ρ Bs.z Bs.z' Bs.z_mem Bs.z'_mem q.1.1 q.1.2 (Matrix.of q.2.1) (Matrix.of q.2.2)`. Unfold `psiC`. Rewrite using `[e]`.

Conclude with `hmin hq.2`. Use `⟨1, one_pos, fun g hg hne => ?_⟩` and prove the remaining obligations. Take `⟨q, hq, -⟩` from `hsub g hg hne`. Conclude with `absurd ⟨q.2, hq.2⟩ hKe`.
-/
theorem chartCoefficient_hasCompactSupport (Bs : B.RealPlaceData k (j + ρ) Wp Wq) (b b' : RC k j ρ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hb' : ContDiff ℝ ∞ b') (hb'c : HasCompactSupport b')
    (Φ : (Fin j → Fin j → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)) (V : Set ((Fin j → Fin j → ℂ) × Mt k ρ)) (hV : IsOpen V)
    (hΦ : ∀ q₀ ∈ V, Matrix.of q₀.2 ∈ B.GV k ρ → ∃ (U : Set ((Fin j → Fin j → ℂ) × Mt k ρ))
      (F : (Fin j → Fin j → ℂ) × Mt k ρ → (Wq →L[ℂ] Wp)), IsOpen U ∧ q₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
        ∀ q ∈ U, Matrix.of q.2 ∈ B.GV k ρ → Φ q.1 q.2 = F q)
    (K : Set ((Fin j → Fin j → ℂ) × Mt k ρ)) (hK : IsCompact K) (hKV : K ⊆ V)
    (hKpos : ∀ q ∈ K, (Matrix.of q.1).det ≠ 0 ∧
      0 < Gf k ρ (lowV k j ρ Bs.z) (lowV k j ρ Bs.z') (Matrix.of q.2))
    (hsupp : ∀ q, Matrix.of q.2 ∈ B.GV k ρ → q ∉ K → Φ q.1 q.2 = 0) :
    KB.CptCoef Bs (chartCoefficient b b' Φ) := by
  set KG : Set ((Fin j → Fin j → ℂ) × Mt k ρ) := K ∩ {q | Matrix.of q.2 ∈ B.GV k ρ} with hKG
  have hKGc : IsCompact KG := hK.inter_right (Formalism.FourierDecayAlt.P.B7.isClosed_GV.preimage continuous_snd)
  set C := psiC '' ((tsupport b ×ˢ tsupport b') ×ˢ KG) with hCdef
  have hCc : IsCompact C := by
    refine IsCompact.image_of_continuousOn ((hbc.isCompact.prod hb'c.isCompact).prod hKGc) fun q hq => ?_
    exact (continuousAt_of_ms (ms_psiC q (hKpos q.2 hq.2.1).1)).continuousWithinAt

  have hsub : ∀ g ∈ B.GV k (j + ρ), chartCoefficient b b' Φ g ≠ 0 → g ∈ C := by
    intro g hg hne
    have hD : DjU k j ρ g ≠ 0 := by
      intro h0; apply hne; unfold chartCoefficient; rw [if_neg (not_not.2 h0)]
    obtain ⟨hZ, hμ, heq⟩ := chart_spec g hg hD
    unfold chartCoefficient at hne
    rw [if_pos hD] at hne
    have hμ' : Matrix.of (chart (Matrix.of.symm g)).2.2 ∈ B.GV k ρ := by
      simpa [chart] using hμ
    obtain ⟨hc, hΦne⟩ := smul_ne_zero_iff.1 hne
    have hc' : b (chart (Matrix.of.symm g)).1.1 * b' (chart (Matrix.of.symm g)).1.2 ≠ 0 := by exact_mod_cast hc
    obtain ⟨hb1, hb2⟩ := mul_ne_zero_iff.1 hc'
    have hK' : (chart (Matrix.of.symm g)).2 ∈ K := by
      by_contra hn; exact hΦne (hsupp _ hμ' hn)
    refine ⟨chart (Matrix.of.symm g), ⟨⟨subset_tsupport _ hb1, subset_tsupport _ hb2⟩, hK', hμ'⟩, ?_⟩
    unfold psiC chart
    simp only [Equiv.apply_symm_apply]
    exact heq.symm
  refine ⟨?_, ?_, ?_⟩
  ·
    intro g₀ hg₀
    by_cases hC : g₀ ∈ C
    · obtain ⟨q₁, hq₁, rfl⟩ := hC
      have hdet : (Matrix.of q₁.2.1).det ≠ 0 := (hKpos _ hq₁.2.1).1
      have hμ₁ : Matrix.of q₁.2.2 ∈ B.GV k ρ := hq₁.2.2
      have hch₁ := chart_psiC hdet hμ₁
      obtain ⟨UΦ, FΦ, hUΦ, hq₁U, hFΦ, hΦF⟩ := hΦ q₁.2 (hKV hq₁.2.1) hμ₁
      have hOpenD : IsOpen {g : B.Mat k (j + ρ) | (bk31 g).det ≠ 0} := isOpen_det_bottom_left_ne_zero
      have hchc : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) => chart (Matrix.of.symm g))
          {g : B.Mat k (j + ρ) | (bk31 g).det ≠ 0} := chart_contDiffOn
      set U := {g : B.Mat k (j + ρ) | (bk31 g).det ≠ 0} ∩
        (fun g : B.Mat k (j + ρ) => (chart (Matrix.of.symm g)).2) ⁻¹' UΦ with hUdef
      have hUo : IsOpen U :=
        (hchc.continuousOn.snd).isOpen_inter_preimage hOpenD hUΦ
      have hD₁ : (bk31 (psiC q₁)).det ≠ 0 := (djU_ne_iff _).1 (by rw [djU_psiC]; exact hdet)
      refine ⟨U, fun g => ((b (chart (Matrix.of.symm g)).1.1 * b' (chart (Matrix.of.symm g)).1.2 : ℝ) : ℂ) •
        FΦ (chart (Matrix.of.symm g)).2, hUo, ⟨hD₁, by simp only [Set.mem_preimage, hch₁]; exact hq₁U⟩, ?_, ?_⟩
      · have hsub' : U ⊆ {g : B.Mat k (j + ρ) | (bk31 g).det ≠ 0} := Set.inter_subset_left
        have hchU := hchc.mono hsub'
        have hx : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) => b (chart (Matrix.of.symm g)).1.1) U :=
          hb.comp_contDiffOn ((contDiff_fst.comp contDiff_fst).comp_contDiffOn hchU)
        have hx' : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) => b' (chart (Matrix.of.symm g)).1.2) U :=
          hb'.comp_contDiffOn ((contDiff_snd.comp contDiff_fst).comp_contDiffOn hchU)
        have hF : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) => FΦ (chart (Matrix.of.symm g)).2) U :=
          hFΦ.comp (contDiff_snd.comp_contDiffOn hchU) (fun g hg => hg.2)
        have hc : ContDiffOn ℝ ∞' (fun g : B.Mat k (j + ρ) =>
            ((b (chart (Matrix.of.symm g)).1.1 * b' (chart (Matrix.of.symm g)).1.2 : ℝ) : ℂ)) U :=
          Complex.ofRealCLM.contDiff.comp_contDiffOn (hx.mul hx')
        exact hc.smul hF
      · intro g hgU hgG
        have hD : DjU k j ρ g ≠ 0 := (djU_ne_iff g).2 hgU.1
        obtain ⟨-, hμ, -⟩ := chart_spec g hgG hD
        have hμ' : Matrix.of (chart (Matrix.of.symm g)).2.2 ∈ B.GV k ρ := by simpa [chart] using hμ
        unfold chartCoefficient
        rw [if_pos hD, hΦF _ hgU.2 hμ']
    · refine ⟨Cᶜ, fun _ => 0, hCc.isClosed.isOpen_compl, hC, contDiffOn_const, fun g hgU hgG => ?_⟩
      by_contra hne
      exact hgU (hsub g hgG hne)
  · obtain ⟨R, hR⟩ := hCc.bddAbove_image continuous_gN'.continuousOn
    exact ⟨R, fun g hg hne => hR ⟨g, hsub g hg hne, rfl⟩⟩
  · by_cases hKe : KG.Nonempty
    · set hf : (Fin j → Fin j → ℂ) × Mt k ρ → ℝ := fun q =>
        Complex.normSq (Matrix.of q.1).det * Gf k ρ (lowV k j ρ Bs.z) (lowV k j ρ Bs.z') (Matrix.of q.2) with hfdef
      have hcont : Continuous hf := by
        have c1 : Continuous (fun q : (Fin j → Fin j → ℂ) × Mt k ρ => (Matrix.of q.1).det) :=
          Continuous.matrix_det continuous_fst
        have c2 : Continuous (fun q : (Fin j → Fin j → ℂ) × Mt k ρ =>
            Gf k ρ (lowV k j ρ Bs.z) (lowV k j ρ Bs.z') (Matrix.of q.2)) :=
          (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf (k := k) (r := ρ) _ _).continuous.comp continuous_snd
        exact (Complex.continuous_normSq.comp c1).mul c2
      obtain ⟨q₀, hq₀, hmin⟩ := hKGc.exists_isMinOn hKe hcont.continuousOn
      have hpos : 0 < hf q₀ := by
        obtain ⟨h1, h2⟩ := hKpos q₀ hq₀.1
        exact mul_pos (Complex.normSq_pos.2 h1) h2
      refine ⟨hf q₀, hpos, fun g hg hne => ?_⟩
      obtain ⟨q, hq, rfl⟩ := hsub g hg hne
      have e := level_function_slice k j ρ Bs.z Bs.z' Bs.z_mem Bs.z'_mem q.1.1 q.1.2 (Matrix.of q.2.1) (Matrix.of q.2.2)
      unfold psiC
      rw [e]
      exact hmin hq.2
    · refine ⟨1, one_pos, fun g hg hne => ?_⟩
      obtain ⟨q, hq, -⟩ := hsub g hg hne
      exact absurd ⟨q.2, hq.2⟩ hKe

end cpt

end Formalism.FourierDecayAlt.P.PBI
