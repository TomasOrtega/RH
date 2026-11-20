import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpR
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffIteratedFDerivBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HsVecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.XFibreOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvMulVecOfFixedVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorEquivariance
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

namespace OpX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.AdmissibleLieWords PI.UnitaryCorollaryDerivatives.CRH

section ubl

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
The claim follows from `sCkOn_mono le_top fun _ _ => ⟨Set.univ, f, isOpen_univ, trivial, hf.contDiffOn, fun _ _ _ => rfl⟩`.
-/
theorem ckOn_of_contDiff {m : ℕ∞} {f : B.Mat k r → E} (hf : ContDiff ℝ ∞ f) : B.CkOn m (B.GV k r) f :=
  sCkOn_mono le_top fun _ _ => ⟨Set.univ, f, isOpen_univ, trivial, hf.contDiffOn, fun _ _ _ => rfl⟩

/- English proof (translation)
Take `⟨⟨C₁, hC₁, hb₁⟩, hl₁⟩` from `h₁`. Take `⟨⟨C₂, hC₂, hb₂⟩, hl₂⟩` from `h₂`. Use `⟨⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw g hg => ?_⟩, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, V, hV, hgV, haa⟩` from `hl₁ g hg`. Take `⟨b, hb, W, hW, hgW, hbb⟩` from `hl₂ g hg`.

Establish `hlie` using `admissible_word_mem_lie hw`. Establish `hG` using `hSG hg`. Establish `e0 : Dw w (fun g => f₁ g + f₂ g) g = Dw w (fun g => a g + b g) g` using `Dw_congr_loc hlie (hV.inter hW) (fun g' hG' hg' => by simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]) g hG ⟨hgV, hgW⟩`. Rewrite using `[e0, Dw_add hlie (ckOn_of_contDiff ha) (ckOn_of_contDiff hb) g hG, ← Dw_congr_loc hlie hV haa g hG hgV, ← Dw_congr_loc hlie hW hbb g hG hgW]`. Establish `b1` using `hb₁ w hw g hg`.

Establish `b2` using `hb₂ w hw g hg`. Combine the equalities or inequalities in the displayed calculation. Take `⟨a, ha, V, hV, hgV, haa⟩` from `hl₁ g hg`. Take `⟨b, hb, W, hW, hgW, hbb⟩` from `hl₂ g hg`. Conclude with `⟨fun g => a g + b g, ha.add hb, V ∩ W, hV.inter hW, ⟨hgV, hgW⟩, fun g' hG' hg' => by`.

Simplify using `[haa g' hG' hg'.1, hbb g' hG' hg'.2]⟩`.
-/
theorem ubl_add' {f₁ f₂ : B.Mat k r → E} {S : Set (B.Mat k r)} (hSG : S ⊆ B.GV k r) {n e γ : ℕ}
    (h₁ : UBL f₁ S n e γ) (h₂ : UBL f₂ S n e γ) : UBL (fun g => f₁ g + f₂ g) S n e γ := by
  obtain ⟨⟨C₁, hC₁, hb₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨C₂, hC₂, hb₂⟩, hl₂⟩ := h₂
  refine ⟨⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw g hg => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨a, ha, V, hV, hgV, haa⟩ := hl₁ g hg
    obtain ⟨b, hb, W, hW, hgW, hbb⟩ := hl₂ g hg
    have hlie := admissible_word_mem_lie hw
    have hG := hSG hg
    have e0 : Dw w (fun g => f₁ g + f₂ g) g = Dw w (fun g => a g + b g) g :=
      Dw_congr_loc hlie (hV.inter hW) (fun g' hG' hg' => by simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]) g hG
        ⟨hgV, hgW⟩
    rw [e0, Dw_add hlie (ckOn_of_contDiff ha) (ckOn_of_contDiff hb) g hG,
      ← Dw_congr_loc hlie hV haa g hG hgV, ← Dw_congr_loc hlie hW hbb g hG hgW]
    have b1 := hb₁ w hw g hg
    have b2 := hb₂ w hw g hg
    calc ‖Dw w f₁ g + Dw w f₂ g‖ ≤ ‖Dw w f₁ g‖ + ‖Dw w f₂ g‖ := norm_add_le _ _
      _ ≤ C₁ * B.gN g ^ (e + γ * w.length) + C₂ * B.gN g ^ (e + γ * w.length) := add_le_add b1 b2
      _ = (C₁ + C₂) * B.gN g ^ (e + γ * w.length) := by ring
  · obtain ⟨a, ha, V, hV, hgV, haa⟩ := hl₁ g hg
    obtain ⟨b, hb, W, hW, hgW, hbb⟩ := hl₂ g hg
    exact ⟨fun g => a g + b g, ha.add hb, V ∩ W, hV.inter hW, ⟨hgV, hgW⟩, fun g' hG' hg' => by
      simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]⟩

/- English proof (translation)
Use `ubl_clm ((c • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) hSG h` as an intermediate fact. Simplify using `using this`.
-/
theorem ubl_smulC (c : ℂ) {f : B.Mat k r → E} {S : Set (B.Mat k r)} (hSG : S ⊆ B.GV k r) {n e γ : ℕ}
    (h : UBL f S n e γ) : UBL (fun g => c • f g) S n e γ := by
  have := ubl_clm ((c • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) hSG h
  simpa using this

/- English proof (translation)
The claim follows from `| 0 => by simpa using ubl_mono hSG (ubl_const (0 : E) hSG n γ) (Nat.zero_le e) le_rfl | N + 1 => by have := ubl_add' hSG (ubl_sumRange hSG h N) (h N) simpa [Finset.sum_range_succ] using this`.
-/
theorem ubl_sumRange {f : ℕ → B.Mat k r → E} {S : Set (B.Mat k r)} (hSG : S ⊆ B.GV k r) {n e γ : ℕ}
    (h : ∀ i, UBL (f i) S n e γ) : ∀ N : ℕ, UBL (fun g => ∑ i ∈ Finset.range N, f i g) S n e γ
  | 0 => by
    simpa using ubl_mono hSG (ubl_const (0 : E) hSG n γ) (Nat.zero_le e) le_rfl
  | N + 1 => by
    have := ubl_add' hSG (ubl_sumRange hSG h N) (h N)
    simpa [Finset.sum_range_succ] using this

end ubl

section radial

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def OpAt (x : (Fin r → ℂ) × Mx k r) (T : Module.End ℂ (RadSp k r z z' π π'))
    (M : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Φ : RadSp k r z z' π π', (T Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = M ((Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2)

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C c`. Introduce `Φ`. Rewrite using `[Polynomial.aeval_C, Polynomial.aeval_C]`. Use `show ((c • Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _`.

Simplify using `[Algebra.algebraMap_eq_smul_one]`. Consider the case `add p q hp hq`. Introduce `Φ`. Rewrite using `[map_add, map_add]`. Use `show (((Polynomial.aeval a p).1 Φ + (Polynomial.aeval a q).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _`.

Simplify using `only [Submodule.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply]`. Rewrite using `[hp Φ, hq Φ]`. Consider the case `monomial n c hn`. Introduce `Φ`. Establish `e1 : Polynomial.C c * Polynomial.X ^ (n + 1) = Polynomial.C c * Polynomial.X ^ n * Polynomial.X`.

Rewrite using `[pow_succ, mul_assoc]`. Establish `e2 : Polynomial.aeval a (Polynomial.C c * Polynomial.X ^ n * Polynomial.X) = Polynomial.aeval a (Polynomial.C c * Polynomial.X ^ n) * a`. Simplify using `only [map_mul, Polynomial.aeval_X]`. Establish `e3 : Polynomial.aeval M (Polynomial.C c * Polynomial.X ^ n * Polynomial.X) = Polynomial.aeval M (Polynomial.C c * Polynomial.X ^ n) * M`. Simplify using `only [map_mul, Polynomial.aeval_X]`.

Rewrite using `[e1, e2, e3]`. Use `show ((Polynomial.aeval a (Polynomial.C c * Polynomial.X ^ n)).1 (a.1 Φ) : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _`. Rewrite using `[hn (a.1 Φ), h Φ]`. Both sides reduce to the same expression.
-/
theorem opAt_aeval {x : (Fin r → ℂ) × Mx k r} {a : Pr (RadSp k r z z' π π')}
    {M : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)} (h : OpAt x a.1 M) (p : Polynomial ℂ) :
    OpAt x (Polynomial.aeval a p).1 (Polynomial.aeval M p) := by
  induction p using Polynomial.induction_on with
  | C c =>
    intro Φ
    rw [Polynomial.aeval_C, Polynomial.aeval_C]
    show ((c • Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
    simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq =>
    intro Φ
    rw [map_add, map_add]
    show (((Polynomial.aeval a p).1 Φ + (Polynomial.aeval a q).1 Φ : RadSp k r z z' π π') :
      Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
    simp only [Submodule.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply]
    rw [hp Φ, hq Φ]
  | monomial n c hn =>
    intro Φ
    have e1 : Polynomial.C c * Polynomial.X ^ (n + 1) = Polynomial.C c * Polynomial.X ^ n * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    have e2 : Polynomial.aeval a (Polynomial.C c * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval a (Polynomial.C c * Polynomial.X ^ n) * a := by
      simp only [map_mul, Polynomial.aeval_X]
    have e3 : Polynomial.aeval M (Polynomial.C c * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval M (Polynomial.C c * Polynomial.X ^ n) * M := by
      simp only [map_mul, Polynomial.aeval_X]
    rw [e1, e2, e3]
    show ((Polynomial.aeval a (Polynomial.C c * Polynomial.X ^ n)).1 (a.1 Φ) : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
    rw [hn (a.1 Φ), h Φ]
    rfl

end radial

section equiv

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C c`. Introduce `A`. Simplify using `[Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, hφs]`. Consider the case `add p q hp hq`.

Introduce `A`. Simplify using `only [map_add, ContinuousLinearMap.add_apply, hp, hq, hφa]`. Consider the case `monomial n c hn`. Introduce `A`. Establish `e1 : Polynomial.C c * Polynomial.X ^ (n + 1) = Polynomial.C c * Polynomial.X ^ n * Polynomial.X`.

Rewrite using `[pow_succ, mul_assoc]`. Establish `e3 : ∀ K : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp), Polynomial.aeval K (Polynomial.C c * Polynomial.X ^ n * Polynomial.X) = Polynomial.aeval K (Polynomial.C c * Polynomial.X ^ n) * K` using `fun K => by`. Simplify using `only [map_mul, Polynomial.aeval_X]`. Rewrite using `[e1, e3 M, e3 N, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, h, hn]`.
-/
theorem aeval_intertwine (φ : (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (hφa : ∀ A B, φ (A + B) = φ A + φ B)
    (hφs : ∀ (c : ℂ) A, φ (c • A) = c • φ A) {M N : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)}
    (h : ∀ A, M (φ A) = φ (N A)) (p : Polynomial ℂ) :
    ∀ A, Polynomial.aeval M p (φ A) = φ (Polynomial.aeval N p A) := by
  induction p using Polynomial.induction_on with
  | C c =>
    intro A
    simp [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, hφs]
  | add p q hp hq =>
    intro A
    simp only [map_add, ContinuousLinearMap.add_apply, hp, hq, hφa]
  | monomial n c hn =>
    intro A
    have e1 : Polynomial.C c * Polynomial.X ^ (n + 1) = Polynomial.C c * Polynomial.X ^ n * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    have e3 : ∀ K : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp), Polynomial.aeval K (Polynomial.C c * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval K (Polynomial.C c * Polynomial.X ^ n) * K := fun K => by
      simp only [map_mul, Polynomial.aeval_X]
    rw [e1, e3 M, e3 N, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, h, hn]

end equiv

end OpX

section main

open OpX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.AdmissibleLieWords PI.UnitaryCorollaryDerivatives.CRH

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hYi`. Substitute `hz hz' hπ hπ'` using the available equality. Take `⟨B0, -, hxf⟩` from `x_fibre_of_parts big_cell_values omega_polynomial_facts capelli_vector_frame capelli_vector_equivariance Wp Wq P D X`. Take `⟨hfb, hfeq, hfrad⟩` from `hxf Y`. Take `⟨-, -, hpoly⟩` from `actual_algebra_facts Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD`.

Take `⟨q, hq⟩` from `hpoly Y hYi`. Take `⟨-, -, hL, hQQ, -, -, -, hst⟩` from `hD`. Use `set s : ℂ := M.sgn P l0 with hs`. Use `set xf : B.Mat P.k P.r → C6.EndH Wp Wq := TL.xFib D B0 (Y + ((P.k : ℂ) - 2) / 2) with hxfdef`. Use `set cf : B.Mat P.k P.r → C6.EndH Wp Wq := fun g => ((Gf P.k P.r D.z D.z' g : ℝ) : ℂ)⁻¹ • Polynomial.aeval (s • xf g) q with hcf`.

Set `T0 : B.DTerm P.k P.r Wp Wq` to `{ coef := cf coefAdj := fun g => HilbertSchmidtVectorization.adjH (cf g) word := [] word_lie := fun X hX => by simp at hX adj_id := fun g A B' => HilbertSchmidtVectorization.adjH_spec (cf g) A B' }`. Set `fib : Fin 1 → B.Mat P.k P.r → C6.EndH Wp Wq` to `fun _ => xf`. Establish `hfib : ∀ j, C6.FibBound D (fib j)` using `fun _ => hfb`. Establish `hP1 : U.IsPolyDeg 0 (fun _ : B.Mat P.k P.r => (1 : ℂ))` using `⟨MvPolynomial.C 1, by simp, fun g => by simp⟩`. Establish `hsum : cf = fun g => ∑ i ∈ Finset.range (q.natDegree + 1), (q.coeff i * s ^ i) • (((fun _ : B.Mat P.k P.r => (1 : ℂ)) g * C6.monoM D 0 0 1 g) • C6.Epart fib (List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r)))) g)`.

Use function extensionality and compare the values at `g`. Simplify using `only [hcf]`. Rewrite using `[Polynomial.aeval_eq_sum_range, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hm : C6.monoM D 0 0 1 g = (((Gf P.k P.r D.z D.z' g : ℝ) : ℂ))⁻¹` using `by simp [C6.monoM]`.

Establish `he : C6.Epart fib (List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r)))) g = xf g ^ i`. Simplify using `[C6.Epart, B.Rw, List.map_replicate, List.prod_replicate, fib]`. Rewrite using `[hm, he, smul_pow, smul_smul, smul_smul, smul_smul, one_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hU : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, UBL cf {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} n 0 (3 * (P.r + 1))`. Introduce `ε hε n`. Use `set S : Set (B.Mat P.k P.r) := {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} with hSdef`. Establish `hSG : S ⊆ B.GV P.k P.r` using `fun g hg => hg.1`. Use `set c₀ : ℝ := min ε (ε ^ 2) with hc₀`.

Establish `hc₀p : 0 < c₀` using `lt_min hε (by positivity)`. Establish `hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (P.r + 2))) ∨ l = Fin.last (P.r + 1)) → c₀ ≤ Complex.normSq (Dmin P.k P.r D.z D.z' g l)`. Introduce `g hg l hl`. Break down `hl with hl | rfl` into its components or cases. Simplify using `at hl`.

Use `Formalism.FourierDecayAlt.P.gram_function_last_minor P.k P.r D.z D.z' D.T_pos.le D.T'_pos.le g ε hg.2` as an intermediate fact. Conclude with `(min_le_left _ _).trans this`. Establish `hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf P.k P.r D.z D.z' g : ℝ) : ℂ)`. Introduce `g hg`. Rewrite using `[Complex.normSq_ofReal]`.

Establish `h1` using `hg.2`. Establish `: ε ^ 2 ≤ Gf P.k P.r D.z D.z' g * Gf P.k P.r D.z D.z' g` using `by nlinarith`. Conclude with `(min_le_right _ _).trans this`. Rewrite using `[hsum]`. Use `ubl_sumRange hSG (fun i => ubl_smulC _ hSG ?_) _` and prove the remaining obligations.

Establish `hes : ∀ e ∈ List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r))), ∀ X ∈ e.2, B.inLie P.k P.r X`. Introduce `e he X hX`. Rewrite `he` using `[List.mem_replicate]`. Rewrite `hX` using `[he.2]`. Simplify using `at hX`.

Establish `h` using `Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_coefP D fib hfib ∅ (fun _ => (1 : ℂ)) (0 : Fin (P.r + 2) → ℕ) (0 : Fin (P.r + 2) → ℕ) 1 (List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r)))) hP1 (fun _ _ _ => ⟨rfl, rfl⟩) hes hε (fun g hg => hg) hc₀p hSD hSGf n`. Conclude with `ubl_mono hSG h (by simp) le_rfl`. Establish `hUa : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, UBL (fun g => HilbertSchmidtVectorization.adjH (cf g)) {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} n 0 (3 * (P.r + 1))` using `fun ε hε n => ubl_clm HilbertSchmidtVectorization.adjR (fun g hg => hg.1) (hU ε hε n)`. Establish `hck : ∀ f : B.Mat P.k P.r → C6.EndH Wp Wq, (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, UBL f {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} n 0 (3 * (P.r + 1))) → B.CkOn ⊤ (B.GPos D) f`. Introduce `f hf g₀ hg₀`.

Take `⟨-, hl⟩` from `hf _ hg₀.2 0`. Take `⟨f', hf', V, hV, hgV, hff⟩` from `hl g₀ ⟨hg₀.1, le_rfl⟩`. Conclude with `⟨V, f', hV, hgV, hf'.contDiffOn, fun g hg hgG => hff g hgG hg⟩`. Use `⟨T0, ⟨rfl, hck cf hU, hck _ hUa, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `p hp g hg A`.

Establish `hgd : g ∈ C6.domL D ∅` using `⟨hg.1, hg.2, fun l hl => by simp at hl⟩`. Use `set φ : (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp) := fun J => (D.π (Matrix.of p.1.1)).comp (J.comp (D.π' (Matrix.of p.2.1)⁻¹)) with hφ`. Establish `hφa : ∀ A B', φ (A + B') = φ A + φ B'` using `fun A B' => by`. Simplify using `only [hφ, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]`. Establish `hφs : ∀ (c : ℂ) A, φ (c • A) = c • φ A` using `fun c A => by`.

Simplify using `only [hφ, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]`. Establish `hint : ∀ J, (s • xf g) (φ J) = φ ((s • xf (B.sgs p g)) J)` using `fun J => by`. Rewrite using `[ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hφs]`. Conclude with `congrArg (s • ·) (hfeq p hp g hgd J)`. Establish `h2` using `aeval_intertwine φ hφa hφs hint q A`.

Use `show cf g (φ A) = φ (cf (B.sgs p g) A)`. Simplify using `only [hcf, ContinuousLinearMap.smul_apply]`. Rewrite using `[h2, hφs, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs D hp g]`. Introduce `ε hε m`. Take `⟨⟨C1, hC1, hb1⟩, -⟩` from `hU ε hε m`.

Take `⟨⟨C2, hC2, hb2⟩, -⟩` from `hUa ε hε m`. Use `⟨max C1 C2, ((3 * (P.r + 1) * m : ℕ) : ℝ), by positivity, fun u v hu hv hl g hg hgε => ?_⟩` and prove the remaining obligations. Establish `hw : admitted m (wL u ++ wR v)` using `⟨u, v, hu, hv, hl, rfl⟩`. Establish `hS : g ∈ {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g}` using `⟨hg, hgε⟩`. Establish `hg1` using `gN_ge_one hg`.

Establish `hpow : B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length) ≤ B.gN g ^ ((3 * (P.r + 1) * m : ℕ) : ℝ)`. Rewrite using `[Real.rpow_natCast]`. Apply `pow_le_pow_right₀ hg1` to reduce the goal to its premises. Rewrite using `[len_LR]`. Use `Nat.mul_le_mul_left (3 * (P.r + 1)) hl` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hpos : 0 ≤ B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length)` using `by positivity`. Prove the components needed by the constructor for the conclusion. Use `show ‖B.dLR u v cf g‖ ≤ _`. Rewrite using `[dLR_eq]`.

Combine the equalities or inequalities in the displayed calculation. Use `show ‖B.dLR u v (fun g => HilbertSchmidtVectorization.adjH (cf g)) g‖ ≤ _`. Rewrite using `[dLR_eq]`. Combine the equalities or inequalities in the displayed calculation. Introduce `Ψ x hx`.

Use `set g : B.Mat P.k P.r := wCell P.k P.r (Fin.last P.r) x.1 * x.2 with hgdef`. Establish `hcell` using `big_cell_values P.k P.r Wp Wq D`. Establish `hGGpos : (0 : ℝ) < GGl P.k P.r D.z D.z' x.2` using `hx.2.2`. Establish `hGGi : Formalism.FourierDecayAlt.P.TLB.MulAt x L.GGi.1 ((GGl P.k P.r D.z D.z' x.2 : ℂ))⁻¹`. Rewrite using `[hL.2.2.2.2.2.2.2.2.2.2.2.1]`.

Conclude with `Formalism.FourierDecayAlt.P.TLB.act_fn X x hx 5`. Establish `hDri : Formalism.FourierDecayAlt.P.TLB.MulAt x L.Dri.1 (∏ a, (x.1 a)⁻¹)` using `Formalism.FourierDecayAlt.P.TLB.mulAt_ofFn L.ci _ fun l => Formalism.FourierDecayAlt.P.TLB.act_ci X L hL x l`. Establish `hDrbi : Formalism.FourierDecayAlt.P.TLB.MulAt x L.Drbi.1 (∏ a, (star (x.1 a))⁻¹)` using `Formalism.FourierDecayAlt.P.TLB.mulAt_ofFn L.cbi _ fun l => Formalism.FourierDecayAlt.P.TLB.act_cbi X L hL x l`. Establish `hGi : Formalism.FourierDecayAlt.P.TLB.MulAt x (GiR L).1 (((Gf P.k P.r D.z D.z' g : ℝ) : ℂ))⁻¹`. Rewrite using `[hgdef, (hcell x hx).2.2.2, Complex.ofReal_mul, ← Complex.mul_conj, mul_inv, mul_inv, ← Finset.prod_inv_distrib, map_prod, ← Finset.prod_inv_distrib]`.

Conclude with `Formalism.FourierDecayAlt.P.TLB.mulAt_mul (Formalism.FourierDecayAlt.P.TLB.mulAt_mul hDri hDrbi) hGGi`. Establish `hX : OpAt x (st.x Y).1 (s • xf g)`. Introduce `Φ`. Establish `e1 : st.x Y = L.GGi * st.QQ Y 1 1` using `by rw [hst.tau Y, ← mul_assoc, L.GGi_GG, one_mul]`. Rewrite using `[e1, hQQ Y]`.

Use `show (L.GGi.1 ((s • X.QQ Y 1 1).1 Φ) : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _`. Rewrite using `[hGGi]`. Establish `e3 : (s • X.QQ Y 1 1).1 Φ = s • X.t Y 1 1 Φ`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.

Rewrite using `[e3, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hfrad Φ x hx, ContinuousLinearMap.smul_apply, smul_smul, smul_smul]`. Establish `hne : ((GGl P.k P.r D.z D.z' x.2 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hGGpos.ne'`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hXi : OpAt x (st.xi Y).1 (Polynomial.aeval (s • xf g) q)`.

Rewrite using `[hq]`. Conclude with `opAt_aeval hX q`. Use `show (((GiR L).1 ((st.xi Y).1 Ψ) : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = cf g ((Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)`. Rewrite using `[hGi, hXi]`. Both sides reduce to the same expression.
-/
theorem spectral_operator_X : RDSOpX := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hYi
  subst hz hz' hπ hπ'
  obtain ⟨B0, -, hxf⟩ := x_fibre_of_parts big_cell_values omega_polynomial_facts capelli_vector_frame
    capelli_vector_equivariance Wp Wq P D X
  obtain ⟨hfb, hfeq, hfrad⟩ := hxf Y
  obtain ⟨-, -, hpoly⟩ := actual_algebra_facts Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD
  obtain ⟨q, hq⟩ := hpoly Y hYi
  obtain ⟨-, -, hL, hQQ, -, -, -, hst⟩ := hD
  set s : ℂ := M.sgn P l0 with hs
  set xf : B.Mat P.k P.r → C6.EndH Wp Wq := TL.xFib D B0 (Y + ((P.k : ℂ) - 2) / 2) with hxfdef
  set cf : B.Mat P.k P.r → C6.EndH Wp Wq := fun g =>
    ((Gf P.k P.r D.z D.z' g : ℝ) : ℂ)⁻¹ • Polynomial.aeval (s • xf g) q with hcf
  let T0 : B.DTerm P.k P.r Wp Wq :=
    { coef := cf
      coefAdj := fun g => HilbertSchmidtVectorization.adjH (cf g)
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun g A B' => HilbertSchmidtVectorization.adjH_spec (cf g) A B' }

  let fib : Fin 1 → B.Mat P.k P.r → C6.EndH Wp Wq := fun _ => xf
  have hfib : ∀ j, C6.FibBound D (fib j) := fun _ => hfb
  have hP1 : U.IsPolyDeg 0 (fun _ : B.Mat P.k P.r => (1 : ℂ)) := ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
  have hsum : cf = fun g => ∑ i ∈ Finset.range (q.natDegree + 1), (q.coeff i * s ^ i) •
      (((fun _ : B.Mat P.k P.r => (1 : ℂ)) g * C6.monoM D 0 0 1 g) •
        C6.Epart fib (List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r)))) g) := by
    funext g
    simp only [hcf]
    rw [Polynomial.aeval_eq_sum_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm : C6.monoM D 0 0 1 g = (((Gf P.k P.r D.z D.z' g : ℝ) : ℂ))⁻¹ := by simp [C6.monoM]
    have he : C6.Epart fib (List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r)))) g = xf g ^ i := by
      simp [C6.Epart, B.Rw, List.map_replicate, List.prod_replicate, fib]
    rw [hm, he, smul_pow, smul_smul, smul_smul, smul_smul, one_mul]
    congr 1
    ring
  have hU : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      UBL cf {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} n 0 (3 * (P.r + 1)) := by
    intro ε hε n
    set S : Set (B.Mat P.k P.r) := {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} with hSdef
    have hSG : S ⊆ B.GV P.k P.r := fun g hg => hg.1
    set c₀ : ℝ := min ε (ε ^ 2) with hc₀
    have hc₀p : 0 < c₀ := lt_min hε (by positivity)
    have hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (P.r + 2))) ∨ l = Fin.last (P.r + 1)) →
        c₀ ≤ Complex.normSq (Dmin P.k P.r D.z D.z' g l) := by
      intro g hg l hl
      rcases hl with hl | rfl
      · simp at hl
      · have := Formalism.FourierDecayAlt.P.gram_function_last_minor P.k P.r D.z D.z' D.T_pos.le D.T'_pos.le g ε hg.2
        exact (min_le_left _ _).trans this
    have hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf P.k P.r D.z D.z' g : ℝ) : ℂ) := by
      intro g hg
      rw [Complex.normSq_ofReal]
      have h1 := hg.2
      have : ε ^ 2 ≤ Gf P.k P.r D.z D.z' g * Gf P.k P.r D.z D.z' g := by nlinarith
      exact (min_le_right _ _).trans this
    rw [hsum]
    refine ubl_sumRange hSG (fun i => ubl_smulC _ hSG ?_) _
    have hes : ∀ e ∈ List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r))), ∀ X ∈ e.2, B.inLie P.k P.r X := by
      intro e he X hX
      rw [List.mem_replicate] at he
      rw [he.2] at hX
      simp at hX
    have h := Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_coefP D fib hfib ∅ (fun _ => (1 : ℂ)) (0 : Fin (P.r + 2) → ℕ)
      (0 : Fin (P.r + 2) → ℕ) 1 (List.replicate i ((0 : Fin 1), ([] : List (B.Mat P.k P.r)))) hP1
      (fun _ _ _ => ⟨rfl, rfl⟩) hes hε (fun g hg => hg) hc₀p hSD hSGf n
    exact ubl_mono hSG h (by simp) le_rfl
  have hUa : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      UBL (fun g => HilbertSchmidtVectorization.adjH (cf g)) {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} n 0 (3 * (P.r + 1)) :=
    fun ε hε n => ubl_clm HilbertSchmidtVectorization.adjR (fun g hg => hg.1) (hU ε hε n)
  have hck : ∀ f : B.Mat P.k P.r → C6.EndH Wp Wq,
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, UBL f {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} n 0 (3 * (P.r + 1))) →
      B.CkOn ⊤ (B.GPos D) f := by
    intro f hf g₀ hg₀
    obtain ⟨-, hl⟩ := hf _ hg₀.2 0
    obtain ⟨f', hf', V, hV, hgV, hff⟩ := hl g₀ ⟨hg₀.1, le_rfl⟩
    exact ⟨V, f', hV, hgV, hf'.contDiffOn, fun g hg hgG => hff g hgG hg⟩
  refine ⟨T0, ⟨rfl, hck cf hU, hck _ hUa, ?_, ?_⟩, ?_⟩
  ·
    intro p hp g hg A
    have hgd : g ∈ C6.domL D ∅ := ⟨hg.1, hg.2, fun l hl => by simp at hl⟩
    set φ : (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp) := fun J =>
      (D.π (Matrix.of p.1.1)).comp (J.comp (D.π' (Matrix.of p.2.1)⁻¹)) with hφ
    have hφa : ∀ A B', φ (A + B') = φ A + φ B' := fun A B' => by
      simp only [hφ, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    have hφs : ∀ (c : ℂ) A, φ (c • A) = c • φ A := fun c A => by
      simp only [hφ, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    have hint : ∀ J, (s • xf g) (φ J) = φ ((s • xf (B.sgs p g)) J) := fun J => by
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hφs]
      exact congrArg (s • ·) (hfeq p hp g hgd J)
    have h2 := aeval_intertwine φ hφa hφs hint q A
    show cf g (φ A) = φ (cf (B.sgs p g) A)
    simp only [hcf, ContinuousLinearMap.smul_apply]
    rw [h2, hφs, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs D hp g]
  ·
    intro ε hε m
    obtain ⟨⟨C1, hC1, hb1⟩, -⟩ := hU ε hε m
    obtain ⟨⟨C2, hC2, hb2⟩, -⟩ := hUa ε hε m
    refine ⟨max C1 C2, ((3 * (P.r + 1) * m : ℕ) : ℝ), by positivity, fun u v hu hv hl g hg hgε => ?_⟩
    have hw : admitted m (wL u ++ wR v) := ⟨u, v, hu, hv, hl, rfl⟩
    have hS : g ∈ {g | g ∈ B.GV P.k P.r ∧ ε ≤ Gf P.k P.r D.z D.z' g} := ⟨hg, hgε⟩
    have hg1 := gN_ge_one hg
    have hpow : B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length) ≤ B.gN g ^ ((3 * (P.r + 1) * m : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      apply pow_le_pow_right₀ hg1
      rw [len_LR]
      have := Nat.mul_le_mul_left (3 * (P.r + 1)) hl
      omega
    have hpos : 0 ≤ B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length) := by positivity
    constructor
    · show ‖B.dLR u v cf g‖ ≤ _
      rw [dLR_eq]
      calc _ ≤ C1 * B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length) := hb1 _ hw g hS
        _ ≤ max C1 C2 * B.gN g ^ ((3 * (P.r + 1) * m : ℕ) : ℝ) :=
          mul_le_mul (le_max_left _ _) hpow hpos (le_trans hC1 (le_max_left _ _))
    · show ‖B.dLR u v (fun g => HilbertSchmidtVectorization.adjH (cf g)) g‖ ≤ _
      rw [dLR_eq]
      calc _ ≤ C2 * B.gN g ^ (0 + 3 * (P.r + 1) * (wL u ++ wR v).length) := hb2 _ hw g hS
        _ ≤ max C1 C2 * B.gN g ^ ((3 * (P.r + 1) * m : ℕ) : ℝ) :=
          mul_le_mul (le_max_right _ _) hpow hpos (le_trans hC2 (le_max_right _ _))
  ·
    intro Ψ x hx
    set g : B.Mat P.k P.r := wCell P.k P.r (Fin.last P.r) x.1 * x.2 with hgdef
    have hcell := big_cell_values P.k P.r Wp Wq D
    have hGGpos : (0 : ℝ) < GGl P.k P.r D.z D.z' x.2 := hx.2.2
    have hGGi : Formalism.FourierDecayAlt.P.TLB.MulAt x L.GGi.1 ((GGl P.k P.r D.z D.z' x.2 : ℂ))⁻¹ := by
      rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact Formalism.FourierDecayAlt.P.TLB.act_fn X x hx 5
    have hDri : Formalism.FourierDecayAlt.P.TLB.MulAt x L.Dri.1 (∏ a, (x.1 a)⁻¹) :=
      Formalism.FourierDecayAlt.P.TLB.mulAt_ofFn L.ci _ fun l => Formalism.FourierDecayAlt.P.TLB.act_ci X L hL x l
    have hDrbi : Formalism.FourierDecayAlt.P.TLB.MulAt x L.Drbi.1 (∏ a, (star (x.1 a))⁻¹) :=
      Formalism.FourierDecayAlt.P.TLB.mulAt_ofFn L.cbi _ fun l => Formalism.FourierDecayAlt.P.TLB.act_cbi X L hL x l
    have hGi : Formalism.FourierDecayAlt.P.TLB.MulAt x (GiR L).1 (((Gf P.k P.r D.z D.z' g : ℝ) : ℂ))⁻¹ := by
      rw [hgdef, (hcell x hx).2.2.2, Complex.ofReal_mul, ← Complex.mul_conj, mul_inv, mul_inv,
        ← Finset.prod_inv_distrib, map_prod, ← Finset.prod_inv_distrib]
      exact Formalism.FourierDecayAlt.P.TLB.mulAt_mul (Formalism.FourierDecayAlt.P.TLB.mulAt_mul hDri hDrbi) hGGi
    have hX : OpAt x (st.x Y).1 (s • xf g) := by
      intro Φ
      have e1 : st.x Y = L.GGi * st.QQ Y 1 1 := by rw [hst.tau Y, ← mul_assoc, L.GGi_GG, one_mul]
      rw [e1, hQQ Y]
      show (L.GGi.1 ((s • X.QQ Y 1 1).1 Φ) : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
      rw [hGGi]
      have e3 : (s • X.QQ Y 1 1).1 Φ = s • X.t Y 1 1 Φ := by
        rw [Algebra.smul_def]
        rfl
      rw [e3, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hfrad Φ x hx, ContinuousLinearMap.smul_apply,
        smul_smul, smul_smul]
      have hne : ((GGl P.k P.r D.z D.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hGGpos.ne'
      congr 1
      field_simp
    have hXi : OpAt x (st.xi Y).1 (Polynomial.aeval (s • xf g) q) := by
      rw [hq]; exact opAt_aeval hX q
    show (((GiR L).1 ((st.xi Y).1 Ψ) : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      cf g ((Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
    rw [hGi, hXi]
    rfl

end main

end Formalism.FourierDecayAlt.P.CutSE
