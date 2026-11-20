import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomInvSqrt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ContDiff Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section tools

variable {k r : ℕ}

/- English proof (translation)
Introduce `g₀ _`. Conclude with `⟨Set.univ, f, isOpen_univ, Set.mem_univ _, (hf.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn, fun _ _ _ => rfl⟩`.
-/
theorem ckOn_of_cd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} (hf : ContDiff ℝ ∞ f)
    (m : ℕ∞) (UU : Set (Mat k r)) : CkOn m UU f := by
  intro g₀ _
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn, fun _ _ _ => rfl⟩

/- English proof (translation)
Introduce `g hg`. Take `⟨a, ha, V, hV, hgV, hae⟩` from `hl₁ g hg`. Take `⟨b, hb, W, hW, hgW, hbe⟩` from `hl₂ g hg`. Use `⟨fun g => a g + b g, ha.add hb, V ∩ W, hV.inter hW, ⟨hgV, hgW⟩, fun g' hg' hm => ?_⟩` and prove the remaining obligations. Use `show f₁ g' + f₂ g' = a g' + b g'`.

Rewrite using `[hae g' hg' hm.1, hbe g' hg' hm.2]`.
-/
theorem lss_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    {f₁ f₂ : Mat k r → E} (hl₁ : LSS f₁ S) (hl₂ : LSS f₂ S) : LSS (fun g => f₁ g + f₂ g) S := by
  intro g hg
  obtain ⟨a, ha, V, hV, hgV, hae⟩ := hl₁ g hg
  obtain ⟨b, hb, W, hW, hgW, hbe⟩ := hl₂ g hg
  refine ⟨fun g => a g + b g, ha.add hb, V ∩ W, hV.inter hW, ⟨hgV, hgW⟩, fun g' hg' hm => ?_⟩
  show f₁ g' + f₂ g' = a g' + b g'
  rw [hae g' hg' hm.1, hbe g' hg' hm.2]

/- English proof (translation)
Take `⟨⟨C₁, hC₁, hb₁⟩, hl₁⟩` from `h₁`. Take `⟨⟨C₂, hC₂, hb₂⟩, hl₂⟩` from `h₂`. Use `⟨⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw g hg => ?_⟩, lss_add hl₁ hl₂⟩` and prove the remaining obligations. Take `⟨a, ha, V, hV, hgV, haa⟩` from `hl₁ g hg`. Take `⟨b, hb, W, hW, hgW, hbb⟩` from `hl₂ g hg`.

Establish `hlie` using `admissible_word_mem_lie hw`. Establish `hG` using `hSG hg`. Establish `e0 : Dw w (fun g => f₁ g + f₂ g) g = Dw w (fun g => a g + b g) g` using `Dw_congr_loc hlie (hV.inter hW) (fun g' hG' hg' => by simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]) g hG ⟨hgV, hgW⟩`. Rewrite using `[e0, Dw_add hlie (ckOn_of_cd ha _ _) (ckOn_of_cd hb _ _) g hG, ← Dw_congr_loc hlie hV haa g hG hgV, ← Dw_congr_loc hlie hW hbb g hG hgW]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[add_mul]`. Conclude with `add_le_add (hb₁ w hw g hg) (hb₂ w hw g hg)`.
-/
theorem ubl_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {f₁ f₂ : Mat k r → E} {n e γ : ℕ} (h₁ : UBL f₁ S n e γ) (h₂ : UBL f₂ S n e γ) :
    UBL (fun g => f₁ g + f₂ g) S n e γ := by
  obtain ⟨⟨C₁, hC₁, hb₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨C₂, hC₂, hb₂⟩, hl₂⟩ := h₂
  refine ⟨⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw g hg => ?_⟩, lss_add hl₁ hl₂⟩
  obtain ⟨a, ha, V, hV, hgV, haa⟩ := hl₁ g hg
  obtain ⟨b, hb, W, hW, hgW, hbb⟩ := hl₂ g hg
  have hlie := admissible_word_mem_lie hw
  have hG := hSG hg
  have e0 : Dw w (fun g => f₁ g + f₂ g) g = Dw w (fun g => a g + b g) g :=
    Dw_congr_loc hlie (hV.inter hW) (fun g' hG' hg' => by simp [haa g' hG' hg'.1, hbb g' hG' hg'.2]) g hG
      ⟨hgV, hgW⟩
  rw [e0, Dw_add hlie (ckOn_of_cd ha _ _) (ckOn_of_cd hb _ _) g hG,
    ← Dw_congr_loc hlie hV haa g hG hgV, ← Dw_congr_loc hlie hW hbb g hG hgW]
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add (hb₁ w hw g hg) (hb₂ w hw g hg)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `ubl_mono hSG (ubl_const (0 : E) hSG n γ) (Nat.zero_le e) le_rfl`. Consider the case `@insert a s has ih`.

Simplify using `only [Finset.sum_insert has]`. Conclude with `ubl_add hSG (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem ubl_sum {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    (s : Finset ι) {f : ι → Mat k r → E} {n e γ : ℕ} (h : ∀ i ∈ s, UBL (f i) S n e γ) :
    UBL (fun g => ∑ i ∈ s, f i g) S n e γ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ubl_mono hSG (ubl_const (0 : E) hSG n γ) (Nat.zero_le e) le_rfl
  | @insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact ubl_add hSG (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `g hg`. Use `choose F hF V hV hgV hFe using fun i => h i g hg`. Use `⟨fun g i => F i g, contDiff_pi.2 hF, ⋂ i, V i, isOpen_iInter_of_finite hV, Set.mem_iInter.2 hgV, fun g' hg' hm => funext fun i => hFe i g' hg' (Set.mem_iInter.1 hm i)⟩` and prove the remaining obligations.
-/
theorem lss_pi {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    {f : Mat k r → ι → E} (h : ∀ i, LSS (fun g => f g i) S) : LSS f S := by
  intro g hg
  choose F hF V hV hgV hFe using fun i => h i g hg
  refine ⟨fun g i => F i g, contDiff_pi.2 hF, ⋂ i, V i, isOpen_iInter_of_finite hV,
    Set.mem_iInter.2 hgV, fun g' hg' hm => funext fun i => hFe i g' hg' (Set.mem_iInter.1 hm i)⟩

/- English proof (translation)
Establish `h1` using `fun i => (h i).1`. Establish `hL` using `fun i => (h i).2`. Use `choose C hC hB using h1`. Establish `hCs : 0 ≤ ∑ i, C i` using `Finset.sum_nonneg fun i _ => hC i`. Use `⟨⟨∑ i, C i, hCs, fun w hw g hg => ?_⟩, lss_pi hL⟩` and prove the remaining obligations.

Establish `hlie` using `admissible_word_mem_lie hw`. Establish `hgG` using `hSG hg`. Establish `hgN : 0 ≤ gN g` using `Real.sqrt_nonneg _`. Take `⟨F, hF, V, hV, hgV, hFe⟩` from `lss_pi hL g hg`. Rewrite using `[Dw_congr_loc hlie hV hFe g hgG hgV]`.

Use `(pi_norm_le_iff_of_nonneg (mul_nonneg hCs (pow_nonneg hgN _))).2 fun i => ?_` and prove the remaining obligations. Rewrite using `[Formalism.FourierDecayAlt.P.Ux8.Dw_pi hlie (ckOn_of_cd hF _ _) g hgG i]`. Establish `e1` using `Dw_congr_loc hlie hV (f := fun g => f g i) (f₂ := fun g => F g i) (fun g' hg' hm => congrFun (hFe g' hg' hm) i) g hgG hgV`. Rewrite using `[← e1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ubl_pi {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set (Mat k r)}
    (hSG : S ⊆ GV k r) {f : Mat k r → ι → E} {n e γ : ℕ} (h : ∀ i, UBL (fun g => f g i) S n e γ) :
    UBL f S n e γ := by
  have h1 := fun i => (h i).1
  have hL := fun i => (h i).2
  choose C hC hB using h1
  have hCs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨⟨∑ i, C i, hCs, fun w hw g hg => ?_⟩, lss_pi hL⟩
  have hlie := admissible_word_mem_lie hw
  have hgG := hSG hg
  have hgN : 0 ≤ gN g := Real.sqrt_nonneg _
  obtain ⟨F, hF, V, hV, hgV, hFe⟩ := lss_pi hL g hg
  rw [Dw_congr_loc hlie hV hFe g hgG hgV]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hCs (pow_nonneg hgN _))).2 fun i => ?_
  rw [Formalism.FourierDecayAlt.P.Ux8.Dw_pi hlie (ckOn_of_cd hF _ _) g hgG i]
  have e1 := Dw_congr_loc hlie hV (f := fun g => f g i) (f₂ := fun g => F g i)
    (fun g' hg' hm => congrFun (hFe g' hg' hm) i) g hgG hgV
  rw [← e1]
  calc ‖Dw w (fun g => f g i) g‖ ≤ C i * gN g ^ (e + γ * w.length) := hB i w hw g hg
    _ ≤ (∑ j, C j) * gN g ^ (e + γ * w.length) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
          (pow_nonneg hgN _)

/- English proof (translation)
Establish `hfun : (fun g => star (f g)) = fun g => (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap (f g)`. Use function extensionality and compare the values at `g`. Both sides reduce to the same expression. Rewrite using `[hfun]`. Conclude with `ubl_clm _ hSG h`.
-/
theorem ubl_star {S : Set (Mat k r)} (hSG : S ⊆ GV k r) {f : Mat k r → ℂ} {n e γ : ℕ} (h : UBL f S n e γ) :
    UBL (fun g => star (f g)) S n e γ := by
  have hfun : (fun g => star (f g)) =
      fun g => (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap (f g) := by
    funext g; rfl
  rw [hfun]
  exact ubl_clm _ hSG h

/- English proof (translation)
Establish `hfun : (fun g => (A g * B g) i j) = fun g => ∑ l ∈ Finset.univ, A g i l * B g l j`. Use function extensionality and compare the values at `g`. Simplify using `[Matrix.mul_apply]`. Rewrite using `[hfun]`. Conclude with `ubl_sum hSG _ fun l _ => ubl_mul hSG (hA i l) (hB l j)`.
-/
theorem ubl_mmul {m : ℕ} {S : Set (Mat k r)} (hSG : S ⊆ GV k r)
    {A B : Mat k r → Matrix (Fin m) (Fin m) ℂ} {n ea eb γ : ℕ}
    (hA : ∀ i j, UBL (fun g => A g i j) S n ea γ) (hB : ∀ i j, UBL (fun g => B g i j) S n eb γ) (i j : Fin m) :
    UBL (fun g => (A g * B g) i j) S n (ea + eb) γ := by
  have hfun : (fun g => (A g * B g) i j) = fun g => ∑ l ∈ Finset.univ, A g i l * B g l j := by
    funext g; simp [Matrix.mul_apply]
  rw [hfun]
  exact ubl_sum hSG _ fun l _ => ubl_mul hSG (hA i l) (hB l j)

end tools

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
