import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

section Loc

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
The claim follows from `g.2`.
-/
theorem umat_mem (g : Formalism.REAL.UJ ε) : umat g ∈ UJset ε := g.2

def homOf (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsURepOn (UJset ε) σ) :
    Formalism.REAL.UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (umat g)
  map_one' := h.1.1
  map_mul' a b := h.1.2 _ (umat_mem a) _ (umat_mem b)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homOf_apply (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsURepOn (UJset ε) σ)
    (g : Formalism.REAL.UJ ε) : homOf σ h g = σ (umat g) := rfl

/- English proof (translation)
The claim follows from `h.2.1 _ (umat_mem g) x`.
-/
theorem homOf_norm (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsURepOn (UJset ε) σ)
    (g : Formalism.REAL.UJ ε) (x : H) : ‖homOf σ h g x‖ = ‖x‖ := h.2.1 _ (umat_mem g) x

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_umat : Continuous (fun g : Formalism.REAL.UJ ε => umat g) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
The claim follows from `(h.2.2 x).comp_continuous continuous_umat umat_mem`.
-/
theorem homOf_cont (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsURepOn (UJset ε) σ) (x : H) :
    Continuous fun g => homOf σ h g x :=
  (h.2.2 x).comp_continuous continuous_umat umat_mem

/- English proof (translation)
Establish `: star z = (starRingEnd ℂ) z` using `rfl`. Rewrite using `[this, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.
-/
theorem mul_star_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  have : star z = (starRingEnd ℂ) z := rfl
  rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Take `⟨hi, he⟩` from `hd.2 x y x y`. Establish `hfun : (fun g : Formalism.REAL.UJ ε => coefOn σ x y g * star (coefOn σ x y g)) = fun g : Formalism.REAL.UJ ε => ((‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)`. Use function extensionality and compare the values at `g`. Conclude with `mul_star_eq _`. Rewrite `hi`, `he` using `[hfun]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `hi.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _)`. Rewrite `he` using `[integral_complex_ofReal]`. Establish `h2 : ((∫ g : Formalism.REAL.UJ ε, ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ)`. Rewrite using `[he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`.

Use `push_cast`. Both sides reduce to the same expression. Conclude with `h2` after adjusting the coercions.
-/
theorem schur_abs {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) (x y : H) :
    Integrable (fun g : Formalism.REAL.UJ ε => ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2) (Formalism.REAL.muG ε) ∧
      ∫ g : Formalism.REAL.UJ ε, ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 ∂(Formalism.REAL.muG ε) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by
  obtain ⟨hi, he⟩ := hd.2 x y x y
  have hfun : (fun g : Formalism.REAL.UJ ε => coefOn σ x y g * star (coefOn σ x y g)) =
      fun g : Formalism.REAL.UJ ε => ((‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    exact mul_star_eq _
  rw [hfun] at hi he
  refine ⟨?_, ?_⟩
  · exact hi.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _)
  · rw [integral_complex_ofReal] at he
    have h2 : ((∫ g : Formalism.REAL.UJ ε, ‖⟪y, σ (umat g) x⟫_ℂ‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) =
        ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
      rw [he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    exact_mod_cast h2

/- English proof (translation)
Unfold `fdegOf`. Establish `h` using `(schur_abs hd w w).2`. Establish `h' : ∫ g : Formalism.REAL.UJ ε, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / d`. Establish `: (fun g : Formalism.REAL.UJ ε => ‖coefOn σ w w g‖ ^ 2) = fun g : Formalism.REAL.UJ ε => ‖⟪w, σ (umat g) w⟫_ℂ‖ ^ 2` using `rfl`. Rewrite using `[this, h, hw]`.

Evaluate the numerical expressions. Rewrite using `[h', hw]`. Use `hd.1` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem fdegOf_eq {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) {w : H} (hw : ‖w‖ = 1) : fdegOf (Formalism.REAL.muG ε) σ w = d := by
  unfold fdegOf
  have h := (schur_abs hd w w).2
  have h' : ∫ g : Formalism.REAL.UJ ε, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / d := by
    have : (fun g : Formalism.REAL.UJ ε => ‖coefOn σ w w g‖ ^ 2) = fun g : Formalism.REAL.UJ ε => ‖⟪w, σ (umat g) w⟫_ℂ‖ ^ 2 := rfl
    rw [this, h, hw]
    norm_num
  rw [h', hw]
  have := hd.1
  field_simp

end Loc

/- English proof (translation)
Introduce `h1 hL1 habs n ε lam hlam H _ _ _ σ hDS w hw h hgap hh`. Take `⟨d, hd⟩` from `h1 n ε lam hlam H σ hDS`. Establish `hU : IsURepOn (UJset ε) σ` using `hDS.2.2.1`. Establish `hint : Integrable (phLoc ε σ w) (Formalism.REAL.muG ε)` using `hL1 n ε lam hlam H σ hDS w hw h hgap hh`. Establish `hdeg : fdegOf (Formalism.REAL.muG ε) σ w = d` using `fdegOf_eq hd hw.1`.

Establish `hph : phLoc ε σ w = phA d (homOf σ hU) w`. Use function extensionality and compare the values at `g`. Unfold `phLoc phA`. Rewrite using `[hdeg]`. Both sides reduce to the same expression.

Establish `: (Formalism.REAL.muG ε).IsMulRightInvariant` using `⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩`. Establish `hcoef : Integrable (fun g => ⟪w, homOf σ hU g w⟫_ℂ) (Formalism.REAL.muG ε)`. Establish `h2 : Integrable (fun g => ((d : ℂ)⁻¹) * phLoc ε σ w g) (Formalism.REAL.muG ε)` using `hint.const_mul _`. Establish `h3` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h2`. Use `h3.congr (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Establish `hd0 : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.1.ne'`. Simplify using `only [phLoc, hdeg]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hd0, one_mul]`. Simplify using `[coefOn, homOf_apply]`. Take `⟨c1, c2, c3⟩` from `habs (Formalism.REAL.UJ ε) (Formalism.REAL.muG ε) H (homOf σ hU) (homOf_norm σ hU) (homOf_cont σ hU) d hd.1 (fun x y => schur_abs hd x y) w hw.1 hcoef`.

Use `⟨hint, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Rewrite using `[hph]`. Conclude with `c1 g`. Introduce `x y`.

Rewrite using `[hph]`. Conclude with `c2 x y`. Introduce `Hp _ _ _ π hπ`. Rewrite using `[hph]`. Conclude with `c3 Hp (homOf π hπ) (homOf_norm π hπ) (homOf_cont π hπ)`.
-/
theorem projector_section_local (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaceDegreeData.LocalProjectorFromSchur D := by
  intro h1 hL1 habs n ε lam hlam H _ _ _ σ hDS w hw h hgap hh
  obtain ⟨d, hd⟩ := h1 n ε lam hlam H σ hDS
  have hU : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hint : Integrable (phLoc ε σ w) (Formalism.REAL.muG ε) := hL1 n ε lam hlam H σ hDS w hw h hgap hh
  have hdeg : fdegOf (Formalism.REAL.muG ε) σ w = d := fdegOf_eq hd hw.1
  have hph : phLoc ε σ w = phA d (homOf σ hU) w := by
    funext g
    unfold phLoc phA
    rw [hdeg]
    rfl
  have : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hcoef : Integrable (fun g => ⟪w, homOf σ hU g w⟫_ℂ) (Formalism.REAL.muG ε) := by
    have h2 : Integrable (fun g => ((d : ℂ)⁻¹) * phLoc ε σ w g) (Formalism.REAL.muG ε) := hint.const_mul _
    have h3 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h2
    refine h3.congr (Filter.Eventually.of_forall fun g => ?_)
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
    simp only [phLoc, hdeg]
    rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    simp [coefOn, homOf_apply]
  obtain ⟨c1, c2, c3⟩ := habs (Formalism.REAL.UJ ε) (Formalism.REAL.muG ε) H (homOf σ hU) (homOf_norm σ hU) (homOf_cont σ hU) d hd.1
    (fun x y => schur_abs hd x y) w hw.1 hcoef
  refine ⟨hint, ?_, ?_, ?_⟩
  · intro g
    rw [hph]
    exact c1 g
  · intro x y
    rw [hph]
    exact c2 x y
  · intro Hp _ _ _ π hπ
    rw [hph]
    exact c3 Hp (homOf π hπ) (homOf_norm π hπ) (homOf_cont π hπ)

/- English proof (translation)
Introduce `h1 h2 h3 x i` and use `projector_section_local (Fm.D x i) (h1 x i) (h2 x i) (h3 x i)`.
-/
theorem family_projector_section_local {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.PlaceDegreeData.FamilyLocalProjectorOfAbstractProjector Fm :=
  fun h1 h2 h3 x i => projector_section_local (Fm.D x i) (h1 x i) (h2 x i) (h3 x i)

end Formalism.MainNotions.BridgeLemma

end
