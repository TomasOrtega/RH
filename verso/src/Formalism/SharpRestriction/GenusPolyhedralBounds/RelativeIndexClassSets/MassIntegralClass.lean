import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralStmt
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

noncomputable section

open NumberField

namespace Formalism.MainNotions.Gaps.MI

open Formalism.MainNotions.Inhab Formalism.BasicNotions Formalism.MainNotions.StandardLattice

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stdForm_apply' (n : ℕ) (x y : Fin n → K) :
    stdForm K n x y = ∑ i, star (x i) * y i := rfl

/- English proof (translation)
Use `first`. Consider the case `(intro x y`. Simplify using `only [stdForm_apply', map_sum, starRingEnd_apply, star_mul', star_star]`. Conclude with `Finset.sum_congr rfl (fun i _ => mul_comm _ _))`. Consider the case `(refine ⟨fun x y => ?_⟩`.

Simplify using `only [stdForm_apply', map_sum, starRingEnd_apply, star_mul', star_star]`. Conclude with `Finset.sum_congr rfl (fun i _ => mul_comm _ _))`.
-/
theorem stdForm_isSymm (n : ℕ) : (stdForm K n).IsSymm := by
  first
    | (intro x y
       simp only [stdForm_apply', map_sum, starRingEnd_apply, star_mul', star_star]
       exact Finset.sum_congr rfl (fun i _ => mul_comm _ _))
    | (refine ⟨fun x y => ?_⟩
       simp only [stdForm_apply', map_sum, starRingEnd_apply, star_mul', star_star]
       exact Finset.sum_congr rfl (fun i _ => mul_comm _ _))

/- English proof (translation)
The claim follows from `Submodule.fg_span (Set.finite_range _) span_eq_top := by rw [stdLat, Submodule.span_span_of_tower] have h : (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = Pi.basisFun K (Fin n) := by funext i simp [Pi.basisFun_apply] rw [h] exact (Pi.basisFun K (Fin n)).span_eq`.
-/
theorem stdLat_isLattice' (n : ℕ) : Submodule.IsLattice K (stdLat K n) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [stdLat, Submodule.span_span_of_tower]
    have h : (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = Pi.basisFun K (Fin n) := by
      funext i
      simp [Pi.basisFun_apply]
    rw [h]
    exact (Pi.basisFun K (Fin n)).span_eq

variable (hc : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))

include hc in
/- English proof (translation)
Establish `hsum : (algebraMap ℚ ℂ) (Algebra.trace ℚ K (star a * a)) = ((∑ σ : K →ₐ[ℚ] ℂ, Complex.normSq (σ a) : ℝ) : ℂ)`. Rewrite using `[trace_eq_sum_embeddings (E := ℂ), Complex.ofReal_sum]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Establish `h1 : σ (star a) = starRingEnd ℂ (σ a)` using `hc σ.toRingHom a`. Rewrite using `[map_mul, h1, Complex.normSq_eq_conj_mul_self]`.

Establish `hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, Complex.normSq (σ a)`. Establish `σ0 : K →ₐ[ℚ] ℂ` using `IsAlgClosed.lift`. Use `Finset.sum_pos' (fun σ _ => Complex.normSq_nonneg _) ⟨σ0, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Conclude with `Complex.normSq_pos.mpr ((map_ne_zero σ0).mpr ha)`. Establish `hq : ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, Complex.normSq (σ a)`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← hsum]`. Simplify using the standard rewrite rules. Establish `h2 : (0 : ℝ) < ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ)`. Rewrite using `[hq]`.

Conclude with `hpos`. Conclude with `h2` after adjusting the coercions.
-/
theorem trace_star_mul_pos (a : K) (ha : a ≠ 0) : 0 < Algebra.trace ℚ K (star a * a) := by
  classical
  have hsum : (algebraMap ℚ ℂ) (Algebra.trace ℚ K (star a * a)) =
      ((∑ σ : K →ₐ[ℚ] ℂ, Complex.normSq (σ a) : ℝ) : ℂ) := by
    rw [trace_eq_sum_embeddings (E := ℂ), Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have h1 : σ (star a) = starRingEnd ℂ (σ a) := hc σ.toRingHom a
    rw [map_mul, h1, Complex.normSq_eq_conj_mul_self]
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, Complex.normSq (σ a) := by
    have σ0 : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
    refine Finset.sum_pos' (fun σ _ => Complex.normSq_nonneg _) ⟨σ0, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.mpr ((map_ne_zero σ0).mpr ha)
  have hq : ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ) =
      ∑ σ : K →ₐ[ℚ] ℂ, Complex.normSq (σ a) := by
    apply Complex.ofReal_injective
    rw [← hsum]
    simp
  have h2 : (0 : ℝ) < ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ) := by
    rw [hq]
    exact hpos
  exact_mod_cast h2

include hc in
/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Conclude with `le_of_lt (trace_star_mul_pos K hc a ha)`.
-/
theorem trace_star_mul_nonneg (a : K) : 0 ≤ Algebra.trace ℚ K (star a * a) := by
  by_cases ha : a = 0
  · subst ha
    simp
  · exact le_of_lt (trace_star_mul_pos K hc a ha)

include hc in
/- English proof (translation)
Rewrite using `[stdForm_apply', map_sum]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx (funext h)`.

Conclude with `Finset.sum_pos' (fun j _ => trace_star_mul_nonneg K hc (x j)) ⟨i, Finset.mem_univ _, trace_star_mul_pos K hc (x i) hi⟩`.
-/
theorem stdForm_def (n : ℕ) (x : Fin n → K) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (stdForm K n x x) := by
  rw [stdForm_apply', map_sum]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  exact Finset.sum_pos' (fun j _ => trace_star_mul_nonneg K hc (x j))
    ⟨i, Finset.mem_univ _, trace_star_mul_pos K hc (x i) hi⟩

include hc in
/- English proof (translation)
Establish `hS` using `stdForm_isSymm K n`. Establish `hD : ∀ x : Fin n → K, x ≠ 0 → 0 < Algebra.trace ℚ K (stdForm K n x x)` using `stdForm_def K hc n`. Establish `hL` using `stdLat_isLattice' K n`. Take `⟨h1, h2, h3⟩` from `Formalism.HermitianLatticesTheory.massBasic K (Fin n → K) (stdForm K n) hS hD (stdLat K n) hL`. Take `⟨-, h4, -⟩` from `Formalism.ThetaLiftIndependence.classRepsDefinite K (Fin n → K) (stdForm K n) hS hD (stdLat K n) hL`.

Use `⟨h1, h2, ?_, h3⟩` and prove the remaining obligations. Introduce `M hM`. Take `⟨m, hm, hw⟩` from `h4 M hM`. Unfold `Formalism.ThetaLiftIndependence.latWt at hw`. Establish `e1 : ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M) : ℕ) : ℂ) = (m : ℂ)` using `inv_injective hw`.

Establish `e2 : Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M) = m` using `by exact_mod_cast e1`. Rewrite using `[e2]`. Conclude with `hm`.
-/
theorem std_class (n : ℕ) :
    (∃ s, Formalism.ThetaLiftIndependence.IsClassReps (stdForm K n) (stdLat K n) s) ∧
    (∀ s, Formalism.ThetaLiftIndependence.IsClassReps (stdForm K n) (stdLat K n) s →
      Formalism.HermitianLatticesTheory.mass (stdForm K n) (stdLat K n) =
        ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M) : ℕ) : ℝ)⁻¹) ∧
    (∀ M ∈ Formalism.HermitianLatticesTheory.genus (stdForm K n) (stdLat K n),
      0 < Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M)) ∧
    0 < Formalism.HermitianLatticesTheory.mass (stdForm K n) (stdLat K n) := by
  have hS := stdForm_isSymm K n
  have hD : ∀ x : Fin n → K, x ≠ 0 → 0 < Algebra.trace ℚ K (stdForm K n x x) :=
    stdForm_def K hc n
  have hL := stdLat_isLattice' K n
  obtain ⟨h1, h2, h3⟩ :=
    Formalism.HermitianLatticesTheory.massBasic K (Fin n → K) (stdForm K n) hS hD (stdLat K n) hL
  obtain ⟨-, h4, -⟩ :=
    Formalism.ThetaLiftIndependence.classRepsDefinite K (Fin n → K) (stdForm K n) hS hD (stdLat K n) hL
  refine ⟨h1, h2, ?_, h3⟩
  intro M hM
  obtain ⟨m, hm, hw⟩ := h4 M hM
  unfold Formalism.ThetaLiftIndependence.latWt at hw
  have e1 : ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M) : ℕ) : ℂ) = (m : ℂ) := inv_injective hw
  have e2 : Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm K n) M) = m := by exact_mod_cast e1
  rw [e2]
  exact hm

end Std

/- English proof (translation)
Introduce `K H k`. Use `letI := H.cmStar`. Use `haveI := H.isCMField_hostE`. Conclude with `std_class H.E (fun φ a => NumberField.IsCMField.complexEmbedding_complexConj H.E φ a) k`.
-/
theorem mIClass : MIClass := by
  intro K H k
  letI := H.cmStar
  haveI := H.isCMField_hostE
  exact std_class H.E (fun φ a => NumberField.IsCMField.complexEmbedding_complexConj H.E φ a) k

end Formalism.MainNotions.Gaps.MI
