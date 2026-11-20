import Mathlib
import Formalism.HermitianLattices.StatementMass
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MassTelescopeAux

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def massTelescope_form (n : ℕ) : (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => ∑ i, star (x i) * y i)
    (by intro m₁ m₂ y; simp [star_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c m y
      simp only [Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum, starRingEnd_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
    (by intro m y₁ y₂; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro c m y
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)

def massTelescope_lat (n : ℕ) : Submodule (RingOfIntegers K) (Fin n → K) :=
  Submodule.span (RingOfIntegers K) (Set.range (Pi.basisFun K (Fin n)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma massTelescope_form_apply (n : ℕ) (x y : Fin n → K) :
    massTelescope_form K n x y = ∑ i, star (x i) * y i := rfl

/- English proof (translation)
Establish `key : ∀ x y : Fin n → K, starRingEnd K (massTelescope_form K n x y) = massTelescope_form K n y x`. Introduce `x y`. Simplify using `only [massTelescope_form_apply, map_sum, starRingEnd_apply, star_mul, star_star]`. Use `first`. Consider the case `exact key`.

Consider the case `exact ⟨key⟩`.
-/
lemma massTelescope_symm (n : ℕ) : (massTelescope_form K n).IsSymm := by
  have key : ∀ x y : Fin n → K,
      starRingEnd K (massTelescope_form K n x y) = massTelescope_form K n y x := by
    intro x y
    simp only [massTelescope_form_apply, map_sum, starRingEnd_apply, star_mul, star_star]
  first
  | exact key
  | exact ⟨key⟩

/- English proof (translation)
Unfold `IsOrthoLattice`. Use `⟨⇑(Pi.basisFun K (Fin n)), (Pi.basisFun K (Fin n)).linearIndependent, (Pi.basisFun K (Fin n)).span_eq, rfl, ?_⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[massTelescope_form_apply]`. Simplify using `only [Pi.basisFun_apply]`.

Rewrite using `[Finset.sum_eq_single i]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, Pi.single_eq_of_ne hij]`.

Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.
-/
lemma massTelescope_ortho (n : ℕ) :
    IsOrthoLattice (massTelescope_form K n) (massTelescope_lat K n) n := by
  unfold IsOrthoLattice
  refine ⟨⇑(Pi.basisFun K (Fin n)), (Pi.basisFun K (Fin n)).linearIndependent,
    (Pi.basisFun K (Fin n)).span_eq, rfl, ?_⟩
  intro i j
  rw [massTelescope_form_apply]
  simp only [Pi.basisFun_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Pi.single_eq_of_ne hij]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/- English proof (translation)
The claim follows from `Submodule.fg_span (Set.finite_range _) span_eq_top := by rw [massTelescope_lat, Submodule.span_span_of_tower] exact (Pi.basisFun K (Fin n)).span_eq`.
-/
lemma massTelescope_isLattice (n : ℕ) : Submodule.IsLattice K (massTelescope_lat K n) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [massTelescope_lat, Submodule.span_span_of_tower]
    exact (Pi.basisFun K (Fin n)).span_eq

/- English proof (translation)
Use `haveI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩`. Establish `key : ∀ σ : K →ₐ[ℚ] ℂ, σ (star a * a) = ((Complex.normSq (σ a) : ℝ) : ℂ)`. Introduce `σ`. Establish `h1 : σ (star a) = starRingEnd ℂ (σ a)` using `hCM.2.1 (σ : K →+* ℂ) a`. Rewrite using `[map_mul, h1]`.

Conclude with `Complex.normSq_eq_conj_mul_self.symm`. Establish `hE : algebraMap ℚ ℂ (Algebra.trace ℚ K (star a * a)) = ∑ σ : K →ₐ[ℚ] ℂ, σ (star a * a)` using `by first`. Consider the case `exact trace_eq_sum_embeddings ℂ`. Consider the case `exact trace_eq_sum_embeddings (E := ℂ)`. Consider the case `exact Algebra.trace_eq_sum_embeddings ℂ`.

Simplify using `only [key] at hE`. Rewrite `hE` using `[eq_ratCast (algebraMap ℚ ℂ)]`. Establish `hR` using `congrArg Complex.re hE`. Simplify using `only [Complex.ratCast_re, Complex.re_sum, Complex.ofReal_re] at hR`. Establish `hpos : (0 : ℝ) < ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ)`.

Rewrite using `[hR]`. Conclude with `Finset.sum_pos (fun σ _ => Complex.normSq_pos.mpr ((map_ne_zero σ).mpr ha)) Finset.univ_nonempty`. Conclude with `hpos` after adjusting the coercions.
-/
lemma massTelescope_trace_pos (hCM : IsCMUnram K) (a : K) (ha : a ≠ 0) :
    0 < Algebra.trace ℚ K (star a * a) := by
  haveI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have key : ∀ σ : K →ₐ[ℚ] ℂ, σ (star a * a) = ((Complex.normSq (σ a) : ℝ) : ℂ) := by
    intro σ
    have h1 : σ (star a) = starRingEnd ℂ (σ a) := hCM.2.1 (σ : K →+* ℂ) a
    rw [map_mul, h1]
    exact Complex.normSq_eq_conj_mul_self.symm
  have hE : algebraMap ℚ ℂ (Algebra.trace ℚ K (star a * a)) =
      ∑ σ : K →ₐ[ℚ] ℂ, σ (star a * a) := by
    first
    | exact trace_eq_sum_embeddings ℂ
    | exact trace_eq_sum_embeddings (E := ℂ)
    | exact Algebra.trace_eq_sum_embeddings ℂ
  simp only [key] at hE
  rw [eq_ratCast (algebraMap ℚ ℂ)] at hE
  have hR := congrArg Complex.re hE
  simp only [Complex.ratCast_re, Complex.re_sum, Complex.ofReal_re] at hR
  have hpos : (0 : ℝ) < ((Algebra.trace ℚ K (star a * a) : ℚ) : ℝ) := by
    rw [hR]
    exact Finset.sum_pos (fun σ _ => Complex.normSq_pos.mpr ((map_ne_zero σ).mpr ha))
      Finset.univ_nonempty
  exact_mod_cast hpos

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Conclude with `le_of_lt (massTelescope_trace_pos K hCM a ha)`.
-/
lemma massTelescope_trace_nonneg (hCM : IsCMUnram K) (a : K) :
    0 ≤ Algebra.trace ℚ K (star a * a) := by
  by_cases ha : a = 0
  · subst ha
    simp
  · exact le_of_lt (massTelescope_trace_pos K hCM a ha)

/- English proof (translation)
Rewrite using `[massTelescope_form_apply, map_sum]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hx (funext hc)`.

Conclude with `Finset.sum_pos' (fun j _ => massTelescope_trace_nonneg K hCM (x j)) ⟨i, Finset.mem_univ _, massTelescope_trace_pos K hCM (x i) hi⟩`.
-/
lemma massTelescope_def (hCM : IsCMUnram K) (n : ℕ) (x : Fin n → K) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (massTelescope_form K n x x) := by
  rw [massTelescope_form_apply, map_sum]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  exact Finset.sum_pos' (fun j _ => massTelescope_trace_nonneg K hCM (x j))
    ⟨i, Finset.mem_univ _, massTelescope_trace_pos K hCM (x i) hi⟩

/- English proof (translation)
Conclude with `(massBasic K (Fin n → K) (massTelescope_form K n) (massTelescope_symm K n) (fun x hx => massTelescope_def K hCM n x hx) (massTelescope_lat K n) (massTelescope_isLattice K n)).2.2`.
-/
lemma massTelescope_std_pos (hCM : IsCMUnram K) (n : ℕ) :
    0 < mass (massTelescope_form K n) (massTelescope_lat K n) := by
  exact (massBasic K (Fin n → K) (massTelescope_form K n) (massTelescope_symm K n)
    (fun x hx => massTelescope_def K hCM n x hx) (massTelescope_lat K n)
    (massTelescope_isLattice K n)).2.2

/- English proof (translation)
Establish `h` using `hS K hCM (r + 1) (by omega) (Fin (r + 1) → K) (Fin r → K) (massTelescope_form K (r + 1)) (massTelescope_form K r) (massTelescope_lat K (r + 1)) (massTelescope_lat K r) (massTelescope_symm K (r + 1)) (massTelescope_symm K r) (massTelescope_ortho K (r + 1)) (by simpa using massTele …`. Establish `hp` using `massTelescope_std_pos K hCM r`. Rewrite using `[← h]`. Clear the denominators using the available nonvanishing facts.
-/
lemma massTelescope_step (hS : SiegelMassRatio) (hCM : IsCMUnram K) (r : ℕ) (hr : 2 ≤ r) :
    mass (massTelescope_form K (r + 1)) (massTelescope_lat K (r + 1)) =
      mass (massTelescope_form K r) (massTelescope_lat K r) * massRatioRightSide K (r + 1) := by
  have h := hS K hCM (r + 1) (by omega) (Fin (r + 1) → K) (Fin r → K)
    (massTelescope_form K (r + 1)) (massTelescope_form K r) (massTelescope_lat K (r + 1))
    (massTelescope_lat K r) (massTelescope_symm K (r + 1)) (massTelescope_symm K r)
    (massTelescope_ortho K (r + 1)) (by simpa using massTelescope_ortho K r)
  have hp := massTelescope_std_pos K hCM r
  rw [← h]
  field_simp

end MassTelescopeAux

end Formalism.HermitianLatticesTheory
