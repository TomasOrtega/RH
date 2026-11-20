import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.QuadSubfield

variable (D : D7)

/- English proof (translation)
The claim follows from `D.host.conjE_apply f y`.
-/
theorem emb_conj (f : D.host.E →+* ℂ) (y : D.host.E) :
    f (D.host.conj y) = starRingEnd ℂ (f y) := D.host.conjE_apply f y

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[emb_conj, emb_conj, Complex.conj_conj]`.
-/
theorem conj_conj (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

/- English proof (translation)
Establish `halg : IsAlgebraic ℚ D.host.sqrtMinusD` using `Algebra.IsAlgebraic.isAlgebraic _`. Establish `hx' : x ∈ Algebra.adjoin ℚ {D.host.sqrtMinusD}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]`. Conclude with `hx`. Use `clear hx`.

Establish `hs` using `D.host.sqrtMinusD_sq`. Proceed by induction on `hx' using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Conclude with `⟨0, 1, by simp [hx]⟩`.

Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨a', b', rfl⟩` from `hy`. Conclude with `⟨a + a', b + b', by push_cast; ring⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨a', b', rfl⟩` from `hy`. Use `⟨a * a' - D.host.d * b * b', a * b' + a' * b, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Take the linear combination `(b : D.host.E) * (b' : D.host.E) * hs`.
-/
theorem exists_coords {x : D.host.E} (hx : x ∈ D.host.K) :
    ∃ a b : ℚ, x = (a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD := by
  have halg : IsAlgebraic ℚ D.host.sqrtMinusD := Algebra.IsAlgebraic.isAlgebraic _
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqrtMinusD} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hx
  clear hx
  have hs := D.host.sqrtMinusD_sq
  induction hx' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    refine ⟨a * a' - D.host.d * b * b', a * b' + a' * b, ?_⟩
    push_cast
    linear_combination (b : D.host.E) * (b' : D.host.E) * hs

/- English proof (translation)
Rewrite using `[map_add, map_mul, map_ratCast, map_ratCast, D.host.conj_sqrtMinusD]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_coords (a b : ℚ) :
    D.host.conj ((a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD) =
      (a : D.host.E) - (b : D.host.E) * D.host.sqrtMinusD := by
  rw [map_add, map_mul, map_ratCast, map_ratCast, D.host.conj_sqrtMinusD]
  ring

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `exists_coords D hx`. Rewrite using `[conj_coords]`. Conclude with `sub_mem (SubfieldClass.ratCast_mem _ a) (mul_mem (SubfieldClass.ratCast_mem _ b) (Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D))`.
-/
theorem conj_mem {x : D.host.E} (hx : x ∈ D.host.K) : D.host.conj x ∈ D.host.K := by
  obtain ⟨a, b, rfl⟩ := exists_coords D hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem _ a)
    (mul_mem (SubfieldClass.ratCast_mem _ b) (Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D))

def conjK : D.host.K →+* D.host.K :=
  RingHom.codRestrict ((D.host.conj : D.host.E →+* D.host.E).comp D.host.K.val.toRingHom)
    D.host.K (fun x => conj_mem D x.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conjK (x : D.host.K) : ((conjK D x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := rfl

/- English proof (translation)
Establish `: IsGalois ℚ D.host.E` using `D.host.hostE_isGalois`. Conclude with `IsGalois.tower_top_of_isGalois ℚ _ _`.
-/
theorem isGalois_over : IsGalois D.host.K D.host.E := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  exact IsGalois.tower_top_of_isGalois ℚ _ _

/- English proof (translation)
Use `isGalois_over D` as an intermediate fact. Conclude with `trace_eq_sum_automorphisms (K := D.host.K) y`.
-/
theorem coe_trace (y : D.host.E) :
    ((Algebra.trace D.host.K D.host.E y : D.host.K) : D.host.E) =
      ∑ τ : D.host.E ≃ₐ[D.host.K] D.host.E, τ y := by
  have := isGalois_over D
  exact trace_eq_sum_automorphisms (K := D.host.K) y

/- English proof (translation)
Establish `h : D.host.conj * τ.restrictScalars ℚ = τ.restrictScalars ℚ * D.host.conj` using `D.host.gal.injective (by rw [map_mul, map_mul, mul_comm])`. Conclude with `AlgEquiv.congr_fun h y`.
-/
theorem conj_comm (τ : D.host.E ≃ₐ[D.host.K] D.host.E) (y : D.host.E) :
    D.host.conj (τ y) = τ (D.host.conj y) := by
  have h : D.host.conj * τ.restrictScalars ℚ = τ.restrictScalars ℚ * D.host.conj :=
    D.host.gal.injective (by rw [map_mul, map_mul, mul_comm])
  exact AlgEquiv.congr_fun h y

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_conjK, coe_trace, coe_trace, map_sum]`. Conclude with `Finset.sum_congr rfl fun τ _ => (conj_comm D τ y).symm`.
-/
theorem trace_conj (y : D.host.E) :
    Algebra.trace D.host.K D.host.E (D.host.conj y) =
      conjK D (Algebra.trace D.host.K D.host.E y) := by
  apply Subtype.ext
  rw [coe_conjK, coe_trace, coe_trace, map_sum]
  exact Finset.sum_congr rfl fun τ _ => (conj_comm D τ y).symm

/- English proof (translation)
Take `⟨a, b, hab⟩` from `exists_coords D (Algebra.trace D.host.K D.host.E (y * D.host.conj y)).2`. Establish `hfix : D.host.conj ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E) = ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E)`. Rewrite using `[← coe_conjK, ← trace_conj, map_mul, conj_conj, mul_comm]`. Rewrite `hfix` using `[hab, conj_coords]`. Establish `hb : (b : D.host.E) * D.host.sqrtMinusD = 0` using `by linear_combination (-1 / 2 : D.host.E) * hfix`.

Rewrite `hab` using `[hb, add_zero]`. Use `⟨a, ?_, Subtype.ext (by rw [hab]; simp)⟩` and prove the remaining obligations. Establish `h1` using `congrArg D.host.φ₀ hab`. Rewrite `h1` using `[coe_trace, map_sum, map_ratCast]`. Establish `h2 : ∀ τ : D.host.E ≃ₐ[D.host.K] D.host.E, D.host.φ₀ (τ (y * D.host.conj y)) = ((Complex.normSq (D.host.φ₀ (τ y)) : ℝ) : ℂ)`.

Introduce `τ`. Rewrite using `[map_mul, ← conj_comm, map_mul, emb_conj, Complex.mul_conj]`. Simplify using `only [h2] at h1`. Establish `h3 : ∑ τ : D.host.E ≃ₐ[D.host.K] D.host.E, Complex.normSq (D.host.φ₀ (τ y)) = (a : ℝ)`. Conclude with `h1` after adjusting the coercions.

Establish `h4 : (0 : ℝ) < a`. Rewrite using `[← h3]`. Use `Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ?_) Finset.univ_nonempty` and prove the remaining obligations. Simplify using `using hy`. Conclude with `h4` after adjusting the coercions.
-/
theorem trace_pos (y : D.host.E) (hy : y ≠ 0) :
    ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  obtain ⟨a, b, hab⟩ := exists_coords D (Algebra.trace D.host.K D.host.E (y * D.host.conj y)).2
  have hfix : D.host.conj ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E)
      = ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E) := by
    rw [← coe_conjK, ← trace_conj, map_mul, conj_conj, mul_comm]
  rw [hab, conj_coords] at hfix
  have hb : (b : D.host.E) * D.host.sqrtMinusD = 0 := by linear_combination (-1 / 2 : D.host.E) * hfix
  rw [hb, add_zero] at hab
  refine ⟨a, ?_, Subtype.ext (by rw [hab]; simp)⟩
  have h1 := congrArg D.host.φ₀ hab
  rw [coe_trace, map_sum, map_ratCast] at h1
  have h2 : ∀ τ : D.host.E ≃ₐ[D.host.K] D.host.E,
      D.host.φ₀ (τ (y * D.host.conj y)) = ((Complex.normSq (D.host.φ₀ (τ y)) : ℝ) : ℂ) := by
    intro τ
    rw [map_mul, ← conj_comm, map_mul, emb_conj, Complex.mul_conj]
  simp only [h2] at h1
  have h3 : ∑ τ : D.host.E ≃ₐ[D.host.K] D.host.E, Complex.normSq (D.host.φ₀ (τ y)) = (a : ℝ) := by
    exact_mod_cast h1
  have h4 : (0 : ℝ) < a := by
    rw [← h3]
    refine Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ?_) Finset.univ_nonempty
    simpa using hy
  exact_mod_cast h4

/- English proof (translation)
Establish `h` using `Module.finrank_mul_finrank ℚ D.host.K D.host.E`. Rewrite `h` using `[Formalism.L2.Pj.LPb.finrank_K, D.host.finrank_cmField]`. Use `show _ = 2 * D.R.ord`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_over : Module.finrank D.host.K D.host.E = fF D := by
  have h := Module.finrank_mul_finrank ℚ D.host.K D.host.E
  rw [Formalism.L2.Pj.LPb.finrank_K, D.host.finrank_cmField] at h
  show _ = 2 * D.R.ord
  omega

/- English proof (translation)
Introduce `D`. Use `⟨finrank_over D, conjK D, ⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, coe_conjK D, ?_, ?_, ?_, ?_, conj_conj D, trace_conj D, trace_pos D⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using D.host.sqrtMinusD_sq`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[coe_conjK]`. Conclude with `D.host.conj_sqrtMinusD`. Introduce `x`. Take `⟨a, b, h⟩` from `exists_coords D x.2`. Conclude with `⟨a, b, Subtype.ext (by simpa using h)⟩`.

Establish `h` using `(Formalism.L2.Pj.LPb.w0K D).2`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `first | rfl | (apply Subtype.ext; simp [Formalism.L2.Pj.LPb.w0K])`.
-/
theorem quadratic_subfield : ∀ D : D7, Module.finrank D.host.K D.host.E = fF D ∧ ∃ (σ : D.host.K →+* D.host.K) (θ : D.host.K), (∀ x : D.host.K, ((σ x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)) ∧ θ ^ 2 = -(D.host.d : D.host.K) ∧ σ θ = -θ ∧ (∀ x : D.host.K, ∃ a b : ℚ, x = (a : D.host.K) + (b : D.host.K) * θ) ∧ IsIntegral ℤ ((1 + θ) / 2) ∧ (∀ y : D.host.E, D.host.conj (D.host.conj y) = y) ∧ (∀ y : D.host.E, Algebra.trace D.host.K D.host.E (D.host.conj y) = σ (Algebra.trace D.host.K D.host.E y)) ∧ ∀ y : D.host.E, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  intro D
  refine ⟨finrank_over D, conjK D, ⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩,
    coe_conjK D, ?_, ?_, ?_, ?_, conj_conj D, trace_conj D, trace_pos D⟩
  · apply Subtype.ext
    simpa using D.host.sqrtMinusD_sq
  · apply Subtype.ext
    rw [coe_conjK]
    exact D.host.conj_sqrtMinusD
  · intro x
    obtain ⟨a, b, h⟩ := exists_coords D x.2
    exact ⟨a, b, Subtype.ext (by simpa using h)⟩
  · have h := (Formalism.L2.Pj.LPb.w0K D).2
    convert h using 1
    first | rfl | (apply Subtype.ext; simp [Formalism.L2.Pj.LPb.w0K])

end GlobalTheory.QuadSubfield
