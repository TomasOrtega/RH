import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.FrameDual

section Det

variable {A : Type} [CommRing A]

end Det

section Ideals

variable {E : Type} [Field E] [NumberField E]

def Stab (σ : E →+* E) (I : FractionalIdeal (𝓞 E)⁰ E) : Prop := ∀ x ∈ I, σ x ∈ I

/- English proof (translation)
Introduce `x hx`. Take `⟨d, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hx`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨RingOfIntegers.mapRingHom σ d, rfl⟩`.
-/
theorem stab_one (σ : E →+* E) : Stab σ 1 := by
  intro x hx
  obtain ⟨d, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  exact (FractionalIdeal.mem_one_iff _).2 ⟨RingOfIntegers.mapRingHom σ d, rfl⟩

/- English proof (translation)
Introduce `x hx`. Use `FractionalIdeal.mul_induction_on hx (fun i hi j hj => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `FractionalIdeal.mul_mem_mul (hI i hi) (hJ j hj)`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem (I * J).coeToSubmodule ha hb`.
-/
theorem Stab.mul {σ : E →+* E} {I J : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (hJ : Stab σ J) :
    Stab σ (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun i hi j hj => ?_) (fun a b ha hb => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hI i hi) (hJ j hj)
  · rw [map_add]; exact Submodule.add_mem (I * J).coeToSubmodule ha hb

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using stab_one σ`. Consider the case `succ j ih => rw [pow_succ]`. Conclude with `ih.mul hI`.
-/
theorem Stab.pow {σ : E →+* E} {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (j : ℕ) :
    Stab σ (I ^ j) := by
  induction j with
  | zero => simpa using stab_one σ
  | succ j ih => rw [pow_succ]; exact ih.mul hI

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[FractionalIdeal.mem_inv_iff h0]`. Introduce `y hy`. Use `stab_one σ _ (hx _ (hI y hy))` as an intermediate fact. Rewrite `this` using `[map_mul, hσ]`. Then use the resulting hypothesis.
-/
theorem Stab.inv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I)
    (h0 : I ≠ 0) : Stab σ I⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
  intro y hy
  have := stab_one σ _ (hx _ (hI y hy))
  rwa [map_mul, hσ] at this

/- English proof (translation)
The claim follows from `FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot`.
-/
theorem diff_ne_zero : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

/- English proof (translation)
The claim follows from `pow_ne_zero _ (inv_ne_zero diff_ne_zero)`.
-/
theorem dInv_ne_zero (j : ℕ) : dInv E j ≠ 0 := pow_ne_zero _ (inv_ne_zero diff_ne_zero)

/- English proof (translation)
Use `Stab.pow ?_ j` and prove the remaining obligations. Rewrite using `[coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]`. Introduce `x hx`. Establish `h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `one_ne_zero`. Rewrite `hx`, the goal using `[FractionalIdeal.mem_dual h10]`.

Introduce `a ha`. Establish `h1` using `hx _ (stab_one σ a ha)`. Set `e : E ≃ₐ[ℚ] E` to `AlgEquiv.ofBijective σ.toRatAlgHom (Function.Involutive.bijective hσ)`. Establish `h2 : Algebra.traceForm ℚ E (σ x) a = Algebra.traceForm ℚ E x (σ a)`. Rewrite using `[Algebra.traceForm_apply, Algebra.traceForm_apply, ← Algebra.trace_eq_of_algEquiv e (x * σ a)]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = σ (x * σ a)`. Rewrite using `[map_mul, hσ]`. Rewrite using `[h2]` and apply the resulting hypothesis.
-/
theorem stab_dInv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) (j : ℕ) : Stab σ (dInv E j) := by
  refine Stab.pow ?_ j
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  intro x hx
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h10] at hx ⊢
  intro a ha
  have h1 := hx _ (stab_one σ a ha)
  let e : E ≃ₐ[ℚ] E := AlgEquiv.ofBijective σ.toRatAlgHom (Function.Involutive.bijective hσ)
  have h2 : Algebra.traceForm ℚ E (σ x) a = Algebra.traceForm ℚ E x (σ a) := by
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply, ← Algebra.trace_eq_of_algEquiv e (x * σ a)]
    congr 1
    change _ = σ (x * σ a)
    rw [map_mul, hσ]
  rwa [h2]

end Ideals

section Frame

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Simplify using `[id1]`.
-/
theorem frameDualTupleIdeals_castAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.castAdd r b.castSucc) = dInv E (r - b) := by
  simp [id1]

/- English proof (translation)
Simplify using `[id1]`.
-/
theorem frameDualTupleIdeals_natAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.natAdd (r + 1) b) = (dInv E (r - b))⁻¹ := by
  simp [id1]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

/- English proof (translation)
Establish `h0 : differentIdeal (𝓞 F) (𝓞 E) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Conclude with `not_dvd_differentIdeal_iff.2 (inferInstance : Algebra.IsUnramifiedAt (𝓞 F) P) (Ideal.dvd_iff_le.2 hle)`. Establish `h1` using `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)`.

Rewrite `h1` using `[h0, Ideal.absNorm_top, one_mul, h2]`. Then use the resulting hypothesis.
-/
theorem natAbs_discr_sq (h2 : Module.finrank F E = 2) [Algebra.FormallyUnramified (𝓞 F) (𝓞 E)] :
    (discr E).natAbs = (discr F).natAbs ^ 2 := by
  have h0 : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    exact not_dvd_differentIdeal_iff.2 (inferInstance : Algebra.IsUnramifiedAt (𝓞 F) P)
      (Ideal.dvd_iff_le.2 hle)
  have h1 := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rwa [h0, Ideal.absNorm_top, one_mul, h2] at h1

/- English proof (translation)
Rewrite using `[dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E (𝓞 E)]`. Simplify using the standard rewrite rules.
-/
theorem absNorm_dInv (j : ℕ) :
    ((FractionalIdeal.absNorm (dInv E j) : ℚ) : ℝ) = |(discr E : ℝ)|⁻¹ ^ j := by
  rw [dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E (𝓞 E)]
  simp

end Frame

end GlobalTheory.SnMass.FrameDual
