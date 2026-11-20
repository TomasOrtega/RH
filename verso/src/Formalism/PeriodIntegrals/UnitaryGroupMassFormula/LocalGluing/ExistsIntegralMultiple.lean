import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOfPair

noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Take `⟨T, hT⟩` from `SlopeTestRemainingChoices.tr_ex L y`. Take `⟨N, hN⟩` from `SlopeTestRemainingChoices.nm_ex L y`. Take `⟨r₁, h10, h1⟩` from `SlopeTestRemainingChoices.exists_scale T`. Take `⟨r₂, h20, h2⟩` from `SlopeTestRemainingChoices.exists_scale N`. Take `⟨r, hr⟩ : ∃ r : 𝒪[F], (r : F) = (r₁ : F) * (r₂ : F)` from `⟨r₁ * r₂, rfl⟩`.

Use `⟨r, by rw [hr]; exact mul_ne_zero h10 h20, ?_⟩` and prove the remaining obligations. Use `SlopeTestRemainingChoices.mem_O_of_quad L _ ⟨(r : F) * T, ?_⟩ ⟨(r : F) * (r : F) * N, ?_⟩ ?_` and prove the remaining obligations. Establish `: (r : F) * T = (r₂ : F) * ((r₁ : F) * T)` using `by rw [hr]; ring`. Rewrite using `[this]`. Conclude with `(𝒪[F]).mul_mem r₂.2 h1`.

Establish `: (r : F) * (r : F) * N = ((r₁ : F) * (r₁ : F) * (r₂ : F)) * ((r₂ : F) * N)`. Rewrite using `[hr]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(𝒪[F]).mul_mem ((𝒪[F]).mul_mem ((𝒪[F]).mul_mem r₁.2 r₁.2) r₂.2) h2`.

Simplify using `only [map_mul, hT, hN]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scale_E (L : LocE F E) (y : E) :
    ∃ r : 𝒪[F], (r : F) ≠ 0 ∧ algebraMap F E r * y ∈ L.O := by
  obtain ⟨T, hT⟩ := SlopeTestRemainingChoices.tr_ex L y
  obtain ⟨N, hN⟩ := SlopeTestRemainingChoices.nm_ex L y
  obtain ⟨r₁, h10, h1⟩ := SlopeTestRemainingChoices.exists_scale T
  obtain ⟨r₂, h20, h2⟩ := SlopeTestRemainingChoices.exists_scale N
  obtain ⟨r, hr⟩ : ∃ r : 𝒪[F], (r : F) = (r₁ : F) * (r₂ : F) := ⟨r₁ * r₂, rfl⟩
  refine ⟨r, by rw [hr]; exact mul_ne_zero h10 h20, ?_⟩
  refine SlopeTestRemainingChoices.mem_O_of_quad L _ ⟨(r : F) * T, ?_⟩ ⟨(r : F) * (r : F) * N, ?_⟩ ?_
  · have : (r : F) * T = (r₂ : F) * ((r₁ : F) * T) := by rw [hr]; ring
    rw [this]; exact (𝒪[F]).mul_mem r₂.2 h1
  · have : (r : F) * (r : F) * N = ((r₁ : F) * (r₁ : F) * (r₂ : F)) * ((r₂ : F) * N) := by
      rw [hr]; ring
    rw [this]; exact (𝒪[F]).mul_mem ((𝒪[F]).mul_mem ((𝒪[F]).mul_mem r₁.2 r₁.2) r₂.2) h2
  · simp only [map_mul, hT, hN]
    ring

end

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M _ V _ _ S w hw`. Establish `key : ∀ (r : 𝒪[F]) (v : V), v ∈ S → algebraMap F E r • v ∈ S`. Introduce `r v hv`. Establish `: (⟨algebraMap F E r, SlopeTestRemainingChoices.algebraMap_mem_O M.L r⟩ : M.L.O) • v ∈ S` using `S.smul_mem _ hv`. Conclude with `this`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, by simp, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, by simp, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨r, hr0, hr⟩` from `hx`.

Take `⟨s, hs0, hs⟩` from `hy`. Take `⟨t, ht⟩ : ∃ t : 𝒪[F], (t : F) = (r : F) * (s : F)` from `⟨r * s, rfl⟩`. Use `⟨t, by rw [ht]; exact mul_ne_zero hr0 hs0, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap F E t • (x + y) = algebraMap F E s • (algebraMap F E r • x) + algebraMap F E r • (algebraMap F E s • y)`. Rewrite using `[ht, smul_add, smul_smul, smul_smul, map_mul, mul_comm (algebraMap F E s)]`.

Rewrite using `[e]`. Conclude with `S.add_mem (key s _ hr) (key r _ hs)`. Consider the case `smul a x _ hx`. Take `⟨r, hr0, hr⟩` from `hx`. Take `⟨s, hs0, hs⟩` from `scale_E M.L a`.

Take `⟨t, ht⟩ : ∃ t : 𝒪[F], (t : F) = (s : F) * (r : F)` from `⟨s * r, rfl⟩`. Use `⟨t, by rw [ht]; exact mul_ne_zero hs0 hr0, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap F E t • (a • x) = (⟨algebraMap F E s * a, hs⟩ : M.L.O) • (algebraMap F E r • x)`. Express the relevant statement in the definitionally equal form `_ = (algebraMap F E s * a) • (algebraMap F E r • x)`. Rewrite using `[ht, smul_smul, smul_smul, map_mul]`.

Put the polynomial expressions in normal form. Rewrite using `[e]`. Conclude with `S.smul_mem _ hr`.
-/
theorem existsIntegralMultiple : Scale := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ S w hw
  have key : ∀ (r : 𝒪[F]) (v : V), v ∈ S → algebraMap F E r • v ∈ S := by
    intro r v hv
    have : (⟨algebraMap F E r, SlopeTestRemainingChoices.algebraMap_mem_O M.L r⟩ : M.L.O) • v ∈ S := S.smul_mem _ hv
    exact this
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, by simp, by simpa using hx⟩
  | zero => exact ⟨1, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr0, hr⟩ := hx
    obtain ⟨s, hs0, hs⟩ := hy
    obtain ⟨t, ht⟩ : ∃ t : 𝒪[F], (t : F) = (r : F) * (s : F) := ⟨r * s, rfl⟩
    refine ⟨t, by rw [ht]; exact mul_ne_zero hr0 hs0, ?_⟩
    have e : algebraMap F E t • (x + y) =
        algebraMap F E s • (algebraMap F E r • x) + algebraMap F E r • (algebraMap F E s • y) := by
      rw [ht, smul_add, smul_smul, smul_smul, map_mul, mul_comm (algebraMap F E s)]
    rw [e]
    exact S.add_mem (key s _ hr) (key r _ hs)
  | smul a x _ hx =>
    obtain ⟨r, hr0, hr⟩ := hx
    obtain ⟨s, hs0, hs⟩ := scale_E M.L a
    obtain ⟨t, ht⟩ : ∃ t : 𝒪[F], (t : F) = (s : F) * (r : F) := ⟨s * r, rfl⟩
    refine ⟨t, by rw [ht]; exact mul_ne_zero hs0 hr0, ?_⟩
    have e : algebraMap F E t • (a • x) =
        (⟨algebraMap F E s * a, hs⟩ : M.L.O) • (algebraMap F E r • x) := by
      change _ = (algebraMap F E s * a) • (algebraMap F E r • x)
      rw [ht, smul_smul, smul_smul, map_mul]
      ring_nf
    rw [e]
    exact S.smul_mem _ hr

end PI.LocHerm.Glue
