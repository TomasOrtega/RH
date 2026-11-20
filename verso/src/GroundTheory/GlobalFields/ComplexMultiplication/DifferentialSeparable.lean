import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.Differential

namespace GroundTheory.Global

open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

omit [E.IsElliptic] in

/- English proof (translation)
Rewrite using `[← isogenyPullback_D, ← invCoeff_smul E' (D F _ f), isogenyPullback_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span rfl)`.
-/
theorem D_comap_mem_span (φ : Isogeny E E') (f : E'.toAffine.FunctionField) :
    D F E.toAffine.FunctionField (φ.comap f) ∈
      Submodule.span E.toAffine.FunctionField {isogenyPullback φ (invariantDifferential E')} := by
  rw [← isogenyPullback_D, ← invCoeff_smul E' (D F _ f), isogenyPullback_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/- English proof (translation)
Use `set M := φ.comap.fieldRange`. Use `set K := E.toAffine.FunctionField`. Establish `: Algebra.IsSeparable M K` using `hφ`. Establish `: Algebra.FormallyUnramified M K` using `.of_isSeparable _ _`. Use `eq_top_iff.mpr fun ω hω ↦ ?_` and prove the remaining obligations.

Use `clear hω`. Take `⟨z, rfl⟩` from `(exact_mapBaseChange_map F M K ω).mp (Subsingleton.elim _ _)`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add]`.

Conclude with `add_mem ha hb`. Consider the case `tmul a b`. Rewrite using `[mapBaseChange_tmul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hb : b ∈ Submodule.span M (Set.range (D F M))`.

Rewrite using `[span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem _ h`. Take `⟨e, rfl⟩` from `h`.

Rewrite using `[map_D]`. Take `⟨f, hf⟩` from `e.2`. Express the relevant statement in the definitionally equal form `D F K (e : K) ∈ _`. Rewrite using `[← hf]`. Conclude with `D_comap_mem_span φ f`.

Consider the case `zero => simp`. Consider the case `add _ _ _ _ h₁ h₂ => rw [map_add]`. Conclude with `add_mem h₁ h₂`. Consider the case `smul c _ _ h`. Rewrite using `[map_smul, algebra_compatible_smul K c]`.

Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem span_isogenyPullback_eq_top (φ : Isogeny E E') (hφ : φ.IsSeparable) :
    Submodule.span E.toAffine.FunctionField {isogenyPullback φ (invariantDifferential E')} = ⊤ := by
  set M := φ.comap.fieldRange
  set K := E.toAffine.FunctionField
  have : Algebra.IsSeparable M K := hφ
  have : Algebra.FormallyUnramified M K := .of_isSeparable _ _
  refine eq_top_iff.mpr fun ω hω ↦ ?_
  clear hω
  obtain ⟨z, rfl⟩ := (exact_mapBaseChange_map F M K ω).mp (Subsingleton.elim _ _)
  induction z with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    rw [mapBaseChange_tmul]
    refine Submodule.smul_mem _ _ ?_
    have hb : b ∈ Submodule.span M (Set.range (D F M)) := by
      rw [span_range_derivation]; trivial
    induction hb using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨e, rfl⟩ := h
      rw [map_D]
      obtain ⟨f, hf⟩ := e.2
      change D F K (e : K) ∈ _
      rw [← hf]
      exact D_comap_mem_span φ f
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul c _ _ h =>
      rw [map_smul, algebra_compatible_smul K c]
      exact Submodule.smul_mem _ _ h

/- English proof (translation)
Introduce `h0`. Establish `htop` using `span_isogenyPullback_eq_top φ hφ`. Rewrite `htop` using `[h0, Submodule.span_singleton_eq_bot.mpr rfl]`. Establish `hmem : invariantDifferential E ∈ (⊥ : Submodule E.toAffine.FunctionField _)`. Rewrite using `[htop]`.

Discharge the goal by the elementary cases of `trivial`. Conclude with `invariantDifferential_ne_zero E ((Submodule.mem_bot _).mp hmem)`.
-/
theorem isogenyPullback_ne_zero_of_isSeparable (φ : Isogeny E E') (hφ : φ.IsSeparable) :
    isogenyPullback φ (invariantDifferential E') ≠ 0 := by
  intro h0
  have htop := span_isogenyPullback_eq_top φ hφ
  rw [h0, Submodule.span_singleton_eq_bot.mpr rfl] at htop
  have hmem : invariantDifferential E ∈ (⊥ : Submodule E.toAffine.FunctionField _) := by
    rw [htop]; trivial
  exact invariantDifferential_ne_zero E ((Submodule.mem_bot _).mp hmem)

/- English proof (translation)
Use `set M := φ.comap.fieldRange`. Use `set K := E.toAffine.FunctionField`. Establish `hc : isogCoeff φ ≠ 0`. Introduce `h`. Apply `hφ` to reduce the goal to its premises.

Rewrite using `[isogenyPullback_invariantDifferential_eq_smul, h, zero_smul]`. Establish `htop : Submodule.span K {isogenyPullback φ (invariantDifferential E')} = ⊤`. Rewrite using `[isogenyPullback_invariantDifferential_eq_smul, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]`. Conclude with `span_invariantDifferential E`. Establish `hx : φ.comap (genX E') ∈ M` using `⟨genX E', rfl⟩`.

Establish `hzero : KaehlerDifferential.map F M K K (isogenyPullback φ (invariantDifferential E')) = 0`. Rewrite using `[invariantDifferential_eq, isogenyPullback_smul, isogenyPullback_D, map_smul, map_D]`. Establish `: D M K (algebraMap K K (φ.comap (genX E'))) = D M K (algebraMap M K ⟨_, hx⟩)` using `rfl`. Rewrite using `[this, Derivation.map_algebraMap, smul_zero]`. Establish `hsub : Subsingleton Ω[K⁄M]`.

Use `subsingleton_of_forall_eq 0 fun ω' ↦ ?_` and prove the remaining obligations. Take `⟨ω, rfl⟩` from `map_surjective F M K ω'`. Establish `hω : ω ∈ Submodule.span K {isogenyPullback φ (invariantDifferential E')}`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hω`. Rewrite using `[map_smul, hzero, smul_zero]`. Establish `: Algebra.FormallyUnramified M K` using `⟨hsub⟩`. Establish `: FiniteDimensional M K` using `φ.finiteDimensional`. Establish `: Algebra.EssFiniteType M K` using `inferInstance`.

Conclude with `Algebra.FormallyUnramified.isSeparable M K`.
-/
theorem isSeparable_of_isogenyPullback_ne_zero (φ : Isogeny E E')
    (hφ : isogenyPullback φ (invariantDifferential E') ≠ 0) : φ.IsSeparable := by
  set M := φ.comap.fieldRange
  set K := E.toAffine.FunctionField
  have hc : isogCoeff φ ≠ 0 := by
    intro h; apply hφ; rw [isogenyPullback_invariantDifferential_eq_smul, h, zero_smul]
  have htop : Submodule.span K {isogenyPullback φ (invariantDifferential E')} = ⊤ := by
    rw [isogenyPullback_invariantDifferential_eq_smul,
      Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]
    exact span_invariantDifferential E
  have hx : φ.comap (genX E') ∈ M := ⟨genX E', rfl⟩
  have hzero : KaehlerDifferential.map F M K K (isogenyPullback φ (invariantDifferential E')) = 0 := by
    rw [invariantDifferential_eq, isogenyPullback_smul, isogenyPullback_D, map_smul, map_D]
    have : D M K (algebraMap K K (φ.comap (genX E'))) = D M K (algebraMap M K ⟨_, hx⟩) := rfl
    rw [this, Derivation.map_algebraMap, smul_zero]
  have hsub : Subsingleton Ω[K⁄M] := by
    refine subsingleton_of_forall_eq 0 fun ω' ↦ ?_
    obtain ⟨ω, rfl⟩ := map_surjective F M K ω'
    have hω : ω ∈ Submodule.span K {isogenyPullback φ (invariantDifferential E')} := by
      rw [htop]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hω
    rw [map_smul, hzero, smul_zero]
  have : Algebra.FormallyUnramified M K := ⟨hsub⟩
  have : FiniteDimensional M K := φ.finiteDimensional
  have : Algebra.EssFiniteType M K := inferInstance
  exact Algebra.FormallyUnramified.isSeparable M K

/- English proof (translation)
Assemble the required witnesses or components as `⟨isogenyPullback_ne_zero_of_isSeparable φ, isSeparable_of_isogenyPullback_ne_zero φ⟩`.
-/
theorem isSeparable_iff_isogenyPullback_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ isogenyPullback φ (invariantDifferential E') ≠ 0 :=
  ⟨isogenyPullback_ne_zero_of_isSeparable φ, isSeparable_of_isogenyPullback_ne_zero φ⟩

/- English proof (translation)
Rewrite using `[isSeparable_iff_isogenyPullback_ne_zero, isogenyPullback_invariantDifferential_eq_smul]`. Conclude with `⟨fun h h0 => h (by rw [h0, zero_smul]), fun h h0 => h ((smul_eq_zero.mp h0).resolve_right (invariantDifferential_ne_zero E))⟩`.
-/
theorem isSeparable_iff_isogCoeff_ne_zero (φ : Isogeny E E') :
    φ.IsSeparable ↔ isogCoeff φ ≠ 0 := by
  rw [isSeparable_iff_isogenyPullback_ne_zero, isogenyPullback_invariantDifferential_eq_smul]
  exact ⟨fun h h0 => h (by rw [h0, zero_smul]),
    fun h h0 => h ((smul_eq_zero.mp h0).resolve_right (invariantDifferential_ne_zero E))⟩

end GroundTheory.Global
