import Mathlib

open Polynomial

namespace GlobalTheory.FiniteFieldOfPoints

/- English proof (translation)
Use `choose f hf using h`. Use `⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩` and prove the remaining obligations. Apply `j.injective` to reduce the goal to its premises. Simplify using `[hf]`. Introduce `a b`.

Apply `j.injective` to reduce the goal to its premises. Simplify using `[hf]`. Apply `j.injective` to reduce the goal to its premises. Simplify using `[hf]`. Introduce `a b`.

Apply `j.injective` to reduce the goal to its premises. Simplify using `[hf]`. Use extensionality with `c`. Simplify using `[hf]`.
-/
theorem factor_of_range {C K₂ Ω : Type} [CommRing C] [Field K₂] [Field Ω]
    (j : K₂ →+* Ω) (ψ : C →+* Ω) (h : ∀ c, ∃ x, j x = ψ c) :
    ∃ ψ₀ : C →+* K₂, j.comp ψ₀ = ψ := by
  choose f hf using h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · apply j.injective; simp [hf]
  · intro a b; apply j.injective; simp [hf]
  · ext c; simp [hf]

/- English proof (translation)
Use `letI : Algebra K C := φ.toAlgebra`. Use `haveI : Module.Finite K C := hφ`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := K) (M := C)`. Establish `hint : ∀ c : C, IsIntegral K c` using `fun c => Algebra.IsIntegral.isIntegral c`. Use `choose p hpm hpe using hint`.

Use `set P : K[X] := ∏ c ∈ s, p c with hP`. Establish `hPm : P.Monic` using `monic_prod_of_monic _ _ (fun c _ => hpm c)`. Establish `hsf : IsSplittingField K (IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K))) P` using `IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)`. Use `⟨IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)), IsSplittingField.finiteDimensional _ P, ?_⟩` and prove the remaining obligations. Generalize the expression as in `IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)) = E at hsf ⊢`.

Introduce `K₂ Ω _ _ e j ψ hc`. Establish `hspl : (P.map (algebraMap K E)).Splits` using `hsf.splits'`. Establish `hspl2 : (P.map (e.comp (algebraMap K E))).Splits`. Rewrite using `[← Polynomial.map_map]`. Conclude with `hspl.map e`.

Establish `hgen : ∀ c ∈ s, ψ c ∈ j.range`. Introduce `c hcs`. Establish `h0 : eval₂ φ c P = 0`. Rewrite using `[hP, eval₂_finsetProd]`. Conclude with `Finset.prod_eq_zero hcs (hpe c)`.

Establish `h1 : ((P.map (e.comp (algebraMap K E))).map j).IsRoot (ψ c)`. Rewrite using `[Polynomial.map_map, ← hc, IsRoot, eval_map, ← hom_eval₂, h0, map_zero]`. Conclude with `hspl2.mem_range_of_isRoot (hPm.map _).ne_zero h1`. Apply `factor_of_range` to reduce the goal to its premises. Introduce `c`.

Establish `hmem : c ∈ Submodule.span K (s : Set C)` using `by rw [hs]; trivial`. Express the relevant statement in the definitionally equal form `ψ c ∈ j.range`. Proceed by induction on `hmem using Submodule.span_induction with`. Consider the case `mem x hx => exact hgen x hx`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[Algebra.smul_def, map_mul]`. Use `mul_mem ?_ hx` and prove the remaining obligations.

Use `⟨e (algebraMap K E a), ?_⟩` and prove the remaining obligations. Conclude with `(RingHom.congr_fun hc a).symm`.
-/
theorem exists_finite_field_of_points (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C)
    (hφ : RingHom.Finite φ) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)), FiniteDimensional K ↥E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : ↥E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        RingHom.comp ψ φ = RingHom.comp j (RingHom.comp e (algebraMap K ↥E)) →
        ∃ (ψ₀ : C →+* K₂), RingHom.comp j ψ₀ = ψ := by
  classical
  letI : Algebra K C := φ.toAlgebra
  haveI : Module.Finite K C := hφ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := C)
  have hint : ∀ c : C, IsIntegral K c := fun c => Algebra.IsIntegral.isIntegral c
  choose p hpm hpe using hint
  set P : K[X] := ∏ c ∈ s, p c with hP
  have hPm : P.Monic := monic_prod_of_monic _ _ (fun c _ => hpm c)
  have hsf : IsSplittingField K
      (IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K))) P :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  refine ⟨IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)),
    IsSplittingField.finiteDimensional _ P, ?_⟩
  generalize IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K)) = E at hsf ⊢
  intro K₂ Ω _ _ e j ψ hc
  have hspl : (P.map (algebraMap K E)).Splits := hsf.splits'
  have hspl2 : (P.map (e.comp (algebraMap K E))).Splits := by
    rw [← Polynomial.map_map]; exact hspl.map e
  have hgen : ∀ c ∈ s, ψ c ∈ j.range := by
    intro c hcs
    have h0 : eval₂ φ c P = 0 := by
      rw [hP, eval₂_finsetProd]
      exact Finset.prod_eq_zero hcs (hpe c)
    have h1 : ((P.map (e.comp (algebraMap K E))).map j).IsRoot (ψ c) := by
      rw [Polynomial.map_map, ← hc, IsRoot, eval_map, ← hom_eval₂, h0, map_zero]
    exact hspl2.mem_range_of_isRoot (hPm.map _).ne_zero h1
  apply factor_of_range
  intro c
  have hmem : c ∈ Submodule.span K (s : Set C) := by rw [hs]; trivial
  change ψ c ∈ j.range
  induction hmem using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    refine ⟨e (algebraMap K E a), ?_⟩
    exact (RingHom.congr_fun hc a).symm

end GlobalTheory.FiniteFieldOfPoints
