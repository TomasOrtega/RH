import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

open GroundTheory.LocalField

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def boxSet (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℤ) : Set (Matrix (Fin 2) (Fin 2) K) :=
  {m | ∀ i j, m i j ∈ valBall K n}

/- English proof (translation)
Establish `: boxSet K n = ⋂ i, ⋂ j, (fun X : Matrix (Fin 2) (Fin 2) K => X i j) ⁻¹' (valBall K n : Set K)`. Use extensionality with `X`. Simplify using `[boxSet]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))`.
-/
private theorem isOpen_boxSet (n : ℤ) : IsOpen (boxSet K n) := by
  have : boxSet K n = ⋂ i, ⋂ j, (fun X : Matrix (Fin 2) (Fin 2) K => X i j) ⁻¹'
      (valBall K n : Set K) := by
    ext X; simp [boxSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))

/- English proof (translation)
Establish `: boxSet K n = Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => (valBall K n : Set K)`. Use extensionality with `X`. Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩`. Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_valBall n`.
-/
private theorem isCompact_boxSet (n : ℤ) : IsCompact (boxSet K n) := by
  have : boxSet K n = Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
      (valBall K n : Set K) := by
    ext X
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_valBall n

private def boxGrp (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℤ) : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K)) where
  carrier := Multiplicative.toAdd ⁻¹' boxSet K n
  one_mem' := fun _ _ => zero_mem _
  mul_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
  inv_mem' := fun ha i j => neg_mem (ha i j)

/- English proof (translation)
Introduce `N hN`. Establish `hS : Multiplicative.ofAdd ⁻¹' N ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K)` using `(continuous_ofAdd.tendsto (0 : Matrix (Fin 2) (Fin 2) K)) hN`. Take `⟨r, hr⟩` from `GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS`. Use `⟨boxGrp K r, (isOpen_boxSet (r : ℤ)).preimage continuous_toAdd, ?_, ?_⟩` and prove the remaining obligations. Use `(isCompact_boxSet (K := K) (r : ℤ)).image continuous_ofAdd` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨Multiplicative.toAdd x, hx, rfl⟩`.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `x hx`. Conclude with `hr hx`.
-/
private theorem lgrp_matrix : Lgrp (Multiplicative (Matrix (Fin 2) (Fin 2) K)) := by
  intro N hN
  have hS : Multiplicative.ofAdd ⁻¹' N ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K) :=
    (continuous_ofAdd.tendsto (0 : Matrix (Fin 2) (Fin 2) K)) hN
  obtain ⟨r, hr⟩ := GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS
  refine ⟨boxGrp K r, (isOpen_boxSet (r : ℤ)).preimage continuous_toAdd, ?_, ?_⟩
  · have := (isCompact_boxSet (K := K) (r : ℤ)).image continuous_ofAdd
    convert this using 1
    ext x
    constructor
    · intro hx
      exact ⟨Multiplicative.toAdd x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · intro x hx
    exact hr hx

private def cgrp (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {g | g.1 - 1 ∈ boxSet K ((n : ℤ) + 1)}
  one_mem' := by
    intro i j
    simp
  mul_mem' := by
    intro a b ha hb i j
    have e : (a * b).1 - 1 = (a.1 - 1) * (b.1 - 1) + (a.1 - 1) + (b.1 - 1) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
    rw [e]
    refine add_mem (add_mem ?_ (ha i j)) (hb i j)
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    exact valBall_antitone (by omega) (mul_mem_valBall (ha i l) (hb l j))
  inv_mem' := by
    intro g hg i j
    have e : (g⁻¹).1 = !![g.1 1 1, -g.1 0 1; -g.1 1 0, g.1 0 0] := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    have h00 := hg 0 0
    have h01 := hg 0 1
    have h10 := hg 1 0
    have h11 := hg 1 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h00 h11
    simp only [Matrix.sub_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h01 h10
    rw [e]
    fin_cases i <;> fin_cases j <;> simp
    · exact h11
    · exact h01
    · exact h10
    · exact h00

/- English proof (translation)
Establish `hc : Continuous fun g : Matrix.SpecialLinearGroup (Fin 2) K => g.1 - 1` using `continuous_subtype_val.sub continuous_const`. Conclude with `(isOpen_boxSet _).preimage hc`.
-/
private theorem isOpen_cgrp (n : ℕ) :
    IsOpen (cgrp K n : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  have hc : Continuous fun g : Matrix.SpecialLinearGroup (Fin 2) K => g.1 - 1 :=
    continuous_subtype_val.sub continuous_const
  exact (isOpen_boxSet _).preimage hc

/- English proof (translation)
Use `(Subtype.isCompact_iff (p := fun A : Matrix (Fin 2) (Fin 2) K => A.det = 1)).2 ?_` and prove the remaining obligations. Establish `hC : IsCompact ((fun m : Matrix (Fin 2) (Fin 2) K => m + 1) '' boxSet K ((n : ℤ) + 1))` using `(isCompact_boxSet _).image (continuous_id.add continuous_const)`. Establish `hD : IsClosed {m : Matrix (Fin 2) (Fin 2) K | m.det = 1}` using `isClosed_eq (Continuous.matrix_det continuous_id) continuous_const`. Use `hC.inter_right hD using 1` and compare the differences between its conclusion and the goal. Use extensionality with `m`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `⟨⟨g.1 - 1, hg, by simp⟩, g.2⟩`. Introduce and unpack `⟨⟨y, hy, rfl⟩, hd⟩`. Use `⟨⟨y + 1, hd⟩, ?_, rfl⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(y + 1) - 1 ∈ boxSet K ((n : ℤ) + 1)`. Simplify using `using hy`.
-/
private theorem isCompact_cgrp [T2Space K] (n : ℕ) :
    IsCompact (cgrp K n : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  refine (Subtype.isCompact_iff (p := fun A : Matrix (Fin 2) (Fin 2) K => A.det = 1)).2 ?_
  have hC : IsCompact ((fun m : Matrix (Fin 2) (Fin 2) K => m + 1) '' boxSet K ((n : ℤ) + 1)) :=
    (isCompact_boxSet _).image (continuous_id.add continuous_const)
  have hD : IsClosed {m : Matrix (Fin 2) (Fin 2) K | m.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  convert hC.inter_right hD using 1
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g.1 - 1, hg, by simp⟩, g.2⟩
  · rintro ⟨⟨y, hy, rfl⟩, hd⟩
    refine ⟨⟨y + 1, hd⟩, ?_, rfl⟩
    change (y + 1) - 1 ∈ boxSet K ((n : ℤ) + 1)
    simpa using hy

/- English proof (translation)
Introduce `N hN`. Take `⟨W, hW', hWN⟩` from `(mem_nhds_subtype _ _ _).1 hN`. Establish `hW : W ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) K)` using `hW'`. Establish `hS : (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K)`. Establish `hc : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m + 1` using `continuous_id.add continuous_const`.

Use `hc.tendsto (0 : Matrix (Fin 2) (Fin 2) K)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Conclude with `this hW`. Take `⟨r, hr⟩` from `GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS`. Use `⟨cgrp K r, isOpen_cgrp r, isCompact_cgrp r, fun g hg => hWN ?_⟩` and prove the remaining obligations.

Establish `h1 : g.1 - 1 ∈ (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W` using `hr fun i j => valBall_antitone (m := (r : ℤ)) (n := (r : ℤ) + 1) (by omega) (hg i j)`. Establish `h2 : (g.1 - 1) + 1 ∈ W` using `h1`. Rewrite `h2` using `[sub_add_cancel]`. Conclude with `h2`.
-/
private theorem lgrp_sl [T2Space K] : Lgrp (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro N hN
  obtain ⟨W, hW', hWN⟩ := (mem_nhds_subtype _ _ _).1 hN
  have hW : W ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) K) := hW'
  have hS : (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K) := by
    have hc : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m + 1 :=
      continuous_id.add continuous_const
    have := hc.tendsto (0 : Matrix (Fin 2) (Fin 2) K)
    rw [zero_add] at this
    exact this hW
  obtain ⟨r, hr⟩ := GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS
  refine ⟨cgrp K r, isOpen_cgrp r, isCompact_cgrp r, fun g hg => hWN ?_⟩
  have h1 : g.1 - 1 ∈ (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W :=
    hr fun i j => valBall_antitone (m := (r : ℤ)) (n := (r : ℤ) + 1) (by omega) (hg i j)
  have h2 : (g.1 - 1) + 1 ∈ W := h1
  rw [sub_add_cancel] at h2
  exact h2

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F _ _ v`. Conclude with `⟨lgrp_sl, lgrp_matrix⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.lgrp :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), Lgrp (SL v) ∧ Lgrp (Multiplicative (M2 v)) := by
  intro F _ _ v
  exact ⟨lgrp_sl, lgrp_matrix⟩
