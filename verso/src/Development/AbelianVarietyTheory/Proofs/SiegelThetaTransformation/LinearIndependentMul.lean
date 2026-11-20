import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsNearlyPrimitive
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryExt

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.LagRep

/- English proof (translation)
Establish `h1 : Function.Injective W.vecMul` using `Matrix.vecMul_injective_iff.mpr hW`. Establish `h2 : Function.Injective b.vecMul` using `Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det b).mpr hb.isUnit)`. Use `Matrix.vecMul_injective_iff.mp ?_` and prove the remaining obligations. Introduce `s t hst`. Apply `h2` to reduce the goal to its premises.

Apply `h1` to reduce the goal to its premises. Simplify `hst` using `only [Matrix.vecMul_vecMul]`.
-/
theorem linearIndependent_mul {E κ ι : Type} [Field E] [Fintype κ] [DecidableEq κ]
    (b : Matrix κ κ E) (hb : b.det ≠ 0) (W : Matrix κ ι E)
    (hW : LinearIndependent E (fun i => W i)) : LinearIndependent E (fun i => (b * W) i) := by
  have h1 : Function.Injective W.vecMul := Matrix.vecMul_injective_iff.mpr hW
  have h2 : Function.Injective b.vecMul :=
    Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det b).mpr hb.isUnit)
  refine Matrix.vecMul_injective_iff.mp ?_
  intro s t hst
  apply h2
  apply h1
  simpa only [Matrix.vecMul_vecMul] using hst

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: (b * W) i = ∑ k, b i k • W k`. Use extensionality with `j`. Simplify using `[Matrix.mul_apply, Finset.sum_apply]`.

Use `show (b * W) i ∈ Submodule.span E (Set.range fun i => W i)`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem span_mul_le {E κ ι : Type} [Field E] [Fintype κ]
    (b : Matrix κ κ E) (W : Matrix κ ι E) :
    Submodule.span E (Set.range fun i => (b * W) i) ≤
      Submodule.span E (Set.range fun i => W i) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have : (b * W) i = ∑ k, b i k • W k := by
    ext j
    simp [Matrix.mul_apply, Finset.sum_apply]
  show (b * W) i ∈ Submodule.span E (Set.range fun i => W i)
  rw [this]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/- English proof (translation)
Use `le_antisymm (span_mul_le b W) ?_` and prove the remaining obligations. Use `span_mul_le b⁻¹ (b * W)` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul b hb.isUnit, Matrix.one_mul]`. Then use the resulting hypothesis.
-/
theorem span_mul {E κ ι : Type} [Field E] [Fintype κ] [DecidableEq κ]
    (b : Matrix κ κ E) (hb : b.det ≠ 0) (W : Matrix κ ι E) :
    Submodule.span E (Set.range fun i => (b * W) i) =
      Submodule.span E (Set.range fun i => W i) := by
  refine le_antisymm (span_mul_le b W) ?_
  have := span_mul_le b⁻¹ (b * W)
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul b hb.isUnit, Matrix.one_mul] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, cc]`.
-/
theorem ccT_ccT' {α β : Type} (A : Matrix α β E) : ccT (ccT A) = A := by
  ext i j
  simp [ccT, cc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, cc, Matrix.mul_apply, mul_comm]`.
-/
theorem ccT_mul' {α β δ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β δ E) :
    ccT (A * B) = ccT B * ccT A := by
  ext i j
  simp [ccT, cc, Matrix.mul_apply, mul_comm]

/- English proof (translation)
Take `⟨⟨hdet, -, hc, -⟩, -⟩` from `unitary_act_halfSpace E ∅ N γ hγ`. Prove the components needed by the constructor for the conclusion. Establish `h : LinearIndependent E (fun i => γ i)` using `Matrix.linearIndependent_rows_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det γ).mpr hdet)`. Conclude with `h.comp Sum.inr Sum.inr_injective`. Establish `h : γ * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E`.

Establish `: ccT (ccT γ) * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E` using `hc`. Rewrite `this` using `[ccT_ccT']`. Then use the resulting hypothesis. Use extensionality with `i j`. Establish `h' : (γ * Matrix.J (Fin N) E * ccT γ) (Sum.inr i) (Sum.inr j) = 0`. Rewrite using `[h]`.

Simplify using `[Matrix.J]`. Conclude with `h'`.
-/
theorem lower_rows {N : ℕ} (γ : M2 E N) (hγ : γ ∈ UU E N) :
    LinearIndependent E (fun i => (γ.submatrix Sum.inr id) i) ∧
      γ.submatrix Sum.inr id * Matrix.J (Fin N) E * ccT (γ.submatrix Sum.inr id) = 0 := by
  obtain ⟨⟨hdet, -, hc, -⟩, -⟩ := unitary_act_halfSpace E ∅ N γ hγ
  constructor
  · have h : LinearIndependent E (fun i => γ i) :=
      Matrix.linearIndependent_rows_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det γ).mpr hdet)
    exact h.comp Sum.inr Sum.inr_injective
  · have h : γ * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E := by
      have : ccT (ccT γ) * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E := hc
      rwa [ccT_ccT'] at this
    ext i j
    have h' : (γ * Matrix.J (Fin N) E * ccT γ) (Sum.inr i) (Sum.inr j) = 0 := by
      rw [h]
      simp [Matrix.J]
    exact h'

/- English proof (translation)
Introduce `E _ _ _ N`. Take `⟨c, C, hc, hprim⟩` from `exists_nearly_primitive E N`. Take `⟨c', hc', hext⟩` from `RowExt.exists_unitary_ext E N c hc`. Use `⟨c', hc', ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨U, γ₀, hγ₀, rfl⟩`.

Take `⟨hli, hiso⟩` from `lower_rows γ₀ hγ₀`. Use `set W₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E := γ₀.submatrix Sum.inr id with hW₀`. Take `⟨d, hd, hint⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : Fin N × (Fin N ⊕ Fin N) => W₀ p.1 p.2)`. Use `set D : Matrix (Fin N) (Fin N) E := (d : E) • (1 : Matrix (Fin N) (Fin N) E) with hD`. Establish `hDdet : D.det ≠ 0`.

Rewrite using `[hD, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `pow_ne_zero _ (Int.cast_ne_zero.mpr hd)`. Establish `hDint : IntM (D * W₀)`. Introduce `i j`. Use `hint (W₀ i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)` as an intermediate fact.

Rewrite using `[hD, Matrix.smul_mul, Matrix.one_mul]`. Simplify `this` using `[zsmul_eq_mul]`. Take `⟨a, ha, -, haint, hap⟩` from `hprim _ (D * W₀) hDint (linearIndependent_mul D hDdet W₀ hli)`. Take `⟨γ, hγ, hden, hrows⟩` from `hext (a * (D * W₀)) haint (linearIndependent_mul a ha _ (linearIndependent_mul D hDdet W₀ hli)) (by`. Establish `: a * (D * W₀) * Matrix.J (Fin N) E * ccT (a * (D * W₀)) = a * D * (W₀ * Matrix.J (Fin N) E * ccT W₀) * (ccT D * ccT a)`.

Simplify using `only [ccT_mul', Matrix.mul_assoc]`. Rewrite using `[this, hiso, Matrix.mul_zero, Matrix.zero_mul]) hap`. Use `⟨γ, hγ, hden, ?_⟩` and prove the remaining obligations. Use `show botSpan γ = botSpan γ₀`. Unfold `botSpan`.

Simplify using `only [hrows]`. Rewrite using `[span_mul a ha, span_mul D hDdet]`. Both sides reduce to the same expression.
-/
theorem exists_rep_den : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ),
    ∃ c : ℕ, 0 < c ∧ ∀ U : Lag E N, ∃ γ ∈ UU E N, Den c γ ∧ botSpan γ = U.1 := by
  intro E _ _ _ N
  classical
  obtain ⟨c, C, hc, hprim⟩ := exists_nearly_primitive E N
  obtain ⟨c', hc', hext⟩ := RowExt.exists_unitary_ext E N c hc
  refine ⟨c', hc', ?_⟩
  rintro ⟨U, γ₀, hγ₀, rfl⟩
  obtain ⟨hli, hiso⟩ := lower_rows γ₀ hγ₀
  set W₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E := γ₀.submatrix Sum.inr id with hW₀
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin N × (Fin N ⊕ Fin N) => W₀ p.1 p.2)
  set D : Matrix (Fin N) (Fin N) E := (d : E) • (1 : Matrix (Fin N) (Fin N) E) with hD
  have hDdet : D.det ≠ 0 := by
    rw [hD, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Int.cast_ne_zero.mpr hd)
  have hDint : IntM (D * W₀) := by
    intro i j
    have := hint (W₀ i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    rw [hD, Matrix.smul_mul, Matrix.one_mul]
    simpa [zsmul_eq_mul] using this
  obtain ⟨a, ha, -, haint, hap⟩ := hprim _ (D * W₀) hDint (linearIndependent_mul D hDdet W₀ hli)
  obtain ⟨γ, hγ, hden, hrows⟩ := hext (a * (D * W₀)) haint
    (linearIndependent_mul a ha _ (linearIndependent_mul D hDdet W₀ hli))
    (by
      have : a * (D * W₀) * Matrix.J (Fin N) E * ccT (a * (D * W₀)) =
          a * D * (W₀ * Matrix.J (Fin N) E * ccT W₀) * (ccT D * ccT a) := by
        simp only [ccT_mul', Matrix.mul_assoc]
      rw [this, hiso, Matrix.mul_zero, Matrix.zero_mul]) hap
  refine ⟨γ, hγ, hden, ?_⟩
  show botSpan γ = botSpan γ₀
  unfold botSpan
  simp only [hrows]
  rw [span_mul a ha, span_mul D hDdet]
  rfl

end GlobalTheory.SW.LagRep
