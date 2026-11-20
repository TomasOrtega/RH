import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelfDualLatticeMass
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MassFormulaPositivity

noncomputable section

namespace GlobalTheory.Proof.GenusMassSignature

open NumberField Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass Matrix
open scoped ComplexOrder MatrixOrder

/- English proof (translation)
Establish `hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ)` using `Subfield.isClosed_topologicalClosure _`. Break down `Complex.subfield_eq_of_closed hc with h1 | h1` into its components or cases. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Establish `hx : σ x ∈ σ.fieldRange.topologicalClosure` using `Subfield.le_topologicalClosure _ ⟨x, rfl⟩`. Rewrite `hx` using `[h1]`. Take `⟨r, hr⟩` from `hx`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hr]`.

Conclude with `Complex.conj_ofReal r`. Establish `: closure (Set.range σ) = Set.univ`. Use `congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1` as an intermediate fact. Conclude with `this`. Conclude with `dense_iff_closure_eq.2 this`.
-/
theorem denseRange_of_not_isReal {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

/- English proof (translation)
Set `e : Fin n ≃ Fin n ⊕ Fin 0` to `(Equiv.sumEmpty (Fin n) (Fin 0)).symm`. Establish `h1 : (J.reindex e e).PosDef`. Simplify using `using h.submatrix (e := e.symm) e.symm.injective`. Establish `hJ : Formalism.UG.Jpq n 0 = 1`. Use extensionality with `i j`.

Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases. Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`. Conclude with `i.elim0`.

Use `set A := J.reindex e e with hA`. Establish `hS : star (CFC.sqrt A) = CFC.sqrt A` using `(CFC.sqrt_nonneg A).isSelfAdjoint`. Establish `hSS : CFC.sqrt A * CFC.sqrt A = A` using `CFC.sqrt_mul_sqrt_self A h1.posSemidef.nonneg`. Establish `hu : IsUnit (CFC.sqrt A)`. Use `h1.isUnit` as an intermediate fact.

Rewrite `this` using `[← hSS]`. Conclude with `isUnit_of_mul_isUnit_left this`. Take `⟨U, hU⟩` from `hu`. Use `⟨e, U⁻¹, ?_⟩` and prove the remaining obligations. Establish `hc : Formalism.UG.cT (starRingEnd ℂ) ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix _ _ ℂ) = star ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ)`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hA2 : A = star (U : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) * U`. Rewrite using `[hU, hS, hSS]`. Rewrite using `[hJ, hc, ← hA, hA2, ← mul_assoc, ← star_mul, mul_assoc, Units.mul_inv, star_one, one_mul]`.
-/
theorem hasSignature_of_posDef {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : J.PosDef) :
    Formalism.UG.HasSignature J n 0 := by
  let e : Fin n ≃ Fin n ⊕ Fin 0 := (Equiv.sumEmpty (Fin n) (Fin 0)).symm
  have h1 : (J.reindex e e).PosDef := by
    simpa using h.submatrix (e := e.symm) e.symm.injective
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  set A := J.reindex e e with hA
  have hS : star (CFC.sqrt A) = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h1.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt A) := by
    have := h1.isUnit
    rw [← hSS] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨U, hU⟩ := hu
  refine ⟨e, U⁻¹, ?_⟩
  have hc : Formalism.UG.cT (starRingEnd ℂ) ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix _ _ ℂ) =
      star ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := by
    ext i j; rfl
  have hA2 : A = star (U : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) * U := by
    rw [hU, hS, hSS]
  rw [hJ, hc, ← hA, hA2, ← mul_assoc, ← star_mul, mul_assoc, Units.mul_inv, star_one, one_mul]

section Field

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Unfold `HSpace.hD`. Use `conv_lhs => rw [← W.frame.sum_repr x]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, starRingEnd_apply, hst, dotProduct, Matrix.mulVec, Matrix.map_apply, HSpace.gram, Pi.star_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem emb_form (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) (x : W.V) :
    τ (W.hD x x) = star (fun i => τ (W.frame.repr x i)) ⬝ᵥ
        (W.gram.map τ).mulVec (fun i => τ (W.frame.repr x i)) := by
  unfold HSpace.hD
  conv_lhs => rw [← W.frame.sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, map_mul, RingHom.id_apply, starRingEnd_apply, hst, dotProduct, Matrix.mulVec,
    Matrix.map_apply, HSpace.gram, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use extensionality with `i k`. Rewrite using `[conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, HSpace.gram, HSpace.gram, ← W.herm.eq (W.frame k) (W.frame i), starRingEnd_apply, hst]`. Both sides reduce to the same expression.
-/
theorem gram_isHermitian (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) : (W.gram.map τ).IsHermitian := by
  ext i k
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, HSpace.gram, HSpace.gram,
    ← W.herm.eq (W.frame k) (W.frame i), starRingEnd_apply, hst]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hH` using `gram_isHermitian hst W τ`. Establish `hd : DenseRange τ` using `denseRange_of_not_isReal τ (IsTotallyComplex.complexEmbedding_not_isReal τ)`. Establish `hdn : DenseRange fun (l : Fin W.rank → E) => (fun i => τ (l i))` using `DenseRange.piMap (fun _ : Fin W.rank => hd)`.

Establish `hco : ∀ l : Fin W.rank → E, τ (W.hD (W.frame.equivFun.symm l) (W.frame.equivFun.symm l)) = star (fun i => τ (l i)) ⬝ᵥ (W.gram.map τ).mulVec (fun i => τ (l i))`. Introduce `l`. Rewrite using `[emb_form hst]`. Establish `: ∀ i, W.frame.repr (W.frame.equivFun.symm l) i = l i` using `fun i => congrFun (W.frame.equivFun.apply_symm_apply l) i`. Simplify using `only [this]`.

Establish `hne : ∀ l : Fin W.rank → E, l ≠ 0 → W.frame.equivFun.symm l ≠ 0` using `fun l hl h0 => hl (W.frame.equivFun.symm.injective (by rw [h0, map_zero]))`. Establish `hpsd : (W.gram.map τ).PosSemidef`. Use `PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_` and prove the remaining obligations. Rewrite using `[Complex.nonneg_iff]`. Use `⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩` and prove the remaining obligations.

Use `hdn.induction_on (p := fun y => 0 ≤ (star y ⬝ᵥ ((W.gram.map τ) *ᵥ y)).re) x ?_ ?_` and prove the remaining obligations. Conclude with `isClosed_le continuous_const (by fun_prop)`. Introduce `l`. Distinguish the cases in `hl : l = 0`. Substitute `hl` using the available equality.

Simplify using `[dotProduct]`. Use `h _ (hne l hl)` as an intermediate fact. Rewrite `this` using `[hco]`. Conclude with `this.le`. Rewrite using `[hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`.

Introduce `h0`. Establish `h1 : W.gram.det = 0`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, map_zero]`. Conclude with `h0`.

Take `⟨l, hl, hl0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h1`. Establish `h2 : (W.gram.map τ).mulVec (fun i => τ (l i)) = 0`. Use function extensionality and compare the values at `i`. Use `congrArg τ (congrFun hl0 i)` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct]`.

Use `h _ (hne l hl)` as an intermediate fact. Rewrite `this` using `[hco, h2]`. Simplify using `at this`. Introduce `h x hx`. Establish `hv : (fun i => τ (W.frame.repr x i)) ≠ 0`.

Introduce `h`. Apply `hx` to reduce the goal to its premises. Apply `W.frame.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `using congrFun h i`.

Rewrite using `[emb_form hst]`. Conclude with `h.re_dotProduct_pos hv`.
-/
theorem pos_iff_posDef (htc : IsTotallyComplex E)
    (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) :
    (∀ x : W.V, x ≠ 0 → 0 < (τ (W.hD x x)).re) ↔ (W.gram.map τ).PosDef := by
  constructor
  · intro h
    have hH := gram_isHermitian hst W τ
    have hd : DenseRange τ :=
      denseRange_of_not_isReal τ (IsTotallyComplex.complexEmbedding_not_isReal τ)
    have hdn : DenseRange fun (l : Fin W.rank → E) => (fun i => τ (l i)) :=
      DenseRange.piMap (fun _ : Fin W.rank => hd)
    have hco : ∀ l : Fin W.rank → E, τ (W.hD (W.frame.equivFun.symm l) (W.frame.equivFun.symm l)) =
        star (fun i => τ (l i)) ⬝ᵥ (W.gram.map τ).mulVec (fun i => τ (l i)) := by
      intro l
      rw [emb_form hst]
      have : ∀ i, W.frame.repr (W.frame.equivFun.symm l) i = l i := fun i =>
        congrFun (W.frame.equivFun.apply_symm_apply l) i
      simp only [this]
    have hne : ∀ l : Fin W.rank → E, l ≠ 0 → W.frame.equivFun.symm l ≠ 0 := fun l hl h0 =>
      hl (W.frame.equivFun.symm.injective (by rw [h0, map_zero]))
    have hpsd : (W.gram.map τ).PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
      rw [Complex.nonneg_iff]
      refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
      refine hdn.induction_on (p := fun y => 0 ≤ (star y ⬝ᵥ ((W.gram.map τ) *ᵥ y)).re) x ?_ ?_
      · exact isClosed_le continuous_const (by fun_prop)
      · intro l
        by_cases hl : l = 0
        · subst hl
          simp [dotProduct]
        · have := h _ (hne l hl)
          rw [hco] at this
          exact this.le
    rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    have h1 : W.gram.det = 0 := by
      apply τ.injective
      rw [RingHom.map_det, map_zero]
      exact h0
    obtain ⟨l, hl, hl0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h1
    have h2 : (W.gram.map τ).mulVec (fun i => τ (l i)) = 0 := by
      funext i
      have := congrArg τ (congrFun hl0 i)
      simpa [Matrix.mulVec, dotProduct] using this
    have := h _ (hne l hl)
    rw [hco, h2] at this
    simp at this
  · intro h x hx
    have hv : (fun i => τ (W.frame.repr x i)) ≠ 0 := by
      intro h
      apply hx
      apply W.frame.repr.injective
      ext i
      simpa using congrFun h i
    rw [emb_form hst]
    exact h.re_dotProduct_pos hv

def withPosSig (W : HSpace E) : HSpace E := { W with sig := fun _ => (W.rank, 0) }

end Field

end GlobalTheory.Proof.GenusMassSignature
