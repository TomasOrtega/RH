import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTLat

noncomputable section

open NumberField Matrix Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

abbrev UU {S : HSpace E} (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) :
    Submodule ℝ (EuclideanSpace ℝ (Idx S)) :=
  Submodule.span ℝ (Set.range fun i ↦ psi M (e i : S.V))

section U

variable (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L)

def bU : Basis ι ℝ (UU M L e) := Basis.span (psi_e_linInd S hσ hsig hpos M L e)

/- English proof (translation)
Simplify using `[bU, Basis.span_apply]`.
-/
theorem bU_coe (i : ι) : ((bU S hσ hsig hpos M L e i : UU M L e) : EuclideanSpace ℝ (Idx S)) = psi M (e i : S.V) :=
  by simp [bU, Basis.span_apply]

abbrev abelian₂ : Submodule ℤ (UU M L e) := Submodule.span ℤ (Set.range (bU S hσ hsig hpos M L e))

/- English proof (translation)
Establish `h` using `congrArg (fun t : L ↦ (t : S.V)) (e.sum_repr ⟨l, hl⟩)`. Simplify using `only [Submodule.coe_sum] at h`. Establish `h' : ∑ i, (e.repr ⟨l, hl⟩ i) • (e i : S.V) = l`. Combine the equalities or inequalities in the displayed calculation. Use `conv_lhs => rw [← h']`.

Conclude with `psi_sum_int M L e _`.
-/
theorem psi_eq_sum (l : S.V) (hl : l ∈ L) :
    psi M l = ∑ i, (e.repr ⟨l, hl⟩ i) • psi M (e i : S.V) := by
  have h := congrArg (fun t : L ↦ (t : S.V)) (e.sum_repr ⟨l, hl⟩)
  simp only [Submodule.coe_sum] at h
  have h' : ∑ i, (e.repr ⟨l, hl⟩ i) • (e i : S.V) = l :=
    calc ∑ i, (e.repr ⟨l, hl⟩ i) • (e i : S.V) = ∑ i, ((e.repr ⟨l, hl⟩ i • e i : L) : S.V) :=
          Finset.sum_congr rfl fun i _ ↦ by simp
      _ = l := h
  conv_lhs => rw [← h']
  exact psi_sum_int M L e _

/- English proof (translation)
Rewrite using `[psi_eq_sum S M L e l hl]`. Conclude with `Submodule.sum_mem _ fun i _ ↦ zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _`.
-/
theorem psi_mem_U (l : S.V) (hl : l ∈ L) : psi M l ∈ UU M L e := by
  rw [psi_eq_sum S M L e l hl]
  exact Submodule.sum_mem _ fun i _ ↦ zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

/- English proof (translation)
Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Use `⟨fun i ↦ e.repr ⟨l, hl⟩ i, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower, bU_coe]`. Rewrite using `[psi_eq_sum S M L e l hl]`.
-/
theorem mem_Lam_of (l : S.V) (hl : l ∈ L) :
    (⟨psi M l, psi_mem_U S M L e l hl⟩ : UU M L e) ∈ abelian₂ S hσ hsig hpos M L e := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i ↦ e.repr ⟨l, hl⟩ i, Subtype.ext ?_⟩
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, bU_coe]
  rw [psi_eq_sum S M L e l hl]

/- English proof (translation)
Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hu`. Use `⟨∑ i, c i • (e i : S.V), Submodule.sum_mem _ fun i _ ↦ zsmul_mem (e i).2 _, ?_⟩` and prove the remaining obligations. Rewrite using `[psi_sum_int M L e, ← hc]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower, bU_coe]`.
-/
theorem exists_of_mem_Lam (u : UU M L e) (hu : u ∈ abelian₂ S hσ hsig hpos M L e) :
    ∃ l ∈ L, (u : EuclideanSpace ℝ (Idx S)) = psi M l := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hu
  refine ⟨∑ i, c i • (e i : S.V), Submodule.sum_mem _ fun i _ ↦ zsmul_mem (e i).2 _, ?_⟩
  rw [psi_sum_int M L e, ← hc]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, bU_coe]

/- English proof (translation)
Use `set b := bU S hσ hsig hpos M L e with hb`. Establish `hbmem : ∀ j, b j ∈ abelian₂ S hσ hsig hpos M L e` using `fun j ↦ Submodule.subset_span ⟨j, rfl⟩`. Use `choose n hn using fun j ↦ hy (b j) (hbmem j)`. Use `set c : ι → ℝ := fun i ↦ b.repr y i with hc`. Establish `hyc : (y : EuclideanSpace ℝ (Idx S)) = ∑ i, c i • psi M (e i : S.V)`.

Use `congrArg (fun t : UU M L e ↦ (t : EuclideanSpace ℝ (Idx S))) (b.sum_repr y)` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hb, bU_coe] at this`. Rewrite using `[← this]`. Establish `hGc : (GR S L e) *ᵥ c = fun j ↦ (n j : ℝ)`. Use extensionality with `j`.

Rewrite using `[← hn j]`. Express the relevant statement in the definitionally equal form `_ = ⟪(b j : EuclideanSpace ℝ (Idx S)), (y : EuclideanSpace ℝ (Idx S))⟫_ℝ`. Rewrite using `[hyc, inner_sum, hb, bU_coe]`. Simplify using `only [real_inner_smul_right, inner_e hσ M L e, Matrix.mulVec, dotProduct, GR_apply]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ by ring`.

Use `set c' : ι → ℚ := (GQ S L e)⁻¹ *ᵥ fun j ↦ (n j : ℚ) with hc'`. Establish `hdet` using `GQ_det S hσ hsig hpos M L e`. Establish `hGc' : (GQ S L e) *ᵥ c' = fun j ↦ (n j : ℚ)`. Rewrite using `[hc', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]`. Establish `hGR' : (GR S L e) *ᵥ (fun i ↦ (c' i : ℝ)) = fun j ↦ (n j : ℝ)`.

Use extensionality with `j`. Use `RingHom.map_mulVec (Rat.castHom ℝ) (GQ S L e) c' j` as an intermediate fact. Rewrite `this` using `[hGc']`. Simplify `this.symm` using `[GR, Function.comp_def]`. Establish `hcc : c = fun i ↦ (c' i : ℝ)`.

Establish `h0 : (GR S L e) *ᵥ (c - fun i ↦ (c' i : ℝ)) = 0`. Rewrite using `[Matrix.mulVec_sub, hGc, hGR', sub_self]`. Conclude with `sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero (GR_det S hσ hsig hpos M L e) h0)`. Use `set z : S.V := ∑ i, (c' i : E) • (e i : S.V) with hz`. Establish `hyz : (y : EuclideanSpace ℝ (Idx S)) = psi M z`.

Rewrite using `[hyc, hz, psi_sum_rat M L e, hcc]`. Use `⟨z, ?_, ?_, hyz⟩` and prove the remaining obligations. Introduce `l hl`. Take `⟨m, hm⟩` from `hy _ (mem_Lam_of S hσ hsig hpos M L e l hl)`. Establish `h1 : ⟪psi M l, psi M z⟫_ℝ = (m : ℝ)`.

Rewrite using `[← hyz]`. Conclude with `hm`. Rewrite `h1` using `[inner_psi hσ, trR_eq]`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `: ((Algebra.trace ℚ E (S.hT l z) : ℚ) : ℝ) = ((m : ℚ) : ℝ)` using `by rw [h1]; simp`.

Rewrite using `[eq_intCast]`. Conclude with `this.symm` after adjusting the coercions. Introduce `h0`. Apply `hy0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hyz, h0, map_zero]`. Both sides reduce to the same expression.
-/
theorem dual_vector_of_integral_pairing (y : UU M L e) (hy0 : y ≠ 0)
    (hy : ∀ x ∈ abelian₂ S hσ hsig hpos M L e, ∃ n : ℤ, ⟪x, y⟫_ℝ = (n : ℝ)) :
    ∃ z : S.V, TrDual S L z ∧ z ≠ 0 ∧ (y : EuclideanSpace ℝ (Idx S)) = psi M z := by
  set b := bU S hσ hsig hpos M L e with hb
  have hbmem : ∀ j, b j ∈ abelian₂ S hσ hsig hpos M L e := fun j ↦ Submodule.subset_span ⟨j, rfl⟩
  choose n hn using fun j ↦ hy (b j) (hbmem j)
  set c : ι → ℝ := fun i ↦ b.repr y i with hc
  have hyc : (y : EuclideanSpace ℝ (Idx S)) = ∑ i, c i • psi M (e i : S.V) := by
    have := congrArg (fun t : UU M L e ↦ (t : EuclideanSpace ℝ (Idx S))) (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, hb, bU_coe] at this
    rw [← this]
  have hGc : (GR S L e) *ᵥ c = fun j ↦ (n j : ℝ) := by
    ext j
    rw [← hn j]
    change _ = ⟪(b j : EuclideanSpace ℝ (Idx S)), (y : EuclideanSpace ℝ (Idx S))⟫_ℝ
    rw [hyc, inner_sum, hb, bU_coe]
    simp only [real_inner_smul_right, inner_e hσ M L e, Matrix.mulVec, dotProduct, GR_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  set c' : ι → ℚ := (GQ S L e)⁻¹ *ᵥ fun j ↦ (n j : ℚ) with hc'
  have hdet := GQ_det S hσ hsig hpos M L e
  have hGc' : (GQ S L e) *ᵥ c' = fun j ↦ (n j : ℚ) := by
    rw [hc', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  have hGR' : (GR S L e) *ᵥ (fun i ↦ (c' i : ℝ)) = fun j ↦ (n j : ℝ) := by
    ext j
    have := RingHom.map_mulVec (Rat.castHom ℝ) (GQ S L e) c' j
    rw [hGc'] at this
    simpa [GR, Function.comp_def] using this.symm
  have hcc : c = fun i ↦ (c' i : ℝ) := by
    have h0 : (GR S L e) *ᵥ (c - fun i ↦ (c' i : ℝ)) = 0 := by
      rw [Matrix.mulVec_sub, hGc, hGR', sub_self]
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero (GR_det S hσ hsig hpos M L e) h0)
  set z : S.V := ∑ i, (c' i : E) • (e i : S.V) with hz
  have hyz : (y : EuclideanSpace ℝ (Idx S)) = psi M z := by
    rw [hyc, hz, psi_sum_rat M L e, hcc]
  refine ⟨z, ?_, ?_, hyz⟩
  · intro l hl
    obtain ⟨m, hm⟩ := hy _ (mem_Lam_of S hσ hsig hpos M L e l hl)
    have h1 : ⟪psi M l, psi M z⟫_ℝ = (m : ℝ) := by
      rw [← hyz]; exact hm
    rw [inner_psi hσ, trR_eq] at h1
    refine ⟨m, ?_⟩
    have : ((Algebra.trace ℚ E (S.hT l z) : ℚ) : ℝ) = ((m : ℚ) : ℝ) := by rw [h1]; simp
    rw [eq_intCast]
    exact_mod_cast this.symm
  · intro h0
    apply hy0
    apply Subtype.ext
    rw [hyz, h0, map_zero]
    rfl

end U

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
