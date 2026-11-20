import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

/- English proof (translation)
Simplify using `[sigR, inclR]`.
-/
theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

/- English proof (translation)
Simplify using `[sigR]`.
-/
theorem sigR_tmul_one (x : R) : sigR R σ (x ⊗ₜ[F] (1 : E)) = x ⊗ₜ[F] (1 : E) := by
  simp [sigR]

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul {A : Type} [CommRing A] {M : ℕ} (τ : A →+* A) (J : Matrix (Fin M) (Fin M) A) (c d : A)
    (x y : Fin M → A) : Formalism.UG.hform τ J (c • x) (d • y) = τ c * d * Formalism.UG.hform τ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hR, hE, Formalism.UG.hform, JR, ratTup, Matrix.map_apply, map_sum, map_mul, sigR_inclR]`. Both sides reduce to the same expression.
-/
theorem hR_ratTup {M k : ℕ} (J : Matrix (Fin M) (Fin M) E) (Y : Fin k → Fin M → E) (a b : Fin k) :
    hR R σ J (ratTup R Y a) (ratTup R Y b) = inclR R (hE σ J (Y a) (Y b)) := by
  simp only [hR, hE, Formalism.UG.hform, JR, ratTup, Matrix.map_apply, map_sum, map_mul, sigR_inclR]
  rfl

end Gen

/- English proof (translation)
Unfold `dV`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `one_ne_zero`.
-/
theorem dV_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

/- English proof (translation)
Unfold `alp`. Use `split_ifs`. Conclude with `pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))`. Conclude with `one_ne_zero`.
-/
theorem alp_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) (a : Fin (r + 1)) :
    alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

/- English proof (translation)
Simplify using `[alp]`.
-/
theorem alp_last {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) :
    alp v r (Fin.last r) = 1 := by
  simp [alp]

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

/- English proof (translation)
Introduce `R H x`. Use `H.isCMField_hostE` as an intermediate fact. Apply `H.φ₀.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `H.φ₀ (NumberField.IsCMField.complexConj H.E x) = H.φ₀ (H.conj x)`. Rewrite using `[NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]`.
-/
theorem host_star_conj : Formalism.BasicNotions.bridge_star := by
  intro R H x
  have := H.isCMField_hostE
  apply H.φ₀.injective
  change H.φ₀ (NumberField.IsCMField.complexConj H.E x) = H.φ₀ (H.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sig_apply (a : X.B.I.E) : X.B.I.cm.sig a = star a := rfl

/- English proof (translation)
Establish `key : (VS D).hT x y = ∑ i, ∑ j, star (X.bas.repr x i) * (VS D).hT (X.bas i) (X.bas j) * X.bas.repr y j` using `by conv_lhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Apply `X.ιE.injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, key]`. Simplify using `only [hE, Formalism.UG.hform, crdOf, map_sum, map_mul, RingHom.coe_coe, sig_apply, X.ιE_conj, RingEquiv.apply_symm_apply, X.J_eq]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← host_star_conj D.R D.host]`.
-/
theorem hE_crdOf (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas x) (crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  have key : (VS D).hT x y = ∑ i, ∑ j, star (X.bas.repr x i) * (VS D).hT (X.bas i) (X.bas j) *
      X.bas.repr y j := by
    conv_lhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply, key]
  simp only [hE, Formalism.UG.hform, crdOf, map_sum, map_mul, RingHom.coe_coe, sig_apply, X.ιE_conj,
    RingEquiv.apply_symm_apply, X.J_eq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← host_star_conj D.R D.host]

def hv : Fin (D.R.rS + 1 + D.R.rS) → (VS D).V := Fin.append (Fin.snoc X.eX (X.zu u')) X.fY

/- English proof (translation)
Use `Fin.addCases (fun a => ?_) (fun b => ?_) a` and prove the remaining obligations. Rewrite using `[hv, Fin.append_left, tupH, Fin.append_left]`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Rewrite using `[F0, Fin.snoc_last, Fin.snoc_last]`. Both sides reduce to the same expression.

Rewrite using `[F0, Fin.snoc_castSucc, Fin.snoc_castSucc]`. Both sides reduce to the same expression. Rewrite using `[hv, Fin.append_right, tupH, Fin.append_right]`. Both sides reduce to the same expression.
-/
theorem tupH_eq (a : Fin (D.R.rS + 1 + D.R.rS)) :
    tupH (frameOf X u') a = crdOf X.B.I X.ιE X.bas (hv X u' a) := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) a
  · rw [hv, Fin.append_left, tupH, Fin.append_left]
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [F0, Fin.snoc_last, Fin.snoc_last]; rfl
    · rw [F0, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
  · rw [hv, Fin.append_right, tupH, Fin.append_right]; rfl

/- English proof (translation)
Establish `hs` using `(VS D).herm`. Apply the tactic sequence `refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>`. Simplify using `only [hv, scl, Fin.append_left, Fin.append_right]`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b <;>`. Simplify using `only [Fin.snoc_last, Fin.snoc_castSucc]`.

Use `right`. Rewrite using `[alp_last, one_mul]`. Use `left`. Conclude with `(hs.eq_iff).1 (X.zu_orth u' j).1`. Use `left`.

Conclude with `(X.zu_orth u' i).1`. Use `left`. Conclude with `X.ee i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) a <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]`. Use `left`.

Conclude with `(hs.eq_iff).1 (X.zu_orth u' b).2`. Distinguish the cases in `h : i = b`. Use `right`. Substitute `h` using the available equality. Conclude with `mul_inv_cancel₀ (alp_ne_zero v _ _)`.

Use `left`. Rewrite using `[X.ef, if_neg h]`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun j => ?_) b <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]`. Use `left`. Conclude with `(X.zu_orth u' a).2`.

Distinguish the cases in `h : j = a`. Use `right`. Substitute `h` using the available equality. Conclude with `inv_mul_cancel₀ (alp_ne_zero v _ _)`. Use `left`.

Use `(hs.eq_iff).1 ?_` and prove the remaining obligations. Rewrite using `[X.ef, if_neg h]`. Use `left`. Conclude with `X.ff a b`.
-/
theorem hT_zero_or (v : PlX X) (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    (VS D).hT (hv X u' a) (hv X u' b) = 0 ∨ scl X v a * scl X v b = 1 := by
  have hs := (VS D).herm
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
    simp only [hv, scl, Fin.append_left, Fin.append_right]
  · refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · right; rw [alp_last, one_mul]
    · left; exact (hs.eq_iff).1 (X.zu_orth u' j).1
    · left; exact (X.zu_orth u' i).1
    · left; exact X.ee i j
  · refine Fin.lastCases ?_ (fun i => ?_) a <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · left; exact (hs.eq_iff).1 (X.zu_orth u' b).2
    · by_cases h : i = b
      · right; subst h; exact mul_inv_cancel₀ (alp_ne_zero v _ _)
      · left; rw [X.ef, if_neg h]
  · refine Fin.lastCases ?_ (fun j => ?_) b <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · left; exact (X.zu_orth u' a).2
    · by_cases h : j = a
      · right; subst h; exact inv_mul_cancel₀ (alp_ne_zero v _ _)
      · left; refine (hs.eq_iff).1 ?_; rw [X.ef, if_neg h]
  · left; exact X.ff a b

/- English proof (translation)
Introduce `v`. Use function extensionality and compare the values at `a b`. Establish `hY : ∀ i, yTup X u' v i = sc (E` using `X.B.I.E) v (scl X v i) • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')) i := fun i => rfl`. Use `show hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v a) (yTup X u' v b) = inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b)`. Rewrite using `[hY, hY]`.

Unfold `hR`. Rewrite using `[hform_smul]`. Express the relevant statement in the definitionally equal form `sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc v (scl X v a)) * sc v (scl X v b) * hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J _ _ = _`. Rewrite using `[hR_ratTup]`. Simplify using `only [sc, sigR_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.

Express the relevant statement in the definitionally equal form `_ = inclR (Fv X.B.I.F v) (hE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u') a) (tupH (frameOf X u') b))`. Break down `hT_zero_or X u' v a b with h | h` into its components or cases. Establish `h0 : hE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u') a) (tupH (frameOf X u') b) = 0`. Rewrite using `[tupH_eq, tupH_eq, hE_crdOf, h, map_zero]`. Rewrite using `[h0, map_zero, mul_zero]`.

Rewrite using `[h, ← Algebra.TensorProduct.one_def, one_mul]`.
-/
theorem omVGram_holds : OmVGram X u' := by
  intro v
  funext a b
  have hY : ∀ i, yTup X u' v i = sc (E := X.B.I.E) v (scl X v i) • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')) i :=
    fun i => rfl
  show hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v a) (yTup X u' v b) =
    inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b)
  rw [hY, hY]
  unfold hR
  rw [hform_smul]
  change sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc v (scl X v a)) * sc v (scl X v b) *
      hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J _ _ = _
  rw [hR_ratTup]
  simp only [sc, sigR_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  change _ = inclR (Fv X.B.I.F v) (hE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u') a) (tupH (frameOf X u') b))
  rcases hT_zero_or X u' v a b with h | h
  · have h0 : hE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u') a) (tupH (frameOf X u') b) = 0 := by
      rw [tupH_eq, tupH_eq, hE_crdOf, h, map_zero]
    rw [h0, map_zero, mul_zero]
  · rw [h, ← Algebra.TensorProduct.one_def, one_mul]

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
