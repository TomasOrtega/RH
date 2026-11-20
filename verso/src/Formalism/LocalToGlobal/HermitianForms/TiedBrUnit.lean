import Formalism.LocalToGlobal.HermitianForms.TiedBr

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Matrix

/- English proof (translation)
Substitute `hN` using the available equality. Apply `(Matrix.isUnit_iff_isUnit_det _).mp` to reduce the goal to its premises. Rewrite using `[← Matrix.mulVec_injective_iff_isUnit]`. Introduce `v1 v2 h12`. Establish `hv : (Matrix.of fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ (v1 - v2) = 0`.

Rewrite using `[Matrix.mulVec_sub, h12, sub_self]`. Rewrite using `[← sub_eq_zero]`. Generalize the expression as in `v1 - v2 = v at hv ⊢`. Establish `hsplit : ∀ a, ((Matrix.of fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ v) a = (A *ᵥ fun j => v j.castSucc) a + v (Fin.last n) * z a`. Introduce `a`.

Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]`. Establish `hv' : ∀ a, (A *ᵥ fun j => v j.castSucc) a + v (Fin.last n) * z a = 0` using `fun a => by`. Rewrite using `[← hsplit]`. Conclude with `congrFun hv a`. Establish `hlast : v (Fin.last n) = 0`.

Assume the negation of the conclusion as `h`. Apply `hz (-(v (Fin.last n))⁻¹ • fun j : Fin n => v j.castSucc)` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Establish `e : (A *ᵥ fun j : Fin n => v j.castSucc) a = -(v (Fin.last n) * z a)` using `by linear_combination hv' a`.

Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Establish `hcs : (fun j : Fin n => v j.castSucc) = 0`. Apply `hA` to reduce the goal to its premises. Use function extensionality and compare the values at `a`.

Use `hv' a` as an intermediate fact. Rewrite `this` using `[hlast, zero_mul, add_zero]`. Rewrite using `[this, Matrix.mulVec_zero]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `j`.

Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations. Conclude with `hlast`. Conclude with `congrFun hcs i`.
-/
theorem isUnit_det_cols {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    IsUnit (Matrix.of (fun a (b : Fin N) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a)).det := by
  subst hN
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v1 v2 h12
  have hv : (Matrix.of fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ (v1 - v2) = 0 := by
    rw [Matrix.mulVec_sub, h12, sub_self]
  rw [← sub_eq_zero]
  generalize v1 - v2 = v at hv ⊢
  have hsplit : ∀ a, ((Matrix.of fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ v) a =
      (A *ᵥ fun j => v j.castSucc) a + v (Fin.last n) * z a := by
    intro a
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  have hv' : ∀ a, (A *ᵥ fun j => v j.castSucc) a + v (Fin.last n) * z a = 0 := fun a => by
    rw [← hsplit]; exact congrFun hv a
  have hlast : v (Fin.last n) = 0 := by
    by_contra h
    apply hz (-(v (Fin.last n))⁻¹ • fun j : Fin n => v j.castSucc)
    funext a
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have e : (A *ᵥ fun j : Fin n => v j.castSucc) a = -(v (Fin.last n) * z a) := by linear_combination hv' a
    rw [e]; field_simp
  have hcs : (fun j : Fin n => v j.castSucc) = 0 := by
    apply hA
    funext a
    have := hv' a
    rw [hlast, zero_mul, add_zero] at this
    rw [this, Matrix.mulVec_zero]; rfl
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact hlast
  · exact congrFun hcs i

variable (D : D7)

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce `x y h`. Rewrite using `[← sub_eq_zero]`. Establish `h0 : D.sp.iX' (x - y) = 0` using `by rw [map_sub, h, sub_self]`. Apply `D.sp.X'.nondeg.1 (x - y)` to reduce the goal to its premises.

Introduce `w`. Rewrite using `[← D.sp.iX'_isom (x - y) w, h0, map_zero, LinearMap.zero_apply]`.
-/
theorem iX'_injective : letI := D.host.cmStar; Function.Injective D.sp.iX' := by
  letI := D.host.cmStar
  intro x y h
  rw [← sub_eq_zero]
  have h0 : D.sp.iX' (x - y) = 0 := by rw [map_sub, h, sub_self]
  apply D.sp.X'.nondeg.1 (x - y)
  intro w
  rw [← D.sp.iX'_isom (x - y) w, h0, map_zero, LinearMap.zero_apply]

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce `x y h`. Unfold `iXc at h`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, EmbeddingLike.apply_eq_iff_eq] at h`. Conclude with `(LinearEquiv.injective _) (iX'_injective D h)`.
-/
theorem iXc_injective : Function.Injective (iXc D) := by
  letI := D.host.cmStar
  intro x y h
  unfold iXc at h
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, EmbeddingLike.apply_eq_iff_eq] at h
  exact (LinearEquiv.injective _) (iX'_injective D h)

/- English proof (translation)
Introduce `x y h`. Simplify using `only [iXm, LinearMap.toMatrix'_mulVec] at h`. Conclude with `iXc_injective D h`.
-/
theorem iXm_mulVec_injective : Function.Injective (iXm D).mulVec := by
  intro x y h
  simp only [iXm, LinearMap.toMatrix'_mulVec] at h
  exact iXc_injective D h

variable {D}

/- English proof (translation)
Use `letI := D.host.cmStar`. Take `⟨a, ha⟩` from `Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line`. Establish `hT : ((D.mem u).A.T : D.host.E) ≠ 0` using `Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`.

Establish `h` using `Tf.til.hermitianForm_lastCoordinateUniformizerVector_self`. Rewrite `h` using `[ha, zero_smul]`. Simplify using `[Formalism.UG.hform] at h`. Conclude with `hT h.symm`. Introduce `hx`.

Simplify using `only [iXm, LinearMap.toMatrix'_mulVec] at hx`. Establish `hc : iXc D x = (a / ((D.mem u).A.T : D.host.E)) • zc D`. Rewrite using `[hx]`. Use function extensionality and compare the values at `i`. Rewrite using `[ha]`.

Simplify using `[Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Unfold `iXc zc at hc`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, ← map_smul, EmbeddingLike.apply_eq_iff_eq] at hc`. Establish `h1` using `D.sp.z_orth ((D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm x)`.

Rewrite `h1` using `[hc, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]`. Break down `mul_eq_zero.mp h1 with h2 | h2` into its components or cases. Conclude with `div_ne_zero ha0 hT ((map_eq_zero _).mp h2)`. Conclude with `D.sp.z_anis h2`.
-/
theorem vector_quotient_not_in_range {u : D.what₂.Word} (Tf : FormsTied D u) (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    iXm D *ᵥ x ≠ fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E) := by
  letI := D.host.cmStar
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  intro hx
  simp only [iXm, LinearMap.toMatrix'_mulVec] at hx
  have hc : iXc D x = (a / ((D.mem u).A.T : D.host.E)) • zc D := by
    rw [hx]; funext i; rw [ha]; simp [Pi.smul_apply, smul_eq_mul]; ring
  unfold iXc zc at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, ← map_smul,
    EmbeddingLike.apply_eq_iff_eq] at hc
  have h1 := D.sp.z_orth ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm x)
  rw [hc, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact div_ne_zero ha0 hT ((map_eq_zero _).mp h2)
  · exact D.sp.z_anis h2

/- English proof (translation)
The claim follows from `isUnit_det_cols (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E)) (iXm_mulVec_injective D) (vector_quotient_not_in_range Tf)`.
-/
theorem bZ_isUnit {u : D.what₂.Word} (Tf : FormsTied D u) : IsUnit (bZ u Tf.til.z0).det :=
  isUnit_det_cols (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E))
    (iXm_mulVec_injective D) (vector_quotient_not_in_range Tf)

end Formalism.L2.Forms
