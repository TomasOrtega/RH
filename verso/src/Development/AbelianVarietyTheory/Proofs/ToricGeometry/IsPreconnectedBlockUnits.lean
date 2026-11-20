import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Matrix

namespace GlobalTheory.PeriodConn

open NumberField Matrix in
/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.PeriodConn.hermForm_conj_mul {g : ℕ} (Hm N : Matrix (Fin g) (Fin g) ℂ)
    (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Nᵀ * Hm * N.map star) z w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (N.mulVec z) (N.mulVec w) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  congr 2
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open NumberField Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.PeriodConn.isPeriod_mulVec {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) {A : Matrix (Fin g) (Fin g) ℂ} (hA : A.det ≠ 0)
    (hty : ∀ i j, ty i ≠ ty j → A i j = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty ((A.mulVecLin).toAddMonoidHom.comp P) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hHm, hpos, him⟩ := hP
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hcancel : ∀ v, A⁻¹ *ᵥ (A *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
  have hcancel' : ∀ v, A *ᵥ (A⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a x i
    simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hlin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : ty i = ty j
    · rw [h]; ring
    · rw [hty i j h]; simp
  · intro x y hxy
    apply hinj
    have := congrArg (fun v => A⁻¹ *ᵥ v) hxy
    simpa [hcancel] using this
  · let f : (A.mulVecLin.toAddMonoidHom.comp P).range → P.range := fun v =>
      ⟨A⁻¹ *ᵥ (v : Fin g → ℂ), by
        obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp v.2
        refine AddMonoidHom.mem_range.mpr ⟨x, ?_⟩
        rw [← hx]
        exact (hcancel (P x)).symm⟩
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · exact (continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _
    · intro v w hvw
      apply Subtype.ext
      have := congrArg (fun u : P.range => A *ᵥ (u : Fin g → ℂ)) hvw
      simpa [f, hcancel'] using this
  · have hr : Set.range ⇑(A.mulVecLin.toAddMonoidHom.comp P) =
        ((A.mulVecLin).restrictScalars ℝ) '' Set.range ⇑P := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact fun v => ⟨A⁻¹ *ᵥ v, hcancel' v⟩
  · have hct : ∀ N : Matrix (Fin g) (Fin g) ℂ, (N.map star)ᴴ = Nᵀ := fun N => by
      ext i j; simp
    have hct' : ∀ N : Matrix (Fin g) (Fin g) ℂ, (Nᵀ)ᴴ = N.map star := fun N => by
      ext i j; simp
    refine ⟨(A⁻¹)ᵀ * Hm * (A⁻¹).map star, ?_, ?_, ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHm.eq, hct, hct',
        Matrix.mul_assoc]
    · intro z hz
      rw [_root_.GlobalTheory.PeriodConn.hermForm_conj_mul]
      refine hpos _ fun h => hz ?_
      simpa [hcancel'] using congrArg (fun v => A *ᵥ v) h
    · intro x y
      change (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm _ (A *ᵥ P x) (A *ᵥ P y)).im = _
      rw [_root_.GlobalTheory.PeriodConn.hermForm_conj_mul, hcancel, hcancel]
      exact him x y

open NumberField Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.PeriodConn.entry_eq_zero {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P P' : D.La →+ (Fin g → ℂ)}
    (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (hP' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P') {A : Matrix (Fin g) (Fin g) ℂ}
    (h : ∀ x, P' x = A.mulVec (P x)) (i j : Fin g) (hij : ty i ≠ ty j) : A i j = 0 := by
  obtain ⟨hlin, -, -, hspan, -⟩ := hP
  have hlin' := hP'.1
  have key : ∀ a : 𝓞 E, A i j * ((ty j) (a : E) - (ty i) (a : E)) = 0 := by
    intro a
    set d : Fin g → ℂ := fun k => (ty k) (a : E) - (ty i) (a : E) with hd
    let φ : (Fin g → ℂ) →ₗ[ℝ] ℂ :=
      ((LinearMap.proj i).comp (A.mulVecLin.comp (Matrix.diagonal d).mulVecLin)).restrictScalars ℝ
    have hφ : φ = 0 := by
      refine LinearMap.ext_on_range hspan fun x => ?_
      have h1 := hlin' a x i
      rw [h (a • x), h x] at h1
      have hvec : Matrix.diagonal d *ᵥ P x = P (a • x) - (ty i) (a : E) • P x := by
        funext k
        simp [Matrix.mulVec_diagonal, hd, hlin, sub_mul]
      simp only [φ, LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        Matrix.mulVecLin_apply, LinearMap.zero_apply, hvec, Matrix.mulVec_sub,
        Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, sub_self]
    have := LinearMap.congr_fun hφ (Pi.single j 1)
    simpa [φ, hd, Matrix.mulVec_single, Matrix.mulVec, dotProduct, Matrix.diagonal,
      Pi.single_apply] using this
  by_contra hA
  apply hij
  refine (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_).symm
  ext a
  have := key a
  simp only [RingHom.comp_apply]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hA))

end GlobalTheory.PeriodConn
