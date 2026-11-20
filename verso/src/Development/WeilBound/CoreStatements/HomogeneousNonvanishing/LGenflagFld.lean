import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LGenflagLU
open GlobalTheory.CompanionTheory.Ar Matrix

namespace PositivityTheory.UnitarySelfGeneration.GF

variable {S : Type} {r : S → ℕ} {Ω : Type} [Field Ω]

abbrev Idx (r : S → ℕ) : Type := Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1}

abbrev ent {F : Type} (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F) : Idx r → F := fun q => u q.1 q.2.1.1 q.2.1.2

noncomputable def gen (Ω : Type) [Field Ω] (r : S → ℕ) (σ : S) :
    Matrix (Fin (r σ)) (Fin (r σ)) (MvPolynomial (Idx r) Ω) :=
  Matrix.of fun l k => if h : k < l then MvPolynomial.X ⟨σ, ⟨(l, k), h⟩⟩ else if l = k then 1 else 0

/- English proof (translation)
Use extensionality with `l k`. Simplify using `only [gen, map_apply, of_apply]`. Use `split_ifs with h1 h2`. Simplify using `[ent]`. Substitute `h2` using the available equality.

Simplify using `[(hu σ).1]`. Simplify using `[(hu σ).2 l k (lt_of_le_of_ne (not_lt.1 h1) h2)]`.
-/
theorem gen_map {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (σ : S) :
    (gen Ω r σ).map (MvPolynomial.aeval (R := Ω) (ent u)).toRingHom = u σ := by
  ext l k
  simp only [gen, map_apply, of_apply]
  split_ifs with h1 h2
  · simp [ent]
  · subst h2; simp [(hu σ).1]
  · simp [(hu σ).2 l k (lt_of_le_of_ne (not_lt.1 h1) h2)]

/- English proof (translation)
Use `choose w hw hw' using fun σ => exists_general (g σ) (hg σ)`. Establish `key : ∀ (F : Type) [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F), (∀ σ, Uni (u σ)) → (trunc k ((g σ).map (algebraMap Ω F) * u σ)).det = MvPolynomial.aeval (R` using `Ω) (ent u) (trunc k ((g σ).map MvPolynomial.C * gen Ω r σ)).det := by`. Introduce `F _ _ u hu`. Use `det_trunc_map (MvPolynomial.aeval (R := Ω) (ent u)).toRingHom k ((g σ).map MvPolynomial.C * gen Ω r σ)` as an intermediate fact. Rewrite `this` using `[Matrix.map_mul, gen_map u hu σ, Matrix.map_map]`.

Establish `e : (⇑(MvPolynomial.aeval (R` using `Ω) (ent u)).toRingHom ∘ ⇑MvPolynomial.C) = algebraMap Ω F := by`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Rewrite `this` using `[e]`. Conclude with `this`.

Introduce `h0`. Rewrite `h0` using `[key F u hu, map_eq_zero_iff _ hi]`. Conclude with `hw' σ k (by rw [key _ w hw, h0, map_zero])`.
-/
theorem general_of_indep {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hi : AlgebraicIndependent Ω (ent u)) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω)
    (hg : ∀ σ, (g σ).det ≠ 0) (σ : S) (k : Fin (r σ)) :
    (trunc k ((g σ).map (algebraMap Ω F) * u σ)).det ≠ 0 := by
  choose w hw hw' using fun σ => exists_general (g σ) (hg σ)
  have key : ∀ (F : Type) [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F),
      (∀ σ, Uni (u σ)) → (trunc k ((g σ).map (algebraMap Ω F) * u σ)).det =
        MvPolynomial.aeval (R := Ω) (ent u) (trunc k ((g σ).map MvPolynomial.C * gen Ω r σ)).det := by
    intro F _ _ u hu
    have := det_trunc_map (MvPolynomial.aeval (R := Ω) (ent u)).toRingHom k ((g σ).map MvPolynomial.C * gen Ω r σ)
    rw [Matrix.map_mul, gen_map u hu σ, Matrix.map_map] at this
    have e : (⇑(MvPolynomial.aeval (R := Ω) (ent u)).toRingHom ∘ ⇑MvPolynomial.C) = algebraMap Ω F := by
      funext a
      simp
    rw [e] at this
    exact this
  intro h0
  rw [key F u hu, map_eq_zero_iff _ hi] at h0
  exact hw' σ k (by rw [key _ w hw, h0, map_zero])

/- English proof (translation)
Break down `lt_trichotomy l k with h | h | h` into its components or cases. Rewrite using `[(hu σ).2 l k h]`. Conclude with `zero_mem _`. Rewrite using `[h, (hu σ).1]`. Conclude with `one_mem _`.

Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l, k), h⟩⟩, rfl⟩`.
-/
theorem mem_adjoin_ent {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (σ : S) (l k : Fin (r σ)) : u σ l k ∈ IntermediateField.adjoin Ω (Set.range (ent u)) := by
  rcases lt_trichotomy l k with h | h | h
  · rw [(hu σ).2 l k h]; exact zero_mem _
  · rw [h, (hu σ).1]; exact one_mem _
  · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l, k), h⟩⟩, rfl⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `mem_adjoin_ent u hu _ _ _`. Apply `IntermediateField.adjoin.mono` to reduce the goal to its premises.

Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `⟨⟨q.1, q.2.1⟩, rfl⟩`.
-/
theorem adjoin_all {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) :
    IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω (Set.range (ent u)) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    exact mem_adjoin_ent u hu _ _ _
  · apply IntermediateField.adjoin.mono
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨q.1, q.2.1⟩, rfl⟩

/- English proof (translation)
Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨q, rfl⟩`. Use `lu_mem (IntermediateField.adjoin Ω (Set.range (ent u))).toSubfield (hC q.1) (e q.1 ▸ hu' q.1) (fun i j => by` as an intermediate fact. Rewrite using `[mul_apply]`. Conclude with `sum_mem fun l _ => mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_ent u hu _ _ _))`.

Rewrite `this` using `[← e q.1]`. Conclude with `this _ _`.
-/
theorem adjoin_le {F : Type} [Field F] [Algebra Ω F] (u u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hu' : ∀ σ, Uni (u' σ)) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω)
    (C : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F) (hC : ∀ σ, Up (C σ))
    (e : ∀ σ, u' σ = (g σ).map (algebraMap Ω F) * u σ * C σ) :
    IntermediateField.adjoin Ω (Set.range (ent u')) ≤ IntermediateField.adjoin Ω (Set.range (ent u)) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨q, rfl⟩
  have := lu_mem (IntermediateField.adjoin Ω (Set.range (ent u))).toSubfield (hC q.1) (e q.1 ▸ hu' q.1)
    (fun i j => by
      rw [mul_apply]
      exact sum_mem fun l _ => mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_ent u hu _ _ _))
  rw [← e q.1] at this
  exact this _ _

/- English proof (translation)
Use `choose C hC hU using fun σ => exists_lu _ (general_of_indep u hu hi g hg σ)`. Establish `hC0` using `fun σ => (dets_of_lu (hC σ) (hU σ)).2.1`. Set `u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F` to `fun σ => (g σ).map (algebraMap Ω F) * u σ * C σ`. Establish `heq : IntermediateField.adjoin Ω (Set.range (ent u')) = IntermediateField.adjoin Ω (Set.range (ent u))`. Use `le_antisymm (adjoin_le u u' hu hU g C hC fun _ => rfl) (adjoin_le u' u hU hu (fun σ => (g σ)⁻¹) (fun σ => (C σ)⁻¹) (fun σ => (hC σ).inv (hC0 σ)) fun σ => ?_)` and prove the remaining obligations.

Simplify using `only [u']`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (hC0 σ)), Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.map_mul, nonsing_inv_mul _ (IsUnit.mk0 _ (hg σ)), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`. Use `⟨u', hU, ?_, heq, fun σ i => fl_mul _ _ (hC σ) (hC0 σ) i⟩` and prove the remaining obligations. Establish `a1 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u))) F` using `inferInstance`. Establish `a2 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u'))) F` using `by rw [heq]; exact a1`.

Rewrite `a1`, `a2` using `[IntermediateField.isAlgebraic_adjoin_iff_top]`. Establish `b1` using `hi.isTranscendenceBasis_iff_isAlgebraic.2 a1`. Conclude with `(Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω (ent u') b1.cardinalMk_eq_trdeg.le).1`.
-/
theorem change [Finite S] {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hi : AlgebraicIndependent Ω (ent u))
    (hf : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (ent u))) F)
    (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω) (hg : ∀ σ, (g σ).det ≠ 0) :
    ∃ u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F, (∀ σ, Uni (u' σ)) ∧ AlgebraicIndependent Ω (ent u') ∧
      IntermediateField.adjoin Ω (Set.range (ent u')) = IntermediateField.adjoin Ω (Set.range (ent u)) ∧
      ∀ σ i, fl (u' σ) i = fl ((g σ).map (algebraMap Ω F) * u σ) i := by
  choose C hC hU using fun σ => exists_lu _ (general_of_indep u hu hi g hg σ)
  have hC0 := fun σ => (dets_of_lu (hC σ) (hU σ)).2.1
  let u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F := fun σ => (g σ).map (algebraMap Ω F) * u σ * C σ
  have heq : IntermediateField.adjoin Ω (Set.range (ent u')) = IntermediateField.adjoin Ω (Set.range (ent u)) := by
    refine le_antisymm (adjoin_le u u' hu hU g C hC fun _ => rfl)
      (adjoin_le u' u hU hu (fun σ => (g σ)⁻¹) (fun σ => (C σ)⁻¹) (fun σ => (hC σ).inv (hC0 σ)) fun σ => ?_)
    simp only [u']
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (hC0 σ)), Matrix.mul_one,
      ← Matrix.mul_assoc, ← Matrix.map_mul, nonsing_inv_mul _ (IsUnit.mk0 _ (hg σ)),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  refine ⟨u', hU, ?_, heq, fun σ i => fl_mul _ _ (hC σ) (hC0 σ) i⟩
  have a1 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u))) F := inferInstance
  have a2 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u'))) F := by rw [heq]; exact a1
  rw [IntermediateField.isAlgebraic_adjoin_iff_top] at a1 a2
  have b1 := hi.isTranscendenceBasis_iff_isAlgebraic.2 a1
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω (ent u') b1.cardinalMk_eq_trdeg.le).1

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (TensorProduct K Ω₁ Ω₂)`. Set `Ω₃` to `TensorProduct K Ω₁ Ω₂ ⧸ M`. Set `_ : Field Ω₃` to `Ideal.Quotient.field M`. Establish `fin : FiniteDimensional K Ω₃` using `Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)`. Set `j₁ : Ω₁ →ₐ[K] Ω₃` to `(Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeLeft`.

Set `j₂ : Ω₂ →ₐ[K] Ω₃` to `(Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeRight`. Establish `e₁` using `Module.finrank_mul_finrank K j₁.fieldRange Ω₃`. Establish `e₂` using `Module.finrank_mul_finrank K j₂.fieldRange Ω₃`. Establish `q₁ : Module.finrank K Ω₁ = Module.finrank K j₁.fieldRange` using `(AlgEquiv.ofInjectiveField j₁).toLinearEquiv.finrank_eq`. Establish `q₂ : Module.finrank K Ω₂ = Module.finrank K j₂.fieldRange` using `(AlgEquiv.ofInjectiveField j₂).toLinearEquiv.finrank_eq`.

Rewrite `e₁` using `[← q₁]`. Rewrite `e₂` using `[← q₂]`. Use `⟨Ω₃, inferInstance, j₁.toRingHom, j₂.toRingHom, fun x => (j₁.commutes x).trans (j₂.commutes x).symm, Module.finrank j₁.fieldRange Ω₃, Module.finrank j₂.fieldRange Ω₃, Module.finrank_pos, ?_, rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[mul_comm, e₁, mul_comm, e₂]`.
-/
theorem compositum (K Ω₁ Ω₂ : Type) [Field K] [Field Ω₁] [Field Ω₂] [Algebra K Ω₁] [Algebra K Ω₂]
    [FiniteDimensional K Ω₁] [FiniteDimensional K Ω₂] :
    ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃),
      (∀ x, i₁ (algebraMap K Ω₁ x) = i₂ (algebraMap K Ω₂ x)) ∧
      ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * Module.finrank K Ω₁ = n₂ * Module.finrank K Ω₂ ∧
        Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂ := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct K Ω₁ Ω₂)
  let Ω₃ := TensorProduct K Ω₁ Ω₂ ⧸ M
  let _ : Field Ω₃ := Ideal.Quotient.field M
  have fin : FiniteDimensional K Ω₃ :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  let j₁ : Ω₁ →ₐ[K] Ω₃ := (Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeLeft
  let j₂ : Ω₂ →ₐ[K] Ω₃ := (Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeRight
  have e₁ := Module.finrank_mul_finrank K j₁.fieldRange Ω₃
  have e₂ := Module.finrank_mul_finrank K j₂.fieldRange Ω₃
  have q₁ : Module.finrank K Ω₁ = Module.finrank K j₁.fieldRange :=
    (AlgEquiv.ofInjectiveField j₁).toLinearEquiv.finrank_eq
  have q₂ : Module.finrank K Ω₂ = Module.finrank K j₂.fieldRange :=
    (AlgEquiv.ofInjectiveField j₂).toLinearEquiv.finrank_eq
  rw [← q₁] at e₁
  rw [← q₂] at e₂
  refine ⟨Ω₃, inferInstance, j₁.toRingHom, j₂.toRingHom, fun x => (j₁.commutes x).trans (j₂.commutes x).symm,
    Module.finrank j₁.fieldRange Ω₃, Module.finrank j₂.fieldRange Ω₃, Module.finrank_pos, ?_, rfl, rfl⟩
  rw [mul_comm, e₁, mul_comm, e₂]

/- English proof (translation)
Set `K₁` to `IntermediateField.adjoin Ω (Set.range x₁)`. Set `K₂` to `IntermediateField.adjoin Ω (Set.range x₂)`. Set `e : K₁ ≃ₐ[Ω] K₂` to `h₁.aevalEquivField.symm.trans h₂.aevalEquivField`. Set `_ : Algebra K₁ Ω₂` to `((algebraMap K₂ Ω₂).comp e.toRingEquiv.toRingHom).toAlgebra`. Establish `hr : Module.finrank K₁ Ω₂ = Module.finrank K₂ Ω₂` using `Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl _) rfl`.

Establish `: FiniteDimensional K₁ Ω₂` using `Module.finite_of_finrank_pos (by rw [hr]; exact Module.finrank_pos)`. Take `⟨Ω₃, _, i₁, i₂, h, n₁, n₂, hn, e', e₁, e₂⟩` from `compositum K₁ Ω₁ Ω₂`. Use `⟨Ω₃, inferInstance, i₁, i₂, fun a => ?_, fun q => ?_, n₁, n₂, hn, hr ▸ e', e₁, e₂⟩` and prove the remaining obligations. Use `(h (algebraMap Ω K₁ a)).trans ?_` and prove the remaining obligations. Use `congr 1`.

Express the relevant statement in the definitionally equal form `((e (algebraMap Ω K₁ a) : K₂) : Ω₂) = _`. Rewrite using `[e.commutes]`. Both sides reduce to the same expression. Use `h (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)))` as an intermediate fact. Express the relevant statement in the definitionally equal form `i₁ (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) : Ω₁) = i₂ (e (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))) : Ω₂) at this`.

Simplify using `only [e, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] at this`. Rewrite `this` using `[h₁.aevalEquivField_algebraMap_apply_coe, h₂.aevalEquivField_algebraMap_apply_coe]`. Simplify using `using this`.
-/
theorem compositum' {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [Algebra Ω Ω₁] [Algebra Ω Ω₂] {I : Type}
    (x₁ : I → Ω₁) (x₂ : I → Ω₂) (h₁ : AlgebraicIndependent Ω x₁) (h₂ : AlgebraicIndependent Ω x₂)
    (f₁ : FiniteDimensional (IntermediateField.adjoin Ω (Set.range x₁)) Ω₁)
    (f₂ : FiniteDimensional (IntermediateField.adjoin Ω (Set.range x₂)) Ω₂) :
    ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃),
      (∀ a, i₁ (algebraMap Ω Ω₁ a) = i₂ (algebraMap Ω Ω₂ a)) ∧ (∀ q, i₁ (x₁ q) = i₂ (x₂ q)) ∧
      ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * Module.finrank (IntermediateField.adjoin Ω (Set.range x₁)) Ω₁ =
          n₂ * Module.finrank (IntermediateField.adjoin Ω (Set.range x₂)) Ω₂ ∧
        Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂ := by
  let K₁ := IntermediateField.adjoin Ω (Set.range x₁)
  let K₂ := IntermediateField.adjoin Ω (Set.range x₂)
  let e : K₁ ≃ₐ[Ω] K₂ := h₁.aevalEquivField.symm.trans h₂.aevalEquivField
  let _ : Algebra K₁ Ω₂ := ((algebraMap K₂ Ω₂).comp e.toRingEquiv.toRingHom).toAlgebra
  have hr : Module.finrank K₁ Ω₂ = Module.finrank K₂ Ω₂ :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl _) rfl
  have : FiniteDimensional K₁ Ω₂ := Module.finite_of_finrank_pos (by rw [hr]; exact Module.finrank_pos)
  obtain ⟨Ω₃, _, i₁, i₂, h, n₁, n₂, hn, e', e₁, e₂⟩ := compositum K₁ Ω₁ Ω₂
  refine ⟨Ω₃, inferInstance, i₁, i₂, fun a => ?_, fun q => ?_, n₁, n₂, hn, hr ▸ e', e₁, e₂⟩
  · refine (h (algebraMap Ω K₁ a)).trans ?_
    congr 1
    change ((e (algebraMap Ω K₁ a) : K₂) : Ω₂) = _
    rw [e.commutes]
    rfl
  · have := h (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)))
    change i₁ (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) : Ω₁) =
      i₂ (e (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))) : Ω₂) at this
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] at this
    rw [h₁.aevalEquivField_algebraMap_apply_coe, h₂.aevalEquivField_algebraMap_apply_coe] at this
    simpa using this

/- English proof (translation)
Use `fl_of_indep hc' ?_` and prove the remaining obligations. Rewrite using `[← hf]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [hb, hh, map_sum, hj, Finset.smul_sum, smul_smul, mul_apply, map_apply, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_comm]`.
-/
theorem fl_coord {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E']
    [Module Ω' E'] (j : E →+ E') (hj : ∀ (a : Ω) e, j (a • e) = algebraMap Ω Ω' a • j e) {n : ℕ} {c c' : Fin n → E}
    (hc' : LinearIndependent Ω' fun k => j (c' k)) {h : Matrix (Fin n) (Fin n) Ω} (hh : ∀ k, c k = ∑ l, h l k • c' l)
    {b : Fin n → E'} {m u : Matrix (Fin n) (Fin n) Ω'} (hb : ∀ k, b k = ∑ l, m l k • j (c l)) {i : ℕ}
    (hf : flagStep Ω' b i = flagStep Ω' (fun k => ∑ l, u l k • j (c' l)) i) :
    fl (h.map (algebraMap Ω Ω') * m) i = fl u i := by
  refine fl_of_indep hc' ?_
  rw [← hf]
  congr 1
  funext k
  simp only [hb, hh, map_sum, hj, Finset.smul_sum, smul_smul, mul_apply, map_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end PositivityTheory.UnitarySelfGeneration.GF
