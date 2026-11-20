import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralUnitRootNormOneAdeleStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

noncomputable section

namespace GlobalTheory.AdLat.RootNear

/- English proof (translation)
Introduce `V hV`. Establish `: ContinuousAdd R` using `IsModuleTopology.toContinuousAdd A R`. Establish `hM : Continuous (fun x : R => Algebra.leftMulMatrix b x)` using `IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap`. Establish `hb : Continuous (b.equivFun.symm)` using `IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap`. Set `d : R → A` to `fun x => (Algebra.leftMulMatrix b x).det`.

Set `adj : R → R` to `fun x => b.equivFun.symm ((Algebra.leftMulMatrix b x).adjugate *ᵥ b.equivFun 1)`. Establish `hd : Continuous d` using `hM.matrix_det`. Establish `hadj : Continuous adj` using `hb.comp (hM.matrix_adjugate.matrix_mulVec continuous_const)`. Establish `hd1 : d 1 = 1` using `by simp [d]`. Establish `hadj1 : adj 1 = 1` using `by simp [adj]`.

Establish `key : ∀ x, x * adj x = d x • (1 : R)`. Introduce `x`. Apply `b.equivFun.injective` to reduce the goal to its premises. Establish `h1 : ∀ y : R, b.equivFun (x * y) = Algebra.leftMulMatrix b x *ᵥ b.equivFun y`. Introduce `y`.

Use `Algebra.leftMulMatrix_mulVec_repr b x y` as an intermediate fact. Simplify using `using this.symm`. Rewrite using `[h1, map_smul]`. Simplify using `only [adj, d, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `hdt : Filter.Tendsto d (𝓝 1) (𝓝 1)`.

Use `hd.tendsto 1` as an intermediate fact. Rewrite `this` using `[hd1]`. Then use the resulting hypothesis. Establish `hy : Filter.Tendsto (fun x => i (d x) • adj x) (𝓝 1) (𝓝 1)`. Establish `h1 : Filter.Tendsto (fun x => i (d x)) (𝓝 1) (𝓝 1)`. Use `hi.tendsto` as an intermediate fact.

Rewrite `this` using `[hi1]`. Conclude with `this.comp hdt`. Establish `h2` using `h1.smul (hadj.tendsto 1)`. Simplify `h2` using `[hadj1]`. Use `filter_upwards [hy hV, hdt hii] with x h1 h2`.

Use `⟨_, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul_comm, key, smul_smul, mul_comm, h2, one_smul]`.
-/
theorem inv_near {A R ι : Type} [CommRing A] [CommRing R] [Algebra A R] [TopologicalSpace A]
    [IsTopologicalRing A] [TopologicalSpace R] [IsModuleTopology A R] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A R) (i : A → A) (hi : ContinuousAt i 1) (hi1 : i 1 = 1)
    (hii : ∀ᶠ a in 𝓝 (1 : A), a * i a = 1) :
    ∀ V ∈ 𝓝 (1 : R), ∀ᶠ x in 𝓝 (1 : R), ∃ y ∈ V, x * y = 1 := by
  intro V hV
  have : ContinuousAdd R := IsModuleTopology.toContinuousAdd A R
  have hM : Continuous (fun x : R => Algebra.leftMulMatrix b x) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hb : Continuous (b.equivFun.symm) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  let d : R → A := fun x => (Algebra.leftMulMatrix b x).det
  let adj : R → R := fun x => b.equivFun.symm ((Algebra.leftMulMatrix b x).adjugate *ᵥ b.equivFun 1)
  have hd : Continuous d := hM.matrix_det
  have hadj : Continuous adj := hb.comp (hM.matrix_adjugate.matrix_mulVec continuous_const)
  have hd1 : d 1 = 1 := by simp [d]
  have hadj1 : adj 1 = 1 := by simp [adj]
  have key : ∀ x, x * adj x = d x • (1 : R) := by
    intro x
    apply b.equivFun.injective
    have h1 : ∀ y : R, b.equivFun (x * y) = Algebra.leftMulMatrix b x *ᵥ b.equivFun y := by
      intro y
      have := Algebra.leftMulMatrix_mulVec_repr b x y
      simpa using this.symm
    rw [h1, map_smul]
    simp only [adj, d, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdt : Filter.Tendsto d (𝓝 1) (𝓝 1) := by
    have := hd.tendsto 1
    rwa [hd1] at this
  have hy : Filter.Tendsto (fun x => i (d x) • adj x) (𝓝 1) (𝓝 1) := by
    have h1 : Filter.Tendsto (fun x => i (d x)) (𝓝 1) (𝓝 1) := by
      have := hi.tendsto
      rw [hi1] at this
      exact this.comp hdt
    have h2 := h1.smul (hadj.tendsto 1)
    simpa [hadj1] using h2
  filter_upwards [hy hV, hdt hii] with x h1 h2
  refine ⟨_, h1, ?_⟩
  rw [mul_smul_comm, key, smul_smul, mul_comm, h2, one_smul]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨M, hM, hx⟩` from `exists_max_ideal_of_mem_nonunits h`. Establish `hm` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hφ M`. Establish `hjm : j ∈ M.comap φ`. Establish `: j ∈ Ideal.jacobson (⊥ : Ideal A)`.

Rewrite using `[Ideal.mem_jacobson_bot]`. Introduce `y`. Rewrite using `[add_comm]`. Conclude with `hj y`. Conclude with `Ideal.mem_sInf.1 this ⟨bot_le, hm⟩`.

Apply `hM.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Use `M.sub_mem hx (M.mul_mem_right z (Ideal.mem_comap.1 hjm))` as an intermediate fact. Simplify using `using this`.
-/
theorem unit_of_integral {A O : Type} [CommRing A] [CommRing O] (φ : A →+* O) (hφ : φ.IsIntegral) (j : A)
    (hj : ∀ a, IsUnit (1 + j * a)) (z : O) : IsUnit (1 + φ j * z) := by
  by_contra h
  obtain ⟨M, hM, hx⟩ := exists_max_ideal_of_mem_nonunits h
  have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hφ M
  have hjm : j ∈ M.comap φ := by
    have : j ∈ Ideal.jacobson (⊥ : Ideal A) := by
      rw [Ideal.mem_jacobson_bot]
      intro y
      rw [add_comm]; exact hj y
    exact Ideal.mem_sInf.1 this ⟨bot_le, hm⟩
  apply hM.ne_top
  rw [Ideal.eq_top_iff_one]
  have := M.sub_mem hx (M.mul_mem_right z (Ideal.mem_comap.1 hjm))
  simpa using this

/- English proof (translation)
Use `⟨fun v => if IsUnit (n : O v) then 0 else 1, fun v => if IsUnit (n : O v) then Ring.inverse (n : O v) else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Apply the tactic sequence `by_cases h : IsUnit (n : O v) <;> simp [h]`. Use function extensionality and compare the values at `v`. Apply the tactic sequence `by_cases h : IsUnit (n : O v) <;> simp [h, Ring.mul_inverse_cancel]`.

Introduce `a`. Rewrite using `[Pi.isUnit_iff]`. Introduce `v`. Distinguish the cases in `h : IsUnit (n : O v)`. Simplify using `[h]`.

Establish `h2 : -((n : O v) * a v) ∈ nonunits (O v)`. Introduce `h3`. Conclude with `h (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h3))`. Simplify `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h2` using `[h]`.
-/
theorem exists_idem {ι : Type} (O : ι → Type) [∀ v, CommRing (O v)] [∀ v, IsLocalRing (O v)] (n : ℕ) :
    ∃ e f : ∀ v, O v, e * e = e ∧ 1 - e = n * f ∧ ∀ a, IsUnit (1 + e * n * a) := by
  classical
  refine ⟨fun v => if IsUnit (n : O v) then 0 else 1,
    fun v => if IsUnit (n : O v) then Ring.inverse (n : O v) else 0, ?_, ?_, ?_⟩
  · funext v
    by_cases h : IsUnit (n : O v) <;> simp [h]
  · funext v
    by_cases h : IsUnit (n : O v) <;> simp [h, Ring.mul_inverse_cancel]
  · intro a
    rw [Pi.isUnit_iff]
    intro v
    by_cases h : IsUnit (n : O v)
    · simp [h]
    · have h2 : -((n : O v) * a v) ∈ nonunits (O v) := by
        intro h3
        exact h (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h3))
      simpa [h] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h2

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def incl : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := (⟨fun v => (a v : v.adicCompletion F), Filter.Eventually.of_forall fun v => (a v).2⟩ :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => v.adicCompletionIntegers F) Filter.cofinite)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [NumberField E] in
/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩`.
-/
theorem tmul_mem (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (x : 𝓞 E) :
    a ⊗ₜ[F] (algebraMap (𝓞 E) E x) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
  AddSubgroup.subset_closure ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `ha, hb using AddSubgroup.closure_induction₂ with`. Consider the case `mem x y hx hy`. Take `⟨a, ha, _, ⟨s, rfl⟩, rfl⟩` from `hx`. Take `⟨b, hb, _, ⟨t, rfl⟩, rfl⟩` from `hy`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]`.

Conclude with `tmul_mem F E (a * b) (fun v => (v.adicCompletionIntegers F).mul_mem _ _ (ha v) (hb v)) (s * t)`. Consider the case `zero_left x hx => rw [zero_mul]`. Conclude with `AddSubgroup.zero_mem _`. Consider the case `zero_right x hx => rw [mul_zero]`. Conclude with `AddSubgroup.zero_mem _`.

Consider the case `add_left x y z _ _ _ h1 h2 => rw [add_mul]`. Conclude with `AddSubgroup.add_mem _ h1 h2`. Consider the case `add_right x y z _ _ _ h1 h2 => rw [mul_add]`. Conclude with `AddSubgroup.add_mem _ h1 h2`. Consider the case `neg_left x y _ _ h => rw [neg_mul]`.

Conclude with `AddSubgroup.neg_mem _ h`. Consider the case `neg_right x y _ _ h => rw [mul_neg]`. Conclude with `AddSubgroup.neg_mem _ h`.
-/
theorem mul_mem_hat {a b : RA F E} (ha : a ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hb : b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) : a * b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  induction ha, hb using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
    obtain ⟨b, hb, _, ⟨t, rfl⟩, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
    exact tmul_mem F E (a * b) (fun v => (v.adicCompletionIntegers F).mul_mem _ _ (ha v) (hb v)) (s * t)
  | zero_left x hx => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | zero_right x hx => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact AddSubgroup.add_mem _ h1 h2
  | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
  | neg_left x y _ _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h
  | neg_right x y _ _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h

def intHat : Subring (RA F E) where
  carrier := hat1 F (Set.range (algebraMap (𝓞 E) E))
  add_mem' := AddSubgroup.add_mem _
  zero_mem' := AddSubgroup.zero_mem _
  neg_mem' := AddSubgroup.neg_mem _
  one_mem' := by
    have := tmul_mem F E 1 (fun v => one_mem _) 1
    rw [map_one] at this
    exact this
  mul_mem' := mul_mem_hat F E

def inclHat : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* intHat F E :=
  ((Algebra.TensorProduct.includeLeftRingHom : FiniteAdeleRing (𝓞 F) F →+* RA F E).comp (incl F)).codRestrict
    (intHat F E) (fun a => by
      have := tmul_mem F E (incl F a) (fun v => (a v).2) 1
      rw [map_one] at this
      exact this)

def ratHat : 𝓞 E →+* intHat F E :=
  ((Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict
    (intHat F E) (fun x => tmul_mem F E 1 (fun v => one_mem _) x)

/- English proof (translation)
Use `letI := (inclHat F E).toAlgebra`. Introduce and unpack `⟨z, hz⟩`. Express the relevant statement in the definitionally equal form `IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (⟨z, hz⟩ : intHat F E)`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`.

Take `⟨a, ha, _, ⟨s, rfl⟩, rfl⟩` from `hx`. Establish `h1 : IsIntegral ℤ (ratHat F E s)` using `(RingOfIntegers.isIntegral s).map (ratHat F E).toIntAlgHom`. Establish `h2 : IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (ratHat F E s)` using `h1.tower_top`. Establish `h3` using `(isIntegral_algebraMap (A := intHat F E) (x := (fun v => ⟨a v, ha v⟩ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F))).mul h2`. Use `Eq.mpr (congrArg (IsIntegral _) (Subtype.ext ?_)) h3` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = (a ⊗ₜ[F] (1 : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E s))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Consider the case `zero => exact isIntegral_zero`. Consider the case `add x y _ _ h1 h2 => exact h1.add h2`. Consider the case `neg x _ h => exact h.neg`.
-/
theorem inclHat_integral : (inclHat F E).IsIntegral := by
  letI := (inclHat F E).toAlgebra
  rintro ⟨z, hz⟩
  change IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (⟨z, hz⟩ : intHat F E)
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
    have h1 : IsIntegral ℤ (ratHat F E s) :=
      (RingOfIntegers.isIntegral s).map (ratHat F E).toIntAlgHom
    have h2 : IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (ratHat F E s) :=
      h1.tower_top
    have h3 := (isIntegral_algebraMap (A := intHat F E)
      (x := (fun v => ⟨a v, ha v⟩ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F))).mul h2
    refine Eq.mpr (congrArg (IsIntegral _) (Subtype.ext ?_)) h3
    change _ = (a ⊗ₜ[F] (1 : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E s))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | zero => exact isIntegral_zero
  | add x y _ _ h1 h2 => exact h1.add h2
  | neg x _ h => exact h.neg

omit [NumberField E] in
/- English proof (translation)
Establish `h2 : IsUnit (2 : A ⊗[F] E)`. Use `(IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (A ⊗[F] E))` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Apply `h2.mul_left_cancel` to reduce the goal to its premises. Use `congrArg (sg A c) hx` as an intermediate fact.

Rewrite `this` using `[map_mul, map_ofNat, map_add, map_one]`. Take the linear combination `hx - u * this - hu`.
-/
theorem half_root {A : Type} [CommRing A] [Algebra F A] (c : E ≃ₐ[F] E) (u x : A ⊗[F] E)
    (hu : u * sg A c u = 1) (hx : 2 * x = 1 + u) : x = u * sg A c x := by
  have h2 : IsUnit (2 : A ⊗[F] E) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (A ⊗[F] E))
    rwa [map_ofNat] at this
  apply h2.mul_left_cancel
  have := congrArg (sg A c) hx
  rw [map_mul, map_ofNat, map_add, map_one] at this
  linear_combination hx - u * this - hu

/- English proof (translation)
Establish `hu1 : u = 1 + 2 * n * z`. Rewrite `huz` using `[nsmul_eq_mul]`. Move the coercions through the operations in `at huz`. Take the linear combination `huz`. Establish `huO : u ∈ intHat F E`.

Rewrite using `[hu1]`. Conclude with `add_mem (one_mem _) (mul_mem (mul_mem (ofNat_mem _ 2) (natCast_mem _ n)) hz)`. Take `⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩` from `GlobalTheory.T.exists_integral_unit_root_norm_one_adele F E c h2 hc hP u huO hu`. Take `⟨e, f, hee, hef, hun⟩` from `exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n`. Take `⟨y₀, hy₀⟩` from `(unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun ⟨z, hz⟩).exists_right_inv`.

Establish `hr₀ : (1 + n * z) = u * sg (FiniteAdeleRing (𝓞 F) F) c (1 + n * z)` using `half_root F E c u _ hu (by rw [hu1]; ring)`. Establish `hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E)`. Express the relevant statement in the definitionally equal form `sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)`. Simplify using `[sg]`. Establish `hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e`.

Rewrite using `[← Subring.coe_mul, ← map_mul, hee]`. Establish `hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f`. Use `congrArg (fun t => (inclHat F E t : RA F E)) hef` as an intermediate fact. Simplify using `using this`. Establish `hy₀' : (1 + (inclHat F E e : RA F E) * n * z) * y₀ = 1`.

Use `congrArg (fun t : intHat F E => (t : RA F E)) hy₀` as an intermediate fact. Simplify using `using this`. Establish `heO` using `(inclHat F E e).2`. Establish `hfO` using `(inclHat F E f).2`. Establish `hy₀O` using `y₀.2`.

Generalize the expression as in `(inclHat F E e : RA F E) = e' at *`. Generalize the expression as in `(inclHat F E f : RA F E) = f' at *`. Generalize the expression as in `(y₀ : RA F E) = y' at *`. Establish `hx₁' : x₁ ∈ intHat F E` using `hx₁`. Establish `hy₁' : y₁ ∈ intHat F E` using `hy₁`.

Establish `hxy : (e' * (1 + n * z) + (1 - e') * x₁) * (e' * y' + (1 - e') * y₁) = 1`. Take the linear combination `e' * hy₀' + (1 - e') * hxy₁ + (y' - (1 + n * z) * y₁ - x₁ * y' + x₁ * y₁) * hee'`. Establish `hp : e' * z + f' * (x₁ - 1) ∈ intHat F E` using `add_mem (mul_mem heO hz) (mul_mem hfO (sub_mem hx₁' (one_mem _)))`. Establish `hx : e' * (1 + n * z) + (1 - e') * x₁ = 1 + n * (e' * z + f' * (x₁ - 1))`. Take the linear combination `(x₁ - 1) * hef'`.

Use `⟨_, _, hxy, ?_, ⟨_, hp, by rw [nsmul_eq_mul]; exact hx⟩, -((e' * y' + (1 - e') * y₁) * (e' * z + f' * (x₁ - 1))), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_sub, map_one, hse]`. Take the linear combination `e' * hr₀ + (1 - e') * hr₁`. Conclude with `neg_mem (mul_mem (add_mem (mul_mem heO hy₀O) (mul_mem (sub_mem (one_mem _) heO) hy₁')) hp)`. Rewrite using `[nsmul_eq_mul]`.

Rewrite `hxy` using `[hx]`. Take the linear combination `hxy`.
-/
theorem finite_root (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) (n : ℕ)
    (u z : RA F E) (hz : z ∈ intHat F E) (huz : u - 1 = (2 * n) • z)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) :
    ∃ x y : RA F E, x * y = 1 ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x ∧
      (∃ p ∈ intHat F E, x = 1 + n • p) ∧ ∃ p ∈ intHat F E, y = 1 + n • p := by
  have hu1 : u = 1 + 2 * n * z := by
    rw [nsmul_eq_mul] at huz
    push_cast at huz
    linear_combination huz
  have huO : u ∈ intHat F E := by
    rw [hu1]
    exact add_mem (one_mem _) (mul_mem (mul_mem (ofNat_mem _ 2) (natCast_mem _ n)) hz)
  obtain ⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩ := GlobalTheory.T.exists_integral_unit_root_norm_one_adele F E c h2 hc hP u huO hu
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n
  obtain ⟨y₀, hy₀⟩ := (unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun ⟨z, hz⟩).exists_right_inv
  have hr₀ : (1 + n * z) = u * sg (FiniteAdeleRing (𝓞 F) F) c (1 + n * z) :=
    half_root F E c u _ hu (by rw [hu1]; ring)
  have hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E) := by
    change sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)
    simp [sg]
  have hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e := by
    rw [← Subring.coe_mul, ← map_mul, hee]
  have hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hef
    simpa using this
  have hy₀' : (1 + (inclHat F E e : RA F E) * n * z) * y₀ = 1 := by
    have := congrArg (fun t : intHat F E => (t : RA F E)) hy₀
    simpa using this
  have heO := (inclHat F E e).2
  have hfO := (inclHat F E f).2
  have hy₀O := y₀.2
  generalize (inclHat F E e : RA F E) = e' at *
  generalize (inclHat F E f : RA F E) = f' at *
  generalize (y₀ : RA F E) = y' at *
  have hx₁' : x₁ ∈ intHat F E := hx₁
  have hy₁' : y₁ ∈ intHat F E := hy₁
  have hxy : (e' * (1 + n * z) + (1 - e') * x₁) * (e' * y' + (1 - e') * y₁) = 1 := by
    linear_combination e' * hy₀' + (1 - e') * hxy₁ +
      (y' - (1 + n * z) * y₁ - x₁ * y' + x₁ * y₁) * hee'
  have hp : e' * z + f' * (x₁ - 1) ∈ intHat F E :=
    add_mem (mul_mem heO hz) (mul_mem hfO (sub_mem hx₁' (one_mem _)))
  have hx : e' * (1 + n * z) + (1 - e') * x₁ = 1 + n * (e' * z + f' * (x₁ - 1)) := by
    linear_combination (x₁ - 1) * hef'
  refine ⟨_, _, hxy, ?_, ⟨_, hp, by rw [nsmul_eq_mul]; exact hx⟩,
    -((e' * y' + (1 - e') * y₁) * (e' * z + f' * (x₁ - 1))), ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, map_sub, map_one, hse]
    linear_combination e' * hr₀ + (1 - e') * hr₁
  · exact neg_mem (mul_mem (add_mem (mul_mem heO hy₀O) (mul_mem (sub_mem (one_mem _) heO) hy₁')) hp)
  · rw [nsmul_eq_mul]
    rw [hx] at hxy
    linear_combination hxy

/- English proof (translation)
Use `letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)`. Establish `: IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)` using `⟨rfl⟩`. Establish `: ContinuousAdd (RA F E)` using `IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _`. Introduce `V hV`. Set `L : Submodule (𝓞 E) (Fin 1 → E)` to `Submodule.pi Set.univ (fun _ => LinearMap.range (Algebra.linearMap (𝓞 E) E))`.

Establish `hL : Submodule.span E (L : Set (Fin 1 → E)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `h1 : (fun _ => (1 : E)) ∈ L` using `fun i _ => ⟨1, map_one (algebraMap (𝓞 E) E)⟩`. Establish `h3` using `Submodule.smul_mem _ (v 0) (Submodule.subset_span (R := E) h1)`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using the standard rewrite rules. Take `⟨hopen, hbas⟩` from `GlobalTheory.T.isOpen_nsmul_adelicCompletionOfVectorSet F E 1 L hL`.

Establish `hV0 : {y : RA F E | 1 + y ∈ V} ∈ 𝓝 (0 : RA F E)`. Establish `: Continuous (fun y : RA F E => 1 + y)` using `continuous_const_add 1`. Establish `h` using `this.tendsto 0`. Rewrite `h` using `[add_zero]`. Conclude with `h hV`.

Take `⟨n, hn, hnV⟩` from `hbas _ hV0`. Establish `hhat : ∀ y ∈ hat F (L : Set (Fin 1 → E)), y 0 ∈ intHat F E`. Introduce `y hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem x hx`.

Take `⟨a, ha, w, hw, rfl⟩` from `hx`. Take `⟨s, hs⟩` from `hw 0 (Set.mem_univ _)`. Use `tmul_mem F E a ha s` as an intermediate fact. Express the relevant statement in the definitionally equal form `a ⊗ₜ[F] (w 0) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))`. Rewrite using `[← hs]`.

Conclude with `this`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ h1 h2 => exact add_mem h1 h2`. Consider the case `neg x _ h => exact neg_mem h`. Establish `hcont : Continuous (fun (u : RA F E) (_ : Fin 1) => u + (-1))` using `continuous_pi fun _ => continuous_id.add continuous_const`.

Establish `hN` using `((hopen (2 * n) (by omega)).preimage hcont).mem_nhds (x := 1) ⟨0, zero_mem _, by funext i; simp⟩`. Use `filter_upwards [hN] with u hu hn1`. Take `⟨z, hz, hz2⟩` from `hu`. Establish `hz3 : u - 1 = (2 * n) • z 0`. Rewrite using `[sub_eq_add_neg]`.

Conclude with `congrFun hz2 0`. Take `⟨x, y, hxy, hx, ⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩` from `finite_root F E c h2 hc hP n u (z 0) (hhat z hz) hz3 hn1`. Conclude with `⟨_, hnV p hp, _, hnV q hq, hxy, hx⟩`.
-/
theorem finite_near (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) :
    letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
    ∀ V ∈ 𝓝 (1 : RA F E), ∀ᶠ u in 𝓝 (1 : RA F E), u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1 →
      ∃ x ∈ V, ∃ y ∈ V, x * y = 1 ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by
  letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
  have : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E) := ⟨rfl⟩
  have : ContinuousAdd (RA F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  intro V hV
  let L : Submodule (𝓞 E) (Fin 1 → E) :=
    Submodule.pi Set.univ (fun _ => LinearMap.range (Algebra.linearMap (𝓞 E) E))
  have hL : Submodule.span E (L : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : (fun _ => (1 : E)) ∈ L := fun i _ => ⟨1, map_one (algebraMap (𝓞 E) E)⟩
    have h3 := Submodule.smul_mem _ (v 0) (Submodule.subset_span (R := E) h1)
    convert h3 using 1
    funext i
    rw [Subsingleton.elim i 0]
    simp
  obtain ⟨hopen, hbas⟩ := GlobalTheory.T.isOpen_nsmul_adelicCompletionOfVectorSet F E 1 L hL
  have hV0 : {y : RA F E | 1 + y ∈ V} ∈ 𝓝 (0 : RA F E) := by
    have : Continuous (fun y : RA F E => 1 + y) := continuous_const_add 1
    have h := this.tendsto 0
    rw [add_zero] at h
    exact h hV
  obtain ⟨n, hn, hnV⟩ := hbas _ hV0
  have hhat : ∀ y ∈ hat F (L : Set (Fin 1 → E)), y 0 ∈ intHat F E := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hx
      obtain ⟨s, hs⟩ := hw 0 (Set.mem_univ _)
      have := tmul_mem F E a ha s
      change a ⊗ₜ[F] (w 0) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))
      rw [← hs]
      exact this
    | zero => exact zero_mem _
    | add x y _ _ h1 h2 => exact add_mem h1 h2
    | neg x _ h => exact neg_mem h
  have hcont : Continuous (fun (u : RA F E) (_ : Fin 1) => u + (-1)) :=
    continuous_pi fun _ => continuous_id.add continuous_const
  have hN := ((hopen (2 * n) (by omega)).preimage hcont).mem_nhds (x := 1)
    ⟨0, zero_mem _, by funext i; simp⟩
  filter_upwards [hN] with u hu hn1
  obtain ⟨z, hz, hz2⟩ := hu
  have hz3 : u - 1 = (2 * n) • z 0 := by
    rw [sub_eq_add_neg]
    exact congrFun hz2 0
  obtain ⟨x, y, hxy, hx, ⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩ := finite_root F E c h2 hc hP n u (z 0) (hhat z hz) hz3 hn1
  exact ⟨_, hnV p hp, _, hnV q hq, hxy, hx⟩

/- English proof (translation)
Use `letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)`. Establish `: IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)` using `⟨rfl⟩`. Establish `: ContinuousAdd (InfiniteAdeleRing F ⊗[F] E)` using `IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _`. Introduce `V hV`. Establish `: Module.Finite F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`.

Establish `hev : ∀ v : InfinitePlace F, Continuous (fun a : InfiniteAdeleRing F => a v)` using `fun v => continuous_apply v`. Establish `hinv` using `inv_near (Algebra.TensorProduct.basis (InfiniteAdeleRing F) (Module.finBasis F E)) (fun a v => (a v)⁻¹) (continuousAt_pi.2 fun v => ((hev v).continuousAt (x := 1)).inv₀ (one_ne_zero)) (funext fun v => inv_one) (by`. Establish `: ∀ v : InfinitePlace F, ∀ᶠ a in 𝓝 (1 : InfiniteAdeleRing F), a v ≠ 0` using `fun v => ((hev v).continuousAt (x := 1)).eventually_ne one_ne_zero`. Use `filter_upwards [Filter.eventually_all.2 this] with a ha`. Conclude with `funext fun v => mul_inv_cancel₀ (ha v)) V hV`.

Set `h : InfiniteAdeleRing F` to `algebraMap F _ 2⁻¹`. Establish `hh : ∀ w : InfiniteAdeleRing F ⊗[F] E, 2 * (h • w) = w`. Introduce `w`. Rewrite using `[algebraMap_smul, ← map_ofNat (algebraMap F (InfiniteAdeleRing F ⊗[F] E)) 2, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]`. Establish `hcont : Continuous (fun u : InfiniteAdeleRing F ⊗[F] E => h • (1 + u))` using `(continuous_const.add continuous_id).const_smul h`.

Establish `ht` using `hcont.tendsto 1`. Establish `h11 : h • ((1 : InfiniteAdeleRing F ⊗[F] E) + 1) = 1`. Rewrite using `[smul_add, ← two_mul, hh]`. Rewrite `ht` using `[h11]`. Use `filter_upwards [ht hV, ht hinv] with u h1 h3 hu`.

Take `⟨y, hy, hxy⟩` from `h3`. Conclude with `⟨_, h1, y, hy, hxy, half_root F E c u _ hu (hh _)⟩`.
-/
theorem infinite_near (c : E ≃ₐ[F] E) :
    letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
      moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
    ∀ V ∈ 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E), ∀ᶠ u in 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E),
      u * sg (InfiniteAdeleRing F) c u = 1 →
      ∃ x ∈ V, ∃ y ∈ V, x * y = 1 ∧ x = u * sg (InfiniteAdeleRing F) c x := by
  classical
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  have : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (InfiniteAdeleRing F ⊗[F] E) :=
    IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _
  intro V hV
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hev : ∀ v : InfinitePlace F, Continuous (fun a : InfiniteAdeleRing F => a v) :=
    fun v => continuous_apply v
  have hinv := inv_near (Algebra.TensorProduct.basis (InfiniteAdeleRing F) (Module.finBasis F E))
    (fun a v => (a v)⁻¹)
    (continuousAt_pi.2 fun v => ((hev v).continuousAt (x := 1)).inv₀ (one_ne_zero))
    (funext fun v => inv_one)
    (by
      have : ∀ v : InfinitePlace F, ∀ᶠ a in 𝓝 (1 : InfiniteAdeleRing F), a v ≠ 0 :=
        fun v => ((hev v).continuousAt (x := 1)).eventually_ne one_ne_zero
      filter_upwards [Filter.eventually_all.2 this] with a ha
      exact funext fun v => mul_inv_cancel₀ (ha v)) V hV
  let h : InfiniteAdeleRing F := algebraMap F _ 2⁻¹
  have hh : ∀ w : InfiniteAdeleRing F ⊗[F] E, 2 * (h • w) = w := by
    intro w
    rw [algebraMap_smul, ← map_ofNat (algebraMap F (InfiniteAdeleRing F ⊗[F] E)) 2, ← Algebra.smul_def,
      smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]
  have hcont : Continuous (fun u : InfiniteAdeleRing F ⊗[F] E => h • (1 + u)) :=
    (continuous_const.add continuous_id).const_smul h
  have ht := hcont.tendsto 1
  have h11 : h • ((1 : InfiniteAdeleRing F ⊗[F] E) + 1) = 1 := by
    rw [smul_add, ← two_mul, hh]
  rw [h11] at ht
  filter_upwards [ht hV, ht hinv] with u h1 h3 hu
  obtain ⟨y, hy, hxy⟩ := h3
  exact ⟨_, h1, y, hy, hxy, half_root F E c u _ hu (hh _)⟩

/- English proof (translation)
Rewrite `hW` using `[Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap]`. Take `⟨T, hT, hTW⟩` from `hW`. Rewrite `hT` using `[map_one]`. Take `⟨V₁, h₁, V₂, h₂, hsub⟩` from `mem_nhds_prod_iff.1 hT`. Establish `h₃ : MulOpposite.op ⁻¹' V₂ ∈ 𝓝 (1 : M)` using `MulOpposite.continuous_op.continuousAt.preimage_mem_nhds h₂`.

Conclude with `⟨_, Filter.inter_mem h₁ h₃, fun x hx hy => hTW (hsub ⟨hx.1, hy.2⟩)⟩`.
-/
theorem units_nhds {M : Type} [Monoid M] [TopologicalSpace M] (W : Set Mˣ) (hW : W ∈ 𝓝 (1 : Mˣ)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ x : Mˣ, (x : M) ∈ V → ((x⁻¹ : Mˣ) : M) ∈ V → x ∈ W := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨T, hT, hTW⟩ := hW
  rw [map_one] at hT
  obtain ⟨V₁, h₁, V₂, h₂, hsub⟩ := mem_nhds_prod_iff.1 hT
  have h₃ : MulOpposite.op ⁻¹' V₂ ∈ 𝓝 (1 : M) := MulOpposite.continuous_op.continuousAt.preimage_mem_nhds h₂
  exact ⟨_, Filter.inter_mem h₁ h₃, fun x hx hy => hTW (hsub ⟨hx.1, hy.2⟩)⟩

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => simp [sg]`. Consider the case `add x y h1 h2 => simp only [map_add, h1, h2]`.
-/
theorem map_sg {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (c : E ≃ₐ[F] E)
    (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    Algebra.TensorProduct.map p (AlgHom.id F E) (sg A c z) =
      sg B c (Algebra.TensorProduct.map p (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sg]
  | add x y h1 h2 => simp only [map_add, h1, h2]

/- English proof (translation)
Introduce `F E _ _ _ _ _ c h2 hc hP`. Use `letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)`. Use `letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)`. Use `letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)`. Introduce `W hW`.

Take `⟨V, hV, hVW⟩` from `units_nhds W hW`. Take `⟨e, he, hec, hes⟩` from `GlobalTheory.T.exists_adeleRing_tensor_equiv_infinite_prod_finite F E`. Establish `hs1 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).1 = sg _ c (e z).1` using `fun z => by`. Rewrite using `[(he _).1, (he _).1]`. Conclude with `map_sg F E c _ z`.

Establish `hs2 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).2 = sg _ c (e z).2` using `fun z => by`. Rewrite using `[(he _).2, (he _).2]`. Conclude with `map_sg F E c _ z`. Establish `hV' : e.symm ⁻¹' V ∈ 𝓝 (1 : (InfiniteAdeleRing F ⊗[F] E) × RA F E)` using `hes.continuousAt.preimage_mem_nhds (by rwa [map_one])`. Take `⟨V₁, h₁, V₂, h₂, hsub⟩` from `mem_nhds_prod_iff.1 hV'`.

Establish `ht : Filter.Tendsto (fun u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ => e u) (𝓝 1) (𝓝 1)`. Use `(hec.comp Units.continuous_val).tendsto 1` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `ht1` using `(continuous_fst.tendsto _).comp ht`. Establish `ht2` using `(continuous_snd.tendsto _).comp ht`.

Use `⟨_, Filter.inter_mem (ht1 (infinite_near F E c V₁ h₁)) (ht2 (finite_near F E c h2 hc hP V₂ h₂)), ?_⟩` and prove the remaining obligations. Introduce and unpack `u ⟨hu1, hu2⟩ hu`. Establish `heu` using `congrArg e hu`. Rewrite `heu` using `[map_mul, map_one]`. Take `⟨x₁, hx₁, y₁, hy₁, hxy₁, hr₁⟩` from `hu1 (by`.

Use `congrArg Prod.fst heu` as an intermediate fact. Rewrite `this` using `[Prod.fst_mul, hs1]`. Conclude with `this)`. Take `⟨x₂, hx₂, y₂, hy₂, hxy₂, hr₂⟩` from `hu2 (by`. Use `congrArg Prod.snd heu` as an intermediate fact.

Rewrite `this` using `[Prod.snd_mul, hs2]`. Conclude with `this)`. Establish `hxy : e.symm (x₁, x₂) * e.symm (y₁, y₂) = 1`. Rewrite using `[← map_mul, Prod.mk_mul_mk, hxy₁, hxy₂]`. Conclude with `map_one _`.

Use `⟨⟨e.symm (x₁, x₂), e.symm (y₁, y₂), hxy, by rw [mul_comm]; exact hxy⟩, hVW _ (hsub (⟨hx₁, hx₂⟩ : (x₁, x₂) ∈ V₁ ×ˢ V₂)) (hsub (⟨hy₁, hy₂⟩ : (y₁, y₂) ∈ V₁ ×ˢ V₂)), ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `e (e.symm (x₁, x₂)) = e (u * sg (AdeleRing (𝓞 F) F) c (e.symm (x₁, x₂)))`. Rewrite using `[map_mul]`. Apply `Prod.ext` to reduce the goal to its premises.

Rewrite using `[Prod.fst_mul, hs1, e.apply_symm_apply]`. Conclude with `hr₁`. Rewrite using `[Prod.snd_mul, hs2, e.apply_symm_apply]`. Conclude with `hr₂`.
-/
theorem exists_root_near : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∀ W ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∃ N ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), ∀ u ∈ N, (u : AdeleRing (𝓞 F) F ⊗[F] E) * sg (AdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ W, (x : AdeleRing (𝓞 F) F ⊗[F] E) = u * sg (AdeleRing (𝓞 F) F) c x := by
  intro F E _ _ _ _ _ c h2 hc hP
  letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)
  letI : TopologicalSpace (RA F E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (RA F E)
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  intro W hW
  obtain ⟨V, hV, hVW⟩ := units_nhds W hW
  obtain ⟨e, he, hec, hes⟩ := GlobalTheory.T.exists_adeleRing_tensor_equiv_infinite_prod_finite F E
  have hs1 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).1 = sg _ c (e z).1 := fun z => by
    rw [(he _).1, (he _).1]
    exact map_sg F E c _ z
  have hs2 : ∀ z, (e (sg (AdeleRing (𝓞 F) F) c z)).2 = sg _ c (e z).2 := fun z => by
    rw [(he _).2, (he _).2]
    exact map_sg F E c _ z
  have hV' : e.symm ⁻¹' V ∈ 𝓝 (1 : (InfiniteAdeleRing F ⊗[F] E) × RA F E) :=
    hes.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨V₁, h₁, V₂, h₂, hsub⟩ := mem_nhds_prod_iff.1 hV'
  have ht : Filter.Tendsto (fun u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ => e u) (𝓝 1) (𝓝 1) := by
    have := (hec.comp Units.continuous_val).tendsto 1
    simpa [Function.comp_def] using this
  have ht1 := (continuous_fst.tendsto _).comp ht
  have ht2 := (continuous_snd.tendsto _).comp ht
  refine ⟨_, Filter.inter_mem (ht1 (infinite_near F E c V₁ h₁)) (ht2 (finite_near F E c h2 hc hP V₂ h₂)), ?_⟩
  rintro u ⟨hu1, hu2⟩ hu
  have heu := congrArg e hu
  rw [map_mul, map_one] at heu
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁, hr₁⟩ := hu1 (by
    have := congrArg Prod.fst heu
    rw [Prod.fst_mul, hs1] at this
    exact this)
  obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂, hr₂⟩ := hu2 (by
    have := congrArg Prod.snd heu
    rw [Prod.snd_mul, hs2] at this
    exact this)
  have hxy : e.symm (x₁, x₂) * e.symm (y₁, y₂) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, hxy₁, hxy₂]
    exact map_one _
  refine ⟨⟨e.symm (x₁, x₂), e.symm (y₁, y₂), hxy, by rw [mul_comm]; exact hxy⟩,
    hVW _ (hsub (⟨hx₁, hx₂⟩ : (x₁, x₂) ∈ V₁ ×ˢ V₂)) (hsub (⟨hy₁, hy₂⟩ : (y₁, y₂) ∈ V₁ ×ˢ V₂)), ?_⟩
  apply e.injective
  change e (e.symm (x₁, x₂)) = e (u * sg (AdeleRing (𝓞 F) F) c (e.symm (x₁, x₂)))
  rw [map_mul]
  apply Prod.ext
  · rw [Prod.fst_mul, hs1, e.apply_symm_apply]
    exact hr₁
  · rw [Prod.snd_mul, hs2, e.apply_symm_apply]
    exact hr₂

end GlobalTheory.AdLat.RootNear
