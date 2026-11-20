import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocB

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω]

omit hl in
variable (E Ω) in
include E in
/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Use `haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic`. Conclude with `⟨inferInstance, Algebra.IsAlgebraic.trans ℚ E Ω⟩`.
-/
theorem isAlgClosureQ : IsAlgClosure ℚ Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact ⟨inferInstance, Algebra.IsAlgebraic.trans ℚ E Ω⟩

variable [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)

omit [IsAlgClosure E Ω] [Algebra E Ω] [NumberField E] [Field E] in

def resQ (σ : GQ l) : Ω ≃ₐ[ℚ] Ω :=
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  AlgHom.restrictNormal' ((σ.restrictScalars ℚ : PadicAlgCl l ≃ₐ[ℚ] PadicAlgCl l) :
    PadicAlgCl l →ₐ[ℚ] PadicAlgCl l) Ω

omit [IsAlgClosure E Ω] [Algebra E Ω] [NumberField E] [Field E] in
/- English proof (translation)
Use `letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra`. Use `haveI : IsScalarTower ℚ Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Use `haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω`. Conclude with `AlgHom.restrictNormal_commutes _ Ω x`.
-/
theorem j_resQ (σ : GQ l) (x : Ω) : j (resQ j σ x) = σ (j x) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  exact AlgHom.restrictNormal_commutes _ Ω x

def resE (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) : G E Ω :=
  AlgEquiv.ofRingEquiv (f := (resQ j σ).toRingEquiv) fun x => j.injective (by
    show j (resQ j σ (algebraMap E Ω x)) = _
    rw [j_resQ]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ (jE_mem j x))

/- English proof (translation)
The claim follows from `j_resQ j σ x`.
-/
theorem j_resE (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j (resE j σ hσ x) = σ (j x) := j_resQ j σ x

variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

include hj in
/- English proof (translation)
Establish `hiso : ∀ y : PadicAlgCl l, ‖σ y‖ = ‖y‖` using `fun y => by`. Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]`. Use `first`. Consider the case `(simp only [spectralNorm, minpoly.algEquiv_eq]; done)`. Consider the case `exact (spectralNorm.aut_isom σ y).symm`.

Consider the case `(unfold spectralNorm; rw [minpoly.algEquiv_eq])`. Consider the case `(unfold spectralNorm; congr 1; exact minpoly.algEquiv_eq σ y)`. Establish `key : ∀ x, resE j σ hσ x ∈ A ↔ x ∈ A` using `fun x => by`. Rewrite using `[hj, hj, j_resE, hiso]`. Use `show resE j σ hσ ∈ MulAction.stabilizer _ A`.

Rewrite using `[MulAction.mem_stabilizer_iff]`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← key, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`.
-/
theorem resE_mem (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) :
    resE j σ hσ ∈ Dec (F := E) A := by
  have hiso : ∀ y : PadicAlgCl l, ‖σ y‖ = ‖y‖ := fun y => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    first
      | (simp only [spectralNorm, minpoly.algEquiv_eq]; done)
      | exact (spectralNorm.aut_isom σ y).symm
      | (unfold spectralNorm; rw [minpoly.algEquiv_eq])
      | (unfold spectralNorm; congr 1; exact minpoly.algEquiv_eq σ y)
  have key : ∀ x, resE j σ hσ x ∈ A ↔ x ∈ A := fun x => by
    rw [hj, hj, j_resE, hiso]
  show resE j σ hσ ∈ MulAction.stabilizer _ A
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← key,
    ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

def rHom : ↥(KwF (E := E) j).fixingSubgroup →* ↥(Dec (F := E) A) where
  toFun σ := ⟨resE j σ.1 σ.2, resE_mem hj σ.1 σ.2⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun x => j.injective
    ((j_resE j _ (1 : ↥(KwF (E := E) j).fixingSubgroup).2 x).trans rfl))
  map_mul' σ τ := Subtype.ext (AlgEquiv.ext fun x => j.injective ((j_resE j _ (σ * τ).2 x).trans
    ((congrArg (σ : GQ l) (j_resE j _ τ.2 x)).symm.trans (j_resE j _ σ.2 _).symm)))

/- English proof (translation)
The claim follows from `j_resE j σ.1 σ.2 x`.
-/
theorem j_rHom (σ : ↥(KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j ((rHom hj σ : G E Ω) x) = (σ : GQ l) (j x) := j_resE j σ.1 σ.2 x

/- English proof (translation)
Establish `hiso : ∀ y : PadicAlgCl l, ‖σ y‖ = ‖y‖` using `fun y => by`. Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]`. Use `first`. Consider the case `(simp only [spectralNorm, minpoly.algEquiv_eq]; done)`. Consider the case `exact (spectralNorm.aut_isom σ y).symm`.

Consider the case `(unfold spectralNorm; rw [minpoly.algEquiv_eq])`. Consider the case `(unfold spectralNorm; congr 1; exact minpoly.algEquiv_eq σ y)`. Conclude with `(AddMonoidHomClass.isometry_of_norm σ hiso).continuous`.
-/
theorem continuous_aut (σ : GQ l) : Continuous σ := by
  have hiso : ∀ y : PadicAlgCl l, ‖σ y‖ = ‖y‖ := fun y => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    first
      | (simp only [spectralNorm, minpoly.algEquiv_eq]; done)
      | exact (spectralNorm.aut_isom σ y).symm
      | (unfold spectralNorm; rw [minpoly.algEquiv_eq])
      | (unfold spectralNorm; congr 1; exact minpoly.algEquiv_eq σ y)
  exact (AddMonoidHomClass.isometry_of_norm σ hiso).continuous

/- English proof (translation)
Introduce `σ τ h`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Establish `hd` using `denseRange_emb l j`. Establish `heq : ((σ : GQ l) : PadicAlgCl l → PadicAlgCl l) = (τ : GQ l)` using `hd.equalizer (continuous_aut _) (continuous_aut _) (funext fun x => by`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[← j_rHom hj σ x, ← j_rHom hj τ x, h])`. Conclude with `Subtype.ext (AlgEquiv.ext (congrFun heq))`.
-/
theorem rHom_injective : Function.Injective (rHom (E := E) hj) := by
  intro σ τ h
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hd := denseRange_emb l j
  have heq : ((σ : GQ l) : PadicAlgCl l → PadicAlgCl l) = (τ : GQ l) :=
    hd.equalizer (continuous_aut _) (continuous_aut _) (funext fun x => by
      simp only [Function.comp_apply]
      rw [← j_rHom hj σ x, ← j_rHom hj τ x, h])
  exact Subtype.ext (AlgEquiv.ext (congrFun heq))

include hj in
/- English proof (translation)
Establish `hl0 : ((l : ℕ) : Ω) ≠ 0` using `Nat.cast_ne_zero.mpr hl.out.ne_zero`. Establish `hlpos : 0 < ‖((l : ℕ) : PadicAlgCl l)‖`. Rewrite using `[norm_pos_iff, ← map_natCast j]`. Conclude with `(map_ne_zero j).mpr hl0`. Establish `h1 : z / ((l : ℕ) : Ω) ^ n ∈ A`.

Rewrite using `[hj, map_div₀, map_pow, map_natCast, norm_div, norm_pow]`. Conclude with `div_le_one_of_le₀ h (by positivity)`. Establish `hg' : g • A = A` using `MulAction.mem_stabilizer_iff.mp hg`. Establish `h2 : g (z / ((l : ℕ) : Ω) ^ n) ∈ A`. Rewrite using `[← hg', ← AlgEquiv.smul_def]`.

Conclude with `ValuationSubring.smul_mem_pointwise_smul g _ A h1`. Rewrite `h2` using `[map_div₀, map_pow, map_natCast, hj, map_div₀, map_pow, map_natCast, norm_div, norm_pow]`. Conclude with `(div_le_one (by positivity)).mp h2`.
-/
theorem norm_le_pow (g : G E Ω) (hg : g ∈ Dec (F := E) A) (z : Ω) (n : ℕ)
    (h : ‖j z‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ n) : ‖j (g z)‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ n := by
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hlpos : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := by
    rw [norm_pos_iff, ← map_natCast j]
    exact (map_ne_zero j).mpr hl0
  have h1 : z / ((l : ℕ) : Ω) ^ n ∈ A := by
    rw [hj, map_div₀, map_pow, map_natCast, norm_div, norm_pow]
    exact div_le_one_of_le₀ h (by positivity)
  have hg' : g • A = A := MulAction.mem_stabilizer_iff.mp hg
  have h2 : g (z / ((l : ℕ) : Ω) ^ n) ∈ A := by
    rw [← hg', ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul g _ A h1
  rw [map_div₀, map_pow, map_natCast, hj, map_div₀, map_pow, map_natCast, norm_div, norm_pow] at h2
  exact (div_le_one (by positivity)).mp h2

include hj in

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Set `iC : Ω →+* ℂ_[l]` to `(algebraMap (PadicAlgCl l) ℂ_[l]).comp j`. Use `letI : PseudoMetricSpace Ω := PseudoMetricSpace.induced iC inferInstance`. Establish `ue : IsUniformInducing iC` using `⟨rfl⟩`. Establish `dr : DenseRange iC` using `(UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).comp (denseRange_emb l j) (UniformSpace.Completion.continuous_coe _)`.

Set `f : Ω →+* ℂ_[l]` to `iC.comp (g : Ω →+* Ω)`. Establish `hn : ∀ z : Ω, ‖iC z‖ = ‖j z‖` using `fun z => PadicComplex.norm_extends l (j z)`. Establish `hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1`. Establish `h1 : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖((l : ℕ) : ℚ_[l])‖`. Rewrite using `[← PadicAlgCl.norm_extends, map_natCast]`.

Rewrite using `[h1]`. Conclude with `Padic.norm_p_lt_one`. Establish `hf : UniformContinuous f`. Rewrite using `[Metric.uniformContinuous_iff]`. Introduce `ε hε`.

Take `⟨n, hn'⟩` from `exists_pow_lt_of_lt_one hε hl1`. Use `⟨‖((l : ℕ) : PadicAlgCl l)‖ ^ n, pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n, fun {a b} hab => ?_⟩` and prove the remaining obligations. Establish `h1 : dist a b = ‖j (a - b)‖` using `by show dist (iC a) (iC b) = _`. Rewrite using `[dist_eq_norm, ← map_sub, hn]`. Establish `h2 : dist (f a) (f b) = ‖j (g (a - b))‖`.

Rewrite using `[dist_eq_norm, ← map_sub]`. Conclude with `hn _`. Rewrite using `[h2]`. Rewrite `hab` using `[h1]`. Conclude with `lt_of_le_of_lt (norm_le_pow hj g hg _ n hab.le) hn'`.

Set `gh : ℂ_[l] →+* ℂ_[l]` to `IsDenseInducing.extendRingHom ue dr hf`. Establish `hgh : ∀ x, gh (iC x) = f x` using `fun x => (ue.isDenseInducing dr).extend_eq hf.continuous x`. Establish `hcont : Continuous gh` using `(uniformContinuous_uniformly_extend ue dr hf).continuous`. Establish `hQ : ∀ x : ℚ_[l], gh (algebraMap ℚ_[l] ℂ_[l] x) = algebraMap ℚ_[l] ℂ_[l] x`. Establish `hc : Continuous (algebraMap ℚ_[l] ℂ_[l])` using `continuous_algebraMap ℚ_[l] ℂ_[l]`.

Establish `e` using `(Padic.denseRange_ratCast l).equalizer (hcont.comp hc) hc (funext fun q => by show gh (algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l])) = algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l])`. Rewrite using `[map_ratCast, map_ratCast])`. Conclude with `fun x => congrFun e x`. Set `gA : ℂ_[l] →ₐ[ℚ_[l]] ℂ_[l]` to `{ gh with commutes' := hQ }`. Use `⟨gA.restrictNormal' (PadicAlgCl l), fun x => ?_⟩` and prove the remaining obligations.

Establish `h3` using `AlgHom.restrictNormal_commutes gA (PadicAlgCl l) (j x)`. Conclude with `(algebraMap (PadicAlgCl l) ℂ_[l]).injective (h3.trans (hgh x))`.
-/
theorem exists_ext (g : G E Ω) (hg : g ∈ Dec (F := E) A) :
    ∃ σ : GQ l, ∀ x, σ (j x) = j (g x) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  let iC : Ω →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp j
  letI : PseudoMetricSpace Ω := PseudoMetricSpace.induced iC inferInstance
  have ue : IsUniformInducing iC := ⟨rfl⟩
  have dr : DenseRange iC :=
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).comp (denseRange_emb l j)
      (UniformSpace.Completion.continuous_coe _)
  let f : Ω →+* ℂ_[l] := iC.comp (g : Ω →+* Ω)
  have hn : ∀ z : Ω, ‖iC z‖ = ‖j z‖ := fun z => PadicComplex.norm_extends l (j z)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    have h1 : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖((l : ℕ) : ℚ_[l])‖ := by
      rw [← PadicAlgCl.norm_extends, map_natCast]
    rw [h1]
    exact Padic.norm_p_lt_one
  have hf : UniformContinuous f := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one hε hl1
    refine ⟨‖((l : ℕ) : PadicAlgCl l)‖ ^ n,
      pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n, fun {a b} hab => ?_⟩
    have h1 : dist a b = ‖j (a - b)‖ := by
      show dist (iC a) (iC b) = _
      rw [dist_eq_norm, ← map_sub, hn]
    have h2 : dist (f a) (f b) = ‖j (g (a - b))‖ := by
      rw [dist_eq_norm, ← map_sub]
      exact hn _
    rw [h2]
    rw [h1] at hab
    exact lt_of_le_of_lt (norm_le_pow hj g hg _ n hab.le) hn'
  let gh : ℂ_[l] →+* ℂ_[l] := IsDenseInducing.extendRingHom ue dr hf
  have hgh : ∀ x, gh (iC x) = f x := fun x => (ue.isDenseInducing dr).extend_eq hf.continuous x
  have hcont : Continuous gh := (uniformContinuous_uniformly_extend ue dr hf).continuous
  have hQ : ∀ x : ℚ_[l], gh (algebraMap ℚ_[l] ℂ_[l] x) = algebraMap ℚ_[l] ℂ_[l] x := by
    have hc : Continuous (algebraMap ℚ_[l] ℂ_[l]) := continuous_algebraMap ℚ_[l] ℂ_[l]
    have e := (Padic.denseRange_ratCast l).equalizer (hcont.comp hc) hc (funext fun q => by
      show gh (algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l])) = algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l])
      rw [map_ratCast, map_ratCast])
    exact fun x => congrFun e x
  let gA : ℂ_[l] →ₐ[ℚ_[l]] ℂ_[l] := { gh with commutes' := hQ }
  refine ⟨gA.restrictNormal' (PadicAlgCl l), fun x => ?_⟩
  have h3 := AlgHom.restrictNormal_commutes gA (PadicAlgCl l) (j x)
  exact (algebraMap (PadicAlgCl l) ℂ_[l]).injective (h3.trans (hgh x))

/- English proof (translation)
Introduce and unpack `⟨g, hg⟩`. Take `⟨σ, hσ⟩` from `exists_ext hj g hg`. Establish `hfix : ∀ y ∈ Set.range fun i => jE (E` using `E) j (Module.finBasis ℚ E i), σ y = y := by`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `only [jE, RingHom.comp_apply]`.

Rewrite using `[hσ, AlgEquiv.commutes]`. Establish `hmem : σ ∈ (KwF (E` using `E) j).fixingSubgroup := by`. Establish `hz : Subgroup.zpowers σ ≤ (KwF (E` using `E) j).fixingSubgroup := by`. Rewrite using `[← IntermediateField.le_iff_le]`. Unfold `KwF`.

Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `y hy`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixedField_iff]`. Introduce `τ hτ`. Establish `hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (GQ l) y`.

Rewrite using `[Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Conclude with `hfix y hy`. Establish `h2` using `hst hτ`. Rewrite `h2` using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Then use the resulting hypothesis. Conclude with `hz (Subgroup.mem_zpowers σ)`.

Use `⟨⟨σ, hmem⟩, Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)⟩` and prove the remaining obligations. Rewrite using `[j_rHom]`. Conclude with `hσ x`.
-/
theorem rHom_surjective : Function.Surjective (rHom (E := E) hj) := by
  rintro ⟨g, hg⟩
  obtain ⟨σ, hσ⟩ := exists_ext hj g hg
  have hfix : ∀ y ∈ Set.range fun i => jE (E := E) j (Module.finBasis ℚ E i), σ y = y := by
    rintro _ ⟨i, rfl⟩
    simp only [jE, RingHom.comp_apply]
    rw [hσ, AlgEquiv.commutes]
  have hmem : σ ∈ (KwF (E := E) j).fixingSubgroup := by
    have hz : Subgroup.zpowers σ ≤ (KwF (E := E) j).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le]
      unfold KwF
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (GQ l) y := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        exact hfix y hy
      have h2 := hst hτ
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at h2
    exact hz (Subgroup.mem_zpowers σ)
  refine ⟨⟨σ, hmem⟩, Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)⟩
  rw [j_rHom]
  exact hσ x

end Formalism.BasicNotions.Examples₂.LB
