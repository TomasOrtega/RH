import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.OneHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨-, -, -, h⟩` from `hσ`. Set `τ : E →+* ℂ` to `Classical.choice (inferInstance : Nonempty (E →+* ℂ))`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h τ, h τ, star_star]`.
-/
theorem sigma_sigma {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h⟩ := hσ
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h τ, h τ, star_star]

/- English proof (translation)
Establish `hcm` using `hσ`. Take `⟨-, hc, h2, h⟩` from `hσ`. Set `τ : E →+* ℂ` to `Classical.choice (inferInstance : Nonempty (E →+* ℂ))`. Establish `hnr : ∃ x : E, star (τ x) ≠ τ x`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hreal : NumberField.ComplexEmbedding.IsReal τ`. Use extensionality with `x`. Conclude with `hcon x`. Use `hc.isComplex (NumberField.InfinitePlace.mk τ)` as an intermediate fact.

Rewrite `this` using `[← NumberField.InfinitePlace.not_isReal_iff_isComplex]`. Conclude with `this ⟨τ, hreal, rfl⟩`. Take `⟨x, hx⟩` from `hnr`. Use `set δ : E := x - σ x with hδ`. Establish `hσδ : σ δ = -δ`.

Simplify using `[hδ, sigma_sigma hcm]`. Establish `hδ0 : δ ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Establish `: τ δ = 0` using `by rw [h0, map_zero]`.

Rewrite `this` using `[hδ, map_sub, h τ, sub_eq_zero]`. Conclude with `this.symm`. Establish `hli : LinearIndependent F ![(1 : E), δ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Establish `hσs : ∀ (c : F) (z : E), σ (c • z) = c • σ z` using `fun c z => by`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]`. Establish `h'` using `congrArg σ hst`. Simplify using `only [map_add, hσs, map_one, hσδ, map_zero, smul_neg] at h'`. Establish `hs2 : (s + s) • (1 : E) = 0`.

Rewrite using `[add_smul]`. Take the linear combination `hst + h'`. Establish `hs : s = 0`. Establish `h3 : s + s = 0` using `by simpa using hs2`. Establish `h4 : (2 : F) * s = 0` using `by rw [two_mul]; exact h3`.

Simplify using `using h4`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Rewrite `hst` using `[hs, zero_smul, zero_add]`. Conclude with `(smul_eq_zero.mp hst).resolve_right hδ0`. Use `⟨basisOfLinearIndependentOfCardEqFinrank hli (by simpa using h2.symm), ?_, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using `using hσδ`.
-/
theorem exists_basis {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) :
    ∃ bb : Module.Basis (Fin 2) F E, bb 0 = 1 ∧ σ (bb 1) = - bb 1 := by
  have hcm := hσ
  obtain ⟨-, hc, h2, h⟩ := hσ
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  have hnr : ∃ x : E, star (τ x) ≠ τ x := by
    by_contra hcon
    push_neg at hcon
    have hreal : NumberField.ComplexEmbedding.IsReal τ := by
      ext x
      exact hcon x
    have := hc.isComplex (NumberField.InfinitePlace.mk τ)
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex] at this
    exact this ⟨τ, hreal, rfl⟩
  obtain ⟨x, hx⟩ := hnr
  set δ : E := x - σ x with hδ
  have hσδ : σ δ = -δ := by
    simp [hδ, sigma_sigma hcm]
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hx
    have : τ δ = 0 := by rw [h0, map_zero]
    rw [hδ, map_sub, h τ, sub_eq_zero] at this
    exact this.symm
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hσs : ∀ (c : F) (z : E), σ (c • z) = c • σ z := fun c z => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
    have h' := congrArg σ hst
    simp only [map_add, hσs, map_one, hσδ, map_zero, smul_neg] at h'
    have hs2 : (s + s) • (1 : E) = 0 := by
      rw [add_smul]
      linear_combination hst + h'
    have hs : s = 0 := by
      have h3 : s + s = 0 := by simpa using hs2
      have h4 : (2 : F) * s = 0 := by rw [two_mul]; exact h3
      simpa using h4
    refine ⟨hs, ?_⟩
    rw [hs, zero_smul, zero_add] at hst
    exact (smul_eq_zero.mp hst).resolve_right hδ0
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simpa using h2.symm), ?_, ?_⟩
  · simp
  · simpa using hσδ

variable (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Establish `h : r + r = algebraMap F R 2 * r`. Rewrite using `[map_ofNat, two_mul]`. Rewrite using `[h, ← mul_assoc, ← map_mul]`. Evaluate the numerical expressions.
-/
theorem half_add (r : R) : algebraMap F R (1 / 2) * (r + r) = r := by
  have h : r + r = algebraMap F R 2 * r := by
    rw [map_ofNat, two_mul]
  rw [h, ← mul_assoc, ← map_mul]
  norm_num

variable {R}

/- English proof (translation)
Take `⟨bb, h0, h1⟩` from `exists_basis hσ`. Use `set B := Algebra.TensorProduct.basis R bb with hB`. Establish `hy' : y = (B.repr y 0) ⊗ₜ[F] (1 : E) + (B.repr y 1) ⊗ₜ[F] bb 1` using `by conv_lhs => rw [← B.sum_repr y]`. Simplify using `[Fin.sum_univ_two, hB, Algebra.TensorProduct.basis_apply, h0, TensorProduct.smul_tmul']`. Generalize the expression as in `B.repr y 0 = c0 at hy'`.

Generalize the expression as in `hc1 : B.repr y 1 = c1 at hy'`. Establish `hs : sigR R σ y = c0 ⊗ₜ[F] (1 : E) - c1 ⊗ₜ[F] bb 1`. Rewrite using `[hy']`. Simplify using `[sigR, h1, TensorProduct.tmul_neg, sub_eq_add_neg]`. Establish `hz : c1 ⊗ₜ[F] bb 1 + c1 ⊗ₜ[F] bb 1 = 0`.

Use `hs.symm.trans hy` as an intermediate fact. Rewrite `this` using `[hy']`. Take the linear combination `(-1 : ℤ) • this`. Establish `hr : ∀ c : R, (B.repr (c ⊗ₜ[F] bb 1)) 1 = c`. Introduce `c`.

Simplify using `[hB, Algebra.TensorProduct.basis_repr_tmul]`. Establish `hc : c1 = 0`. Use `congrArg (fun z => B.repr z 1) hz` as an intermediate fact. Simplify using `only [map_add, Finsupp.add_apply, hr, map_zero, Finsupp.zero_apply] at this`. Rewrite using `[← half_add (F := F) R c1, this, mul_zero]`.

Conclude with `⟨c0, by rw [hy', hc]; simp⟩`.
-/
theorem fixed_eq {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {y : R ⊗[F] E} (hy : sigR R σ y = y) :
    ∃ r : R, y = r ⊗ₜ[F] (1 : E) := by
  obtain ⟨bb, h0, h1⟩ := exists_basis hσ
  set B := Algebra.TensorProduct.basis R bb with hB
  have hy' : y = (B.repr y 0) ⊗ₜ[F] (1 : E) + (B.repr y 1) ⊗ₜ[F] bb 1 := by
    conv_lhs => rw [← B.sum_repr y]
    simp [Fin.sum_univ_two, hB, Algebra.TensorProduct.basis_apply, h0, TensorProduct.smul_tmul']
  generalize B.repr y 0 = c0 at hy'
  generalize hc1 : B.repr y 1 = c1 at hy'
  have hs : sigR R σ y = c0 ⊗ₜ[F] (1 : E) - c1 ⊗ₜ[F] bb 1 := by
    rw [hy']
    simp [sigR, h1, TensorProduct.tmul_neg, sub_eq_add_neg]
  have hz : c1 ⊗ₜ[F] bb 1 + c1 ⊗ₜ[F] bb 1 = 0 := by
    have := hs.symm.trans hy
    rw [hy'] at this
    linear_combination (-1 : ℤ) • this
  have hr : ∀ c : R, (B.repr (c ⊗ₜ[F] bb 1)) 1 = c := by
    intro c
    simp [hB, Algebra.TensorProduct.basis_repr_tmul]
  have hc : c1 = 0 := by
    have := congrArg (fun z => B.repr z 1) hz
    simp only [map_add, Finsupp.add_apply, hr, map_zero, Finsupp.zero_apply] at this
    rw [← half_add (F := F) R c1, this, mul_zero]
  exact ⟨c0, by rw [hy', hc]; simp⟩

/- English proof (translation)
Take `⟨bb, -, -⟩` from `exists_basis hσ`. Use `Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R bb) r` as an intermediate fact. Rewrite `this` using `[Algebra.TensorProduct.algebraMap_apply]`. Simplify `this` using `[two_smul]`.
-/
theorem trace_tmul_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (r : R) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r + r := by
  obtain ⟨bb, -, -⟩ := exists_basis hσ
  have := Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R bb) r
  rw [Algebra.TensorProduct.algebraMap_apply] at this
  simpa [two_smul] using this

end GlobalTheory.CompanionTheory.SW.OneHerm

namespace GlobalTheory.CompanionTheory.SW.OneHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Top

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)`. Establish `h` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap R (R ⊗[F] E))`. Use `h using 2 with s` and compare the differences between its conclusion and the goal. Simplify using `[Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem continuous_tmul_one : Continuous fun s : R => s ⊗ₜ[F] (1 : E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have h := IsModuleTopology.continuous_of_linearMap (Algebra.linearMap R (R ⊗[F] E))
  convert h using 2 with s
  simp [Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Conclude with `IsModuleTopology.continuous_of_linearMap (Algebra.trace R (R ⊗[F] E))`.
-/
theorem continuous_trace : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (Algebra.trace R (R ⊗[F] E))

def hermHalf (σ : E →ₐ[F] E) (S : HermR R σ 1) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)

/- English proof (translation)
Establish `hfix : sigR R σ ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0` using `S.2 0 0`. Take `⟨r, hr⟩` from `fixed_eq hσ hfix`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `a b`. Establish `ha : a = 0` using `Subsingleton.elim _ _`.

Establish `hb : b = 0` using `Subsingleton.elim _ _`. Substitute `ha hb` using the available equality. Express the relevant statement in the definitionally equal form `(hermHalf R σ S) ⊗ₜ[F] (1 : E) = _`. Rewrite using `[hr, hermHalf, hr, trace_tmul_one hσ, half_add]`.
-/
theorem hermScal_hermHalf {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (S : HermR R σ 1) :
    hermScal R σ (hermHalf R σ S) = S := by
  have hfix : sigR R σ ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
    S.2 0 0
  obtain ⟨r, hr⟩ := fixed_eq hσ hfix
  apply Subtype.ext
  ext a b
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst ha hb
  change (hermHalf R σ S) ⊗ₜ[F] (1 : E) = _
  rw [hr, hermHalf, hr, trace_tmul_one hσ, half_add]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s`. Rewrite using `[trace_tmul_one hσ, half_add]`.
-/
theorem hermHalf_hermScal {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (s : R) :
    hermHalf R σ (hermScal R σ s) = s := by
  change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s
  rw [trace_tmul_one hσ, half_add]

/- English proof (translation)
Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `continuous_pi fun _ => continuous_pi fun _ => continuous_tmul_one R`.
-/
theorem continuous_hermScal (σ : E →ₐ[F] E) : Continuous (hermScal R σ) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_pi fun _ => continuous_pi fun _ => continuous_tmul_one R

/- English proof (translation)
Use `continuous_const.mul ((continuous_trace R).comp ?_)` and prove the remaining obligations. Conclude with `(continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)`.
-/
theorem continuous_hermHalf (σ : E →ₐ[F] E) : Continuous (hermHalf R σ) := by
  refine continuous_const.mul ((continuous_trace R).comp ?_)
  exact (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)

def hermHomeo {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) : R ≃ₜ HermR R σ 1 where
  toFun := hermScal R σ
  invFun := hermHalf R σ
  left_inv := hermHalf_hermScal R hσ
  right_inv := hermScal_hermHalf R hσ
  continuous_toFun := continuous_hermScal R σ
  continuous_invFun := continuous_hermHalf R σ

end Top

section Meas

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

instance : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
  ⟨fun p => by
    have h := p.2
    rw [Subsingleton.elim p.1.1 p.1.2] at h
    exact lt_irrefl _ h⟩

/- English proof (translation)
Use `haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩`. Set `P` to `{p : Fin 1 × Fin 1 // p.1 < p.2}`. Set `x₀ : P → R ⊗[F] E` to `isEmptyElim`. Set `ψ : HermR R σ 1 → (Fin 1 → R) × (P → R ⊗[F] E)` to `fun S => ((fun i : Fin 1 => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)), (fun p : P => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))`. Set `e : R → (Fin 1 → R) × (P → R ⊗[F] E)` to `fun s => (fun _ => s, x₀)`.

Establish `hHs : MeasurableEmbedding (hermScal R σ)` using `(hermHomeo R hσ).measurableEmbedding`. Establish `hψe : ∀ S, ψ S = e (hermHalf R σ S)`. Introduce `S`. Use `Prod.ext ?_ (Subsingleton.elim _ _)` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `hi : i = 0` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Both sides reduce to the same expression. Establish `hemb : MeasurableEmbedding e`. Use `MeasurableEmbedding.of_measurable_inverse (g := fun y => y.1 0) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `(measurable_pi_lambda _ fun _ => measurable_id).prodMk measurable_const`. Establish `: Set.range e = Set.univ`. Use `Set.eq_univ_of_forall fun y => ⟨y.1 0, ?_⟩` and prove the remaining obligations. Use `Prod.ext ?_ (Subsingleton.elim _ _)` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `hi : i = 0` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `MeasurableSet.univ`.

Conclude with `(measurable_pi_apply 0).comp measurable_fst`. Introduce `s`. Both sides reduce to the same expression. Establish `hψ : MeasurableEmbedding ψ`. Establish `: ψ = e ∘ (hermHomeo R hσ).symm` using `funext hψe`.

Rewrite using `[this]`. Conclude with `hemb.comp (hermHomeo R hσ).symm.measurableEmbedding`. Establish `hprod : (Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : P => coordK R b lam) = lam.map e`. Rewrite using `[Measure.pi_of_empty _ x₀, Measure.prod_dirac]`. Establish `h1 : (Measure.pi fun _ : Fin 1 => lam) = lam.map (fun s _ => s)` using `((measurePreserving_funUnique lam (Fin 1)).symm (MeasurableEquiv.funUnique (Fin 1) R)).map_eq.symm`.

Establish `hm1 : Measurable fun (s : R) (_ : Fin 1) => s` using `measurable_pi_lambda _ fun _ => measurable_id`. Establish `hm2 : Measurable fun y : Fin 1 → R => (y, x₀)` using `measurable_id.prodMk measurable_const`. Rewrite using `[h1, Measure.map_map hm2 hm1]`. Both sides reduce to the same expression. Establish `hcomp : e = ψ ∘ hermScal R σ`.

Use function extensionality and compare the values at `s`. Rewrite using `[Function.comp, hψe, hermHalf_hermScal R hσ]`. Establish `hmap : lam.map e = (lam.map (hermScal R σ)).map ψ`. Rewrite using `[Measure.map_map hψ.measurable hHs.measurable, hcomp]`. Express the relevant statement in the definitionally equal form `_ = Measure.comap ψ _`.

Rewrite using `[hprod, hmap, hψ.comap_map]`.
-/
theorem map_hermScal {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [lam.IsAddHaarMeasure] :
    lam.map (hermScal R σ) = coordHerm R σ b lam 1 := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  let P := {p : Fin 1 × Fin 1 // p.1 < p.2}
  let x₀ : P → R ⊗[F] E := isEmptyElim
  let ψ : HermR R σ 1 → (Fin 1 → R) × (P → R ⊗[F] E) := fun S =>
      ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : P => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))
  let e : R → (Fin 1 → R) × (P → R ⊗[F] E) := fun s => (fun _ => s, x₀)
  have hHs : MeasurableEmbedding (hermScal R σ) := (hermHomeo R hσ).measurableEmbedding
  have hψe : ∀ S, ψ S = e (hermHalf R σ S) := by
    intro S
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rfl
  have hemb : MeasurableEmbedding e := by
    refine MeasurableEmbedding.of_measurable_inverse (g := fun y => y.1 0) ?_ ?_ ?_ ?_
    · exact (measurable_pi_lambda _ fun _ => measurable_id).prodMk measurable_const
    · have : Set.range e = Set.univ := by
        refine Set.eq_univ_of_forall fun y => ⟨y.1 0, ?_⟩
        refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rfl
      rw [this]
      exact MeasurableSet.univ
    · exact (measurable_pi_apply 0).comp measurable_fst
    · intro s
      rfl
  have hψ : MeasurableEmbedding ψ := by
    have : ψ = e ∘ (hermHomeo R hσ).symm := funext hψe
    rw [this]
    exact hemb.comp (hermHomeo R hσ).symm.measurableEmbedding
  have hprod : (Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : P => coordK R b lam) =
      lam.map e := by
    rw [Measure.pi_of_empty _ x₀, Measure.prod_dirac]
    have h1 : (Measure.pi fun _ : Fin 1 => lam) = lam.map (fun s _ => s) :=
      ((measurePreserving_funUnique lam (Fin 1)).symm (MeasurableEquiv.funUnique (Fin 1) R)).map_eq.symm
    have hm1 : Measurable fun (s : R) (_ : Fin 1) => s := measurable_pi_lambda _ fun _ => measurable_id
    have hm2 : Measurable fun y : Fin 1 → R => (y, x₀) := measurable_id.prodMk measurable_const
    rw [h1, Measure.map_map hm2 hm1]
    rfl
  have hcomp : e = ψ ∘ hermScal R σ := by
    funext s
    rw [Function.comp, hψe, hermHalf_hermScal R hσ]
  have hmap : lam.map e = (lam.map (hermScal R σ)).map ψ := by
    rw [Measure.map_map hψ.measurable hHs.measurable, hcomp]
  change _ = Measure.comap ψ _
  rw [hprod, hmap, hψ.comap_map]

end Meas

end GlobalTheory.CompanionTheory.SW.OneHerm

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b`. Use `⟨(GlobalTheory.CompanionTheory.SW.OneHerm.hermHomeo R hσ).isHomeomorph, GlobalTheory.CompanionTheory.SW.OneHerm.hermScal_hermHalf R hσ, ?_⟩` and prove the remaining obligations. Introduce `lam hlam`. Conclude with `GlobalTheory.CompanionTheory.SW.OneHerm.map_hermScal R hσ b lam`.
-/
theorem GlobalTheory.CompanionTheory.SW.hermScal_main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph (hermScal R σ) ∧ (∀ S : HermR R σ 1, hermScal R σ (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)) = S) ∧ ∀ (lam : Measure R), lam.IsAddHaarMeasure → lam.map (hermScal R σ) = coordHerm R σ b lam 1 := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b
  refine ⟨(GlobalTheory.CompanionTheory.SW.OneHerm.hermHomeo R hσ).isHomeomorph, GlobalTheory.CompanionTheory.SW.OneHerm.hermScal_hermHalf R hσ, ?_⟩
  intro lam hlam
  exact GlobalTheory.CompanionTheory.SW.OneHerm.map_hermScal R hσ b lam
