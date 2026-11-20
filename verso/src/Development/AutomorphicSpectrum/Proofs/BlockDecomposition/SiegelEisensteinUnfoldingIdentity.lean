import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableSetIntF
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Lim

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R] [CommRing R']
  [Algebra F R']

/- English proof (translation)
Use `conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]`. Simplify using `[map_sum, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']`.
-/
theorem map_eq_sum (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) x =
      ∑ k, f ((Algebra.TensorProduct.basis R b).repr x k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]
  simp [map_sum, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

/- English proof (translation)
Establish `h : Algebra.TensorProduct.map f (AlgHom.id F E) x = ∑ j, f ((Algebra.TensorProduct.basis R b).repr x j) • (Algebra.TensorProduct.basis R' b) j`. Rewrite using `[map_eq_sum f b x]`. Simplify using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']`. Rewrite using `[h, Module.Basis.repr_sum_self]`.
-/
theorem repr_map (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) x) k =
      f ((Algebra.TensorProduct.basis R b).repr x k) := by
  have h : Algebra.TensorProduct.map f (AlgHom.id F E) x =
      ∑ j, f ((Algebra.TensorProduct.basis R b).repr x j) • (Algebra.TensorProduct.basis R' b) j := by
    rw [map_eq_sum f b x]
    simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  rw [h, Module.Basis.repr_sum_self]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_basis b`. Establish `h1 : ∀ e : E, Algebra.trace R' (R' ⊗[F] E) ((1 : R') ⊗ₜ[F] e) = algebraMap F R' (Algebra.trace F E e)`. Introduce `e`. Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]`. Rewrite using `[map_eq_sum f b x, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h2 : ∀ (a : R') (e : E), a ⊗ₜ[F] e = a • ((1 : R') ⊗ₜ[F] e)`. Introduce `a e`. Simplify using `[TensorProduct.smul_tmul']`. Rewrite using `[h2, map_smul, h1, smul_eq_mul]`.
-/
theorem trace_map (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      ∑ k, f ((Algebra.TensorProduct.basis R b).repr x k) * algebraMap F R' (Algebra.trace F E (b k)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have h1 : ∀ e : E, Algebra.trace R' (R' ⊗[F] E) ((1 : R') ⊗ₜ[F] e) = algebraMap F R' (Algebra.trace F E e) := by
    intro e
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  rw [map_eq_sum f b x, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 : ∀ (a : R') (e : E), a ⊗ₜ[F] e = a • ((1 : R') ⊗ₜ[F] e) := by
    intro a e
    simp [TensorProduct.smul_tmul']
  rw [h2, map_smul, h1, smul_eq_mul]

end Tens

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def cf (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E) (x : AF F ⊗[F] E) (k : Fin d) : Fv F v :=
  ((evalV F v).comp (sndA F)) ((Algebra.TensorProduct.basis (AF F) b).repr x k)

/- English proof (translation)
Establish `h : Algebra.TensorProduct.map ((evalV F v).comp (sndA F)) (AlgHom.id F E) = (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).comp (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))`. Rewrite using `[← Algebra.TensorProduct.map_comp]`. Both sides reduce to the same expression. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem hermV_apply (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : HermR (AF F) σ n) (i j : Fin n) :
    ((hermV σ v (hermFin σ y) : HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j =
      Algebra.TensorProduct.map ((evalV F v).comp (sndA F)) (AlgHom.id F E)
        ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) := by
  have h : Algebra.TensorProduct.map ((evalV F v).comp (sndA F)) (AlgHom.id F E) =
      (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).comp
        (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) := by
    rw [← Algebra.TensorProduct.map_comp]
    rfl
  rw [h]
  rfl

/- English proof (translation)
Unfold `latH`. Simplify using `only [Set.mem_setOf_eq, hermV_apply, trace_map _ b, repr_map]`. Both sides reduce to the same expression.
-/
theorem mem_latH_iff (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (y : HermR (AF F) σ n) :
    hermV σ v (hermFin σ y) ∈ latH σ b v n ↔
      (∀ i, algebraMap F (Fv F v) (1 / 2) *
          ∑ k, cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i i) k *
            algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F) ∧
        ∀ i j, i < j → ∀ k, cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k ∈
          v.adicCompletionIntegers F := by
  unfold latH
  simp only [Set.mem_setOf_eq, hermV_apply, trace_map _ b, repr_map]
  rfl

/- English proof (translation)
Use `filter_upwards [(algebraMap F (Af F) a).2] with v hv`. Establish `h : evalV F v (algebraMap F (Af F) a) = algebraMap F (Fv F v) a` using `(evalV F v).commutes a`. Rewrite using `[← h]`. Conclude with `hv`.
-/
theorem ev_rat (a : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  filter_upwards [(algebraMap F (Af F) a).2] with v hv
  have h : evalV F v (algebraMap F (Af F) a) = algebraMap F (Fv F v) a := (evalV F v).commutes a
  rw [← h]
  exact hv

/- English proof (translation)
The claim follows from `(sndA F ((Algebra.TensorProduct.basis (AF F) b).repr x k)).2`.
-/
theorem ev_cf {d : ℕ} (b : Module.Basis (Fin d) F E) (x : AF F ⊗[F] E) (k : Fin d) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, cf v b x k ∈ v.adicCompletionIntegers F :=
  (sndA F ((Algebra.TensorProduct.basis (AF F) b).repr x k)).2

/- English proof (translation)
Establish `h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (i j : Fin n) (k : Fin d), cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun k => ev_cf b _ k`. Establish `h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k : Fin d, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun k => ev_rat _`. Use `filter_upwards [h1, h2, ev_rat (1 / 2 : F)] with v h1 h2 h3`. Rewrite using `[mem_latH_iff]`. Use `⟨fun i => mul_mem h3 (sum_mem fun k _ => mul_mem (h1 i i k) (h2 k)), fun i j _ k => h1 i j k⟩` and prove the remaining obligations.
-/
theorem ev_latH (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) {n : ℕ} (y : HermR (AF F) σ n) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hermV σ v (hermFin σ y) ∈ latH σ b v n := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (i j : Fin n) (k : Fin d),
      cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun k => ev_cf b _ k
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k : Fin d,
      algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_rat _
  filter_upwards [h1, h2, ev_rat (1 / 2 : F)] with v h1 h2 h3
  rw [mem_latH_iff]
  refine ⟨fun i => mul_mem h3 (sum_mem fun k _ => mul_mem (h1 i i k) (h2 k)), fun i j _ k => h1 i j k⟩

end Adelic

section Cont

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
The claim follows from `continuous_subtype_val.matrix_elem i j`.
-/
theorem continuous_entry (σ : E →ₐ[F] E) {n : ℕ} (i j : Fin n) :
    Continuous fun y : HermR (AF F) σ n => (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j :=
  continuous_subtype_val.matrix_elem i j

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Establish `h1 : Continuous fun x : AF F ⊗[F] E => (Algebra.TensorProduct.basis (AF F) b).repr x k` using `IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (AF F) b).coord k)`. Establish `h2 : Continuous fun a : AF F => sndA F a` using `continuous_snd`. Establish `h3 : Continuous fun a : Af F => a v` using `RestrictedProduct.continuous_eval v`. Conclude with `h3.comp (h2.comp h1)`.
-/
theorem continuous_cf (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E) (k : Fin d) :
    Continuous fun x : AF F ⊗[F] E => cf v b x k := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have h1 : Continuous fun x : AF F ⊗[F] E => (Algebra.TensorProduct.basis (AF F) b).repr x k :=
    IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (AF F) b).coord k)
  have h2 : Continuous fun a : AF F => sndA F a := continuous_snd
  have h3 : Continuous fun a : Af F => a v := RestrictedProduct.continuous_eval v
  exact h3.comp (h2.comp h1)

/- English proof (translation)
Use `haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩`. Establish `hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`. Apply the tactic sequence `have hc : ∀ (i j : Fin n) (k : Fin d), Continuous fun y : HermR (AF F) σ n => cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k := fun i j k => (continuous_cf v b k).comp (continuous_entry σ i j)`. Establish `hset : {y : HermR (AF F) σ n | hermV σ v (hermFin σ y) ∈ latH σ b v n} = (⋂ i : Fin n, (fun y : HermR (AF F) σ n => algebraMap F (Fv F v) (1 / 2) * ∑ k, cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i i) k * algebraMap F (Fv F v) (Algebra.trace F E (b k))) ⁻¹' (v.adicComplet …`. Use extensionality with `y`.

Simplify using `only [Set.mem_setOf_eq, mem_latH_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Rewrite using `[hset]`. Use `MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun k => (hO.preimage (hc i j k)).measurableSet)` and prove the remaining obligations. Use `(hO.preimage ?_).measurableSet` and prove the remaining obligations. Conclude with `continuous_const.mul (continuous_finset_sum _ fun k _ => (hc i i k).mul continuous_const)`.
-/
theorem measurableSet_latH (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    {n : ℕ} : MeasurableSet {y : HermR (AF F) σ n | hermV σ v (hermFin σ y) ∈ latH σ b v n} := by
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hc : ∀ (i j : Fin n) (k : Fin d), Continuous fun y : HermR (AF F) σ n =>
      cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k :=
    fun i j k => (continuous_cf v b k).comp (continuous_entry σ i j)
  have hset : {y : HermR (AF F) σ n | hermV σ v (hermFin σ y) ∈ latH σ b v n} =
      (⋂ i : Fin n, (fun y : HermR (AF F) σ n => algebraMap F (Fv F v) (1 / 2) *
          ∑ k, cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i i) k *
            algebraMap F (Fv F v) (Algebra.trace F E (b k))) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ _ : i < j, ⋂ k : Fin d,
        (fun y : HermR (AF F) σ n => cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k) ⁻¹'
          (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp only [Set.mem_setOf_eq, mem_latH_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) (MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun k =>
      (hO.preimage (hc i j k)).measurableSet)
  refine (hO.preimage ?_).measurableSet
  exact continuous_const.mul (continuous_finset_sum _ fun k _ => (hc i i k).mul continuous_const)

/- English proof (translation)
Use `haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F`. Establish `hset : {y : HermR (AF F) σ n | hermFin σ y ∈ intH σ b n S} = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S, {y : HermR (AF F) σ n | hermV σ v (hermFin σ y) ∈ latH σ b v n}`. Use extensionality with `y`. Simplify using `[intH]`. Rewrite using `[hset]`.

Conclude with `MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => measurableSet_latH σ b v`.
-/
theorem measurableSet_intH (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) {n : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSet {y : HermR (AF F) σ n | hermFin σ y ∈ intH σ b n S} := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have hset : {y : HermR (AF F) σ n | hermFin σ y ∈ intH σ b n S} =
      ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S,
        {y : HermR (AF F) σ n | hermV σ v (hermFin σ y) ∈ latH σ b v n} := by
    ext y
    simp [intH]
  rw [hset]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => measurableSet_latH σ b v

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Establish `hl : ∀ t : AF F ⊗[F] E, Continuous fun x : AF F ⊗[F] E => Algebra.trace (AF F) (AF F ⊗[F] E) (t * x)` using `fun t => IsModuleTopology.continuous_of_linearMap ((Algebra.trace (AF F) (AF F ⊗[F] E)).comp (LinearMap.mulLeft (AF F) t))`. Establish `hs : (fun y : HermR (AF F) σ n => Algebra.trace (AF F) (AF F ⊗[F] E) (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))) = fun y : HermR (AF F) σ n => ∑ a, ∑ c, Algebra.trace (AF F) (AF F ⊗[F] E) (T.map (inclR (AF F)) a c * (y : Matrix (Fin n) (Fin …`. Use function extensionality and compare the values at `y`. Simplify using `only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum]`.

Establish `ht : Continuous fun y : HermR (AF F) σ n => Algebra.trace (AF F) (AF F ⊗[F] E) (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))`. Rewrite using `[hs]`. Apply the tactic sequence `exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ => (hl _).comp (continuous_entry σ c a)`. Conclude with `hψ.comp (continuous_const.mul ht).neg`.
-/
theorem continuous_chiT (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (T : Matrix (Fin n) (Fin n) E) : Continuous (chiT σ ψ T) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hl : ∀ t : AF F ⊗[F] E, Continuous fun x : AF F ⊗[F] E =>
      Algebra.trace (AF F) (AF F ⊗[F] E) (t * x) := fun t =>
    IsModuleTopology.continuous_of_linearMap
      ((Algebra.trace (AF F) (AF F ⊗[F] E)).comp (LinearMap.mulLeft (AF F) t))
  have hs : (fun y : HermR (AF F) σ n => Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))) =
      fun y : HermR (AF F) σ n => ∑ a, ∑ c, Algebra.trace (AF F) (AF F ⊗[F] E)
        (T.map (inclR (AF F)) a c * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) c a) := by
    funext y
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum]
  have ht : Continuous fun y : HermR (AF F) σ n => Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))) := by
    rw [hs]
    exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ =>
      (hl _).comp (continuous_entry σ c a)
  exact hψ.comp (continuous_const.mul ht).neg

end Cont

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ M J _ n _ ψ hψ dx db Φ hI d b T`. Use `haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩`. Use `haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F`. Take `⟨hψc, hψn, -, -⟩` from `hψ`. Establish `hchar : AEStronglyMeasurable (chiT σ ψ T) db` using `(continuous_chiT σ ψ hψc T).aestronglyMeasurable`.

Establish `hf : AEStronglyMeasurable (fun y => starN σ J ψ dx Φ y * chiT σ ψ T y) db` using `hI.aestronglyMeasurable.mul hchar`. Establish `hnorm : ∀ y, ‖chiT σ ψ T y‖ = 1` using `fun y => hψn _`. Establish `hlim : coefN σ J ψ dx db Φ T = ∫ y, starN σ J ψ dx Φ y * chiT σ ψ T y ∂db` using `rfl`. Rewrite using `[hlim]`. Unfold `coefSN`.

Use `tendsto_integral_filter_of_dominated_convergence (fun y => ‖starN σ J ψ dx Φ y‖) ?_ ?_ hI.norm ?_` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun S => ?_` and prove the remaining obligations. Establish `hind : Measurable (fun y : HermR (AF F) σ n => (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y))`. Establish `he : (fun y : HermR (AF F) σ n => (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y)) = {y : HermR (AF F) σ n | hermFin σ y ∈ intH σ b n S}.indicator (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `y`.

Apply the tactic sequence `by_cases h : hermFin σ y ∈ intH σ b n S <;> simp [Set.indicator, h]`. Rewrite using `[he]`. Conclude with `measurable_const.indicator (measurableSet_intH σ b S)`. Conclude with `hind.aestronglyMeasurable.mul hf`. Use `Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun y => ?_` and prove the remaining obligations.

Establish `h1 : ‖(intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y)‖ ≤ 1`. Apply the tactic sequence `by_cases h : hermFin σ y ∈ intH σ b n S <;> simp [h]`. Rewrite using `[norm_mul, norm_mul, hnorm, mul_one]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) h1`. Use `Filter.Eventually.of_forall fun y => ?_` and prove the remaining obligations.

Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ hermV σ v (hermFin σ y) ∈ latH σ b v n}.Finite` using `Filter.eventually_cofinite.1 (ev_latH σ b y)`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS`. Establish `hmem : hermFin σ y ∈ intH σ b n S`. Introduce `v hv`.

Assume the negation of the conclusion as `hcon`. Conclude with `hv (hS (hfin.mem_toFinset.2 hcon))`. Simplify using `[hmem]`.
-/
theorem coefSN_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E), Filter.Tendsto (fun S => coefSN σ b J ψ dx db Φ T S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ ψ hψ dx db Φ hI d b T
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  have hchar : AEStronglyMeasurable (chiT σ ψ T) db := (continuous_chiT σ ψ hψc T).aestronglyMeasurable
  have hf : AEStronglyMeasurable (fun y => starN σ J ψ dx Φ y * chiT σ ψ T y) db :=
    hI.aestronglyMeasurable.mul hchar
  have hnorm : ∀ y, ‖chiT σ ψ T y‖ = 1 := fun y => hψn _
  have hlim : coefN σ J ψ dx db Φ T = ∫ y, starN σ J ψ dx Φ y * chiT σ ψ T y ∂db := rfl
  rw [hlim]
  unfold coefSN
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖starN σ J ψ dx Φ y‖) ?_ ?_ hI.norm ?_
  · refine Filter.Eventually.of_forall fun S => ?_
    have hind : Measurable (fun y : HermR (AF F) σ n =>
        (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y)) := by
      have he : (fun y : HermR (AF F) σ n => (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y)) =
          {y : HermR (AF F) σ n | hermFin σ y ∈ intH σ b n S}.indicator (fun _ => (1 : ℂ)) := by
        funext y
        by_cases h : hermFin σ y ∈ intH σ b n S <;> simp [Set.indicator, h]
      rw [he]
      exact measurable_const.indicator (measurableSet_intH σ b S)
    exact hind.aestronglyMeasurable.mul hf
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun y => ?_
    have h1 : ‖(intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y)‖ ≤ 1 := by
      by_cases h : hermFin σ y ∈ intH σ b n S <;> simp [h]
    rw [norm_mul, norm_mul, hnorm, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ hermV σ v (hermFin σ y) ∈ latH σ b v n}.Finite :=
      Filter.eventually_cofinite.1 (ev_latH σ b y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    have hmem : hermFin σ y ∈ intH σ b n S := by
      intro v hv
      by_contra hcon
      exact hv (hS (hfin.mem_toFinset.2 hcon))
    simp [hmem]

end GlobalTheory.CompanionTheory.SiegelND.Coef.Lim
