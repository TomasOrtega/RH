import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoPolish
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct

namespace RestrictedProductGluing

open PositiveNearLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)

def good : Set ((Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :=
  {p | ∀ᶠ v in cofinite, p.2 v ∈ latV b v}

def mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨x, h⟩ : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

omit [FiniteDimensional F E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf x h) = x v := rfl

open Classical in

def finAd (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : Af F :=
  if h : p ∈ good b then
    mkAf (fun v => crd b (Fv F v) (p.2 v i j) k)
      ((show ∀ᶠ v in cofinite, p.2 v ∈ latV b v from h).mono fun _ hv => hv i j k)
  else 0

def crdA (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : AF F :=
  pairA F (crd b (Ainf F) (p.1 i j) k) (finAd b p i j k)

def glue (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :
    Fin a → Fin M → AF F ⊗[F] E :=
  fun i j => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm (fun k => crdA b p i j k)

/- English proof (translation)
Use `show (Algebra.TensorProduct.basis (AF F) b).repr ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k => crdA b p i j k) k = _`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem crd_glue (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : crd b (AF F) (glue b p i j) k = crdA b p i j k := by
  show (Algebra.TensorProduct.basis (AF F) b).repr
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k => crdA b p i j k) k = _
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Establish `e : good (F` using `F) (E := E) (M := M) (a := a) b = ⋃ S : Finset (HeightOneSpectrum (𝓞 F)), ⋂ v, ⋂ (_ : v ∉ S), {p | p.2 v ∈ latV b v} := by`. Use extensionality with `p`. Simplify using `only [good, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_cofinite]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨h.toFinset, fun v hv => by`. Assume the negation of the conclusion as `hc`. Conclude with `hv (h.mem_toFinset.2 hc)⟩`. Introduce and unpack `⟨S, hS⟩`. Conclude with `S.finite_toSet.subset fun v hv => by`.

Assume the negation of the conclusion as `hc`. Conclude with `hv (hS v hc)`. Rewrite using `[e]`. Establish `: ∀ v, BorelSpace (Fv F v)` using `fun v => ⟨rfl⟩`. Use `MeasurableSet.iUnion fun S => MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_` and prove the remaining obligations.

Conclude with `((measurable_pi_apply v).comp measurable_snd) (isClopen_latV b v a M).isOpen.measurableSet`.
-/
theorem measurableSet_good :
    MeasurableSet (good (F := F) (E := E) (M := M) (a := a) b) := by
  have e : good (F := F) (E := E) (M := M) (a := a) b = ⋃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ⋂ v, ⋂ (_ : v ∉ S), {p | p.2 v ∈ latV b v} := by
    ext p
    simp only [good, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_cofinite]
    constructor
    · intro h
      exact ⟨h.toFinset, fun v hv => by
        by_contra hc
        exact hv (h.mem_toFinset.2 hc)⟩
    · rintro ⟨S, hS⟩
      exact S.finite_toSet.subset fun v hv => by
        by_contra hc
        exact hv (hS v hc)
  rw [e]
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine MeasurableSet.iUnion fun S => MeasurableSet.iInter fun v =>
    MeasurableSet.iInter fun _ => ?_
  exact ((measurable_pi_apply v).comp measurable_snd)
    (isClopen_latV b v a M).isOpen.measurableSet

def coeA (x : Af F) : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v := fun v => evalV F v x

/- English proof (translation)
Establish `: BorelSpace (Af F)` using `⟨rfl⟩`. Establish `: ∀ v, BorelSpace (Fv F v)` using `fun v => ⟨rfl⟩`. Establish `: PolishSpace (Af F)` using `TopoPolish.polish_of_lcsc (Af F)`. Use `Continuous.measurableEmbedding ?_ ?_` and prove the remaining obligations. Conclude with `continuous_pi fun v => by exact RestrictedProduct.continuous_eval v`.

Introduce `x y h`. Conclude with `Subtype.ext (funext fun v => congrFun h v)`.
-/
theorem measurableEmbedding_coeA : MeasurableEmbedding (coeA (F := F)) := by
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have : PolishSpace (Af F) := TopoPolish.polish_of_lcsc (Af F)
  refine Continuous.measurableEmbedding ?_ ?_
  · exact continuous_pi fun v => by exact RestrictedProduct.continuous_eval v
  · intro x y h
    exact Subtype.ext (funext fun v => congrFun h v)

/- English proof (translation)
Establish `: ∀ v, BorelSpace (Fv F v)` using `fun v => ⟨rfl⟩`. Use `(measurableEmbedding_coeA (F := F)).measurable_comp_iff.1 ?_` and prove the remaining obligations. Establish `e : (coeA (F` using `F)) ∘ (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) = (good b).piecewise (fun p v => crd b (Fv F v) (p.2 v i j) k) 0 := by`. Use function extensionality and compare the values at `p`. Distinguish the cases in `hp : p ∈ good b`.

Use function extensionality and compare the values at `v`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ hp]`. Simplify using `only [Function.comp, coeA]`. Rewrite using `[finAd, dif_pos hp, evalV_mkAf]`. Use function extensionality and compare the values at `v`.

Rewrite using `[Set.piecewise_eq_of_notMem _ _ _ hp]`. Simplify using `only [Function.comp, coeA, Pi.zero_apply]`. Rewrite using `[finAd, dif_neg hp, map_zero]`. Rewrite using `[e]`. Use `Measurable.piecewise (measurableSet_good b) ?_ measurable_const` and prove the remaining obligations.

Conclude with `measurable_pi_lambda _ fun v => (continuous_crd b (Fv F v) k).measurable.comp ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp ((measurable_pi_apply v).comp measurable_snd)))`.
-/
theorem measurable_finAd (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) := by
  classical
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine (measurableEmbedding_coeA (F := F)).measurable_comp_iff.1 ?_
  have e : (coeA (F := F)) ∘ (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) =
      (good b).piecewise (fun p v => crd b (Fv F v) (p.2 v i j) k) 0 := by
    funext p
    by_cases hp : p ∈ good b
    · funext v
      rw [Set.piecewise_eq_of_mem _ _ _ hp]
      simp only [Function.comp, coeA]
      rw [finAd, dif_pos hp, evalV_mkAf]
    · funext v
      rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      simp only [Function.comp, coeA, Pi.zero_apply]
      rw [finAd, dif_neg hp, map_zero]
  rw [e]
  refine Measurable.piecewise (measurableSet_good b) ?_ measurable_const
  exact measurable_pi_lambda _ fun v => (continuous_crd b (Fv F v) k).measurable.comp
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply v).comp measurable_snd)))

/- English proof (translation)
Establish `: BorelSpace (Ainf F)` using `⟨rfl⟩`. Establish `: BorelSpace (Af F)` using `⟨rfl⟩`. Establish `: BorelSpace (AF F)` using `⟨rfl⟩`. Establish `hc : Continuous (fun q : Ainf F × Af F => pairA F q.1 q.2)` using `continuous_id`. Establish `hx : Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => crd b (Ainf F) (p.1 i j) k)` using `(continuous_crd b (Ainf F) k).measurable.comp ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))`.

Conclude with `hc.measurable.comp (hx.prodMk (measurable_finAd b i j k))`.
-/
theorem measurable_crdA (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => crdA b p i j k) := by
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hc : Continuous (fun q : Ainf F × Af F => pairA F q.1 q.2) := continuous_id
  have hx : Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) =>
      crd b (Ainf F) (p.1 i j) k) :=
    (continuous_crd b (Ainf F) k).measurable.comp
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
  exact hc.measurable.comp (hx.prodMk (measurable_finAd b i j k))

/- English proof (translation)
Establish `: BorelSpace (AF F)` using `⟨rfl⟩`. Establish `: BorelSpace (AF F ⊗[F] E)` using `⟨rfl⟩`. Establish `hL : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm` using `IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap)`. Conclude with `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hL.measurable.comp (measurable_pi_lambda _ fun k => measurable_crdA b i j k)`.
-/
theorem measurable_glue :
    Measurable (glue (F := F) (E := E) (M := M) (a := a) b) := by
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hL : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap)
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    hL.measurable.comp (measurable_pi_lambda _ fun k => measurable_crdA b i j k)

/- English proof (translation)
Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Use `(Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_` and prove the remaining obligations. Use `show crd b (Ainf F) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (glue b p i j)) k = crd b (Ainf F) (p.1 i j) k`. Rewrite using `[crd_map, crd_glue]`.

Both sides reduce to the same expression. Use function extensionality and compare the values at `i j`. Use `(Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_` and prove the remaining obligations. Use `show crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glue b p i j))) k = crd b (Fv F v) (p.2 v i j) k`. Rewrite using `[crd_map, crd_map, crd_glue]`.

Use `show evalV F v (finAd b p i j k) = _`. Rewrite using `[finAd, dif_pos hp, evalV_mkAf]`.
-/
theorem glue_spec (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (hp : p ∈ good b) :
    projInf (glue b p) = p.1 ∧ ∀ v, projV v (projFin (glue b p)) = p.2 v := by
  refine ⟨?_, fun v => ?_⟩
  · funext i j
    refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
    show crd b (Ainf F) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (glue b p i j)) k =
      crd b (Ainf F) (p.1 i j) k
    rw [crd_map, crd_glue]
    rfl
  · funext i j
    refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
    show crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glue b p i j))) k =
      crd b (Fv F v) (p.2 v i j) k
    rw [crd_map, crd_map, crd_glue]
    show evalV F v (finAd b p i j k) = _
    rw [finAd, dif_pos hp, evalV_mkAf]

end RestrictedProductGluing

/- English proof (translation)
Introduce `F E _ _ _ _ _ M a d b`. Conclude with `⟨RestrictedProductGluing.glue b, RestrictedProductGluing.measurable_glue b, fun p hp => RestrictedProductGluing.glue_spec b p hp⟩`.
-/
theorem rpGlue_holds : RPGlue := by
  intro F E _ _ _ _ _ M a d b
  exact ⟨RestrictedProductGluing.glue b, RestrictedProductGluing.measurable_glue b,
    fun p hp => RestrictedProductGluing.glue_spec b p hp⟩

end PI.VolStabSW
