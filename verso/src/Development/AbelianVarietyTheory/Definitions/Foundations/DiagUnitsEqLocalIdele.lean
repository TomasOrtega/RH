import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne

noncomputable section
open NumberField IsDedekindDomain
namespace GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v (x : v.adicCompletion L) v = x`. Conclude with `Pi.mulSingle_eq_same _ _`.
-/
theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) v = x
  exact Pi.mulSingle_eq_same _ _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v (x : v.adicCompletion L) w = 1`. Conclude with `Pi.mulSingle_eq_of_ne h _`.
-/
theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) w = 1
  exact Pi.mulSingle_eq_of_ne h _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem localIdele_fst (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) w = x`. Conclude with `Pi.mulSingle_eq_same _ _`.
-/
theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) w = x
  exact Pi.mulSingle_eq_same _ _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) u = 1`. Conclude with `Pi.mulSingle_eq_of_ne h _`.
-/
theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) u = 1
  exact Pi.mulSingle_eq_of_ne h _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infIdele_snd (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).2 = 1 := rfl

/- English proof (translation)
Introduce `x y hxy`. Apply `Units.ext` to reduce the goal to its premises. Establish `h` using `congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).2 v) hxy`. Simplify `h` using `only [localIdele_snd_self]`.
-/
theorem localIdele_injective (v : HeightOneSpectrum (𝓞 L)) : Function.Injective (localIdele L v) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).2 v) hxy
  simpa only [localIdele_snd_self] using h

/- English proof (translation)
Introduce `x y hxy`. Apply `Units.ext` to reduce the goal to its premises. Establish `h` using `congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) hxy`. Simplify `h` using `only [infIdele_fst_self]`.
-/
theorem infIdele_injective (w : InfinitePlace L) : Function.Injective (infIdele L w) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) hxy
  simpa only [infIdele_fst_self] using h

/- English proof (translation)
Introduce `a b hab`. Apply `Units.ext` to reduce the goal to its premises. Apply `NumberField.AdeleRing.algebraMap_injective (R := 𝓞 L) (K := L)` to reduce the goal to its premises. Conclude with `congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L)) hab`.
-/
theorem diagUnits_injective : Function.Injective (diagUnits L) := by
  intro a b hab
  apply Units.ext
  apply NumberField.AdeleRing.algebraMap_injective (R := 𝓞 L) (K := L)
  exact congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L)) hab

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagUnits_snd (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ) :
    ((diagUnits L a : Ideles L) : AdeleRing (𝓞 L) L).2 v = algebraMap L (v.adicCompletion L) a := rfl

/- English proof (translation)
Conclude with `Continuous.units_map _ ((continuous_mulSingle w).prodMk continuous_const)`.
-/
theorem infIdele_continuous (w : InfinitePlace L) : Continuous (infIdele L w) := by
  classical
  exact Continuous.units_map _ ((continuous_mulSingle w).prodMk continuous_const)

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : IsTopologicalGroup (Ideles L) := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : CommGroup (Ideles L) := inferInstance

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagUnits_fst (w : InfinitePlace L) (a : Lˣ) :
    ((diagUnits L a : Ideles L) : AdeleRing (𝓞 L) L).1 w = algebraMap L w.Completion a := rfl

/- English proof (translation)
Establish `hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 L)))`. Rewrite using `[Filter.le_principal_iff]`. Conclude with `(Set.finite_singleton v).compl_mem_cofinite`. Set `g : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal {v}ᶜ)` to `fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw => by`. Rewrite using `[Pi.mulSingle_eq_of_ne (Set.mem_compl_singleton_iff.mp hw)]`.

Conclude with `one_mem _⟩`. Establish `hg : Continuous g` using `RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle v)`. Establish `hfg : (finSingle L v : v.adicCompletion L → FiniteAdeleRing (𝓞 L) L) = RestrictedProduct.inclusion _ _ hS ∘ g`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression.

Rewrite using `[hfg]`. Conclude with `(RestrictedProduct.continuous_inclusion hS).comp hg`.
-/
theorem finSingle_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (finSingle L v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 L))) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal {v}ᶜ) :=
    fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.mulSingle_eq_of_ne (Set.mem_compl_singleton_iff.mp hw)]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle v)
  have hfg : (finSingle L v : v.adicCompletion L → FiniteAdeleRing (𝓞 L) L) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    funext x
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

/- English proof (translation)
Conclude with `Continuous.units_map _ (continuous_const.prodMk (finSingle_continuous L v))`.
-/
theorem localIdele_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  exact Continuous.units_map _ (continuous_const.prodMk (finSingle_continuous L v))

/- English proof (translation)
Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace L))`. Establish `h1` using `congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) h`. Simplify using `only [diagUnits_fst, localIdele_fst] at h1`. Apply `Units.ext` to reduce the goal to its premises. Apply `(algebraMap L w.Completion).injective` to reduce the goal to its premises.

Rewrite using `[h1, Units.val_one, map_one]`. Both sides reduce to the same expression.
-/
theorem diagUnits_eq_localIdele (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ) (x : (v.adicCompletion L)ˣ)
    (h : diagUnits L a = localIdele L v x) : a = 1 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have h1 := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) h
  simp only [diagUnits_fst, localIdele_fst] at h1
  apply Units.ext
  apply (algebraMap L w.Completion).injective
  rw [h1, Units.val_one, map_one]
  rfl

/- English proof (translation)
Establish `h1` using `congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).2 v) h`. Establish `h2` using `congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) h`. Simplify using `only [localIdele_snd_self, infIdele_snd, localIdele_fst, infIdele_fst_self] at h1 h2`. Conclude with `⟨Units.ext (h1.trans rfl), Units.ext (h2.symm.trans rfl)⟩`.
-/
theorem localIdele_eq_infIdele (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (v.adicCompletion L)ˣ)
    (y : (w.Completion)ˣ) (h : localIdele L v x = infIdele L w y) : x = 1 ∧ y = 1 := by
  have h1 := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).2 v) h
  have h2 := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) h
  simp only [localIdele_snd_self, infIdele_snd, localIdele_fst, infIdele_fst_self] at h1 h2
  exact ⟨Units.ext (h1.trans rfl), Units.ext (h2.symm.trans rfl)⟩

/- English proof (translation)
Introduce `h`. Establish `h1 : (-1 : Lˣ) = 1` using `diagUnits_injective L (h.trans (map_one _).symm)`. Establish `h2 : ((-1 : Lˣ) : L) = ((1 : Lˣ) : L)` using `congrArg Units.val h1`. Simplify using `only [Units.val_neg, Units.val_one] at h2`. Establish `h3 : (2 : L) = 0` using `by linear_combination -h2`.

Conclude with `two_ne_zero h3`.
-/
theorem diagUnits_neg_one_ne : diagUnits L (-1) ≠ 1 := by
  intro h
  have h1 : (-1 : Lˣ) = 1 := diagUnits_injective L (h.trans (map_one _).symm)
  have h2 : ((-1 : Lˣ) : L) = ((1 : Lˣ) : L) := congrArg Units.val h1
  simp only [Units.val_neg, Units.val_one] at h2
  have h3 : (2 : L) = 0 := by linear_combination -h2
  exact two_ne_zero h3

end GlobalTheory.Mem.Chr.Model
