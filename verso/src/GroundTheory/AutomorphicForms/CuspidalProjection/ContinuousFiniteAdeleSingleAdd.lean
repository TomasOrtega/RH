import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.CuspidalProjection.Unfold
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.GlobalFields.LocalFieldAtPlace

open MeasureTheory Set Function Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalProjection

open Reduction AutomorphicForm CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ} (v : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
Establish `hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 {v}ᶜ`. Rewrite using `[Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]`. Conclude with `Set.finite_singleton v`. Set `g : v.adicCompletion K → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (𝓟 {v}ᶜ)` to `fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x, Filter.eventually_principal.2 fun w hw => by`. Rewrite using `[Pi.single_eq_of_ne (Set.mem_compl_singleton_iff.1 hw)]`.

Conclude with `zero_mem _⟩`. Establish `hs : Continuous fun x : v.adicCompletion K => Pi.single (M` using `fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x := continuous_single v`. Establish `hg : Continuous g` using `RestrictedProduct.continuous_rng_of_principal.2 hs`. Establish `heq : (GroundTheory.Global.finiteAdeleSingleAdd (K` using `K) v : v.adicCompletion K → _) = RestrictedProduct.inclusion _ _ hle ∘ g := by`. Use function extensionality and compare the values at `x`.

Both sides reduce to the same expression. Rewrite using `[heq]`. Conclude with `(RestrictedProduct.continuous_inclusion hle).comp hg`.
-/
theorem continuous_finiteAdeleSingleAdd :
    Continuous (GroundTheory.Global.finiteAdeleSingleAdd (K := K) v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 {v}ᶜ := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact Set.finite_singleton v
  let g : v.adicCompletion K → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (𝓟 {v}ᶜ) := fun x =>
    ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x,
      Filter.eventually_principal.2 fun w hw => by
        rw [Pi.single_eq_of_ne (Set.mem_compl_singleton_iff.1 hw)]
        exact zero_mem _⟩
  have hs : Continuous fun x : v.adicCompletion K =>
      Pi.single (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x :=
    continuous_single v
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.2 hs
  have heq : (GroundTheory.Global.finiteAdeleSingleAdd (K := K) v : v.adicCompletion K → _) =
      RestrictedProduct.inclusion _ _ hle ∘ g := by
    funext x
    rfl
  rw [heq]
  exact (RestrictedProduct.continuous_inclusion hle).comp hg

def adeleSingle : v.adicCompletion K →+ 𝔸[K] :=
  (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
    (GroundTheory.Global.finiteAdeleSingleAdd v)

/- English proof (translation)
The claim follows from `continuous_const.prodMk (continuous_finiteAdeleSingleAdd v)`.
-/
theorem continuous_adeleSingle : Continuous (adeleSingle (K := K) v) :=
  continuous_const.prodMk (continuous_finiteAdeleSingleAdd v)

def evAt : 𝔸[K] →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) v).comp
    (RingHom.snd _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evAt_apply (x : 𝔸[K]) : evAt v x = x.2 v := rfl

/- English proof (translation)
The claim follows from `GroundTheory.Global.finiteAdeleSingleAdd_apply_self v x`.
-/
theorem evAt_adeleSingle (x : v.adicCompletion K) : evAt v (adeleSingle v x) = x :=
  GroundTheory.Global.finiteAdeleSingleAdd_apply_self v x

def compAt : AdelicGLn.AdelicGL K n →* GL (Fin n) (v.adicCompletion K) :=
  (RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 K) => GL (Fin n) (w.adicCompletion K)) v).comp
    ((MonoidHom.snd _ _).comp (AdelicGLn.restrictedProductEquiv K n).toMonoidHom)

/- English proof (translation)
The claim follows from `AdelicGLn.restrictedProductEquiv_apply_snd K n g v a b`.
-/
theorem compAt_apply (g : AdelicGLn.AdelicGL K n) (a b : Fin n) :
    (compAt v g : GL (Fin n) (v.adicCompletion K)) a b = ((g : AdelicGLn.AdelicMatrix K n) a b).2 v :=
  AdelicGLn.restrictedProductEquiv_apply_snd K n g v a b

/- English proof (translation)
The claim follows from `(RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (AdelicGLn.restrictedProductEquiv K n).continuous)`.
-/
theorem continuous_compAt : Continuous (compAt (K := K) (n := n) v) :=
  (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (AdelicGLn.restrictedProductEquiv K n).continuous)

def awayAt : 𝔸[K] →+*
    InfiniteAdeleRing K × ((w : {w : HeightOneSpectrum (𝓞 K) // w ≠ v}) → w.1.adicCompletion K) :=
  (RingHom.fst _ _).prod (RingHom.pi fun w =>
    (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 K) => u.adicCompletion K) w.1).comp
      (RingHom.snd _ _))

def AgreeAway (g g' : AdelicGLn.AdelicGL K n) : Prop :=
  (awayAt v).mapMatrix (g : AdelicGLn.AdelicMatrix K n) =
    (awayAt v).mapMatrix (g' : AdelicGLn.AdelicMatrix K n)

variable (n r) in

def unipAt (y : UPos n r → v.adicCompletion K) : normOneGL K n :=
  unipOne K n r fun p => adeleSingle v (y p)

/- English proof (translation)
Rewrite using `[unipAt, unipAt, unipAt, ← unipOne_add]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `[map_add]`.
-/
theorem unipAt_add (y y' : UPos n r → v.adicCompletion K) :
    unipAt n r v (y + y') = unipAt n r v y * unipAt n r v y' := by
  rw [unipAt, unipAt, unipAt, ← unipOne_add]
  congr 1
  funext p
  simp [map_add]

/- English proof (translation)
The claim follows from `(continuous_unipOne (K := K) (n := n) r).comp (continuous_pi fun p => (continuous_adeleSingle v).comp (continuous_apply p))`.
-/
theorem continuous_unipAt : Continuous (unipAt (K := K) n r v) :=
  (continuous_unipOne (K := K) (n := n) r).comp (continuous_pi fun p => (continuous_adeleSingle v).comp
    (continuous_apply p))

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Use `show (compAt v ((unipAt n r v y : normOneGL K n) : AdelicGLn.AdelicGL K n) : GL (Fin n) (v.adicCompletion K)) a b = (unipGL y : GL (Fin n) (v.adicCompletion K)) a b`. Rewrite using `[compAt_apply, ← evAt_apply]`. Simplify using `only [unipAt, coe_unipOne, coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply, map_add]`. Apply the tactic sequence `split_ifs <;> simp [evAt_adeleSingle]`.
-/
theorem compAt_unipAt (y : UPos n r → v.adicCompletion K) :
    compAt v ((unipAt n r v y : normOneGL K n) : AdelicGLn.AdelicGL K n) = unipGL y := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  show (compAt v ((unipAt n r v y : normOneGL K n) : AdelicGLn.AdelicGL K n) :
    GL (Fin n) (v.adicCompletion K)) a b = (unipGL y : GL (Fin n) (v.adicCompletion K)) a b
  rw [compAt_apply, ← evAt_apply]
  simp only [unipAt, coe_unipOne, coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply,
    Matrix.one_apply, map_add]
  split_ifs <;> simp [evAt_adeleSingle]

def unipCoord (g : normOneGL K n) : UPos n r → v.adicCompletion K := fun p =>
  (compAt v (g : AdelicGLn.AdelicGL K n) : GL (Fin n) (v.adicCompletion K)) p.1.1 p.1.2

/- English proof (translation)
Use `continuous_pi fun p => ?_` and prove the remaining obligations. Establish `h : Continuous fun g : GL (Fin n) (v.adicCompletion K) => (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) p.1.1 p.1.2` using `Units.continuous_val.matrix_elem p.1.1 p.1.2`. Conclude with `h.comp ((continuous_compAt v).comp continuous_subtype_val)`.
-/
theorem continuous_unipCoord : Continuous (unipCoord (K := K) (n := n) (r := r) v) := by
  refine continuous_pi fun p => ?_
  have h : Continuous fun g : GL (Fin n) (v.adicCompletion K) =>
      (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) p.1.1 p.1.2 :=
    Units.continuous_val.matrix_elem p.1.1 p.1.2
  exact h.comp ((continuous_compAt v).comp continuous_subtype_val)

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [unipCoord, compAt_unipAt, coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply, dif_pos p.2]`. Establish `hne : p.1.1 ≠ p.1.2` using `fun e => by have := p.2; rw [e] at this; omega`. Rewrite using `[Matrix.one_apply_ne hne, zero_add]`.
-/
theorem unipCoord_unipAt (y : UPos n r → v.adicCompletion K) :
    unipCoord v (unipAt n r v y) = y := by
  funext p
  simp only [unipCoord, compAt_unipAt, coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply,
    dif_pos p.2]
  have hne : p.1.1 ≠ p.1.2 := fun e => by have := p.2; rw [e] at this; omega
  rw [Matrix.one_apply_ne hne, zero_add]

/- English proof (translation)
The claim follows from `continuous_unipAt v map_add := unipAt_add v isCompact_preimage _ hC := (hC.image (continuous_unipCoord v)).of_isClosed_subset (hC.isClosed.preimage (continuous_unipAt v)) fun y hy => ⟨_, hy, unipCoord_unipAt v y⟩`.
-/
theorem isProperHom_unipAt : IsProperHom (unipAt (K := K) n r v) where
  continuous := continuous_unipAt v
  map_add := unipAt_add v
  isCompact_preimage _ hC :=
    (hC.image (continuous_unipCoord v)).of_isClosed_subset
      (hC.isClosed.preimage (continuous_unipAt v)) fun y hy => ⟨_, hy, unipCoord_unipAt v y⟩

end CuspidalProjection

end

end GroundTheory.Automorphic
