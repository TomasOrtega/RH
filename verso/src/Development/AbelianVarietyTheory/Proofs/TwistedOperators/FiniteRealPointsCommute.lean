import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.FinRealComm

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul, ← TensorProduct.add_tmul]`. Use `congr 1`.

Apply the tactic sequence `ext <;> simp`. Consider the case `add u v hu hv`. Rewrite using `[map_add, map_add, map_add, map_add]`. Use `conv_lhs => rw [hu, hv]`. Normalize the expressions using the abelian group laws.
-/
private theorem eq_map_inl_fst_add_map_inr_snd_tmul {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E) :
    z = TensorProduct.map (LinearMap.inl F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
        TensorProduct.map (LinearMap.inr F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.map_tmul, ← TensorProduct.add_tmul]
    congr 1
    ext <;> simp
  | add u v hu hv =>
    rw [map_add, map_add, map_add, map_add]
    conv_lhs => rw [hu, hv]
    abel

/- English proof (translation)
Rewrite using `[eq_map_inl_fst_add_map_inr_snd_tmul x, eq_map_inl_fst_add_map_inr_snd_tmul y, h1, h2]`.
-/
theorem tensor_prod_ext {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (x y : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) y)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) y) : x = y := by
  rw [eq_map_inl_fst_add_map_inr_snd_tmul x, eq_map_inl_fst_add_map_inr_snd_tmul y, h1, h2]

/- English proof (translation)
Establish `hm : (matHom V x).1 = (matHom V y).1`. Use extensionality with `i j`. Establish `e1` using `congrArg (fun g => g.1 i j) h1`. Establish `e2` using `congrArg (fun g => g.1 i j) h2`. Simplify using `only [infHom, finHom, MonoidHom.comp_apply, Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e1 e2`.

Conclude with `tensor_prod_ext _ _ e1 e2`. Conclude with `Subtype.ext (Units.ext hm)`.
-/
theorem GA_ext_inf_fin {D : D7} (V : HSp D) (x y : GA D V)
    (h1 : infHom V x = infHom V y) (h2 : finHom V x = finHom V y) : x = y := by
  have hm : (matHom V x).1 = (matHom V y).1 := by
    ext i j
    have e1 := congrArg (fun g => g.1 i j) h1
    have e2 := congrArg (fun g => g.1 i j) h2
    simp only [infHom, finHom, MonoidHom.comp_apply, Formalism.UG.bc, Units.coe_map,
      MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e1 e2
    exact tensor_prod_ext _ _ e1 e2
  exact Subtype.ext (Units.ext hm)

/- English proof (translation)
Introduce `D V a b ha hb`. Establish `ha' : infHom V a = 1` using `ha`. Establish `hb' : finHom V b = 1` using `hb`. Apply `GA_ext_inf_fin V` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ha', one_mul, mul_one]`.

Rewrite using `[map_mul, map_mul, hb', one_mul, mul_one]`.
-/
theorem finite_real_points_commute :
    ∀ {D : D7} (V : HSp D) (a b : GA D V), a ∈ GfC V → b ∈ GinfC V → a * b = b * a := by
  intro D V a b ha hb
  have ha' : infHom V a = 1 := ha
  have hb' : finHom V b = 1 := hb
  apply GA_ext_inf_fin V
  · rw [map_mul, map_mul, ha', one_mul, mul_one]
  · rw [map_mul, map_mul, hb', one_mul, mul_one]

end GlobalTheory.FinRealComm
