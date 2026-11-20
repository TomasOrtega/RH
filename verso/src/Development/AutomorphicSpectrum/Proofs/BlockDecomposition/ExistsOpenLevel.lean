import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AutLevel

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

/- English proof (translation)
Apply `(AdelicGLn.prodEquiv E a).injective` to reduce the goal to its premises. Rewrite using `[AutomorphicForm.prodEquiv_finEmb]`. Establish `s1 : ∀ x, (sFin E x).1 = 0` using `fun _ => rfl`. Establish `s2 : ∀ x, (sFin E x).2 = x` using `fun _ => rfl`. Use `Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).1 - (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).1 + (sFin E (k i j)).1`. Rewrite using `[s1, s1, sub_zero, add_zero]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq]`.

Both sides reduce to the same expression. Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne h]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `k.1 i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 - (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).2 + (sFin E (k i j)).2`. Rewrite using `[s2, s2]`.

Establish `h1 : ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 = (1 : Matrix (Fin a) (Fin a) (Af E)) i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq]`. Both sides reduce to the same expression.

Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne h]`. Both sides reduce to the same expression. Rewrite using `[h1, sub_self, zero_add]`.
-/
theorem finEmb_eq_finGL (k : AdelicGLn.FiniteAdelicGL E a) :
    AutomorphicForm.finEmb E a k = finGL E a k := by
  apply (AdelicGLn.prodEquiv E a).injective
  rw [AutomorphicForm.prodEquiv_finEmb]
  have s1 : ∀ x, (sFin E x).1 = 0 := fun _ => rfl
  have s2 : ∀ x, (sFin E x).2 = x := fun _ => rfl
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).1 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).1 + (sFin E (k i j)).1
    rw [s1, s1, sub_zero, add_zero]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
  · change k.1 i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).2 + (sFin E (k i j)).2
    rw [s2, s2]
    have h1 : ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 = (1 : Matrix (Fin a) (Fin a) (Af E)) i j := by
      by_cases h : i = j
      · subst h
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        rfl
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
        rfl
    rw [h1, sub_self, zero_add]

/- English proof (translation)
Introduce `E _ _ _ a φ hφ`. Set `S : Subgroup (AdelicGLn.FiniteAdelicGL E a)` to `{ carrier := {k | finRep E a k φ = φ} mul_mem' := fun {x y} hx hy => by`. Express the relevant statement in the definitionally equal form `finRep E a (x * y) φ = φ`. Rewrite using `[map_mul, Module.End.mul_apply, hy, hx]`. Use the proof step `one_mem' := by`.

Express the relevant statement in the definitionally equal form `finRep E a 1 φ = φ`. Rewrite using `[map_one, Module.End.one_apply]`. Use the proof step `inv_mem' := fun {x} hx => by`. Express the relevant statement in the definitionally equal form `finRep E a x⁻¹ φ = φ`. Establish `h : finRep E a x⁻¹ (finRep E a x φ) = φ`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Rewrite using `[hx] at h }` and apply the resulting hypothesis. Use `⟨S.subgroupOf (AdelicGLn.integralFiniteGL E a), ?_, ?_⟩` and prove the remaining obligations. Conclude with `hφ.level.preimage continuous_subtype_val`. Introduce `g u`.

Establish `hu : finRep E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a) φ = φ` using `Subgroup.mem_subgroupOf.1 u.2`. Rewrite using `[finEmb_eq_finGL]`. Conclude with `congrArg (fun ψ : Sm E a => ψ.1 g) hu`.
-/
theorem exists_open_level : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → (∃ U : Subgroup (AdelicGLn.integralFiniteGL E a), IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) ∧
    ∀ (g : AdelicGLn.AdelicGL E a) (u : U), φ.1 (g * AutomorphicForm.finEmb E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a)) = φ.1 g) := by
  intro E _ _ _ a φ hφ
  let S : Subgroup (AdelicGLn.FiniteAdelicGL E a) :=
    { carrier := {k | finRep E a k φ = φ}
      mul_mem' := fun {x y} hx hy => by
        change finRep E a (x * y) φ = φ
        rw [map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := by
        change finRep E a 1 φ = φ
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {x} hx => by
        change finRep E a x⁻¹ φ = φ
        have h : finRep E a x⁻¹ (finRep E a x φ) = φ := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [hx] at h }
  refine ⟨S.subgroupOf (AdelicGLn.integralFiniteGL E a), ?_, ?_⟩
  · exact hφ.level.preimage continuous_subtype_val
  · intro g u
    have hu : finRep E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a) φ = φ :=
      Subgroup.mem_subgroupOf.1 u.2
    rw [finEmb_eq_finGL]
    exact congrArg (fun ψ : Sm E a => ψ.1 g) hu

end GlobalTheory.CompanionTheory.AutLevel
