import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Set `S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M')` to `{ carrier := {z | R ∘ₗ z.1 = z.2 ∘ₗ R} mul_mem' := fun {x y} hx hy => by`. Express the relevant statement in the definitionally equal form `R ∘ₗ (x.1 ∘ₗ y.1) = (x.2 ∘ₗ y.2) ∘ₗ R`. Rewrite using `[← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]`. Use the proof step `add_mem' := fun {x y} hx hy => by`. Express the relevant statement in the definitionally equal form `R ∘ₗ (x.1 + y.1) = (x.2 + y.2) ∘ₗ R`.

Rewrite using `[LinearMap.comp_add, LinearMap.add_comp, hx, hy]`. Use the proof step `algebraMap_mem' := fun c => by`. Express the relevant statement in the definitionally equal form `R ∘ₗ (algebraMap ℂ (Module.End ℂ M) c) = (algebraMap ℂ (Module.End ℂ M') c) ∘ₗ R`. Use extensionality with `φ`. Simplify using `}`.

Set `Z : Fin k → Fin k → S` to `fun p q => ⟨(X p q, Y p q), h p q⟩`. Establish `e1 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 = Formalism.REAL.qdet X v` using `map_qdet ((AlgHom.fst ℂ _ _).comp S.val) Z v`. Establish `e2 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 = Formalism.REAL.qdet Y v` using `map_qdet ((AlgHom.snd ℂ _ _).comp S.val) Z v`. Rewrite using `[← e1, ← e2]`. Conclude with `(Formalism.REAL.qdet Z v).2`.
-/
private theorem qdet_intertw {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {k : ℕ}
    (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q, R ∘ₗ X p q = Y p q ∘ₗ R) (v : ℂ) :
    R ∘ₗ Formalism.REAL.qdet X v = Formalism.REAL.qdet Y v ∘ₗ R := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | R ∘ₗ z.1 = z.2 ∘ₗ R}
      mul_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 ∘ₗ y.1) = (x.2 ∘ₗ y.2) ∘ₗ R
        rw [← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]
      add_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 + y.1) = (x.2 + y.2) ∘ₗ R
        rw [LinearMap.comp_add, LinearMap.add_comp, hx, hy]
      algebraMap_mem' := fun c => by
        change R ∘ₗ (algebraMap ℂ (Module.End ℂ M) c) = (algebraMap ℂ (Module.End ℂ M') c) ∘ₗ R
        ext φ; simp }
  let Z : Fin k → Fin k → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 = Formalism.REAL.qdet X v :=
    map_qdet ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 = Formalism.REAL.qdet Y v :=
    map_qdet ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]
  exact (Formalism.REAL.qdet Z v).2

/- English proof (translation)
Introduce `E _ _ _ a π Ξ`. Set `f : Module.End ℂ π.V →ₐ[ℂ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))` to `Module.End.rTensorAlgHom ℂ π.V (Fin Ξ.d → ℂ)`. Establish `hf : ∀ X, lieA π Ξ X = f (lieOp π X)` using `fun _ => rfl`. Use `⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩` and prove the remaining obligations. Rewrite using `[hf, hf, hf, ← map_mul f, ← map_mul f, ← map_sub f]`.

Use `congr 1`. Conclude with `LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun ((lie_comm (toL X) (toL Y)).trans (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm) φ.1)`. Use `TensorProduct.ext' fun φ v => ?_` and prove the remaining obligations. Establish `h1 : π.op (.cpt k) (lieOp π (toL X) φ) = lieOp π (toL (k.1 * X * star k.1)) (π.op (.cpt k) φ)` using `Subtype.ext (LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ.1)`. Simplify using `only [Module.End.mul_apply, tensorK, lieA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]`.

Establish `e : eL (N` using `Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ = fun i j => f (eL (N := Module.End ℂ π.V) (lieOp π) τ i j) := by`. Use function extensionality and compare the values at `i j`. Simplify using `only [eL, hf, map_smul, map_sub]`. Establish `h` using `qdet_intertw π.V.subtype (eL (N := Module.End ℂ π.V) (lieOp π) τ) (Eop τ) (fun _ _ => rfl) (u + ((a : ℂ) - 1) / 2)`. Establish `h2 : Formalism.REAL.qdet (eL (N` using `Module.End ℂ π.V) (lieOp π) τ) (u + ((a : ℂ) - 1) / 2) = (m.map (u + ·)).prod • (1 : Module.End ℂ π.V) := LinearMap.ext fun φ => Subtype.ext ((LinearMap.congr_fun h φ).trans (hm.2 u φ.1 φ.2))`.

Rewrite using `[e, ← map_qdet, h2, map_smul, map_one]`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.tensA :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), IsLieHom (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) ∧
      (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), tensorK π Ξ k * lieA π Ξ (toL X) = lieA π Ξ (toL (k.1 * X * star k.1)) * tensorK π Ξ k) ∧
      ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ u : ℂ,
        Formalism.REAL.qdet (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ) (u + ((a : ℂ) - 1) / 2) =
          (m.map (u + ·)).prod • (1 : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) := by
  intro E _ _ _ a π Ξ
  let f : Module.End ℂ π.V →ₐ[ℂ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) := Module.End.rTensorAlgHom ℂ π.V (Fin Ξ.d → ℂ)
  have hf : ∀ X, lieA π Ξ X = f (lieOp π X) := fun _ => rfl
  refine ⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩
  · rw [hf, hf, hf, ← map_mul f, ← map_mul f, ← map_sub f]
    congr 1
    exact LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun ((lie_comm (toL X) (toL Y)).trans
      (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm) φ.1)
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : π.op (.cpt k) (lieOp π (toL X) φ) = lieOp π (toL (k.1 * X * star k.1)) (π.op (.cpt k) φ) :=
      Subtype.ext (LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ.1)
    simp only [Module.End.mul_apply, tensorK, lieA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · have e : eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ =
        fun i j => f (eL (N := Module.End ℂ π.V) (lieOp π) τ i j) := by
      funext i j
      simp only [eL, hf, map_smul, map_sub]
    have h := qdet_intertw π.V.subtype (eL (N := Module.End ℂ π.V) (lieOp π) τ) (Eop τ) (fun _ _ => rfl)
      (u + ((a : ℂ) - 1) / 2)
    have h2 : Formalism.REAL.qdet (eL (N := Module.End ℂ π.V) (lieOp π) τ) (u + ((a : ℂ) - 1) / 2) =
        (m.map (u + ·)).prod • (1 : Module.End ℂ π.V) :=
      LinearMap.ext fun φ => Subtype.ext ((LinearMap.congr_fun h φ).trans (hm.2 u φ.1 φ.2))
    rw [e, ← map_qdet, h2, map_smul, map_one]
