import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

/- English proof (translation)
Introduce `k O C W V _ _ _ _ _ _ _ _ _ _ σW τ χ hτ`. Establish `hker : ∀ T : W →ₗ[k] V, T ∈ homO σW τ → mSub σW χ ⊤ ≤ LinearMap.ker T`. Introduce `T hT`. Rewrite `hT` using `[mem_homO]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `z ⟨c, x, -, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hT, hτ, LinearMap.smul_apply, Module.End.one_apply, sub_self]`. Set `qa` to `qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))`. Set `e : homO qa τ ≃ₗ[k] homO σW τ` to `{ toFun := fun f => ⟨f.1 ∘ₗ (mSub σW χ ⊤).mkQ, by`. Rewrite using `[mem_homO]`.

Introduce `a x`. Establish `h` using `(mem_homO _ _ _).mp f.2 a ((mSub σW χ ⊤).mkQ x)`. Express the relevant statement in the definitionally equal form `f.1 ((mSub σW χ ⊤).mkQ (σW a x)) = τ a (f.1 ((mSub σW χ ⊤).mkQ x))`. Rewrite using `[← qAct_mk]`. Conclude with `h⟩`.

Use `invFun := fun T => ⟨(mSub σW χ ⊤).liftQ T.1 (hker T.1 T.2), by`. Rewrite using `[mem_homO]`. Introduce `a y`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H x`.

Establish `h` using `(mem_homO _ _ _).mp T.2 a x`. Express the relevant statement in the definitionally equal form `(mSub σW χ ⊤).liftQ T.1 _ (qa a ((mSub σW χ ⊤).mkQ x)) = τ a ((mSub σW χ ⊤).liftQ T.1 _ ((mSub σW χ ⊤).mkQ x))`. Simplify using `only [qa, qAct_mk, Submodule.liftQ_mkQ, Submodule.mkQ_apply, Submodule.liftQ_apply]`. Conclude with `h⟩`. Use the proof step `map_add' := fun f g => by ext; rfl`.

Use the proof step `map_smul' := fun c f => by ext; rfl`. Use `left_inv := fun f => by`. Use extensionality with `y`. Both sides reduce to the same expression. Use `right_inv := fun T => by ext; rfl }`.

Conclude with `e.finrank_eq.symm`.
-/
theorem finrank_homO_eq_quot_mSub : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k),
    (∀ c, τ (algebraMap C O c) = χ c • 1) →
    finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  intro k O C W V _ _ _ _ _ _ _ _ _ _ σW τ χ hτ
  have hker : ∀ T : W →ₗ[k] V, T ∈ homO σW τ → mSub σW χ ⊤ ≤ LinearMap.ker T := by
    intro T hT
    rw [mem_homO] at hT
    refine Submodule.span_le.mpr ?_
    rintro z ⟨c, x, -, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hT, hτ, LinearMap.smul_apply,
      Module.End.one_apply, sub_self]
  let qa := qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))
  let e : homO qa τ ≃ₗ[k] homO σW τ :=
    { toFun := fun f => ⟨f.1 ∘ₗ (mSub σW χ ⊤).mkQ, by
        rw [mem_homO]
        intro a x
        have h := (mem_homO _ _ _).mp f.2 a ((mSub σW χ ⊤).mkQ x)
        change f.1 ((mSub σW χ ⊤).mkQ (σW a x)) = τ a (f.1 ((mSub σW χ ⊤).mkQ x))
        rw [← qAct_mk]
        exact h⟩
      invFun := fun T => ⟨(mSub σW χ ⊤).liftQ T.1 (hker T.1 T.2), by
        rw [mem_homO]
        intro a y
        induction y using Submodule.Quotient.induction_on with
        | H x =>
          have h := (mem_homO _ _ _).mp T.2 a x
          change (mSub σW χ ⊤).liftQ T.1 _ (qa a ((mSub σW χ ⊤).mkQ x)) = τ a ((mSub σW χ ⊤).liftQ T.1 _ ((mSub σW χ ⊤).mkQ x))
          simp only [qa, qAct_mk, Submodule.liftQ_mkQ, Submodule.mkQ_apply, Submodule.liftQ_apply]
          exact h⟩
      map_add' := fun f g => by ext; rfl
      map_smul' := fun c f => by ext; rfl
      left_inv := fun f => by
        ext y
        rfl
      right_inv := fun T => by ext; rfl }
  exact e.finrank_eq.symm

end GlobalTheory.HTRho
