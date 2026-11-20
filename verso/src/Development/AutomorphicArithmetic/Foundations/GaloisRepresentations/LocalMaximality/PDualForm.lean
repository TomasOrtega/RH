import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceWedgePairingPerfectRationalFormsStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Establish `hinj : Function.Injective B` using `(injective_iff_map_eq_zero B).2 fun w hw => hB w fun y => by simp [hw]`. Establish `hs : Function.Surjective B` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [show Module.finrank F (P →ₗ[F] F) = Module.finrank F P from Subspace.dual_finrank_eq, hr])).1 hinj`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Establish `hinj' : Function.Injective B.flip`. Use `(injective_iff_map_eq_zero B.flip).2 fun y hy => ?_` and prove the remaining obligations.

Use `(Module.forall_dual_apply_eq_zero_iff F y).1 fun f => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `hs f`. Conclude with `LinearMap.congr_fun hy w`. Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [show Module.finrank F (Q →ₗ[F] F) = Module.finrank F Q from Subspace.dual_finrank_eq, hr])).1 hinj'`.
-/
private lemma perfectPairing_surjective {F Q P : Type*} [Field F] [AddCommGroup Q] [Module F Q] [AddCommGroup P] [Module F P]
    [FiniteDimensional F Q] [FiniteDimensional F P] (hr : Module.finrank F Q = Module.finrank F P)
    (B : Q →ₗ[F] P →ₗ[F] F) (hB : ∀ w, (∀ y, B w y = 0) → w = 0) :
    Function.Surjective B ∧ Function.Surjective B.flip := by
  have hinj : Function.Injective B :=
    (injective_iff_map_eq_zero B).2 fun w hw => hB w fun y => by simp [hw]
  have hs : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (P →ₗ[F] F) = Module.finrank F P from Subspace.dual_finrank_eq, hr])).1 hinj
  refine ⟨hs, ?_⟩
  have hinj' : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    refine (Module.forall_dual_apply_eq_zero_iff F y).1 fun f => ?_
    obtain ⟨w, rfl⟩ := hs f
    exact LinearMap.congr_fun hy w
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (Q →ₗ[F] F) = Module.finrank F Q from Subspace.dual_finrank_eq, hr])).1 hinj'

/- English proof (translation)
Introduce `F K _ _ _ _ _ _ d x hc τ ht a ha ψ`. Take `⟨hinj, hrk, hfdP⟩` from `GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht (d - a) a (by omega)`. Take `⟨-, -, hfdQ⟩` from `GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht a (d - a) (by omega)`. Use `haveI : FiniteDimensional F K := hc.fin`. Use `haveI : FiniteDimensional F (⋀[K]^(d - a) Ω[K⁄ℂ]) := Module.Finite.trans K _`.

Use `haveI : FiniteDimensional F (⋀[K]^a Ω[K⁄ℂ]) := Module.Finite.trans K _`. Set `T : DR ℂ K →ₗ[F] F` to `(Algebra.trace F K) ∘ₗ (τ.restrictScalars F)`. Set `B : (⋀[K]^a Ω[K⁄ℂ]) →ₗ[F] (⋀[K]^(d - a) Ω[K⁄ℂ]) →ₗ[F] F` to `LinearMap.mk₂ F (fun w y => T ((y : DR ℂ K) * (w : DR ℂ K))) (fun w w' y => by simp [mul_add]) (fun c w y => by simp [mul_smul_comm]) (fun w y y' => by simp [add_mul]) (fun c w y => by simp [smul_mul_assoc])`. Establish `hr : Module.finrank F (⋀[K]^a Ω[K⁄ℂ]) = Module.finrank F (⋀[K]^(d - a) Ω[K⁄ℂ])`. Rewrite using `[← Module.finrank_mul_finrank F K (⋀[K]^a Ω[K⁄ℂ]), ← Module.finrank_mul_finrank F K (⋀[K]^(d - a) Ω[K⁄ℂ]), hrk]`.

Take `⟨hs, hs'⟩` from `perfectPairing_surjective hr B (fun w hw => Subtype.ext (hinj w.1 w.2 fun y hy => hw ⟨y, hy⟩))`. Prove the components needed by the constructor for the conclusion. Take `⟨w, hw⟩` from `hs (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)`. Conclude with `⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩`. Take `⟨w, hw⟩` from `hs' (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)`.

Conclude with `⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩`.
-/
theorem UpperTheory.Gal.productCup_of_system.dualForm_of :
    DualForm := by
  intro F K _ _ _ _ _ _ d x hc τ ht a ha ψ
  obtain ⟨hinj, hrk, hfdP⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht (d - a) a (by omega)
  obtain ⟨-, -, hfdQ⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht a (d - a) (by omega)
  haveI : FiniteDimensional F K := hc.fin
  haveI : FiniteDimensional F (⋀[K]^(d - a) Ω[K⁄ℂ]) := Module.Finite.trans K _
  haveI : FiniteDimensional F (⋀[K]^a Ω[K⁄ℂ]) := Module.Finite.trans K _
  let T : DR ℂ K →ₗ[F] F := (Algebra.trace F K) ∘ₗ (τ.restrictScalars F)
  let B : (⋀[K]^a Ω[K⁄ℂ]) →ₗ[F] (⋀[K]^(d - a) Ω[K⁄ℂ]) →ₗ[F] F :=
    LinearMap.mk₂ F (fun w y => T ((y : DR ℂ K) * (w : DR ℂ K)))
      (fun w w' y => by simp [mul_add])
      (fun c w y => by simp [mul_smul_comm])
      (fun w y y' => by simp [add_mul])
      (fun c w y => by simp [smul_mul_assoc])
  have hr : Module.finrank F (⋀[K]^a Ω[K⁄ℂ]) = Module.finrank F (⋀[K]^(d - a) Ω[K⁄ℂ]) := by
    rw [← Module.finrank_mul_finrank F K (⋀[K]^a Ω[K⁄ℂ]),
      ← Module.finrank_mul_finrank F K (⋀[K]^(d - a) Ω[K⁄ℂ]), hrk]
  obtain ⟨hs, hs'⟩ := perfectPairing_surjective hr B (fun w hw => Subtype.ext (hinj w.1 w.2 fun y hy => hw ⟨y, hy⟩))
  constructor
  · obtain ⟨w, hw⟩ := hs (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
  · obtain ⟨w, hw⟩ := hs' (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
