import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Introduce `F E _ _ _ _ n _ _ σ J γ hreg hE s hs A`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hfield : IsField (E ⊗[F] F)` using `MulEquiv.isField hE (Algebra.TensorProduct.rid F F E).toMulEquiv`. Use `haveI : Nontrivial (E ⊗[F] F) := hfield.nontrivial`.

Use `haveI : CharZero (E ⊗[F] F) := charZero_of_injective_algebraMap (algebraMap F (E ⊗[F] F)).injective`. Establish `h2 : (2 : F) ≠ 0` using `two_ne_zero`. Set `t₀ : Fin s → Fˣ` to `fun _ => Units.mk0 2 h2`. Establish `hsq : A.hom F (t₀ * t₀) = 1`. Use `Units.ext ?_` and prove the remaining obligations.

Use extensionality with `i j`. Establish `hH : IsHerm (sigR σ F) (J.map (inclE (F` using `F) F)) := by`. Establish `h : cT (σ : E →+* E) J = J` using `hreg.herm`. Express the relevant statement in the definitionally equal form `cT _ _ = _`. Use `conv_rhs => rw [← h]`.

Use extensionality with `a b`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `(inclE_conj σ F _).symm`. Establish `hdet : IsUnit (J.map (inclE (F` using `F) F)).det := isUnit_det_map _ hreg.nondeg`. Establish `hsc : ∀ t, (A.hom F t : Matrix n n (E ⊗[F] F)) = ((A.hom F t : Matrix n n (E ⊗[F] F)) i i) • (1 : Matrix n n (E ⊗[F] F))`.

Introduce `t`. Take `⟨c, hc⟩` from `hU (E ⊗[F] F) hfield (sigR σ F) (sigR_sigR hreg.quad.invol F) n _ hH hdet (A.hom F t : Matrix n n (E ⊗[F] F)) (fun g hg => congrArg Units.val (hcon g hg t))`. Rewrite using `[hc]`. Simplify using the standard rewrite rules. Use `letI := hfield.toField`.

Set `f : (Fin s → Fˣ) →* E ⊗[F] F` to `{ toFun := fun t => (A.hom F t : Matrix n n (E ⊗[F] F)) i i map_one' := by simp map_mul' := fun a b => by`. Rewrite using `[map_mul, Units.val_mul, hsc a, smul_mul_assoc, one_mul]`. Simplify using `}`. Take `⟨S, C, hSC⟩` from `hL F E n σ J γ s A`. Take `⟨a, ha⟩` from `hC F (E ⊗[F] F) s f S (fun a => C a i i) (fun t => by`.

Express the relevant statement in the definitionally equal form `(A.hom F t : Matrix n n (E ⊗[F] F)) i i = _`. Rewrite using `[hSC t, Matrix.sum_apply]`. Use the proof step `rfl)`. Establish `hfix : sigR σ F (f t₀) = f t₀`. Rewrite using `[ha]`.

Simplify using `[sigR]`. Establish `hmem` using `(mem_UJ_iff_mul_adj (sigR σ F) hdet (A.hom F t₀)).1 (A.mem F t₀).1`. Establish `hadj : adj (sigR σ F) (J.map (inclE (F` using `F) F)) (A.hom F t₀ : Matrix n n (E ⊗[F] F)) = (A.hom F t₀ : Matrix n n (E ⊗[F] F)) := by`. Rewrite using `[hsc t₀, adj_smul, adj_one _ hdet]`. Conclude with `congrArg (· • (1 : Matrix n n (E ⊗[F] F))) hfix`.

Rewrite `hmem` using `[hadj]`. Rewrite using `[map_mul, Units.val_mul, hmem, Units.val_one]`. Establish `h1 : t₀ * t₀ = 1` using `A.inj F (by rw [hsq, map_one])`. Establish `h4` using `congrArg Units.val (congrFun h1 ⟨0, hs⟩)`. Simplify using `only [t₀, Pi.mul_apply, Units.val_mul, Units.val_mk0, Pi.one_apply, Units.val_one] at h4`.

Evaluate the numerical expressions using `at h4`.
-/
theorem subtorusNotCentral_of (hU : UnitaryCommutant) (hL : SubtorusLaurent)
    (hC : CharacterMonomial) : SubtorusNotCentral := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hE s hs A
  by_contra hcon
  push Not at hcon
  have hfield : IsField (E ⊗[F] F) :=
    MulEquiv.isField hE (Algebra.TensorProduct.rid F F E).toMulEquiv
  haveI : Nontrivial (E ⊗[F] F) := hfield.nontrivial
  haveI : CharZero (E ⊗[F] F) := charZero_of_injective_algebraMap (algebraMap F (E ⊗[F] F)).injective
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let t₀ : Fin s → Fˣ := fun _ => Units.mk0 2 h2
  have hsq : A.hom F (t₀ * t₀) = 1 := by
    refine Units.ext ?_
    ext i j
    have hH : IsHerm (sigR σ F) (J.map (inclE (F := F) F)) := by
      have h : cT (σ : E →+* E) J = J := hreg.herm
      change cT _ _ = _
      conv_rhs => rw [← h]
      ext a b
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      exact (inclE_conj σ F _).symm
    have hdet : IsUnit (J.map (inclE (F := F) F)).det := isUnit_det_map _ hreg.nondeg
    have hsc : ∀ t, (A.hom F t : Matrix n n (E ⊗[F] F)) =
        ((A.hom F t : Matrix n n (E ⊗[F] F)) i i) • (1 : Matrix n n (E ⊗[F] F)) := by
      intro t
      obtain ⟨c, hc⟩ := hU (E ⊗[F] F) hfield (sigR σ F) (sigR_sigR hreg.quad.invol F) n _ hH hdet
        (A.hom F t : Matrix n n (E ⊗[F] F)) (fun g hg => congrArg Units.val (hcon g hg t))
      rw [hc]; simp
    letI := hfield.toField
    let f : (Fin s → Fˣ) →* E ⊗[F] F :=
      { toFun := fun t => (A.hom F t : Matrix n n (E ⊗[F] F)) i i
        map_one' := by simp
        map_mul' := fun a b => by
          rw [map_mul, Units.val_mul, hsc a, smul_mul_assoc, one_mul]
          simp }
    obtain ⟨S, C, hSC⟩ := hL F E n σ J γ s A
    obtain ⟨a, ha⟩ := hC F (E ⊗[F] F) s f S (fun a => C a i i) (fun t => by
      change (A.hom F t : Matrix n n (E ⊗[F] F)) i i = _
      rw [hSC t, Matrix.sum_apply]
      rfl)
    have hfix : sigR σ F (f t₀) = f t₀ := by
      rw [ha]; simp [sigR]
    have hmem := (mem_UJ_iff_mul_adj (sigR σ F) hdet (A.hom F t₀)).1 (A.mem F t₀).1
    have hadj : adj (sigR σ F) (J.map (inclE (F := F) F)) (A.hom F t₀ : Matrix n n (E ⊗[F] F)) =
        (A.hom F t₀ : Matrix n n (E ⊗[F] F)) := by
      rw [hsc t₀, adj_smul, adj_one _ hdet]
      exact congrArg (· • (1 : Matrix n n (E ⊗[F] F))) hfix
    rw [hadj] at hmem
    rw [map_mul, Units.val_mul, hmem, Units.val_one]
  have h1 : t₀ * t₀ = 1 := A.inj F (by rw [hsq, map_one])
  have h4 := congrArg Units.val (congrFun h1 ⟨0, hs⟩)
  simp only [t₀, Pi.mul_apply, Units.val_mul, Units.val_mk0, Pi.one_apply, Units.val_one] at h4
  norm_num at h4

end GlobalTheory.RegSS
