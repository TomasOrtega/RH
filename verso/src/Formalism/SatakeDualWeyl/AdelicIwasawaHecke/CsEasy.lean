import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

noncomputable section

open Matrix NumberField

namespace Formalism.UG.P

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities.
-/
theorem sigma_involution_holds : Formalism.UG.CS.SigmaInvol := by
  intro F E _ _ _ _ _ σ hσ e
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have h : ∀ x, τ (σ x) = starRingEnd ℂ (τ x) := fun x => by
    simpa using RingHom.congr_fun (hσ τ) x
  apply τ.injective
  rw [h, h, Complex.conj_conj]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem csEasy_stdLat_eq_range (E : Type) [Field E] [NumberField E] (n : Type) [Fintype n]
    [DecidableEq n] :
    Formalism.UG.stdLat (n := n) (A := E) (𝓞 E) =
      LinearMap.range (LinearMap.pi (fun i : n =>
        (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i))) := by
  ext x
  simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i => by simpa using hy i⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, by simp⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem standard_lattice_full_holds : Formalism.UG.CS.StdLatFull := by
  intro E _ _ n _ _
  refine ⟨?_, ?_⟩
  · rw [csEasy_stdLat_eq_range]
    infer_instance
  · rw [eq_top_iff, ← (Pi.basisFun E n).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    show Pi.basisFun E n i ∈ Formalism.UG.stdLat (n := n) (A := E) (𝓞 E)
    simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
      Pi.basisFun_apply]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem csEasy_formJ_apply {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ e, σ (σ e) = e)
    {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (c : E) (x y : n → E) :
    Formalism.UG.CS.formJ σ hσ J c x y = c * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.CS.formJ Formalism.UG.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show σ (x i) * (y j * (c * J i j)) = c * (σ (x i) * J i j * y j)
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem hermitian_form_symmetry_holds : Formalism.UG.CS.FormSymm := by
  intro E _ σ hσ n _ _ J c hc hJ
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using this
  refine ⟨?_, fun x y => csEasy_formJ_apply σ hσ J c x y⟩
  constructor
  intro x y
  rw [csEasy_formJ_apply, csEasy_formJ_apply]
  show σ (c * Formalism.UG.hform σ J x y) = c * Formalism.UG.hform σ J y x
  rw [map_mul, hc]
  congr 1
  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private lemma hform_mulVec_mulVec_of_cT_mul_mul_eq {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (J M : Matrix n n E) (x y : n → E) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (A : Matrix n n E) (u v : n → E),
      Formalism.UG.hform σ A u v = (fun i => σ (u i)) ⬝ᵥ (A *ᵥ v) := by
    intro A u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((M *ᵥ x) i)) = (M.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    simp [mulVec, dotProduct, map_sum]
  rw [e, e, hs, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Formalism.UG.cT]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private lemma hform_single_single_stabilizer_orbit_volume {E : Type} [Field E] (σ : E →+* E) {n : Type} [Fintype n]
    [DecidableEq n] (A : Matrix n n E) (i j : n) :
    Formalism.UG.hform σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [Formalism.UG.hform, Pi.single_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem unitary_isometry_lattice_holds : Formalism.UG.CS.IsomUJ := by
  intro E _ σ hσ n _ _ J c hc hcσ g
  have hg : ∀ x, Formalism.UG.glEquiv g x = (g : Matrix n n E) *ᵥ x := fun x => rfl
  show Formalism.UG.cT σ (g : Matrix n n E) * J * (g : Matrix n n E) = J ↔ _
  show _ ↔ ∀ x y, _ = _
  simp only [hg, csEasy_formJ_apply, hform_mulVec_mulVec_of_cT_mul_mul_eq, mul_right_inj' hc]
  constructor
  · intro h x y
    rw [h]
  · intro h
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_single_single_stabilizer_orbit_volume, hform_single_single_stabilizer_orbit_volume] at this

end Formalism.UG.P
