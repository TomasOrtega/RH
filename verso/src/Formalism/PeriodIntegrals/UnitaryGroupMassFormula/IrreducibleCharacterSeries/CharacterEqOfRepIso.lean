import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.IrrCharIff

noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT

namespace PI.SerBridgeGLW

section
variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem card_ne_zero' : (Nat.card G : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem isChar_of_fdrep (V : FDRep ℂ G) : IsChar V.character := by
  classical
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V,
    MonoidHom.toHomUnits ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp V.ρ), fun x => ?_⟩
  simp [FDRep.character, LinearMap.trace_eq_matrix_trace ℂ b]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem ipG_eq (hC : ConjChar) (V : FDRep ℂ G) :
    ipG V.character V.character = ∑ x, V.character x * V.character x⁻¹ := by
  unfold ipG
  exact Finset.sum_congr rfl fun x _ => by rw [hC G V x]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem isIrrChar_of_simple (hC : ConjChar) (V : FDRep ℂ G) [Simple V] : IsIrrChar V.character := by
  refine ⟨isChar_of_fdrep V, ?_⟩
  rw [ipG_eq hC, (FDRep.simple_iff_char_is_norm_one V).mp inferInstance, Nat.card_eq_fintype_card]

def repOfGL {n : ℕ} (ρ : G →* GL (Fin n) ℂ) : FDRep ℂ G :=
  FDRep.of (((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ)).toRingEquiv.toMonoidHom).comp
    ((Units.coeHom _).comp ρ))

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem repOfGL_character {n : ℕ} (ρ : G →* GL (Fin n) ℂ) (x : G) :
    (repOfGL ρ).character x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ) := by
  change LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLinAlgEquiv' (ρ x : Matrix (Fin n) (Fin n) ℂ)) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
  congr 1
  exact LinearMap.toMatrix'_toLin' _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Substitute using the available equality.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem irrCharIff_of (hC : ConjChar) : IrrCharIff := by
  intro G _ _ χ
  constructor
  · rintro ⟨⟨n, ρ, hρ⟩, hip⟩
    have hχ : χ = (repOfGL ρ).character := funext fun x => by rw [hρ, repOfGL_character]
    subst hχ
    refine ⟨repOfGL ρ, ?_, rfl⟩
    rw [FDRep.simple_iff_char_is_norm_one, ← ipG_eq hC, hip, Nat.card_eq_fintype_card]
  · rintro ⟨V, hV, rfl⟩
    exact isIrrChar_of_simple hC V

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem iso_of_character_eq (V W : FDRep ℂ G) [Simple V] [Simple W] (h : V.character = W.character) :
    Nonempty (V ≅ W) := by
  classical
  haveI : Invertible ((Nat.card G : ℕ) : ℂ) := invertibleOfNonzero card_ne_zero'
  have h1 := FDRep.char_orthonormal V W
  have h2 := FDRep.char_orthonormal V V
  rw [if_pos ⟨Iso.refl V⟩] at h2
  rw [← h, h2] at h1
  by_contra hn
  rw [if_neg hn] at h1
  exact one_ne_zero h1

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem repIso_of_iso {V W : FDRep ℂ G} (i : V ≅ W) : RepIso V.ρ W.ρ := ⟨FDRep.isoToLinearEquiv i, fun γ v => by
    rw [FDRep.Iso.conj_ρ i γ]
    simp [LinearEquiv.conj_apply]⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem character_eq_of_repIso {V W : FDRep ℂ G} (h : RepIso V.ρ W.ρ) : V.character = W.character := by
  obtain ⟨e, he⟩ := h
  funext γ
  show LinearMap.trace ℂ V (V.ρ γ) = LinearMap.trace ℂ W (W.ρ γ)
  have hc : W.ρ γ = e.conj (V.ρ γ) := by
    ext w
    have h1 := he γ (e.symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    exact h1.symm
  rw [hc, LinearMap.trace_conj']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem irrSys_of (hC : ConjChar) : IrrSys := by
  intro G _ _ I _ ρ hs hi he
  have hI := irrCharIff_of hC
  refine ⟨fun χ => ⟨fun hχ => ?_, ?_⟩, fun i j hij => ?_⟩
  · obtain ⟨V, hV, rfl⟩ := (hI G χ).mp hχ
    obtain ⟨i, hi'⟩ := he V hV
    exact ⟨i, character_eq_of_repIso hi'⟩
  · rintro ⟨i, rfl⟩
    exact (hI G _).mpr ⟨ρ i, hs i, rfl⟩
  · haveI := hs i; haveI := hs j
    obtain ⟨e⟩ := iso_of_character_eq (ρ i) (ρ j) hij
    exact hi i j (repIso_of_iso e)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem eOf_eq_zIdem (V : FDRep ℂ G) : eOf V.character = zIdem V := by
  apply MonoidAlgebra.coeff_injective
  ext x
  rw [zIdem_coeff, eOf, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm, FDRep.char_one]
  rfl

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem serSum_of (hC : ConjChar) : SerSum := by
  intro g _ cv r I _ ρ hs hi he f
  classical
  obtain ⟨hchar, hinj⟩ := irrSys_of hC _ I ρ hs hi he
  set χ : I → (GL (Fin r) (ZMod g) → ℂ) := fun i => (ρ i).character with hχ
  set s : Set I := {i | InSeries cv.ι cv.gen (χ i) f}
  have hset : {ψ : GL (Fin r) (ZMod g) → ℂ | IsIrrChar ψ ∧ InSeries cv.ι cv.gen ψ f} = χ '' s := by
    ext ψ
    simp only [Set.mem_ofPred_eq, Set.mem_image, s]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨i, rfl⟩ := (hchar ψ).mp h1
      exact ⟨i, h2, rfl⟩
    · rintro ⟨i, h2, rfl⟩
      exact ⟨(hchar _).mpr ⟨i, rfl⟩, h2⟩
  have h1 : eSerC cv.ι cv.gen r f = ∑ᶠ ψ ∈ χ '' s, eOf ψ := by
    rw [← hset]; rfl
  rw [h1, finsum_mem_image (fun i _ j _ h => hinj i j h)]
  rw [finsum_mem_eq_toFinset_sum]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext i; simp [s, hχ]
  · intro i _; exact eOf_eq_zIdem _

end PI.SerBridgeGLW
