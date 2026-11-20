import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.IrrCharIff

noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT

namespace PI.SerBridgeGLW

section
variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`.
-/
theorem card_ne_zero' : (Nat.card G : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/- English proof (translation)
Set `b` to `Module.finBasis ℂ V`. Use `⟨Module.finrank ℂ V, MonoidHom.toHomUnits ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp V.ρ), fun x => ?_⟩` and prove the remaining obligations. Simplify using `[FDRep.character, LinearMap.trace_eq_matrix_trace ℂ b]`. Both sides reduce to the same expression.
-/
theorem isChar_of_fdrep (V : FDRep ℂ G) : IsChar V.character := by
  classical
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V,
    MonoidHom.toHomUnits ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp V.ρ), fun x => ?_⟩
  simp [FDRep.character, LinearMap.trace_eq_matrix_trace ℂ b]
  rfl

/- English proof (translation)
Unfold `ipG`. Conclude with `Finset.sum_congr rfl fun x _ => by rw [hC G V x]`.
-/
theorem ipG_eq (hC : ConjChar) (V : FDRep ℂ G) :
    ipG V.character V.character = ∑ x, V.character x * V.character x⁻¹ := by
  unfold ipG
  exact Finset.sum_congr rfl fun x _ => by rw [hC G V x]

/- English proof (translation)
Use `⟨isChar_of_fdrep V, ?_⟩` and prove the remaining obligations. Rewrite using `[ipG_eq hC, (FDRep.simple_iff_char_is_norm_one V).mp inferInstance, Nat.card_eq_fintype_card]`.
-/
theorem isIrrChar_of_simple (hC : ConjChar) (V : FDRep ℂ G) [Simple V] : IsIrrChar V.character := by
  refine ⟨isChar_of_fdrep V, ?_⟩
  rw [ipG_eq hC, (FDRep.simple_iff_char_is_norm_one V).mp inferInstance, Nat.card_eq_fintype_card]

def repOfGL {n : ℕ} (ρ : G →* GL (Fin n) ℂ) : FDRep ℂ G :=
  FDRep.of (((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ)).toRingEquiv.toMonoidHom).comp
    ((Units.coeHom _).comp ρ))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLinAlgEquiv' (ρ x : Matrix (Fin n) (Fin n) ℂ)) = _`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']`. Use `congr 1`. Conclude with `LinearMap.toMatrix'_toLin' _`.
-/
theorem repOfGL_character {n : ℕ} (ρ : G →* GL (Fin n) ℂ) (x : G) :
    (repOfGL ρ).character x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ) := by
  change LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLinAlgEquiv' (ρ x : Matrix (Fin n) (Fin n) ℂ)) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix']
  congr 1
  exact LinearMap.toMatrix'_toLin' _

/- English proof (translation)
Introduce `G _ _ χ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨n, ρ, hρ⟩, hip⟩`. Establish `hχ : χ = (repOfGL ρ).character` using `funext fun x => by rw [hρ, repOfGL_character]`. Substitute `hχ` using the available equality.

Use `⟨repOfGL ρ, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[FDRep.simple_iff_char_is_norm_one, ← ipG_eq hC, hip, Nat.card_eq_fintype_card]`. Introduce and unpack `⟨V, hV, rfl⟩`. Conclude with `isIrrChar_of_simple hC V`.
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
Use `haveI : Invertible ((Nat.card G : ℕ) : ℂ) := invertibleOfNonzero card_ne_zero'`. Establish `h1` using `FDRep.char_orthonormal V W`. Establish `h2` using `FDRep.char_orthonormal V V`. Rewrite `h2` using `[if_pos ⟨Iso.refl V⟩]`. Rewrite `h1` using `[← h, h2]`.

Assume the negation of the conclusion as `hn`. Rewrite `h1` using `[if_neg hn]`. Conclude with `one_ne_zero h1`.
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
Assemble the required witnesses or components as `⟨FDRep.isoToLinearEquiv i, fun γ v => by rw [FDRep.Iso.conj_ρ i γ] simp [LinearEquiv.conj_apply]⟩`.
-/
theorem repIso_of_iso {V W : FDRep ℂ G} (i : V ≅ W) : RepIso V.ρ W.ρ := ⟨FDRep.isoToLinearEquiv i, fun γ v => by
    rw [FDRep.Iso.conj_ρ i γ]
    simp [LinearEquiv.conj_apply]⟩

/- English proof (translation)
Take `⟨e, he⟩` from `h`. Use function extensionality and compare the values at `γ`. Use `show LinearMap.trace ℂ V (V.ρ γ) = LinearMap.trace ℂ W (W.ρ γ)`. Establish `hc : W.ρ γ = e.conj (V.ρ γ)`. Use extensionality with `w`.

Establish `h1` using `he γ (e.symm w)`. Rewrite `h1` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]`. Conclude with `h1.symm`. Rewrite using `[hc, LinearMap.trace_conj']`.
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
Introduce `G _ _ I _ ρ hs hi he`. Establish `hI` using `irrCharIff_of hC`. Use `⟨fun χ => ⟨fun hχ => ?_, ?_⟩, fun i j hij => ?_⟩` and prove the remaining obligations. Take `⟨V, hV, rfl⟩` from `(hI G χ).mp hχ`. Take `⟨i, hi'⟩` from `he V hV`.

Conclude with `⟨i, character_eq_of_repIso hi'⟩`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(hI G _).mpr ⟨ρ i, hs i, rfl⟩`. Use `haveI := hs i`. Use `haveI := hs j`.

Take `⟨e⟩` from `iso_of_character_eq (ρ i) (ρ j) hij`. Conclude with `hi i j (repIso_of_iso e)`.
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
Apply `MonoidAlgebra.coeff_injective` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[zIdem_coeff, eOf, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm, FDRep.char_one]`. Both sides reduce to the same expression.
-/
theorem eOf_eq_zIdem (V : FDRep ℂ G) : eOf V.character = zIdem V := by
  apply MonoidAlgebra.coeff_injective
  ext x
  rw [zIdem_coeff, eOf, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm, FDRep.char_one]
  rfl

end

/- English proof (translation)
Introduce `g _ cv r I _ ρ hs hi he f`. Take `⟨hchar, hinj⟩` from `irrSys_of hC _ I ρ hs hi he`. Use `set χ : I → (GL (Fin r) (ZMod g) → ℂ) := fun i => (ρ i).character with hχ`. Use `set s : Set I := {i | InSeries cv.ι cv.gen (χ i) f}`. Establish `hset : {ψ : GL (Fin r) (ZMod g) → ℂ | IsIrrChar ψ ∧ InSeries cv.ι cv.gen ψ f} = χ '' s`.

Use extensionality with `ψ`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_image, s]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Take `⟨i, rfl⟩` from `(hchar ψ).mp h1`.

Conclude with `⟨i, h2, rfl⟩`. Introduce and unpack `⟨i, h2, rfl⟩`. Conclude with `⟨(hchar _).mpr ⟨i, rfl⟩, h2⟩`. Establish `h1 : eSerC cv.ι cv.gen r f = ∑ᶠ ψ ∈ χ '' s, eOf ψ`. Rewrite using `[← hset]`.

Both sides reduce to the same expression. Rewrite using `[h1, finsum_mem_image (fun i _ j _ h => hinj i j h)]`. Rewrite using `[finsum_mem_eq_toFinset_sum]`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero]`. Apply `Finset.sum_congr` to reduce the goal to its premises.

Use extensionality with `i`. Simplify using `[s, hχ]`. Introduce `i _`. Conclude with `eOf_eq_zIdem _`.
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
