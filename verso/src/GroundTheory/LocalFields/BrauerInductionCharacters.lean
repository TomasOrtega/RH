import Mathlib

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section Transport

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def conjRep (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation ℂ G W where
  toFun g := e.conj (ρ g)
  map_one' := by
    ext w
    simp [LinearEquiv.conj_apply]
  map_mul' g h := by
    ext w
    simp [LinearEquiv.conj_apply]

/- English proof (translation)
Simplify using `[conjRep, LinearEquiv.conj_apply]`.
-/
theorem conjRep_apply (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (g : G) (w : W) :
    conjRep ρ e g w = e (ρ g (e.symm w)) := by
  simp [conjRep, LinearEquiv.conj_apply]

def conjRepEquiv (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation.Equiv ρ (conjRep ρ e) :=
  Representation.Equiv.mk e fun g ↦ by
    ext v
    simp [conjRep_apply]

def subrepOrderIso {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : Representation.Equiv ρ σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U := ⟨U.toSubmodule.map (φ.toLinearEquiv : V →ₗ[ℂ] W), by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨ρ g v, U.apply_mem_toSubmodule g hv, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v⟩
  invFun U := ⟨U.toSubmodule.map (φ.toLinearEquiv.symm : W →ₗ[ℂ] V), by
    rintro g _ ⟨w, hw, rfl⟩
    refine ⟨σ g w, U.apply_mem_toSubmodule g hw, ?_⟩
    apply φ.toLinearEquiv.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    have := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g
      (φ.toLinearEquiv.symm w)
    rw [show φ.toIntertwiningMap (φ.toLinearEquiv.symm w) = w from
      φ.toLinearEquiv.apply_symm_apply w] at this
    exact this.symm⟩
  left_inv U := by
    apply Subrepresentation.ext
    change (U.toSubmodule.map (φ.toLinearEquiv : V →ₗ[ℂ] W)).map
      (φ.toLinearEquiv.symm : W →ₗ[ℂ] V) = U.toSubmodule
    rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id]
  right_inv U := by
    apply Subrepresentation.ext
    change (U.toSubmodule.map (φ.toLinearEquiv.symm : W →ₗ[ℂ] V)).map
      (φ.toLinearEquiv : V →ₗ[ℂ] W) = U.toSubmodule
    rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]
  map_rel_iff' {U U'} := by
    change U.toSubmodule.map _ ≤ U'.toSubmodule.map _ ↔ U.toSubmodule ≤ U'.toSubmodule
    exact Submodule.map_le_map_iff_of_injective φ.toLinearEquiv.injective _ _

/- English proof (translation)
The claim follows from `(subrepOrderIso φ).isSimpleOrder_iff.mp inferInstance`.
-/
theorem isIrreducible_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : Representation.Equiv ρ σ) [ρ.IsIrreducible] : σ.IsIrreducible :=
  (subrepOrderIso φ).isSimpleOrder_iff.mp inferInstance

end Transport

section Inner

variable {G : Type*} [Group G] [Fintype G]

variable (G) in

def charInner : (G → ℂ) →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun χ ψ ↦ (Nat.card G : ℂ)⁻¹ * ∑ g, χ g * ψ g⁻¹)
    (fun χ χ' ψ ↦ by simp [add_mul, Finset.sum_add_distrib, mul_add])
    (fun c χ ψ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ ↦ by ring)
    (fun χ ψ ψ' ↦ by simp [mul_add, Finset.sum_add_distrib])
    (fun c χ ψ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ ↦ by ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem charInner_apply (χ ψ : G → ℂ) :
    charInner G χ ψ = (Nat.card G : ℂ)⁻¹ * ∑ g, χ g * ψ g⁻¹ := rfl

/- English proof (translation)
Rewrite using `[charInner_apply, charInner_apply]`. Use `congr 1`. Conclude with `Fintype.sum_equiv (Equiv.inv G) _ _ fun g ↦ by simp [mul_comm]`.
-/
theorem charInner_comm (χ ψ : G → ℂ) : charInner G χ ψ = charInner G ψ χ := by
  rw [charInner_apply, charInner_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g ↦ by simp [mul_comm]

def IsClassFun (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g

end Inner

section Characters

universe u

variable {G : Type*} [Group G] [Fintype G]

def IsCharacter (χ : G → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.character = χ

def IsIrrCharacter (χ : G → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧ ρ.character = χ

section Rep

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in

/- English proof (translation)
Set `e` to `(Module.finBasis ℂ V).equivFun`. Conclude with `⟨Fin (finrank ℂ V) → ℂ, inferInstance, inferInstance, inferInstance, conjRep ρ e, (char_iso (conjRepEquiv ρ e)).symm⟩`.
-/
theorem isCharacter_character (ρ : Representation ℂ G V) : IsCharacter ρ.character := by
  let e := (Module.finBasis ℂ V).equivFun
  exact ⟨Fin (finrank ℂ V) → ℂ, inferInstance, inferInstance, inferInstance, conjRep ρ e,
    (char_iso (conjRepEquiv ρ e)).symm⟩

omit [Fintype G] in

/- English proof (translation)
Set `e` to `(Module.finBasis ℂ V).equivFun`. Conclude with `⟨Fin (finrank ℂ V) → ℂ, inferInstance, inferInstance, inferInstance, conjRep ρ e, isIrreducible_of_equiv (conjRepEquiv ρ e), (char_iso (conjRepEquiv ρ e)).symm⟩`.
-/
theorem isIrrCharacter_character (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    IsIrrCharacter ρ.character := by
  let e := (Module.finBasis ℂ V).equivFun
  exact ⟨Fin (finrank ℂ V) → ℂ, inferInstance, inferInstance, inferInstance, conjRep ρ e,
    isIrreducible_of_equiv (conjRepEquiv ρ e), (char_iso (conjRepEquiv ρ e)).symm⟩

/- English proof (translation)
Establish `: Invertible (Nat.card G : ℂ)` using `invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')`. Rewrite using `[charInner_apply]`. Conclude with `card_inv_mul_sum_char_mul_char_eq_finrank ρ σ`.
-/
theorem charInner_character_character {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    charInner G σ.character ρ.character = finrank ℂ (IntertwiningMap ρ σ) := by
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [charInner_apply]
  exact card_inv_mul_sum_char_mul_char_eq_finrank ρ σ

end Rep

omit [Fintype G] in
/- English proof (translation)
Take `⟨V, _, _, _, ρ, _, rfl⟩` from `h`. Conclude with `⟨V, inferInstance, inferInstance, inferInstance, ρ, rfl⟩`.
-/
theorem IsIrrCharacter.isCharacter {χ : G → ℂ} (h : IsIrrCharacter χ) : IsCharacter χ := by
  obtain ⟨V, _, _, _, ρ, _, rfl⟩ := h
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, rfl⟩

/- English proof (translation)
Take `⟨V, _, _, _, ρ, hρ, rfl⟩` from `hχ`. Take `⟨W, _, _, _, σ, hσ, rfl⟩` from `hψ`. Establish `: Invertible (Nat.card G : ℂ)` using `invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')`. Establish `h1` using `char_orthonormal ρ σ`. Establish `h2` using `char_orthonormal ρ ρ`.

Rewrite `h1`, `h2` using `[← charInner_apply]`. Rewrite `h2` using `[if_pos ⟨Representation.Equiv.refl ρ⟩]`. Rewrite using `[h1]`. Distinguish the cases in `he : Nonempty (Representation.Equiv σ ρ)`. Rewrite using `[if_pos he, if_pos (char_iso he.some).symm]`.

Establish `hne : ρ.character ≠ σ.character`. Introduce `heq`. Rewrite `h1` using `[if_neg he, ← heq, h2]`. Simplify using `at h1`. Rewrite using `[if_neg he, if_neg hne]`.
-/
theorem charInner_of_isIrrCharacter {χ ψ : G → ℂ} (hχ : IsIrrCharacter χ) (hψ : IsIrrCharacter ψ) :
    charInner G χ ψ = if χ = ψ then 1 else 0 := by
  classical
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hχ
  obtain ⟨W, _, _, _, σ, hσ, rfl⟩ := hψ
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h1 := char_orthonormal ρ σ
  have h2 := char_orthonormal ρ ρ
  rw [← charInner_apply] at h1 h2
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at h2
  rw [h1]
  by_cases he : Nonempty (Representation.Equiv σ ρ)
  · rw [if_pos he, if_pos (char_iso he.some).symm]
  · have hne : ρ.character ≠ σ.character := by
      intro heq
      rw [if_neg he, ← heq, h2] at h1
      simp at h1
    rw [if_neg he, if_neg hne]

omit [Fintype G] in

/- English proof (translation)
Take `⟨V, _, _, _, ρ, hρ, rfl⟩` from `h`. Establish `: Nontrivial V`. Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Apply `(bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)` to reduce the goal to its premises.

Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Conclude with `Subsingleton.elim _ _`. Conclude with `⟨finrank ℂ V, finrank_pos, char_one ρ⟩`.
-/
theorem IsIrrCharacter.exists_one {χ : G → ℂ} (h : IsIrrCharacter χ) : ∃ n : ℕ, 0 < n ∧ χ 1 = n := by
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := h
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  exact ⟨finrank ℂ V, finrank_pos, char_one ρ⟩

omit [Fintype G] in
/- English proof (translation)
Take `⟨n, hn, h1⟩` from `h.exists_one`. Rewrite using `[h1]`. Conclude with `Nat.cast_ne_zero.mpr hn.ne'`.
-/
theorem IsIrrCharacter.one_ne_zero {χ : G → ℂ} (h : IsIrrCharacter χ) : χ 1 ≠ 0 := by
  obtain ⟨n, hn, h1⟩ := h.exists_one
  rw [h1]
  exact Nat.cast_ne_zero.mpr hn.ne'

/- English proof (translation)
Apply `LinearIndependent.setFinite (R := ℂ)` to reduce the goal to its premises. Rewrite using `[linearIndependent_iff']`. Introduce `s c hs i hi`. Establish `h` using `congrArg (fun f ↦ charInner G f i.1) hs`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_zero, LinearMap.zero_apply] at h`.

Rewrite `h` using `[Finset.sum_eq_single i]`. Rewrite `h` using `[charInner_of_isIrrCharacter i.2 i.2, if_pos rfl, smul_eq_mul, mul_one]`. Conclude with `h`. Introduce `j _ hj`. Rewrite using `[charInner_of_isIrrCharacter j.2 i.2, if_neg fun h ↦ hj (Subtype.ext h), smul_zero]`.

Introduce `hi'`. Conclude with `absurd hi hi'`.
-/
theorem finite_setOf_isIrrCharacter : {χ : G → ℂ | IsIrrCharacter χ}.Finite := by
  classical
  apply LinearIndependent.setFinite (R := ℂ)
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h := congrArg (fun f ↦ charInner G f i.1) hs
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_zero,
    LinearMap.zero_apply] at h
  rw [Finset.sum_eq_single i] at h
  · rw [charInner_of_isIrrCharacter i.2 i.2, if_pos rfl, smul_eq_mul, mul_one] at h
    exact h
  · intro j _ hj
    rw [charInner_of_isIrrCharacter j.2 i.2, if_neg fun h ↦ hj (Subtype.ext h), smul_zero]
  · intro hi'
    exact absurd hi hi'

variable (G) in

def irrChars : Finset (G → ℂ) := finite_setOf_isIrrCharacter.toFinset

/- English proof (translation)
Simplify using `[irrChars]`.
-/
theorem mem_irrChars {χ : G → ℂ} : χ ∈ irrChars G ↔ IsIrrCharacter χ := by
  simp [irrChars]

/- English proof (translation)
Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]`. Rewrite using `[Finset.sum_eq_single ψ]`. Rewrite using `[charInner_of_isIrrCharacter (mem_irrChars.mp hψ) (mem_irrChars.mp hψ), if_pos rfl, smul_eq_mul, mul_one]`. Introduce `χ hχ hne`. Rewrite using `[charInner_of_isIrrCharacter (mem_irrChars.mp hχ) (mem_irrChars.mp hψ), if_neg hne, smul_zero]`.

Introduce `h`. Conclude with `absurd hψ h`.
-/
theorem charInner_sum_irrChars (c : (G → ℂ) → ℂ) {ψ : G → ℂ} (hψ : ψ ∈ irrChars G) :
    charInner G (∑ χ ∈ irrChars G, c χ • χ) ψ = c ψ := by
  classical
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_eq_single ψ]
  · rw [charInner_of_isIrrCharacter (mem_irrChars.mp hψ) (mem_irrChars.mp hψ), if_pos rfl, smul_eq_mul,
      mul_one]
  · intro χ hχ hne
    rw [charInner_of_isIrrCharacter (mem_irrChars.mp hχ) (mem_irrChars.mp hψ), if_neg hne, smul_zero]
  · intro h
    exact absurd hψ h

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `V _ _ _ ρ hn`. Distinguish the cases in `hirr : ρ.IsIrreducible`. Rewrite using `[Finset.sum_eq_single ρ.character]`.

Rewrite using `[charInner_of_isIrrCharacter (isIrrCharacter_character ρ) (isIrrCharacter_character ρ), if_pos rfl, one_smul]`. Introduce `ψ hψ hne`. Rewrite using `[charInner_of_isIrrCharacter (isIrrCharacter_character ρ) (mem_irrChars.mp hψ), if_neg (Ne.symm hne), zero_smul]`. Introduce `h`. Conclude with `absurd (mem_irrChars.mpr (isIrrCharacter_character ρ)) h`.

Break down `subsingleton_or_nontrivial V with hV | hV` into its components or cases. Establish `h0 : ρ.character = 0` using `funext fun g ↦ by`. Establish `: ρ g = 0` using `LinearMap.ext fun v ↦ Subsingleton.elim _ _`. Simplify using `[Representation.character, this]`. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Establish `hnt : Nontrivial (Subrepresentation ρ)` using `⟨⊥, ⊤, fun h ↦ (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) (congrArg Subrepresentation.toSubmodule h)⟩`. Choose the witnesses or unpack the hypotheses as in `⟨U, hU⟩ : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hirr { toNontrivial := hnt, eq_bot_or_eq_top := fun U ↦ or_iff_not_imp_left.mpr (h U) }`. Establish `: NeZero (Nat.card G : ℂ)` using `⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩`. Take `⟨U', hUU'⟩` from `exists_isCompl U`. Establish `hc : IsCompl U.toSubmodule U'.toSubmodule` using `⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hUU'.inf_eq_bot), codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hUU'.sup_eq_top)⟩`. Establish `hsplit : ρ.character = U.toRepresentation.character + U'.toRepresentation.character`.

Use function extensionality and compare the values at `g`. Set `e` to `Submodule.prodEquivOfIsCompl _ _ hc`. Establish `: ρ g = e.conj ((U.toRepresentation g).prodMap (U'.toRepresentation g))`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Take `⟨⟨x, y⟩, rfl⟩` from `e.surjective v`. Simplify using `[LinearEquiv.conj_apply, e, Subrepresentation.toRepresentation, Submodule.coe_prodEquivOfIsCompl']`. Simplify using `only [Representation.character, Pi.add_apply, this, LinearMap.trace_conj', LinearMap.trace_prodMap']`. Establish `hlt : ∀ U'' : Subrepresentation ρ, U'' ≠ ⊤ → finrank ℂ U''.toSubmodule < n` using `fun U'' h ↦ hn ▸ Submodule.finrank_lt fun h' ↦ h (Subrepresentation.toSubmodule_injective h')`. Establish `hU'top : U' ≠ ⊤`.

Introduce `h`. Apply `hU.1` to reduce the goal to its premises. Rewrite `hUU'` using `[h]`. Simplify using `using hUU'.inf_eq_bot`. Establish `h1` using `ih _ (hlt U hU.2) _ U.toRepresentation rfl`.

Establish `h2` using `ih _ (hlt U' hU'top) _ U'.toRepresentation rfl`. Rewrite using `[hsplit]`. Use `conv_lhs => rw [h1, h2]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun ψ _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[map_add, LinearMap.add_apply, add_smul]`.
-/
theorem character_eq_sum_irrChars_of_finrank (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V),
      finrank ℂ V = n → ρ.character = ∑ ψ ∈ irrChars G, charInner G ρ.character ψ • ψ := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ ρ hn
  by_cases hirr : ρ.IsIrreducible
  · rw [Finset.sum_eq_single ρ.character]
    · rw [charInner_of_isIrrCharacter (isIrrCharacter_character ρ) (isIrrCharacter_character ρ),
        if_pos rfl, one_smul]
    · intro ψ hψ hne
      rw [charInner_of_isIrrCharacter (isIrrCharacter_character ρ) (mem_irrChars.mp hψ),
        if_neg (Ne.symm hne), zero_smul]
    · intro h
      exact absurd (mem_irrChars.mpr (isIrrCharacter_character ρ)) h
  rcases subsingleton_or_nontrivial V with hV | hV
  · have h0 : ρ.character = 0 := funext fun g ↦ by
      have : ρ g = 0 := LinearMap.ext fun v ↦ Subsingleton.elim _ _
      simp [Representation.character, this]
    rw [h0]
    simp
  have hnt : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, fun h ↦
    (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) (congrArg Subrepresentation.toSubmodule h)⟩
  obtain ⟨U, hU⟩ : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
    by_contra h
    push Not at h
    exact hirr { toNontrivial := hnt, eq_bot_or_eq_top := fun U ↦ or_iff_not_imp_left.mpr (h U) }
  have : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨U', hUU'⟩ := exists_isCompl U
  have hc : IsCompl U.toSubmodule U'.toSubmodule :=
    ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hUU'.inf_eq_bot),
      codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hUU'.sup_eq_top)⟩
  have hsplit : ρ.character = U.toRepresentation.character + U'.toRepresentation.character := by
    funext g
    let e := Submodule.prodEquivOfIsCompl _ _ hc
    have : ρ g = e.conj ((U.toRepresentation g).prodMap (U'.toRepresentation g)) := by
      apply LinearMap.ext
      intro v
      obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
      simp [LinearEquiv.conj_apply, e, Subrepresentation.toRepresentation,
        Submodule.coe_prodEquivOfIsCompl']
    simp only [Representation.character, Pi.add_apply, this, LinearMap.trace_conj',
      LinearMap.trace_prodMap']
  have hlt : ∀ U'' : Subrepresentation ρ, U'' ≠ ⊤ → finrank ℂ U''.toSubmodule < n := fun U'' h ↦
    hn ▸ Submodule.finrank_lt fun h' ↦ h (Subrepresentation.toSubmodule_injective h')
  have hU'top : U' ≠ ⊤ := by
    intro h
    apply hU.1
    rw [h] at hUU'
    simpa using hUU'.inf_eq_bot
  have h1 := ih _ (hlt U hU.2) _ U.toRepresentation rfl
  have h2 := ih _ (hlt U' hU'top) _ U'.toRepresentation rfl
  rw [hsplit]
  conv_lhs => rw [h1, h2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ψ _ ↦ ?_
  rw [map_add, LinearMap.add_apply, add_smul]

/- English proof (translation)
The claim follows from `character_eq_sum_irrChars_of_finrank _ V ρ rfl`.
-/
theorem character_eq_sum_irrChars {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.character = ∑ ψ ∈ irrChars G, charInner G ρ.character ψ • ψ :=
  character_eq_sum_irrChars_of_finrank _ V ρ rfl

/- English proof (translation)
Take `⟨W, _, _, _, σ, _, rfl⟩` from `hψ`. Conclude with `⟨_, charInner_character_character σ ρ⟩`.
-/
theorem exists_nat_charInner_character {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {ψ : G → ℂ} (hψ : IsIrrCharacter ψ) :
    ∃ m : ℕ, charInner G ρ.character ψ = m := by
  obtain ⟨W, _, _, _, σ, _, rfl⟩ := hψ
  exact ⟨_, charInner_character_character σ ρ⟩

/- English proof (translation)
Take `⟨V, _, _, _, ρ, rfl⟩` from `hχ`. Establish `h : ∀ ψ ∈ irrChars G, ∃ m : ℕ, charInner G ρ.character ψ = m` using `fun ψ hψ ↦ exists_nat_charInner_character ρ (mem_irrChars.mp hψ)`. Use `choose! m hm using h`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [character_eq_sum_irrChars ρ]`.

Conclude with `Finset.sum_congr rfl fun ψ hψ ↦ by rw [hm ψ hψ]`.
-/
theorem IsCharacter.exists_nat {χ : G → ℂ} (hχ : IsCharacter χ) :
    ∃ m : (G → ℂ) → ℕ, χ = ∑ ψ ∈ irrChars G, (m ψ : ℂ) • ψ := by
  classical
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  have h : ∀ ψ ∈ irrChars G, ∃ m : ℕ, charInner G ρ.character ψ = m := fun ψ hψ ↦
    exists_nat_charInner_character ρ (mem_irrChars.mp hψ)
  choose! m hm using h
  refine ⟨m, ?_⟩
  conv_lhs => rw [character_eq_sum_irrChars ρ]
  exact Finset.sum_congr rfl fun ψ hψ ↦ by rw [hm ψ hψ]

end Characters

section Regular

variable {G : Type*} [Group G] [Fintype G]

/- English proof (translation)
Rewrite using `[Representation.character, Representation.ofMulAction_def]`. Establish `: ((MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ Finsupp.lmapDomain ℂ ℂ (g • · : G → G) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap) = (MonoidAlgebra.coeffLinearEquiv (R` using `ℂ) (S := ℂ) (M := G)).symm.conj (Finsupp.lmapDomain ℂ ℂ (g • · : G → G)) := by`. Use extensionality with `x`. Simplify using `[LinearEquiv.conj_apply]`. Rewrite using `[this, LinearMap.trace_conj', LinearMap.trace_eq_matrix_trace ℂ (Finsupp.basisSingleOne), Matrix.trace]`.

Simplify using `only [Matrix.diag, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply, smul_eq_mul, mul_eq_right]`. Use `split_ifs with hg`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem character_leftRegular_apply [DecidableEq G] (g : G) :
    (Representation.leftRegular ℂ G).character g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  rw [Representation.character, Representation.ofMulAction_def]
  have : ((MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
      Finsupp.lmapDomain ℂ ℂ (g • · : G → G) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap) =
      (MonoidAlgebra.coeffLinearEquiv (R := ℂ) (S := ℂ) (M := G)).symm.conj
        (Finsupp.lmapDomain ℂ ℂ (g • · : G → G)) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [this, LinearMap.trace_conj', LinearMap.trace_eq_matrix_trace ℂ (Finsupp.basisSingleOne),
    Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
    Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Finsupp.single_apply, smul_eq_mul, mul_eq_right]
  split_ifs with hg
  · simp
  · simp

/- English proof (translation)
Establish `hG : (Fintype.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_pos.ne'`. Rewrite using `[charInner_apply]`. Repeatedly rewrite using `[character_leftRegular_apply, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq', if_pos (Finset.mem_univ _), inv_one, Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hG, one_mul]`.
-/
theorem charInner_leftRegular (ψ : G → ℂ) :
    charInner G (Representation.leftRegular ℂ G).character ψ = ψ 1 := by
  classical
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [charInner_apply]
  simp_rw [character_leftRegular_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), inv_one, Nat.card_eq_fintype_card, ← mul_assoc,
    inv_mul_cancel₀ hG, one_mul]

/- English proof (translation)
Use `conv_lhs => rw [character_eq_sum_irrChars (Representation.leftRegular ℂ G)]`. Repeatedly rewrite using `[charInner_leftRegular]`.
-/
theorem character_leftRegular_eq_sum :
    (Representation.leftRegular ℂ G).character = ∑ ψ ∈ irrChars G, ψ 1 • ψ := by
  conv_lhs => rw [character_eq_sum_irrChars (Representation.leftRegular ℂ G)]
  simp_rw [charInner_leftRegular]

/- English proof (translation)
Establish `h` using `congrFun (character_leftRegular_eq_sum (G := G)) g`. Rewrite `h` using `[character_leftRegular_apply, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h`. Rewrite using `[← h, Nat.card_eq_fintype_card]`.
-/
theorem sum_irrChars_mul_apply [DecidableEq G] (g : G) :
    ∑ ψ ∈ irrChars G, ψ 1 * ψ g = if g = 1 then (Nat.card G : ℂ) else 0 := by
  have h := congrFun (character_leftRegular_eq_sum (G := G)) g
  rw [character_leftRegular_apply, Finset.sum_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [← h, Nat.card_eq_fintype_card]

/- English proof (translation)
Establish `h` using `sum_irrChars_mul_apply (G := G) 1`. Rewrite `h` using `[if_pos rfl]`. Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl fun ψ _ ↦ sq _`.
-/
theorem sum_irrChars_sq : ∑ ψ ∈ irrChars G, ψ 1 ^ 2 = (Nat.card G : ℂ) := by
  classical
  have h := sum_irrChars_mul_apply (G := G) 1
  rw [if_pos rfl] at h
  rw [← h]
  exact Finset.sum_congr rfl fun ψ _ ↦ sq _

end Regular

section Completeness

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in

/- English proof (translation)
Take `⟨V, _, _, _, ρ, rfl⟩` from `h`. Introduce `g k`. Conclude with `char_conj ρ g k`.
-/
theorem IsCharacter.isClassFun {χ : G → ℂ} (h : IsCharacter χ) : IsClassFun χ := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := h
  intro g k
  exact char_conj ρ g k

/- English proof (translation)
Establish `h1` using `hψ.one_ne_zero`. Take `⟨V, _, _, _, ρ, hρ, rfl⟩` from `hψ`. Set `T : V →ₗ[ℂ] V` to `∑ g, f g • ρ g⁻¹`. Establish `hT : ∀ k, T ∘ₗ ρ k = ρ k ∘ₗ T`. Introduce `k`.

Use extensionality with `v`. Simplify using `only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]`. Use `Fintype.sum_equiv (MulAut.conj k⁻¹).toEquiv _ _ fun g ↦ ?_` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]`. Rewrite using `[show f (k⁻¹ * g * k) = f g by simpa using hf g k⁻¹, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, show k * (k⁻¹ * g * k)⁻¹ = g⁻¹ * k by group]`.

Take `⟨c, hc⟩` from `(IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2 ⟨T, hT⟩`. Establish `hTc : T = c • LinearMap.id`. Use `congrArg IntertwiningMap.toLinearMap hc` as an intermediate fact. Rewrite `this` using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `this.symm`.

Establish `htr : ∀ h' : G, LinearMap.trace ℂ V (T ∘ₗ ρ h') = ∑ g, f g * ρ.character (g⁻¹ * h')`. Introduce `h'`. Establish `hcomp : T ∘ₗ ρ h' = ∑ g, f g • ρ (g⁻¹ * h')`. Use extensionality with `v`. Simplify using `[T, LinearMap.sum_apply, map_mul]`.

Rewrite using `[hcomp, map_sum]`. Simplify using `only [map_smul, smul_eq_mul, Representation.character]`. Establish `hval : ∀ h' : G, ∑ g, f g * ρ.character (g⁻¹ * h') = c * ρ.character h'`. Introduce `h'`. Rewrite using `[← htr, hTc, LinearMap.smul_comp, LinearMap.id_comp, map_smul, smul_eq_mul]`.

Both sides reduce to the same expression. Establish `hc' : c = (Nat.card G : ℂ) * charInner G f ρ.character / ρ.character 1`. Establish `h0` using `hval 1`. Simplify using `only [mul_one] at h0`. Establish `hG : (Nat.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`.

Rewrite using `[charInner_apply, ← mul_assoc, mul_inv_cancel₀ hG, one_mul, h0]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hval, hc']`.
-/
theorem sum_mul_irr_apply {f : G → ℂ} (hf : IsClassFun f) {ψ : G → ℂ} (hψ : IsIrrCharacter ψ)
    (h : G) :
    ∑ g, f g * ψ (g⁻¹ * h) = (Nat.card G : ℂ) * charInner G f ψ / ψ 1 * ψ h := by
  have h1 := hψ.one_ne_zero
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hψ
  let T : V →ₗ[ℂ] V := ∑ g, f g • ρ g⁻¹
  have hT : ∀ k, T ∘ₗ ρ k = ρ k ∘ₗ T := by
    intro k
    ext v
    simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul]
    refine Fintype.sum_equiv (MulAut.conj k⁻¹).toEquiv _ _ fun g ↦ ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
    rw [show f (k⁻¹ * g * k) = f g by simpa using hf g k⁻¹, ← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul, show k * (k⁻¹ * g * k)⁻¹ = g⁻¹ * k by group]
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).2 ⟨T, hT⟩
  have hTc : T = c • LinearMap.id := by
    have := congrArg IntertwiningMap.toLinearMap hc
    rw [Algebra.algebraMap_eq_smul_one] at this
    exact this.symm
  have htr : ∀ h' : G, LinearMap.trace ℂ V (T ∘ₗ ρ h') = ∑ g, f g * ρ.character (g⁻¹ * h') := by
    intro h'
    have hcomp : T ∘ₗ ρ h' = ∑ g, f g • ρ (g⁻¹ * h') := by
      ext v
      simp [T, LinearMap.sum_apply, map_mul]
    rw [hcomp, map_sum]
    simp only [map_smul, smul_eq_mul, Representation.character]
  have hval : ∀ h' : G, ∑ g, f g * ρ.character (g⁻¹ * h') = c * ρ.character h' := by
    intro h'
    rw [← htr, hTc, LinearMap.smul_comp, LinearMap.id_comp, map_smul, smul_eq_mul]
    rfl
  have hc' : c = (Nat.card G : ℂ) * charInner G f ρ.character / ρ.character 1 := by
    have h0 := hval 1
    simp only [mul_one] at h0
    have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [charInner_apply, ← mul_assoc, mul_inv_cancel₀ hG, one_mul, h0]
    field_simp
  rw [hval, hc']

/- English proof (translation)
Use function extensionality and compare the values at `h`. Establish `hG : (Nat.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `key : f h = (Nat.card G : ℂ)⁻¹ * ∑ g, f g * ∑ ψ ∈ irrChars G, ψ 1 * ψ (g⁻¹ * h)`. Repeatedly rewrite using `[sum_irrChars_mul_apply, inv_mul_eq_one, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq', if_pos (Finset.mem_univ _), mul_comm (f h), ← mul_assoc, inv_mul_cancel₀ hG, one_mul]`.

Establish `hswap : ∑ g, f g * ∑ ψ ∈ irrChars G, ψ 1 * ψ (g⁻¹ * h) = ∑ ψ ∈ irrChars G, ∑ g, f g * (ψ 1 * ψ (g⁻¹ * h))`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[key, Finset.sum_apply, hswap, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ψ hψ ↦ ?_` and prove the remaining obligations.

Establish `h1` using `(mem_irrChars.mp hψ).one_ne_zero`. Use `sum_mul_irr_apply hf (mem_irrChars.mp hψ) h` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun g _ ↦ by ring`.

Use `_ = (charInner G f ψ • ψ) h := by`. Rewrite using `[this, Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem eq_sum_irrChars_of_isClassFun {f : G → ℂ} (hf : IsClassFun f) :
    f = ∑ ψ ∈ irrChars G, charInner G f ψ • ψ := by
  classical
  funext h
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key : f h = (Nat.card G : ℂ)⁻¹ * ∑ g, f g * ∑ ψ ∈ irrChars G, ψ 1 * ψ (g⁻¹ * h) := by
    simp_rw [sum_irrChars_mul_apply, inv_mul_eq_one, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), mul_comm (f h), ← mul_assoc, inv_mul_cancel₀ hG,
      one_mul]
  have hswap : ∑ g, f g * ∑ ψ ∈ irrChars G, ψ 1 * ψ (g⁻¹ * h) =
      ∑ ψ ∈ irrChars G, ∑ g, f g * (ψ 1 * ψ (g⁻¹ * h)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [key, Finset.sum_apply, hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ hψ ↦ ?_
  have h1 := (mem_irrChars.mp hψ).one_ne_zero
  have := sum_mul_irr_apply hf (mem_irrChars.mp hψ) h
  calc (Nat.card G : ℂ)⁻¹ * ∑ g, f g * (ψ 1 * ψ (g⁻¹ * h))
      = (Nat.card G : ℂ)⁻¹ * ψ 1 * ∑ g, f g * ψ (g⁻¹ * h) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ ↦ by ring
    _ = (charInner G f ψ • ψ) h := by
        rw [this, Pi.smul_apply, smul_eq_mul]
        field_simp

/- English proof (translation)
Rewrite using `[eq_sum_irrChars_of_isClassFun hf]`. Conclude with `Finset.sum_eq_zero fun ψ hψ ↦ by rw [h ψ hψ, zero_smul]`.
-/
theorem eq_zero_of_isClassFun_of_charInner {f : G → ℂ} (hf : IsClassFun f)
    (h : ∀ ψ ∈ irrChars G, charInner G f ψ = 0) : f = 0 := by
  rw [eq_sum_irrChars_of_isClassFun hf]
  exact Finset.sum_eq_zero fun ψ hψ ↦ by rw [h ψ hψ, zero_smul]

/- English proof (translation)
Rewrite using `[eq_sum_irrChars_of_isClassFun hf, eq_sum_irrChars_of_isClassFun hf']`. Conclude with `Finset.sum_congr rfl fun ψ hψ ↦ by rw [h ψ hψ]`.
-/
theorem eq_of_isClassFun_of_charInner {f f' : G → ℂ} (hf : IsClassFun f) (hf' : IsClassFun f')
    (h : ∀ ψ ∈ irrChars G, charInner G f ψ = charInner G f' ψ) : f = f' := by
  rw [eq_sum_irrChars_of_isClassFun hf, eq_sum_irrChars_of_isClassFun hf']
  exact Finset.sum_congr rfl fun ψ hψ ↦ by rw [h ψ hψ]

end Completeness

section Closure

variable {G : Type*} [Group G]

/- English proof (translation)
Use `⟨PUnit, inferInstance, inferInstance, inferInstance, Representation.trivial ℂ G PUnit, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Establish `: (Representation.trivial ℂ G PUnit) g = 0` using `LinearMap.ext fun v ↦ Subsingleton.elim _ _`. Simplify using `[Representation.character, this]`.
-/
theorem isCharacter_zero : IsCharacter (0 : G → ℂ) := by
  refine ⟨PUnit, inferInstance, inferInstance, inferInstance, Representation.trivial ℂ G PUnit, ?_⟩
  funext g
  have : (Representation.trivial ℂ G PUnit) g = 0 := LinearMap.ext fun v ↦ Subsingleton.elim _ _
  simp [Representation.character, this]

/- English proof (translation)
Use `⟨ℂ, inferInstance, inferInstance, inferInstance, Representation.trivial ℂ G ℂ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Simplify using `[Representation.character, Representation.trivial]`.
-/
theorem isCharacter_one : IsCharacter (1 : G → ℂ) := by
  refine ⟨ℂ, inferInstance, inferInstance, inferInstance, Representation.trivial ℂ G ℂ, ?_⟩
  funext g
  simp [Representation.character, Representation.trivial]

/- English proof (translation)
Take `⟨V, _, _, _, ρ, rfl⟩` from `hχ`. Take `⟨W, _, _, _, σ, rfl⟩` from `hψ`. Use `⟨V × W, inferInstance, inferInstance, inferInstance, ρ.prod σ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `LinearMap.trace ℂ (V × W) ((ρ g).prodMap (σ g)) = _`.

Conclude with `LinearMap.trace_prodMap' _ _`.
-/
theorem IsCharacter.add {χ ψ : G → ℂ} (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    IsCharacter (χ + ψ) := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  obtain ⟨W, _, _, _, σ, rfl⟩ := hψ
  refine ⟨V × W, inferInstance, inferInstance, inferInstance, ρ.prod σ, ?_⟩
  funext g
  change LinearMap.trace ℂ (V × W) ((ρ g).prodMap (σ g)) = _
  exact LinearMap.trace_prodMap' _ _

/- English proof (translation)
Take `⟨V, _, _, _, ρ, rfl⟩` from `hχ`. Take `⟨W, _, _, _, σ, rfl⟩` from `hψ`. Conclude with `⟨TensorProduct ℂ V W, inferInstance, inferInstance, inferInstance, ρ.tprod σ, char_tensor ρ σ⟩`.
-/
theorem IsCharacter.mul {χ ψ : G → ℂ} (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    IsCharacter (χ * ψ) := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  obtain ⟨W, _, _, _, σ, rfl⟩ := hψ
  exact ⟨TensorProduct ℂ V W, inferInstance, inferInstance, inferInstance, ρ.tprod σ, char_tensor ρ σ⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using isCharacter_zero`. Consider the case `succ n ih => rw [succ_nsmul]`. Conclude with `ih.add hχ`.
-/
theorem IsCharacter.nsmul {χ : G → ℂ} (hχ : IsCharacter χ) (n : ℕ) : IsCharacter (n • χ) := by
  induction n with
  | zero => simpa using isCharacter_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add hχ

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isCharacter_zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))`.
-/
theorem isCharacter_sum {ι : Type*} (s : Finset ι) {χ : ι → G → ℂ} (h : ∀ i ∈ s, IsCharacter (χ i)) :
    IsCharacter (∑ i ∈ s, χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCharacter_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

variable [Fintype G]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf`. Use `⟨hf.isClassFun, fun ψ hψ ↦ ?_⟩` and prove the remaining obligations. Take `⟨V, _, _, _, ρ, rfl⟩` from `hf`. Conclude with `exists_nat_charInner_character ρ (mem_irrChars.mp hψ)`.

Introduce and unpack `⟨hf, h⟩ choose! n hn using h`. Rewrite using `[eq_sum_irrChars_of_isClassFun hf]`. Use `isCharacter_sum _ fun ψ hψ ↦ ?_` and prove the remaining obligations. Rewrite using `[hn ψ hψ, Nat.cast_smul_eq_nsmul ℂ]`. Conclude with `(mem_irrChars.mp hψ).isCharacter.nsmul _`.
-/
theorem isCharacter_iff {f : G → ℂ} :
    IsCharacter f ↔ IsClassFun f ∧ ∀ ψ ∈ irrChars G, ∃ n : ℕ, charInner G f ψ = n := by
  classical
  constructor
  · intro hf
    refine ⟨hf.isClassFun, fun ψ hψ ↦ ?_⟩
    obtain ⟨V, _, _, _, ρ, rfl⟩ := hf
    exact exists_nat_charInner_character ρ (mem_irrChars.mp hψ)
  · rintro ⟨hf, h⟩
    choose! n hn using h
    rw [eq_sum_irrChars_of_isClassFun hf]
    refine isCharacter_sum _ fun ψ hψ ↦ ?_
    rw [hn ψ hψ, Nat.cast_smul_eq_nsmul ℂ]
    exact (mem_irrChars.mp hψ).isCharacter.nsmul _

end Closure

end GroundTheory.LocalField
