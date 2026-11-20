import Mathlib
import GroundTheory.LocalFields.BrauerInductionCharacters
import GroundTheory.LocalFields.BrauerInductionInduced

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section Basics

variable {G : Type*} [Group G]

/- English proof (translation)
Take `⟨V, _, _, _, ρ, rfl⟩` from `h`. Conclude with `⟨finrank ℂ V, char_one ρ⟩`.
-/
theorem IsCharacter.exists_nat_one {χ : G → ℂ} (h : IsCharacter χ) : ∃ n : ℕ, χ 1 = n := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := h
  exact ⟨finrank ℂ V, char_one ρ⟩

/- English proof (translation)
Take `⟨V, _, _, _, ρ, rfl⟩` from `h`. Rewrite `h1` using `[char_one, Nat.cast_eq_zero, Module.finrank_zero_iff]`. Use function extensionality and compare the values at `g`. Establish `: ρ g = 0` using `LinearMap.ext fun v ↦ Subsingleton.elim _ _`. Simplify using `[Representation.character, this]`.
-/
theorem IsCharacter.eq_zero_of_apply_one {χ : G → ℂ} (h : IsCharacter χ) (h1 : χ 1 = 0) : χ = 0 := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := h
  rw [char_one, Nat.cast_eq_zero, Module.finrank_zero_iff] at h1
  funext g
  have : ρ g = 0 := LinearMap.ext fun v ↦ Subsingleton.elim _ _
  simp [Representation.character, this]

def linRep (l : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := (l g : ℂ) • LinearMap.id
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp [mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem linRep_apply (l : G →* ℂˣ) (g : G) (z : ℂ) : linRep l g z = (l g : ℂ) * z := rfl

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[Representation.character, linRep]`.
-/
theorem character_linRep (l : G →* ℂˣ) : (linRep l).character = fun g ↦ (l g : ℂ) := by
  funext g
  simp [Representation.character, linRep]

instance linRep_isIrreducible (l : G →* ℂˣ) : (linRep l).IsIrreducible where
  exists_pair_ne := ⟨⊥, ⊤, fun h ↦
    (bot_ne_top : (⊥ : Submodule ℂ ℂ) ≠ ⊤) (congrArg Subrepresentation.toSubmodule h)⟩
  eq_bot_or_eq_top U := by
    rcases Ideal.eq_bot_or_top U.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/- English proof (translation)
Rewrite using `[← character_linRep]`. Conclude with `isIrrCharacter_character _`.
-/
theorem isIrrCharacter_hom (l : G →* ℂˣ) : IsIrrCharacter (fun g ↦ (l g : ℂ)) := by
  rw [← character_linRep]
  exact isIrrCharacter_character _

/- English proof (translation)
Establish `hs : ∀ a, ∃ c : ℂ, σ a = c • (1 : Module.End ℂ V)`. Introduce `a`. Take `⟨c, hc'⟩` from `(IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := σ)).2 ⟨σ a, fun b ↦ hc a b⟩`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use `congrArg IntertwiningMap.toLinearMap hc'` as an intermediate fact.

Rewrite `this` using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `this.symm`. Use `choose c hc' using hs`. Establish `hV : Nontrivial V`. Assume the negation of the conclusion as `hV`.

Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Apply `(bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Conclude with `Subsingleton.elim _ _`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`.

Set `U : Subrepresentation σ` to `⟨ℂ ∙ v, fun a w hw ↦ by`. Rewrite using `[hc' a]`. Conclude with `Submodule.smul_mem _ _ hw⟩`. Establish `hU : U = ⊤`. Use `(hσ.eq_bot_or_eq_top U).resolve_left fun h ↦ hv ?_` and prove the remaining obligations.

Establish `: v ∈ U.toSubmodule` using `Submodule.mem_span_singleton_self v`. Rewrite `this` using `[h]`. Conclude with `this`. Establish `hrank : finrank ℂ V = 1`. Establish `h1` using `finrank_span_singleton (K := ℂ) hv`.

Establish `h2 : (ℂ ∙ v) = ⊤` using `congrArg Subrepresentation.toSubmodule hU`. Rewrite `h1` using `[h2, finrank_top]`. Conclude with `h1`. Establish `hchar : ∀ a, σ.character a = c a`. Introduce `a`.

Simplify using `[Representation.character, hc' a, LinearMap.trace_one, hrank]`. Establish `hmul : ∀ a b, c (a * b) = c a * c b`. Introduce `a b`. Establish `h` using `map_mul σ a b`. Rewrite `h` using `[hc', hc', hc', smul_mul_smul, one_mul]`.

Establish `h'` using `congrArg (fun T : Module.End ℂ V ↦ T v) h`. Simplify using `only [LinearMap.smul_apply, Module.End.one_apply] at h'`. Conclude with `smul_left_injective ℂ hv h'`. Establish `hone : c 1 = 1`. Rewrite using `[← hchar, char_one, hrank, Nat.cast_one]`.

Set `f : G →* ℂ` to `{ toFun := c, map_one' := hone, map_mul' := hmul }`. Use `⟨f.toHomUnits, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Simplify using `[f, hchar]`.
-/
theorem exists_hom_of_isIrreducible_of_commute {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (σ : Representation ℂ G V) [hσ : σ.IsIrreducible]
    (hc : ∀ a b, σ a * σ b = σ b * σ a) :
    ∃ l : G →* ℂˣ, σ.character = fun g ↦ (l g : ℂ) := by
  have hs : ∀ a, ∃ c : ℂ, σ a = c • (1 : Module.End ℂ V) := by
    intro a
    obtain ⟨c, hc'⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := σ)).2 ⟨σ a, fun b ↦ hc a b⟩
    refine ⟨c, ?_⟩
    have := congrArg IntertwiningMap.toLinearMap hc'
    rw [Algebra.algebraMap_eq_smul_one] at this
    exact this.symm
  choose c hc' using hs
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let U : Subrepresentation σ := ⟨ℂ ∙ v, fun a w hw ↦ by
    rw [hc' a]
    exact Submodule.smul_mem _ _ hw⟩
  have hU : U = ⊤ := by
    refine (hσ.eq_bot_or_eq_top U).resolve_left fun h ↦ hv ?_
    have : v ∈ U.toSubmodule := Submodule.mem_span_singleton_self v
    rw [h] at this
    exact this
  have hrank : finrank ℂ V = 1 := by
    have h1 := finrank_span_singleton (K := ℂ) hv
    have h2 : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hU
    rw [h2, finrank_top] at h1
    exact h1
  have hchar : ∀ a, σ.character a = c a := by
    intro a
    simp [Representation.character, hc' a, LinearMap.trace_one, hrank]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    have h := map_mul σ a b
    rw [hc', hc', hc', smul_mul_smul, one_mul] at h
    have h' := congrArg (fun T : Module.End ℂ V ↦ T v) h
    simp only [LinearMap.smul_apply, Module.End.one_apply] at h'
    exact smul_left_injective ℂ hv h'
  have hone : c 1 = 1 := by
    rw [← hchar, char_one, hrank, Nat.cast_one]
  let f : G →* ℂ := { toFun := c, map_one' := hone, map_mul' := hmul }
  refine ⟨f.toHomUnits, ?_⟩
  funext g
  simp [f, hchar]

variable [Fintype G]

/- English proof (translation)
Rewrite using `[isCharacter_iff]`. Use `⟨fun g k ↦ by simp [hη.isClassFun g k, hχ.isCharacter.isClassFun g k], fun ψ hψ ↦ ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `hη.exists_nat_charInner (mem_irrChars.mp hψ).isCharacter`. Rewrite using `[map_sub, LinearMap.sub_apply, hn, charInner_of_isIrrCharacter hχ (mem_irrChars.mp hψ)]`. Use `split_ifs with he`.

Substitute `he` using the available equality. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `h (by rw [hn, Nat.cast_zero])`. Conclude with `⟨n - 1, by rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0), Nat.cast_one]⟩`.

Conclude with `⟨n, by rw [sub_zero]⟩`.
-/
theorem IsCharacter.sub_of_charInner_ne_zero {η χ : G → ℂ} (hη : IsCharacter η)
    (hχ : IsIrrCharacter χ) (h : charInner G η χ ≠ 0) : IsCharacter (η - χ) := by
  classical
  rw [isCharacter_iff]
  refine ⟨fun g k ↦ by simp [hη.isClassFun g k, hχ.isCharacter.isClassFun g k], fun ψ hψ ↦ ?_⟩
  obtain ⟨n, hn⟩ := hη.exists_nat_charInner (mem_irrChars.mp hψ).isCharacter
  rw [map_sub, LinearMap.sub_apply, hn, charInner_of_isIrrCharacter hχ (mem_irrChars.mp hψ)]
  split_ifs with he
  · subst he
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact h (by rw [hn, Nat.cast_zero])
    exact ⟨n - 1, by rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0), Nat.cast_one]⟩
  · exact ⟨n, by rw [sub_zero]⟩

end Basics

section IndFunMore

variable {G H H' : Type*} [Group G] [Group H] [Group H'] [Fintype G] [Fintype H] [Fintype H']

/- English proof (translation)
Use function extensionality and compare the values at `s`. Rewrite using `[indFun_apply, indFun_apply, Nat.card_congr e.toEquiv]`. Use `congr 1`. Use `Finset.sum_congr rfl fun t _ ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `exact Fintype.sum_equiv e.toEquiv _ _ fun h ↦ by split_ifs <;> simp_all`.
-/
theorem indFun_comp_mulEquiv (φ : H' →* G) (e : H ≃* H') (ψ : H → ℂ) :
    indFun (φ.comp e.toMonoidHom) ψ = indFun φ (ψ ∘ e.symm) := by
  funext s
  rw [indFun_apply, indFun_apply, Nat.card_congr e.toEquiv]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  exact Fintype.sum_equiv e.toEquiv _ _ fun h ↦ by split_ifs <;> simp_all

/- English proof (translation)
Use function extensionality and compare the values at `s`. Rewrite using `[indFun_apply]`. Simplify using `only [MonoidHom.id_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `h : ∀ t : G, ψ (t⁻¹ * s * t) = ψ s` using `fun t ↦ by simpa using hψ s t⁻¹`. Repeatedly rewrite using `[h]`.

Establish `hG : (Nat.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hG, one_mul]`.
-/
theorem indFun_id {ψ : G → ℂ} (hψ : IsClassFun ψ) : indFun (MonoidHom.id G) ψ = ψ := by
  classical
  funext s
  rw [indFun_apply]
  simp only [MonoidHom.id_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h : ∀ t : G, ψ (t⁻¹ * s * t) = ψ s := fun t ↦ by simpa using hψ s t⁻¹
  simp_rw [h]
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, ← mul_assoc,
    inv_mul_cancel₀ hG, one_mul]

/- English proof (translation)
Establish `h : (⊤ : Subgroup G).subtype = (MonoidHom.id G).comp Subgroup.topEquiv.toMonoidHom`. Use `ext`. Both sides reduce to the same expression. Rewrite using `[h, indFun_comp_mulEquiv]`. Use `indFun_id fun g k ↦ ?_` and prove the remaining obligations.

Use `show ((l (k * g * k⁻¹) : ℂˣ) : ℂ) = l g`. Rewrite using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`.
-/
theorem indFun_top_hom [Fintype (⊤ : Subgroup G)] (l : G →* ℂˣ) :
    indFun (⊤ : Subgroup G).subtype (fun k ↦ ((l.comp (⊤ : Subgroup G).subtype) k : ℂ)) =
      fun g ↦ (l g : ℂ) := by
  have h : (⊤ : Subgroup G).subtype = (MonoidHom.id G).comp Subgroup.topEquiv.toMonoidHom := by
    ext
    rfl
  rw [h, indFun_comp_mulEquiv]
  refine indFun_id fun g k ↦ ?_
  show ((l (k * g * k⁻¹) : ℂˣ) : ℂ) = l g
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/- English proof (translation)
Rewrite using `[indFun_indFun, ← indFun_comp_mulEquiv]`. Use `congr 1`.
-/
theorem indFun_subtype_indFun_subtype (T : Subgroup G) [Fintype T] (K : Subgroup T) [Fintype K]
    [Fintype (K.map T.subtype)] (ψ : K → ℂ) :
    indFun T.subtype (indFun K.subtype ψ) = indFun (K.map T.subtype).subtype
      (ψ ∘ (K.equivMapOfInjective T.subtype T.subtype_injective).symm) := by
  rw [indFun_indFun, ← indFun_comp_mulEquiv]
  congr 1

end IndFunMore

section Conj

variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]

def conjNormal (g : G) : A ≃* A where
  toFun a := ⟨g⁻¹ * a * g, by simpa using hA.conj_mem a a.2 g⁻¹⟩
  invFun a := ⟨g * a * g⁻¹, hA.conj_mem a a.2 g⟩
  left_inv a := by
    ext
    simp [mul_assoc]
  right_inv a := by
    ext
    simp [mul_assoc]
  map_mul' a b := by
    ext
    simp [mul_assoc]

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conjNormal (g : G) (a : A) : (conjNormal A g a : G) = g⁻¹ * a * g := rfl

/- English proof (translation)
Use `ext`. Simplify using `[mul_assoc]`.
-/
theorem conjNormal_mul (g h : G) (a : A) :
    conjNormal A (g * h) a = conjNormal A h (conjNormal A g a) := by
  ext
  simp [mul_assoc]

/- English proof (translation)
Use `ext`. Simplify using the standard rewrite rules.
-/
theorem conjNormal_one (a : A) : conjNormal A 1 a = a := by
  ext
  simp

def inertia (θ : A → ℂ) : Subgroup G where
  carrier := {g | ∀ a, θ (conjNormal A g a) = θ a}
  one_mem' := by
    intro a
    rw [conjNormal_one]
  mul_mem' {g h} hg hh := by
    intro a
    rw [conjNormal_mul, hh, hg]
  inv_mem' {g} hg := by
    intro a
    calc θ (conjNormal A g⁻¹ a) = θ (conjNormal A g (conjNormal A g⁻¹ a)) := (hg _).symm
      _ = θ a := by rw [← conjNormal_mul, inv_mul_cancel, conjNormal_one]

/- English proof (translation)
Introduce `x hx a`. Use `hθ a ⟨x, hx⟩⁻¹` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem le_inertia {θ : A → ℂ} (hθ : IsClassFun θ) : A ≤ inertia A θ := by
  intro x hx a
  have := hθ a ⟨x, hx⟩⁻¹
  convert this using 2
  ext
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e b`. Take `⟨a, rfl⟩` from `(conjNormal A g).surjective b`. Rewrite using `[← conjNormal_mul, mul_inv_cancel_left]`. Conclude with `congrFun e a`.

Introduce `hx`. Use function extensionality and compare the values at `a`. Establish `hh : h = g * (g⁻¹ * h)` using `by group`. Simplify using `only [Function.comp_apply]`. Rewrite using `[hh, conjNormal_mul]`.

Conclude with `hx _`.
-/
theorem comp_conjNormal_eq_iff (θ : A → ℂ) (g h : G) :
    θ ∘ conjNormal A h = θ ∘ conjNormal A g ↔ g⁻¹ * h ∈ inertia A θ := by
  constructor
  · intro e b
    obtain ⟨a, rfl⟩ := (conjNormal A g).surjective b
    rw [← conjNormal_mul, mul_inv_cancel_left]
    exact congrFun e a
  · intro hx
    funext a
    have hh : h = g * (g⁻¹ * h) := by group
    simp only [Function.comp_apply]
    rw [hh, conjNormal_mul]
    exact hx _

open Classical in

/- English proof (translation)
Establish `hcard : ∀ g : G, (Finset.univ.filter fun h : G ↦ θ ∘ conjNormal A h = θ ∘ conjNormal A g).card = Nat.card (inertia A θ)`. Introduce `g`. Rewrite using `[← Fintype.card_subtype, ← Nat.card_eq_fintype_card]`. Conclude with `Nat.card_congr ((Equiv.mulLeft g⁻¹).subtypeEquiv fun h ↦ by`. Rewrite using `[comp_conjNormal_eq_iff]`.

Use the proof step `rfl)`. Establish `h` using `Finset.card_eq_sum_card_image (fun g : G ↦ θ ∘ conjNormal A g) Finset.univ`. Establish `h2 : ∑ φ ∈ Finset.univ.image (fun g : G ↦ θ ∘ conjNormal A g), (Finset.univ.filter fun x : G ↦ θ ∘ conjNormal A x = φ).card = ∑ φ ∈ Finset.univ.image (fun g : G ↦ θ ∘ conjNormal A g), Nat.card (inertia A θ)` using `Finset.sum_congr rfl fun φ hφ ↦ by`. Take `⟨g, -, rfl⟩` from `Finset.mem_image.mp hφ`. Conclude with `hcard g`.

Establish `h3` using `h.trans h2`. Rewrite `h3` using `[Finset.sum_const, smul_eq_mul, Finset.card_univ]`. Rewrite using `[← h3, Nat.card_eq_fintype_card]`.
-/
theorem card_conjugates_mul_card_inertia [Fintype G] (θ : A → ℂ) :
    (Finset.univ.image fun g : G ↦ θ ∘ conjNormal A g).card * Nat.card (inertia A θ) = Nat.card G := by
  have hcard : ∀ g : G, (Finset.univ.filter fun h : G ↦ θ ∘ conjNormal A h = θ ∘ conjNormal A g).card =
      Nat.card (inertia A θ) := by
    intro g
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr ((Equiv.mulLeft g⁻¹).subtypeEquiv fun h ↦ by
      rw [comp_conjNormal_eq_iff]
      rfl)
  have h := Finset.card_eq_sum_card_image (fun g : G ↦ θ ∘ conjNormal A g) Finset.univ
  have h2 : ∑ φ ∈ Finset.univ.image (fun g : G ↦ θ ∘ conjNormal A g),
      (Finset.univ.filter fun x : G ↦ θ ∘ conjNormal A x = φ).card =
      ∑ φ ∈ Finset.univ.image (fun g : G ↦ θ ∘ conjNormal A g), Nat.card (inertia A θ) :=
    Finset.sum_congr rfl fun φ hφ ↦ by
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hφ
      exact hcard g
  have h3 := h.trans h2
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ] at h3
  rw [← h3, Nat.card_eq_fintype_card]

/- English proof (translation)
Rewrite using `[charInner_apply, charInner_apply]`. Use `congr 1`. Use `Fintype.sum_equiv (conjNormal A g).toEquiv _ _ fun a ↦ ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Subgroup.coe_subtype, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, map_inv, coe_conjNormal]`. Use `congr 1`.

Simplify using `using (hχ a g⁻¹).symm`.
-/
theorem charInner_comp_conjNormal [Fintype A] {χ : G → ℂ} (hχ : IsClassFun χ) (θ : A → ℂ) (g : G) :
    charInner A (χ ∘ A.subtype) (θ ∘ conjNormal A g) = charInner A (χ ∘ A.subtype) θ := by
  rw [charInner_apply, charInner_apply]
  congr 1
  refine Fintype.sum_equiv (conjNormal A g).toEquiv _ _ fun a ↦ ?_
  simp only [Function.comp_apply, Subgroup.coe_subtype, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv, map_inv, coe_conjNormal]
  congr 1
  simpa using (hχ a g⁻¹).symm

end Conj

/- English proof (translation)
Take `⟨V, _, _, _, σ, hσ, rfl⟩` from `hθ`. Use `⟨V, inferInstance, inferInstance, inferInstance, σ.comp e.toMonoidHom, ?_, rfl⟩` and prove the remaining obligations. Set `iso : Subrepresentation (σ.comp e.toMonoidHom) ≃o Subrepresentation σ` to `{ toFun := fun U ↦ ⟨U.toSubmodule, fun h v hv ↦ by`. Use `U.apply_mem_toSubmodule (e.symm h) hv` as an intermediate fact. Simplify using `using this⟩`.

Use `invFun := fun U ↦ ⟨U.toSubmodule, fun h v hv ↦ U.apply_mem_toSubmodule (e h) hv⟩`. Use `left_inv := fun U ↦ rfl`. Use `right_inv := fun U ↦ rfl`. Use the proof step `map_rel_iff' := Iff.rfl }`. Conclude with `iso.isSimpleOrder_iff.mpr hσ`.
-/
theorem IsIrrCharacter.comp_mulEquiv {H H' : Type*} [Group H] [Group H'] {θ : H → ℂ}
    (hθ : IsIrrCharacter θ) (e : H' ≃* H) : IsIrrCharacter (θ ∘ e) := by
  obtain ⟨V, _, _, _, σ, hσ, rfl⟩ := hθ
  refine ⟨V, inferInstance, inferInstance, inferInstance, σ.comp e.toMonoidHom, ?_, rfl⟩
  let iso : Subrepresentation (σ.comp e.toMonoidHom) ≃o Subrepresentation σ :=
    { toFun := fun U ↦ ⟨U.toSubmodule, fun h v hv ↦ by
        have := U.apply_mem_toSubmodule (e.symm h) hv
        simpa using this⟩
      invFun := fun U ↦ ⟨U.toSubmodule, fun h v hv ↦ U.apply_mem_toSubmodule (e h) hv⟩
      left_inv := fun U ↦ rfl
      right_inv := fun U ↦ rfl
      map_rel_iff' := Iff.rfl }
  exact iso.isSimpleOrder_iff.mpr hσ

section Clifford

variable {G : Type*} [Group G] [Fintype G] {A : Subgroup G} [A.Normal]

open Classical in

/- English proof (translation)
Use `set T := inertia A θ with hT`. Establish `hAT : A ≤ T` using `le_inertia A hθ.isCharacter.isClassFun`. Set `ι : A →* T` to `Subgroup.inclusion hAT`. Set `res : (T → ℂ) →ₗ[ℂ] (A → ℂ)` to `LinearMap.funLeft ℂ ℂ ι`. Establish `hχT : IsCharacter (χ ∘ T.subtype)` using `hχ.isCharacter.comp _`.

Establish `hχA : χ ∘ A.subtype = res (χ ∘ T.subtype)` using `rfl`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψ, hne⟩ : ∃ ψ ∈ irrChars T, charInner T (χ ∘ T.subtype) ψ * charInner A (res ψ) θ ≠ 0 := by`. Apply `Finset.exists_ne_zero_of_sum_ne_zero` to reduce the goal to its premises. Rewrite `h` using `[hχA, eq_sum_irrChars_of_isClassFun hχT.isClassFun]`. Simplify `h` using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`.

Establish `hψirr` using `mem_irrChars.mp hψ`. Establish `ha : charInner T (χ ∘ T.subtype) ψ ≠ 0` using `left_ne_zero_of_mul hne`. Establish `he : charInner A (res ψ) θ ≠ 0` using `right_ne_zero_of_mul hne`. Take `⟨e, he'⟩` from `(hψirr.isCharacter.comp ι).exists_nat_charInner hθ.isCharacter`. Express the relevant statement in the definitionally equal form `charInner A (res ψ) θ = e at he'`.

Establish `hInd : IsCharacter (indFun ι θ)` using `hθ.isCharacter.indFun ι`. Establish `hIndψ : charInner T (indFun ι θ) ψ ≠ 0`. Rewrite using `[charInner_indFun ι θ hψirr.isCharacter.isClassFun, charInner_comm]`. Conclude with `he`. Establish `hη` using `hInd.sub_of_charInner_ne_zero hψirr hIndψ`.

Establish `hIndA : res (indFun ι θ) = ((Nat.card T : ℂ) / Nat.card A) • θ`. Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `indFun ι θ (ι a) = _`. Rewrite using `[indFun_apply, Pi.smul_apply, smul_eq_mul]`. Establish `hiff : ∀ (t : T) (b : A), ι b = t⁻¹ * ι a * t ↔ b = conjNormal A t a`.

Introduce `t b`. Rewrite using `[Subtype.ext_iff, Subtype.ext_iff]`. Simplify using `[ι]`. Repeatedly rewrite using `[hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `ht : ∀ t : T, θ (conjNormal A t a) = θ a` using `fun t ↦ t.2 a`.

Repeatedly rewrite using `[ht]`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]`. Expand and normalize the polynomial expressions, which then agree. Establish `hzero : ∀ φ ∈ irrChars A, φ ≠ θ → charInner A (res ψ) φ = 0`. Introduce `φ hφ hne`.

Establish `h1 : charInner A (res (indFun ι θ)) φ = 0`. Rewrite using `[hIndA, map_smul, LinearMap.smul_apply, charInner_of_isIrrCharacter hθ (mem_irrChars.mp hφ), if_neg (Ne.symm hne), smul_zero]`. Establish `h2 : res (indFun ι θ) = res ψ + res (indFun ι θ - ψ)` using `by simp`. Rewrite `h1` using `[h2, map_add, LinearMap.add_apply]`. Take `⟨m, hm⟩` from `(hψirr.isCharacter.comp ι).exists_nat_charInner (mem_irrChars.mp hφ).isCharacter`.

Take `⟨k, hk⟩` from `(hη.comp ι).exists_nat_charInner (mem_irrChars.mp hφ).isCharacter`. Express the relevant statement in the definitionally equal form `charInner A (res ψ) φ = m at hm`. Express the relevant statement in the definitionally equal form `charInner A (res (indFun ι θ - ψ)) φ = k at hk`. Rewrite `h1` using `[hm, hk, ← Nat.cast_add, Nat.cast_eq_zero, Nat.add_eq_zero_iff]`. Rewrite using `[hm, h1.1, Nat.cast_zero]`.

Establish `hψ1 : ψ 1 = e * θ 1`. Establish `hdec` using `congrFun (eq_sum_irrChars_of_isClassFun (hψirr.isCharacter.comp ι).isClassFun) 1`. Rewrite `hdec` using `[Finset.sum_apply, Finset.sum_eq_single θ]`. Express the relevant statement in the definitionally equal form `ψ (ι 1) = _ at hdec`. Rewrite `hdec` using `[map_one]`.

Rewrite using `[hdec, Pi.smul_apply, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `charInner A (res ψ) θ * θ 1 = _`. Rewrite using `[he']`. Introduce `φ hφ hne`. Express the relevant statement in the definitionally equal form `(charInner A (res ψ) φ • φ) 1 = 0`.

Rewrite using `[hzero φ hφ hne, zero_smul, Pi.zero_apply]`. Introduce `hθ'`. Conclude with `absurd (mem_irrChars.mpr hθ) hθ'`. Take `⟨f, hf⟩` from `(hχ.isCharacter.comp A.subtype).exists_nat_charInner hθ.isCharacter`. Establish `hη2` using `hχT.sub_of_charInner_ne_zero hψirr ha`.

Take `⟨k2, hk2⟩` from `(hη2.comp ι).exists_nat_charInner hθ.isCharacter`. Express the relevant statement in the definitionally equal form `charInner A (res (χ ∘ T.subtype - ψ)) θ = k2 at hk2`. Establish `hef : e ≤ f`. Establish `h3 : charInner A (res (χ ∘ T.subtype)) θ = charInner A (res ψ) θ + charInner A (res (χ ∘ T.subtype - ψ)) θ`. Rewrite using `[← LinearMap.add_apply, ← map_add, ← map_add, add_sub_cancel]`.

Rewrite `h3` using `[← hχA, hf, he', hk2, ← Nat.cast_add]`. Use `Nat.cast_injective h3` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨m, hm⟩` from `(hχ.isCharacter.comp A.subtype).exists_nat`. Establish `hmφ : ∀ φ ∈ irrChars A, charInner A (χ ∘ A.subtype) φ = m φ`.

Introduce `φ hφ`. Rewrite using `[hm, charInner_sum_irrChars _ hφ]`. Establish `hd : ∀ φ ∈ irrChars A, ∃ d : ℕ, φ 1 = d` using `fun φ hφ ↦ (mem_irrChars.mp hφ).isCharacter.exists_nat_one`. Use `choose! d hd using hd`. Establish `hθmem : θ ∈ irrChars A` using `mem_irrChars.mpr hθ`.

Use `set C := Finset.univ.image fun g : G ↦ θ ∘ conjNormal A g with hC`. Establish `hCsub : C ⊆ irrChars A`. Introduce `φ hφ`. Take `⟨g, -, rfl⟩` from `Finset.mem_image.mp hφ`. Conclude with `mem_irrChars.mpr (hθ.comp_mulEquiv _)`.

Establish `hCterm : ∀ φ ∈ C, m φ * d φ = f * d θ`. Introduce `φ hφ`. Take `⟨g, -, rfl⟩` from `Finset.mem_image.mp hφ`. Establish `h1 : (m (θ ∘ conjNormal A g) : ℂ) = f`. Rewrite using `[← hmφ _ (hCsub hφ), charInner_comp_conjNormal A hχ.isCharacter.isClassFun, hf]`.

Establish `h2 : (d (θ ∘ conjNormal A g) : ℂ) = d θ`. Rewrite using `[← hd _ (hCsub hφ), ← hd _ hθmem, Function.comp_apply, map_one]`. Rewrite using `[Nat.cast_injective h1, Nat.cast_injective h2]`. Establish `hχ1 : χ 1 = ((∑ φ ∈ irrChars A, m φ * d φ : ℕ) : ℂ)`. Use `congrFun hm 1` as an intermediate fact.

Rewrite `this` using `[Finset.sum_apply]`. Express the relevant statement in the definitionally equal form `χ 1 = _ at this`. Rewrite using `[this]`. Use `push_cast`. Use `Finset.sum_congr rfl fun φ hφ ↦ ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, smul_eq_mul, hd φ hφ]`. Establish `hbound : C.card * f * d θ ≤ ∑ φ ∈ irrChars A, m φ * d φ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_congr rfl hCterm, Finset.sum_const, smul_eq_mul, mul_assoc]`. Use `_ ≤ ∑ φ ∈ irrChars A, m φ * d φ := Finset.sum_le_sum_of_subset hCsub`.

Establish `hcard` using `card_conjugates_mul_card_inertia A θ`. Establish `hψG : IsCharacter (indFun T.subtype ψ)` using `hψirr.isCharacter.indFun _`. Establish `hne3 : charInner G (indFun T.subtype ψ) χ ≠ 0`. Rewrite using `[charInner_indFun _ _ hχ.isCharacter.isClassFun, charInner_comm]`. Conclude with `ha`.

Establish `hη3` using `hψG.sub_of_charInner_ne_zero hχ hne3`. Take `⟨k3, hk3⟩` from `hη3.exists_nat_one`. Establish `hT0 : (Nat.card T : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `hdeg : indFun T.subtype ψ 1 = ((C.card * e * d θ : ℕ) : ℂ)`. Rewrite using `[indFun_apply_one _ T.subtype_injective, hψ1, hd θ hθmem, ← hcard, ← hC, ← hT]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hk0 : k3 = 0`. Rewrite `hk3` using `[Pi.sub_apply, hdeg, hχ1, sub_eq_iff_eq_add, ← Nat.cast_add]`. Establish `h4` using `Nat.cast_injective hk3`.

Establish `h5 : C.card * e * d θ ≤ C.card * f * d θ` using `by gcongr`. Use linear arithmetic over natural numbers and integers. Use `⟨ψ, hψirr, ?_⟩` and prove the remaining obligations. Establish `h6` using `hη3.eq_zero_of_apply_one (by rw [hk3, hk0, Nat.cast_zero])`. Conclude with `(sub_eq_zero.mp h6).symm`.
-/
theorem IsIrrCharacter.exists_eq_indFun_inertia {χ : G → ℂ} (hχ : IsIrrCharacter χ) {θ : A → ℂ}
    (hθ : IsIrrCharacter θ) (h : charInner A (χ ∘ A.subtype) θ ≠ 0) :
    ∃ ψ : inertia A θ → ℂ, IsIrrCharacter ψ ∧ χ = indFun (inertia A θ).subtype ψ := by
  classical
  set T := inertia A θ with hT
  have hAT : A ≤ T := le_inertia A hθ.isCharacter.isClassFun
  let ι : A →* T := Subgroup.inclusion hAT
  let res : (T → ℂ) →ₗ[ℂ] (A → ℂ) := LinearMap.funLeft ℂ ℂ ι
  have hχT : IsCharacter (χ ∘ T.subtype) := hχ.isCharacter.comp _
  have hχA : χ ∘ A.subtype = res (χ ∘ T.subtype) := rfl

  obtain ⟨ψ, hψ, hne⟩ : ∃ ψ ∈ irrChars T,
      charInner T (χ ∘ T.subtype) ψ * charInner A (res ψ) θ ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    rw [hχA, eq_sum_irrChars_of_isClassFun hχT.isClassFun] at h
    simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h
  have hψirr := mem_irrChars.mp hψ
  have ha : charInner T (χ ∘ T.subtype) ψ ≠ 0 := left_ne_zero_of_mul hne
  have he : charInner A (res ψ) θ ≠ 0 := right_ne_zero_of_mul hne
  obtain ⟨e, he'⟩ := (hψirr.isCharacter.comp ι).exists_nat_charInner hθ.isCharacter
  change charInner A (res ψ) θ = e at he'

  have hInd : IsCharacter (indFun ι θ) := hθ.isCharacter.indFun ι
  have hIndψ : charInner T (indFun ι θ) ψ ≠ 0 := by
    rw [charInner_indFun ι θ hψirr.isCharacter.isClassFun, charInner_comm]
    exact he
  have hη := hInd.sub_of_charInner_ne_zero hψirr hIndψ
  have hIndA : res (indFun ι θ) = ((Nat.card T : ℂ) / Nat.card A) • θ := by
    funext a
    change indFun ι θ (ι a) = _
    rw [indFun_apply, Pi.smul_apply, smul_eq_mul]
    have hiff : ∀ (t : T) (b : A), ι b = t⁻¹ * ι a * t ↔ b = conjNormal A t a := by
      intro t b
      rw [Subtype.ext_iff, Subtype.ext_iff]
      simp [ι]
    simp_rw [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have ht : ∀ t : T, θ (conjNormal A t a) = θ a := fun t ↦ t.2 a
    simp_rw [ht]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    ring

  have hzero : ∀ φ ∈ irrChars A, φ ≠ θ → charInner A (res ψ) φ = 0 := by
    intro φ hφ hne
    have h1 : charInner A (res (indFun ι θ)) φ = 0 := by
      rw [hIndA, map_smul, LinearMap.smul_apply, charInner_of_isIrrCharacter hθ (mem_irrChars.mp hφ),
        if_neg (Ne.symm hne), smul_zero]
    have h2 : res (indFun ι θ) = res ψ + res (indFun ι θ - ψ) := by simp
    rw [h2, map_add, LinearMap.add_apply] at h1
    obtain ⟨m, hm⟩ := (hψirr.isCharacter.comp ι).exists_nat_charInner (mem_irrChars.mp hφ).isCharacter
    obtain ⟨k, hk⟩ := (hη.comp ι).exists_nat_charInner (mem_irrChars.mp hφ).isCharacter
    change charInner A (res ψ) φ = m at hm
    change charInner A (res (indFun ι θ - ψ)) φ = k at hk
    rw [hm, hk, ← Nat.cast_add, Nat.cast_eq_zero, Nat.add_eq_zero_iff] at h1
    rw [hm, h1.1, Nat.cast_zero]
  have hψ1 : ψ 1 = e * θ 1 := by
    have hdec := congrFun (eq_sum_irrChars_of_isClassFun (hψirr.isCharacter.comp ι).isClassFun) 1
    rw [Finset.sum_apply, Finset.sum_eq_single θ] at hdec
    · change ψ (ι 1) = _ at hdec
      rw [map_one] at hdec
      rw [hdec, Pi.smul_apply, smul_eq_mul]
      change charInner A (res ψ) θ * θ 1 = _
      rw [he']
    · intro φ hφ hne
      change (charInner A (res ψ) φ • φ) 1 = 0
      rw [hzero φ hφ hne, zero_smul, Pi.zero_apply]
    · intro hθ'
      exact absurd (mem_irrChars.mpr hθ) hθ'

  obtain ⟨f, hf⟩ := (hχ.isCharacter.comp A.subtype).exists_nat_charInner hθ.isCharacter
  have hη2 := hχT.sub_of_charInner_ne_zero hψirr ha
  obtain ⟨k2, hk2⟩ := (hη2.comp ι).exists_nat_charInner hθ.isCharacter
  change charInner A (res (χ ∘ T.subtype - ψ)) θ = k2 at hk2
  have hef : e ≤ f := by
    have h3 : charInner A (res (χ ∘ T.subtype)) θ =
        charInner A (res ψ) θ + charInner A (res (χ ∘ T.subtype - ψ)) θ := by
      rw [← LinearMap.add_apply, ← map_add, ← map_add, add_sub_cancel]
    rw [← hχA, hf, he', hk2, ← Nat.cast_add] at h3
    have := Nat.cast_injective h3
    omega

  obtain ⟨m, hm⟩ := (hχ.isCharacter.comp A.subtype).exists_nat
  have hmφ : ∀ φ ∈ irrChars A, charInner A (χ ∘ A.subtype) φ = m φ := by
    intro φ hφ
    rw [hm, charInner_sum_irrChars _ hφ]
  have hd : ∀ φ ∈ irrChars A, ∃ d : ℕ, φ 1 = d := fun φ hφ ↦
    (mem_irrChars.mp hφ).isCharacter.exists_nat_one
  choose! d hd using hd
  have hθmem : θ ∈ irrChars A := mem_irrChars.mpr hθ
  set C := Finset.univ.image fun g : G ↦ θ ∘ conjNormal A g with hC
  have hCsub : C ⊆ irrChars A := by
    intro φ hφ
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hφ
    exact mem_irrChars.mpr (hθ.comp_mulEquiv _)
  have hCterm : ∀ φ ∈ C, m φ * d φ = f * d θ := by
    intro φ hφ
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hφ
    have h1 : (m (θ ∘ conjNormal A g) : ℂ) = f := by
      rw [← hmφ _ (hCsub hφ), charInner_comp_conjNormal A hχ.isCharacter.isClassFun, hf]
    have h2 : (d (θ ∘ conjNormal A g) : ℂ) = d θ := by
      rw [← hd _ (hCsub hφ), ← hd _ hθmem, Function.comp_apply, map_one]
    rw [Nat.cast_injective h1, Nat.cast_injective h2]
  have hχ1 : χ 1 = ((∑ φ ∈ irrChars A, m φ * d φ : ℕ) : ℂ) := by
    have := congrFun hm 1
    rw [Finset.sum_apply] at this
    change χ 1 = _ at this
    rw [this]
    push_cast
    refine Finset.sum_congr rfl fun φ hφ ↦ ?_
    rw [Pi.smul_apply, smul_eq_mul, hd φ hφ]
  have hbound : C.card * f * d θ ≤ ∑ φ ∈ irrChars A, m φ * d φ := by
    calc C.card * f * d θ = ∑ φ ∈ C, m φ * d φ := by
          rw [Finset.sum_congr rfl hCterm, Finset.sum_const, smul_eq_mul, mul_assoc]
      _ ≤ ∑ φ ∈ irrChars A, m φ * d φ := Finset.sum_le_sum_of_subset hCsub

  have hcard := card_conjugates_mul_card_inertia A θ
  have hψG : IsCharacter (indFun T.subtype ψ) := hψirr.isCharacter.indFun _
  have hne3 : charInner G (indFun T.subtype ψ) χ ≠ 0 := by
    rw [charInner_indFun _ _ hχ.isCharacter.isClassFun, charInner_comm]
    exact ha
  have hη3 := hψG.sub_of_charInner_ne_zero hχ hne3
  obtain ⟨k3, hk3⟩ := hη3.exists_nat_one
  have hT0 : (Nat.card T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hdeg : indFun T.subtype ψ 1 = ((C.card * e * d θ : ℕ) : ℂ) := by
    rw [indFun_apply_one _ T.subtype_injective, hψ1, hd θ hθmem, ← hcard, ← hC, ← hT]
    push_cast
    field_simp
  have hk0 : k3 = 0 := by
    rw [Pi.sub_apply, hdeg, hχ1, sub_eq_iff_eq_add, ← Nat.cast_add] at hk3
    have h4 := Nat.cast_injective hk3
    have h5 : C.card * e * d θ ≤ C.card * f * d θ := by gcongr
    omega
  refine ⟨ψ, hψirr, ?_⟩
  have h6 := hη3.eq_zero_of_apply_one (by rw [hk3, hk0, Nat.cast_zero])
  exact (sub_eq_zero.mp h6).symm

end Clifford

end GroundTheory.LocalField
