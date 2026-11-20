import Mathlib
import GroundTheory.LocalFields.BrauerInductionCharacters
import GroundTheory.LocalFields.BrauerInductionInduced
import GroundTheory.LocalFields.BrauerInductionClifford

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section Nilpotent

open scoped commutatorElement

variable {G : Type*} [Group G]

/- English proof (translation)
Set `ρ'` to `ρ.toHomUnits`. Set `cent : Set G → Subgroup G` to `fun s ↦ (Subgroup.centralizer (ρ' '' s)).comap ρ'`. Establish `hcent : ∀ (s : Set G) (x : G), x ∈ cent s ↔ ∀ y ∈ s, ρ y * ρ x = ρ x * ρ y`. Introduce `s x`. Simplify using `only [cent, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.forall_mem_image, Units.ext_iff, Units.val_mul, ρ', MonoidHom.coe_toHomUnits]`.

Set `S` to `cent Set.univ`. Establish `hS : ∀ x, x ∈ S ↔ ∀ y, ρ y * ρ x = ρ x * ρ y` using `fun x ↦ by`. Simplify using `[S, hcent]`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz2, hz1⟩ : ∃ z, (∀ y, ⁅z, y⁆ ∈ S) ∧ z ∉ S := by`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `hle : ∀ n, Subgroup.upperCentralSeries G n ≤ S`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `x hx`. Rewrite `hx` using `[Subgroup.upperCentralSeries_zero, Subgroup.mem_bot]`. Rewrite using `[hx]`. Conclude with `S.one_mem`. Consider the case `succ n ih`.

Introduce `x hx`. Conclude with `hcon x fun y ↦ ih (Subgroup.mem_upperCentralSeries_succ_iff.mp hx y)`. Take `⟨n, hn⟩` from `Group.IsNilpotent.nilpotent G`. Take `⟨a, b, hab⟩` from `h`. Conclude with `hab ((hS b).mp (hle n (hn ▸ Subgroup.mem_top b)) a)`.

Establish `hzmem : z ∈ insert z (S : Set G)` using `Set.mem_insert z _`. Establish `hSmem : ∀ x ∈ S, x ∈ insert z (S : Set G)` using `fun x hx ↦ Set.mem_insert_of_mem z hx`. Use `⟨Subgroup.closure (insert z (S : Set G)), ⟨fun n hn g ↦ ?_⟩, fun a ha b hb ↦ ?_, ?_⟩` and prove the remaining obligations. Establish `hle : Subgroup.closure (insert z (S : Set G)) ≤ (Subgroup.closure (insert z (S : Set G))).comap (MulAut.conj g).toMonoidHom`. Rewrite using `[Subgroup.closure_le]`.

Introduce `x hx`. Simplify using `only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Break down `hx with rfl | hx` into its components or cases. Rewrite using `[show g * x * g⁻¹ = ⁅x, g⁆⁻¹ * x by rw [commutatorElement_inv, commutatorElement_def]; group]`. Conclude with `Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (hSmem _ (hz2 g)))) (Subgroup.subset_closure hzmem)`.

Apply `Subgroup.subset_closure` to reduce the goal to its premises. Apply `hSmem` to reduce the goal to its premises. Rewrite using `[hS]`. Introduce `y`. Establish `hx' : ρ (g * x * g⁻¹) = ρ x`.

Rewrite using `[map_mul, map_mul, (hS x).mp hx g, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]`. Rewrite using `[hx']`. Conclude with `(hS x).mp hx y`. Conclude with `hle hn`. Establish `h1 : ∀ y ∈ insert z (S : Set G), Subgroup.closure (insert z (S : Set G)) ≤ cent {y}`.

Introduce `y hy`. Rewrite using `[Subgroup.closure_le]`. Introduce `x hx`. Rewrite using `[SetLike.mem_coe, hcent]`. Introduce `y' hy'`.

Rewrite using `[Set.mem_singleton_iff.mp hy']`. Break down `hx with rfl | hx` into its components or cases. Break down `hy with rfl | hy` into its components or cases. Both sides reduce to the same expression. Conclude with `((hS y).mp hy x).symm`.

Conclude with `(hS x).mp hx y`. Establish `h2 : Subgroup.closure (insert z (S : Set G)) ≤ cent {a}`. Rewrite using `[Subgroup.closure_le]`. Introduce `y hy`. Rewrite using `[SetLike.mem_coe, hcent]`.

Introduce `a' ha'`. Rewrite using `[Set.mem_singleton_iff.mp ha']`. Conclude with `((hcent {y} a).mp (h1 y hy ha) y rfl).symm`. Conclude with `((hcent {a} b).mp (h2 hb) a rfl)`. Use `⟨z, Subgroup.subset_closure hzmem, ?_⟩` and prove the remaining obligations.

Rewrite `hz1` using `[hS]`. Use `push Not at hz1`. Conclude with `hz1`.
-/
theorem exists_normal_commute_of_not_commute {M : Type*} [Monoid M] [Group.IsNilpotent G] (ρ : G →* M)
    (h : ∃ a b, ρ a * ρ b ≠ ρ b * ρ a) :
    ∃ A : Subgroup G, A.Normal ∧ (∀ a ∈ A, ∀ b ∈ A, ρ a * ρ b = ρ b * ρ a) ∧
      ∃ a ∈ A, ∃ g, ρ g * ρ a ≠ ρ a * ρ g := by
  let ρ' := ρ.toHomUnits
  let cent : Set G → Subgroup G := fun s ↦ (Subgroup.centralizer (ρ' '' s)).comap ρ'
  have hcent : ∀ (s : Set G) (x : G), x ∈ cent s ↔ ∀ y ∈ s, ρ y * ρ x = ρ x * ρ y := by
    intro s x
    simp only [cent, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.forall_mem_image,
      Units.ext_iff, Units.val_mul, ρ', MonoidHom.coe_toHomUnits]

  let S := cent Set.univ
  have hS : ∀ x, x ∈ S ↔ ∀ y, ρ y * ρ x = ρ x * ρ y := fun x ↦ by
    simp [S, hcent]
  obtain ⟨z, hz2, hz1⟩ : ∃ z, (∀ y, ⁅z, y⁆ ∈ S) ∧ z ∉ S := by
    by_contra hcon
    push Not at hcon
    have hle : ∀ n, Subgroup.upperCentralSeries G n ≤ S := by
      intro n
      induction n with
      | zero =>
        intro x hx
        rw [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] at hx
        rw [hx]
        exact S.one_mem
      | succ n ih =>
        intro x hx
        exact hcon x fun y ↦ ih (Subgroup.mem_upperCentralSeries_succ_iff.mp hx y)
    obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent G
    obtain ⟨a, b, hab⟩ := h
    exact hab ((hS b).mp (hle n (hn ▸ Subgroup.mem_top b)) a)
  have hzmem : z ∈ insert z (S : Set G) := Set.mem_insert z _
  have hSmem : ∀ x ∈ S, x ∈ insert z (S : Set G) := fun x hx ↦ Set.mem_insert_of_mem z hx
  refine ⟨Subgroup.closure (insert z (S : Set G)), ⟨fun n hn g ↦ ?_⟩, fun a ha b hb ↦ ?_, ?_⟩
  ·
    have hle : Subgroup.closure (insert z (S : Set G)) ≤
        (Subgroup.closure (insert z (S : Set G))).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases hx with rfl | hx
      · rw [show g * x * g⁻¹ = ⁅x, g⁆⁻¹ * x by rw [commutatorElement_inv, commutatorElement_def]; group]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (hSmem _ (hz2 g))))
          (Subgroup.subset_closure hzmem)
      · apply Subgroup.subset_closure
        apply hSmem
        rw [hS]
        intro y
        have hx' : ρ (g * x * g⁻¹) = ρ x := by
          rw [map_mul, map_mul, (hS x).mp hx g, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
        rw [hx']
        exact (hS x).mp hx y
    exact hle hn
  ·
    have h1 : ∀ y ∈ insert z (S : Set G), Subgroup.closure (insert z (S : Set G)) ≤ cent {y} := by
      intro y hy
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, hcent]
      intro y' hy'
      rw [Set.mem_singleton_iff.mp hy']
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · rfl
        · exact ((hS y).mp hy x).symm
      · exact (hS x).mp hx y
    have h2 : Subgroup.closure (insert z (S : Set G)) ≤ cent {a} := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, hcent]
      intro a' ha'
      rw [Set.mem_singleton_iff.mp ha']
      exact ((hcent {y} a).mp (h1 y hy ha) y rfl).symm
    exact ((hcent {a} b).mp (h2 hb) a rfl)
  · refine ⟨z, Subgroup.subset_closure hzmem, ?_⟩
    rw [hS] at hz1
    push Not at hz1
    exact hz1

end Nilpotent

section Scalar

variable {G : Type*} [Group G] {A : Subgroup G} [A.Normal] [Fintype A]

/- English proof (translation)
Establish `hrank : finrank ℂ (IntertwiningMap (linRep l) (ρ.comp A.subtype)) ≠ 0`. Rewrite using `[← Nat.cast_ne_zero (R := ℂ), ← charInner_character_character, character_linRep]`. Conclude with `h`. Establish `: Nontrivial (IntertwiningMap (linRep l) (ρ.comp A.subtype))` using `Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hrank)`. Take `⟨F, hF⟩` from `exists_ne (0 : IntertwiningMap (linRep l) (ρ.comp A.subtype))`.

Set `W : Subrepresentation ρ` to `{ toSubmodule := { carrier := {w | ∀ a : A, ρ a w = (l a : ℂ) • w} add_mem' := fun {w w'} hw hw' a ↦ by rw [map_add, hw a, hw' a, smul_add] zero_mem' := fun a ↦ by rw [map_zero, smul_zero] smul_mem' := fun c w hw a ↦ by rw [map_smul, hw a, smul_comm] } apply_mem_toSubmodule := fu …`. Establish `hag : (a : G) * g = g * (conjNormal A g a : G)` using `by simp [mul_assoc]`. Express the relevant statement in the definitionally equal form `ρ a (ρ g w) = (l a : ℂ) • ρ g w`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hag, map_mul, Module.End.mul_apply]`. Rewrite using `[show ρ (conjNormal A g a : G) w = (l (conjNormal A g a) : ℂ) • w from hw _, hl, map_smul] }`.

Establish `hF1 : F 1 ∈ W.toSubmodule` using `fun a ↦ by`. Use `IntertwiningMap.isIntertwining _ _ F a 1` as an intermediate fact. Rewrite `this` using `[linRep_apply, mul_one, show ((l a : ℂˣ) : ℂ) = (l a : ℂ) • (1 : ℂ) by rw [smul_eq_mul, mul_one], map_smul]`. Conclude with `this.symm`. Establish `hW : W = ⊤`.

Use `(hρ.eq_bot_or_eq_top W).resolve_left fun hb ↦ hF ?_` and prove the remaining obligations. Establish `h0 : F 1 = 0`. Use `hF1` as an intermediate fact. Rewrite `this` using `[hb]`. Conclude with `this`.

Apply `IntertwiningMap.ext` to reduce the goal to its premises. Apply `LinearMap.ext_ring` to reduce the goal to its premises. Rewrite using `[IntertwiningMap.toLinearMap_apply, h0]`. Both sides reduce to the same expression. Establish `hv : v ∈ W.toSubmodule`.

Rewrite using `[hW]`. Conclude with `Submodule.mem_top`. Conclude with `hv a`.
-/
theorem apply_eq_smul_of_forall_conj {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [hρ : ρ.IsIrreducible] (l : A →* ℂˣ)
    (h : charInner A (ρ.character ∘ A.subtype) (fun a ↦ (l a : ℂ)) ≠ 0)
    (hl : ∀ (g : G) (a : A), l (conjNormal A g a) = l a) (a : A) (v : V) :
    ρ a v = (l a : ℂ) • v := by
  have hrank : finrank ℂ (IntertwiningMap (linRep l) (ρ.comp A.subtype)) ≠ 0 := by
    rw [← Nat.cast_ne_zero (R := ℂ), ← charInner_character_character, character_linRep]
    exact h
  have : Nontrivial (IntertwiningMap (linRep l) (ρ.comp A.subtype)) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hrank)
  obtain ⟨F, hF⟩ := exists_ne (0 : IntertwiningMap (linRep l) (ρ.comp A.subtype))
  let W : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {w | ∀ a : A, ρ a w = (l a : ℂ) • w}
          add_mem' := fun {w w'} hw hw' a ↦ by rw [map_add, hw a, hw' a, smul_add]
          zero_mem' := fun a ↦ by rw [map_zero, smul_zero]
          smul_mem' := fun c w hw a ↦ by rw [map_smul, hw a, smul_comm] }
      apply_mem_toSubmodule := fun g w hw a ↦ by
        have hag : (a : G) * g = g * (conjNormal A g a : G) := by simp [mul_assoc]
        change ρ a (ρ g w) = (l a : ℂ) • ρ g w
        rw [← Module.End.mul_apply, ← map_mul, hag, map_mul, Module.End.mul_apply]
        rw [show ρ (conjNormal A g a : G) w = (l (conjNormal A g a) : ℂ) • w from hw _, hl, map_smul] }
  have hF1 : F 1 ∈ W.toSubmodule := fun a ↦ by
    have := IntertwiningMap.isIntertwining _ _ F a 1
    rw [linRep_apply, mul_one,
      show ((l a : ℂˣ) : ℂ) = (l a : ℂ) • (1 : ℂ) by rw [smul_eq_mul, mul_one], map_smul] at this
    exact this.symm
  have hW : W = ⊤ := by
    refine (hρ.eq_bot_or_eq_top W).resolve_left fun hb ↦ hF ?_
    have h0 : F 1 = 0 := by
      have := hF1
      rw [hb] at this
      exact this
    apply IntertwiningMap.ext
    apply LinearMap.ext_ring
    rw [IntertwiningMap.toLinearMap_apply, h0]
    rfl
  have hv : v ∈ W.toSubmodule := by
    rw [hW]
    exact Submodule.mem_top
  exact hv a

end Scalar

section Monomial

universe u

open Classical in

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `G _ _ _ hn χ hχ`. Take `⟨V, _, _, _, ρ, hρ, rfl⟩` from `hχ`. Distinguish the cases in `hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a`.

Take `⟨l, hl⟩` from `exists_hom_of_isIrreducible_of_commute ρ hc`. Conclude with `⟨⊤, l.comp (⊤ : Subgroup G).subtype, by rw [hl, indFun_top_hom]⟩`. Use `push Not at hc`. Take `⟨A, hAn, hAc, a₀, ha₀, g₀, hg₀⟩` from `exists_normal_commute_of_not_commute ρ hc`. Establish `hχA : IsCharacter (ρ.character ∘ A.subtype)` using `(isCharacter_character ρ).comp _`.

Establish `hne0 : ρ.character ∘ A.subtype ≠ 0` using `fun h0 ↦ (isIrrCharacter_character ρ).one_ne_zero (by simpa using congrFun h0 1)`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ, hφne⟩ : ∃ φ ∈ irrChars A, charInner A (ρ.character ∘ A.subtype) φ ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hne0 (eq_zero_of_isClassFun_of_charInner hχA.isClassFun hcon)`.

Take `⟨W, _, _, _, σ, hσ, rfl⟩` from `mem_irrChars.mp hφ`. Establish `hrank : finrank ℂ (IntertwiningMap σ (ρ.comp A.subtype)) ≠ 0`. Rewrite using `[← Nat.cast_ne_zero (R := ℂ), ← charInner_character_character]`. Conclude with `hφne`. Establish `: Nontrivial (IntertwiningMap σ (ρ.comp A.subtype))` using `Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hrank)`.

Take `⟨F, hF⟩` from `exists_ne (0 : IntertwiningMap σ (ρ.comp A.subtype))`. Establish `hFinj : Function.Injective F` using `(IsIrreducible.injective_or_eq_zero F).resolve_right hF`. Establish `hσc : ∀ a b : A, σ a * σ b = σ b * σ a`. Introduce `a b`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `w`. Apply `hFinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `F (σ a (σ b w)) = F (σ b (σ a w))`. Rewrite using `[IntertwiningMap.isIntertwining _ _ F, IntertwiningMap.isIntertwining _ _ F, IntertwiningMap.isIntertwining _ _ F, IntertwiningMap.isIntertwining _ _ F]`. Express the relevant statement in the definitionally equal form `(ρ a * ρ b) (F w) = (ρ b * ρ a) (F w)`.

Rewrite using `[hAc a a.2 b b.2]`. Take `⟨l, hl⟩` from `exists_hom_of_isIrreducible_of_commute σ hσc`. Rewrite `hφne` using `[hl]`. Distinguish the cases in `hT : inertia A (fun a ↦ (l a : ℂ)) = ⊤`. It suffices to derive a contradiction.

Establish `hlinv : ∀ (g : G) (a : A), l (conjNormal A g a) = l a`. Introduce `g a`. Establish `hg : g ∈ inertia A (fun a ↦ (l a : ℂ))` using `hT ▸ Subgroup.mem_top g`. Conclude with `Units.ext (hg a)`. Apply `hg₀` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Express the relevant statement in the definitionally equal form `ρ g₀ (ρ ((⟨a₀, ha₀⟩ : A) : G) v) = ρ ((⟨a₀, ha₀⟩ : A) : G) (ρ g₀ v)`. Rewrite using `[apply_eq_smul_of_forall_conj ρ l hφne hlinv, apply_eq_smul_of_forall_conj ρ l hφne hlinv, map_smul]`. Take `⟨ψ, hψ, hχψ⟩` from `(isIrrCharacter_character ρ).exists_eq_indFun_inertia (isIrrCharacter_hom l) hφne`.

Use `set T := inertia A (fun a ↦ (l a : ℂ))`. Establish `hlt : Nat.card T < n` using `hn ▸ lt_of_le_of_ne (Subgroup.card_le_card_group T) fun h ↦ hT ((Subgroup.card_eq_iff_eq_top T).mp h)`. Take `⟨K, l', hK⟩` from `ih (Nat.card T) hlt T rfl hψ`. Use `⟨K.map T.subtype, l'.comp (K.equivMapOfInjective T.subtype T.subtype_injective).symm.toMonoidHom, ?_⟩` and prove the remaining obligations. Rewrite using `[hχψ, hK, indFun_subtype_indFun_subtype]`.

Both sides reduce to the same expression.
-/
theorem exists_eq_indFun_of_isNilpotent_of_card (n : ℕ) :
    ∀ (G : Type u) [Group G] [Fintype G] [Group.IsNilpotent G], Nat.card G = n →
      ∀ {χ : G → ℂ}, IsIrrCharacter χ →
        ∃ (K : Subgroup G) (l : K →* ℂˣ), χ = indFun K.subtype (fun k ↦ (l k : ℂ)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ _ hn χ hχ
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hχ

  by_cases hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a
  · obtain ⟨l, hl⟩ := exists_hom_of_isIrreducible_of_commute ρ hc
    exact ⟨⊤, l.comp (⊤ : Subgroup G).subtype, by rw [hl, indFun_top_hom]⟩
  push Not at hc
  obtain ⟨A, hAn, hAc, a₀, ha₀, g₀, hg₀⟩ := exists_normal_commute_of_not_commute ρ hc

  have hχA : IsCharacter (ρ.character ∘ A.subtype) := (isCharacter_character ρ).comp _
  have hne0 : ρ.character ∘ A.subtype ≠ 0 := fun h0 ↦
    (isIrrCharacter_character ρ).one_ne_zero (by simpa using congrFun h0 1)
  obtain ⟨φ, hφ, hφne⟩ : ∃ φ ∈ irrChars A, charInner A (ρ.character ∘ A.subtype) φ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne0 (eq_zero_of_isClassFun_of_charInner hχA.isClassFun hcon)
  obtain ⟨W, _, _, _, σ, hσ, rfl⟩ := mem_irrChars.mp hφ

  have hrank : finrank ℂ (IntertwiningMap σ (ρ.comp A.subtype)) ≠ 0 := by
    rw [← Nat.cast_ne_zero (R := ℂ), ← charInner_character_character]
    exact hφne
  have : Nontrivial (IntertwiningMap σ (ρ.comp A.subtype)) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hrank)
  obtain ⟨F, hF⟩ := exists_ne (0 : IntertwiningMap σ (ρ.comp A.subtype))
  have hFinj : Function.Injective F := (IsIrreducible.injective_or_eq_zero F).resolve_right hF
  have hσc : ∀ a b : A, σ a * σ b = σ b * σ a := by
    intro a b
    apply LinearMap.ext
    intro w
    apply hFinj
    change F (σ a (σ b w)) = F (σ b (σ a w))
    rw [IntertwiningMap.isIntertwining _ _ F, IntertwiningMap.isIntertwining _ _ F,
      IntertwiningMap.isIntertwining _ _ F, IntertwiningMap.isIntertwining _ _ F]
    change (ρ a * ρ b) (F w) = (ρ b * ρ a) (F w)
    rw [hAc a a.2 b b.2]
  obtain ⟨l, hl⟩ := exists_hom_of_isIrreducible_of_commute σ hσc
  rw [hl] at hφne
  by_cases hT : inertia A (fun a ↦ (l a : ℂ)) = ⊤
  ·
    exfalso
    have hlinv : ∀ (g : G) (a : A), l (conjNormal A g a) = l a := by
      intro g a
      have hg : g ∈ inertia A (fun a ↦ (l a : ℂ)) := hT ▸ Subgroup.mem_top g
      exact Units.ext (hg a)
    apply hg₀
    apply LinearMap.ext
    intro v
    change ρ g₀ (ρ ((⟨a₀, ha₀⟩ : A) : G) v) = ρ ((⟨a₀, ha₀⟩ : A) : G) (ρ g₀ v)
    rw [apply_eq_smul_of_forall_conj ρ l hφne hlinv, apply_eq_smul_of_forall_conj ρ l hφne hlinv,
      map_smul]
  ·
    obtain ⟨ψ, hψ, hχψ⟩ :=
      (isIrrCharacter_character ρ).exists_eq_indFun_inertia (isIrrCharacter_hom l) hφne
    set T := inertia A (fun a ↦ (l a : ℂ))
    have hlt : Nat.card T < n := hn ▸ lt_of_le_of_ne (Subgroup.card_le_card_group T)
      fun h ↦ hT ((Subgroup.card_eq_iff_eq_top T).mp h)
    obtain ⟨K, l', hK⟩ := ih (Nat.card T) hlt T rfl hψ
    refine ⟨K.map T.subtype,
      l'.comp (K.equivMapOfInjective T.subtype T.subtype_injective).symm.toMonoidHom, ?_⟩
    rw [hχψ, hK, indFun_subtype_indFun_subtype]
    rfl

open Classical in

/- English proof (translation)
The claim follows from `exists_eq_indFun_of_isNilpotent_of_card _ G rfl h`.
-/
theorem IsIrrCharacter.exists_eq_indFun_of_isNilpotent {G : Type*} [Group G] [Fintype G]
    [Group.IsNilpotent G] {χ : G → ℂ} (h : IsIrrCharacter χ) :
    ∃ (K : Subgroup G) (l : K →* ℂˣ), χ = indFun K.subtype (fun k ↦ (l k : ℂ)) :=
  exists_eq_indFun_of_isNilpotent_of_card _ G rfl h

end Monomial

end GroundTheory.LocalField
