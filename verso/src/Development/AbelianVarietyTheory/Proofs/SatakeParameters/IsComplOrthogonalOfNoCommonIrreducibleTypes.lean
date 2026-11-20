import Mathlib

open Module

namespace GlobalTheory.IsotypicOrth

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
  {σ : K →* K}

/- English proof (translation)
Rewrite using `[← hB k x (ρ (σ k⁻¹) y), map_inv, Representation.self_inv_apply]`.
-/
lemma pair_left (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    (k : K) (x y : V) : B (ρ k x) y = B x (ρ (σ k⁻¹) y) := by
  rw [← hB k x (ρ (σ k⁻¹) y), map_inv, Representation.self_inv_apply]

/- English proof (translation)
Set `T : Subrepresentation ρ` to `⟨S₁.toSubmodule ⊓ ⨅ y ∈ S.toSubmodule, LinearMap.ker (B.flip y), by`. Introduce `k x hx`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply] at hx ⊢`. Use `⟨S₁.apply_mem_toSubmodule k hx.1, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[pair_left B hB]`.

Conclude with `hx.2 _ (S.apply_mem_toSubmodule _ hy)⟩`. Establish `hle : T ≤ S₁` using `fun x hx => (Submodule.mem_inf.mp hx).1`. Establish `hmem : ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x ∈ T.toSubmodule`. Introduce `x hx h0`. Simplify using `only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]`.

Conclude with `⟨hx, h0⟩`. Break down `h₁.le_iff.mp hle with h | h` into its components or cases. Introduce `x hx h0`. Establish `hT : T.toSubmodule = ⊥` using `congrArg Subrepresentation.toSubmodule h`. Use `hmem x hx h0` as an intermediate fact.

Rewrite `this` using `[hT]`. Conclude with `(Submodule.mem_bot ℂ).mp this`. It suffices to derive a contradiction. Take `⟨x, hx, y, hy, hne⟩` from `hn`. Establish `hT : T.toSubmodule = S₁.toSubmodule` using `congrArg Subrepresentation.toSubmodule h`.

Rewrite `hx` using `[← hT]`. Simplify using `only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply] at hx`. Conclude with `hne (hx.2 y hy)`.
-/
lemma left_ker_zero (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x = 0 := by
  let T : Subrepresentation ρ :=
    ⟨S₁.toSubmodule ⊓ ⨅ y ∈ S.toSubmodule, LinearMap.ker (B.flip y), by
      intro k x hx
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.flip_apply] at hx ⊢
      refine ⟨S₁.apply_mem_toSubmodule k hx.1, fun y hy => ?_⟩
      rw [pair_left B hB]
      exact hx.2 _ (S.apply_mem_toSubmodule _ hy)⟩
  have hle : T ≤ S₁ := fun x hx => (Submodule.mem_inf.mp hx).1
  have hmem : ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x ∈ T.toSubmodule := by
    intro x hx h0
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    exact ⟨hx, h0⟩
  rcases h₁.le_iff.mp hle with h | h
  · intro x hx h0
    have hT : T.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    have := hmem x hx h0
    rw [hT] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exfalso
    obtain ⟨x, hx, y, hy, hne⟩ := hn
    have hT : T.toSubmodule = S₁.toSubmodule := congrArg Subrepresentation.toSubmodule h
    rw [← hT] at hx
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.flip_apply] at hx
    exact hne (hx.2 y hy)

/- English proof (translation)
Set `T : Subrepresentation ρ` to `⟨S.toSubmodule ⊓ ⨅ x ∈ S₁.toSubmodule, LinearMap.ker (B x), by`. Introduce `k' y hy`. Take `⟨k, rfl⟩` from `hσ k'`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢`. Use `⟨S.apply_mem_toSubmodule _ hy.1, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `e` using `hB k (ρ k⁻¹ x) y`. Rewrite `e` using `[Representation.self_inv_apply]`. Rewrite using `[e]`. Conclude with `hy.2 _ (S₁.apply_mem_toSubmodule _ hx)⟩`. Establish `hle : T ≤ S` using `fun x hx => (Submodule.mem_inf.mp hx).1`.

Establish `hmem : ∀ y ∈ S.toSubmodule, (∀ x ∈ S₁.toSubmodule, B x y = 0) → y ∈ T.toSubmodule`. Introduce `y hy h0`. Simplify using `only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]`. Conclude with `⟨hy, h0⟩`. Break down `h.le_iff.mp hle with h' | h'` into its components or cases.

Introduce `y hy h0`. Establish `hT : T.toSubmodule = ⊥` using `congrArg Subrepresentation.toSubmodule h'`. Use `hmem y hy h0` as an intermediate fact. Rewrite `this` using `[hT]`. Conclude with `(Submodule.mem_bot ℂ).mp this`.

It suffices to derive a contradiction. Take `⟨x, hx, y, hy, hne⟩` from `hn`. Establish `hT : T.toSubmodule = S.toSubmodule` using `congrArg Subrepresentation.toSubmodule h'`. Rewrite `hy` using `[← hT]`. Simplify using `only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy`.

Conclude with `hne (hy.2 x hx)`.
-/
lemma right_ker_zero (hσ : Function.Surjective σ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h : IsAtom S)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    ∀ y ∈ S.toSubmodule, (∀ x ∈ S₁.toSubmodule, B x y = 0) → y = 0 := by
  let T : Subrepresentation ρ :=
    ⟨S.toSubmodule ⊓ ⨅ x ∈ S₁.toSubmodule, LinearMap.ker (B x), by
      intro k' y hy
      obtain ⟨k, rfl⟩ := hσ k'
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      refine ⟨S.apply_mem_toSubmodule _ hy.1, fun x hx => ?_⟩
      have e := hB k (ρ k⁻¹ x) y
      rw [Representation.self_inv_apply] at e
      rw [e]
      exact hy.2 _ (S₁.apply_mem_toSubmodule _ hx)⟩
  have hle : T ≤ S := fun x hx => (Submodule.mem_inf.mp hx).1
  have hmem : ∀ y ∈ S.toSubmodule, (∀ x ∈ S₁.toSubmodule, B x y = 0) → y ∈ T.toSubmodule := by
    intro y hy h0
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    exact ⟨hy, h0⟩
  rcases h.le_iff.mp hle with h' | h'
  · intro y hy h0
    have hT : T.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h'
    have := hmem y hy h0
    rw [hT] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exfalso
    obtain ⟨x, hx, y, hy, hne⟩ := hn
    have hT : T.toSubmodule = S.toSubmodule := congrArg Subrepresentation.toSubmodule h'
    rw [← hT] at hy
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy
    exact hne (hy.2 x hx)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Apply `Subtype.ext` to reduce the goal to its premises. Use `left_ker_zero B hB h₁ hn a a.2 fun y hy => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun ha ⟨y, hy⟩` as an intermediate fact.

Simplify `this` using `[LinearMap.domRestrict₁₂_apply]`.
-/
lemma restr_injective (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Function.Injective (B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply Subtype.ext
  refine left_ker_zero B hB h₁ hn a a.2 fun y hy => ?_
  have := LinearMap.congr_fun ha ⟨y, hy⟩
  simpa [LinearMap.domRestrict₁₂_apply] using this

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Apply `Subtype.ext` to reduce the goal to its premises. Use `right_ker_zero hσ B hB h hn a a.2 fun x hx => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun ha ⟨x, hx⟩` as an intermediate fact.

Simplify `this` using `[LinearMap.domRestrict₁₂_apply]`.
-/
lemma restr_flip_injective (hσ : Function.Surjective σ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h : IsAtom S)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Function.Injective (B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule).flip := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply Subtype.ext
  refine right_ker_zero hσ B hB h hn a a.2 fun x hx => ?_
  have := LinearMap.congr_fun ha ⟨x, hx⟩
  simpa [LinearMap.domRestrict₁₂_apply] using this

/- English proof (translation)
Use `haveI := hfin S₁ h₁`. Use `haveI := hfin S₂ h₂`. Use `haveI := hfin S h`. Use `set f₁ := B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule with hf₁def`. Use `set f₂ := B.domRestrict₁₂ S₂.toSubmodule S.toSubmodule with hf₂def`.

Establish `i₁ : Function.Injective f₁` using `restr_injective B hB h₁ hn₁`. Establish `i₂ : Function.Injective f₂` using `restr_injective B hB h₂ hn₂`. Establish `j₁ : Function.Injective f₁.flip` using `restr_flip_injective hσ B hB h hn₁`. Establish `j₂ : Function.Injective f₂.flip` using `restr_flip_injective hσ B hB h hn₂`. Establish `d₁ : finrank ℂ S₁.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule)`.

Rewrite using `[Subspace.dual_finrank_eq]`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Conclude with `(LinearMap.finrank_le_finrank_of_injective i₁).trans_eq Subspace.dual_finrank_eq`. Conclude with `(LinearMap.finrank_le_finrank_of_injective j₁).trans_eq Subspace.dual_finrank_eq`. Establish `d₂ : finrank ℂ S₂.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule)`.

Rewrite using `[Subspace.dual_finrank_eq]`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Conclude with `(LinearMap.finrank_le_finrank_of_injective i₂).trans_eq Subspace.dual_finrank_eq`. Conclude with `(LinearMap.finrank_le_finrank_of_injective j₂).trans_eq Subspace.dual_finrank_eq`. Set `e₁` to `LinearEquiv.ofBijective f₁ ⟨i₁, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₁).mp i₁⟩`.

Set `e₂` to `LinearEquiv.ofBijective f₂ ⟨i₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₂).mp i₂⟩`. Set `e` to `e₁.trans e₂.symm`. Establish `hfe : ∀ x, f₂ (e x) = f₁ x`. Introduce `x`. Establish `h1 : ∀ z, e₁ z = f₁ z` using `fun z => LinearEquiv.ofBijective_apply _ _`.

Establish `h2 : ∀ z, e₂ z = f₂ z` using `fun z => LinearEquiv.ofBijective_apply _ _`. Rewrite using `[← h1, ← h2]`. Simplify using `[e]`. Establish `hcomm : ∀ (x : S₁.toSubmodule) (y : S.toSubmodule), B (e x : V) y = B x y`. Introduce `x y`.

Use `LinearMap.congr_fun (hfe x) y` as an intermediate fact. Simplify `this` using `[f₁, f₂, LinearMap.domRestrict₁₂_apply]`. Use `⟨Representation.Equiv.mk e fun k => ?_⟩` and prove the remaining obligations. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`.

Apply `i₂` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf₂def, LinearMap.domRestrict₁₂_apply]`. Rewrite using `[hcomm]`.

Express the relevant statement in the definitionally equal form `B (ρ k x) y = B (ρ k (e x)) y`. Rewrite using `[pair_left B hB, pair_left B hB]`. Conclude with `(hcomm x ⟨_, S.apply_mem_toSubmodule _ y.2⟩).symm`.
-/
theorem nonempty_equiv_of_pair (hσ : Function.Surjective σ)
    (hfin : ∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S₂ S : Subrepresentation ρ} (h₁ : IsAtom S₁) (h₂ : IsAtom S₂) (h : IsAtom S)
    (hn₁ : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0)
    (hn₂ : ∃ x ∈ S₂.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) := by
  haveI := hfin S₁ h₁
  haveI := hfin S₂ h₂
  haveI := hfin S h
  set f₁ := B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule with hf₁def
  set f₂ := B.domRestrict₁₂ S₂.toSubmodule S.toSubmodule with hf₂def
  have i₁ : Function.Injective f₁ := restr_injective B hB h₁ hn₁
  have i₂ : Function.Injective f₂ := restr_injective B hB h₂ hn₂
  have j₁ : Function.Injective f₁.flip := restr_flip_injective hσ B hB h hn₁
  have j₂ : Function.Injective f₂.flip := restr_flip_injective hσ B hB h hn₂
  have d₁ : finrank ℂ S₁.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule) := by
    rw [Subspace.dual_finrank_eq]
    refine le_antisymm ?_ ?_
    · exact (LinearMap.finrank_le_finrank_of_injective i₁).trans_eq Subspace.dual_finrank_eq
    · exact (LinearMap.finrank_le_finrank_of_injective j₁).trans_eq Subspace.dual_finrank_eq
  have d₂ : finrank ℂ S₂.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule) := by
    rw [Subspace.dual_finrank_eq]
    refine le_antisymm ?_ ?_
    · exact (LinearMap.finrank_le_finrank_of_injective i₂).trans_eq Subspace.dual_finrank_eq
    · exact (LinearMap.finrank_le_finrank_of_injective j₂).trans_eq Subspace.dual_finrank_eq
  let e₁ := LinearEquiv.ofBijective f₁ ⟨i₁, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₁).mp i₁⟩
  let e₂ := LinearEquiv.ofBijective f₂ ⟨i₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₂).mp i₂⟩
  let e := e₁.trans e₂.symm
  have hfe : ∀ x, f₂ (e x) = f₁ x := by
    intro x
    have h1 : ∀ z, e₁ z = f₁ z := fun z => LinearEquiv.ofBijective_apply _ _
    have h2 : ∀ z, e₂ z = f₂ z := fun z => LinearEquiv.ofBijective_apply _ _
    rw [← h1, ← h2]
    simp [e]
  have hcomm : ∀ (x : S₁.toSubmodule) (y : S.toSubmodule), B (e x : V) y = B x y := by
    intro x y
    have := LinearMap.congr_fun (hfe x) y
    simpa [f₁, f₂, LinearMap.domRestrict₁₂_apply] using this
  refine ⟨Representation.Equiv.mk e fun k => ?_⟩
  apply LinearMap.ext
  intro x
  apply i₂
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf₂def, LinearMap.domRestrict₁₂_apply]
  rw [hcomm]
  change B (ρ k x) y = B (ρ k (e x)) y
  rw [pair_left B hB, pair_left B hB]
  exact (hcomm x ⟨_, S.apply_mem_toSubmodule _ y.2⟩).symm

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨y, hy, hne⟩` from `h`. Apply `hne` to reduce the goal to its premises. Establish `hle : Y.toSubmodule ≤ LinearMap.ker (B.flip ψ)`.

Rewrite using `[hsum Y]`. Conclude with `iSup₂_le fun S hS x hx => by simpa using hc S hS.1 hS.2 x hx`. Simplify using `using hle hy`.
-/
lemma exists_atom_pair
    (hsum : ∀ X : Subrepresentation ρ,
      X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (Y : Subrepresentation ρ) (ψ : V)
    (h : ∃ y ∈ Y.toSubmodule, B y ψ ≠ 0) :
    ∃ S₁ : Subrepresentation ρ, IsAtom S₁ ∧ S₁ ≤ Y ∧ ∃ x ∈ S₁.toSubmodule, B x ψ ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨y, hy, hne⟩ := h
  apply hne
  have hle : Y.toSubmodule ≤ LinearMap.ker (B.flip ψ) := by
    rw [hsum Y]
    exact iSup₂_le fun S hS x hx => by simpa using hc S hS.1 hS.2 x hx
  simpa using hle hy

end GlobalTheory.IsotypicOrth

namespace GlobalTheory.IsotypicOrth

/- English proof (translation)
Introduce `K V _ _ _ ρ σ hσ hfin hsum B _hl hr hB X Y hXY hiso`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.disjoint_def]`. Introduce `ψ h1 h2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at h1 h2`.

Apply `hr` to reduce the goal to its premises. Introduce `φ`. Establish `: φ ∈ X.toSubmodule ⊔ Y.toSubmodule` using `by rw [hXY.sup_eq_top]; trivial`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp this`. Rewrite using `[map_add, LinearMap.add_apply, h1 b hb, h2 a ha, add_zero]`.

Rewrite using `[codisjoint_iff, eq_top_iff]`. Establish `htop` using `hsum ⊤`. Express the relevant statement in the definitionally equal form `(⊤ : Submodule ℂ V) = _ at htop`. Rewrite using `[htop]`. Use `iSup₂_le fun S hS => ?_` and prove the remaining obligations.

Distinguish the cases in `hY : S.toSubmodule ≤ ⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)`. Conclude with `le_sup_of_le_left hY`. Distinguish the cases in `hX : S.toSubmodule ≤ ⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)`. Conclude with `le_sup_of_le_right hX`. It suffices to derive a contradiction.

Take `⟨ψ₁, hψ₁, hψ₁'⟩` from `SetLike.not_le_iff_exists.mp hY`. Take `⟨ψ₂, hψ₂, hψ₂'⟩` from `SetLike.not_le_iff_exists.mp hX`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, not_forall] at hψ₁' hψ₂'`. Take `⟨y, hy, hy'⟩` from `hψ₁'`. Take `⟨x, hx, hx'⟩` from `hψ₂'`.

Take `⟨S₁, a₁, l₁, x₁, hx₁, n₁⟩` from `exists_atom_pair hsum B Y ψ₁ ⟨y, hy, hy'⟩`. Take `⟨S₂, a₂, l₂, x₂, hx₂, n₂⟩` from `exists_atom_pair hsum B X ψ₂ ⟨x, hx, hx'⟩`. Establish `e` using `nonempty_equiv_of_pair hσ hfin B hB a₁ a₂ hS.1 ⟨x₁, hx₁, ψ₁, hψ₁, n₁⟩ ⟨x₂, hx₂, ψ₂, hψ₂, n₂⟩`. Conclude with `(hiso S₁ S₂ a₁ a₂ l₁ l₂).false e.some`.
-/
theorem orth_isCompl : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V) (σ : K →* K), Function.Surjective σ → (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) → ∀ X Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule → (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) → IsCompl (⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)) (⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)) := by
  intro K V _ _ _ ρ σ hσ hfin hsum B _hl hr hB X Y hXY hiso
  constructor
  · rw [Submodule.disjoint_def]
    intro ψ h1 h2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h1 h2
    apply hr
    intro φ
    have : φ ∈ X.toSubmodule ⊔ Y.toSubmodule := by rw [hXY.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
    rw [map_add, LinearMap.add_apply, h1 b hb, h2 a ha, add_zero]
  · rw [codisjoint_iff, eq_top_iff]
    have htop := hsum ⊤
    change (⊤ : Submodule ℂ V) = _ at htop
    rw [htop]
    refine iSup₂_le fun S hS => ?_
    by_cases hY : S.toSubmodule ≤ ⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)
    · exact le_sup_of_le_left hY
    by_cases hX : S.toSubmodule ≤ ⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)
    · exact le_sup_of_le_right hX
    exfalso
    obtain ⟨ψ₁, hψ₁, hψ₁'⟩ := SetLike.not_le_iff_exists.mp hY
    obtain ⟨ψ₂, hψ₂, hψ₂'⟩ := SetLike.not_le_iff_exists.mp hX
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, not_forall] at hψ₁' hψ₂'
    obtain ⟨y, hy, hy'⟩ := hψ₁'
    obtain ⟨x, hx, hx'⟩ := hψ₂'
    obtain ⟨S₁, a₁, l₁, x₁, hx₁, n₁⟩ := exists_atom_pair hsum B Y ψ₁ ⟨y, hy, hy'⟩
    obtain ⟨S₂, a₂, l₂, x₂, hx₂, n₂⟩ := exists_atom_pair hsum B X ψ₂ ⟨x, hx, hx'⟩
    have e := nonempty_equiv_of_pair hσ hfin B hB a₁ a₂ hS.1 ⟨x₁, hx₁, ψ₁, hψ₁, n₁⟩
      ⟨x₂, hx₂, ψ₂, hψ₂, n₂⟩
    exact (hiso S₁ S₂ a₁ a₂ l₁ l₂).false e.some

end GlobalTheory.IsotypicOrth
