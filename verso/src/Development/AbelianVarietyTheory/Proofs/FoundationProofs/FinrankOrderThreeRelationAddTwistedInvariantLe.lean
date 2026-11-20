import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

/- English proof (translation)
Introduce `G _ E _ _ Γ ρ t hmul hone ht hfd`. Establish `h2 : ∀ v, ρ (t ^ 2) v = ρ t (ρ t v)` using `fun v => by rw [pow_two, hmul]`. Establish `h3 : ∀ v, ρ (t ^ 3) v = ρ t (ρ t (ρ t v))` using `fun v => by`. Rewrite using `[pow_succ t 2, hmul, h2]`. Establish `h6 : ∀ v, ρ t (ρ t (ρ t (ρ t (ρ t (ρ t v))))) = v` using `fun v => by`.

Establish `h : t ^ 3 * t ^ 3 = 1` using `by rw [← pow_add]; exact ht`. Establish `h'` using `hmul (t ^ 3) (t ^ 3) v`. Rewrite `h'` using `[h, hone, h3, h3]`. Conclude with `h'.symm`. Establish `e2 : ∀ x : G, x * t * t = x * t ^ 2` using `fun x => by rw [pow_two, mul_assoc]`.

Establish `e3 : ∀ x : G, x * t * t ^ 2 = x * t ^ 3` using `fun x => by`. Rewrite using `[mul_assoc, ← pow_succ']`. Establish `hle : relThree Γ ρ t ≤ twInv Γ (t ^ 3) (ρ (t ^ 3))` using `fun Φ hΦ => hΦ.1`. Use `⟨Submodule.finiteDimensional_of_le hle, ?_⟩` and prove the remaining obligations. Set `P : twInv Γ (t ^ 3) (ρ (t ^ 3)) →ₗ[ℂ] twInv Γ t (ρ t)` to `{ toFun := fun Φ => ⟨fun x => ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2), by`.

Take `⟨Φ, hΓ, hΦ⟩` from `Φ`. Use `⟨fun γ hγ x => ?_, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [mul_assoc, hΓ γ hγ]`. Simplify using `only [e2, e3, hΦ, h2, h3, map_add] abel⟩`. Use the proof step `map_add' := fun Φ Ψ => by`.

Use extensionality with `x`. Simplify using `only [Submodule.coe_add, Pi.add_apply, map_add]`. Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := fun c Φ => by`. Use extensionality with `x`.

Simplify using `only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply, smul_add] }`. Establish `hP : ∀ Φ x, (P Φ).1 x = ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2)` using `fun _ _ => rfl`. Establish `hsurj : LinearMap.range P = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce and unpack `⟨Ψ, hΓ, hΨ⟩`.

Establish `hΨ2 : ∀ x, Ψ (x * t ^ 2) = ρ t (ρ t (Ψ x))` using `fun x => by rw [← e2, hΨ, hΨ]`. Establish `hΨ3 : ∀ x, Ψ (x * t ^ 3) = ρ t (ρ t (ρ t (Ψ x)))` using `fun x => by rw [← e3, hΨ2, hΨ]`. Use `⟨⟨fun x => (1 / 3 : ℂ) • ρ t (ρ t (ρ t (ρ t (Ψ x)))), fun γ hγ x => ?_, fun x => ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [hΓ γ hγ]`. Simplify using `only [hΨ3, h3, map_smul]`.

Use extensionality with `x`. Rewrite using `[hP]`. Simplify using `only [hΨ, hΨ2, h2, map_smul, h6]`. Use `module`. Establish `hker : Module.finrank ℂ (relThree Γ ρ t) ≤ Module.finrank ℂ (LinearMap.ker P)`.

Set `ι : relThree Γ ρ t →ₗ[ℂ] LinearMap.ker P` to `(Submodule.inclusion hle).codRestrict _ (fun Φ => by`. Rewrite using `[LinearMap.mem_ker]`. Use extensionality with `x`. Rewrite using `[hP]`. Conclude with `Φ.2.2 x)`.

Use `LinearMap.finrank_le_finrank_of_injective (f := ι) ?_` and prove the remaining obligations. Introduce `a b hab`. Conclude with `Submodule.inclusion_injective hle (congrArg Subtype.val hab)`. Establish `hrk` using `LinearMap.finrank_range_add_finrank_ker P`. Rewrite `hrk` using `[hsurj, finrank_top]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_relThree_add_finrank_twInv_le :
    ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G)
      (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) →
      t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) →
      FiniteDimensional ℂ (relThree Γ ρ t) ∧
        Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤
          Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  intro G _ E _ _ Γ ρ t hmul hone ht hfd
  have h2 : ∀ v, ρ (t ^ 2) v = ρ t (ρ t v) := fun v => by rw [pow_two, hmul]
  have h3 : ∀ v, ρ (t ^ 3) v = ρ t (ρ t (ρ t v)) := fun v => by
    rw [pow_succ t 2, hmul, h2]
  have h6 : ∀ v, ρ t (ρ t (ρ t (ρ t (ρ t (ρ t v))))) = v := fun v => by
    have h : t ^ 3 * t ^ 3 = 1 := by rw [← pow_add]; exact ht
    have h' := hmul (t ^ 3) (t ^ 3) v
    rw [h, hone, h3, h3] at h'
    exact h'.symm
  have e2 : ∀ x : G, x * t * t = x * t ^ 2 := fun x => by rw [pow_two, mul_assoc]
  have e3 : ∀ x : G, x * t * t ^ 2 = x * t ^ 3 := fun x => by
    rw [mul_assoc, ← pow_succ']
  have hle : relThree Γ ρ t ≤ twInv Γ (t ^ 3) (ρ (t ^ 3)) := fun Φ hΦ => hΦ.1
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  let P : twInv Γ (t ^ 3) (ρ (t ^ 3)) →ₗ[ℂ] twInv Γ t (ρ t) :=
    { toFun := fun Φ => ⟨fun x => ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2), by
        obtain ⟨Φ, hΓ, hΦ⟩ := Φ
        refine ⟨fun γ hγ x => ?_, fun x => ?_⟩
        · simp only [mul_assoc, hΓ γ hγ]
        · simp only [e2, e3, hΦ, h2, h3, map_add]
          abel⟩
      map_add' := fun Φ Ψ => by
        ext x
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        abel
      map_smul' := fun c Φ => by
        ext x
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply, smul_add] }
  have hP : ∀ Φ x, (P Φ).1 x = ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2) :=
    fun _ _ => rfl
  have hsurj : LinearMap.range P = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨Ψ, hΓ, hΨ⟩
    have hΨ2 : ∀ x, Ψ (x * t ^ 2) = ρ t (ρ t (Ψ x)) := fun x => by rw [← e2, hΨ, hΨ]
    have hΨ3 : ∀ x, Ψ (x * t ^ 3) = ρ t (ρ t (ρ t (Ψ x))) := fun x => by rw [← e3, hΨ2, hΨ]
    refine ⟨⟨fun x => (1 / 3 : ℂ) • ρ t (ρ t (ρ t (ρ t (Ψ x)))), fun γ hγ x => ?_, fun x => ?_⟩, ?_⟩
    · simp only [hΓ γ hγ]
    · simp only [hΨ3, h3, map_smul]
    · ext x
      rw [hP]
      simp only [hΨ, hΨ2, h2, map_smul, h6]
      module
  have hker : Module.finrank ℂ (relThree Γ ρ t) ≤ Module.finrank ℂ (LinearMap.ker P) := by
    let ι : relThree Γ ρ t →ₗ[ℂ] LinearMap.ker P :=
      (Submodule.inclusion hle).codRestrict _ (fun Φ => by
        rw [LinearMap.mem_ker]
        ext x
        rw [hP]
        exact Φ.2.2 x)
    refine LinearMap.finrank_le_finrank_of_injective (f := ι) ?_
    intro a b hab
    exact Submodule.inclusion_injective hle (congrArg Subtype.val hab)
  have hrk := LinearMap.finrank_range_add_finrank_ker P
  rw [hsurj, finrank_top] at hrk
  omega

end GlobalTheory.HeckeFamilyMatrices.CocBound
