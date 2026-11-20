import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Anisotropic

namespace PI.Witt

variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Introduce `n`. Use `Nat.strong_induction_on n (fun n ih => ?_)` and prove the remaining obligations. Introduce `U hU hnd f hf`. Distinguish the cases in `hex : ∃ x ∈ U, ∃ y ∈ U, B x y ≠ 0`. Take `⟨u, hu, hBu⟩` from `h2 K V B hB U hex`.

Take `⟨g₁, hg₁, hg₁u, hg₁fix⟩` from `h1 K V B hB u (f ⟨u, hu⟩) (hf ⟨u, hu⟩ ⟨u, hu⟩).symm hBu`. Establish `hsym : ∀ a b, B (g₁.symm a) b = B a (g₁ b)`. Introduce `a b`. Rewrite using `[← hg₁ (g₁.symm a) b, LinearEquiv.apply_symm_apply]`. Establish `hsym₂ : ∀ a b, B (g₁.symm a) (g₁.symm b) = B a b`.

Introduce `a b`. Rewrite using `[hsym, LinearEquiv.apply_symm_apply]`. Set `U' : Submodule K V` to `U ⊓ LinearMap.ker (B u)`. Establish `hle : U' ≤ U` using `inf_le_left`. Establish `hker : ∀ w ∈ U', B u w = 0` using `fun w hw => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2`.

Establish `hwu : ∀ w ∈ U', B w u = 0`. Introduce `w hw`. Rewrite using `[← hB u w, hker w hw, star_zero]`. Establish `hproj : ∀ y ∈ U, y - (B u y / B u u) • u ∈ U'`. Introduce `y hy`.

Use `Submodule.mem_inf.mpr ⟨U.sub_mem hy (U.smul_mem _ hu), LinearMap.mem_ker.mpr ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hBu, sub_self]`. Establish `hlt : Module.finrank K U' < n`. Rewrite using `[← hU]`. Use `Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle fun heq => hBu ?_)` and prove the remaining obligations.

Establish `hu' : u ∈ U'` using `by rw [heq]; exact hu`. Conclude with `hker u hu'`. Establish `hnd' : ∀ x ∈ U', (∀ y ∈ U', B x y = 0) → x = 0`. Introduce `x hx hxy`. Use `hnd x (hle hx) fun y hy => ?_` and prove the remaining obligations.

Establish `h` using `hxy _ (hproj y hy)`. Rewrite `h` using `[map_sub, map_smul, hwu x hx, smul_zero, sub_zero]`. Conclude with `h`. Set `f' : U' →ₗ[K] V` to `g₁.symm.toLinearMap ∘ₗ f ∘ₗ Submodule.inclusion hle`. Establish `hf'x : ∀ x : U', f' x = g₁.symm (f (Submodule.inclusion hle x))` using `fun x => rfl`.

Establish `hf' : ∀ x y : U', B (f' x) (f' y) = B x y`. Introduce `x y`. Rewrite using `[hf'x, hf'x, hsym₂, hf]`. Both sides reduce to the same expression. Take `⟨g₂, hg₂, hg₂f, hg₂fix⟩` from `ih _ hlt U' rfl hnd' f' hf'`.

Establish `hg₂u : g₂ u = u`. Use `hg₂fix u (fun w => hwu w w.2) fun w => ?_` and prove the remaining obligations. Rewrite using `[hf'x, hsym, hg₁u, hf]`. Conclude with `hwu w w.2`. Use `⟨g₂.trans g₁, fun x y => ?_, fun x => ?_, fun z hz₁ hz₂ => ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearEquiv.trans_apply]`. Rewrite using `[hg₁, hg₂]`. Take `⟨c, hc⟩ : ∃ c : K, c = B u x / B u u` from `⟨_, rfl⟩`. Establish `hmem : (x : V) - c • u ∈ U'` using `hc ▸ hproj x x.2`. Set `x' : U'` to `⟨_, hmem⟩`.

Establish `hxv : (x : V) = c • u + (x' : V)` using `by simp [x']`. Establish `hxU : x = c • (⟨u, hu⟩ : U) + Submodule.inclusion hle x'` using `Subtype.ext (by simp [x'])`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_add, map_smul, hg₂u, hg₂f x', map_add, map_smul]`. Use `_ = f x := by`.

Rewrite using `[hg₁u, hf'x, LinearEquiv.apply_symm_apply]`. Use `conv_rhs => rw [hxU]`. Rewrite using `[map_add, map_smul]`. Establish `hg₁z : g₁ z = z` using `hg₁fix z (hz₁ ⟨u, hu⟩) (hz₂ ⟨u, hu⟩)`. Establish `hg₂z : g₂ z = z`.

Use `hg₂fix z (fun w => hz₁ (Submodule.inclusion hle w)) fun w => ?_` and prove the remaining obligations. Rewrite using `[hf'x, hsym, hg₁z]`. Conclude with `hz₂ _`. Use `show g₁ (g₂ z) = z`. Rewrite using `[hg₂z, hg₁z]`.

Use `push Not at hex`. Use `⟨LinearEquiv.refl K V, fun x y => rfl, fun x => ?_, fun z _ _ => rfl⟩` and prove the remaining obligations. Establish `hx0 : x = 0` using `Subtype.ext (hnd x x.2 (hex x x.2))`. Substitute `hx0` using the available equality. Simplify using the standard rewrite rules.
-/
theorem nondeg_extend (h1 : OneVector) (h2 : Anisotropic) [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x) :
    ∀ (n : ℕ) (U : Submodule K V), Module.finrank K U = n →
      (∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0) →
      ∀ f : U →ₗ[K] V, (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ (∀ x : U, g x = f x) ∧
        ∀ z, (∀ u : U, B (u : V) z = 0) → (∀ u : U, B (f u) z = 0) → g z = z := by
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro U hU hnd f hf
  by_cases hex : ∃ x ∈ U, ∃ y ∈ U, B x y ≠ 0
  · obtain ⟨u, hu, hBu⟩ := h2 K V B hB U hex
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ :=
      h1 K V B hB u (f ⟨u, hu⟩) (hf ⟨u, hu⟩ ⟨u, hu⟩).symm hBu
    have hsym : ∀ a b, B (g₁.symm a) b = B a (g₁ b) := by
      intro a b
      rw [← hg₁ (g₁.symm a) b, LinearEquiv.apply_symm_apply]
    have hsym₂ : ∀ a b, B (g₁.symm a) (g₁.symm b) = B a b := by
      intro a b
      rw [hsym, LinearEquiv.apply_symm_apply]
    let U' : Submodule K V := U ⊓ LinearMap.ker (B u)
    have hle : U' ≤ U := inf_le_left
    have hker : ∀ w ∈ U', B u w = 0 := fun w hw => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2
    have hwu : ∀ w ∈ U', B w u = 0 := by
      intro w hw
      rw [← hB u w, hker w hw, star_zero]
    have hproj : ∀ y ∈ U, y - (B u y / B u u) • u ∈ U' := by
      intro y hy
      refine Submodule.mem_inf.mpr ⟨U.sub_mem hy (U.smul_mem _ hu), LinearMap.mem_ker.mpr ?_⟩
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hBu, sub_self]
    have hlt : Module.finrank K U' < n := by
      rw [← hU]
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle fun heq => hBu ?_)
      have hu' : u ∈ U' := by rw [heq]; exact hu
      exact hker u hu'
    have hnd' : ∀ x ∈ U', (∀ y ∈ U', B x y = 0) → x = 0 := by
      intro x hx hxy
      refine hnd x (hle hx) fun y hy => ?_
      have h := hxy _ (hproj y hy)
      rw [map_sub, map_smul, hwu x hx, smul_zero, sub_zero] at h
      exact h
    let f' : U' →ₗ[K] V := g₁.symm.toLinearMap ∘ₗ f ∘ₗ Submodule.inclusion hle
    have hf'x : ∀ x : U', f' x = g₁.symm (f (Submodule.inclusion hle x)) := fun x => rfl
    have hf' : ∀ x y : U', B (f' x) (f' y) = B x y := by
      intro x y
      rw [hf'x, hf'x, hsym₂, hf]
      rfl
    obtain ⟨g₂, hg₂, hg₂f, hg₂fix⟩ := ih _ hlt U' rfl hnd' f' hf'
    have hg₂u : g₂ u = u := by
      refine hg₂fix u (fun w => hwu w w.2) fun w => ?_
      rw [hf'x, hsym, hg₁u, hf]
      exact hwu w w.2
    refine ⟨g₂.trans g₁, fun x y => ?_, fun x => ?_, fun z hz₁ hz₂ => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      rw [hg₁, hg₂]
    · obtain ⟨c, hc⟩ : ∃ c : K, c = B u x / B u u := ⟨_, rfl⟩
      have hmem : (x : V) - c • u ∈ U' := hc ▸ hproj x x.2
      let x' : U' := ⟨_, hmem⟩
      have hxv : (x : V) = c • u + (x' : V) := by simp [x']
      have hxU : x = c • (⟨u, hu⟩ : U) + Submodule.inclusion hle x' := Subtype.ext (by simp [x'])
      calc (g₂.trans g₁) (x : V) = g₁ (g₂ (c • u + (x' : V))) := by rw [← hxv]; rfl
        _ = c • g₁ u + g₁ (f' x') := by
            rw [map_add, map_smul, hg₂u, hg₂f x', map_add, map_smul]
        _ = f x := by
            rw [hg₁u, hf'x, LinearEquiv.apply_symm_apply]
            conv_rhs => rw [hxU]
            rw [map_add, map_smul]
    · have hg₁z : g₁ z = z := hg₁fix z (hz₁ ⟨u, hu⟩) (hz₂ ⟨u, hu⟩)
      have hg₂z : g₂ z = z := by
        refine hg₂fix z (fun w => hz₁ (Submodule.inclusion hle w)) fun w => ?_
        rw [hf'x, hsym, hg₁z]
        exact hz₂ _
      show g₁ (g₂ z) = z
      rw [hg₂z, hg₁z]
  · push Not at hex
    refine ⟨LinearEquiv.refl K V, fun x y => rfl, fun x => ?_, fun z _ _ => rfl⟩
    have hx0 : x = 0 := Subtype.ext (hnd x x.2 (hex x x.2))
    subst hx0
    simp

end PI.Witt
