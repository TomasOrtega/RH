import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ (s γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ c c' : C, γ * s * c = γ' * s * c' → lam c = lam c'`. Introduce `s γ γ' hγ hγ' c c' e`. Establish `e2 : (γ'⁻¹ * γ) * s = s * ((c' * c⁻¹ : C) : G)`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.

Use `h s _ (Γ.mul_mem (Γ.inv_mem hγ') hγ) _ e2` as an intermediate fact. Rewrite `this` using `[map_mul, map_inv, mul_inv_eq_one]`. Conclude with `this.symm`. Set `S : Setoid G` to `{ r := fun a b => ∃ γ ∈ Γ, ∃ c : C, b = γ * a * c iseqv := by`. Use `⟨fun a => ⟨1, Γ.one_mem, 1, by simp⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `a b ⟨γ, hγ, c, rfl⟩`. Conclude with `⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by push_cast; group⟩`. Introduce and unpack `a b d ⟨γ, hγ, c, rfl⟩ ⟨γ', hγ', c', rfl⟩`. Conclude with `⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by push_cast; group⟩ }`. Set `rep : G → G` to `fun g => (Quotient.mk S g).out`.

Establish `hrep : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c`. Introduce `g`. Take `⟨γ, hγ, c, e⟩` from `Quotient.mk_out (s := S) g`. Conclude with `⟨c, γ, hγ, e⟩`. Establish `rep_eq : ∀ a b, S.r a b → rep a = rep b`.

Introduce `a b hab`. Simplify using `only [rep]`. Rewrite using `[Quotient.sound hab]`. Set `cf : G → C` to `fun g => Classical.choose (hrep g)`. Establish `hcf : ∀ g, ∃ γ ∈ Γ, g = γ * rep g * cf g` using `fun g => Classical.choose_spec (hrep g)`.

Use `⟨fun g => Multiplicative.toAdd (lam (cf g)), ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ g`. Simplify using `only`. Use `congr 1`. Establish `hr : rep (γ * g) = rep g` using `(rep_eq _ _ ⟨γ, hγ, 1, by simp⟩).symm`.

Take `⟨γ1, hγ1, e1⟩` from `hcf (γ * g)`. Take `⟨γ2, hγ2, e2⟩` from `hcf g`. Rewrite `e1` using `[hr]`. Apply `key (rep g) (γ⁻¹ * γ1) γ2 (Γ.mul_mem (Γ.inv_mem hγ) hγ1) hγ2` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Introduce `g c`. Simplify using `only`. Rewrite using `[← toAdd_mul]`. Use `congr 1`. Establish `hr : rep (g * c) = rep g` using `(rep_eq _ _ ⟨1, Γ.one_mem, c, by simp⟩).symm`.

Take `⟨γ1, hγ1, e1⟩` from `hcf (g * c)`. Take `⟨γ2, hγ2, e2⟩` from `hcf g`. Rewrite `e1` using `[hr]`. Use `key (rep g) γ1 γ2 hγ1 hγ2 (cf (g * c) * c⁻¹) (cf g) (by` as an intermediate fact. Use `push_cast`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `this` using `[map_mul, map_inv]`. Rewrite using `[← this]`. Use `group`.
-/
theorem exists_leftInv_rightEquivariant (G A : Type) [Group G] [AddCommGroup A] (Γ C : Subgroup G)
    (lam : C →* Multiplicative A)
    (h : ∀ g : G, ∀ γ ∈ Γ, ∀ c : C, γ * g = g * c → lam c = 1) :
    ∃ ℓ : G → A, (∀ γ ∈ Γ, ∀ g, ℓ (γ * g) = ℓ g) ∧
      ∀ g (c : C), ℓ (g * c) = ℓ g + Multiplicative.toAdd (lam c) := by

  have key : ∀ (s γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ c c' : C,
      γ * s * c = γ' * s * c' → lam c = lam c' := by
    intro s γ γ' hγ hγ' c c' e
    have e2 : (γ'⁻¹ * γ) * s = s * ((c' * c⁻¹ : C) : G) := by
      push_cast
      calc γ'⁻¹ * γ * s = γ'⁻¹ * (γ * s * c) * (c : G)⁻¹ := by group
        _ = γ'⁻¹ * (γ' * s * c') * (c : G)⁻¹ := by rw [e]
        _ = s * ((c' : G) * (c : G)⁻¹) := by group
    have := h s _ (Γ.mul_mem (Γ.inv_mem hγ') hγ) _ e2
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this.symm
  let S : Setoid G :=
    { r := fun a b => ∃ γ ∈ Γ, ∃ c : C, b = γ * a * c
      iseqv := by
        refine ⟨fun a => ⟨1, Γ.one_mem, 1, by simp⟩, ?_, ?_⟩
        · rintro a b ⟨γ, hγ, c, rfl⟩
          exact ⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by push_cast; group⟩
        · rintro a b d ⟨γ, hγ, c, rfl⟩ ⟨γ', hγ', c', rfl⟩
          exact ⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by push_cast; group⟩ }
  let rep : G → G := fun g => (Quotient.mk S g).out
  have hrep : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c := by
    intro g
    obtain ⟨γ, hγ, c, e⟩ := Quotient.mk_out (s := S) g
    exact ⟨c, γ, hγ, e⟩
  have rep_eq : ∀ a b, S.r a b → rep a = rep b := by
    intro a b hab
    simp only [rep]
    rw [Quotient.sound hab]
  let cf : G → C := fun g => Classical.choose (hrep g)
  have hcf : ∀ g, ∃ γ ∈ Γ, g = γ * rep g * cf g := fun g => Classical.choose_spec (hrep g)
  refine ⟨fun g => Multiplicative.toAdd (lam (cf g)), ?_, ?_⟩
  · intro γ hγ g
    simp only
    congr 1
    have hr : rep (γ * g) = rep g := (rep_eq _ _ ⟨γ, hγ, 1, by simp⟩).symm
    obtain ⟨γ1, hγ1, e1⟩ := hcf (γ * g)
    obtain ⟨γ2, hγ2, e2⟩ := hcf g
    rw [hr] at e1
    apply key (rep g) (γ⁻¹ * γ1) γ2 (Γ.mul_mem (Γ.inv_mem hγ) hγ1) hγ2
    calc γ⁻¹ * γ1 * rep g * (cf (γ * g) : G) = γ⁻¹ * (γ1 * rep g * cf (γ * g)) := by group
      _ = g := by rw [← e1]; group
      _ = γ2 * rep g * cf g := e2
  · intro g c
    simp only
    rw [← toAdd_mul]
    congr 1
    have hr : rep (g * c) = rep g := (rep_eq _ _ ⟨1, Γ.one_mem, c, by simp⟩).symm
    obtain ⟨γ1, hγ1, e1⟩ := hcf (g * c)
    obtain ⟨γ2, hγ2, e2⟩ := hcf g
    rw [hr] at e1
    have := key (rep g) γ1 γ2 hγ1 hγ2 (cf (g * c) * c⁻¹) (cf g) (by
      push_cast
      calc γ1 * rep g * ((cf (g * c) : G) * (c : G)⁻¹) = (γ1 * rep g * cf (g * c)) * (c : G)⁻¹ := by group
        _ = g := by rw [← e1]; group
        _ = γ2 * rep g * cf g := e2)
    rw [map_mul, map_inv] at this
    rw [← this]; group

/- English proof (translation)
The claim follows from `exists_leftInv_rightEquivariant`.
-/
example : ∀ (G A : Type) [Group G] [AddCommGroup A] (Γ C : Subgroup G) (lam : C →* Multiplicative A), (∀ g : G, ∀ γ ∈ Γ, ∀ c : C, γ * g = g * c → lam c = 1) → ∃ ℓ : G → A, (∀ γ ∈ Γ, ∀ g, ℓ (γ * g) = ℓ g) ∧ ∀ g (c : C), ℓ (g * c) = ℓ g + Multiplicative.toAdd (lam c) := exists_leftInv_rightEquivariant

end GlobalTheory
