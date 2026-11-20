import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HBBump

/- English proof (translation)
Introduce `G Z _ _ _ _ _ H ρ B hBo hBc z hz`. Establish `hwell : ∀ (h h' : H) (β β' : G), β ∈ B → β' ∈ B → (h : G) * β = (h' : G) * β' → ρ h z = ρ h' z`. Introduce `h h' β β' hβ hβ' e`. Establish `ha : ((h'⁻¹ * h : H) : G) ∈ B`. Establish `: ((h'⁻¹ * h : H) : G) = β' * β⁻¹`.

Use `push_cast`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]`. Use `group`. Rewrite using `[this]`. Conclude with `B.mul_mem hβ' (B.inv_mem hβ)`.

Establish `h1` using `hz _ ha`. Establish `h2 : h = h' * (h'⁻¹ * h)` using `by group`. Rewrite using `[h2, map_mul, Module.End.mul_apply, h1]`. Set `P : G → Prop` to `fun p => ∃ h : H, ∃ β ∈ B, p = (h : G) * β`. Set `f : G → Z` to `fun p => if hp : P p then ρ hp.choose z else 0`.

Establish `hval : ∀ (h : H) (β : G), β ∈ B → f ((h : G) * β) = ρ h z`. Introduce `h β hβ`. Establish `hp : P ((h : G) * β)` using `⟨h, β, hβ, rfl⟩`. Take `⟨β', hβ', e⟩` from `hp.choose_spec`. Simplify using `only [f, dif_pos hp]`.

Conclude with `hwell _ _ _ _ hβ' hβ e.symm`. Establish `hzero : ∀ p, ¬ P p → f p = 0` using `fun p hp => by simp only [f, dif_neg hp]`. Establish `hleft : ∀ (h : H) (g : G), f ((h : G) * g) = ρ h (f g)`. Introduce `h g`. Distinguish the cases in `hg : P g`.

Take `⟨h', β, hβ, rfl⟩` from `hg`. Establish `: (h : G) * ((h' : G) * β) = ((h * h' : H) : G) * β` using `by push_cast; group`. Rewrite using `[this, hval _ _ hβ, hval _ _ hβ, map_mul, Module.End.mul_apply]`. Establish `hn : ¬ P ((h : G) * g)`. Introduce and unpack `⟨h', β, hβ, e⟩`.

Use `hg ⟨h⁻¹ * h', β, hβ, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[mul_assoc, ← e]`. Use `group`. Rewrite using `[hzero _ hn, hzero _ hg, map_zero]`.

Establish `hright : ∀ (p : G), ∀ x ∈ B, f (p * x) = f p`. Introduce `p x hx`. Distinguish the cases in `hp : P p`. Take `⟨h, β, hβ, rfl⟩` from `hp`. Rewrite using `[mul_assoc, hval _ _ (B.mul_mem hβ hx), hval _ _ hβ]`.

Establish `hn : ¬ P (p * x)`. Introduce and unpack `⟨h, β, hβ, e⟩`. Use `hp ⟨h, β * x⁻¹, B.mul_mem hβ (B.inv_mem hx), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← e]`. Use `group`.

Rewrite using `[hzero _ hn, hzero _ hp]`. Set `F : indSpace H ρ` to `⟨f, hleft⟩`. Establish `hsm : F ∈ smoothPart (ind H ρ)`. Set `T : Subgroup G` to `{ carrier := {g | ind H ρ g F = F} mul_mem' := by`. Introduce `a b ha hb`.

Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`.

Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Establish `hBT : (B : Set G) ⊆ T`.

Introduce `x hx`. Use `show ind H ρ x F = F`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `p`. Conclude with `hright p x hx`.

Conclude with `T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hBo.mem_nhds B.one_mem) hBT)`. Use `⟨⟨⟨F, hsm⟩, ⟨(B : Set G), hBc, ?_⟩⟩, hval, hzero⟩` and prove the remaining obligations. Introduce `g hg`. Assume the negation of the conclusion as `hc`. Use `hg (hzero g ?_)` and prove the remaining obligations.

Introduce and unpack `⟨h, β, hβ, e⟩`. Conclude with `hc ⟨h, h.2, β, hβ, e⟩`.
-/
theorem exists_bump : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (B : Subgroup G),
    IsOpen (B : Set G) → IsCompact (B : Set G) → ∀ z : Z, (∀ h : H, (h : G) ∈ B → ρ h z = z) →
    ∃ b : cIndSpace H ρ, (∀ (h : H) (β : G), β ∈ B → b.1.1.1 ((h : G) * β) = ρ h z) ∧
      ∀ p : G, (¬ ∃ h : H, ∃ β ∈ B, p = (h : G) * β) → b.1.1.1 p = 0 := by
  intro G Z _ _ _ _ _ H ρ B hBo hBc z hz
  classical

  have hwell : ∀ (h h' : H) (β β' : G), β ∈ B → β' ∈ B → (h : G) * β = (h' : G) * β' →
      ρ h z = ρ h' z := by
    intro h h' β β' hβ hβ' e
    have ha : ((h'⁻¹ * h : H) : G) ∈ B := by
      have : ((h'⁻¹ * h : H) : G) = β' * β⁻¹ := by
        push_cast
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
        group
      rw [this]
      exact B.mul_mem hβ' (B.inv_mem hβ)
    have h1 := hz _ ha
    have h2 : h = h' * (h'⁻¹ * h) := by group
    rw [h2, map_mul, Module.End.mul_apply, h1]
  let P : G → Prop := fun p => ∃ h : H, ∃ β ∈ B, p = (h : G) * β
  let f : G → Z := fun p => if hp : P p then ρ hp.choose z else 0
  have hval : ∀ (h : H) (β : G), β ∈ B → f ((h : G) * β) = ρ h z := by
    intro h β hβ
    have hp : P ((h : G) * β) := ⟨h, β, hβ, rfl⟩
    obtain ⟨β', hβ', e⟩ := hp.choose_spec
    simp only [f, dif_pos hp]
    exact hwell _ _ _ _ hβ' hβ e.symm
  have hzero : ∀ p, ¬ P p → f p = 0 := fun p hp => by simp only [f, dif_neg hp]
  have hleft : ∀ (h : H) (g : G), f ((h : G) * g) = ρ h (f g) := by
    intro h g
    by_cases hg : P g
    · obtain ⟨h', β, hβ, rfl⟩ := hg
      have : (h : G) * ((h' : G) * β) = ((h * h' : H) : G) * β := by push_cast; group
      rw [this, hval _ _ hβ, hval _ _ hβ, map_mul, Module.End.mul_apply]
    · have hn : ¬ P ((h : G) * g) := by
        rintro ⟨h', β, hβ, e⟩
        refine hg ⟨h⁻¹ * h', β, hβ, ?_⟩
        push_cast
        rw [mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hg, map_zero]
  have hright : ∀ (p : G), ∀ x ∈ B, f (p * x) = f p := by
    intro p x hx
    by_cases hp : P p
    · obtain ⟨h, β, hβ, rfl⟩ := hp
      rw [mul_assoc, hval _ _ (B.mul_mem hβ hx), hval _ _ hβ]
    · have hn : ¬ P (p * x) := by
        rintro ⟨h, β, hβ, e⟩
        refine hp ⟨h, β * x⁻¹, B.mul_mem hβ (B.inv_mem hx), ?_⟩
        rw [← mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hp]
  let F : indSpace H ρ := ⟨f, hleft⟩
  have hsm : F ∈ smoothPart (ind H ρ) := by
    let T : Subgroup G :=
      { carrier := {g | ind H ρ g F = F}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hBT : (B : Set G) ⊆ T := by
      intro x hx
      show ind H ρ x F = F
      apply Subtype.ext
      funext p
      exact hright p x hx
    exact T.isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset (hBo.mem_nhds B.one_mem) hBT)
  refine ⟨⟨⟨F, hsm⟩, ⟨(B : Set G), hBc, ?_⟩⟩, hval, hzero⟩
  intro g hg
  by_contra hc
  refine hg (hzero g ?_)
  rintro ⟨h, β, hβ, e⟩
  exact hc ⟨h, h.2, β, hβ, e⟩

end GlobalTheory.CompanionTheory.HBBump
