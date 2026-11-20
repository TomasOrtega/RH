import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ n L hL x hx`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx (funext h)`.

Set `f : E →ₗ[𝓞 E] (Fin n → E)` to `(LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)`. Set `I : Submodule (𝓞 E) E` to `L.comap f`. Establish `hI : ∀ s, s ∈ I ↔ s • x ∈ L` using `fun s => by simp [I, f]`. Set `π : (Fin n → E) →ₗ[𝓞 E] E` to `LinearMap.proj (R := 𝓞 E) (φ := fun _ => E) i`. Establish `hfg : L.FG` using `Submodule.IsLattice.fg (A := E) (M := L)`.

Establish `hJ : IsFractional (𝓞 E)⁰ (L.map π)` using `FractionalIdeal.isFractional_of_fg (hfg.map π)`. Set `J : FractionalIdeal (𝓞 E)⁰ E` to `⟨L.map π, hJ⟩`. Establish `hle : I ≤ ((FractionalIdeal.spanSingleton (𝓞 E)⁰ (x i)⁻¹ * J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)`. Introduce `s hs`. Rewrite using `[FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]`.

Use `⟨s * x i, ?_, ?_⟩` and prove the remaining obligations. Use `show s * x i ∈ L.map π`. Conclude with `⟨s • x, (hI s).1 hs, by simp [π]⟩`. Clear the denominators using the available nonvanishing facts. Conclude with `⟨⟨I, FractionalIdeal.isFractional_of_le hle⟩, fun s => hI s⟩`.
-/
theorem exists_fractionalIdeal_smul_mem_lattice :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  intro E _ _ n L hL x hx
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let f : E →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)
  let I : Submodule (𝓞 E) E := L.comap f
  have hI : ∀ s, s ∈ I ↔ s • x ∈ L := fun s => by simp [I, f]
  let π : (Fin n → E) →ₗ[𝓞 E] E := LinearMap.proj (R := 𝓞 E) (φ := fun _ => E) i
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (M := L)
  have hJ : IsFractional (𝓞 E)⁰ (L.map π) := FractionalIdeal.isFractional_of_fg (hfg.map π)
  let J : FractionalIdeal (𝓞 E)⁰ E := ⟨L.map π, hJ⟩
  have hle : I ≤ ((FractionalIdeal.spanSingleton (𝓞 E)⁰ (x i)⁻¹ * J :
      FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
    intro s hs
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]
    refine ⟨s * x i, ?_, ?_⟩
    · show s * x i ∈ L.map π
      exact ⟨s • x, (hI s).1 hs, by simp [π]⟩
    · field_simp
  exact ⟨⟨I, FractionalIdeal.isFractional_of_le hle⟩, fun s => hI s⟩

end GlobalTheory
