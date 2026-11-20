import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ n L hL x hx`. Set `f : E →ₗ[𝓞 E] (Fin n → E)` to `(LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)`. Establish `hf : Function.Injective f`. Introduce `a b h`. Establish `h' : a • x = b • x` using `h`.

Conclude with `smul_left_injective E hx h'`. Establish `hLfg : L.FG` using `hL.fg`. Establish `hmapfg : ((L.comap f).map f).FG` using `Submodule.FG.of_le hLfg (Submodule.map_comap_le f L)`. Establish `hS : (L.comap f).FG` using `Submodule.fg_of_fg_map_injective f hf hmapfg`. Conclude with `⟨⟨L.comap f, FractionalIdeal.isFractional_of_fg hS⟩, fun s => Iff.rfl⟩`.
-/
theorem latticeLine_fractionalIdeal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  intro E _ _ n L hL x hx
  let f : E →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)
  have hf : Function.Injective f := by
    intro a b h
    have h' : a • x = b • x := h
    exact smul_left_injective E hx h'
  have hLfg : L.FG := hL.fg
  have hmapfg : ((L.comap f).map f).FG :=
    Submodule.FG.of_le hLfg (Submodule.map_comap_le f L)
  have hS : (L.comap f).FG := Submodule.fg_of_fg_map_injective f hf hmapfg
  exact ⟨⟨L.comap f, FractionalIdeal.isFractional_of_fg hS⟩, fun s => Iff.rfl⟩

end GlobalTheory
