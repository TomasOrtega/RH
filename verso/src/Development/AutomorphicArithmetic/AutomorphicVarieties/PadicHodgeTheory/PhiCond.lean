import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateFin
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Introduce `hP v l _ _ H hH`. Use `letI : Algebra ℤ_[l] (ZMod l) := (PadicInt.toZMod (p := l)).toAlgebra`. Use `letI : TopologicalSpace (ZMod l) := ⊥`. Use `haveI : DiscreteTopology (ZMod l) := ⟨rfl⟩`. Set `ρ : Representation (ZMod l) H (ZMod l)` to `1`.

Establish `hρ : ContAction ρ` using `continuous_snd`. Establish `hfin` using `(tateFin hP (v := v) (l := l) H.subtype hH.isOpenEmbedding_subtypeVal (ZMod l) (ZMod l) ρ hρ).1`. Use `haveI : Finite (H1 ρ) := Module.finite_of_finite (ZMod l)`. Establish `hc : ∀ f : {f : H →* Multiplicative (ZMod l) // IsOpen (f.ker : Set H)}, (fun g => Multiplicative.toAdd (f.1 g)) ∈ Z1 ρ`. Introduce `f`.

Use `⟨?_, fun g h => ?_⟩` and prove the remaining obligations. Use `IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)` and prove the remaining obligations. Use `⟨(fun x => g⁻¹ * x) ⁻¹' (f.1.ker : Set H), f.2.preimage (by fun_prop), by simp, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: f.1 (g⁻¹ * x) = 1` using `hx`. Rewrite `this` using `[map_mul, map_inv, inv_mul_eq_one]`.

Rewrite using `[this]`. Simplify using `[ρ]`. Use `Finite.of_injective (fun f => (Submodule.Quotient.mk ⟨_, hc f⟩ : H1 ρ)) fun f f' hff => ?_` and prove the remaining obligations. Establish `h1` using `(Submodule.Quotient.eq ((ReciprocityTheory.Gal.B1 ρ).comap (Z1 ρ).subtype)).1 hff`. Take `⟨m, hm⟩` from `(mem_coboundaries1 ρ _).1 (Submodule.mem_comap.1 h1)`.

Use `Subtype.ext (MonoidHom.ext fun g => Multiplicative.toAdd.injective ?_)` and prove the remaining obligations. Use `hm g` as an intermediate fact. Simplify `this` using `[ρ, sub_eq_zero]`.
-/
theorem UpperTheory.V.Loc.phiCond :
    LocalPublishedTheorems → ∀ (v l : ℕ) [Fact v.Prime] [Fact l.Prime] (H : Subgroup (GQ v)), IsOpen (H : Set (GQ v)) → Finite {f : H →* Multiplicative (ZMod l) // IsOpen (f.ker : Set H)} := by
  intro hP v l _ _ H hH
  letI : Algebra ℤ_[l] (ZMod l) := (PadicInt.toZMod (p := l)).toAlgebra
  letI : TopologicalSpace (ZMod l) := ⊥
  haveI : DiscreteTopology (ZMod l) := ⟨rfl⟩
  let ρ : Representation (ZMod l) H (ZMod l) := 1
  have hρ : ContAction ρ := continuous_snd
  have hfin := (tateFin hP (v := v) (l := l) H.subtype hH.isOpenEmbedding_subtypeVal (ZMod l) (ZMod l) ρ hρ).1
  haveI : Finite (H1 ρ) := Module.finite_of_finite (ZMod l)
  have hc : ∀ f : {f : H →* Multiplicative (ZMod l) // IsOpen (f.ker : Set H)},
      (fun g => Multiplicative.toAdd (f.1 g)) ∈ Z1 ρ := by
    intro f
    refine ⟨?_, fun g h => ?_⟩
    · refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g => ?_)
      refine ⟨(fun x => g⁻¹ * x) ⁻¹' (f.1.ker : Set H), f.2.preimage (by fun_prop), by simp, fun x hx => ?_⟩
      have : f.1 (g⁻¹ * x) = 1 := hx
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      rw [this]
    · simp [ρ]
  refine Finite.of_injective (fun f => (Submodule.Quotient.mk ⟨_, hc f⟩ : H1 ρ)) fun f f' hff => ?_
  have h1 := (Submodule.Quotient.eq ((ReciprocityTheory.Gal.B1 ρ).comap (Z1 ρ).subtype)).1 hff
  obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 (Submodule.mem_comap.1 h1)
  refine Subtype.ext (MonoidHom.ext fun g => Multiplicative.toAdd.injective ?_)
  have := hm g
  simpa [ρ, sub_eq_zero] using this
