import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `R _ G _ _ g n M B ψ e b hb`. Establish `h0 : e.ex b 0 = 1`. Establish `h` using `e.add b hb 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `(left_eq_mul.mp h)`.

Set `A : AddSubgroup (Fin g → ℂ)` to `{ carrier := e.per b zero_mem' := h0 add_mem' := by`. Introduce `z w hz hw`. Establish `hz' : e.ex b z = 1` using `hz`. Establish `hw' : e.ex b w = 1` using `hw`. Use `show e.ex b (z + w) = 1`.

Rewrite using `[e.add b hb, hz', hw', _root_.one_mul]`. Use the proof step `neg_mem' := by`. Introduce `z hz`. Establish `hz' : e.ex b z = 1` using `hz`. Use `show e.ex b (-z) = 1`.

Establish `h` using `e.add b hb z (-z)`. Rewrite `h` using `[add_neg_cancel, h0, hz', _root_.one_mul]`. Conclude with `h.symm }`. Set `Γ₀ : Submodule ℤ (Fin g → ℂ)` to `AddSubgroup.toIntSubmodule A`. Take `⟨V, N, f, L, -, -, hL, -⟩` from `e.log b hb`.

Establish `hslice : ∀ᶠ z : Fin g → ℂ in 𝓝 0, L (b, fun j => valAt' (e.ex b z).left V (f j)) = z`. Establish `hc : Tendsto (fun z : Fin g → ℂ => (b, z)) (𝓝 0) (𝓝 (b, 0))` using `(Continuous.prodMk_right b).tendsto 0`. Conclude with `hc.eventually hL`. Establish `hiso : ∀ᶠ z : Fin g → ℂ in 𝓝 0, z ∈ e.per b → z = 0`. Establish `h00` using `hslice.self_of_nhds`.

Use `filter_upwards [hslice] with z hz hper`. Establish `hz' : e.ex b z = e.ex b 0`. Establish `: e.ex b z = 1` using `hper`. Rewrite using `[this, h0]`. Rewrite `hz` using `[hz']`.

Conclude with `hz.symm.trans h00`. Establish `hdisc : DiscreteTopology Γ₀`. Take `⟨U, hU, hUo, h0U⟩` from `_root_.eventually_nhds_iff.mp hiso`. Apply `discreteTopology_of_isOpen_singleton_zero` to reduce the goal to its premises. Establish `: ({0} : Set Γ₀) = Subtype.val ⁻¹' U`.

Use extensionality with `⟨z, hz⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: z = 0` using `congrArg Subtype.val h`. Simplify `h0U` using `[this]`.

Introduce `h`. Establish `: z = 0` using `hU z h hz`. Conclude with `Subtype.ext this`. Rewrite using `[this]`. Conclude with `hUo.preimage continuous_subtype_val`.

Use `⟨Γ₀, rfl, hdisc, ?_, ?_⟩` and prove the remaining obligations. Conclude with `instModuleFinite_of_discrete_submodule Γ₀`. Conclude with `instModuleFree_of_discrete_submodule Γ₀`.
-/
theorem FamExp.per_discrete : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), ∀ b ∈ B, ∃ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b ∧ DiscreteTopology Γ₀ ∧ Module.Finite ℤ Γ₀ ∧ Module.Free ℤ Γ₀ := by
  intro R _ G _ _ g n M B ψ e b hb
  have h0 : e.ex b 0 = 1 := by
    have h := e.add b hb 0 0
    rw [add_zero] at h
    exact (left_eq_mul.mp h)
  let A : AddSubgroup (Fin g → ℂ) :=
    { carrier := e.per b
      zero_mem' := h0
      add_mem' := by
        intro z w hz hw
        have hz' : e.ex b z = 1 := hz
        have hw' : e.ex b w = 1 := hw
        show e.ex b (z + w) = 1
        rw [e.add b hb, hz', hw', _root_.one_mul]
      neg_mem' := by
        intro z hz
        have hz' : e.ex b z = 1 := hz
        show e.ex b (-z) = 1
        have h := e.add b hb z (-z)
        rw [add_neg_cancel, h0, hz', _root_.one_mul] at h
        exact h.symm }
  let Γ₀ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule A
  obtain ⟨V, N, f, L, -, -, hL, -⟩ := e.log b hb
  have hslice : ∀ᶠ z : Fin g → ℂ in 𝓝 0,
      L (b, fun j => valAt' (e.ex b z).left V (f j)) = z := by
    have hc : Tendsto (fun z : Fin g → ℂ => (b, z)) (𝓝 0) (𝓝 (b, 0)) :=
      (Continuous.prodMk_right b).tendsto 0
    exact hc.eventually hL
  have hiso : ∀ᶠ z : Fin g → ℂ in 𝓝 0, z ∈ e.per b → z = 0 := by
    have h00 := hslice.self_of_nhds
    filter_upwards [hslice] with z hz hper
    have hz' : e.ex b z = e.ex b 0 := by
      have : e.ex b z = 1 := hper
      rw [this, h0]
    rw [hz'] at hz
    exact hz.symm.trans h00
  have hdisc : DiscreteTopology Γ₀ := by
    obtain ⟨U, hU, hUo, h0U⟩ := _root_.eventually_nhds_iff.mp hiso
    apply discreteTopology_of_isOpen_singleton_zero
    have : ({0} : Set Γ₀) = Subtype.val ⁻¹' U := by
      ext ⟨z, hz⟩
      constructor
      · intro h
        have : z = 0 := congrArg Subtype.val h
        simpa [this] using h0U
      · intro h
        have : z = 0 := hU z h hz
        exact Subtype.ext this
    rw [this]
    exact hUo.preimage continuous_subtype_val
  refine ⟨Γ₀, rfl, hdisc, ?_, ?_⟩
  · exact instModuleFinite_of_discrete_submodule Γ₀
  · exact instModuleFree_of_discrete_submodule Γ₀

end GlobalTheory.CompanionTheory.Ar.Flat
