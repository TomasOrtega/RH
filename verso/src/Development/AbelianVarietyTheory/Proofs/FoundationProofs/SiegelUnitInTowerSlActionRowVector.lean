import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelSL

/- English proof (translation)
Use `show IsOpen {z : ℂ | 0 < z.im}`. Conclude with `isOpen_lt continuous_const Complex.continuous_im`.
-/
theorem isOpen_Hs : IsOpen Hs := by
  show IsOpen {z : ℂ | 0 < z.im}
  exact isOpen_lt continuous_const Complex.continuous_im

/- English proof (translation)
Rewrite using `[Filter.neBot_iff]`. Introduce `h`. Establish `hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs` using `h ▸ Filter.mem_bot`. Rewrite `hmem` using `[mem_codiscreteWithin]`. Establish `hI : Complex.I ∈ Hs` using `by show (0 : ℝ) < Complex.I.im`.

Simplify using the standard rewrite rules. Establish `h1` using `hmem Complex.I hI`. Rewrite `h1` using `[Set.sdiff_empty, Filter.disjoint_principal_right]`. Establish `h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ` using `mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)`. Establish `h3` using `Filter.inter_mem h1 h2`.

Rewrite `h3` using `[Set.compl_inter_self]`. Simplify using `using Filter.nonempty_of_mem h3`.
-/
theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := h ▸ Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by
    show (0 : ℝ) < Complex.I.im
    simp
  have h1 := hmem Complex.I hI
  rw [Set.sdiff_empty, Filter.disjoint_principal_right] at h1
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)
  have h3 := Filter.inter_mem h1 h2
  rw [Set.compl_inter_self] at h3
  simpa using Filter.nonempty_of_mem h3

/- English proof (translation)
Apply `Filter.Germ.coe_eq.2` to reduce the goal to its premises. Use `filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz`. Conclude with `h z hz`.
-/
theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) := by
  apply Filter.Germ.coe_eq.2
  filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
  exact h z hz

/- English proof (translation)
Simplify using `[sgC, UpperHalfPlane.ofComplex_apply]`.
-/
theorem sgC_coe (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : sgC c x τ = sg c x τ := by
  simp [sgC, UpperHalfPlane.ofComplex_apply]

/- English proof (translation)
Rewrite using `[UpperHalfPlane.coe_specialLinearGroup_apply]`. Simplify using `[mob, ent, ofSL]`.
-/
theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

/- English proof (translation)
Use `neBot_Hs` as an intermediate fact. Conclude with `T.an.injective`.
-/
theorem an_injective {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) :
    Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

/- English proof (translation)
Establish `hex : ∃ g : T.K, T.an g = ((sgC c x : ℂ → ℂ) : Mero)` using `⟨f, hf⟩`. Apply `an_injective T` to reduce the goal to its premises. Rewrite using `[siegel, dif_pos hex, hex.choose_spec, hf]`.
-/
theorem siegel_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) {c : ℕ} {x : Fin 2 → ℚ} {f : T.K}
    (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) : siegel T c x = f := by
  have hex : ∃ g : T.K, T.an g = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  apply an_injective T
  rw [siegel, dif_pos hex, hex.choose_spec, hf]

/- English proof (translation)
Introduce `Ω _ _ _ ε T c x γ hx`. Use `symm`. Apply `siegel_eq` to reduce the goal to its premises. Rewrite using `[T.an_sl _ _ _ (GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hx)]`. Apply `germ_eq_of_eqOn` to reduce the goal to its premises.

Introduce `z hz`. Establish `hτ : ((⟨z, hz⟩ : ℍ) : ℂ) = z` using `rfl`. Rewrite using `[← hτ, mob_ofSL, sgC_coe, sgC_coe, GlobalTheory.T.siegel_function_transformation c x γ _ hx]`.
-/
theorem sl_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ)
    (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  intro Ω _ _ _ ε T c x γ hx
  symm
  apply siegel_eq
  rw [T.an_sl _ _ _ (GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hx)]
  apply germ_eq_of_eqOn
  intro z hz
  have hτ : ((⟨z, hz⟩ : ℍ) : ℂ) = z := rfl
  rw [← hτ, mob_ofSL, sgC_coe, sgC_coe, GlobalTheory.T.siegel_function_transformation c x γ _ hx]

end GlobalTheory.KZ.SiegelSL

/- English proof (translation)
The claim follows from `GlobalTheory.KZ.SiegelSL.sl_siegel`.
-/
example : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := GlobalTheory.KZ.SiegelSL.sl_siegel
