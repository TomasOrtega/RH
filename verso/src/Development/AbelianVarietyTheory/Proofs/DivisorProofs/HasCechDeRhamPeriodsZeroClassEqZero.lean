import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicPrimitiveOfCechDeRhamPeriodsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

/- English proof (translation)
Introduce `A _ g L u q hq`. Take `⟨hopen, -, hadd, -, hinf, -, -, hbasis, -, -, -, htop⟩` from `GlobalTheory.T.uniformisation_preimage_value_rules A g L u`. Take `⟨h, ⟨hdiff, hres0, hder0⟩, hper⟩` from `GlobalTheory.T.exists_holomorphic_primitive_of_cechDeRham_periods A g L u 0 q hq 0 (map_zero _)`. Establish `hres : ∀ (U V : A.left.affineOpens), V.1 ≤ U.1 → ∀ z ∈ pre u.ex V.1, h V z = h U z`. Introduce `U V hVU z hz`.

Use `hres0 U V (homOfLE hVU).op z hz` as an intermediate fact. Rewrite using `[this]`. Express the relevant statement in the definitionally equal form `h U z + valAt' _ _ (0 : Γ(A.left, V.1)) = h U z`. Unfold `valAt' valAt`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hder : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, fderiv ℂ (h U) z = 0`. Introduce `U z hz`. Rewrite using `[hder0 U z hz]`. Express the relevant statement in the definitionally equal form `evForm u.ex U.1 z 0 = 0`. Simplify using the standard rewrite rules.

Establish `hex : ∀ z, ∃ U : A.left.affineOpens, z ∈ pre u.ex U.1` using `fun z ↦ by`. Take `⟨W, -, hW⟩` from `hbasis ⊤ z (htop z)`. Conclude with `⟨W, hW⟩`. Use `choose Uz hUz using hex`. Set `G : (Fin g → ℂ) → ℂ` to `fun z ↦ h (Uz z) z`.

Establish `hG : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, G z = h U z`. Introduce `U z hz`. Take `⟨W, hWle, hW⟩` from `hbasis (U.1 ⊓ (Uz z).1) z (by rw [hinf]; exact ⟨hz, hUz z⟩)`. Establish `h1` using `hres U W (hWle.trans inf_le_left) z hW`. Establish `h2` using `hres (Uz z) W (hWle.trans inf_le_right) z hW`.

Simplify using `only [G]`. Rewrite using `[← h1, ← h2]`. Establish `hloc : ∀ z, G =ᶠ[nhds z] h (Uz z)` using `fun z ↦ by filter_upwards [(hopen _).mem_nhds (hUz z)] with w hw`. Conclude with `hG _ w hw`. Establish `hGd : Differentiable ℂ G` using `fun z ↦ (((hdiff (Uz z)).differentiableAt ((hopen _).mem_nhds (hUz z)))).congr_of_eventuallyEq (hloc z)`.

Establish `hGf : ∀ z, fderiv ℂ G z = 0` using `fun z ↦ by`. Rewrite using `[(hloc z).fderiv_eq]`. Conclude with `hder _ z (hUz z)`. Use function extensionality and compare the values at `l`. Establish `hl : (0 : Fin g → ℂ) + l ∈ pre u.ex (Uz 0).1` using `(hadd _ l 0).2 (hUz 0)`.

Establish `e1` using `hper (Uz 0) l 0 (hUz 0)`. Establish `e2` using `hG (Uz 0) _ hl`. Establish `e3` using `is_const_of_fderiv_eq_zero hGd hGf ((0 : Fin g → ℂ) + l) 0`. Establish `e4` using `hG (Uz 0) 0 (hUz 0)`. Simplify using `only [Pi.zero_apply]`.

Take the linear combination `-e1 - e2 + e3 + e4`.
-/
theorem zero_periods_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ q, IsPer u.ex u.Λ 0 q → q = 0 := by
  intro A _ g L u q hq
  obtain ⟨hopen, -, hadd, -, hinf, -, -, hbasis, -, -, -, htop⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨h, ⟨hdiff, hres0, hder0⟩, hper⟩ := GlobalTheory.T.exists_holomorphic_primitive_of_cechDeRham_periods A g L u 0 q hq 0 (map_zero _)
  have hres : ∀ (U V : A.left.affineOpens), V.1 ≤ U.1 → ∀ z ∈ pre u.ex V.1, h V z = h U z := by
    intro U V hVU z hz
    have := hres0 U V (homOfLE hVU).op z hz
    rw [this]
    change h U z + valAt' _ _ (0 : Γ(A.left, V.1)) = h U z
    unfold valAt' valAt
    split_ifs <;> simp
  have hder : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, fderiv ℂ (h U) z = 0 := by
    intro U z hz
    rw [hder0 U z hz]
    change evForm u.ex U.1 z 0 = 0
    simp
  have hex : ∀ z, ∃ U : A.left.affineOpens, z ∈ pre u.ex U.1 := fun z ↦ by
    obtain ⟨W, -, hW⟩ := hbasis ⊤ z (htop z)
    exact ⟨W, hW⟩
  choose Uz hUz using hex
  let G : (Fin g → ℂ) → ℂ := fun z ↦ h (Uz z) z
  have hG : ∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, G z = h U z := by
    intro U z hz
    obtain ⟨W, hWle, hW⟩ := hbasis (U.1 ⊓ (Uz z).1) z (by rw [hinf]; exact ⟨hz, hUz z⟩)
    have h1 := hres U W (hWle.trans inf_le_left) z hW
    have h2 := hres (Uz z) W (hWle.trans inf_le_right) z hW
    simp only [G]
    rw [← h1, ← h2]
  have hloc : ∀ z, G =ᶠ[nhds z] h (Uz z) := fun z ↦ by
    filter_upwards [(hopen _).mem_nhds (hUz z)] with w hw
    exact hG _ w hw
  have hGd : Differentiable ℂ G := fun z ↦
    (((hdiff (Uz z)).differentiableAt ((hopen _).mem_nhds (hUz z)))).congr_of_eventuallyEq (hloc z)
  have hGf : ∀ z, fderiv ℂ G z = 0 := fun z ↦ by
    rw [(hloc z).fderiv_eq]; exact hder _ z (hUz z)
  funext l
  have hl : (0 : Fin g → ℂ) + l ∈ pre u.ex (Uz 0).1 := (hadd _ l 0).2 (hUz 0)
  have e1 := hper (Uz 0) l 0 (hUz 0)
  have e2 := hG (Uz 0) _ hl
  have e3 := is_const_of_fderiv_eq_zero hGd hGf ((0 : Fin g → ℂ) + l) 0
  have e4 := hG (Uz 0) 0 (hUz 0)
  simp only [Pi.zero_apply]
  linear_combination -e1 - e2 + e3 + e4

end GlobalTheory.CechPer
