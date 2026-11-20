import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule

noncomputable section

open ReciprocityTheory.ChartRestriction.DS
open scoped InnerProductSpace Matrix

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Take `⟨hu, hc⟩` from `hg`. Use `⟨Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hu), ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Matrix.conjTranspose hc`. Simplify using `only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at h`. Conclude with `h.symm`.
-/
theorem sumTypes_conjT_mem {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : gᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hg
  refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hu), ?_⟩
  have h := congrArg Matrix.conjTranspose hc
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at h
  exact h.symm

/- English proof (translation)
The claim follows from `Matrix.mem_unitaryGroup_iff.1 hg.1`.
-/
theorem sumTypes_mul_conjT {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : g * gᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hg.1

/- English proof (translation)
Establish `hK` using `Formalism.REAL.kFacts n ε`. Establish `hgU : g ∈ UJset ε` using `hK.1 g hg`. Establish `hgU' : gᴴ ∈ UJset ε` using `hK.1 _ (sumTypes_conjT_mem hg)`. Set `f : H →ₗᵢ[ℂ] H` to `{ (σ g : H →ₗ[ℂ] H) with norm_map' := hσ.2.1 g hgU }`. Establish `e : σ g (σ gᴴ r) = r`.

Establish `h1` using `hσ.1.2 g hgU gᴴ hgU'`. Rewrite `h1` using `[sumTypes_mul_conjT hg, hσ.1.1]`. Use `congrArg (fun T : H →L[ℂ] H => T r) h1` as an intermediate fact. Simplify using `using this.symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e]`. Use `_ = ⟪σ gᴴ r, v⟫_ℂ := f.inner_map_map _ _`.
-/
theorem sumTypes_inner {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) (r v : H) :
    ⟪r, σ g v⟫_ℂ = ⟪σ gᴴ r, v⟫_ℂ := by
  have hK := Formalism.REAL.kFacts n ε
  have hgU : g ∈ UJset ε := hK.1 g hg
  have hgU' : gᴴ ∈ UJset ε := hK.1 _ (sumTypes_conjT_mem hg)
  let f : H →ₗᵢ[ℂ] H := { (σ g : H →ₗ[ℂ] H) with norm_map' := hσ.2.1 g hgU }
  have e : σ g (σ gᴴ r) = r := by
    have h1 := hσ.1.2 g hgU gᴴ hgU'
    rw [sumTypes_mul_conjT hg, hσ.1.1] at h1
    have := congrArg (fun T : H →L[ℂ] H => T r) h1
    simpa using this.symm
  calc ⟪r, σ g v⟫_ℂ = ⟪f (σ gᴴ r), f v⟫_ℂ := by
        show ⟪r, σ g v⟫_ℂ = ⟪σ g (σ gᴴ r), σ g v⟫_ℂ
        rw [e]
    _ = ⟪σ gᴴ r, v⟫_ℂ := f.inner_map_map _ _

/- English proof (translation)
Introduce `n ε H _ _ σ hσ S hSfd hSK`. Use `set R : Submodule ℂ H := sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} with hR`. Establish `hRS : R ≤ S` using `sSup_le fun S' hS' => hS'.1`. Establish `: FiniteDimensional ℂ R` using `Submodule.finiteDimensional_of_le hRS`. Establish `hRK : Formalism.MainNotions.S.IsKStableOn ε σ R`.

Introduce `g hg v hv`. Establish `hle : R ≤ Submodule.comap (σ g : H →ₗ[ℂ] H) R` using `sSup_le fun S' hS' x hx => by`. Take `⟨μ, hμ⟩` from `hS'.2`. Conclude with `Submodule.mem_sSup_of_mem hS' (hμ.2.1 g hg x hx)`. Conclude with `hle hv`.

Establish `hRoK : Formalism.MainNotions.S.IsKStableOn ε σ Rᗮ`. Introduce `g hg v hv r hr`. Rewrite using `[sumTypes_inner hσ hg]`. Conclude with `hv _ (hRK _ (sumTypes_conjT_mem hg) r hr)`. Use `set T : Submodule ℂ H := S ⊓ Rᗮ`.

Establish `hT : T = ⊥`. Assume the negation of the conclusion as `h0`. Establish `: FiniteDimensional ℂ T` using `Submodule.finiteDimensional_of_le inf_le_left`. Take `⟨μ, S', hS'T, hS'⟩` from `GlobalTheory.KTypeExists.exists_kType n ε H σ hσ T inferInstance (fun g hg v hv => Submodule.mem_inf.2 ⟨hSK g hg v (Submodule.mem_inf.1 hv).1, hRoK g hg v (Submodule.mem_inf.1 hv).2⟩) h0`. Take `⟨v, hv, hv0, -⟩` from `hS'.2.2.2.1`.

Establish `hvR : v ∈ R` using `Submodule.mem_sSup_of_mem (show S' ∈ {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} from ⟨hS'T.trans inf_le_left, μ, hS'⟩) hv`. Establish `hvRo : v ∈ Rᗮ` using `(hS'T hv).2`. Conclude with `hv0 (inner_self_eq_zero.1 (hvRo v hvR))`. Introduce `v hv`. Take `⟨y, hy, z, hz, rfl⟩` from `R.exists_add_mem_mem_orthogonal v`.

Establish `hzS : z ∈ S`. Use `sub_mem hv (hRS hy)` as an intermediate fact. Simplify using `using this`. Establish `hz0 : z ∈ T` using `⟨hzS, hz⟩`. Rewrite `hz0` using `[hT, Submodule.mem_bot]`.

Rewrite using `[hz0, add_zero]`. Conclude with `hy`.
-/
theorem finDimStable_isSumOfKTypes : SumTypes := by
  intro n ε H _ _ σ hσ S hSfd hSK
  set R : Submodule ℂ H := sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} with hR
  have hRS : R ≤ S := sSup_le fun S' hS' => hS'.1
  have : FiniteDimensional ℂ R := Submodule.finiteDimensional_of_le hRS
  have hRK : Formalism.MainNotions.S.IsKStableOn ε σ R := by
    intro g hg v hv
    have hle : R ≤ Submodule.comap (σ g : H →ₗ[ℂ] H) R := sSup_le fun S' hS' x hx => by
      obtain ⟨μ, hμ⟩ := hS'.2
      exact Submodule.mem_sSup_of_mem hS' (hμ.2.1 g hg x hx)
    exact hle hv
  have hRoK : Formalism.MainNotions.S.IsKStableOn ε σ Rᗮ := by
    intro g hg v hv r hr
    rw [sumTypes_inner hσ hg]
    exact hv _ (hRK _ (sumTypes_conjT_mem hg) r hr)
  set T : Submodule ℂ H := S ⊓ Rᗮ
  have hT : T = ⊥ := by
    by_contra h0
    have : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨μ, S', hS'T, hS'⟩ := GlobalTheory.KTypeExists.exists_kType n ε H σ hσ T inferInstance
      (fun g hg v hv => Submodule.mem_inf.2 ⟨hSK g hg v (Submodule.mem_inf.1 hv).1, hRoK g hg v (Submodule.mem_inf.1 hv).2⟩) h0
    obtain ⟨v, hv, hv0, -⟩ := hS'.2.2.2.1
    have hvR : v ∈ R := Submodule.mem_sSup_of_mem (show S' ∈ {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} from ⟨hS'T.trans inf_le_left, μ, hS'⟩) hv
    have hvRo : v ∈ Rᗮ := (hS'T hv).2
    exact hv0 (inner_self_eq_zero.1 (hvRo v hvR))
  intro v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := R.exists_add_mem_mem_orthogonal v
  have hzS : z ∈ S := by
    have := sub_mem hv (hRS hy)
    simpa using this
  have hz0 : z ∈ T := ⟨hzS, hz⟩
  rw [hT, Submodule.mem_bot] at hz0
  rw [hz0, add_zero]
  exact hy

end GlobalTheory.PsCo.PcEF
