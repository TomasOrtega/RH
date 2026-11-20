import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hU u hε0`. Take `⟨U, hU⟩` from `hU`. Take `⟨ε, hε⟩` from `hε0`. Use `haveI := L.frac`. Set `D : K` to `τ ^ 2 - 4`.

Establish `L' : IsLoc O D` using `⟨L.frac, L.compl, L.fin, L.two, ⟨U, 1, one_ne_zero, by simp [D, hU]⟩⟩`. Establish `hw : ((2 : K) • (ω : Etau K τ) - algebraMap K _ τ) * ((2 : K) • ω - algebraMap K _ τ) = D • 1 + (0 : K) • ((2 : K) • ω - algebraMap K _ τ)`. Apply the tactic sequence `ext <;> simp [D] <;> ring`. Set `φ : Lsq K D →ₐ[K] Etau K τ` to `QuadraticAlgebra.lift ⟨_, hw⟩`. Establish `hφ : ∀ z : Lsq K D, φ z = ⟨z.re - τ * z.im, 2 * z.im⟩`.

Introduce `z`. Apply the tactic sequence `ext <;> simp [φ] <;> ring`. Establish `hn : ∀ z : Lsq K D, QuadraticAlgebra.norm (φ z) = QuadraticAlgebra.norm z`. Introduce `z`. Rewrite using `[hφ]`.

Simplify using `[QuadraticAlgebra.norm_def, D]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ∀ z : Lsq K D, φ (star z) = star (φ z)`. Introduce `z`. Rewrite using `[hφ, hφ]`.

Apply the tactic sequence `ext <;> simp <;> ring`. Take `⟨ν, hνi, hνn⟩` from `normEx O K D L' ε`. Establish `hv0n : QuadraticAlgebra.norm (φ ν) = algebraMap O K ε` using `by rw [hn, hνn]`. Establish `hεK : IsUnit (algebraMap O K (ε : O))` using `ε.isUnit.map _`. Establish `hv0u : IsUnit (φ ν)` using `QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [hv0n]; exact hεK)`.

Take `⟨v, hv⟩` from `hv0u`. Establish `hvi : IsIntegral O (v : Etau K τ)`. Rewrite using `[hv]`. Conclude with `IsIntegral.map (φ.restrictScalars O) hνi`. Set `β : Etau K τ` to `(u : Etau K τ) * ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ)`.

Establish `hβn : QuadraticAlgebra.norm β = 1`. Establish `h1 : QuadraticAlgebra.norm (v : Etau K τ) * QuadraticAlgebra.norm ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Rewrite `h1` using `[hv, hv0n]`. Simplify using `only [β, map_mul, hε]`.

Conclude with `h1`. Establish `h2 : (2 : K) ≠ 0` using `two_ne_zero_of_isLoc L`. Set `β' : Lsq K D` to `⟨β.re + τ * β.im / 2, β.im / 2⟩`. Establish `hφβ : φ β' = β`. Rewrite using `[hφ]`.

Apply the tactic sequence `ext <;> simp [β'] <;> field_simp <;> ring`. Establish `hβ'n : QuadraticAlgebra.norm β' = 1` using `by rw [← hn, hφβ, hβn]`. Take `⟨y, hy⟩` from `h90L O K D L' β' hβ'n`. Set `w : (Etau K τ)ˣ` to `Units.map (φ : Lsq K D →* Etau K τ) y`. Establish `hw' : (w : Etau K τ) = φ y` using `rfl`.

Use `⟨w⁻¹, v, hvi, ?_, ?_⟩` and prove the remaining obligations. Establish `e : ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) = star (v : Etau K τ) * algebraMap O (Etau K τ) ((ε⁻¹ : Oˣ) : O)`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hv, hv0n, algebraMap_etau (τ := τ) ((ε⁻¹ : Oˣ) : O), ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`. Rewrite using `[e]`.

Conclude with `(isIntegral_star hvi).mul isIntegral_algebraMap`. Establish `hq : quo w⁻¹ = β`. Unfold `quo`. Rewrite using `[inv_inv, hw', ← hs, hy, map_mul, hφβ, mul_left_comm, ← hw', Units.inv_mul, mul_one]`. Rewrite using `[hq]`.

Simplify using `only [β, mul_assoc, Units.inv_mul, mul_one]`.
-/
theorem UpperTheory.V.Z.Sym.Loc.One.eUnit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → ∀ u : (Etau K τ)ˣ, (∃ ε : Oˣ, QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε) →
        ∃ z v : (Etau K τ)ˣ, IsIntegral O (v : Etau K τ) ∧ IsIntegral O ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∧ (u : Etau K τ) = quo z * v := by
  intro O K _ _ _ _ _ Δ τ L hU u hε0
  obtain ⟨U, hU⟩ := hU
  obtain ⟨ε, hε⟩ := hε0
  haveI := L.frac
  let D : K := τ ^ 2 - 4
  have L' : IsLoc O D := ⟨L.frac, L.compl, L.fin, L.two, ⟨U, 1, one_ne_zero, by simp [D, hU]⟩⟩
  have hw : ((2 : K) • (ω : Etau K τ) - algebraMap K _ τ) * ((2 : K) • ω - algebraMap K _ τ)
      = D • 1 + (0 : K) • ((2 : K) • ω - algebraMap K _ τ) := by
    ext <;> simp [D] <;> ring
  let φ : Lsq K D →ₐ[K] Etau K τ := QuadraticAlgebra.lift ⟨_, hw⟩
  have hφ : ∀ z : Lsq K D, φ z = ⟨z.re - τ * z.im, 2 * z.im⟩ := by
    intro z
    ext <;> simp [φ] <;> ring
  have hn : ∀ z : Lsq K D, QuadraticAlgebra.norm (φ z) = QuadraticAlgebra.norm z := by
    intro z
    rw [hφ]
    simp [QuadraticAlgebra.norm_def, D]
    ring
  have hs : ∀ z : Lsq K D, φ (star z) = star (φ z) := by
    intro z
    rw [hφ, hφ]
    ext <;> simp <;> ring
  obtain ⟨ν, hνi, hνn⟩ := normEx O K D L' ε
  have hv0n : QuadraticAlgebra.norm (φ ν) = algebraMap O K ε := by rw [hn, hνn]
  have hεK : IsUnit (algebraMap O K (ε : O)) := ε.isUnit.map _
  have hv0u : IsUnit (φ ν) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [hv0n]; exact hεK)
  obtain ⟨v, hv⟩ := hv0u
  have hvi : IsIntegral O (v : Etau K τ) := by
    rw [hv]
    exact IsIntegral.map (φ.restrictScalars O) hνi
  let β : Etau K τ := (u : Etau K τ) * ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ)
  have hβn : QuadraticAlgebra.norm β = 1 := by
    have h1 : QuadraticAlgebra.norm (v : Etau K τ) * QuadraticAlgebra.norm ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hv, hv0n] at h1
    simp only [β, map_mul, hε]
    exact h1
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_isLoc L
  let β' : Lsq K D := ⟨β.re + τ * β.im / 2, β.im / 2⟩
  have hφβ : φ β' = β := by
    rw [hφ]
    ext <;> simp [β'] <;> field_simp <;> ring
  have hβ'n : QuadraticAlgebra.norm β' = 1 := by rw [← hn, hφβ, hβn]
  obtain ⟨y, hy⟩ := h90L O K D L' β' hβ'n
  let w : (Etau K τ)ˣ := Units.map (φ : Lsq K D →* Etau K τ) y
  have hw' : (w : Etau K τ) = φ y := rfl
  refine ⟨w⁻¹, v, hvi, ?_, ?_⟩
  · have e : ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ)
        = star (v : Etau K τ) * algebraMap O (Etau K τ) ((ε⁻¹ : Oˣ) : O) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hv, hv0n,
        algebraMap_etau (τ := τ) ((ε⁻¹ : Oˣ) : O), ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [e]
    exact (isIntegral_star hvi).mul isIntegral_algebraMap
  · have hq : quo w⁻¹ = β := by
      unfold quo
      rw [inv_inv, hw', ← hs, hy, map_mul, hφβ, mul_left_comm, ← hw', Units.inv_mul, mul_one]
    rw [hq]
    simp only [β, mul_assoc, Units.inv_mul, mul_one]
