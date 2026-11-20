import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RootEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatFormM

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce and unpack `O K _ _ _ _ _ Δ τ L ⟨τ₀, e₀⟩`. Distinguish the cases in `h1 : IsUnit (2 + τ₀)`. Take `⟨lam, -, hl⟩` from `normEx O K Δ L h1.unit`. Establish `ep : algebraMap O K (2 + τ₀) = 2 + τ` using `by simp [map_ofNat, e₀]`. Rewrite `hl` using `[IsUnit.unit_spec, ep]`.

Establish `h0 : 2 + τ ≠ 0` using `ep ▸ (h1.map _).ne_zero`. Establish `hll : lam * star lam = algebraMap K _ (2 + τ)` using `by rw [← hl, QuadraticAlgebra.algebraMap_norm_eq_mul_star]`. Use `⟨lam • ofE Δ ((2 + τ)⁻¹ • (1 + ω : Etau K τ)), ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have s1 : ∀ x : Etau K τ, sigL (lam • ofE Δ x) = star lam • ofE Δ x := fun x => by ext <;> simp [sigL, ofE]`. Rewrite using `[s1, smul_mul_smul_comm, hll]`.

Apply the tactic sequence `ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring`. Take `⟨x, y, -, hu, hn⟩` from `rootEx O K Δ τ L τ₀ (-1) e₀ (by simpa [add_comm] using h1)`. Take `⟨ν, -, hν⟩` from `normEx O K Δ L (-1)`. Conclude with `⟨_, (datFormM O K Δ τ L 1 _ (by simpa using hu) hn ν (by simpa using hν) 1 one_ne_zero).1⟩`.
-/
theorem UpperTheory.V.Z.Sym.Loc.locNorm : UpperTheory.V.Z.Sym.Loc.LocNorm := by
  rintro O K _ _ _ _ _ Δ τ L ⟨τ₀, e₀⟩
  by_cases h1 : IsUnit (2 + τ₀)
  · obtain ⟨lam, -, hl⟩ := normEx O K Δ L h1.unit
    have ep : algebraMap O K (2 + τ₀) = 2 + τ := by simp [map_ofNat, e₀]
    rw [IsUnit.unit_spec, ep] at hl
    have h0 : 2 + τ ≠ 0 := ep ▸ (h1.map _).ne_zero
    have hll : lam * star lam = algebraMap K _ (2 + τ) := by rw [← hl, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    refine ⟨lam • ofE Δ ((2 + τ)⁻¹ • (1 + ω : Etau K τ)), ?_⟩
    have s1 : ∀ x : Etau K τ, sigL (lam • ofE Δ x) = star lam • ofE Δ x := fun x => by ext <;> simp [sigL, ofE]
    rw [s1, smul_mul_smul_comm, hll]
    ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  · obtain ⟨x, y, -, hu, hn⟩ := rootEx O K Δ τ L τ₀ (-1) e₀ (by simpa [add_comm] using h1)
    obtain ⟨ν, -, hν⟩ := normEx O K Δ L (-1)
    exact ⟨_, (datFormM O K Δ τ L 1 _ (by simpa using hu) hn ν (by simpa using hν) 1 one_ne_zero).1⟩
