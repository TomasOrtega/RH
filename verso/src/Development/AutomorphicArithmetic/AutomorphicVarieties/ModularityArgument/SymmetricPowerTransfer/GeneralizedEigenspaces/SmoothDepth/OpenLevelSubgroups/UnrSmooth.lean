import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

/- English proof (translation)
Take `⟨x, hx0, hx⟩` from `Valuation.IsNontrivial.exists_lt_one (v := valuation k)`. Conclude with `⟨Units.mk0 x (fun h => hx0 (by simp [h])), hx⟩`.
-/
private theorem exists_small (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ s : kˣ, valuation k (s : k) < 1 := by
  obtain ⟨x, hx0, hx⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  exact ⟨Units.mk0 x (fun h => hx0 (by simp [h])), hx⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `exists_small k`. Distinguish the cases in `hx : valuation k (x : k) < 1`. Use `⟨x * p, p, ?_, hp, by simp⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hx.le) hp`.

Use `⟨p, p * x⁻¹, hp, ?_, by simp⟩` and prove the remaining obligations. Establish `h1 : 1 ≤ valuation k (x : k)` using `not_lt.1 hx`. Rewrite using `[Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]`. Establish `h0 : valuation k (x : k) ≠ 0` using `by simp`. Establish `h2 : (valuation k (x : k))⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ h1`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' h2) hp`.
-/
private theorem split_small (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : ∃ s t : kˣ, valuation k (s : k) < 1 ∧ valuation k (t : k) < 1 ∧ x = s / t := by
  obtain ⟨p, hp⟩ := exists_small k
  by_cases hx : valuation k (x : k) < 1
  · refine ⟨x * p, p, ?_, hp, by simp⟩
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx.le) hp
  · refine ⟨p, p * x⁻¹, hp, ?_, by simp⟩
    have h1 : 1 ≤ valuation k (x : k) := not_lt.1 hx
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    have h0 : valuation k (x : k) ≠ 0 := by simp
    have h2 : (valuation k (x : k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) hp

/- English proof (translation)
Introduce `k _ _ _ _`. Use `⟨fun χ h => isSmoothChar_of_isUnram fun x hx => h x hx, fun ψ b h => ?_⟩` and prove the remaining obligations. Establish `key : ∀ t : kˣ, valuation k (t : k) < 1 → (ψ 0 / ψ 1) t = b t`. Introduce `t ht`. Establish `h1` using `Units.val_injective (h t ht)`.

Establish `h2` using `mul_right_cancel h1`. Rewrite `h2` using `[torusChar_apply, torusChar_apply, Fin.prod_univ_two, Fin.prod_univ_two]`. Simplify `h2` using `[MonoidHom.div_apply, div_eq_mul_inv]`. Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨s, t, hs, ht, rfl⟩` from `split_small k x`.

Rewrite using `[map_div, map_div, key s hs, key t ht]`.
-/
theorem UpperTheory.V.Z.Sym.Al.unrSmooth :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ χ : kˣ →* ℂˣ, (∀ u ∈ Hi.Uo k, χ u = 1) → IsSmoothChar χ) ∧
        ∀ (ψ : Fin 2 → kˣ →* ℂˣ) (b : kˣ →* ℂˣ), (∀ t : kˣ, valuation k (t : k) < 1 → expo ψ ![t, t⁻¹] = expo ![b, 1] ![t, t⁻¹]) → ψ 0 / ψ 1 = b := by
  intro k _ _ _ _
  refine ⟨fun χ h => isSmoothChar_of_isUnram fun x hx => h x hx, fun ψ b h => ?_⟩
  have key : ∀ t : kˣ, valuation k (t : k) < 1 → (ψ 0 / ψ 1) t = b t := by
    intro t ht
    have h1 := Units.val_injective (h t ht)
    have h2 := mul_right_cancel h1
    rw [torusChar_apply, torusChar_apply, Fin.prod_univ_two, Fin.prod_univ_two] at h2
    simpa [MonoidHom.div_apply, div_eq_mul_inv] using h2
  refine MonoidHom.ext fun x => ?_
  obtain ⟨s, t, hs, ht, rfl⟩ := split_small k x
  rw [map_div, map_div, key s hs, key t ht]
