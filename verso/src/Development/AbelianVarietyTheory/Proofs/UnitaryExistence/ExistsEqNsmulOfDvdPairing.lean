import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LevelHalf

open NumberField Matrix in
open scoped nonZeroDivisors in

/- English proof (translation)
Introduce `E _ _ _ H D l gam hiso hhalf x`. Consider the cases of `D with`. Consider the case `mk La _ _ EF _ hbij hbar _ _ _ _ => ?_`. Take `⟨M, _, _, Mb, _, _, hsup, _, _⟩` from `l`. Simplify using `only at *`.

Take `⟨i, hi, j, hj, hij⟩` from `Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ Mb ⊔ Mb.map (H.bar : 𝓞 E →+* 𝓞 E))`. Use `set y := gam x - x with hy`. Take `⟨e₁, he₁⟩` from `hhalf (j • x) (Submodule.smul_mem_smul hj Submodule.mem_top)`. Establish `hjy : j • y = M • e₁`. Rewrite using `[hy, smul_sub, ← LinearEquiv.map_smul, he₁]`.

Normalize the expressions using the abelian group laws. Establish `hdiv : ∀ z, (M : ℤ) ∣ EF (i • y) z`. Introduce `z`. Rewrite using `[hbar]`. Establish `hmem : H.bar i ∈ Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`.

Simplify using `using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hi`. Take `⟨e₂, he₂⟩` from `hhalf (H.bar i • z) (Submodule.smul_mem_smul hmem Submodule.mem_top)`. Use `⟨-EF (gam x) e₂, ?_⟩` and prove the remaining obligations. Rewrite using `[hy, map_sub, LinearMap.sub_apply, ← hiso x (H.bar i • z), he₂, map_add, map_nsmul, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Set `ψ : La →ₗ[ℤ] ℤ` to `{ toFun := fun z => EF (i • y) z / M map_add' := fun a b => by`. Simplify using `only [map_add]`. Conclude with `Int.add_ediv_of_dvd_left (hdiv a)`. Use the proof step `map_smul' := fun c a => by`. Simplify using `only [map_zsmul, smul_eq_mul, eq_intCast, Int.cast_id]`.

Conclude with `Int.mul_ediv_assoc _ (hdiv a) }`. Take `⟨w, hw⟩` from `hbij.2 ψ`. Establish `hiy : i • y = M • w`. Apply `hbij.1` to reduce the goal to its premises. Use extensionality with `z`.

Rewrite using `[map_nsmul, LinearMap.smul_apply, hw]`. Simplify using `[ψ, nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv z)]`. Use `⟨e₁ + w, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_add, ← hjy, ← hiy, add_comm (j • y), ← add_smul, hij, one_smul]`.
-/
theorem _root_.GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
      (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (gam : D.La ≃ₗ[𝓞 E] D.La), (∀ a b, D.EF (gam a) (gam b) = D.EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        ∃ e, gam a = a + l.M • e) → ∀ a, ∃ e, gam a = a + l.M • e := by
  intro E _ _ _ H D l gam hiso hhalf x
  cases D with
  | mk La _ _ EF _ hbij hbar _ _ _ _ => ?_
  obtain ⟨M, _, _, Mb, _, _, hsup, _, _⟩ := l
  dsimp only at *
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp
    (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ Mb ⊔ Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  set y := gam x - x with hy
  obtain ⟨e₁, he₁⟩ := hhalf (j • x) (Submodule.smul_mem_smul hj Submodule.mem_top)
  have hjy : j • y = M • e₁ := by
    rw [hy, smul_sub, ← LinearEquiv.map_smul, he₁]
    abel
  have hdiv : ∀ z, (M : ℤ) ∣ EF (i • y) z := by
    intro z
    rw [hbar]
    have hmem : H.bar i ∈ Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hi
    obtain ⟨e₂, he₂⟩ := hhalf (H.bar i • z) (Submodule.smul_mem_smul hmem Submodule.mem_top)
    refine ⟨-EF (gam x) e₂, ?_⟩
    rw [hy, map_sub, LinearMap.sub_apply, ← hiso x (H.bar i • z), he₂, map_add, map_nsmul,
      nsmul_eq_mul]
    ring
  let ψ : La →ₗ[ℤ] ℤ :=
    { toFun := fun z => EF (i • y) z / M
      map_add' := fun a b => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_left (hdiv a)
      map_smul' := fun c a => by
        simp only [map_zsmul, smul_eq_mul, eq_intCast, Int.cast_id]
        exact Int.mul_ediv_assoc _ (hdiv a) }
  obtain ⟨w, hw⟩ := hbij.2 ψ
  have hiy : i • y = M • w := by
    apply hbij.1
    ext z
    rw [map_nsmul, LinearMap.smul_apply, hw]
    simp [ψ, nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv z)]
  refine ⟨e₁ + w, ?_⟩
  calc gam x = x + y := by rw [hy]; abel
    _ = x + M • (e₁ + w) := by
      rw [smul_add, ← hjy, ← hiy, add_comm (j • y), ← add_smul, hij, one_smul]

end GlobalTheory.LevelHalf
