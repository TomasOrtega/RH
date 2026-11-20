import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsPosCombinationDefiniteSumStatement
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.MinSysTypeBal

/- English proof (translation)
Introduce `O _ bar φ Y _ _ _ _ hX n N _ _ eb`. Use `haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm`. Use `haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm`. Take `⟨S₀, hS₀, hfin⟩` from `hX.finite`. Use `set F := hS₀.toFinset with hF`.

Set `ι` to `Σ m : Fin (F.card + 1), (Fin m.val → F)`. Set `P : ι → Prop` to `fun i => IsCone bar φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ Y)) ∧ ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ Y) x x`. Set `T : ι → Finset ((Fin n → ZMod N) → Y)` to `fun i => if h : P i then Classical.choose (GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb i.1.val _ (fun j x y => (h.1.mem j).1 x y) (fun j y => h.1.nonneg j y) h.2) else ∅`. Use `⟨Finset.univ.biUnion T, ?_⟩` and prove the remaining obligations. Introduce `b hb hpos`.

Take `⟨m, γ, k, cf, hcone, hk, hcf, hsum⟩` from `GlobalTheory.Poinc.Cover.exists_cone O bar φ Y hX b hb hpos`. Take `⟨e, he⟩` from `hfin m γ hcone`. Use `⟨e, fun μ h1 h2 => ?_⟩` and prove the remaining obligations. Set `γ' : Fin m → F` to `fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩`. Establish `hcone'` using `hcone.pull_equiv e`.

Establish `hinj : Function.Injective γ'` using `fun j l hjl => by`. Establish `h` using `congrArg Subtype.val hjl`. Simplify using `only [γ'] at h`. Conclude with `hcone'.injective h`. Establish `hm : m < F.card + 1`.

Use `Fintype.card_le_of_injective γ' hinj` as an intermediate fact. Simplify using `only [Fintype.card_fin, Fintype.card_coe] at this`. Use linear arithmetic over natural numbers and integers. Set `i : ι` to `⟨⟨m, hm⟩, γ'⟩`. Establish `hbyy : ∀ y, (k : ℤ) * b y y = ∑ j, (cf j : ℤ) * γ j y y` using `fun y => by`.

Use `LinearMap.congr_fun₂ hsum y y` as an intermediate fact. Simplify `this` using `[LinearMap.sum_apply, nsmul_eq_mul]`. Establish `hPi : P i`. Use `⟨hcone', fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [i, γ', pull_apply]`.

Establish `hex : e x ≠ 0` using `by simpa using hx`. Establish `hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x)` using `fun j _ => hcone.nonneg j _`. Use `lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_` and prove the remaining obligations. Establish `hz` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm`. Establish `h3` using `hpos _ hex`.

Establish `h4` using `hbyy (e x)`. Simplify using `[hz] at h4`. Break down `h4 with h4 | h4` into its components or cases. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Establish `hmem : μ ∈ T i`. Simplify using `only [T, dif_pos hPi]`. Use `Classical.choose_spec (GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb i.1.val _ (fun j x y => (hPi.1.mem j).1 x y) (fun j y => hPi.1.nonneg j y) hPi.2) (pull e.toLinearMap b) k cf hk hcf ?_ μ h1 h2` and prove the remaining obligations. Use extensionality with `a c`. Use `LinearMap.congr_fun₂ hsum (e a) (e c)` as an intermediate fact.

Simplify `this` using `[i, γ', pull_apply, LinearMap.sum_apply]`. Conclude with `Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩`.
-/
theorem finite_minimiser_systems_upTo_aut : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N →
    ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ b ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b x x) →
    ∃ e : Y ≃ₗ[O] Y, ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) →
    (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → pull e.toLinearMap b (μ cl) (μ cl) ≤ pull e.toLinearMap b α α) →
    μ ∈ S := by
  intro O _ bar φ Y _ _ _ _ hX n N _ _ eb
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  obtain ⟨S₀, hS₀, hfin⟩ := hX.finite
  set F := hS₀.toFinset with hF
  let ι := Σ m : Fin (F.card + 1), (Fin m.val → F)
  let P : ι → Prop := fun i => IsCone bar φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ Y)) ∧
    ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ Y) x x
  let T : ι → Finset ((Fin n → ZMod N) → Y) := fun i =>
    if h : P i then Classical.choose (GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb i.1.val _ (fun j x y => (h.1.mem j).1 x y)
      (fun j y => h.1.nonneg j y) h.2) else ∅
  refine ⟨Finset.univ.biUnion T, ?_⟩
  intro b hb hpos
  obtain ⟨m, γ, k, cf, hcone, hk, hcf, hsum⟩ := GlobalTheory.Poinc.Cover.exists_cone O bar φ Y hX b hb hpos
  obtain ⟨e, he⟩ := hfin m γ hcone
  refine ⟨e, fun μ h1 h2 => ?_⟩
  let γ' : Fin m → F := fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩
  have hcone' := hcone.pull_equiv e
  have hinj : Function.Injective γ' := fun j l hjl => by
    have h := congrArg Subtype.val hjl
    simp only [γ'] at h
    exact hcone'.injective h
  have hm : m < F.card + 1 := by
    have := Fintype.card_le_of_injective γ' hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  let i : ι := ⟨⟨m, hm⟩, γ'⟩
  have hbyy : ∀ y, (k : ℤ) * b y y = ∑ j, (cf j : ℤ) * γ j y y := fun y => by
    have := LinearMap.congr_fun₂ hsum y y
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hPi : P i := by
    refine ⟨hcone', fun x hx => ?_⟩
    simp only [i, γ', pull_apply]
    have hex : e x ≠ 0 := by simpa using hx
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x) := fun j _ => hcone.nonneg j _
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
    have h3 := hpos _ hex
    have h4 := hbyy (e x)
    simp [hz] at h4
    rcases h4 with h4 | h4
    · omega
    · omega
  have hmem : μ ∈ T i := by
    simp only [T, dif_pos hPi]
    refine Classical.choose_spec (GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb i.1.val _ (fun j x y => (hPi.1.mem j).1 x y)
      (fun j y => hPi.1.nonneg j y) hPi.2) (pull e.toLinearMap b) k cf hk hcf ?_ μ h1 h2
    ext a c
    have := LinearMap.congr_fun₂ hsum (e a) (e c)
    simpa [i, γ', pull_apply, LinearMap.sum_apply] using this
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩

end GlobalTheory.Poinc.MinSysTypeBal
