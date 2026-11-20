import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ExtTwo

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Use `set H : Subgroup V := U.subgroupOf V with hH`. Establish `hidx : H.index = 2` using `hi`. Establish `hσH : (⟨σ, hσ⟩ : V) ∉ H`. Rewrite using `[hH, Subgroup.mem_subgroupOf]`. Conclude with `hn`.

Establish `hcl : IsClosed (H : Set V)` using `H.isClosed_of_isOpen ho`. Establish `h10 : (1 : ZMod 2) ≠ 0` using `one_ne_zero`. Set `ε : V → ZMod 2` to `fun v => if v ∈ H then 0 else 1`. Establish `hmem : ε ∈ CharOff V S 2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsLocallyConstant.iff_isOpen_fiber_apply]`. Introduce `x`. Distinguish the cases in `hx : x ∈ H`. Use `ho using 1` and compare the differences between its conclusion and the goal. Use extensionality with `v`.

Apply the tactic sequence `by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10]`. Use `hcl.isOpen_compl using 1` and compare the differences between its conclusion and the goal. Use extensionality with `v`. Apply the tactic sequence `by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10, h10.symm]`. Introduce `a b`.

Establish `hab` using `Subgroup.mul_mem_iff_of_index_two hidx (a := a) (b := b)`. Apply the tactic sequence `by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ε, ha, hb, hab] <;> decide`. Introduce `u hu`. Establish `: u ∈ H`. Rewrite using `[hH, Subgroup.mem_subgroupOf]`.

Conclude with `hS _ hu u.2`. Simplify using `[ε, this]`. Use `⟨ε, hmem, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[ε, hσH]`. Introduce `v hv`.

Establish `: v ∈ H`. Rewrite using `[hH, Subgroup.mem_subgroupOf]`. Conclude with `hv`. Simplify using `[ε, this]`.
-/
private theorem UpperTheory.V.Two.invTwo_sign (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (hσ : σ ∈ V) (ho : IsOpen (U.subgroupOf V : Set V)) (hi : U.relIndex V = 2)
    (hn : σ ∉ U) (hS : ∀ s ∈ S, s ∈ V → s ∈ U) :
    ∃ ε ∈ CharOff V S 2, ε ⟨σ, hσ⟩ = 1 ∧ ∀ v : V, v.1 ∈ U → ε v = 0 := by
  classical
  set H : Subgroup V := U.subgroupOf V with hH
  have hidx : H.index = 2 := hi
  have hσH : (⟨σ, hσ⟩ : V) ∉ H := by
    rw [hH, Subgroup.mem_subgroupOf]; exact hn
  have hcl : IsClosed (H : Set V) := H.isClosed_of_isOpen ho
  have h10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  let ε : V → ZMod 2 := fun v => if v ∈ H then 0 else 1
  have hmem : ε ∈ CharOff V S 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [IsLocallyConstant.iff_isOpen_fiber_apply]
      intro x
      by_cases hx : x ∈ H
      · convert ho using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10]
      · convert hcl.isOpen_compl using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10, h10.symm]
    · intro a b
      have hab := Subgroup.mul_mem_iff_of_index_two hidx (a := a) (b := b)
      by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ε, ha, hb, hab] <;> decide
    · intro u hu
      have : u ∈ H := by
        rw [hH, Subgroup.mem_subgroupOf]; exact hS _ hu u.2
      simp [ε, this]
  refine ⟨ε, hmem, ?_, ?_⟩
  · simp [ε, hσH]
  · intro v hv
    have : v ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]; exact hv
    simp [ε, this]

/- English proof (translation)
Introduce `Γ _ _ _ U V S σ n hUV hσ ho hi hn hS hQ`. Establish `two : ∀ x : ZMod 2, x = 0 ∨ x = 1` using `by decide`. Take `⟨ε, hε, hεσ, hεU⟩` from `UpperTheory.V.Two.invTwo_sign Γ U V S σ hσ ho hi hn hS`. Establish `hσσ : σ * σ ∈ U`. Establish `h2 : (U.subgroupOf V).index = 2` using `hi`.

Use `(Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨σ, hσ⟩ : V)) (b := ⟨σ, hσ⟩)).mpr Iff.rfl` as an intermediate fact. Rewrite `this` using `[Subgroup.mem_subgroupOf]`. Then use the resulting hypothesis. Use `set P := {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} with hP`. Set `val : P → ZMod 2` to `fun φ => (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩`. Choose the witnesses or unpack the hypotheses as in `⟨φ0, hφ0⟩ : ∃ φ0 : P, ∀ φ : P, val φ ≠ 0 → val φ0 = 1 := by`.

Distinguish the cases in `hex : ∃ φ : P, val φ ≠ 0`. Take `⟨φ, hφ⟩` from `hex`. Conclude with `⟨φ, fun _ _ => (two _).resolve_left hφ⟩`. Use `push_neg at hex`. Conclude with `⟨⟨0, fun _ _ _ => rfl⟩, fun φ h => absurd (hex φ) h⟩`.

Set `χ : P → U → ZMod 2` to `fun φ => if val φ = 0 then (φ.1 : U → ZMod 2) else (φ.1 : U → ZMod 2) + (φ0.1 : U → ZMod 2)`. Establish `hχmem : ∀ φ, χ φ ∈ CharOff U S 2`. Introduce `φ`. Simplify using `only [χ]`. Use `split_ifs`.

Conclude with `φ.1.2`. Conclude with `add_mem φ.1.2 φ0.1.2`. Establish `hχinv : ∀ φ, ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → χ φ u' = χ φ u`. Introduce `φ u u' h`. Simplify using `only [χ]`.

Use `split_ifs`. Conclude with `φ.2 u u' h`. Simplify using `only [Pi.add_apply]`. Rewrite using `[φ.2 u u' h, φ0.2 u u' h]`. Establish `hχσ : ∀ φ, χ φ ⟨σ * σ, hσσ⟩ = 0`.

Introduce `φ`. Simplify using `only [χ]`. Use `split_ifs with h`. Conclude with `h`. Establish `h1 : (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1` using `(two _).resolve_left h`.

Establish `h2 : (φ0.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1` using `hφ0 φ h`. Simplify using `only [Pi.add_apply]`. Rewrite using `[h1, h2]`. Both sides reduce to the same expression. Establish `hext : ∀ φ, ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u, hUV u.2⟩ = χ φ u` using `fun φ => UpperTheory.V.Two.extTwo Γ U V S hUV σ hσ hσσ ho hi hn hS (χ φ) (hχmem φ) (hχinv φ) (hχσ φ)`.

Use `choose ψ hψmem hψσ hψU using hext`. Set `f : P → CharOff V S 2` to `fun φ => ⟨ψ φ + (if val φ = 0 then 0 else ε), add_mem (hψmem φ) (by split_ifs; exact zero_mem _; exact hε)⟩`. Use `UpperTheory.V.Two.CardLe.of_injective hQ f ?_` and prove the remaining obligations. Introduce `φ φ' hff`. Establish `hfun : ψ φ + (if val φ = 0 then 0 else ε) = ψ φ' + (if val φ' = 0 then 0 else ε)` using `congrArg Subtype.val hff`.

Establish `hbranch : (val φ = 0 ↔ val φ' = 0)`. Use `congrFun hfun ⟨σ, hσ⟩` as an intermediate fact. Simplify using `only [Pi.add_apply] at this`. Rewrite `this` using `[hψσ φ, hψσ φ']`. Apply the tactic sequence `by_cases h : val φ = 0 <;> by_cases h' : val φ' = 0 <;> simp [h, h', hεσ] at this ⊢`.

Establish `hχ : χ φ = χ φ'`. Use function extensionality and compare the values at `u`. Use `congrFun hfun ⟨u, hUV u.2⟩` as an intermediate fact. Simplify using `only [Pi.add_apply] at this`. Rewrite `this` using `[hψU φ u, hψU φ' u]`.

Establish `hu : ε ⟨u, hUV u.2⟩ = 0` using `hεU _ u.2`. Apply the tactic sequence `split_ifs at this <;> simpa [hu] using this`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [χ] at hχ`.

Distinguish the cases in `h : val φ = 0`. Establish `h'` using `hbranch.mp h`. Simplify `hχ` using `[h, h']`. Establish `h' : ¬ val φ' = 0` using `fun h' => h (hbranch.mpr h')`. Simplify using `only [h, h', if_false] at hχ`.

Conclude with `add_right_cancel hχ`.
-/
theorem UpperTheory.V.Two.invTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (n : ℕ), U ≤ V → σ ∈ V → IsOpen (U.subgroupOf V : Set V) → U.relIndex V = 2 → σ ∉ U → (∀ s ∈ S, s ∈ V → s ∈ U) →
      CardLe (CharOff V S 2) n → CardLe {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} n := by
  intro Γ _ _ _ U V S σ n hUV hσ ho hi hn hS hQ
  have two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  classical
  obtain ⟨ε, hε, hεσ, hεU⟩ := UpperTheory.V.Two.invTwo_sign Γ U V S σ hσ ho hi hn hS
  have hσσ : σ * σ ∈ U := by
    have h2 : (U.subgroupOf V).index = 2 := hi
    have := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨σ, hσ⟩ : V)) (b := ⟨σ, hσ⟩)).mpr Iff.rfl
    rwa [Subgroup.mem_subgroupOf] at this
  set P := {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} with hP
  let val : P → ZMod 2 := fun φ => (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : P, ∀ φ : P, val φ ≠ 0 → val φ0 = 1 := by
    by_cases hex : ∃ φ : P, val φ ≠ 0
    · obtain ⟨φ, hφ⟩ := hex
      exact ⟨φ, fun _ _ => (two _).resolve_left hφ⟩
    · push_neg at hex
      exact ⟨⟨0, fun _ _ _ => rfl⟩, fun φ h => absurd (hex φ) h⟩
  let χ : P → U → ZMod 2 := fun φ =>
    if val φ = 0 then (φ.1 : U → ZMod 2) else (φ.1 : U → ZMod 2) + (φ0.1 : U → ZMod 2)
  have hχmem : ∀ φ, χ φ ∈ CharOff U S 2 := by
    intro φ
    simp only [χ]
    split_ifs
    · exact φ.1.2
    · exact add_mem φ.1.2 φ0.1.2
  have hχinv : ∀ φ, ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → χ φ u' = χ φ u := by
    intro φ u u' h
    simp only [χ]
    split_ifs
    · exact φ.2 u u' h
    · simp only [Pi.add_apply]
      rw [φ.2 u u' h, φ0.2 u u' h]
  have hχσ : ∀ φ, χ φ ⟨σ * σ, hσσ⟩ = 0 := by
    intro φ
    simp only [χ]
    split_ifs with h
    · exact h
    · have h1 : (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := (two _).resolve_left h
      have h2 : (φ0.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := hφ0 φ h
      simp only [Pi.add_apply]
      rw [h1, h2]
      rfl
  have hext : ∀ φ, ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u, hUV u.2⟩ = χ φ u :=
    fun φ => UpperTheory.V.Two.extTwo Γ U V S hUV σ hσ hσσ ho hi hn hS (χ φ) (hχmem φ) (hχinv φ) (hχσ φ)
  choose ψ hψmem hψσ hψU using hext
  let f : P → CharOff V S 2 := fun φ =>
    ⟨ψ φ + (if val φ = 0 then 0 else ε), add_mem (hψmem φ) (by split_ifs; exact zero_mem _; exact hε)⟩
  refine UpperTheory.V.Two.CardLe.of_injective hQ f ?_
  intro φ φ' hff
  have hfun : ψ φ + (if val φ = 0 then 0 else ε) = ψ φ' + (if val φ' = 0 then 0 else ε) :=
    congrArg Subtype.val hff
  have hbranch : (val φ = 0 ↔ val φ' = 0) := by
    have := congrFun hfun ⟨σ, hσ⟩
    simp only [Pi.add_apply] at this
    rw [hψσ φ, hψσ φ'] at this
    by_cases h : val φ = 0 <;> by_cases h' : val φ' = 0 <;> simp [h, h', hεσ] at this ⊢
  have hχ : χ φ = χ φ' := by
    funext u
    have := congrFun hfun ⟨u, hUV u.2⟩
    simp only [Pi.add_apply] at this
    rw [hψU φ u, hψU φ' u] at this
    have hu : ε ⟨u, hUV u.2⟩ = 0 := hεU _ u.2
    split_ifs at this <;> simpa [hu] using this
  apply Subtype.ext
  apply Subtype.ext
  simp only [χ] at hχ
  by_cases h : val φ = 0
  · have h' := hbranch.mp h
    simpa [h, h'] using hχ
  · have h' : ¬ val φ' = 0 := fun h' => h (hbranch.mpr h')
    simp only [h, h', if_false] at hχ
    exact add_right_cancel hχ
