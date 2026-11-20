import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNeZeroOfEventually
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IrredSBVec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Take `⟨n, hn, hxn⟩` from `GlobalTheory.SBUnif.exists_nat_mem_mul_integer x⁻¹ (inv_ne_zero hx)`. Rewrite `hxn` using `[inv_inv]`. Establish `hp : ψ0 x ^ n = 1`.

Rewrite using `[← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]`. Conclude with `h1 _ hxn`. Use `congrArg norm hp` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this`.
-/
theorem norm_char_eq_one (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (x : k) : ‖ψ0 x‖ = 1 := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, hn, hxn⟩ := GlobalTheory.SBUnif.exists_nat_mem_mul_integer x⁻¹ (inv_ne_zero hx)
  rw [inv_inv] at hxn
  have hp : ψ0 x ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]
    exact h1 _ hxn
  have := congrArg norm hp
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

def toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (norm_char_eq_one ψ0 h1 x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (AddChar.map_add_eq_mul ψ0 a b)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (x : k) :
    ((toCircle ψ0 h1 x : Circle) : ℂ) = ψ0 x := rfl

/- English proof (translation)
The claim follows from `hψ.subtype_mk _`.
-/
theorem continuous_toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (hψ : Continuous ψ0) :
    Continuous (toCircle ψ0 h1) :=
  hψ.subtype_mk _

/- English proof (translation)
Introduce `k _ _ _ _ _ κ _ ψ0 hψ hcond W hW hT hM φ₀ h0 hne`. Establish `h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1` using `fun y hy => by`. Simplify using `using (hcond 1).2 (one_mem _) y hy`. Use `set ψ := toCircle ψ0 h1 with hψdef`. Establish `hψc : Continuous ψ` using `continuous_toCircle ψ0 h1 hψ`.

Establish `hψ1 : ψ ≠ 1`. Take `⟨w, hw0, hw1⟩` from `Valuation.IsNontrivial.exists_lt_one (v := valuation k)`. Establish `hno : w⁻¹ ∉ 𝒪[k]`. Introduce `h`. Establish `h' : valuation k w⁻¹ ≤ 1` using `h`.

Rewrite `h'` using `[map_inv₀]`. Establish `hv0 : valuation k w ≠ 0` using `(Valuation.ne_zero_iff _).2 hw0`. Use `(one_lt_inv₀ (zero_lt_iff.2 hv0)).2 hw1` as an intermediate fact. Conclude with `absurd h' (not_le.2 this)`. Use `mt (hcond w⁻¹).1 hno` as an intermediate fact.

Use `push_neg at this`. Take `⟨y, -, hy⟩` from `this`. Introduce `he`. Apply `hy` to reduce the goal to its premises. Use `congrArg (fun χ : AddChar k Circle => ((χ (w⁻¹ * y) : Circle) : ℂ)) he` as an intermediate fact.

Simplify `this` using `[hψdef, coe_toCircle]`. Set `toM : (κ → k) → Matrix κ Unit k` to `fun x i _ => x i`. Set `frM : Matrix κ Unit k → (κ → k)` to `fun t i => t i ()`. Establish `hto : Continuous toM` using `by fun_prop`. Establish `hfr : Continuous frM` using `by fun_prop`.

Establish `hft : ∀ t, toM (frM t) = t` using `fun t => by funext i j; rfl`. Set `e : Matrix κ Unit k ≃ₜ (κ → k)` to `{ toFun := frM, invFun := toM, left_inv := hft, right_inv := fun x => rfl, continuous_toFun := hfr, continuous_invFun := hto }`. Establish `SBto : ∀ φ : (κ → k) → ℂ, φ ∈ GlobalTheory.WeilM.SB (κ → k) → (fun t => φ (frM t)) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k)` using `fun φ hφ => ⟨hφ.1.comp_continuous hfr, hφ.2.comp_homeomorph e⟩`. Set `W' : Submodule ℂ (Matrix κ Unit k → ℂ)` to `W.comap (LinearMap.funLeft ℂ ℂ toM)`. Establish `mem' : ∀ Φ, Φ ∈ W' ↔ (fun x => Φ (toM x)) ∈ W` using `fun Φ => Iff.rfl`.

Establish `hW' : W' ≤ GlobalTheory.SplitWeil.SB (Matrix κ Unit k)`. Introduce `Φ hΦ`. Use `SBto _ (hW ((mem' Φ).1 hΦ))` as an intermediate fact. Simplify `this` using `only [hft]`. Establish `key` using `GlobalTheory.IrredSB.sb_irreducible k κ Unit ψ hψc hψ1 W' hW' (fun Φ hΦ x _ => by`.

Rewrite using `[mem']`. Use `hT _ ((mem' Φ).1 hΦ) (frM x)` as an intermediate fact. Establish `hv : ∀ v, toM (v + frM x) = toM v + x` using `fun v => by`. Use function extensionality and compare the values at `i j`. Consider the cases of `j`.

Both sides reduce to the same expression. Use `show (fun v => Φ (toM v + x)) ∈ W`. Simplify `this)` using `only [hv]`. Use the proof step `(fun Φ hΦ b _ => by`. Rewrite using `[mem']`.

Use `hM _ ((mem' Φ).1 hΦ) (fun i => b i ())` as an intermediate fact. Establish `hs : ∀ v, (∑ r, ∑ q, b r q * toM v r q) = v ⬝ᵥ (fun i => b i ())` using `fun v => by`. Rewrite using `[dotProduct]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_unique]`.

Conclude with `mul_comm _ _`. Use `show (fun v => ((ψ (∑ r, ∑ q, b r q * toM v r q) : Circle) : ℂ) * Φ (toM v)) ∈ W`. Simplify using `only [hs]`. Conclude with `this)`. Use the proof step `(fun t => φ₀ (frM t)) ((mem' _).2 h0) (by`.

Introduce `h`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Conclude with `congrFun h (toM x))`. Use `le_antisymm hW fun φ hφ => ?_` and prove the remaining obligations.

Establish `: (fun t => φ (frM t)) ∈ W'` using `key ▸ SBto φ hφ`. Conclude with `(mem' _).1 this`.
-/
theorem sb_irreducible_vec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {κ : Type} [Fintype κ] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ W : Submodule ℂ ((κ → k) → ℂ), W ≤ GlobalTheory.WeilM.SB (κ → k) →
    (∀ φ ∈ W, ∀ v : κ → k, (fun x => φ (x + v)) ∈ W) →
    (∀ φ ∈ W, ∀ y : κ → k, (fun x => ψ0 (x ⬝ᵥ y) * φ x) ∈ W) →
    ∀ φ₀ ∈ W, φ₀ ≠ 0 → W = GlobalTheory.WeilM.SB (κ → k) := by
  intro k _ _ _ _ _ κ _ ψ0 hψ hcond W hW hT hM φ₀ h0 hne
  classical
  have h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1 := fun y hy => by
    simpa using (hcond 1).2 (one_mem _) y hy
  set ψ := toCircle ψ0 h1 with hψdef
  have hψc : Continuous ψ := continuous_toCircle ψ0 h1 hψ
  have hψ1 : ψ ≠ 1 := by
    obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have hno : w⁻¹ ∉ 𝒪[k] := by
      intro h
      have h' : valuation k w⁻¹ ≤ 1 := h
      rw [map_inv₀] at h'
      have hv0 : valuation k w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
      have := (one_lt_inv₀ (zero_lt_iff.2 hv0)).2 hw1
      exact absurd h' (not_le.2 this)
    have := mt (hcond w⁻¹).1 hno
    push_neg at this
    obtain ⟨y, -, hy⟩ := this
    intro he
    apply hy
    have := congrArg (fun χ : AddChar k Circle => ((χ (w⁻¹ * y) : Circle) : ℂ)) he
    simpa [hψdef, coe_toCircle] using this

  let toM : (κ → k) → Matrix κ Unit k := fun x i _ => x i
  let frM : Matrix κ Unit k → (κ → k) := fun t i => t i ()
  have hto : Continuous toM := by fun_prop
  have hfr : Continuous frM := by fun_prop
  have hft : ∀ t, toM (frM t) = t := fun t => by funext i j; rfl
  let e : Matrix κ Unit k ≃ₜ (κ → k) :=
    { toFun := frM, invFun := toM, left_inv := hft, right_inv := fun x => rfl,
      continuous_toFun := hfr, continuous_invFun := hto }
  have SBto : ∀ φ : (κ → k) → ℂ, φ ∈ GlobalTheory.WeilM.SB (κ → k) → (fun t => φ (frM t)) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) :=
    fun φ hφ => ⟨hφ.1.comp_continuous hfr, hφ.2.comp_homeomorph e⟩
  let W' : Submodule ℂ (Matrix κ Unit k → ℂ) := W.comap (LinearMap.funLeft ℂ ℂ toM)
  have mem' : ∀ Φ, Φ ∈ W' ↔ (fun x => Φ (toM x)) ∈ W := fun Φ => Iff.rfl
  have hW' : W' ≤ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) := by
    intro Φ hΦ
    have := SBto _ (hW ((mem' Φ).1 hΦ))
    simpa only [hft] using this
  have key := GlobalTheory.IrredSB.sb_irreducible k κ Unit ψ hψc hψ1 W' hW'
    (fun Φ hΦ x _ => by
      rw [mem']
      have := hT _ ((mem' Φ).1 hΦ) (frM x)
      have hv : ∀ v, toM (v + frM x) = toM v + x := fun v => by
        funext i j
        cases j
        rfl
      show (fun v => Φ (toM v + x)) ∈ W
      simpa only [hv] using this)
    (fun Φ hΦ b _ => by
      rw [mem']
      have := hM _ ((mem' Φ).1 hΦ) (fun i => b i ())
      have hs : ∀ v, (∑ r, ∑ q, b r q * toM v r q) = v ⬝ᵥ (fun i => b i ()) := fun v => by
        rw [dotProduct]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Fintype.sum_unique]
        exact mul_comm _ _
      show (fun v => ((ψ (∑ r, ∑ q, b r q * toM v r q) : Circle) : ℂ) * Φ (toM v)) ∈ W
      simp only [hs]
      exact this)
    (fun t => φ₀ (frM t)) ((mem' _).2 h0) (by
      intro h
      apply hne
      funext x
      exact congrFun h (toM x))
  refine le_antisymm hW fun φ hφ => ?_
  · have : (fun t => φ (frM t)) ∈ W' := key ▸ SBto φ hφ
    exact (mem' _).1 this

end GlobalTheory.IrredSBVec
