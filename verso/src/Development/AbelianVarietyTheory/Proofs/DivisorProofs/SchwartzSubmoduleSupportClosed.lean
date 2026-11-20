import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open ValuativeRel
open scoped Matrix Topology

noncomputable section

namespace GlobalTheory.SBRestrict

variable {k : Type} [Field k] {Y Y' : Type}

open Classical in

def ext (I : Set (Y × Y')) (s : Matrix {p : Y × Y' // p ∉ I} Unit k) : Matrix Y Y' k :=
  fun r q => if h : (r, q) ∈ I then 0 else s ⟨(r, q), h⟩ ()

def proj (I : Set (Y × Y')) (t : Matrix Y Y' k) : Matrix {p : Y × Y' // p ∉ I} Unit k :=
  fun j _ => t j.1.1 j.1.2

/- English proof (translation)
Use function extensionality and compare the values at `j u`. Simplify using `[proj, ext, j.2]`.
-/
theorem proj_ext (I : Set (Y × Y')) (s : Matrix {p : Y × Y' // p ∉ I} Unit k) : proj I (ext I s) = s := by
  funext j u
  simp [proj, ext, j.2]

/- English proof (translation)
Use function extensionality and compare the values at `r q`. Distinguish the cases in `h : (r, q) ∈ I`. Simplify using `[ext, h, ht r q h]`. Simplify using `[ext, proj, h]`.
-/
theorem ext_proj (I : Set (Y × Y')) (t : Matrix Y Y' k) (ht : ∀ r q, (r, q) ∈ I → t r q = 0) :
    ext I (proj I t) = t := by
  funext r q
  by_cases h : (r, q) ∈ I
  · simp [ext, h, ht r q h]
  · simp [ext, proj, h]

/- English proof (translation)
Introduce `r q h` and use `by simp [ext, h]`.
-/
theorem ext_mem (I : Set (Y × Y')) (s : Matrix {p : Y × Y' // p ∉ I} Unit k) :
    ∀ r q, (r, q) ∈ I → ext I s r q = 0 := fun r q h => by simp [ext, h]

/- English proof (translation)
Use function extensionality and compare the values at `r q`. Apply the tactic sequence `by_cases h : (r, q) ∈ I <;> simp [ext, h]`.
-/
theorem ext_add (I : Set (Y × Y')) (s x : Matrix {p : Y × Y' // p ∉ I} Unit k) :
    ext I (s + x) = ext I s + ext I x := by
  funext r q
  by_cases h : (r, q) ∈ I <;> simp [ext, h]

open Classical in
/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type' (f := fun r q => ext I s r q * ext I b r q), ← Fintype.sum_subtype_add_sum_subtype (fun p => p ∈ I)]`. Establish `h1 : ∑ i : {x : Y × Y' // x ∈ I}, ext I s i.1.1 i.1.2 * ext I b i.1.1 i.1.2 = 0` using `Finset.sum_eq_zero fun i _ => by simp [ext, i.2]`. Rewrite using `[h1, zero_add]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[ext, j.2, mul_comm]`.
-/
theorem pair_ext [Fintype Y] [Fintype Y'] (I : Set (Y × Y')) (s b : Matrix {p : Y × Y' // p ∉ I} Unit k) :
    ∑ r, ∑ q, ext I s r q * ext I b r q = ∑ r, ∑ q, b r q * s r q := by
  rw [← Fintype.sum_prod_type' (f := fun r q => ext I s r q * ext I b r q),
    ← Fintype.sum_subtype_add_sum_subtype (fun p => p ∈ I)]
  have h1 : ∑ i : {x : Y × Y' // x ∈ I}, ext I s i.1.1 i.1.2 * ext I b i.1.1 i.1.2 = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [ext, i.2]
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [ext, j.2, mul_comm]

variable [TopologicalSpace k]

/- English proof (translation)
Use `continuous_pi fun r => continuous_pi fun q => ?_` and prove the remaining obligations. Distinguish the cases in `h : (r, q) ∈ I`. Simplify using `only [ext, h, dite_true]`. Conclude with `continuous_const`. Simplify using `only [ext, h, dite_false]`.

Use `fun_prop`.
-/
theorem continuous_ext [IsTopologicalRing k] (I : Set (Y × Y')) :
    Continuous (ext (k := k) I) := by
  refine continuous_pi fun r => continuous_pi fun q => ?_
  by_cases h : (r, q) ∈ I
  · simp only [ext, h, dite_true]; exact continuous_const
  · simp only [ext, h, dite_false]; fun_prop

/- English proof (translation)
Unfold `proj`. Use `fun_prop`.
-/
theorem continuous_proj (I : Set (Y × Y')) : Continuous (proj (k := k) I) := by
  unfold proj; fun_prop

end GlobalTheory.SBRestrict

namespace GlobalTheory.SBRestrict

open Classical in

/- English proof (translation)
Introduce `k _ _ _ _ _ Y Y' _ _ _ _ ψ0 hc h1 hne I S hS hV hT hM φ₀ hφ₀ t₀ ht₀ hne₀`. Set `ψk : AddChar k Circle` to `{ toFun := fun x => ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (h1 x)⟩ map_zero_eq_one' := Circle.ext (by simp) map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ0 a b) }`. Establish `hψv : ∀ x, (ψk x : ℂ) = ψ0 x` using `fun _ => rfl`. Establish `hψc : Continuous ψk` using `Continuous.subtype_mk hc _`. Establish `hψ1 : ψk ≠ 1` using `fun h => hne (AddChar.ext _ _ (fun x => by`.

Use `congrArg (fun χ : AddChar k Circle => (χ x : ℂ)) h` as an intermediate fact. Simplify `this))` using `[hψv]`. Set `res : (Matrix Y Y' k → ℂ) →ₗ[ℂ] (Matrix {p : Y × Y' // p ∉ I} Unit k → ℂ)` to `LinearMap.funLeft ℂ ℂ (ext I)`. Establish `hres_apply : ∀ φ s, res φ s = φ (ext I s)` using `fun _ _ => rfl`. Establish `hres : ∀ φ ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k), res φ ∈ GlobalTheory.WeilM.SB (Matrix {p : Y × Y' // p ∉ I} Unit k)`.

Introduce `φ hφ`. Use `⟨hφ.1.comp_continuous (continuous_ext I), HasCompactSupport.intro (hφ.2.isCompact.image (continuous_proj I)) fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[hres_apply]`. Conclude with `image_eq_zero_of_notMem_tsupport fun h => hs ⟨_, h, proj_ext I s⟩`. Establish `hTeq : S.map res = GlobalTheory.SplitWeil.SB (Matrix {p : Y × Y' // p ∉ I} Unit k)`.

Use `GlobalTheory.IrredSB.sb_irreducible k {p : Y × Y' // p ∉ I} Unit ψk hψc hψ1 (S.map res) ?_ ?_ ?_ (res φ₀) ⟨φ₀, hφ₀, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `hres φ (hS hφ)`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩ x -`. Use `⟨fun t => φ (t + ext I x), hT (ext I x) (ext_mem I x) φ hφ, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `s`. Simplify using `only [hres_apply, ext_add]`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩ b -`. Use `⟨_, hM (ext I b) φ hφ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`.

Simplify using `only [hres_apply, hψv]`. Rewrite using `[pair_ext]`. Introduce `h`. Use `congrFun h (proj I t₀)` as an intermediate fact. Rewrite `this` using `[hres_apply, ext_proj I t₀ ht₀]`.

Conclude with `hne₀ this`. Use `le_antisymm hS fun φ hφ => ?_` and prove the remaining obligations. Take `⟨s, hs, hse⟩ : res φ ∈ S.map res` from `hTeq ▸ hres φ hφ`. Establish `hd : φ - s ∈ S` using `hV _ (sub_mem hφ (hS hs)) fun t ht => by`. Use `congrFun hse (proj I t)` as an intermediate fact.

Rewrite `this` using `[hres_apply, hres_apply, ext_proj I t ht]`. Simplify using `[this]`. Simplify using `using add_mem hd hs`.
-/
theorem eq_SB_of_restrict : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, ‖ψ0 x‖ = 1) → ψ0 ≠ 1 → ∀ (I : Set (Y × Y')) (S : Submodule ℂ (Matrix Y Y' k → ℂ)),
    S ≤ GlobalTheory.WeilM.SB (Matrix Y Y' k) →
    (∀ φ ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k), (∀ t : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → t r q = 0) → φ t = 0) → φ ∈ S) →
    (∀ x : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → x r q = 0) → ∀ φ ∈ S, (fun t => φ (t + x)) ∈ S) →
    (∀ z : Matrix Y Y' k, ∀ φ ∈ S, (fun t => ψ0 (∑ r, ∑ q, t r q * z r q) * φ t) ∈ S) →
    ∀ φ₀ ∈ S, ∀ t₀ : Matrix Y Y' k, (∀ r q, (r, q) ∈ I → t₀ r q = 0) → φ₀ t₀ ≠ 0 → S = GlobalTheory.WeilM.SB (Matrix Y Y' k) := by
  intro k _ _ _ _ _ Y Y' _ _ _ _ ψ0 hc h1 hne I S hS hV hT hM φ₀ hφ₀ t₀ ht₀ hne₀
  let ψk : AddChar k Circle :=
    { toFun := fun x => ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (h1 x)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ0 a b) }
  have hψv : ∀ x, (ψk x : ℂ) = ψ0 x := fun _ => rfl
  have hψc : Continuous ψk := Continuous.subtype_mk hc _
  have hψ1 : ψk ≠ 1 := fun h => hne (AddChar.ext _ _ (fun x => by
    have := congrArg (fun χ : AddChar k Circle => (χ x : ℂ)) h
    simpa [hψv] using this))
  let res : (Matrix Y Y' k → ℂ) →ₗ[ℂ] (Matrix {p : Y × Y' // p ∉ I} Unit k → ℂ) :=
    LinearMap.funLeft ℂ ℂ (ext I)
  have hres_apply : ∀ φ s, res φ s = φ (ext I s) := fun _ _ => rfl
  have hres : ∀ φ ∈ GlobalTheory.WeilM.SB (Matrix Y Y' k), res φ ∈ GlobalTheory.WeilM.SB (Matrix {p : Y × Y' // p ∉ I} Unit k) := by
    intro φ hφ
    refine ⟨hφ.1.comp_continuous (continuous_ext I),
      HasCompactSupport.intro (hφ.2.isCompact.image (continuous_proj I)) fun s hs => ?_⟩
    rw [hres_apply]
    exact image_eq_zero_of_notMem_tsupport fun h => hs ⟨_, h, proj_ext I s⟩
  have hTeq : S.map res = GlobalTheory.SplitWeil.SB (Matrix {p : Y × Y' // p ∉ I} Unit k) := by
    refine GlobalTheory.IrredSB.sb_irreducible k {p : Y × Y' // p ∉ I} Unit ψk hψc hψ1 (S.map res) ?_ ?_ ?_
      (res φ₀) ⟨φ₀, hφ₀, rfl⟩ ?_
    · rintro _ ⟨φ, hφ, rfl⟩
      exact hres φ (hS hφ)
    · rintro _ ⟨φ, hφ, rfl⟩ x -
      refine ⟨fun t => φ (t + ext I x), hT (ext I x) (ext_mem I x) φ hφ, ?_⟩
      funext s
      simp only [hres_apply, ext_add]
    · rintro _ ⟨φ, hφ, rfl⟩ b -
      refine ⟨_, hM (ext I b) φ hφ, ?_⟩
      funext s
      simp only [hres_apply, hψv]
      rw [pair_ext]
    · intro h
      have := congrFun h (proj I t₀)
      rw [hres_apply, ext_proj I t₀ ht₀] at this
      exact hne₀ this
  refine le_antisymm hS fun φ hφ => ?_
  obtain ⟨s, hs, hse⟩ : res φ ∈ S.map res := hTeq ▸ hres φ hφ
  have hd : φ - s ∈ S := hV _ (sub_mem hφ (hS hs)) fun t ht => by
    have := congrFun hse (proj I t)
    rw [hres_apply, hres_apply, ext_proj I t ht] at this
    simp [this]
  simpa using add_mem hd hs

end GlobalTheory.SBRestrict
