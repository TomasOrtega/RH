import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']

namespace WDRep

/- English proof (translation)
Use `⟨TensorProduct.prodLeft ℂ ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩` and prove the remaining obligations. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul x y`. Take `⟨x₁, x₂⟩` from `x`.

Simplify using the standard rewrite rules. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul x y`.

Take `⟨x₁, x₂⟩` from `x`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem iso_sum_tensor (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    ((a.sum b).tensor c).Iso ((a.tensor c).sum (b.tensor c)) := by
  refine ⟨TensorProduct.prodLeft ℂ ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      obtain ⟨x₁, x₂⟩ := x
      simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      obtain ⟨x₁, x₂⟩ := x
      simp
    | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Assemble the required witnesses or components as `⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_left], fun _ => rfl⟩`.
-/
theorem iso_tw_tensor (a : WDRep h V) (c : WDRep h V') (s : ℝ) :
    ((a.tw s).tensor c).Iso ((a.tensor c).tw s) :=
  ⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_left], fun _ => rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_right], fun _ => rfl⟩`.
-/
theorem iso_tensor_tw (a : WDRep h V) (c : WDRep h V') (s : ℝ) :
    (a.tensor (c.tw s)).Iso ((a.tensor c).tw s) :=
  ⟨.refl _ _, fun σ v => by simp [TensorProduct.map_smul_right], fun _ => rfl⟩

/- English proof (translation)
Use `⟨TensorProduct.assoc ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩` and prove the remaining obligations. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul x z`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp`. Consider the case `add x y hx hy => simp only [map_add, add_tmul, hx, hy]`. Proceed by induction on `v using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul x z`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x y => simp [tmul_add, add_tmul, add_assoc]`. Consider the case `add x y hx hy => simp only [map_add, add_tmul, hx, hy]`.
-/
theorem iso_tensor_assoc (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    ((a.tensor b).tensor c).Iso (a.tensor (b.tensor c)) := by
  refine ⟨TensorProduct.assoc ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x z =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp
      | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x z =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [tmul_add, add_tmul, add_assoc]
      | add x y hx hy => simp only [map_add, add_tmul, hx, hy]

/- English proof (translation)
Use `haveI : Subsingleton (V ⊗[ℂ] V') := by`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `key : ∀ z : V ⊗[ℂ] V', z = 0` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rfl`.

Consider the case `tmul x y => rw [Subsingleton.elim x 0, zero_tmul]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`. Rewrite using `[key x, key y]`. Conclude with `⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩`.
-/
theorem iso_zero_tensor (a : WDRep h V) (c : WDRep h V') [Subsingleton V] (b : WDRep h V'') [Subsingleton V''] :
    (a.tensor c).Iso b := by
  haveI : Subsingleton (V ⊗[ℂ] V') := by
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : V ⊗[ℂ] V', z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [key x, key y]
  exact ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

/- English proof (translation)
Take `⟨v, hv⟩` from `((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot).exists_hasEigenvector`. Establish `hv1 : c.ρ (frob h) v = v` using `by simpa using hv.apply_eq_smul`. Establish `hspan` using `(finrank_eq_one_iff_of_nonzero' v hv.2).mp hd`. Establish `hF : c.ρ (frob h) = 1` using `LinearMap.ext fun u => by`. Take `⟨t, rfl⟩` from `hspan u`.

Simplify using `[hv1]`. Take `⟨τ, hτ⟩` from `exists_eq_zpow_mul (deg_frob (h := h)) σ`. Establish `hz : ∀ n : ℤ, c.ρ (frob h ^ n) = 1` using `fun n => by`. Establish `h1 : c.ρ.toHomUnits (frob h) = 1` using `Units.ext hF`. Establish `h2 : c.ρ.toHomUnits (frob h ^ n) = 1` using `by rw [map_zpow, h1, one_zpow]`.

Conclude with `congrArg Units.val h2`. Rewrite using `[hτ, map_mul, hz, hu.2 τ, one_mul]`.
-/
theorem ρ_eq_one_of_line (c : WDRep h V') (hu : c.Unr) (hd : finrank ℂ V' = 1)
    (hroot : (c.ρ (frob h)).charpoly.IsRoot 1) (σ : Weil h) : c.ρ σ = 1 := by
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot).exists_hasEigenvector
  have hv1 : c.ρ (frob h) v = v := by simpa using hv.apply_eq_smul
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv.2).mp hd
  have hF : c.ρ (frob h) = 1 := LinearMap.ext fun u => by
    obtain ⟨t, rfl⟩ := hspan u
    simp [hv1]
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  have hz : ∀ n : ℤ, c.ρ (frob h ^ n) = 1 := fun n => by
    have h1 : c.ρ.toHomUnits (frob h) = 1 := Units.ext hF
    have h2 : c.ρ.toHomUnits (frob h ^ n) = 1 := by rw [map_zpow, h1, one_zpow]
    exact congrArg Units.val h2
  rw [hτ, map_mul, hz, hu.2 τ, one_mul]

/- English proof (translation)
Set `f : V' ≃ₗ[ℂ] ℂ` to `LinearEquiv.ofFinrankEq V' ℂ (by simpa using hd)`. Use `⟨(TensorProduct.congr (.refl ℂ V) f).trans (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩` and prove the remaining obligations. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [hρ]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [hN]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem iso_tensor_line (a : WDRep h V) (c : WDRep h V') (hN : c.N = 0) (hd : finrank ℂ V' = 1)
    (hρ : ∀ σ, c.ρ σ = 1) : (a.tensor c).Iso a := by
  let f : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq V' ℂ (by simpa using hd)
  refine ⟨(TensorProduct.congr (.refl ℂ V) f).trans (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hρ]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hN]
    | add x y hx hy => simp only [map_add, hx, hy]

end WDRep

namespace WD

/- English proof (translation)
Proceed by induction on `a using ind with`. Consider the case `hP n a`. Proceed by induction on `b using ind with`. Consider the case `hP m b`. Proceed by induction on `c using ind with`.

Consider the case `hP k c`. Use `⟨?_, ?_, ?_, ?_, ?_, fun hu hd he => ?_⟩` and prove the remaining obligations. Simplify using `only [lpSum_mk, lpChar_mk]`. Conclude with `sound (a.iso_sum_tensor b c)`. Simplify using `only [lpTw_mk, lpChar_mk]`.

Conclude with `sound (a.iso_tw_tensor c s)`. Simplify using `only [lpTw_mk, lpChar_mk]`. Conclude with `sound (a.iso_tensor_tw c s)`. Simplify using `only [lpChar_mk]`. Conclude with `sound (a.iso_tensor_assoc b c)`.

Simplify using `only [lpZero, lpChar_mk]`. Conclude with `sound (WDRep.iso_zero_tensor _ c _)`. Rewrite `hu` using `[unr_mk]`. Rewrite `hd` using `[lpDim_mk]`. Rewrite `he` using `[frobEig_mk]`.

Establish `hroot : (c.ρ (frob h)).charpoly.IsRoot 1`. Establish `h1 : (1 : ℂ) ∈ (c.ρ (frob h)).charpoly.roots` using `by rw [he]; simp`. Conclude with `(Polynomial.mem_roots'.mp h1).2`. Rewrite using `[lpChar_mk]`. Conclude with `sound (a.iso_tensor_line c hu.1 hd (c.ρ_eq_one_of_line hu hd hroot))`.
-/
theorem lpChar_laws (a b c : WD h) (s : ℝ) :
    (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧
    (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧
    a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧
    (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧
    (WD.lpZero h).lpChar c = WD.lpZero h ∧
    (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) := by
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
  induction c using ind with
  | hP k c =>
  refine ⟨?_, ?_, ?_, ?_, ?_, fun hu hd he => ?_⟩
  · simp only [lpSum_mk, lpChar_mk]
    exact sound (a.iso_sum_tensor b c)
  · simp only [lpTw_mk, lpChar_mk]
    exact sound (a.iso_tw_tensor c s)
  · simp only [lpTw_mk, lpChar_mk]
    exact sound (a.iso_tensor_tw c s)
  · simp only [lpChar_mk]
    exact sound (a.iso_tensor_assoc b c)
  · simp only [lpZero, lpChar_mk]
    exact sound (WDRep.iso_zero_tensor _ c _)
  · rw [unr_mk] at hu
    rw [lpDim_mk] at hd
    rw [frobEig_mk] at he
    have hroot : (c.ρ (frob h)).charpoly.IsRoot 1 := by
      have h1 : (1 : ℂ) ∈ (c.ρ (frob h)).charpoly.roots := by rw [he]; simp
      exact (Polynomial.mem_roots'.mp h1).2
    rw [lpChar_mk]
    exact sound (a.iso_tensor_line c hu.1 hd (c.ρ_eq_one_of_line hu hd hroot))

end WD

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ a b c s` and use `WD.lpChar_laws a b c s`.
-/
theorem lpChar_laws_closed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h) (s : ℝ),
    (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧
    (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧
    a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧
    (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧
    (WD.lpZero h).lpChar c = WD.lpZero h ∧
    (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) :=
  fun _ _ _ _ _ _ _ _ _ _ a b c s => WD.lpChar_laws a b c s

end GlobalTheory.WeilDeligne
