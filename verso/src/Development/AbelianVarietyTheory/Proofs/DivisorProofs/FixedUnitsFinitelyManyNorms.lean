import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Set `N : Submodule ℤ (Additive (𝓞 L)ˣ)` to `LinearMap.range ((2 : ℤ) • LinearMap.id)`. Use `haveI : Module.Finite ℤ (Additive (𝓞 L)ˣ) := inferInstance`. Use `haveI : Finite (Additive (𝓞 L)ˣ ⧸ N) := by`. Use `Module.finite_of_fg_torsion _ fun q => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, ?_⟩` and prove the remaining obligations. Proceed by induction on `q using Submodule.Quotient.induction_on with`.

Consider the case `H x => show (2 : ℤ) • (Submodule.Quotient.mk (p := N) x) = 0`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨x, rfl⟩`. Use `haveI : Fintype (Additive (𝓞 L)ˣ ⧸ N) := Fintype.ofFinite _`. Set `rep` to `Function.surjInv (Submodule.Quotient.mk_surjective N)`.

Use `⟨Finset.univ.image (fun q => Additive.toMul (rep q)), fun x => ?_⟩` and prove the remaining obligations. Set `q : Additive (𝓞 L)ˣ ⧸ N` to `Submodule.Quotient.mk (Additive.ofMul x)`. Use `⟨Additive.toMul (rep q), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩` and prove the remaining obligations. Establish `hq : Submodule.Quotient.mk (p` using `N) (rep q) = q := Function.surjInv_eq _ q`. Establish `hmem : Additive.ofMul x - rep q ∈ N`.

Rewrite using `[← Submodule.Quotient.eq]`. Conclude with `hq.symm`. Take `⟨y, hy⟩` from `hmem`. Use `⟨Additive.toMul y, ?_⟩` and prove the remaining obligations. Establish `h2 : Additive.toMul ((2 : ℤ) • y) = Additive.toMul (Additive.ofMul x - rep q)`.

Simplify using `using congrArg Additive.toMul hy`. Rewrite `h2` using `[toMul_zsmul, toMul_sub, toMul_ofMul]`. Rewrite `h2` using `[eq_div_iff_mul_eq']`. Rewrite using `[← h2]`. Conclude with `mul_comm _ _`.
-/
theorem units_ringOfIntegers_mod_sq (L : Type) [Field L] [NumberField L] :
    ∃ R : Finset (𝓞 L)ˣ, ∀ x : (𝓞 L)ˣ, ∃ ρ ∈ R, ∃ w : (𝓞 L)ˣ, x = ρ * w ^ 2 := by
  classical
  let N : Submodule ℤ (Additive (𝓞 L)ˣ) := LinearMap.range ((2 : ℤ) • LinearMap.id)
  haveI : Module.Finite ℤ (Additive (𝓞 L)ˣ) := inferInstance
  haveI : Finite (Additive (𝓞 L)ˣ ⧸ N) := by
    refine Module.finite_of_fg_torsion _ fun q => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      show (2 : ℤ) • (Submodule.Quotient.mk (p := N) x) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, rfl⟩
  haveI : Fintype (Additive (𝓞 L)ˣ ⧸ N) := Fintype.ofFinite _
  let rep := Function.surjInv (Submodule.Quotient.mk_surjective N)
  refine ⟨Finset.univ.image (fun q => Additive.toMul (rep q)), fun x => ?_⟩
  let q : Additive (𝓞 L)ˣ ⧸ N := Submodule.Quotient.mk (Additive.ofMul x)
  refine ⟨Additive.toMul (rep q), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have hq : Submodule.Quotient.mk (p := N) (rep q) = q := Function.surjInv_eq _ q
  have hmem : Additive.ofMul x - rep q ∈ N := by
    rw [← Submodule.Quotient.eq]; exact hq.symm
  obtain ⟨y, hy⟩ := hmem
  refine ⟨Additive.toMul y, ?_⟩
  have h2 : Additive.toMul ((2 : ℤ) • y) = Additive.toMul (Additive.ofMul x - rep q) := by
    simpa using congrArg Additive.toMul hy
  rw [toMul_zsmul, toMul_sub, toMul_ofMul] at h2
  rw [eq_div_iff_mul_eq'] at h2
  rw [← h2]; exact mul_comm _ _

/- English proof (translation)
Introduce `L _ _ c _hc`. Take `⟨R, hR⟩` from `units_ringOfIntegers_mod_sq L`. Set `φ : 𝓞 L →* L` to `(algebraMap (𝓞 L) L : 𝓞 L →* L)`. Establish `hA : ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) → ∃ ρ ∈ R, ∃ w : (𝓞 L)ˣ, (ε : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2`. Introduce `ε h1 h2`.

Set `u : (𝓞 L)ˣ` to `⟨⟨ε, h1⟩, ⟨((ε⁻¹ : Lˣ) : L), h2⟩, by apply RingOfIntegers.ext; exact ε.mul_inv, by apply RingOfIntegers.ext; exact ε.inv_mul⟩`. Take `⟨ρ, hρ, w, hw⟩` from `hR u`. Use `⟨ρ, hρ, w, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Set `P : (𝓞 L)ˣ → Prop` to `fun ρ => ∃ e : Lˣ, IsIntegral ℤ (e : L) ∧ IsIntegral ℤ ((e⁻¹ : Lˣ) : L) ∧ c e = e ∧ ∃ w : (𝓞 L)ˣ, (e : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2`.

Set `pick : (𝓞 L)ˣ → Finset L` to `fun ρ => if h : P ρ then {((Classical.choose h : Lˣ) : L), -((Classical.choose h : Lˣ) : L)} else ∅`. Use `⟨R.biUnion pick, ?_⟩` and prove the remaining obligations. Introduce `ε h1 h2 hfix`. Take `⟨ρ, hρ, w, hw⟩` from `hA ε h1 h2`. Establish `hP : P ρ` using `⟨ε, h1, h2, hfix, w, hw⟩`.

Take `⟨_g1, _g2, gfix, w', hw'⟩` from `Classical.choose_spec hP`. Establish `hpick : pick ρ = {((Classical.choose hP : Lˣ) : L), -((Classical.choose hP : Lˣ) : L)}`. Simplify using `only [pick, dif_pos hP]`. Use `set e : Lˣ := Classical.choose hP with he`. Set `W : Lˣ` to `Units.map φ (w * w'⁻¹)`.

Establish `hint : ∀ v : (𝓞 L)ˣ, IsIntegral ℤ (φ (v : 𝓞 L))` using `fun v => RingOfIntegers.isIntegral_coe _`. Establish `hWint : IsIntegral ℤ (W : L)` using `hint _`. Establish `hWint' : IsIntegral ℤ ((W⁻¹ : Lˣ) : L)`. Establish `: W⁻¹ = Units.map φ (w * w'⁻¹)⁻¹` using `(map_inv _ _).symm`. Rewrite using `[this]`.

Conclude with `hint _`. Establish `hw'0 : φ (w' : 𝓞 L) ≠ 0` using `(Units.map φ w').ne_zero`. Establish `hWval : (W : L) = φ (w : 𝓞 L) * (φ (w' : 𝓞 L))⁻¹`. Establish `: W = Units.map φ w * (Units.map φ w')⁻¹` using `by simp only [W, map_mul, map_inv]`. Rewrite using `[this, Units.val_mul, Units.val_inv_eq_inv_val]`.

Both sides reduce to the same expression. Establish `key : (ε : L) = (e : L) * (W : L) ^ 2`. Rewrite using `[hWval, hw', hw]`. Clear the denominators using the available nonvanishing facts. Establish `he0 : (e : L) ≠ 0` using `e.ne_zero`.

Establish `hsq : (c (W : L)) ^ 2 = (W : L) ^ 2`. Establish `h3 : c (ε : L) = c (e : L) * (c (W : L)) ^ 2` using `by rw [key, map_mul, map_pow]`. Rewrite `h3` using `[hfix, gfix, key]`. Conclude with `(mul_left_cancel₀ he0 h3).symm`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h` into its components or cases.

Use `⟨(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩` and prove the remaining obligations. Rewrite using `[key, h]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨-(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩` and prove the remaining obligations. Rewrite using `[key, h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem units_fixed_eq_mul_mul_conj : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∃ S : Finset L, ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) → c ε = ε →
      ∃ f ∈ S, ∃ η : Lˣ, IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ (ε : L) = f * ((η : L) * c η) := by
  intro L _ _ c _hc
  classical
  obtain ⟨R, hR⟩ := units_ringOfIntegers_mod_sq L
  let φ : 𝓞 L →* L := (algebraMap (𝓞 L) L : 𝓞 L →* L)
  have hA : ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) →
      ∃ ρ ∈ R, ∃ w : (𝓞 L)ˣ, (ε : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2 := by
    intro ε h1 h2
    let u : (𝓞 L)ˣ := ⟨⟨ε, h1⟩, ⟨((ε⁻¹ : Lˣ) : L), h2⟩,
      by apply RingOfIntegers.ext; exact ε.mul_inv, by apply RingOfIntegers.ext; exact ε.inv_mul⟩
    obtain ⟨ρ, hρ, w, hw⟩ := hR u
    refine ⟨ρ, hρ, w, ?_⟩
    calc (ε : L) = φ (u : 𝓞 L) := rfl
      _ = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2 := by rw [hw, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  let P : (𝓞 L)ˣ → Prop := fun ρ => ∃ e : Lˣ, IsIntegral ℤ (e : L) ∧ IsIntegral ℤ ((e⁻¹ : Lˣ) : L) ∧
    c e = e ∧ ∃ w : (𝓞 L)ˣ, (e : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2
  let pick : (𝓞 L)ˣ → Finset L := fun ρ =>
    if h : P ρ then {((Classical.choose h : Lˣ) : L), -((Classical.choose h : Lˣ) : L)} else ∅
  refine ⟨R.biUnion pick, ?_⟩
  intro ε h1 h2 hfix
  obtain ⟨ρ, hρ, w, hw⟩ := hA ε h1 h2
  have hP : P ρ := ⟨ε, h1, h2, hfix, w, hw⟩
  obtain ⟨_g1, _g2, gfix, w', hw'⟩ := Classical.choose_spec hP
  have hpick : pick ρ = {((Classical.choose hP : Lˣ) : L), -((Classical.choose hP : Lˣ) : L)} := by
    simp only [pick, dif_pos hP]
  set e : Lˣ := Classical.choose hP with he
  let W : Lˣ := Units.map φ (w * w'⁻¹)
  have hint : ∀ v : (𝓞 L)ˣ, IsIntegral ℤ (φ (v : 𝓞 L)) := fun v => RingOfIntegers.isIntegral_coe _
  have hWint : IsIntegral ℤ (W : L) := hint _
  have hWint' : IsIntegral ℤ ((W⁻¹ : Lˣ) : L) := by
    have : W⁻¹ = Units.map φ (w * w'⁻¹)⁻¹ := (map_inv _ _).symm
    rw [this]; exact hint _
  have hw'0 : φ (w' : 𝓞 L) ≠ 0 := (Units.map φ w').ne_zero
  have hWval : (W : L) = φ (w : 𝓞 L) * (φ (w' : 𝓞 L))⁻¹ := by
    have : W = Units.map φ w * (Units.map φ w')⁻¹ := by simp only [W, map_mul, map_inv]
    rw [this, Units.val_mul, Units.val_inv_eq_inv_val]; rfl
  have key : (ε : L) = (e : L) * (W : L) ^ 2 := by
    rw [hWval, hw', hw]; field_simp
  have he0 : (e : L) ≠ 0 := e.ne_zero
  have hsq : (c (W : L)) ^ 2 = (W : L) ^ 2 := by
    have h3 : c (ε : L) = c (e : L) * (c (W : L)) ^ 2 := by rw [key, map_mul, map_pow]
    rw [hfix, gfix, key] at h3
    exact (mul_left_cancel₀ he0 h3).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · refine ⟨(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩
    rw [key, h]; ring
  · refine ⟨-(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩
    rw [key, h]; ring

end GlobalTheory
