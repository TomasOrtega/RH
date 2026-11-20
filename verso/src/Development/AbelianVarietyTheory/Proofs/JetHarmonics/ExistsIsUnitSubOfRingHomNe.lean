import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `A O _ _ _ _ g hg hgO hA σ σ' hne`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hne` to reduce the goal to its premises. Establish `hgm : (g : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hgO)`.

Establish `hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O` using `(Ideal.span_singleton_le_iff_mem _).mpr hgm`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ) (M := A)`. Use `set J : Ideal O := Ideal.span ((fun a => σ a - σ' a) '' (s : Set A)) with hJ`. Establish `hmem : ∀ a : A, σ a - σ' a ∈ J`. Introduce `a`.

Establish `ha : a ∈ Submodule.span ℤ (s : Set A)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem y hy => exact Ideal.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz`.

Establish `: σ (y + z) - σ' (y + z) = (σ y - σ' y) + (σ z - σ' z)`. Rewrite using `[map_add, map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `J.add_mem hy hz`.

Consider the case `smul n y _ hy`. Establish `: σ (n • y) - σ' (n • y) = (n : O) * (σ y - σ' y)`. Simplify using `[zsmul_eq_mul, mul_sub]`. Rewrite using `[this]`. Conclude with `J.mul_mem_left _ hy`.

Establish `hgk : (g : IsLocalRing.ResidueField O) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]`. Conclude with `hgm`. Establish `hle : J ≤ Ideal.span {(g : O)} • J`. Rewrite using `[hJ, Ideal.span_le]`.

Introduce and unpack `_ ⟨a, -, rfl⟩`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp (hA a)`. Establish `hc1 : σ c * g = σ a ^ g - σ a`. Rewrite using `[← map_natCast σ g, ← map_mul, hc, map_sub, map_pow]`. Establish `hc2 : σ' c * g = σ' a ^ g - σ' a`.

Rewrite using `[← map_natCast σ' g, ← map_mul, hc, map_sub, map_pow]`. Establish `hgeom` using `geom_sum₂_mul (σ a) (σ' a) g`. Establish `key : (σ a - σ' a) * ((∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) - 1) = (g : O) * (σ c - σ' c)`. Take the linear combination `hgeom - hc1 + hc2`. Establish `hr : IsLocalRing.residue O (σ' a) = IsLocalRing.residue O (σ a)`.

Rewrite using `[eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon a))`. Establish `hS : (∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sum]`. Repeatedly rewrite using `[map_mul, map_pow, hr, ← pow_add]`.

Rewrite using `[Finset.sum_congr rfl (g := fun _ => IsLocalRing.residue O (σ a) ^ (g - 1)) (fun i hi => by have := Finset.mem_range.mp hi; congr 1; omega)]`. Rewrite using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul, hgk, zero_mul]`. Establish `hu : IsUnit ((∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) - 1)`. Assume the negation of the conclusion as `hu`. Establish `h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O`.

Use `Ideal.sub_mem _ hS ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))` as an intermediate fact. Simplify using `using this`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)`. Establish `: σ a - σ' a = ((g : O) * (σ c - σ' c)) * ↑hu.unit⁻¹`. Rewrite using `[← key, mul_assoc, IsUnit.mul_val_inv, mul_one]`.

Use `show σ a - σ' a ∈ (Ideal.span {(g : O)} • J : Ideal O)`. Rewrite using `[this, Ideal.smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (hmem c))`. Establish `hfg : J.FG` using `by classical`. Conclude with `⟨s.image (fun a => σ a - σ' a), by rw [Finset.coe_image]⟩`.

Establish `hjac : Ideal.span {(g : O)} ≤ (⊥ : Ideal O).jacobson`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Conclude with `hspan`. Establish `hbot` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ J hfg hle hjac`. Use extensionality with `a`.

Use `hmem a` as an intermediate fact. Rewrite `this` using `[hbot]`. Conclude with `sub_eq_zero.mp ((Submodule.mem_bot _).mp this)`.
-/
theorem _root_.GlobalTheory.exists_isUnit_sub_of_ringHom_ne : ∀ (A O : Type) [CommRing A] [Module.Finite ℤ A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ σ σ' : A →+* O, σ ≠ σ' → ∃ a : A, IsUnit (σ a - σ' a) := by
  intro A O _ _ _ _ g hg hgO hA σ σ' hne
  by_contra hcon
  push_neg at hcon
  apply hne
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hgO)
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := A)
  set J : Ideal O := Ideal.span ((fun a => σ a - σ' a) '' (s : Set A)) with hJ
  have hmem : ∀ a : A, σ a - σ' a ∈ J := by
    intro a
    have ha : a ∈ Submodule.span ℤ (s : Set A) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem y hy => exact Ideal.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
        have : σ (y + z) - σ' (y + z) = (σ y - σ' y) + (σ z - σ' z) := by
          rw [map_add, map_add]; ring
        rw [this]
        exact J.add_mem hy hz
    | smul n y _ hy =>
        have : σ (n • y) - σ' (n • y) = (n : O) * (σ y - σ' y) := by
          simp [zsmul_eq_mul, mul_sub]
        rw [this]
        exact J.mul_mem_left _ hy
  have hgk : (g : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact hgm
  have hle : J ≤ Ideal.span {(g : O)} • J := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨a, -, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hA a)
    have hc1 : σ c * g = σ a ^ g - σ a := by
      rw [← map_natCast σ g, ← map_mul, hc, map_sub, map_pow]
    have hc2 : σ' c * g = σ' a ^ g - σ' a := by
      rw [← map_natCast σ' g, ← map_mul, hc, map_sub, map_pow]
    have hgeom := geom_sum₂_mul (σ a) (σ' a) g
    have key : (σ a - σ' a) * ((∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) - 1) =
        (g : O) * (σ c - σ' c) := by
      linear_combination hgeom - hc1 + hc2
    have hr : IsLocalRing.residue O (σ' a) = IsLocalRing.residue O (σ a) := by
      rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon a))
    have hS : (∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) ∈
        IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sum]
      simp_rw [map_mul, map_pow, hr, ← pow_add]
      rw [Finset.sum_congr rfl (g := fun _ => IsLocalRing.residue O (σ a) ^ (g - 1))
        (fun i hi => by have := Finset.mem_range.mp hi; congr 1; omega)]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hgk, zero_mul]
    have hu : IsUnit ((∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) - 1) := by
      by_contra hu
      have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
        have := Ideal.sub_mem _ hS
          ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))
        simpa using this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have : σ a - σ' a = ((g : O) * (σ c - σ' c)) * ↑hu.unit⁻¹ := by
      rw [← key, mul_assoc, IsUnit.mul_val_inv, mul_one]
    show σ a - σ' a ∈ (Ideal.span {(g : O)} • J : Ideal O)
    rw [this, Ideal.smul_eq_mul]
    exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (hmem c))
  have hfg : J.FG := by
    classical
    exact ⟨s.image (fun a => σ a - σ' a), by rw [Finset.coe_image]⟩
  have hjac : Ideal.span {(g : O)} ≤ (⊥ : Ideal O).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hspan
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ J hfg hle hjac
  ext a
  have := hmem a
  rw [hbot] at this
  exact sub_eq_zero.mp ((Submodule.mem_bot _).mp this)

end GlobalTheory
