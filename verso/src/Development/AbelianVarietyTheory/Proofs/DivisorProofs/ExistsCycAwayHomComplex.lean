import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

open GlobalTheory.SiegelTor Polynomial

namespace GlobalTheory.SiegelTor

/- English proof (translation)
The claim follows from `IsPrimitiveRoot.of_map_of_injective (f := (cycAway N).subtype) (Complex.isPrimitiveRoot_exp N hN) Subtype.val_injective`.
-/
theorem isPrimitiveRoot_zetaAway {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zetaAway N) N :=
  IsPrimitiveRoot.of_map_of_injective (f := (cycAway N).subtype) (Complex.isPrimitiveRoot_exp N hN) Subtype.val_injective

/- English proof (translation)
Use extensionality with `⟨x, hx⟩`. Establish `hN' : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | rfl` into its components or cases.

Conclude with `h`. Establish `e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1` using `Subtype.ext (by simpa using mul_inv_cancel₀ hN')`. Establish `e₁` using `congrArg β e`. Establish `e₂` using `congrArg β' e`. Rewrite `e₁`, `e₂` using `[map_mul, map_natCast, map_one]`.

Conclude with `left_inv_eq_right_inv (by rw [mul_comm]; exact e₁) e₂`. Consider the case `zero => exact (map_zero β).trans (map_zero β').symm`. Consider the case `one => exact (map_one β).trans (map_one β').symm`. Consider the case `add x y hx hy ihx ihy`. Conclude with `(map_add β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_add β' ⟨x, hx⟩ ⟨y, hy⟩).symm)`.

Consider the case `neg x hx ih => exact (map_neg β ⟨x, hx⟩).trans ((congrArg _ ih).trans (map_neg β' ⟨x, hx⟩).symm)`. Consider the case `mul x y hx hy ihx ihy`. Conclude with `(map_mul β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_mul β' ⟨x, hx⟩ ⟨y, hy⟩).symm)`.
-/
theorem cycAway_hom_ext {N : ℕ} (hN : N ≠ 0) {R : Type*} [CommRing R] {β β' : cycAway N →+* R}
    (h : β (zetaAway N) = β' (zetaAway N)) : β = β' := by
  ext ⟨x, hx⟩
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · have e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
        Subtype.ext (by simpa using mul_inv_cancel₀ hN')
      have e₁ := congrArg β e
      have e₂ := congrArg β' e
      rw [map_mul, map_natCast, map_one] at e₁ e₂
      exact left_inv_eq_right_inv (by rw [mul_comm]; exact e₁) e₂
  | zero => exact (map_zero β).trans (map_zero β').symm
  | one => exact (map_one β).trans (map_one β').symm
  | add x y hx hy ihx ihy =>
    exact (map_add β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_add β' ⟨x, hx⟩ ⟨y, hy⟩).symm)
  | neg x hx ih => exact (map_neg β ⟨x, hx⟩).trans ((congrArg _ ih).trans (map_neg β' ⟨x, hx⟩).symm)
  | mul x y hx hy ihx ihy =>
    exact (map_mul β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_mul β' ⟨x, hx⟩ ⟨y, hy⟩).symm)

/- English proof (translation)
Establish `hp` using `Nat.pos_of_ne_zero hN`. Establish `hz : IsPrimitiveRoot (zetaAway N : ℂ) N` using `Complex.isPrimitiveRoot_exp N hN`. Establish `hi : IsIntegral ℚ (zetaAway N : ℂ)` using `(hz.isIntegral hp).tower_top`. Set `K` to `IntermediateField.adjoin ℚ {(zetaAway N : ℂ)}`. Establish `hle : cycAway N ≤ K.toSubfield.toSubring`.

Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`. Conclude with `IntermediateField.mem_adjoin_simple_self ℚ _`. Conclude with `K.inv_mem (natCast_mem K N)`. Establish `hr : μ ∈ (minpoly ℚ (zetaAway N : ℂ)).aroots ℂ`.

Rewrite using `[← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]`. Use `⟨cyclotomic_ne_zero N ℚ, ?_⟩` and prove the remaining obligations. Rewrite using `[cyclotomic_eq_minpoly_rat hμ hp]`. Conclude with `minpoly.aeval ℚ μ`. Set `g : K →ₐ[ℚ] ℂ` to `(IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨μ, hr⟩`.

Establish `hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway N : ℂ)) = μ` using `IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨μ, hr⟩`. Conclude with `⟨g.toRingHom.comp (Subring.inclusion hle), hg⟩`.
-/
theorem exists_cycAway_hom_complex {N : ℕ} (hN : N ≠ 0) {μ : ℂ} (hμ : IsPrimitiveRoot μ N) :
    ∃ f : cycAway N →+* ℂ, f (zetaAway N) = μ := by
  have hp := Nat.pos_of_ne_zero hN
  have hz : IsPrimitiveRoot (zetaAway N : ℂ) N := Complex.isPrimitiveRoot_exp N hN
  have hi : IsIntegral ℚ (zetaAway N : ℂ) := (hz.isIntegral hp).tower_top
  let K := IntermediateField.adjoin ℚ {(zetaAway N : ℂ)}
  have hle : cycAway N ≤ K.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
    · exact K.inv_mem (natCast_mem K N)
  have hr : μ ∈ (minpoly ℚ (zetaAway N : ℂ)).aroots ℂ := by
    rw [← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]
    refine ⟨cyclotomic_ne_zero N ℚ, ?_⟩
    rw [cyclotomic_eq_minpoly_rat hμ hp]
    exact minpoly.aeval ℚ μ
  let g : K →ₐ[ℚ] ℂ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨μ, hr⟩
  have hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway N : ℂ)) = μ :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨μ, hr⟩
  exact ⟨g.toRingHom.comp (Subring.inclusion hle), hg⟩

/- English proof (translation)
Establish `hz : IsPrimitiveRoot (zetaAway N : ℂ) N` using `Complex.isPrimitiveRoot_exp N hN`. Take `⟨f, hf⟩` from `exists_cycAway_hom_complex hN (hz.pow_of_coprime m hm)`. Establish `hN' : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN`. Establish `hmem : ∀ x, f x ∈ cycAway N`. Introduce and unpack `⟨x, hx⟩`.

Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | rfl` into its components or cases. Conclude with `hf ▸ pow_mem (zetaAway N).2 m`. Establish `e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1` using `Subtype.ext (by simpa using mul_inv_cancel₀ hN')`.

Establish `e₁` using `congrArg f e`. Rewrite `e₁` using `[map_mul, map_natCast, map_one]`. Conclude with `Set.mem_of_eq_of_mem (eq_inv_of_mul_eq_one_right e₁) (Subring.subset_closure (Or.inr rfl))`. Consider the case `zero => exact Set.mem_of_eq_of_mem (map_zero f) (zero_mem (cycAway N))`. Consider the case `one => exact Set.mem_of_eq_of_mem (map_one f) (one_mem (cycAway N))`.

Consider the case `add x y hx hy ihx ihy => exact (map_add f ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy`. Consider the case `neg x hx ih => exact (map_neg f ⟨x, hx⟩) ▸ neg_mem ih`. Consider the case `mul x y hx hy ihx ihy => exact (map_mul f ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy`. Conclude with `⟨f.codRestrict (cycAway N) hmem, Subtype.ext hf⟩`.
-/
theorem exists_cycAway_end {N : ℕ} (hN : N ≠ 0) {m : ℕ} (hm : m.Coprime N) :
    ∃ f : cycAway N →+* cycAway N, f (zetaAway N) = zetaAway N ^ m := by
  have hz : IsPrimitiveRoot (zetaAway N : ℂ) N := Complex.isPrimitiveRoot_exp N hN
  obtain ⟨f, hf⟩ := exists_cycAway_hom_complex hN (hz.pow_of_coprime m hm)
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hmem : ∀ x, f x ∈ cycAway N := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hf ▸ pow_mem (zetaAway N).2 m
      · have e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ hN')
        have e₁ := congrArg f e
        rw [map_mul, map_natCast, map_one] at e₁
        exact Set.mem_of_eq_of_mem (eq_inv_of_mul_eq_one_right e₁) (Subring.subset_closure (Or.inr rfl))
    | zero => exact Set.mem_of_eq_of_mem (map_zero f) (zero_mem (cycAway N))
    | one => exact Set.mem_of_eq_of_mem (map_one f) (one_mem (cycAway N))
    | add x y hx hy ihx ihy => exact (map_add f ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy
    | neg x hx ih => exact (map_neg f ⟨x, hx⟩) ▸ neg_mem ih
    | mul x y hx hy ihx ihy => exact (map_mul f ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy
  exact ⟨f.codRestrict (cycAway N) hmem, Subtype.ext hf⟩

/- English proof (translation)
Establish `hz` using `isPrimitiveRoot_zetaAway hN`. Establish `: NeZero N` using `⟨hN⟩`. Take `⟨k, -, hk⟩` from `(hz.pow_of_coprime m hm).eq_pow_of_pow_eq_one hz.pow_eq_one`. Establish `hkc : k.Coprime N`. Rewrite using `[← (hz.pow_of_coprime m hm).pow_iff_coprime (Nat.pos_of_ne_zero hN), hk]`.

Conclude with `hz`. Take `⟨f, hf⟩` from `exists_cycAway_end hN hm`. Take `⟨g, hg⟩` from `exists_cycAway_end hN hkc`. Use `⟨RingEquiv.ofRingHom f g (cycAway_hom_ext hN ?_) (cycAway_hom_ext hN ?_), hf⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hg, map_pow, hf, hk, RingHom.id_apply]`.

Rewrite using `[RingHom.comp_apply, hf, map_pow, hg, ← pow_mul, mul_comm, pow_mul, hk, RingHom.id_apply]`.
-/
theorem exists_cycAway_aut {N : ℕ} (hN : N ≠ 0) {m : ℕ} (hm : m.Coprime N) :
    ∃ σ : cycAway N ≃+* cycAway N, σ (zetaAway N) = zetaAway N ^ m := by
  have hz := isPrimitiveRoot_zetaAway hN
  have : NeZero N := ⟨hN⟩
  obtain ⟨k, -, hk⟩ := (hz.pow_of_coprime m hm).eq_pow_of_pow_eq_one hz.pow_eq_one
  have hkc : k.Coprime N := by
    rw [← (hz.pow_of_coprime m hm).pow_iff_coprime (Nat.pos_of_ne_zero hN), hk]; exact hz
  obtain ⟨f, hf⟩ := exists_cycAway_end hN hm
  obtain ⟨g, hg⟩ := exists_cycAway_end hN hkc
  refine ⟨RingEquiv.ofRingHom f g (cycAway_hom_ext hN ?_) (cycAway_hom_ext hN ?_), hf⟩
  · rw [RingHom.comp_apply, hg, map_pow, hf, hk, RingHom.id_apply]
  · rw [RingHom.comp_apply, hf, map_pow, hg, ← pow_mul, mul_comm, pow_mul, hk, RingHom.id_apply]

/- English proof (translation)
Establish `hp` using `Nat.pos_of_ne_zero hN`. Establish `: NeZero N` using `⟨hN⟩`. Establish `hz` using `isPrimitiveRoot_zetaAway hN`. Establish `h₁` using `isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β)`. Establish `h₂` using `isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β')`.

Take `⟨i, hi, he⟩` from `h₁.eq_pow_of_pow_eq_one h₂.pow_eq_one`. Use `⟨i, by rw [← h₁.pow_iff_coprime hp, he]; exact h₂, ?_⟩` and prove the remaining obligations. Establish `hprod : ∏ k ∈ Finset.range N, (β' (zetaAway N) - β (zetaAway N) ^ k) = 0`. Establish `e` using `congrArg (fun p => (p.map β).eval (β' (zetaAway N))) (X_pow_sub_C_eq_prod hz hp (one_pow N))`. Simplify using `only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, Polynomial.map_prod, eval_prod, eval_sub, eval_pow, eval_X, eval_C, mul_one, map_one, map_pow, Polynomial.map_one, eval_one] at e`.

Rewrite using `[← e, ← map_pow, hz.pow_eq_one, map_one, sub_self]`. Rewrite `hprod` using `[← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi)]`. Establish `hu : IsUnit (∏ k ∈ (Finset.range N).erase i, (β' (zetaAway N) - β (zetaAway N) ^ k))`. Use `IsUnit.prod_iff.2 fun k hk => ?_` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, map_pow, sub_ne_zero]`.

Introduce `h`. Take `⟨hki, hk⟩` from `Finset.mem_erase.1 hk`. Conclude with `hki (h₁.pow_inj (Finset.mem_range.1 hk) hi (h.symm.trans he.symm))`. Conclude with `sub_eq_zero.1 (hu.mul_left_eq_zero.1 hprod)`.
-/
theorem exists_pow_of_isLocalRing {N : ℕ} (hN : N ≠ 0) {R : Type} [CommRing R] [IsLocalRing R]
    (β β' : cycAway N →+* R) : ∃ m : ℕ, m.Coprime N ∧ β' (zetaAway N) = β (zetaAway N) ^ m := by
  classical
  have hp := Nat.pos_of_ne_zero hN
  have : NeZero N := ⟨hN⟩
  have hz := isPrimitiveRoot_zetaAway hN
  have h₁ := isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β)
  have h₂ := isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β')
  obtain ⟨i, hi, he⟩ := h₁.eq_pow_of_pow_eq_one h₂.pow_eq_one
  refine ⟨i, by rw [← h₁.pow_iff_coprime hp, he]; exact h₂, ?_⟩
  have hprod : ∏ k ∈ Finset.range N, (β' (zetaAway N) - β (zetaAway N) ^ k) = 0 := by
    have e := congrArg (fun p => (p.map β).eval (β' (zetaAway N))) (X_pow_sub_C_eq_prod hz hp (one_pow N))
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, Polynomial.map_prod, eval_prod, eval_sub, eval_pow,
      eval_X, eval_C, mul_one, map_one, map_pow, Polynomial.map_one, eval_one] at e
    rw [← e, ← map_pow, hz.pow_eq_one, map_one, sub_self]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi)] at hprod
  have hu : IsUnit (∏ k ∈ (Finset.range N).erase i, (β' (zetaAway N) - β (zetaAway N) ^ k)) := by
    refine IsUnit.prod_iff.2 fun k hk => ?_
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, map_pow, sub_ne_zero]
    intro h
    obtain ⟨hki, hk⟩ := Finset.mem_erase.1 hk
    exact hki (h₁.pow_inj (Finset.mem_range.1 hk) hi (h.symm.trans he.symm))
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 hprod)

/- English proof (translation)
Introduce `_ hN` and use `⟨fun _ hm => exists_cycAway_aut hN hm, fun _ _ _ _ h => cycAway_hom_ext hN h, fun _ _ _ β β' => exists_pow_of_isLocalRing hN β β'⟩`.
-/
theorem cycAway_galois : ∀ N : ℕ, N ≠ 0 → (∀ m : ℕ, m.Coprime N → ∃ σ : cycAway N ≃+* cycAway N, σ (zetaAway N) = zetaAway N ^ m) ∧ (∀ (R : Type) [CommRing R] (β β' : cycAway N →+* R), β (zetaAway N) = β' (zetaAway N) → β = β') ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (β β' : cycAway N →+* R), ∃ m : ℕ, m.Coprime N ∧ β' (zetaAway N) = β (zetaAway N) ^ m :=
  fun _ hN => ⟨fun _ hm => exists_cycAway_aut hN hm, fun _ _ _ _ h => cycAway_hom_ext hN h,
    fun _ _ _ β β' => exists_pow_of_isLocalRing hN β β'⟩

end GlobalTheory.SiegelTor
