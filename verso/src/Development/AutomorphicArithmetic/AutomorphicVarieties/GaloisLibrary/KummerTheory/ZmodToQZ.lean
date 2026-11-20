import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Introduce `l _ r`. Establish `hl : l.Prime` using `Fact.out`. Establish `hlr0 : ((l : ℚ_[l]) ^ r) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hl.ne_zero)`. Establish `zsm : ∀ (k : ℤ) (q : ℚ_[l]), k • QZ.mk l q = QZ.mk l ((k : ℚ_[l]) * q)`. Introduce `k q`.

Rewrite using `[← Int.cast_smul_eq_zsmul ℤ_[l]]`. Use `show QZ.mk l (((k : ℤ_[l]) : ℚ_[l]) * q) = _`. Rewrite using `[PadicInt.coe_intCast]`. Establish `hker : ((l ^ r : ℕ) : ℤ) • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0`. Rewrite using `[zsm]`.

Use `(Submodule.Quotient.mk_eq_zero (ZlSub l)).2 ⟨1, ?_⟩` and prove the remaining obligations. Use `push_cast`. Conclude with `(mul_inv_cancel₀ hlr0).symm`. Set `ι : ZMod (l ^ r) →+ QZ l` to `ZMod.lift (l ^ r) ⟨zmultiplesHom (QZ l) (QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹)), by`. Rewrite using `[zmultiplesHom_apply]`.

Conclude with `hker⟩`. Establish `hι : ∀ k : ℤ, ι (k : ZMod (l ^ r)) = QZ.mk l ((k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹)`. Introduce `k`. Simplify using `only [ι, ZMod.lift_coe, zmultiplesHom_apply]`. Conclude with `zsm k _`.

Establish `hkill : ∀ a : ZMod (l ^ r), (l ^ r : ℕ) • ι a = 0`. Introduce `a`. Rewrite using `[← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]`. Establish `h3 : ∀ (z : ℤ_[l]) (a : ZMod (l ^ r)), ι (PadicInt.toZModPow r z * a) = z • ι a`. Introduce `z a`.

Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec r z)`. Establish `hz : PadicInt.toZModPow r z = ((z.appr r : ℕ) : ZMod (l ^ r))` using `rfl`. Rewrite using `[hz, ← nsmul_eq_mul, map_nsmul]`. Establish `hzw : z = ((z.appr r : ℕ) : ℤ_[l]) + w * ((l ^ r : ℕ) : ℤ_[l])`. Use `push_cast`.

Rewrite using `[hw]`. Expand and normalize the polynomial expressions, which then agree. Use `conv_rhs => rw [hzw]`. Rewrite using `[add_smul, Nat.cast_smul_eq_nsmul, mul_smul, Nat.cast_smul_eq_nsmul, hkill, smul_zero, add_zero]`. Use `⟨ι, ?_, ?_, h3⟩` and prove the remaining obligations.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨k, rfl⟩` from `ZMod.intCast_surjective a`. Rewrite `ha` using `[hι]`. Take `⟨y, hy⟩` from `(Submodule.Quotient.mk_eq_zero (ZlSub l)).1 ha`.

Establish `hy' : (y : ℚ_[l]) = (k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹` using `hy`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `hky : (k : ℤ_[l]) = y * (l : ℤ_[l]) ^ r`. Apply `PadicInt.ext` to reduce the goal to its premises. Use `push_cast`.

Rewrite using `[hy', mul_assoc, inv_mul_cancel₀ hlr0, mul_one]`. Establish `hn : ‖(k : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ))`. Rewrite using `[hky, norm_mul, PadicInt.norm_p_pow]`. Conclude with `mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one y)`. Establish `hd` using `PadicInt.norm_int_le_pow_iff_dvd.1 hn`.

Conclude with `hd` after adjusting the coercions. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Establish `h` using `h3 ((l : ℤ_[l]) ^ r) a`.

Rewrite `h` using `[map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, map_zero]`. Conclude with `h.symm`. Introduce `hx`. Take `⟨q, rfl⟩` from `Submodule.Quotient.mk_surjective (ZlSub l) x`. Establish `hx' : QZ.mk l ((((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q) = 0` using `hx`.

Take `⟨z, hz⟩` from `(Submodule.Quotient.mk_eq_zero (ZlSub l)).1 hx'`. Establish `hz' : (z : ℚ_[l]) = (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q` using `hz`. Move the coercions through the operations in `at hz'`. Use `⟨PadicInt.toZModPow r z, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_one (PadicInt.toZModPow r z), h3, show (1 : ZMod (l ^ r)) = ((1 : ℤ) : ZMod (l ^ r)) by simp, hι]`.

Use `show QZ.mk l ((z : ℚ_[l]) * (((1 : ℤ) : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹)) = Submodule.Quotient.mk q`. Use `congr 1`. Rewrite using `[hz']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.V.Kum.zmodToQZ :
    ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧ (∀ x, x ∈ Set.range ι ↔ (l : ℤ_[l]) ^ r • x = 0) ∧
    ∀ (z : ℤ_[l]) (a : ZMod (l ^ r)), ι (PadicInt.toZModPow r z * a) = z • ι a := by
  intro l _ r
  have hl : l.Prime := Fact.out
  have hlr0 : ((l : ℚ_[l]) ^ r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have zsm : ∀ (k : ℤ) (q : ℚ_[l]), k • QZ.mk l q = QZ.mk l ((k : ℚ_[l]) * q) := by
    intro k q
    rw [← Int.cast_smul_eq_zsmul ℤ_[l]]
    show QZ.mk l (((k : ℤ_[l]) : ℚ_[l]) * q) = _
    rw [PadicInt.coe_intCast]
  have hker : ((l ^ r : ℕ) : ℤ) • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0 := by
    rw [zsm]
    refine (Submodule.Quotient.mk_eq_zero (ZlSub l)).2 ⟨1, ?_⟩
    push_cast
    exact (mul_inv_cancel₀ hlr0).symm
  let ι : ZMod (l ^ r) →+ QZ l :=
    ZMod.lift (l ^ r) ⟨zmultiplesHom (QZ l) (QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹)), by
      rw [zmultiplesHom_apply]
      exact hker⟩
  have hι : ∀ k : ℤ, ι (k : ZMod (l ^ r)) = QZ.mk l ((k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹) := by
    intro k
    simp only [ι, ZMod.lift_coe, zmultiplesHom_apply]
    exact zsm k _
  have hkill : ∀ a : ZMod (l ^ r), (l ^ r : ℕ) • ι a = 0 := by
    intro a
    rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]
  have h3 : ∀ (z : ℤ_[l]) (a : ZMod (l ^ r)), ι (PadicInt.toZModPow r z * a) = z • ι a := by
    intro z a
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec r z)
    have hz : PadicInt.toZModPow r z = ((z.appr r : ℕ) : ZMod (l ^ r)) := rfl
    rw [hz, ← nsmul_eq_mul, map_nsmul]
    have hzw : z = ((z.appr r : ℕ) : ℤ_[l]) + w * ((l ^ r : ℕ) : ℤ_[l]) := by
      push_cast
      rw [hw]
      ring
    conv_rhs => rw [hzw]
    rw [add_smul, Nat.cast_smul_eq_nsmul, mul_smul, Nat.cast_smul_eq_nsmul, hkill, smul_zero, add_zero]
  refine ⟨ι, ?_, ?_, h3⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    rw [hι] at ha
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero (ZlSub l)).1 ha
    have hy' : (y : ℚ_[l]) = (k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹ := hy
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hky : (k : ℤ_[l]) = y * (l : ℤ_[l]) ^ r := by
      apply PadicInt.ext
      push_cast
      rw [hy', mul_assoc, inv_mul_cancel₀ hlr0, mul_one]
    have hn : ‖(k : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
      rw [hky, norm_mul, PadicInt.norm_p_pow]
      exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one y)
    have hd := PadicInt.norm_int_le_pow_iff_dvd.1 hn
    exact_mod_cast hd
  · intro x
    constructor
    · rintro ⟨a, rfl⟩
      have h := h3 ((l : ℤ_[l]) ^ r) a
      rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, map_zero] at h
      exact h.symm
    · intro hx
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) x
      have hx' : QZ.mk l ((((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q) = 0 := hx
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero (ZlSub l)).1 hx'
      have hz' : (z : ℚ_[l]) = (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q := hz
      push_cast at hz'
      refine ⟨PadicInt.toZModPow r z, ?_⟩
      rw [← mul_one (PadicInt.toZModPow r z), h3, show (1 : ZMod (l ^ r)) = ((1 : ℤ) : ZMod (l ^ r)) by simp, hι]
      show QZ.mk l ((z : ℚ_[l]) * (((1 : ℤ) : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹)) = Submodule.Quotient.mk q
      congr 1
      rw [hz']
      push_cast
      field_simp
