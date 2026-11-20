import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Establish `h1 : x ^ (l ^ k) - 1 ∈ I` using `Ideal.pow_le_self (Nat.succ_ne_zero k) ih`. Rewrite using `[pow_succ l k, pow_mul, ← mul_geom_sum, pow_succ I (k + 1)]`.

Use `Ideal.mul_mem_mul ih ?_` and prove the remaining obligations. Rewrite `hl`, `h1`, the goal using `[← Ideal.Quotient.eq_zero_iff_mem]`. Rewrite `h1` using `[map_sub, map_one, sub_eq_zero]`. Rewrite using `[map_sum]`. Simplify using `only [map_pow (Ideal.Quotient.mk I) (x ^ (l ^ k)), h1, one_pow]`.

Simplify using `using hl`.
-/
private theorem pow_pow_sub_one_mem {R : Type} [CommRing R] (I : Ideal R) (l : ℕ) (hl : (l : R) ∈ I) (x : R)
    (hx : x - 1 ∈ I) (k : ℕ) : x ^ (l ^ k) - 1 ∈ I ^ (k + 1) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have h1 : x ^ (l ^ k) - 1 ∈ I := Ideal.pow_le_self (Nat.succ_ne_zero k) ih
    rw [pow_succ l k, pow_mul, ← mul_geom_sum, pow_succ I (k + 1)]
    refine Ideal.mul_mem_mul ih ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hl h1 ⊢
    rw [map_sub, map_one, sub_eq_zero] at h1
    rw [map_sum]
    simp only [map_pow (Ideal.Quotient.mk I) (x ^ (l ^ k)), h1, one_pow]
    simpa using hl

/- English proof (translation)
Introduce `l _ F R _ _ hl γ hγ N`. Use `haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact`. Use `set χ := pushCh (Ideal.Quotient.mk (maximalIdeal R ^ N)) γ with hχ`. Establish `hval : ∀ g, (χ g : R ⧸ maximalIdeal R ^ N) = Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R)` using `fun g => rfl`. Establish `hlc : IsLocallyConstant fun g => (χ g : R ⧸ maximalIdeal R ^ N)` using `hγ.cont N`.

Establish `hlc' : IsLocallyConstant χ` using `IsLocallyConstant.desc χ Units.val hlc Units.val_injective`. Establish `hfin : Finite χ.range` using `hlc'.range_finite.to_subtype`. Use `⟨χ.range, inferInstance, hfin, χ.rangeRestrict, χ.range.subtype, ?_, ?_, ?_, rfl⟩` and prove the remaining obligations. Introduce and unpack `⟨_, g, rfl⟩`. Use `⟨N, Subtype.ext (Units.ext ?_)⟩` and prove the remaining obligations.

Establish `h` using `Ideal.pow_le_pow_right (Nat.le_succ N) (pow_pow_sub_one_mem _ l hl _ (hγ.red g) N)`. Rewrite `h` using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, map_pow]`. Simplify `h` using `[hval]`. Rewrite using `[MonoidHom.ker_rangeRestrict]`. Conclude with `hlc'.isOpen_fiber 1`.

Use `hγ.toAnti.mono fun g hg => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]`. Rewrite `hg` using `[MonoidHom.mem_ker]`. Conclude with `Units.ext (by rw [hval, hg]; simp)`.
-/
theorem UpperTheory.V.Ws.H5.finQuot :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {R : Type} [CommRing R] [IsLocalRing R], ((l : ℕ) : R) ∈ maximalIdeal R → ∀ γ : F.G₀ →* Rˣ, TwCh F γ → ∀ N : ℕ, ∃ (Q : Type) (_ : CommGroup Q) (_ : Finite Q) (q : F.G₀ →* Q) (j : Q →* (R ⧸ maximalIdeal R ^ N)ˣ), IsPGroup l Q ∧ IsOpen (q.ker : Set F.G₀) ∧ Anti F q ∧ j.comp q = pushCh (Ideal.Quotient.mk (maximalIdeal R ^ N)) γ := by
  intro l _ F R _ _ hl γ hγ N
  haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  set χ := pushCh (Ideal.Quotient.mk (maximalIdeal R ^ N)) γ with hχ
  have hval : ∀ g, (χ g : R ⧸ maximalIdeal R ^ N) = Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R) := fun g => rfl
  have hlc : IsLocallyConstant fun g => (χ g : R ⧸ maximalIdeal R ^ N) := hγ.cont N
  have hlc' : IsLocallyConstant χ := IsLocallyConstant.desc χ Units.val hlc Units.val_injective
  have hfin : Finite χ.range := hlc'.range_finite.to_subtype
  refine ⟨χ.range, inferInstance, hfin, χ.rangeRestrict, χ.range.subtype, ?_, ?_, ?_, rfl⟩
  · rintro ⟨_, g, rfl⟩
    refine ⟨N, Subtype.ext (Units.ext ?_)⟩
    have h := Ideal.pow_le_pow_right (Nat.le_succ N) (pow_pow_sub_one_mem _ l hl _ (hγ.red g) N)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, map_pow] at h
    simpa [hval] using h
  · rw [MonoidHom.ker_rangeRestrict]
    exact hlc'.isOpen_fiber 1
  · refine hγ.toAnti.mono fun g hg => ?_
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hg
    exact Units.ext (by rw [hval, hg]; simp)
