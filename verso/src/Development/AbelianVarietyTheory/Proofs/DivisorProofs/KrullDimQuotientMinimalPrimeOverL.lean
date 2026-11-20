import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

namespace GlobalTheory

universe u

/- English proof (translation)
Establish `hqp` using `hq.1.1`. Establish `: Algebra.FiniteType k (A ⧸ q)` using `.of_restrictScalars_finiteType R k _`. Take `⟨s, g, hg, hint⟩` from `exists_integral_inj_algHom_of_fg k (A ⧸ q)`. Use `choose x hx using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))`. Set `φ : (MvPolynomial (Fin s) R) →ₐ[R] A` to `MvPolynomial.aeval x`.

Establish `hφ (r : (MvPolynomial (Fin s) R)) : Ideal.Quotient.mk q (φ r) = g (MvPolynomial.map (algebraMap R k) r)`. Establish `: (Ideal.Quotient.mk q).comp φ.toRingHom = g.toRingHom.comp (MvPolynomial.map (algebraMap R k))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]`.

Rewrite using `[← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression. Introduce `i`. Simplify using `[φ, hx]`. Conclude with `congr($this r)`.

Establish `hmem (r : (MvPolynomial (Fin s) R)) : φ r ∈ q ↔ MvPolynomial.C ϖ ∣ r`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg, ← RingHom.mem_ker, MvPolynomial.ker_map, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`. Establish `hϖA : algebraMap R A ϖ ≠ 0`. Introduce `h`. Conclude with `hϖ0 ((FaithfulSMul.algebraMap_injective R A) (h.trans (map_zero _).symm))`.

Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr`. Assume the negation of the conclusion as `hr0`. Establish `hnu : ¬ IsUnit (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R))` using `fun h ↦ hqp.ne_top <| Ideal.eq_top_of_isUnit_mem _ ((hmem _).mpr dvd_rfl) (h.map φ)`.

Take `⟨n, a, ha, rfl⟩` from `WfDvdMonoid.max_power_factor' hr0 hnu`. Rewrite `hr` using `[map_mul, map_pow, MvPolynomial.algHom_C, mul_eq_zero]`. Break down `hr with hr | hr` into its components or cases. Conclude with `hϖA (pow_eq_zero_iff'.mp hr).1`. Conclude with `ha ((hmem a).mp (hr ▸ q.zero_mem))`.

Set `` to `φ.toRingHom.toAlgebra`. Establish `: IsScalarTower R (MvPolynomial (Fin s) R) A` using `IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm`. Establish `: FaithfulSMul (MvPolynomial (Fin s) R) A` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Establish `: Algebra.FiniteType (MvPolynomial (Fin s) R) A` using `.of_restrictScalars_finiteType R (MvPolynomial (Fin s) R) A`. Set `` to `g.toRingHom.toAlgebra`.

Establish `: IsScalarTower k (MvPolynomial (Fin s) k) (A ⧸ q)` using `IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm`. Establish `: FaithfulSMul (MvPolynomial (Fin s) k) (A ⧸ q)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hg`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin s) k) (A ⧸ q)` using `⟨hint⟩`. Establish `: Algebra.QuasiFiniteAt (MvPolynomial (Fin s) R) q`. Use `quasiFiniteAt_of_isolated (MvPolynomial (Fin s) R) A q (fun q' hq' h hle ↦ ?_) (fun q' hq' h hle ↦ ?_)` and prove the remaining obligations.

Use `hle.antisymm (hq.2 ⟨hq', ?_⟩ hle)` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Establish `: (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) ∈ q'.under (MvPolynomial (Fin s) R)` using `h.ge ((hmem _).mpr dvd_rfl)`. Establish `: φ (MvPolynomial.C ϖ) ∈ q'` using `this`. Simplify using `using this`.

Establish `: q'.map (Ideal.Quotient.mk q) = ⊥`. Use `Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin s) k) (eq_bot_iff.mpr ?_)` and prove the remaining obligations. Introduce `y hy`. Take `⟨r, rfl⟩` from `MvPolynomial.map_surjective _ hk y`. Establish `hy : g (MvPolynomial.map (algebraMap R k) r) ∈ q'.map (Ideal.Quotient.mk q)` using `hy`.

Rewrite `hy` using `[← hφ, Ideal.mem_quotient_iff_mem hle]`. Establish `: φ r ∈ q` using `h.le (show r ∈ q'.under (MvPolynomial (Fin s) R) from hy)`. Rewrite `this` using `[← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg]`. Conclude with `this`. Rewrite `this` using `[Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]`.

Conclude with `this.antisymm hle`. Use `isAlgebraic_of_quasiFiniteAt (MvPolynomial (Fin s) R) A q` as an intermediate fact. Rewrite using `[trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k), trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin s) R) A, MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain]`.
-/
theorem trdeg_quotient_eq_of_mem_minimalPrimes_span (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (k : Type u) [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k)) {ϖ : R} (hϖ0 : ϖ ≠ 0)
    (hker : RingHom.ker (algebraMap R k) = Ideal.span {ϖ})
    {A : Type u} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    [FaithfulSMul R A] {q : Ideal A}
    (hq : q ∈ (Ideal.span {algebraMap R A ϖ}).minimalPrimes)
    [Algebra k (A ⧸ q)] [IsScalarTower R k (A ⧸ q)] :
    Algebra.trdeg k (A ⧸ q) = Algebra.trdeg R A := by
  have hqp := hq.1.1
  have : Algebra.FiniteType k (A ⧸ q) := .of_restrictScalars_finiteType R k _
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k (A ⧸ q)
  choose x hx using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let φ : (MvPolynomial (Fin s) R) →ₐ[R] A := MvPolynomial.aeval x
  have hφ (r : (MvPolynomial (Fin s) R)) :
      Ideal.Quotient.mk q (φ r) = g (MvPolynomial.map (algebraMap R k) r) := by
    have : (Ideal.Quotient.mk q).comp φ.toRingHom =
        g.toRingHom.comp (MvPolynomial.map (algebraMap R k)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]
        rw [← IsScalarTower.algebraMap_apply]
        rfl
      · intro i
        simp [φ, hx]
    exact congr($this r)
  have hmem (r : (MvPolynomial (Fin s) R)) : φ r ∈ q ↔ MvPolynomial.C ϖ ∣ r := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg, ← RingHom.mem_ker,
      MvPolynomial.ker_map, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have hϖA : algebraMap R A ϖ ≠ 0 := by
    intro h
    exact hϖ0 ((FaithfulSMul.algebraMap_injective R A) (h.trans (map_zero _).symm))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hnu : ¬ IsUnit (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) := fun h ↦ hqp.ne_top <|
      Ideal.eq_top_of_isUnit_mem _ ((hmem _).mpr dvd_rfl) (h.map φ)
    obtain ⟨n, a, ha, rfl⟩ := WfDvdMonoid.max_power_factor' hr0 hnu
    rw [map_mul, map_pow, MvPolynomial.algHom_C, mul_eq_zero] at hr
    rcases hr with hr | hr
    · exact hϖA (pow_eq_zero_iff'.mp hr).1
    · exact ha ((hmem a).mp (hr ▸ q.zero_mem))
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin s) R) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) R) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.FiniteType (MvPolynomial (Fin s) R) A :=
    .of_restrictScalars_finiteType R (MvPolynomial (Fin s) R) A
  let := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) (A ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) (A ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (A ⧸ q) := ⟨hint⟩
  have : Algebra.QuasiFiniteAt (MvPolynomial (Fin s) R) q := by
    refine quasiFiniteAt_of_isolated (MvPolynomial (Fin s) R) A q
      (fun q' hq' h hle ↦ ?_) (fun q' hq' h hle ↦ ?_)
    · refine hle.antisymm (hq.2 ⟨hq', ?_⟩ hle)
      rw [Ideal.span_singleton_le_iff_mem]
      have : (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) ∈ q'.under (MvPolynomial (Fin s) R) :=
        h.ge ((hmem _).mpr dvd_rfl)
      have : φ (MvPolynomial.C ϖ) ∈ q' := this
      simpa using this
    · have : q'.map (Ideal.Quotient.mk q) = ⊥ := by
        refine Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin s) k) (eq_bot_iff.mpr ?_)
        intro y hy
        obtain ⟨r, rfl⟩ := MvPolynomial.map_surjective _ hk y
        have hy : g (MvPolynomial.map (algebraMap R k) r) ∈ q'.map (Ideal.Quotient.mk q) := hy
        rw [← hφ, Ideal.mem_quotient_iff_mem hle] at hy
        have : φ r ∈ q := h.le (show r ∈ q'.under (MvPolynomial (Fin s) R) from hy)
        rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg] at this
        exact this
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at this
      exact this.antisymm hle
  have := isAlgebraic_of_quasiFiniteAt (MvPolynomial (Fin s) R) A q
  rw [trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k),
    trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin s) R) A,
    MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain]

/- English proof (translation)
Establish `hk : Function.Surjective (algebraMap ℤ (ZMod l))` using `ZMod.intCast_surjective`. Establish `hker : RingHom.ker (algebraMap ℤ (ZMod l)) = Ideal.span {(l : ℤ)}`. Rewrite using `[algebraMap_int_eq]`. Conclude with `ZMod.ker_intCastRingHom l`. Establish `hl0 : (l : ℤ) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`.

Establish `: FaithfulSMul ℤ A` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr (by rw [algebraMap_int_eq]; exact Int.cast_injective)`. Establish `hq' : q ∈ (Ideal.span {algebraMap ℤ A (l : ℤ)}).minimalPrimes` using `by simpa using hq`. Establish `hlq : (l : A) ∈ q` using `hq.1.2 (Ideal.mem_span_singleton_self _)`. Establish `hle : RingHom.ker (algebraMap ℤ (ZMod l)) ≤ RingHom.ker (algebraMap ℤ (A ⧸ q))`. Rewrite using `[hker, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, IsScalarTower.algebraMap_apply ℤ A (A ⧸ q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`.

Simplify using `using hlq`. Set `` to `((algebraMap ℤ (ZMod l)).liftOfSurjective hk ⟨_, hle⟩).toAlgebra`. Establish `: IsScalarTower ℤ (ZMod l) (A ⧸ q)` using `IsScalarTower.of_algebraMap_eq fun x ↦ (RingHom.liftOfSurjective_comp_apply _ hk ⟨_, hle⟩ x).symm`. Establish `: Algebra.FiniteType (ZMod l) (A ⧸ q)` using `.of_restrictScalars_finiteType ℤ _ _`. Use `ringKrullDim_eq_of_trdeg_eq (ZMod l) _ ?_` and prove the remaining obligations.

Rewrite using `[trdeg_quotient_eq_of_mem_minimalPrimes_span ℤ (ZMod l) hk hl0 hker hq', hd]`.
-/
theorem ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime (A : Type) [CommRing A]
    [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] (l : ℕ) [Fact l.Prime] (q : Ideal A)
    [q.IsPrime] (hq : q ∈ (Ideal.span {(l : A)}).minimalPrimes) (d : ℕ)
    (hd : Algebra.trdeg ℤ A = d) : ringKrullDim (A ⧸ q) = d := by
  have hk : Function.Surjective (algebraMap ℤ (ZMod l)) := ZMod.intCast_surjective
  have hker : RingHom.ker (algebraMap ℤ (ZMod l)) = Ideal.span {(l : ℤ)} := by
    rw [algebraMap_int_eq]; exact ZMod.ker_intCastRingHom l
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (by rw [algebraMap_int_eq]; exact Int.cast_injective)
  have hq' : q ∈ (Ideal.span {algebraMap ℤ A (l : ℤ)}).minimalPrimes := by simpa using hq
  have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hle : RingHom.ker (algebraMap ℤ (ZMod l)) ≤ RingHom.ker (algebraMap ℤ (A ⧸ q)) := by
    rw [hker, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply ℤ A (A ⧸ q), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    simpa using hlq
  let := ((algebraMap ℤ (ZMod l)).liftOfSurjective hk ⟨_, hle⟩).toAlgebra
  have : IsScalarTower ℤ (ZMod l) (A ⧸ q) := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.liftOfSurjective_comp_apply _ hk ⟨_, hle⟩ x).symm
  have : Algebra.FiniteType (ZMod l) (A ⧸ q) := .of_restrictScalars_finiteType ℤ _ _
  refine ringKrullDim_eq_of_trdeg_eq (ZMod l) _ ?_
  rw [trdeg_quotient_eq_of_mem_minimalPrimes_span ℤ (ZMod l) hk hl0 hker hq', hd]

end GlobalTheory
