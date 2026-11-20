import Mathlib

open Polynomial

namespace FunctorialResolution.Blowup

variable {R : Type*} [CommRing R]

/- English proof (translation)
Rewrite using `[pow_one]` and apply the resulting hypothesis.
-/
private theorem mem_pow_one (I : Ideal R) {a : R} (ha : a ∈ I) : a ∈ I ^ 1 := by
  rwa [pow_one]

/- English proof (translation)
Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`.
-/
private theorem mem_pow_zero (I : Ideal R) (r : R) : r ∈ I ^ 0 := by
  rw [pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

noncomputable def reesGrading (I : Ideal R) (n : ℕ) : Submodule R ↥(reesAlgebra I) :=
  Submodule.comap (reesAlgebra I).val.toLinearMap
    (LinearMap.range (Polynomial.monomial (R := R) n))

/- English proof (translation)
Establish `hmem : p ∈ reesGrading I n ↔ ∃ r : R, Polynomial.monomial n r = (p : R[X])` using `Iff.rfl`. Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`. Establish `hp : (p : R[X]).coeff n ∈ I ^ n` using `(mem_reesAlgebra_iff I _).mp p.2 n`.

Establish `hcoef : (Polynomial.monomial n r : R[X]).coeff n = r` using `by simp`. Rewrite `hp` using `[← hr, hcoef]`. Conclude with `⟨r, hp, hr.symm⟩`. Introduce and unpack `⟨r, -, hpr⟩`. Conclude with `⟨r, hpr.symm⟩`.
-/
theorem mem_reesGrading_iff_monomial (I : Ideal R) (n : ℕ) (p : ↥(reesAlgebra I)) :
    p ∈ reesGrading I n ↔ ∃ r ∈ I ^ n, (p : R[X]) = Polynomial.monomial n r := by
  have hmem : p ∈ reesGrading I n ↔ ∃ r : R, Polynomial.monomial n r = (p : R[X]) := Iff.rfl
  rw [hmem]
  constructor
  · rintro ⟨r, hr⟩
    have hp : (p : R[X]).coeff n ∈ I ^ n := (mem_reesAlgebra_iff I _).mp p.2 n
    have hcoef : (Polynomial.monomial n r : R[X]).coeff n = r := by simp
    rw [← hr, hcoef] at hp
    exact ⟨r, hp, hr.symm⟩
  · rintro ⟨r, -, hpr⟩
    exact ⟨r, hpr.symm⟩

/- English proof (translation)
Establish `key : p ∈ reesGrading I n ↔ ∃ r : R, Polynomial.monomial n r = (p : R[X])` using `Iff.rfl`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩ i hi`. Rewrite using `[← hr, Polynomial.coeff_monomial, if_neg (Ne.symm hi)]`.

Introduce `h`. Use `⟨(p : R[X]).coeff n, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Break down `eq_or_ne i n with rfl | hi` into its components or cases. Simplify using the standard rewrite rules.

Simplify using `[Polynomial.coeff_monomial, Ne.symm hi, h i hi]`.
-/
theorem mem_reesGrading_iff_coeff (I : Ideal R) (n : ℕ) (p : ↥(reesAlgebra I)) :
    p ∈ reesGrading I n ↔ ∀ i, i ≠ n → (p : R[X]).coeff i = 0 := by
  have key : p ∈ reesGrading I n ↔ ∃ r : R, Polynomial.monomial n r = (p : R[X]) := Iff.rfl
  rw [key]
  constructor
  · rintro ⟨r, hr⟩ i hi
    rw [← hr, Polynomial.coeff_monomial, if_neg (Ne.symm hi)]
  · intro h
    refine ⟨(p : R[X]).coeff n, ?_⟩
    ext i
    rcases eq_or_ne i n with rfl | hi
    · simp
    · simp [Polynomial.coeff_monomial, Ne.symm hi, h i hi]

/- English proof (translation)
Use `show ((1 : ↥(reesAlgebra I)) : R[X]) ∈ LinearMap.range (Polynomial.monomial (R := R) 0)`. Use `LinearMap.mem_range.2 ⟨1, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem reesGrading_one_mem (I : Ideal R) : (1 : ↥(reesAlgebra I)) ∈ reesGrading I 0 := by
  show ((1 : ↥(reesAlgebra I)) : R[X]) ∈ LinearMap.range (Polynomial.monomial (R := R) 0)
  refine LinearMap.mem_range.2 ⟨1, ?_⟩
  simp

/- English proof (translation)
Establish `key : ∀ (k : ℕ) (x : ↥(reesAlgebra I)), x ∈ reesGrading I k ↔ ∃ r : R, Polynomial.monomial k r = (x : R[X])` using `fun _ _ => Iff.rfl`. Take `⟨a, ha⟩` from `(key m p).1 hp`. Take `⟨b, hb⟩` from `(key n q).1 hq`. Use `(key (m + n) (p * q)).2 ⟨a * b, ?_⟩` and prove the remaining obligations. Establish `hpq : ((p * q : ↥(reesAlgebra I)) : R[X]) = (p : R[X]) * (q : R[X])` using `rfl`.

Rewrite using `[hpq, ← ha, ← hb, Polynomial.monomial_mul_monomial]`.
-/
theorem reesGrading_mul_mem (I : Ideal R) {m n : ℕ} {p q : ↥(reesAlgebra I)}
    (hp : p ∈ reesGrading I m) (hq : q ∈ reesGrading I n) :
    p * q ∈ reesGrading I (m + n) := by
  have key : ∀ (k : ℕ) (x : ↥(reesAlgebra I)),
      x ∈ reesGrading I k ↔ ∃ r : R, Polynomial.monomial k r = (x : R[X]) :=
    fun _ _ => Iff.rfl
  obtain ⟨a, ha⟩ := (key m p).1 hp
  obtain ⟨b, hb⟩ := (key n q).1 hq
  refine (key (m + n) (p * q)).2 ⟨a * b, ?_⟩
  have hpq : ((p * q : ↥(reesAlgebra I)) : R[X]) = (p : R[X]) * (q : R[X]) := rfl
  rw [hpq, ← ha, ← hb, Polynomial.monomial_mul_monomial]

instance instGradedMonoidReesGrading (I : Ideal R) : SetLike.GradedMonoid (reesGrading I) where
  one_mem := reesGrading_one_mem I
  mul_mem := @fun _ _ _ _ hp hq => reesGrading_mul_mem I hp hq

/- English proof (translation)
Introduce `n`. Rewrite using `[Submodule.disjoint_def]`. Introduce `p hp hp'`. Establish `hcoeff : ∀ i, i ≠ n → (p : R[X]).coeff i = 0` using `(mem_reesGrading_iff_coeff I n p).1 hp`. Establish `hker : (⨆ (j : ℕ) (_ : j ≠ n), reesGrading I j) ≤ LinearMap.ker ((Polynomial.lcoeff R n).comp ((reesAlgebra I).val.toLinearMap))`.

Use `iSup_le fun j => iSup_le fun hj => ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hx'` using `(mem_reesGrading_iff_coeff I j x).1 hx n (Ne.symm hj)`. Simplify `hx'` using `[LinearMap.mem_ker, Polynomial.lcoeff_apply]`. Establish `hpn : (p : R[X]).coeff n = 0`.

Establish `h` using `hker hp'`. Simplify `h` using `[LinearMap.mem_ker, Polynomial.lcoeff_apply]`. Establish `hp0 : (p : R[X]) = 0`. Use extensionality with `i`. Break down `eq_or_ne i n with rfl | hi` into its components or cases.

Simplify using `using hpn`. Simplify using `using hcoeff i hi`. Conclude with `Subtype.ext (by simpa using hp0)`.
-/
theorem reesGrading_iSupIndep (I : Ideal R) : iSupIndep (reesGrading I) := by
  intro n
  rw [Submodule.disjoint_def]
  intro p hp hp'
  have hcoeff : ∀ i, i ≠ n → (p : R[X]).coeff i = 0 :=
    (mem_reesGrading_iff_coeff I n p).1 hp
  have hker : (⨆ (j : ℕ) (_ : j ≠ n), reesGrading I j) ≤
      LinearMap.ker ((Polynomial.lcoeff R n).comp ((reesAlgebra I).val.toLinearMap)) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro x hx
    have hx' := (mem_reesGrading_iff_coeff I j x).1 hx n (Ne.symm hj)
    simpa [LinearMap.mem_ker, Polynomial.lcoeff_apply] using hx'
  have hpn : (p : R[X]).coeff n = 0 := by
    have h := hker hp'
    simpa [LinearMap.mem_ker, Polynomial.lcoeff_apply] using h
  have hp0 : (p : R[X]) = 0 := by
    ext i
    rcases eq_or_ne i n with rfl | hi
    · simpa using hpn
    · simpa using hcoeff i hi
  exact Subtype.ext (by simpa using hp0)

/- English proof (translation)
The claim follows from `p.2 i`.
-/
private theorem coeff_mem_pow (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ((p : R[X])).coeff i ∈ I ^ i := p.2 i

/- English proof (translation)
Use `(mem_reesGrading_iff_coeff I n _).2 fun i hi => ?_` and prove the remaining obligations. Use `show (Polynomial.monomial n r : R[X]).coeff i = 0`. Rewrite using `[Polynomial.coeff_monomial, if_neg (Ne.symm hi)]`.
-/
private theorem monomial_mem_reesGrading (I : Ideal R) {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    (⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ : ↥(reesAlgebra I))
      ∈ reesGrading I n := by
  refine (mem_reesGrading_iff_coeff I n _).2 fun i hi => ?_
  show (Polynomial.monomial n r : R[X]).coeff i = 0
  rw [Polynomial.coeff_monomial, if_neg (Ne.symm hi)]

/- English proof (translation)
Use `Submodule.eq_top_iff'.2 fun p => ?_` and prove the remaining obligations. Establish `hval : ∀ x y : ↥(reesAlgebra I), (reesAlgebra I).val x = (reesAlgebra I).val y → x = y` using `fun _ _ h => Subtype.ext h`. Establish `hsum : p = ∑ i ∈ (p : R[X]).support, (⟨Polynomial.monomial i ((p : R[X]).coeff i), reesAlgebra.monomial_mem.mpr (coeff_mem_pow I p i)⟩ : ↥(reesAlgebra I))` using `hval _ _ (by rw [map_sum]; exact Polynomial.as_sum_support _)`. Rewrite using `[hsum]`. Conclude with `sum_mem fun i _ => Submodule.mem_iSup_of_mem i (monomial_mem_reesGrading I (coeff_mem_pow I p i))`.
-/
theorem reesGrading_iSup_eq_top (I : Ideal R) : (⨆ n : ℕ, reesGrading I n) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun p => ?_
  have hval : ∀ x y : ↥(reesAlgebra I),
      (reesAlgebra I).val x = (reesAlgebra I).val y → x = y := fun _ _ h => Subtype.ext h
  have hsum : p = ∑ i ∈ (p : R[X]).support,
      (⟨Polynomial.monomial i ((p : R[X]).coeff i),
        reesAlgebra.monomial_mem.mpr (coeff_mem_pow I p i)⟩ : ↥(reesAlgebra I)) :=
    hval _ _ (by rw [map_sum]; exact Polynomial.as_sum_support _)
  rw [hsum]
  exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i
    (monomial_mem_reesGrading I (coeff_mem_pow I p i))

/- English proof (translation)
Conclude with `(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (reesGrading I)).2 ⟨reesGrading_iSupIndep I, reesGrading_iSup_eq_top I⟩`.
-/
theorem reesGrading_isInternal (I : Ideal R) : DirectSum.IsInternal (reesGrading I) := by
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (reesGrading I)).2
    ⟨reesGrading_iSupIndep I, reesGrading_iSup_eq_top I⟩

private noncomputable def directSumReesGradingEquiv (I : Ideal R) :
    DirectSum ℕ (fun n => ↥(reesGrading I n)) ≃ ↥(reesAlgebra I) :=
  Equiv.ofBijective (DirectSum.coeAddMonoidHom (reesGrading I)) (reesGrading_isInternal I)

/- English proof (translation)
Introduce `x` and use `(directSumReesGradingEquiv I).apply_symm_apply x`.
-/
private theorem leftInverse_coeAddMonoidHom_reesGrading (I : Ideal R) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (reesGrading I))
      ⇑(directSumReesGradingEquiv I).symm :=
  fun x => (directSumReesGradingEquiv I).apply_symm_apply x

/- English proof (translation)
Introduce `x` and use `(directSumReesGradingEquiv I).symm_apply_apply x`.
-/
private theorem rightInverse_coeAddMonoidHom_reesGrading (I : Ideal R) :
    Function.RightInverse (DirectSum.coeAddMonoidHom (reesGrading I))
      ⇑(directSumReesGradingEquiv I).symm :=
  fun x => (directSumReesGradingEquiv I).symm_apply_apply x

noncomputable instance instGradedAlgebraReesGrading (I : Ideal R) :
    GradedAlgebra (reesGrading I) where
  __ := instGradedMonoidReesGrading I
  decompose' := ⇑(directSumReesGradingEquiv I).symm
  left_inv := leftInverse_coeAddMonoidHom_reesGrading I
  right_inv := rightInverse_coeAddMonoidHom_reesGrading I

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ r (reesGrading_one_mem I)`.
-/
theorem algebraMap_mem_reesGrading_zero (I : Ideal R) (r : R) :
    algebraMap R ↥(reesAlgebra I) r ∈ reesGrading I 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ r (reesGrading_one_mem I)

noncomputable def reesMonomial (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ↥(reesAlgebra I) :=
  ⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem reesMonomial_coe (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ((reesMonomial I n r hr : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial n r := rfl

/- English proof (translation)
Rewrite using `[mem_reesGrading_iff_monomial]`. Conclude with `⟨r, hr, reesMonomial_coe I n r hr⟩`.
-/
theorem reesMonomial_mem_reesGrading (I : Ideal R) {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    reesMonomial I n r hr ∈ reesGrading I n := by
  rw [mem_reesGrading_iff_monomial]
  exact ⟨r, hr, reesMonomial_coe I n r hr⟩

noncomputable def reesDegreeOneMonomial (I : Ideal R) (a : R) (ha : a ∈ I) : ↥(reesAlgebra I) :=
  reesMonomial I 1 a (mem_pow_one I ha)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem reesDegreeOneMonomial_coe (I : Ideal R) (a : R) (ha : a ∈ I) :
    ((reesDegreeOneMonomial I a ha : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial 1 a := rfl

/- English proof (translation)
The claim follows from `reesMonomial_mem_reesGrading I (mem_pow_one I ha)`.
-/
theorem reesDegreeOneMonomial_mem_reesGrading (I : Ideal R) {a : R} (ha : a ∈ I) :
    reesDegreeOneMonomial I a ha ∈ reesGrading I 1 :=
  reesMonomial_mem_reesGrading I (mem_pow_one I ha)

noncomputable def reesGenerator (I : Ideal R) (a : ↥I) : ↥(reesAlgebra I) :=
  reesDegreeOneMonomial I (a : R) a.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem reesGenerator_coe (I : Ideal R) (a : ↥I) :
    ((reesGenerator I a : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial 1 (a : R) := rfl

/- English proof (translation)
The claim follows from `reesDegreeOneMonomial_mem_reesGrading I a.2`.
-/
theorem reesGenerator_mem_reesGrading (I : Ideal R) (a : ↥I) : reesGenerator I a ∈ reesGrading I 1 :=
  reesDegreeOneMonomial_mem_reesGrading I a.2

private noncomputable def reesMonomialOfCoeff (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ↥(reesAlgebra I) :=
  reesMonomial I i ((p : R[X]).coeff i) (coeff_mem_pow I p i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem reesComponent_coe (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ((reesMonomialOfCoeff I p i : ↥(reesAlgebra I)) : R[X])
      = Polynomial.monomial i ((p : R[X]).coeff i) := rfl

/- English proof (translation)
Use `(mem_reesGrading_iff_coeff I i _).2 fun j hj => ?_` and prove the remaining obligations. Rewrite using `[reesComponent_coe, Polynomial.coeff_monomial, if_neg (Ne.symm hj)]`.
-/
private theorem reesComponent_mem_reesGrading (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    reesMonomialOfCoeff I p i ∈ reesGrading I i := by
  refine (mem_reesGrading_iff_coeff I i _).2 fun j hj => ?_
  rw [reesComponent_coe, Polynomial.coeff_monomial, if_neg (Ne.symm hj)]

/- English proof (translation)
Establish `hval : ∀ x y : ↥(reesAlgebra I), (reesAlgebra I).val x = (reesAlgebra I).val y → x = y` using `fun _ _ h => Subtype.ext h`. Conclude with `hval _ _ (by rw [map_sum]; exact Polynomial.as_sum_support _)`.
-/
private theorem eq_sum_reesComponent (I : Ideal R) (p : ↥(reesAlgebra I)) :
    p = ∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i := by
  have hval : ∀ x y : ↥(reesAlgebra I),
      (reesAlgebra I).val x = (reesAlgebra I).val y → x = y := fun _ _ h => Subtype.ext h
  exact hval _ _ (by rw [map_sum]; exact Polynomial.as_sum_support _)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `r hr x hx`. Establish `hr' : r ∈ I` using `by simpa using hr`.

Establish `hxe : x = reesGenerator I ⟨r, hr'⟩` using `Subtype.ext (hx.trans rfl)`. Rewrite using `[hxe]`. Conclude with `Ideal.subset_span (Set.mem_range_self _)`. Consider the case `succ n ih`. Introduce `r hr`.

Rewrite `hr` using `[pow_succ]`. Use `Submodule.mul_induction_on' (C := fun s _ => ∀ x : ↥(reesAlgebra I), (x : R[X]) = Polynomial.monomial (n + 1 + 1) s → x ∈ Ideal.span (Set.range (reesGenerator I))) ?_ ?_ hr` and prove the remaining obligations. Introduce `m hm a ha x hx`. Establish `hy : reesMonomial I (n + 1) m hm ∈ Ideal.span (Set.range (reesGenerator I))` using `ih m hm (reesMonomial I (n + 1) m hm) rfl`. Establish `hco : ((reesMonomial I (n + 1) m hm * reesGenerator I ⟨a, ha⟩ : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial (n + 1 + 1) (m * a)` using `by show (Polynomial.monomial (n + 1) m : R[X]) * Polynomial.monomial 1 a = Polynomial.monomial (n + 1 + 1) (m * a)`.

Rewrite using `[Polynomial.monomial_mul_monomial]`. Establish `hxe : x = reesMonomial I (n + 1) m hm * reesGenerator I ⟨a, ha⟩` using `Subtype.ext (hx.trans hco.symm)`. Rewrite using `[hxe]`. Conclude with `Ideal.mul_mem_right _ _ hy`. Introduce `s hs t ht hs' ht' x hx`.

Establish `hsm : s ∈ I ^ (n + 1 + 1)` using `by rw [pow_succ]; exact hs`. Establish `htm : t ∈ I ^ (n + 1 + 1)` using `by rw [pow_succ]; exact ht`. Establish `hxe : x = reesMonomial I (n + 1 + 1) s hsm + reesMonomial I (n + 1 + 1) t htm`. Use `Subtype.ext ?_` and prove the remaining obligations. Use `show (x : R[X]) = Polynomial.monomial (n + 1 + 1) s + Polynomial.monomial (n + 1 + 1) t`.

Rewrite using `[hx]`. Conclude with `map_add (Polynomial.monomial (R := R) (n + 1 + 1)) s t`. Rewrite using `[hxe]`. Conclude with `add_mem (hs' _ rfl) (ht' _ rfl)`.
-/
private theorem mem_span_reesGenerator_of_eq_monomial_succ (I : Ideal R) :
    ∀ (n : ℕ) (r : R), r ∈ I ^ (n + 1) →
      ∀ x : ↥(reesAlgebra I), (x : R[X]) = Polynomial.monomial (n + 1) r →
        x ∈ Ideal.span (Set.range (reesGenerator I)) := by
  intro n
  induction n with
  | zero =>
    intro r hr x hx
    have hr' : r ∈ I := by simpa using hr
    have hxe : x = reesGenerator I ⟨r, hr'⟩ := Subtype.ext (hx.trans rfl)
    rw [hxe]
    exact Ideal.subset_span (Set.mem_range_self _)
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on'
      (C := fun s _ => ∀ x : ↥(reesAlgebra I),
        (x : R[X]) = Polynomial.monomial (n + 1 + 1) s →
          x ∈ Ideal.span (Set.range (reesGenerator I))) ?_ ?_ hr
    · intro m hm a ha x hx
      have hy : reesMonomial I (n + 1) m hm ∈ Ideal.span (Set.range (reesGenerator I)) :=
        ih m hm (reesMonomial I (n + 1) m hm) rfl
      have hco : ((reesMonomial I (n + 1) m hm * reesGenerator I ⟨a, ha⟩ : ↥(reesAlgebra I)) : R[X])
          = Polynomial.monomial (n + 1 + 1) (m * a) := by
        show (Polynomial.monomial (n + 1) m : R[X]) * Polynomial.monomial 1 a
            = Polynomial.monomial (n + 1 + 1) (m * a)
        rw [Polynomial.monomial_mul_monomial]
      have hxe : x = reesMonomial I (n + 1) m hm * reesGenerator I ⟨a, ha⟩ :=
        Subtype.ext (hx.trans hco.symm)
      rw [hxe]
      exact Ideal.mul_mem_right _ _ hy
    · intro s hs t ht hs' ht' x hx
      have hsm : s ∈ I ^ (n + 1 + 1) := by rw [pow_succ]; exact hs
      have htm : t ∈ I ^ (n + 1 + 1) := by rw [pow_succ]; exact ht
      have hxe : x = reesMonomial I (n + 1 + 1) s hsm
          + reesMonomial I (n + 1 + 1) t htm := by
        refine Subtype.ext ?_
        show (x : R[X]) = Polynomial.monomial (n + 1 + 1) s + Polynomial.monomial (n + 1 + 1) t
        rw [hx]
        exact map_add (Polynomial.monomial (R := R) (n + 1 + 1)) s t
      rw [hxe]
      exact add_mem (hs' _ rfl) (ht' _ rfl)

/- English proof (translation)
Introduce `p hp`. Establish `hp1 : p ∈ HomogeneousIdeal.irrelevant (reesGrading I)` using `hp`. Rewrite `hp1` using `[HomogeneousIdeal.mem_irrelevant_iff]`. Establish `hsum : p = ∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i` using `eq_sum_reesComponent I p`. Establish `hmapsum : (GradedRing.proj (reesGrading I) 0) (∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i) = ∑ i ∈ (p : R[X]).support, (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i)` using `map_sum (GradedRing.proj (reesGrading I) 0) (fun i => reesMonomialOfCoeff I p i) ((p : R[X]).support)`.

Establish `hprojsum : ∑ i ∈ (p : R[X]).support, (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i) = 0`. Rewrite using `[← hmapsum, ← hsum]`. Conclude with `hp1`. Establish `hsingle : ∑ i ∈ (p : R[X]).support, (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i) = (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p 0)`. Use `Finset.sum_eq_single 0 (fun i _ hi => ?_) (fun h0 => ?_)` and prove the remaining obligations.

Rewrite using `[GradedRing.proj_apply]`. Conclude with `DirectSum.decompose_of_mem_ne (reesGrading I) (reesComponent_mem_reesGrading I p i) hi`. Establish `hc : (p : R[X]).coeff 0 = 0` using `not_not.mp (fun h => h0 (Polynomial.mem_support_iff.mpr h))`. Establish `hz : reesMonomialOfCoeff I p 0 = 0`. Use `Subtype.ext ?_` and prove the remaining obligations.

Use `show Polynomial.monomial 0 ((p : R[X]).coeff 0) = (0 : R[X])`. Rewrite using `[hc, map_zero]`. Rewrite using `[hz, map_zero]`. Establish `hz0 : reesMonomialOfCoeff I p 0 = 0`. Establish `h1 : (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p 0) = 0`.

Rewrite using `[← hsingle]`. Conclude with `hprojsum`. Rewrite `h1` using `[GradedRing.proj_apply, DirectSum.decompose_of_mem_same (reesGrading I) (reesComponent_mem_reesGrading I p 0)]`. Conclude with `h1`. Rewrite using `[hsum]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Rewrite using `[hz0]`. Conclude with `zero_mem _`. Take `⟨k, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hi.ne'`.

Conclude with `mem_span_reesGenerator_of_eq_monomial_succ I k ((p : R[X]).coeff (k + 1)) (coeff_mem_pow I p (k + 1)) (reesMonomialOfCoeff I p (k + 1)) (reesComponent_coe I p (k + 1))`.
-/
theorem reesGrading_irrelevant_le_span (I : Ideal R) :
    (HomogeneousIdeal.irrelevant (reesGrading I)).toIdeal ≤
      Ideal.span (Set.range (reesGenerator I)) := by
  intro p hp
  have hp1 : p ∈ HomogeneousIdeal.irrelevant (reesGrading I) := hp
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hp1
  have hsum : p = ∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i := eq_sum_reesComponent I p
  have hmapsum : (GradedRing.proj (reesGrading I) 0)
        (∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i)
      = ∑ i ∈ (p : R[X]).support, (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i) :=
    map_sum (GradedRing.proj (reesGrading I) 0) (fun i => reesMonomialOfCoeff I p i)
      ((p : R[X]).support)
  have hprojsum : ∑ i ∈ (p : R[X]).support,
      (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i) = 0 := by
    rw [← hmapsum, ← hsum]
    exact hp1
  have hsingle : ∑ i ∈ (p : R[X]).support,
      (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p i)
      = (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p 0) := by
    refine Finset.sum_eq_single 0 (fun i _ hi => ?_) (fun h0 => ?_)
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne (reesGrading I) (reesComponent_mem_reesGrading I p i) hi
    · have hc : (p : R[X]).coeff 0 = 0 :=
        not_not.mp (fun h => h0 (Polynomial.mem_support_iff.mpr h))
      have hz : reesMonomialOfCoeff I p 0 = 0 := by
        refine Subtype.ext ?_
        show Polynomial.monomial 0 ((p : R[X]).coeff 0) = (0 : R[X])
        rw [hc, map_zero]
      rw [hz, map_zero]
  have hz0 : reesMonomialOfCoeff I p 0 = 0 := by
    have h1 : (GradedRing.proj (reesGrading I) 0) (reesMonomialOfCoeff I p 0) = 0 := by
      rw [← hsingle]
      exact hprojsum
    rw [GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same (reesGrading I) (reesComponent_mem_reesGrading I p 0)] at h1
    exact h1
  rw [hsum]
  refine sum_mem fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [hz0]
    exact zero_mem _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    exact mem_span_reesGenerator_of_eq_monomial_succ I k ((p : R[X]).coeff (k + 1))
      (coeff_mem_pow I p (k + 1)) (reesMonomialOfCoeff I p (k + 1))
      (reesComponent_coe I p (k + 1))

noncomputable def reesDegreeZeroMonomial (I : Ideal R) (r : R) : ↥(reesGrading I 0) :=
  ⟨reesMonomial I 0 r (mem_pow_zero I r),
    reesMonomial_mem_reesGrading I (mem_pow_zero I r)⟩

/- English proof (translation)
Use `Subtype.ext (Subtype.ext ?_)` and prove the remaining obligations. Use `show (Polynomial.monomial 0 (1 : R) : R[X]) = _`. Conclude with `Polynomial.monomial_zero_one`.
-/
private theorem reesDegreeZeroMonomial_one (I : Ideal R) : reesDegreeZeroMonomial I 1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (1 : R) : R[X]) = _
  exact Polynomial.monomial_zero_one

/- English proof (translation)
Use `Subtype.ext (Subtype.ext ?_)` and prove the remaining obligations. Use `show (Polynomial.monomial 0 (r * s) : R[X]) = (Polynomial.monomial 0 r : R[X]) * (Polynomial.monomial 0 s : R[X])`. Conclude with `(Polynomial.monomial_mul_monomial 0 0 r s).symm`.
-/
private theorem reesDegreeZeroMonomial_mul (I : Ideal R) (r s : R) :
    reesDegreeZeroMonomial I (r * s) = reesDegreeZeroMonomial I r * reesDegreeZeroMonomial I s := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (r * s) : R[X])
      = (Polynomial.monomial 0 r : R[X]) * (Polynomial.monomial 0 s : R[X])
  exact (Polynomial.monomial_mul_monomial 0 0 r s).symm

/- English proof (translation)
Use `Subtype.ext (Subtype.ext ?_)` and prove the remaining obligations. Use `show (Polynomial.monomial 0 (0 : R) : R[X]) = 0`. Rewrite using `[map_zero]`.
-/
private theorem reesDegreeZeroMonomial_zero (I : Ideal R) : reesDegreeZeroMonomial I 0 = 0 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (0 : R) : R[X]) = 0
  rw [map_zero]

/- English proof (translation)
Use `Subtype.ext (Subtype.ext ?_)` and prove the remaining obligations. Use `show (Polynomial.monomial 0 (r + s) : R[X]) = (Polynomial.monomial 0 r : R[X]) + (Polynomial.monomial 0 s : R[X])`. Conclude with `map_add (Polynomial.monomial (R := R) 0) r s`.
-/
private theorem reesDegreeZeroMonomial_add (I : Ideal R) (r s : R) :
    reesDegreeZeroMonomial I (r + s) = reesDegreeZeroMonomial I r + reesDegreeZeroMonomial I s := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (r + s) : R[X])
      = (Polynomial.monomial 0 r : R[X]) + (Polynomial.monomial 0 s : R[X])
  exact map_add (Polynomial.monomial (R := R) 0) r s

noncomputable def reesDegreeZeroRingHom (I : Ideal R) : R →+* ↥(reesGrading I 0) where
  toFun := reesDegreeZeroMonomial I
  map_one' := reesDegreeZeroMonomial_one I
  map_mul' := reesDegreeZeroMonomial_mul I
  map_zero' := reesDegreeZeroMonomial_zero I
  map_add' := reesDegreeZeroMonomial_add I

/- English proof (translation)
Use `show (Polynomial.monomial 0 r : R[X]) = Polynomial.C r`. Simplify using the standard rewrite rules.
-/
@[simp] theorem reesDegreeZeroRingHom_coe_coe (I : Ideal R) (r : R) :
    ((reesDegreeZeroRingHom I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by
  show (Polynomial.monomial 0 r : R[X]) = Polynomial.C r
  simp

/- English proof (translation)
Introduce `r s h`. Establish `h1` using `congrArg (fun x : ↥(reesGrading I 0) => ((x : ↥(reesAlgebra I)) : R[X])) h`. Establish `h2 : (Polynomial.monomial 0 r : R[X]) = Polynomial.monomial 0 s` using `h1`. Establish `h3 : (Polynomial.monomial 0 r : R[X]).coeff 0 = (Polynomial.monomial 0 s : R[X]).coeff 0` using `congrArg (fun p : R[X] => p.coeff 0) h2`. Simplify using `using h3`.
-/
theorem reesDegreeZeroRingHom_injective (I : Ideal R) :
    Function.Injective (reesDegreeZeroRingHom I) := by
  intro r s h
  have h1 := congrArg (fun x : ↥(reesGrading I 0) => ((x : ↥(reesAlgebra I)) : R[X])) h
  have h2 : (Polynomial.monomial 0 r : R[X]) = Polynomial.monomial 0 s := h1
  have h3 : (Polynomial.monomial 0 r : R[X]).coeff 0 = (Polynomial.monomial 0 s : R[X]).coeff 0 :=
    congrArg (fun p : R[X] => p.coeff 0) h2
  simpa using h3

/- English proof (translation)
Introduce and unpack `⟨x, hx⟩`. Establish `hco : ∀ i, i ≠ 0 → ((x : ↥(reesAlgebra I)) : R[X]).coeff i = 0` using `(mem_reesGrading_iff_coeff I 0 x).1 hx`. Use `⟨((x : ↥(reesAlgebra I)) : R[X]).coeff 0, Subtype.ext (Subtype.ext ?_)⟩` and prove the remaining obligations. Use `show (Polynomial.monomial 0 (((x : ↥(reesAlgebra I)) : R[X]).coeff 0) : R[X]) = ((x : ↥(reesAlgebra I)) : R[X])`. Use extensionality with `i`.

Break down `eq_or_ne i 0 with rfl | hi` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Polynomial.coeff_monomial, if_neg (Ne.symm hi)]`. Conclude with `(hco i hi).symm`.
-/
theorem reesDegreeZeroRingHom_surjective (I : Ideal R) :
    Function.Surjective (reesDegreeZeroRingHom I) := by
  rintro ⟨x, hx⟩
  have hco : ∀ i, i ≠ 0 → ((x : ↥(reesAlgebra I)) : R[X]).coeff i = 0 :=
    (mem_reesGrading_iff_coeff I 0 x).1 hx
  refine ⟨((x : ↥(reesAlgebra I)) : R[X]).coeff 0, Subtype.ext (Subtype.ext ?_)⟩
  show (Polynomial.monomial 0 (((x : ↥(reesAlgebra I)) : R[X]).coeff 0) : R[X])
      = ((x : ↥(reesAlgebra I)) : R[X])
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · rw [Polynomial.coeff_monomial, if_neg (Ne.symm hi)]
    exact (hco i hi).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨reesDegreeZeroRingHom_injective I, reesDegreeZeroRingHom_surjective I⟩`.
-/
theorem reesDegreeZeroRingHom_bijective (I : Ideal R) :
    Function.Bijective (reesDegreeZeroRingHom I) :=
  ⟨reesDegreeZeroRingHom_injective I, reesDegreeZeroRingHom_surjective I⟩

noncomputable def reesDegreeZeroEquiv (I : Ideal R) : R ≃+* ↥(reesGrading I 0) :=
  RingEquiv.ofBijective (reesDegreeZeroRingHom I) (reesDegreeZeroRingHom_bijective I)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem reesDegreeZeroEquiv_apply (I : Ideal R) (r : R) :
    reesDegreeZeroEquiv I r = reesDegreeZeroRingHom I r := rfl

/- English proof (translation)
Simplify using `only [reesDegreeZeroEquiv_apply, reesDegreeZeroRingHom_coe_coe]`.
-/
theorem reesDegreeZeroEquiv_coe_coe (I : Ideal R) (r : R) :
    ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by
  simp only [reesDegreeZeroEquiv_apply, reesDegreeZeroRingHom_coe_coe]

end FunctorialResolution.Blowup
