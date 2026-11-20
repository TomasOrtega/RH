import Mathlib

open Polynomial

namespace FunctorialResolution.Blowup

variable {R : Type*} [CommRing R]

/- English proof (authored)
The first power of the ideal is the ideal itself, so the given membership applies.
-/
private theorem mem_pow_one (I : Ideal R) {a : R} (ha : a ∈ I) : a ∈ I ^ 1 := by
  rwa [pow_one]

/- English proof (authored)
The zeroth power of an ideal is the unit ideal, which contains every ring element.
-/
private theorem mem_pow_zero (I : Ideal R) (r : R) : r ∈ I ^ 0 := by
  rw [pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

noncomputable def reesGrading (I : Ideal R) (n : ℕ) : Submodule R ↥(reesAlgebra I) :=
  Submodule.comap (reesAlgebra I).val.toLinearMap
    (LinearMap.range (Polynomial.monomial (R := R) n))

/- English proof (authored)
The degree-n component consists of degree-n monomials in the Rees algebra. The coefficient of such a monomial is its degree-n coefficient, which lies in the nth ideal power by the definition of the Rees algebra. Conversely, a Rees polynomial represented by such a monomial is in the degree-n component.
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

/- English proof (authored)
A degree-n monomial has zero coefficient at every different degree. Conversely, if those coefficients vanish, the polynomial equals the degree-n monomial built from its degree-n coefficient. Equality follows coefficient by coefficient.
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

/- English proof (authored)
The constant polynomial one is the degree-zero monomial with coefficient one, so it lies in the degree-zero component.
-/
theorem reesGrading_one_mem (I : Ideal R) : (1 : ↥(reesAlgebra I)) ∈ reesGrading I 0 := by
  show ((1 : ↥(reesAlgebra I)) : R[X]) ∈ LinearMap.range (Polynomial.monomial (R := R) 0)
  refine LinearMap.mem_range.2 ⟨1, ?_⟩
  simp

/- English proof (authored)
Write the two homogeneous elements as monomials of their respective degrees. Their product is the monomial whose degree is the sum and whose coefficient is the product of the two coefficients. It lies in the corresponding graded component.
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

/- English proof (authored)
An element in the degree-n component has every coefficient except the nth equal to zero. The sum of all other components lies in the kernel of the nth coefficient map because each of those components does. An element in both therefore has every coefficient zero and is the zero polynomial. This is independence of the graded components.
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

/- English proof (authored)
The defining coefficient condition for a Rees algebra element puts its ith coefficient in the ith power of the ideal.
-/
private theorem coeff_mem_pow (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ((p : R[X])).coeff i ∈ I ^ i := p.2 i

/- English proof (authored)
The specified coefficient gives an element of the Rees algebra by the ideal-power condition. Its other coefficients vanish, so the monomial belongs to its indicated graded component.
-/
private theorem monomial_mem_reesGrading (I : Ideal R) {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    (⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ : ↥(reesAlgebra I))
      ∈ reesGrading I n := by
  refine (mem_reesGrading_iff_coeff I n _).2 fun i hi => ?_
  show (Polynomial.monomial n r : R[X]).coeff i = 0
  rw [Polynomial.coeff_monomial, if_neg (Ne.symm hi)]

/- English proof (authored)
Write any Rees polynomial as the finite sum of the monomials on its support. Each coefficient lies in the corresponding ideal power, so each monomial belongs to its corresponding graded component. The sum therefore belongs to the supremum of those components.
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

/- English proof (authored)
The components are independent, and their sum is the whole Rees algebra. The internal direct sum criterion gives the result.
-/
theorem reesGrading_isInternal (I : Ideal R) : DirectSum.IsInternal (reesGrading I) := by
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (reesGrading I)).2
    ⟨reesGrading_iSupIndep I, reesGrading_iSup_eq_top I⟩

private noncomputable def directSumReesGradingEquiv (I : Ideal R) :
    DirectSum ℕ (fun n => ↥(reesGrading I n)) ≃ ↥(reesAlgebra I) :=
  Equiv.ofBijective (DirectSum.coeAddMonoidHom (reesGrading I)) (reesGrading_isInternal I)

/- English proof (authored)
The forward map of the direct sum equivalence is addition of components. Decompose a Rees element by the inverse and add the components back. The inverse identity returns the element.
-/
private theorem leftInverse_coeAddMonoidHom_reesGrading (I : Ideal R) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (reesGrading I))
      ⇑(directSumReesGradingEquiv I).symm :=
  fun x => (directSumReesGradingEquiv I).apply_symm_apply x

/- English proof (authored)
Adding a tuple of homogeneous components and then decomposing it is the inverse identity for the direct sum equivalence. Thus it returns the original tuple.
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

/- English proof (authored)
The algebra map sends the element to its scalar multiple of one. The degree-zero component contains one and is closed under scalar multiplication.
-/
theorem algebraMap_mem_reesGrading_zero (I : Ideal R) (r : R) :
    algebraMap R ↥(reesAlgebra I) r ∈ reesGrading I 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ r (reesGrading_one_mem I)

noncomputable def reesMonomial (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ↥(reesAlgebra I) :=
  ⟨Polynomial.monomial n r, reesAlgebra.monomial_mem.mpr hr⟩

/- English proof (authored)
The Rees monomial is defined by the given polynomial monomial with its proof of membership in the Rees algebra. Forgetting that membership gives the polynomial.
-/
@[simp] theorem reesMonomial_coe (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    ((reesMonomial I n r hr : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial n r := rfl

/- English proof (authored)
The Rees monomial is represented by a single monomial of degree n whose coefficient belongs to the nth ideal power. The homogeneous membership criterion applies.
-/
theorem reesMonomial_mem_reesGrading (I : Ideal R) {n : ℕ} {r : R} (hr : r ∈ I ^ n) :
    reesMonomial I n r hr ∈ reesGrading I n := by
  rw [mem_reesGrading_iff_monomial]
  exact ⟨r, hr, reesMonomial_coe I n r hr⟩

noncomputable def reesDegreeOneMonomial (I : Ideal R) (a : R) (ha : a ∈ I) : ↥(reesAlgebra I) :=
  reesMonomial I 1 a (mem_pow_one I ha)

/- English proof (authored)
The chosen representative is the monomial of degree one with the given coefficient, so forgetting membership in the Rees algebra gives that monomial.
-/
@[simp] theorem reesDegreeOneMonomial_coe (I : Ideal R) (a : R) (ha : a ∈ I) :
    ((reesDegreeOneMonomial I a ha : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial 1 a := rfl

/- English proof (authored)
The coefficient belongs to the first power of the ideal since it belongs to the ideal itself. The degree-one monomial therefore lies in the degree-one component.
-/
theorem reesDegreeOneMonomial_mem_reesGrading (I : Ideal R) {a : R} (ha : a ∈ I) :
    reesDegreeOneMonomial I a ha ∈ reesGrading I 1 :=
  reesMonomial_mem_reesGrading I (mem_pow_one I ha)

noncomputable def reesGenerator (I : Ideal R) (a : ↥I) : ↥(reesAlgebra I) :=
  reesDegreeOneMonomial I (a : R) a.2

/- English proof (authored)
The Rees generator attached to an ideal element is defined by its degree-one monomial representative.
-/
@[simp] theorem reesGenerator_coe (I : Ideal R) (a : ↥I) :
    ((reesGenerator I a : ↥(reesAlgebra I)) : R[X]) = Polynomial.monomial 1 (a : R) := rfl

/- English proof (authored)
The generator is the degree-one monomial of a member of the ideal. The degree-one membership result applies.
-/
theorem reesGenerator_mem_reesGrading (I : Ideal R) (a : ↥I) : reesGenerator I a ∈ reesGrading I 1 :=
  reesDegreeOneMonomial_mem_reesGrading I a.2

private noncomputable def reesMonomialOfCoeff (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ↥(reesAlgebra I) :=
  reesMonomial I i ((p : R[X]).coeff i) (coeff_mem_pow I p i)

/- English proof (authored)
The ith component monomial is constructed from the ith coefficient of the polynomial, so its polynomial representative is the corresponding single monomial.
-/
private theorem reesComponent_coe (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    ((reesMonomialOfCoeff I p i : ↥(reesAlgebra I)) : R[X])
      = Polynomial.monomial i ((p : R[X]).coeff i) := rfl

/- English proof (authored)
The component monomial has degree i and all its other coefficients vanish. The coefficient criterion places it in the ith graded component.
-/
private theorem reesComponent_mem_reesGrading (I : Ideal R) (p : ↥(reesAlgebra I)) (i : ℕ) :
    reesMonomialOfCoeff I p i ∈ reesGrading I i := by
  refine (mem_reesGrading_iff_coeff I i _).2 fun j hj => ?_
  rw [reesComponent_coe, Polynomial.coeff_monomial, if_neg (Ne.symm hj)]

/- English proof (authored)
After viewing the Rees elements as polynomials, the stated sum is the finite reconstruction of a polynomial from its nonzero coefficients. The inclusion of the Rees algebra into the polynomial ring is injective, so the identity holds in the Rees algebra.
-/
private theorem eq_sum_reesComponent (I : Ideal R) (p : ↥(reesAlgebra I)) :
    p = ∑ i ∈ (p : R[X]).support, reesMonomialOfCoeff I p i := by
  have hval : ∀ x y : ↥(reesAlgebra I),
      (reesAlgebra I).val x = (reesAlgebra I).val y → x = y := fun _ _ h => Subtype.ext h
  exact hval _ _ (by rw [map_sum]; exact Polynomial.as_sum_support _)

/- English proof (authored)
At degree one the monomial is itself a Rees generator. At the next degree, the coefficient lies in the product of the previous ideal power and the original ideal. For a product coefficient, its monomial factors as the previous-degree monomial times the degree-one Rees generator. The previous monomial lies in the generated ideal by induction, hence so does the product. The property is preserved under sums because the monomial operation is additive in the coefficient. This proves membership for every coefficient in the next power.
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

/- English proof (authored)
Decompose an element of the irrelevant ideal into the finite sum of its homogeneous monomials. Projection to degree zero annihilates all terms in positive degree and fixes the degree-zero term. By membership in the irrelevant ideal the projected sum is zero, so the degree-zero term vanishes. Each positive-degree monomial lies in the ideal generated by the degree-one Rees generators by the ideal-power argument. Their sum therefore belongs to that ideal.
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

/- English proof (authored)
The degree-zero monomial with coefficient one is the constant polynomial one. The inclusions of the graded component and the Rees algebra are injective, so the equality holds in the degree-zero component.
-/
private theorem reesDegreeZeroMonomial_one (I : Ideal R) : reesDegreeZeroMonomial I 1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (1 : R) : R[X]) = _
  exact Polynomial.monomial_zero_one

/- English proof (authored)
Multiplying two degree-zero monomials keeps degree zero and multiplies their coefficients. The polynomial identity gives the asserted identity in the component.
-/
private theorem reesDegreeZeroMonomial_mul (I : Ideal R) (r s : R) :
    reesDegreeZeroMonomial I (r * s) = reesDegreeZeroMonomial I r * reesDegreeZeroMonomial I s := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (r * s) : R[X])
      = (Polynomial.monomial 0 r : R[X]) * (Polynomial.monomial 0 s : R[X])
  exact (Polynomial.monomial_mul_monomial 0 0 r s).symm

/- English proof (authored)
The degree-zero monomial with coefficient zero is the zero polynomial, hence the zero element of the graded component.
-/
private theorem reesDegreeZeroMonomial_zero (I : Ideal R) : reesDegreeZeroMonomial I 0 = 0 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (Polynomial.monomial 0 (0 : R) : R[X]) = 0
  rw [map_zero]

/- English proof (authored)
The monomial construction in degree zero is additive in the coefficient. Equality of the polynomial representatives gives equality in the degree-zero component.
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

/- English proof (authored)
The ring homomorphism sends the element to its degree-zero monomial. As a polynomial this is the constant polynomial with the given coefficient.
-/
@[simp] theorem reesDegreeZeroRingHom_coe_coe (I : Ideal R) (r : R) :
    ((reesDegreeZeroRingHom I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by
  show (Polynomial.monomial 0 r : R[X]) = Polynomial.C r
  simp

/- English proof (authored)
If two elements have the same degree-zero monomial, their degree-zero coefficients agree. These coefficients are the original elements.
-/
theorem reesDegreeZeroRingHom_injective (I : Ideal R) :
    Function.Injective (reesDegreeZeroRingHom I) := by
  intro r s h
  have h1 := congrArg (fun x : ↥(reesGrading I 0) => ((x : ↥(reesAlgebra I)) : R[X])) h
  have h2 : (Polynomial.monomial 0 r : R[X]) = Polynomial.monomial 0 s := h1
  have h3 : (Polynomial.monomial 0 r : R[X]).coeff 0 = (Polynomial.monomial 0 s : R[X]).coeff 0 :=
    congrArg (fun p : R[X] => p.coeff 0) h2
  simpa using h3

/- English proof (authored)
An element of the degree-zero component has every coefficient except the constant one equal to zero. The degree-zero monomial of that constant coefficient therefore has the same coefficients as the element and equals it.
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

/- English proof (authored)
The homomorphism is injective because constant coefficients recover the input, and surjective because every degree-zero element is a constant monomial. These two properties give bijectivity.
-/
theorem reesDegreeZeroRingHom_bijective (I : Ideal R) :
    Function.Bijective (reesDegreeZeroRingHom I) :=
  ⟨reesDegreeZeroRingHom_injective I, reesDegreeZeroRingHom_surjective I⟩

noncomputable def reesDegreeZeroEquiv (I : Ideal R) : R ≃+* ↥(reesGrading I 0) :=
  RingEquiv.ofBijective (reesDegreeZeroRingHom I) (reesDegreeZeroRingHom_bijective I)

/- English proof (authored)
The ring equivalence is formed from the degree-zero ring homomorphism and its bijectivity. Its forward function is that homomorphism.
-/
@[simp] theorem reesDegreeZeroEquiv_apply (I : Ideal R) (r : R) :
    reesDegreeZeroEquiv I r = reesDegreeZeroRingHom I r := rfl

/- English proof (authored)
The forward equivalence is the homomorphism taking the degree-zero monomial. Viewed as a polynomial, its value is the original element as a constant.
-/
theorem reesDegreeZeroEquiv_coe_coe (I : Ideal R) (r : R) :
    ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by
  simp only [reesDegreeZeroEquiv_apply, reesDegreeZeroRingHom_coe_coe]

end FunctorialResolution.Blowup
