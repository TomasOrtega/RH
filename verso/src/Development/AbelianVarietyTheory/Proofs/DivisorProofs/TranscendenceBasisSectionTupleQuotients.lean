import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp.TrBasis

variable {K : Type} [Field K]

/- English proof (translation)
Use `⟨Polynomial.C (⟨b, hb⟩ : Algebra.adjoin ℤ s) * Polynomial.X - Polynomial.C ⟨a, ha⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h1` using `congrArg (Polynomial.coeff · 1) h`. Simplify using `at h1`. Conclude with `hb0 (congrArg Subtype.val h1)`.

Simplify using `[mul_div_cancel₀ _ hb0]`.
-/
theorem isAlgebraic_div_of_mem {s : Set K} {a b : K} (ha : a ∈ Algebra.adjoin ℤ s)
    (hb : b ∈ Algebra.adjoin ℤ s) (hb0 : b ≠ 0) : IsAlgebraic (Algebra.adjoin ℤ s) (a / b) := by
  refine ⟨Polynomial.C (⟨b, hb⟩ : Algebra.adjoin ℤ s) * Polynomial.X - Polynomial.C ⟨a, ha⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (Polynomial.coeff · 1) h
    simp at h1
    exact hb0 (congrArg Subtype.val h1)
  · simp [mul_div_cancel₀ _ hb0]

/- English proof (translation)
Rewrite `ht`, the goal using `[← AlgebraicIndependent.matroid_spanning_iff]`. Rewrite `ht`, the goal using `[Matroid.spanning_iff_closure_eq]`. Use `Set.eq_univ_of_univ_subset ?_` and prove the remaining obligations. Rewrite `ht` using `[AlgebraicIndependent.matroid_e]`. Rewrite using `[← ht]`.

Use `Matroid.closure_subset_closure_of_subset_closure ?_` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[AlgebraicIndependent.matroid_closure_eq]`. Conclude with `(Subalgebra.mem_algebraicClosure _ _).2 (hts w hw)`.
-/
theorem isAlgebraic_trans [CharZero K] {s t : Set K}
    (ht : Algebra.IsAlgebraic (Algebra.adjoin ℤ t) K)
    (hts : ∀ w ∈ t, IsAlgebraic (Algebra.adjoin ℤ s) w) :
    Algebra.IsAlgebraic (Algebra.adjoin ℤ s) K := by
  rw [← AlgebraicIndependent.matroid_spanning_iff] at ht ⊢
  rw [Matroid.spanning_iff_closure_eq] at ht ⊢
  refine Set.eq_univ_of_univ_subset ?_
  rw [AlgebraicIndependent.matroid_e] at ht
  rw [← ht]
  refine Matroid.closure_subset_closure_of_subset_closure ?_
  intro w hw
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact (Subalgebra.mem_algebraicClosure _ _).2 (hts w hw)

/- English proof (translation)
Use `haveI : FaithfulSMul ℤ K := (faithfulSMul_iff_algebraMap_injective ℤ K).mpr Int.cast_injective`. Use `set y : Fin (D + 1) → K := fun j => x j / x l with hy`. Establish `hle : ratR x l ≤ (Algebra.adjoin ℤ (Set.range y)).toSubring` using `Subring.closure_le.2 Algebra.subset_adjoin`. Set `φ : ratR x l →+* Algebra.adjoin ℤ (Set.range y)` to `{ toFun := fun v => ⟨v, hle v.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `hAlgA : ∀ w ∈ (A : Set K), IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) w` using `fun w hw => (IsIntegral.map_of_comp_eq φ (RingHom.id K) (by ext; rfl) (hint w hw)).isAlgebraic`.

Establish `hAlgY : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) K`. Use `isAlgebraic_trans (t := (A : Set K)) ⟨fun w => ?_⟩ hAlgA` and prove the remaining obligations. Take `⟨a, ha, b, hb, hb0, rfl⟩` from `hfr w`. Conclude with `isAlgebraic_div_of_mem (Algebra.subset_adjoin ha) (Algebra.subset_adjoin hb) hb0`. Use `set z : Fin D → K := fun j => x (l.succAbove j) / x l with hz`.

Establish `hAlgZ : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range z)) K`. Use `isAlgebraic_trans hAlgY ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Break down `Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩` into its components or cases. Substitute `h` using the available equality.

Simplify using `only [hy, div_self hl]`. Conclude with `isAlgebraic_one`. Conclude with `isAlgebraic_algebraMap (⟨z j', Algebra.subset_adjoin ⟨j', rfl⟩⟩ : Algebra.adjoin ℤ (Set.range z))`. Establish `hZ : IsTranscendenceBasis ℤ z` using `Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ z (by rw [htr]; simp)`. Establish `hx : ∀ j, x j ≠ 0`.

Introduce `j`. Break down `Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩` into its components or cases. Conclude with `h ▸ hl`. Introduce `h0`. Conclude with `hZ.1.ne_zero j' (by simp [hz, h0])`.

Use `set u : Fin D → K := fun j => x j.succ / x 0 with hu`. Establish `hv : ∀ k, x k / x 0 ∈ Algebra.adjoin ℤ (Set.range u)`. Introduce `k`. Use `Fin.cases ?_ (fun j => ?_) k` and prove the remaining obligations. Rewrite using `[div_self (hx 0)]`.

Conclude with `Subalgebra.one_mem _`. Conclude with `Algebra.subset_adjoin ⟨j, rfl⟩`. Establish `hAlgU : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range u)) K`. Use `isAlgebraic_trans hAlgZ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Establish `e : z j = (x (l.succAbove j) / x 0) / (x l / x 0)`. Simplify using `only [hz]`. Clear denominators, using `[hx 0, hl]` for the nonvanishing conditions. Rewrite using `[e]`. Conclude with `isAlgebraic_div_of_mem (hv _) (hv _) (div_ne_zero hl (hx 0))`.

Establish `hU : IsTranscendenceBasis ℤ u` using `Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ u (by rw [htr]; simp)`. Use `⟨hx, hU.1, ?_⟩` and prove the remaining obligations. Establish `hleF : ∀ {v : K}, v ∈ Algebra.adjoin ℤ (Set.range u) → v ∈ ratF x` using `fun hv => Algebra.adjoin_le (S := subalgebraOfSubring (ratF x).toSubring) Subfield.subset_closure hv`. Set `ψ : Algebra.adjoin ℤ (Set.range u) →+* ratF x` to `{ toFun := fun v => ⟨v, hleF v.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `hψ : Function.Injective ψ` using `fun a b h => by`.

Establish `h'` using `congrArg Subtype.val h`. Conclude with `Subtype.ext h'`. Establish `hAlgF : Algebra.IsAlgebraic (ratF x) K` using `⟨fun w => (hAlgU.isAlgebraic w).ringHom_of_comp_eq ψ (RingHom.id K) hψ (by ext; rfl)⟩`. Take `⟨t, ht⟩` from `hA.out`. Set `T : Set K` to `(Subtype.val : A → K) '' (t : Set A)`.

Use `haveI : Finite T := (t.finite_toSet.image _).to_subtype`. Establish `hfd : FiniteDimensional (ratF x) (IntermediateField.adjoin (ratF x) T)` using `IntermediateField.finiteDimensional_adjoin fun w _ => (hAlgF.isAlgebraic w).isIntegral`. Establish `hmemA : ∀ a : A, (a : K) ∈ IntermediateField.adjoin (ratF x) T`. Introduce `a`. Establish `ha : a ∈ Algebra.adjoin ℤ (t : Set A)` using `ht ▸ Algebra.mem_top`.

Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem c hc => exact IntermediateField.subset_adjoin _ _ ⟨c, hc, rfl⟩`. Consider the case `algebraMap n => simpa using IntermediateField.intCast_mem _ n`. Consider the case `add a b _ _ ha hb => simpa using add_mem ha hb`. Consider the case `mul a b _ _ ha hb => simpa using mul_mem ha hb`.

Establish `htop : IntermediateField.adjoin (ratF x) T = ⊤`. Use `eq_top_iff.2 fun w _ => ?_` and prove the remaining obligations. Take `⟨a, ha, b, hb, _, rfl⟩` from `hfr w`. Conclude with `div_mem (hmemA ⟨a, ha⟩) (hmemA ⟨b, hb⟩)`. Rewrite `hfd` using `[htop]`.

Conclude with `IntermediateField.topEquiv.toLinearEquiv.finiteDimensional`.
-/
theorem trBasis_of_integral_ratR (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K) (l : Fin (D + 1))
    (A : Subring K) (htr : Algebra.trdeg ℤ K = D) (hl : x l ≠ 0) (hA : Algebra.FiniteType ℤ A)
    (hint : ∀ w ∈ A, IsIntegral (ratR x l) w)
    (hfr : ∀ w : K, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ w = a / b) :
    (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧
      FiniteDimensional (ratF x) K := by
  haveI : FaithfulSMul ℤ K := (faithfulSMul_iff_algebraMap_injective ℤ K).mpr Int.cast_injective
  set y : Fin (D + 1) → K := fun j => x j / x l with hy
  have hle : ratR x l ≤ (Algebra.adjoin ℤ (Set.range y)).toSubring :=
    Subring.closure_le.2 Algebra.subset_adjoin
  let φ : ratR x l →+* Algebra.adjoin ℤ (Set.range y) :=
    { toFun := fun v => ⟨v, hle v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hAlgA : ∀ w ∈ (A : Set K), IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) w := fun w hw =>
    (IsIntegral.map_of_comp_eq φ (RingHom.id K) (by ext; rfl) (hint w hw)).isAlgebraic
  have hAlgY : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) K := by
    refine isAlgebraic_trans (t := (A : Set K)) ⟨fun w => ?_⟩ hAlgA
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hfr w
    exact isAlgebraic_div_of_mem (Algebra.subset_adjoin ha) (Algebra.subset_adjoin hb) hb0
  set z : Fin D → K := fun j => x (l.succAbove j) / x l with hz
  have hAlgZ : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range z)) K := by
    refine isAlgebraic_trans hAlgY ?_
    rintro _ ⟨j, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩
    · subst h
      simp only [hy, div_self hl]
      exact isAlgebraic_one
    · exact isAlgebraic_algebraMap (⟨z j', Algebra.subset_adjoin ⟨j', rfl⟩⟩ :
        Algebra.adjoin ℤ (Set.range z))
  have hZ : IsTranscendenceBasis ℤ z :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ z (by rw [htr]; simp)
  have hx : ∀ j, x j ≠ 0 := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩
    · exact h ▸ hl
    · intro h0
      exact hZ.1.ne_zero j' (by simp [hz, h0])
  set u : Fin D → K := fun j => x j.succ / x 0 with hu
  have hv : ∀ k, x k / x 0 ∈ Algebra.adjoin ℤ (Set.range u) := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [div_self (hx 0)]; exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin ⟨j, rfl⟩
  have hAlgU : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range u)) K := by
    refine isAlgebraic_trans hAlgZ ?_
    rintro _ ⟨j, rfl⟩
    have e : z j = (x (l.succAbove j) / x 0) / (x l / x 0) := by
      simp only [hz]; field_simp [hx 0, hl]
    rw [e]
    exact isAlgebraic_div_of_mem (hv _) (hv _) (div_ne_zero hl (hx 0))
  have hU : IsTranscendenceBasis ℤ u :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ u (by rw [htr]; simp)
  refine ⟨hx, hU.1, ?_⟩

  have hleF : ∀ {v : K}, v ∈ Algebra.adjoin ℤ (Set.range u) → v ∈ ratF x := fun hv =>
    Algebra.adjoin_le (S := subalgebraOfSubring (ratF x).toSubring) Subfield.subset_closure hv
  let ψ : Algebra.adjoin ℤ (Set.range u) →+* ratF x :=
    { toFun := fun v => ⟨v, hleF v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have hAlgF : Algebra.IsAlgebraic (ratF x) K :=
    ⟨fun w => (hAlgU.isAlgebraic w).ringHom_of_comp_eq ψ (RingHom.id K) hψ (by ext; rfl)⟩
  obtain ⟨t, ht⟩ := hA.out
  let T : Set K := (Subtype.val : A → K) '' (t : Set A)
  haveI : Finite T := (t.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional (ratF x) (IntermediateField.adjoin (ratF x) T) :=
    IntermediateField.finiteDimensional_adjoin fun w _ => (hAlgF.isAlgebraic w).isIntegral
  have hmemA : ∀ a : A, (a : K) ∈ IntermediateField.adjoin (ratF x) T := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (t : Set A) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem c hc => exact IntermediateField.subset_adjoin _ _ ⟨c, hc, rfl⟩
    | algebraMap n => simpa using IntermediateField.intCast_mem _ n
    | add a b _ _ ha hb => simpa using add_mem ha hb
    | mul a b _ _ ha hb => simpa using mul_mem ha hb
  have htop : IntermediateField.adjoin (ratF x) T = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, ha, b, hb, _, rfl⟩ := hfr w
    exact div_mem (hmemA ⟨a, ha⟩) (hmemA ⟨b, hb⟩)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end GlobalTheory.HSAmp.TrBasis
