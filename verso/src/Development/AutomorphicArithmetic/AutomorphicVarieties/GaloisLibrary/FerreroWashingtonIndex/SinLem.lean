import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Nzd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SinMap

open UpperTheory.V.FW

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using hx`. Consider the case `insert j S hj ih`. Apply `ih (fun i hi => h i (Finset.mem_insert_of_mem hi))` to reduce the goal to its premises. Apply `nzd k A (a j) _ (h j (Finset.mem_insert_self _ _))` to reduce the goal to its premises.

Rewrite `hx` using `[Finset.prod_insert hj]`. Rewrite using `[← hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem cancel_prod {k A ι : Type} [CommRing k] [AddCommGroup A] [DecidableEq ι] (a : ι → A)
    (S : Finset ι) (h : ∀ j ∈ S, ∀ m : ℕ, m • a j = 0 → m = 0) (x : AddMonoidAlgebra k A)
    (hx : x * ∏ j ∈ S, (1 - AddMonoidAlgebra.single (a j) (1 : k)) = 0) : x = 0 := by
  induction S using Finset.induction_on with
  | empty => simpa using hx
  | insert j S hj ih =>
    apply ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    apply nzd k A (a j) _ (h j (Finset.mem_insert_self _ _))
    rw [Finset.prod_insert hj] at hx
    rw [← hx]; ring

/- English proof (translation)
Introduce `k A ι _ _ _ _ _ η N P hN htor hpair hE s hs`. Take `⟨i0⟩` from `(inferInstance : Nonempty ι)`. Set `H : AddSubgroup A` to `AddSubgroup.zmultiples (N • η i0)`. Set `φ : A →+ A ⧸ H` to `QuotientAddGroup.mk' H`. Establish `hmap` using `sinMap k A (A ⧸ H) ι φ η N P`.

Rewrite `hmap` using `[hE, map_zero]`. Simplify using `only [sinE] at hmap`. Rewrite `hmap` using `[Finset.sum_eq_single i0]`. Establish `hF : (∑ t ∈ Finset.range N, AddMonoidAlgebra.single (t • φ (η i0)) (P t) : AddMonoidAlgebra k (A ⧸ H)) = 0`. Apply `cancel_prod (fun j => N • φ (η j)) (Finset.univ.erase i0) _ _ hmap.symm` to reduce the goal to its premises.

Introduce `j hj m hm`. Establish `hji : j ≠ i0` using `Finset.ne_of_mem_erase hj`. Rewrite `hm` using `[← map_nsmul φ, ← map_nsmul φ]`. Establish `hm' : m • N • η j ∈ H` using `(QuotientAddGroup.eq_zero_iff _).mp hm`. Take `⟨b, hb⟩` from `AddSubgroup.mem_zmultiples_iff.mp hm'`.

Establish `e1 : ((m * N : ℕ) : ℤ) • η j = m • N • η j`. Rewrite using `[natCast_zsmul, mul_smul]`. Establish `e2 : (b * (N : ℤ)) • η i0 = b • N • η i0`. Rewrite using `[mul_smul, natCast_zsmul]`. Establish `hz` using `hpair j i0 hji ((m * N : ℕ) : ℤ) (b * N) (by rw [e1, e2, hb])`.

Establish `hmN : m * N = 0` using `by exact_mod_cast hz`. Break down `Nat.mul_eq_zero.mp hmN with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hN`. Establish `hcoef` using `congrArg (fun f : AddMonoidAlgebra k (A ⧸ H) => f.coeff (s • φ (η i0))) hF`.

Simplify using `only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero, Finsupp.finset_sum_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoef`. Rewrite `hcoef` using `[Finset.sum_eq_single s]`. Simplify using `using hcoef`. Introduce `t ht hts`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `he`. Rewrite `he` using `[← map_nsmul φ, ← map_nsmul φ]`. Establish `hmem` using `(QuotientAddGroup.eq (s := H)).mp he`. Take `⟨b, hb⟩` from `AddSubgroup.mem_zmultiples_iff.mp hmem`. Establish `h0 : (b * N - ((s : ℤ) - t)) • η i0 = 0`.

Rewrite using `[sub_smul, mul_smul, natCast_zsmul, hb, sub_smul, natCast_zsmul, natCast_zsmul]`. Normalize the expressions using the abelian group laws. Establish `h1` using `htor i0 _ h0`. Establish `htN` using `Finset.mem_range.mp ht`. Establish `hts' : (t : ℤ) = s`.

Break down `lt_trichotomy b 0 with hb0 | hb0 | hb0` into its components or cases. Use the polynomial consequences of the given equalities and inequalities. Substitute `hb0` using the available equality. Use linear arithmetic over natural numbers and integers. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `hts (by exact_mod_cast hts')`. Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr hs) h`. Introduce `i _ hi`. Establish `hmem : i0 ∈ Finset.univ.erase i` using `Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ _⟩`.

Rewrite using `[Finset.prod_eq_zero hmem, mul_zero]`. Establish `hz : N • φ (η i0) = 0`. Rewrite using `[← map_nsmul φ]`. Conclude with `(QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples _)`. Rewrite using `[hz, sub_eq_zero]`.

Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ i0) h`.
-/
theorem UpperTheory.V.FW.sinLem :
    ∀ (k A ι : Type) [CommRing k] [AddCommGroup A] [Fintype ι] [DecidableEq ι] [Nonempty ι] (η : ι → A) (N : ℕ) (P : ℕ → k), N ≠ 0 → (∀ i (m : ℤ), m • η i = 0 → m = 0) → (∀ i j, i ≠ j → ∀ a b : ℤ, a • η i = b • η j → a = 0) → sinE η N P = 0 → ∀ s < N, P s = 0 := by
  intro k A ι _ _ _ _ _ η N P hN htor hpair hE s hs
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  let H : AddSubgroup A := AddSubgroup.zmultiples (N • η i0)
  let φ : A →+ A ⧸ H := QuotientAddGroup.mk' H
  have hmap := sinMap k A (A ⧸ H) ι φ η N P
  rw [hE, map_zero] at hmap
  simp only [sinE] at hmap
  rw [Finset.sum_eq_single i0] at hmap
  · have hF : (∑ t ∈ Finset.range N, AddMonoidAlgebra.single (t • φ (η i0)) (P t) : AddMonoidAlgebra k (A ⧸ H)) = 0 := by
      apply cancel_prod (fun j => N • φ (η j)) (Finset.univ.erase i0) _ _ hmap.symm
      intro j hj m hm
      have hji : j ≠ i0 := Finset.ne_of_mem_erase hj
      rw [← map_nsmul φ, ← map_nsmul φ] at hm
      have hm' : m • N • η j ∈ H := (QuotientAddGroup.eq_zero_iff _).mp hm
      obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp hm'
      have e1 : ((m * N : ℕ) : ℤ) • η j = m • N • η j := by
        rw [natCast_zsmul, mul_smul]
      have e2 : (b * (N : ℤ)) • η i0 = b • N • η i0 := by
        rw [mul_smul, natCast_zsmul]
      have hz := hpair j i0 hji ((m * N : ℕ) : ℤ) (b * N) (by rw [e1, e2, hb])
      have hmN : m * N = 0 := by exact_mod_cast hz
      rcases Nat.mul_eq_zero.mp hmN with h | h
      · exact h
      · exact absurd h hN
    have hcoef := congrArg (fun f : AddMonoidAlgebra k (A ⧸ H) => f.coeff (s • φ (η i0))) hF
    simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero,
      Finsupp.finset_sum_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoef
    rw [Finset.sum_eq_single s] at hcoef
    · simpa using hcoef
    · intro t ht hts
      rw [Finsupp.single_apply, if_neg]
      intro he
      rw [← map_nsmul φ, ← map_nsmul φ] at he
      have hmem := (QuotientAddGroup.eq (s := H)).mp he
      obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
      have h0 : (b * N - ((s : ℤ) - t)) • η i0 = 0 := by
        rw [sub_smul, mul_smul, natCast_zsmul, hb, sub_smul, natCast_zsmul, natCast_zsmul]
        abel
      have h1 := htor i0 _ h0
      have htN := Finset.mem_range.mp ht
      have hts' : (t : ℤ) = s := by
        rcases lt_trichotomy b 0 with hb0 | hb0 | hb0
        · nlinarith
        · subst hb0
          omega
        · nlinarith
      exact hts (by exact_mod_cast hts')
    · intro h
      exact absurd (Finset.mem_range.mpr hs) h
  · intro i _ hi
    have hmem : i0 ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hmem, mul_zero]
    have hz : N • φ (η i0) = 0 := by
      rw [← map_nsmul φ]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples _)
    rw [hz, sub_eq_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ i0) h
