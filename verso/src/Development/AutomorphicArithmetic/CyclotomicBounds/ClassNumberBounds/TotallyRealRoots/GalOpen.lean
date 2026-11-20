import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDegree

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

/- English proof (translation)
Establish `hfin : {ζ : AlgebraicClosure E | ζ ^ m = 1}.Finite`. Use `(Polynomial.nthRoots m (1 : AlgebraicClosure E)).toFinset.finite_toSet.subset ?_` and prove the remaining obligations. Introduce `ζ hζ`. Simplify `hζ` using `[Polynomial.mem_nthRoots hm]`. Establish `: Finite {ζ : AlgebraicClosure E | ζ ^ m = 1}` using `hfin.to_subtype`.

Conclude with `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`.
-/
private theorem go_finiteDimensional_adjoinRoots {m : ℕ} (hm : 0 < m) :
    FiniteDimensional E (adjoinRoots E m) := by
  classical
  have hfin : {ζ : AlgebraicClosure E | ζ ^ m = 1}.Finite := by
    refine (Polynomial.nthRoots m (1 : AlgebraicClosure E)).toFinset.finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots hm] using hζ
  have : Finite {ζ : AlgebraicClosure E | ζ ^ m = 1} := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

/- English proof (translation)
Establish `hpos : 0 < l ^ n` using `pow_pos (Fact.out : l.Prime).pos n`. Establish `: NeZero (l ^ n)` using `⟨hpos.ne'⟩`. Establish `: NeZero ((l ^ n : ℕ) : AlgebraicClosure E)` using `⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩`. Use `go_finiteDimensional_adjoinRoots (E := E) hpos` as an intermediate fact. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure E) (l ^ n)`.

Establish `hmem : ζ ∈ adjoinRoots E (l ^ n)` using `IntermediateField.subset_adjoin E _ hζ.pow_eq_one`. Establish `hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : adjoinRoots E (l ^ n)) (l ^ n)` using `IsPrimitiveRoot.of_map_of_injective (f := (adjoinRoots E (l ^ n)).val) hζ Subtype.val_injective`. Establish `: FiniteDimensional ℚ (adjoinRoots E (l ^ n))` using `Module.Finite.trans E _`. Rewrite using `[Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic (l ^ n) ℚ, Polynomial.cyclotomic_eq_minpoly_rat hζ' hpos]`. Conclude with `minpoly.natDegree_le _`.
-/
theorem totient_le_finrank_mul [NumberField E] (n : ℕ) :
    (l ^ n).totient ≤ Module.finrank ℚ E * Module.finrank E (adjoinRoots E (l ^ n)) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have : NeZero ((l ^ n : ℕ) : AlgebraicClosure E) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  have := go_finiteDimensional_adjoinRoots (E := E) hpos
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure E) (l ^ n)
  have hmem : ζ ∈ adjoinRoots E (l ^ n) := IntermediateField.subset_adjoin E _ hζ.pow_eq_one
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : adjoinRoots E (l ^ n)) (l ^ n) :=
    IsPrimitiveRoot.of_map_of_injective (f := (adjoinRoots E (l ^ n)).val) hζ Subtype.val_injective
  have : FiniteDimensional ℚ (adjoinRoots E (l ^ n)) := Module.Finite.trans E _
  rw [Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic (l ^ n) ℚ,
    Polynomial.cyclotomic_eq_minpoly_rat hζ' hpos]
  exact minpoly.natDegree_le _

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hidx : ∀ n, (U ⊔ princ l n).index = (U.map (redPow l n)).index`. Introduce `n`. Use `show (U ⊔ (redPow l n).ker).index = _`. Rewrite using `[Subgroup.index_map, MonoidHom.range_eq_top.mpr (redPow_surjective n), Subgroup.index_top, mul_one]`.

Establish `hne : ∀ n, (U ⊔ princ l n).index ≠ 0`. Introduce `n`. Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Rewrite using `[hidx]`. Conclude with `Subgroup.index_ne_zero_of_finite`.

Establish `hbdd : BddAbove (Set.range fun n => (U ⊔ princ l n).index)`. Use `⟨B, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`. Use `show (U ⊔ princ l n).index ≤ B`. Rewrite using `[hidx]`.

Conclude with `h n`. Take `⟨n₀, hn₀⟩` from `Nat.sSup_mem (Set.range_nonempty _) hbdd`. Establish `hmax : ∀ n, (U ⊔ princ l n).index ≤ (U ⊔ princ l n₀).index`. Introduce `n`. Establish `hc` using `le_csSup hbdd ⟨n, rfl⟩`.

Rewrite `hc` using `[← hn₀]`. Conclude with `hc`. Establish `hstab : ∀ n, n₀ ≤ n → U ⊔ princ l n₀ ≤ U ⊔ princ l n`. Introduce `n hn`. Establish `hle : U ⊔ princ l n ≤ U ⊔ princ l n₀` using `sup_le_sup_left (princ_anti hn) U`.

Establish `hmul` using `Subgroup.relIndex_mul_index hle`. Establish `h1 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) = 1`. Establish `hpos : 0 < (U ⊔ princ l n₀).index` using `Nat.pos_of_ne_zero (hne n₀)`. Establish `hm : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) * (U ⊔ princ l n₀).index ≤ 1 * (U ⊔ princ l n₀).index`. Rewrite using `[hmul, one_mul]`.

Conclude with `hmax n`. Establish `h'` using `Nat.le_of_mul_le_mul_right hm hpos`. Establish `h0 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) ≠ 0`. Introduce `h0`. Rewrite `hmul` using `[h0, zero_mul]`.

Conclude with `hne n hmul.symm`. Use linear arithmetic over natural numbers and integers. Conclude with `Subgroup.relIndex_eq_one.mp h1`. Establish `hsub : U ⊔ princ l n₀ ≤ U`. Introduce `x hx`.

Apply `mem_of_isClosed hU` to reduce the goal to its premises. Introduce `b`. Establish `hxm : x ∈ U ⊔ princ l (max b n₀)` using `hstab _ (le_max_right _ _) hx`. Take `⟨u, hu, z, hz, rfl⟩` from `Subgroup.mem_sup.mp hxm`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations.

Establish `hz' : z ∈ princ l b` using `princ_anti (le_max_left b n₀) hz`. Establish `hz1 : redPow l b z = 1` using `MonoidHom.mem_ker.mp hz'`. Rewrite using `[map_mul, hz1, mul_one]`. Establish `hEq : U ⊔ princ l n₀ = U` using `le_antisymm hsub le_sup_left`. Rewrite using `[← hEq]`.

Conclude with `⟨hne n₀⟩`.
-/
theorem finiteIndex_of_index_map_le {U : Subgroup ℤ_[l]ˣ} (hU : IsClosed (U : Set ℤ_[l]ˣ)) {B : ℕ}
    (h : ∀ n, (U.map (redPow l n)).index ≤ B) : U.FiniteIndex := by
  have hl : l.Prime := Fact.out
  have hidx : ∀ n, (U ⊔ princ l n).index = (U.map (redPow l n)).index := by
    intro n
    show (U ⊔ (redPow l n).ker).index = _
    rw [Subgroup.index_map, MonoidHom.range_eq_top.mpr (redPow_surjective n), Subgroup.index_top,
      mul_one]
  have hne : ∀ n, (U ⊔ princ l n).index ≠ 0 := by
    intro n
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [hidx]
    exact Subgroup.index_ne_zero_of_finite
  have hbdd : BddAbove (Set.range fun n => (U ⊔ princ l n).index) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨n, rfl⟩
    show (U ⊔ princ l n).index ≤ B
    rw [hidx]
    exact h n
  obtain ⟨n₀, hn₀⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  have hmax : ∀ n, (U ⊔ princ l n).index ≤ (U ⊔ princ l n₀).index := by
    intro n
    have hc := le_csSup hbdd ⟨n, rfl⟩
    rw [← hn₀] at hc
    exact hc
  have hstab : ∀ n, n₀ ≤ n → U ⊔ princ l n₀ ≤ U ⊔ princ l n := by
    intro n hn
    have hle : U ⊔ princ l n ≤ U ⊔ princ l n₀ := sup_le_sup_left (princ_anti hn) U
    have hmul := Subgroup.relIndex_mul_index hle
    have h1 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) = 1 := by
      have hpos : 0 < (U ⊔ princ l n₀).index := Nat.pos_of_ne_zero (hne n₀)
      have hm : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) * (U ⊔ princ l n₀).index
          ≤ 1 * (U ⊔ princ l n₀).index := by
        rw [hmul, one_mul]
        exact hmax n
      have h' := Nat.le_of_mul_le_mul_right hm hpos
      have h0 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hmul
        exact hne n hmul.symm
      omega
    exact Subgroup.relIndex_eq_one.mp h1
  have hsub : U ⊔ princ l n₀ ≤ U := by
    intro x hx
    apply mem_of_isClosed hU
    intro b
    have hxm : x ∈ U ⊔ princ l (max b n₀) := hstab _ (le_max_right _ _) hx
    obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hxm
    refine ⟨u, hu, ?_⟩
    have hz' : z ∈ princ l b := princ_anti (le_max_left b n₀) hz
    have hz1 : redPow l b z = 1 := MonoidHom.mem_ker.mp hz'
    rw [map_mul, hz1, mul_one]
  have hEq : U ⊔ princ l n₀ = U := le_antisymm hsub le_sup_left
  rw [← hEq]
  exact ⟨hne n₀⟩

/- English proof (translation)
Rewrite using `[isOpen_iff_isClosed_finiteIndex]`. Use `⟨isClosed_galImage, finiteIndex_of_index_map_le isClosed_galImage (B := Module.finrank ℚ E) fun n => ?_⟩` and prove the remaining obligations. Establish `hl : l.Prime` using `Fact.out`. Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `hN : 0 < l ^ n` using `pow_pos hl.pos n`.

Use `haveI : FiniteDimensional E (adjoinRoots E (l ^ n)) := go_finiteDimensional_adjoinRoots hN`. Establish `hcard` using `Subgroup.index_mul_card ((galImage l E).map (redPow l n))`. Rewrite `hcard` using `[card_map_redPow_galImage, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]`. Establish `htot` using `totient_le_finrank_mul (l := l) (E := E) n`. Establish `hpos : 0 < Module.finrank E (adjoinRoots E (l ^ n))` using `Module.finrank_pos`.

Rewrite `htot` using `[← hcard]`. Conclude with `Nat.le_of_mul_le_mul_right htot hpos`.
-/
theorem isOpen_galImage [NumberField E] : IsOpen (galImage l E : Set ℤ_[l]ˣ) := by
  rw [isOpen_iff_isClosed_finiteIndex]
  refine ⟨isClosed_galImage,
    finiteIndex_of_index_map_le isClosed_galImage (B := Module.finrank ℚ E) fun n => ?_⟩
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hN : 0 < l ^ n := pow_pos hl.pos n
  haveI : FiniteDimensional E (adjoinRoots E (l ^ n)) := go_finiteDimensional_adjoinRoots hN
  have hcard := Subgroup.index_mul_card ((galImage l E).map (redPow l n))
  rw [card_map_redPow_galImage, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hcard
  have htot := totient_le_finrank_mul (l := l) (E := E) n
  have hpos : 0 < Module.finrank E (adjoinRoots E (l ^ n)) := Module.finrank_pos
  rw [← hcard] at htot
  exact Nat.le_of_mul_le_mul_right htot hpos

end KStar.TotallyRealRoots
