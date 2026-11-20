import Mathlib
import Formalism.LocalRingCardinality.DataSpaces

noncomputable def UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd :
    {E : Type} →
      [inst : Field E] → [inst_1 : NumberField E] → [inst_2 : StarRing E] → (W : Formalism.BasicNotions.HSpace E) → Set (Fin W.rank → E) :=
    fun {E : Type} [Field E] [NumberField E] [StarRing E] (W : Formalism.BasicNotions.HSpace E) ↦
      {x : Fin W.rank → E | ∑ i : Fin W.rank, x i • (W.frame : Fin W.rank → W.V) i ∈ W.L0}

/- English proof (translation)
Set `b : NumberField.RingOfIntegers E` to `⟨a, ha⟩`. Establish `h : (algebraMap (NumberField.RingOfIntegers E) E b) • v ∈ W.L0`. Rewrite using `[algebraMap_smul]`. Conclude with `W.L0.smul_mem b hv`. Conclude with `h`.
-/
private theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    (W : Formalism.BasicNotions.HSpace E) {a : E} (ha : IsIntegral ℤ a) {v : W.V} (hv : v ∈ W.L0) :
    a • v ∈ W.L0 := by
  let b : NumberField.RingOfIntegers E := ⟨a, ha⟩
  have h : (algebraMap (NumberField.RingOfIntegers E) E b) • v ∈ W.L0 := by
    rw [algebraMap_smul]
    exact W.L0.smul_mem b hv
  exact h

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (W.L0 : Set W.V)`. Rewrite using `[W.standardTuple_isLattice.span_eq_top]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨m, hm, hx⟩` from `hx`. Take `⟨n, hn, hy⟩` from `hy`. Use `⟨m * n, mul_ne_zero hm hn, ?_⟩` and prove the remaining obligations.

Establish `h : ((m * n : ℤ) : E) • (x + y) = n • ((m : E) • x) + m • ((n : E) • y)`. Rewrite using `[← Int.cast_smul_eq_zsmul E n, ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul, smul_add, Int.cast_mul, mul_comm (n : E)]`. Rewrite using `[h]`. Conclude with `W.L0.add_mem (zsmul_mem hx n) (zsmul_mem hy m)`. Consider the case `smul a x _ hx`.

Take `⟨n, hn, hx⟩` from `hx`. Establish `ha : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨m, hm, hint⟩` from `ha.exists_integral_multiple`. Use `⟨m * n, mul_ne_zero hm hn, ?_⟩` and prove the remaining obligations. Establish `hmem` using `UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem W hint hx`.

Establish `h : ((m * n : ℤ) : E) • a • x = (m • a) • ((n : E) • x)`. Rewrite using `[smul_smul, smul_smul, zsmul_eq_mul, Int.cast_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`.

Conclude with `hmem`.
-/
private theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.exists_int_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    (W : Formalism.BasicNotions.HSpace E) (v : W.V) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ W.L0 := by
  have hv : v ∈ Submodule.span E (W.L0 : Set W.V) := by
    rw [W.standardTuple_isLattice.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have h : ((m * n : ℤ) : E) • (x + y) = n • ((m : E) • x) + m • ((n : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E n, ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul,
        smul_add, Int.cast_mul, mul_comm (n : E)]
    rw [h]
    exact W.L0.add_mem (zsmul_mem hx n) (zsmul_mem hy m)
  | smul a x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    have ha : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨m, hm, hint⟩ := ha.exists_integral_multiple
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have hmem := UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem W hint hx
    have h : ((m * n : ℤ) : E) • a • x = (m • a) • ((n : E) • x) := by
      rw [smul_smul, smul_smul, zsmul_eq_mul, Int.cast_mul]
      congr 1
      ring
    rw [h]
    exact hmem

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ W`. Use `choose n hn hmem using fun i : Fin W.rank => UpperTheory.Reformulated.B.EmbeddingTypeJumps.exists_int_smul_mem W (W.frame i)`. Use `⟨((∏ i, n i : ℤ) : NumberField.RingOfIntegers F), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hn i)`. Introduce `i e he`.

Take `⟨k, hk⟩ : n i ∣ ∏ j, n j` from `Finset.dvd_prod_of_mem n (Finset.mem_univ i)`. Establish `hk' : IsIntegral ℤ (k • e)` using `he.smul k`. Establish `hm` using `UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem W hk' (hmem i)`. Establish `hc : ((((∏ j, n j : ℤ) : NumberField.RingOfIntegers F) : F)) • e = (k • e) * (n i : E)`. Rewrite using `[hk, Algebra.smul_def, NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast, map_intCast, zsmul_eq_mul, Int.cast_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `show ∑ j : Fin W.rank, (Pi.single i _ : Fin W.rank → E) j • W.frame j ∈ W.L0`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, hc, mul_smul]`. Conclude with `hm`.
-/
theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd_low :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E]
      [inst_5 : StarRing E] (W : Formalism.BasicNotions.HSpace E),
      ∃ (c : NumberField.RingOfIntegers F),
        c ≠ (0 : NumberField.RingOfIntegers F) ∧
          ∀ (i : Fin W.rank) (e : E), IsIntegral ℤ e → Pi.single i ((↑c : F) • e) ∈ UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd W := by
  intro F E _ _ _ _ _ _ W
  choose n hn hmem using fun i : Fin W.rank => UpperTheory.Reformulated.B.EmbeddingTypeJumps.exists_int_smul_mem W (W.frame i)
  refine ⟨((∏ i, n i : ℤ) : NumberField.RingOfIntegers F), ?_, ?_⟩
  · exact Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hn i)
  · intro i e he
    obtain ⟨k, hk⟩ : n i ∣ ∏ j, n j := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    have hk' : IsIntegral ℤ (k • e) := he.smul k
    have hm := UpperTheory.Reformulated.B.EmbeddingTypeJumps.integral_smul_mem W hk' (hmem i)
    have hc : ((((∏ j, n j : ℤ) : NumberField.RingOfIntegers F) : F)) • e = (k • e) * (n i : E) := by
      rw [hk, Algebra.smul_def, NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast,
        map_intCast, zsmul_eq_mul, Int.cast_mul]
      ring
    show ∑ j : Fin W.rank, (Pi.single i _ : Fin W.rank → E) j • W.frame j ∈ W.L0
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, hc, mul_smul]
    exact hm
