import Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality
import Formalism.HyperbolicPlaceProducts.ArithmeticCountRevised

open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure

namespace Formalism.HermitianLatticeCounting.P

/- English proof (translation)
Introduce `E _ _ g a b c d h`. Establish `hI : ∀ y : 𝓞 E, IsInt (y : E)` using `fun y => by unfold IsInt; exact ⟨y, rfl⟩`. Establish `mem : ∀ x y : E, IsInt x → IsInt y → (∃ w : 𝓞 E, x + y = (g : E) * (w : E)) → (x, y) ∈ (ZZ g : Set (E × E))`. Introduce `x y hx hy hw`. Simplify using `only [ZZ, Set.mem_setOf_eq]`.

Conclude with `⟨hx, hy, hw⟩`. Establish `out : ∀ x y : E, (x, y) ∈ (ZZ g : Set (E × E)) → IsInt x ∧ IsInt y`. Introduce `x y hxy`. Simplify using `only [ZZ, Set.mem_setOf_eq] at hxy`. Conclude with `⟨hxy.1, hxy.2.1⟩`.

Establish `hg : IsInt (g : E)` using `by simpa using hI (g : 𝓞 E)`. Establish `h0 : IsInt (0 : E)` using `by simpa using hI 0`. Establish `h1 : IsInt (1 : E)` using `by simpa using hI 1`. Establish `hm1 : IsInt (-1 : E)` using `by simpa using hI (-1)`. Establish `p1` using `out _ _ (h _ (mem _ _ hg h0 ⟨1, by simp⟩))`.

Establish `p2` using `out _ _ (h _ (mem _ _ h0 hg ⟨1, by simp⟩))`. Establish `p3` using `out _ _ (h _ (mem _ _ h1 hm1 ⟨0, by simp⟩))`. Simplify using `only [mul_zero, add_zero, zero_add, mul_one, mul_neg, ← sub_eq_add_neg] at p1 p2 p3`. Use `⟨?_, ?_, ?_, ?_, p3.1, p3.2⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Conclude with `p1.1`. Rewrite using `[mul_comm]`. Conclude with `p2.1`. Rewrite using `[mul_comm]`. Conclude with `p1.2`.

Rewrite using `[mul_comm]`. Conclude with `p2.2`.
-/
theorem integer_group_preservation : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZgPreserve := by
  intro E _ _ g a b c d h
  have hI : ∀ y : 𝓞 E, IsInt (y : E) := fun y => by unfold IsInt; exact ⟨y, rfl⟩
  have mem : ∀ x y : E, IsInt x → IsInt y → (∃ w : 𝓞 E, x + y = (g : E) * (w : E)) →
      (x, y) ∈ (ZZ g : Set (E × E)) := by
    intro x y hx hy hw
    simp only [ZZ, Set.mem_setOf_eq]
    exact ⟨hx, hy, hw⟩
  have out : ∀ x y : E, (x, y) ∈ (ZZ g : Set (E × E)) → IsInt x ∧ IsInt y := by
    intro x y hxy
    simp only [ZZ, Set.mem_setOf_eq] at hxy
    exact ⟨hxy.1, hxy.2.1⟩
  have hg : IsInt (g : E) := by simpa using hI (g : 𝓞 E)
  have h0 : IsInt (0 : E) := by simpa using hI 0
  have h1 : IsInt (1 : E) := by simpa using hI 1
  have hm1 : IsInt (-1 : E) := by simpa using hI (-1)
  have p1 := out _ _ (h _ (mem _ _ hg h0 ⟨1, by simp⟩))
  have p2 := out _ _ (h _ (mem _ _ h0 hg ⟨1, by simp⟩))
  have p3 := out _ _ (h _ (mem _ _ h1 hm1 ⟨0, by simp⟩))
  simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg, ← sub_eq_add_neg] at p1 p2 p3
  refine ⟨?_, ?_, ?_, ?_, p3.1, p3.2⟩
  · rw [mul_comm]; exact p1.1
  · rw [mul_comm]; exact p2.1
  · rw [mul_comm]; exact p1.2
  · rw [mul_comm]; exact p2.2

/- English proof (translation)
Introduce `E _ _ P T T' a b c d hP hT hT' h`. Establish `hT0 : (T : E) ≠ 0` using `Nat.cast_ne_zero.mpr hT.ne'`. Establish `hT'0 : (T' : E) ≠ 0` using `Nat.cast_ne_zero.mpr hT'.ne'`. Establish `h1P : (1 : 𝓞 E) ∉ P` using `(Ideal.ne_top_iff_one P).mp hP.ne_top`. Establish `one : ∀ x : E, x = 1 → LocIn P x 1`.

Introduce `x hx`. Unfold `LocIn`. Conclude with `⟨1, 1, h1P, by simp [hx]⟩`. Establish `zer : ∀ x : E, x = 0 → LocIn P x 1`. Introduce `x hx`.

Unfold `LocIn`. Conclude with `⟨1, 0, h1P, by simp [hx]⟩`. Establish `back : ∀ (x : E) (N : ℕ), (N : E) ≠ 0 → LocIn P (x * (1 / (N : E))) 1 → LocIn P x N`. Introduce `x N hN hx`. Unfold `LocIn at hx ⊢`.

Take `⟨y, z, hy, hyz⟩` from `hx`. Use `⟨y, z, hy, ?_⟩` and prove the remaining obligations. Establish `e : (y : E) * x = (N : E) * ((y : E) * (x * (1 / (N : E))))` using `by first`. Consider the case `field_simp`. Consider the case `rw [mul_one_div, mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hN]`.

Rewrite using `[e, hyz]`. Simplify using the standard rewrite rules. Take `⟨ha, hc⟩` from `h (1 / (T : E)) 0 (one _ (by field_simp)) (zer _ (by simp))`. Take `⟨hb, hd⟩` from `h 0 (1 / (T' : E)) (zer _ (by simp)) (one _ (by field_simp))`. Simplify using `only [mul_zero, add_zero, zero_add] at ha hc hb hd`.

Conclude with `⟨back _ _ hT0 ha, back _ _ hT0 hc, back _ _ hT'0 hb, back _ _ hT'0 hd⟩`.
-/
theorem local_congruence_condition : Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocalCongr := by
  intro E _ _ P T T' a b c d hP hT hT' h
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hT'0 : (T' : E) ≠ 0 := Nat.cast_ne_zero.mpr hT'.ne'
  have h1P : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one P).mp hP.ne_top
  have one : ∀ x : E, x = 1 → LocIn P x 1 := by
    intro x hx; unfold LocIn
    exact ⟨1, 1, h1P, by simp [hx]⟩
  have zer : ∀ x : E, x = 0 → LocIn P x 1 := by
    intro x hx; unfold LocIn
    exact ⟨1, 0, h1P, by simp [hx]⟩
  have back : ∀ (x : E) (N : ℕ), (N : E) ≠ 0 → LocIn P (x * (1 / (N : E))) 1 → LocIn P x N := by
    intro x N hN hx
    unfold LocIn at hx ⊢
    obtain ⟨y, z, hy, hyz⟩ := hx
    refine ⟨y, z, hy, ?_⟩
    have e : (y : E) * x = (N : E) * ((y : E) * (x * (1 / (N : E)))) := by
      first
      | field_simp
      | rw [mul_one_div, mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hN]
    rw [e, hyz]; simp
  obtain ⟨ha, hc⟩ := h (1 / (T : E)) 0 (one _ (by field_simp)) (zer _ (by simp))
  obtain ⟨hb, hd⟩ := h 0 (1 / (T' : E)) (zer _ (by simp)) (one _ (by field_simp))
  simp only [mul_zero, add_zero, zero_add] at ha hc hb hd
  exact ⟨back _ _ hT0 ha, back _ _ hT0 hc, back _ _ hT'0 hb, back _ _ hT'0 hd⟩

/- English proof (translation)
Introduce `E _ _ q x hc hq hx h`. Establish `hm : ∀ w : InfinitePlace E, w.mult = 2` using `fun w => NumberField.InfinitePlace.mult_isComplex ⟨w, hc w⟩`. Establish `hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E)`. Rewrite using `[← NumberField.InfinitePlace.sum_mult_eq]`. Simplify using `only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hm] at h`. Rewrite `h` using `[hn]`. Establish `hP : ∏ w : InfinitePlace E, (x w ^ 2) ^ 2 = (∏ w : InfinitePlace E, x w) ^ 4`. Rewrite using `[← Finset.prod_pow]`.

Conclude with `Finset.prod_congr rfl (fun w _ => by ring)`. Establish `hA : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 = q ^ (2 * Fintype.card (InfinitePlace E))`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 ≤ (∏ w : InfinitePlace E, x w) ^ 4`. Rewrite using `[hA, ← hP]`. Conclude with `h`. Establish `h0 : 0 ≤ ∏ w : InfinitePlace E, x w` using `Finset.prod_nonneg fun w _ => hx w`.

Establish `hq0 : 0 ≤ q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)` using `(Real.rpow_pos_of_pos hq _).le`. Use `first`. Consider the case `exact le_of_pow_le_pow_left₀ (by norm_num) h0 key`. Consider the case `exact (pow_le_pow_iff_left₀ hq0 h0 (by norm_num)).mp key`. Consider the case `exact le_of_pow_le_pow_left (by norm_num) h0 key`.

Consider the case `exact (pow_le_pow_iff_left hq0 h0 (by norm_num)).mp key`.
-/
theorem complex_multiplication_root : Formalism.HermitianLatticeCounting.LocalIntegralStructure.CMRoot := by
  intro E _ _ q x hc hq hx h
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    NumberField.InfinitePlace.mult_isComplex ⟨w, hc w⟩
  have hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  simp only [hm] at h
  rw [hn] at h
  have hP : ∏ w : InfinitePlace E, (x w ^ 2) ^ 2 = (∏ w : InfinitePlace E, x w) ^ 4 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun w _ => by ring)
  have hA : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 =
      q ^ (2 * Fintype.card (InfinitePlace E)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have key : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 ≤ (∏ w : InfinitePlace E, x w) ^ 4 := by
    rw [hA, ← hP]; exact h
  have h0 : 0 ≤ ∏ w : InfinitePlace E, x w := Finset.prod_nonneg fun w _ => hx w
  have hq0 : 0 ≤ q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2) := (Real.rpow_pos_of_pos hq _).le
  first
  | exact le_of_pow_le_pow_left₀ (by norm_num) h0 key
  | exact (pow_le_pow_iff_left₀ hq0 h0 (by norm_num)).mp key
  | exact le_of_pow_le_pow_left (by norm_num) h0 key
  | exact (pow_le_pow_iff_left hq0 h0 (by norm_num)).mp key

namespace IntegralityLocalGlobal

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `first`. Consider the case `exact ha.mul hb`. Consider the case `exact IsIntegral.mul ha hb`. Consider the case `(obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; exact ⟨x * y, by rw [← hx, ← hy]; push_cast; ring⟩)`.
-/
lemma isInt_mul {a b : E} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  first
  | exact ha.mul hb
  | exact IsIntegral.mul ha hb
  | (obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; exact ⟨x * y, by rw [← hx, ← hy]; push_cast; ring⟩)
/- English proof (translation)
Use `first`. Consider the case `exact ha.add hb`. Consider the case `exact IsIntegral.add ha hb`. Consider the case `(obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; exact ⟨x + y, by rw [← hx, ← hy]; push_cast; ring⟩)`.
-/
lemma isInt_add {a b : E} (ha : IsInt a) (hb : IsInt b) : IsInt (a + b) := by
  first
  | exact ha.add hb
  | exact IsIntegral.add ha hb
  | (obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; exact ⟨x + y, by rw [← hx, ← hy]; push_cast; ring⟩)
/- English proof (translation)
Use `first`. Consider the case `exact y.2`. Consider the case `exact ⟨y, rfl⟩`. Consider the case `exact NumberField.RingOfIntegers.isIntegral_coe y`.
-/
lemma isInt_coe (y : 𝓞 E) : IsInt (y : E) := by
  first
  | exact y.2
  | exact ⟨y, rfl⟩
  | exact NumberField.RingOfIntegers.isIntegral_coe y
/- English proof (translation)
Take `⟨x, rfl⟩` from `ha`. Use `first`. Consider the case `exact ⟨⟨σ x, (NumberField.RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom⟩, rfl⟩`. Consider the case `exact ⟨⟨σ x, x.2.map σ.toIntAlgHom⟩, rfl⟩`. Consider the case `exact ⟨NumberField.RingOfIntegers.mapRingHom σ x, rfl⟩`.
-/
lemma isInt_map (σ : E →+* E) {a : E} (ha : IsInt a) : IsInt (σ a) := by
  obtain ⟨x, rfl⟩ := ha
  first
  | exact ⟨⟨σ x, (NumberField.RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom⟩, rfl⟩
  | exact ⟨⟨σ x, x.2.map σ.toIntAlgHom⟩, rfl⟩
  | exact ⟨NumberField.RingOfIntegers.mapRingHom σ x, rfl⟩

/- English proof (translation)
Set `I : Ideal (𝓞 E)` to `{ carrier := {y | IsInt ((y : E) * x)} add_mem' := fun {a b} ha hb => by show IsInt (((a + b : 𝓞 E) : E) * x)`. Use `isInt_add ha hb using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `zero_mem' := by show IsInt (((0 : 𝓞 E) : E) * x)`.

Use `isInt_coe (0 : 𝓞 E) using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `smul_mem' := fun c y hy => by show IsInt (((c • y : 𝓞 E) : E) * x)`. Use `isInt_mul (isInt_coe c) hy using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[smul_eq_mul]`. Use `push_cast`. Use `ring }`. Establish `hI : I = ⊤`. Assume the negation of the conclusion as `hne`.

Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I hne`. Take `⟨y, hy, hyx⟩` from `h M hM.isPrime`. Conclude with `hy (hIM (show y ∈ I from hyx))`. Establish `h1 : (1 : 𝓞 E) ∈ I` using `by rw [hI]; exact Submodule.mem_top`. Establish `h1' : IsInt (((1 : 𝓞 E) : E) * x)` using `h1`.

Use `h1' using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma locGlob (x : E) (h : ∀ P : Ideal (𝓞 E), P.IsPrime → ∃ y : 𝓞 E, y ∉ P ∧ IsInt ((y : E) * x)) :
    IsInt x := by
  let I : Ideal (𝓞 E) :=
    { carrier := {y | IsInt ((y : E) * x)}
      add_mem' := fun {a b} ha hb => by
        show IsInt (((a + b : 𝓞 E) : E) * x)
        convert isInt_add ha hb using 1
        push_cast; ring
      zero_mem' := by
        show IsInt (((0 : 𝓞 E) : E) * x)
        convert isInt_coe (0 : 𝓞 E) using 1
        push_cast; ring
      smul_mem' := fun c y hy => by
        show IsInt (((c • y : 𝓞 E) : E) * x)
        convert isInt_mul (isInt_coe c) hy using 1
        rw [smul_eq_mul]; push_cast; ring }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨y, hy, hyx⟩ := h M hM.isPrime
    exact hy (hIM (show y ∈ I from hyx))
  have h1 : (1 : 𝓞 E) ∈ I := by rw [hI]; exact Submodule.mem_top
  have h1' : IsInt (((1 : 𝓞 E) : E) * x) := h1
  convert h1' using 1
  push_cast; ring

/- English proof (translation)
Establish `hN0 : (N : E) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`. Establish `hx : IsInt (e / (N : E))`. Apply `locGlob` to reduce the goal to its premises. Introduce `P hP`. Distinguish the cases in `hNP : (N : 𝓞 E) ∈ P`.

Take `⟨y, z, hy, hyz⟩` from `h P hP hNP`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Use `isInt_coe z using 1` and compare the differences between its conclusion and the goal. Rewrite using `[mul_div_assoc', hyz]`. Clear the denominators using the available nonvanishing facts.

Use `⟨(N : 𝓞 E), hNP, ?_⟩` and prove the remaining obligations. Use `he using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take `⟨β, hβ⟩` from `hx`.

Use `⟨β, ?_⟩` and prove the remaining obligations. Rewrite using `[hβ]`. Clear the denominators using the available nonvanishing facts.
-/
lemma divGlob (e : E) (N : ℕ) (hN : 0 < N) (he : IsInt e)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P e N) :
    ∃ β : 𝓞 E, e = (N : E) * (β : E) := by
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hx : IsInt (e / (N : E)) := by
    apply locGlob
    intro P hP
    by_cases hNP : (N : 𝓞 E) ∈ P
    · obtain ⟨y, z, hy, hyz⟩ := h P hP hNP
      refine ⟨y, hy, ?_⟩
      convert isInt_coe z using 1
      rw [mul_div_assoc', hyz]
      field_simp
    · refine ⟨(N : 𝓞 E), hNP, ?_⟩
      convert he using 1
      push_cast
      field_simp
  obtain ⟨β, hβ⟩ := hx
  refine ⟨β, ?_⟩
  rw [hβ]
  field_simp

end IntegralityLocalGlobal

open IntegralityLocalGlobal

/- English proof (translation)
Establish `hM0 : (M : E) ≠ 0` using `Nat.cast_ne_zero.mpr hM.ne'`. Set `f : 𝓞 E →+* 𝓞 E` to `NumberField.RingOfIntegers.mapRingHom σ`. Establish `hf : ∀ y : 𝓞 E, ((f y : 𝓞 E) : E) = σ (y : E)` using `fun y => rfl`. Establish `hQ : (P.comap f).IsPrime` using `by haveI := hP first`. Consider the case `exact Ideal.comap_isPrime f P`.

Consider the case `exact Ideal.IsPrime.comap f`. Consider the case `infer_instance`. Establish `hMQ : (M : 𝓞 E) ∈ P.comap f`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hMP`.

Take `⟨y1, z1, hy1, h1⟩` from `hu P hP hMP`. Take `⟨y2, z2, hy2, h2⟩` from `hu _ hQ hMQ`. Establish `h2' : ((f y2 : 𝓞 E) : E) * σ u = (M : E) * ((f z2 : 𝓞 E) : E)`. Establish `h3` using `congrArg σ h2`. Rewrite `h3` using `[map_mul, map_mul, map_natCast]`.

Rewrite using `[hf, hf]`. Conclude with `h3`. Establish `hE : e * (M : E) = (g : E) ^ 2 * ((M' : E) * u * σ u)`. Rewrite using `[he]`. Use `first`.

Consider the case `rw [mul_div_assoc', div_mul_cancel₀ _ hM0]`. Consider the case `field_simp`. Apply the tactic sequence `have c1 : ((y1 * f y2 : 𝓞 E) : E) = (y1 : E) * ((f y2 : 𝓞 E) : E) := by first | rfl | (push_cast; rfl) | simp`. Apply the tactic sequence `have c2 : ((z1 * f z2 : 𝓞 E) : E) = (z1 : E) * ((f z2 : 𝓞 E) : E) := by first | rfl | (push_cast; rfl) | simp`. Use `⟨y1 * f y2, z1 * f z2, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hmem`. Break down `hP.mem_or_mem hmem with h | h` into its components or cases. Conclude with `hy1 h`. Conclude with `hy2 (Ideal.mem_comap.mpr h)`. Rewrite using `[c1, c2]`.

Apply `mul_right_cancel₀ hM0` to reduce the goal to its premises. Take the linear combination `((y1 : E) * ((f y2 : 𝓞 E) : E)) * hE + ((g : E) ^ 2 * (M' : E) * (((f y2 : 𝓞 E) : E) * σ u)) * h1 + ((g : E) ^ 2 * (M' : E) * (M : E) * (z1 : E)) * h2'`.
-/
private theorem exists_not_mem_prime_mul_eq_of_locIn {E : Type} [Field E] [NumberField E] (σ : E →+* E) (M M' g : ℕ) (u e : E)
    (hM : 0 < M) (he : e = (g : E) ^ 2 * ((M' : E) * u * σ u / (M : E)))
    (hu : ∀ P : Ideal (𝓞 E), P.IsPrime → (M : 𝓞 E) ∈ P → LocIn P u M)
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hMP : (M : 𝓞 E) ∈ P) :
    ∃ y z : 𝓞 E, y ∉ P ∧ (y : E) * e = (M : E) * (M' : E) * (g : E) ^ 2 * (z : E) := by
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  let f : 𝓞 E →+* 𝓞 E := NumberField.RingOfIntegers.mapRingHom σ
  have hf : ∀ y : 𝓞 E, ((f y : 𝓞 E) : E) = σ (y : E) := fun y => rfl
  have hQ : (P.comap f).IsPrime := by
    haveI := hP
    first
    | exact Ideal.comap_isPrime f P
    | exact Ideal.IsPrime.comap f
    | infer_instance
  have hMQ : (M : 𝓞 E) ∈ P.comap f := by
    rw [Ideal.mem_comap, map_natCast]; exact hMP
  obtain ⟨y1, z1, hy1, h1⟩ := hu P hP hMP
  obtain ⟨y2, z2, hy2, h2⟩ := hu _ hQ hMQ
  have h2' : ((f y2 : 𝓞 E) : E) * σ u = (M : E) * ((f z2 : 𝓞 E) : E) := by
    have h3 := congrArg σ h2
    rw [map_mul, map_mul, map_natCast] at h3
    rw [hf, hf]; exact h3
  have hE : e * (M : E) = (g : E) ^ 2 * ((M' : E) * u * σ u) := by
    rw [he]
    first
    | rw [mul_div_assoc', div_mul_cancel₀ _ hM0]
    | field_simp
  have c1 : ((y1 * f y2 : 𝓞 E) : E) = (y1 : E) * ((f y2 : 𝓞 E) : E) := by
    first | rfl | (push_cast; rfl) | simp
  have c2 : ((z1 * f z2 : 𝓞 E) : E) = (z1 : E) * ((f z2 : 𝓞 E) : E) := by
    first | rfl | (push_cast; rfl) | simp
  refine ⟨y1 * f y2, z1 * f z2, ?_, ?_⟩
  · intro hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact hy1 h
    · exact hy2 (Ideal.mem_comap.mpr h)
  · rw [c1, c2]
    apply mul_right_cancel₀ hM0
    linear_combination ((y1 : E) * ((f y2 : 𝓞 E) : E)) * hE
      + ((g : E) ^ 2 * (M' : E) * (((f y2 : 𝓞 E) : E) * σ u)) * h1
      + ((g : E) ^ 2 * (M' : E) * (M : E) * (z1 : E)) * h2'

/- English proof (translation)
Introduce `E _ _ σ T T' g s b c hT hT' hs1 hs2 hgb hgc hc hb`. Establish `hT0 : (T : E) ≠ 0` using `Nat.cast_ne_zero.mpr hT.ne'`. Establish `hTT : 0 < T * T'` using `Nat.mul_pos hT hT'`. Establish `e1 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T' : E) * c * σ c / (T : E))` using `by rw [hs1]`. Establish `e2 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T : E) * b * σ b / (T' : E))` using `by rw [hs2]`.

Establish `hint : IsInt ((g : E) ^ 2 * s)`. Apply `locGlob` to reduce the goal to its premises. Introduce `P hP`. Distinguish the cases in `hTP : (T : 𝓞 E) ∈ P`. Take `⟨y, z, hy, hyz⟩` from `exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP hTP`.

Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hyz]`. Use `isInt_coe ((T : 𝓞 E) * (T' : 𝓞 E) * (g : 𝓞 E) ^ 2 * z) using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨(T : 𝓞 E), hTP, ?_⟩` and prove the remaining obligations. Establish `hh` using `isInt_mul (isInt_mul (isInt_coe (T' : 𝓞 E)) hgc) (isInt_map σ hgc)`. Use `hh using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hs1, map_mul, map_natCast]`. Use `push_cast`.

Use `first`. Consider the case `(rw [mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hT0]; ring)`. Consider the case `(field_simp; ring)`. Consider the case `field_simp`. Establish `hloc : ∀ P : Ideal (𝓞 E), P.IsPrime → ((T * T' : ℕ) : 𝓞 E) ∈ P → LocIn P ((g : E) ^ 2 * s) (T * T')`.

Introduce `P hP hmem`. Rewrite `hmem` using `[Nat.cast_mul]`. Unfold `LocIn`. Break down `hP.mem_or_mem hmem with h | h` into its components or cases. Take `⟨y, z, hy, hyz⟩` from `exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP h`.

Use `⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hyz]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨y, z, hy, hyz⟩` from `exists_not_mem_prime_mul_eq_of_locIn σ T' T g b _ hT' e2 hb P hP h`.

Use `⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hyz]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨β, hβ⟩` from `divGlob _ (T * T') hTT hint hloc`.

Use `⟨β, ?_⟩` and prove the remaining obligations. Rewrite using `[hβ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem s_integrality : Formalism.HermitianLatticeCounting.LocalIntegralStructure.SInt := by
  intro E _ _ σ T T' g s b c hT hT' hs1 hs2 hgb hgc hc hb
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hTT : 0 < T * T' := Nat.mul_pos hT hT'
  have e1 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T' : E) * c * σ c / (T : E)) := by rw [hs1]
  have e2 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T : E) * b * σ b / (T' : E)) := by rw [hs2]
  have hint : IsInt ((g : E) ^ 2 * s) := by
    apply locGlob
    intro P hP
    by_cases hTP : (T : 𝓞 E) ∈ P
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP hTP
      refine ⟨y, hy, ?_⟩
      rw [hyz]
      convert isInt_coe ((T : 𝓞 E) * (T' : 𝓞 E) * (g : 𝓞 E) ^ 2 * z) using 1
      push_cast; ring
    · refine ⟨(T : 𝓞 E), hTP, ?_⟩
      have hh := isInt_mul (isInt_mul (isInt_coe (T' : 𝓞 E)) hgc) (isInt_map σ hgc)
      convert hh using 1
      rw [hs1, map_mul, map_natCast]
      push_cast
      first
      | (rw [mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hT0]; ring)
      | (field_simp; ring)
      | field_simp
  have hloc : ∀ P : Ideal (𝓞 E), P.IsPrime → ((T * T' : ℕ) : 𝓞 E) ∈ P →
      LocIn P ((g : E) ^ 2 * s) (T * T') := by
    intro P hP hmem
    rw [Nat.cast_mul] at hmem
    unfold LocIn
    rcases hP.mem_or_mem hmem with h | h
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP h
      refine ⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩
      rw [hyz]; push_cast; ring
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T' T g b _ hT' e2 hb P hP h
      refine ⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩
      rw [hyz]; push_cast; ring
  obtain ⟨β, hβ⟩ := divGlob _ (T * T') hTT hint hloc
  refine ⟨β, ?_⟩
  rw [hβ]; push_cast; ring

namespace IntegralityLocalGlobal

/- English proof (translation)
Establish `h1` using `h 1 0`. Establish `h2` using `h 0 1`. Establish `h3` using `h 1 1`. Establish `h4` using `h 1 Complex.I`. Use `first`.

Consider the case `simp only [← Complex.normSq_eq_norm_sq] at h1 h2 h3 h4 ⊢`. Consider the case `simp only [Complex.sq_norm] at h1 h2 h3 h4 ⊢`. Simplify using `only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im] at h1 h2 h3 h4 ⊢`. Take the linear combination `(T * (a.re * b.re + a.im * b.im) + T' * (c.re * d.re + c.im * d.im)) / 2 * (h3 - h1 - h2) + (T * (a.im * b.re - a.re * b.im) + T' * (c.im * d.re - c.re * d.im)) / 2 * (h4 - h1 - h2) - T * (b.re * b.re + b.im * b.im) * h1 - T' * (c.re * c.re + c.im * c.im) * h2`.
-/
lemma formEq (a b c d : ℂ) (T T' : ℝ)
    (h : ∀ u v : ℂ, T * ‖a * u + b * v‖ ^ 2 - T' * ‖c * u + d * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2) :
    T ^ 2 * ‖b‖ ^ 2 = T' ^ 2 * ‖c‖ ^ 2 := by
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  have h4 := h 1 Complex.I
  first
  | simp only [← Complex.normSq_eq_norm_sq] at h1 h2 h3 h4 ⊢
  | simp only [Complex.sq_norm] at h1 h2 h3 h4 ⊢
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Complex.I_re,
    Complex.I_im] at h1 h2 h3 h4 ⊢
  linear_combination
    (T * (a.re * b.re + a.im * b.im) + T' * (c.re * d.re + c.im * d.im)) / 2 * (h3 - h1 - h2)
    + (T * (a.im * b.re - a.re * b.im) + T' * (c.im * d.re - c.re * d.im)) / 2 * (h4 - h1 - h2)
    - T * (b.re * b.re + b.im * b.im) * h1 - T' * (c.re * c.re + c.im * c.im) * h2

end IntegralityLocalGlobal

/- English proof (translation)
Introduce `E _ _ σ hσ hcx T T' g a b c d x hT hT' hg hiso hZZ hloc hx hxw`. Establish `hTpos : 0 < T` using `by omega`. Establish `hT'pos : 0 < T'` using `by omega`. Establish `hTr : (0 : ℝ) < T` using `by exact_mod_cast hTpos`. Establish `hT'r : (0 : ℝ) < T'` using `by exact_mod_cast hT'pos`.

Establish `hgr : (0 : ℝ) < g` using `by exact_mod_cast (show 0 < g by omega)`. Establish `hm : ∀ w : InfinitePlace E, w.mult = 2` using `fun w => NumberField.InfinitePlace.mult_isComplex ⟨w, hcx w⟩`. Establish `hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E)`. Rewrite using `[← NumberField.InfinitePlace.sum_mult_eq]`. Simplify using `only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hne : Nonempty (InfinitePlace E)` using `by first`. Consider the case `infer_instance`. Consider the case `(apply Fintype.card_pos_iff.mp`. Use `Module.finrank_pos (R := ℚ) (M := E)` as an intermediate fact.

Use the proof step `omega)`. Take `⟨w0⟩` from `hne`. Establish `hcard : 1 ≤ Fintype.card (InfinitePlace E)` using `Fintype.card_pos_iff.mpr ⟨w0⟩`. Establish `hnw : ∀ (w : InfinitePlace E) (y : E), w y = ‖w.embedding y‖` using `fun w y => (NumberField.InfinitePlace.norm_embedding_eq w y).symm`. Establish `hI : ∀ y : 𝓞 E, IsInt (y : E)` using `fun y => by unfold IsInt; exact ⟨y, rfl⟩`.

Establish `hm1 : IsInt (-1 : E)` using `by simpa using hI (-1)`. Establish `h1 : IsInt (1 : E)` using `by simpa using hI 1`. Establish `normge : ∀ β : 𝓞 E, β ≠ 0 → 1 ≤ ∏ w : InfinitePlace E, (w (β : E)) ^ 2`. Introduce `β hβ`. Establish `hp` using `NumberField.InfinitePlace.prod_eq_abs_norm (β : E)`.

Simplify using `only [hm] at hp`. Rewrite using `[hp, ← Algebra.coe_norm_int]`. Establish `hn0 : Algebra.norm ℤ β ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hβ`. Establish `h2 : (1 : ℤ) ≤ |Algebra.norm ℤ β|` using `Int.one_le_abs hn0`. Conclude with `h2` after adjusting the coercions.

Establish `hwn : ∀ w : InfinitePlace E, (T : ℝ) ^ 2 * ‖w.embedding b‖ ^ 2 = (T' : ℝ) ^ 2 * ‖w.embedding c‖ ^ 2` using `fun w => formEq _ _ _ _ _ _ (hiso w.embedding)`. Establish `zz` using `integer_group_preservation E g a b c d hZZ`. Establish `unit1 : ∀ (y : E) (N : ℕ), 3 ≤ N → IsInt (y - 1) → (∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P (y - 1) N) → (∀ w : InfinitePlace E, ‖w.embedding y‖ = 1) → y = 1`. Introduce `y N hN hi hl hy`. Take `⟨β, hβ⟩` from `divGlob (y - 1) N (by omega) hi hl`.

Assume the negation of the conclusion as `hne`. Establish `hβ0 : β ≠ 0`. Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises. Establish `h0 : y - 1 = 0` using `by rw [hβ]; simp`.

Conclude with `sub_eq_zero.mp h0`. Establish `hNr : (3 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hb : ∀ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ 4 / 9`. Introduce `w`. Establish `h5 : w.embedding y - 1 = (N : ℂ) * w.embedding (β : E)`.

Rewrite using `[← map_one w.embedding, ← map_sub, hβ, map_mul, map_natCast]`. Establish `e1 : (N : ℝ) * ‖w.embedding (β : E)‖ = ‖w.embedding y - 1‖`. Rewrite using `[h5, norm_mul]`. Simplify using the standard rewrite rules. Establish `e2 : ‖w.embedding y - 1‖ ≤ 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `e3 : 0 ≤ ‖w.embedding (β : E)‖` using `norm_nonneg _`. Establish `e4 : ‖w.embedding (β : E)‖ ≤ 2 / 3`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hNr) e3]`. Rewrite using `[hnw]`.

Use polynomial arithmetic with `[mul_nonneg e3 (sub_nonneg.mpr e4)]`. Establish `hprod : ∏ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ ∏ _w : InfinitePlace E, (4 / 9 : ℝ)` using `Finset.prod_le_prod (fun w _ => sq_nonneg _) (fun w _ => hb w)`. Rewrite `hprod` using `[Finset.prod_const, Finset.card_univ]`. Establish `h49 : (4 / 9 : ℝ) ^ Fintype.card (InfinitePlace E) ≤ 4 / 9` using `pow_le_of_le_one (by norm_num) (by norm_num) (by omega)`. Combine the linear relations using `[normge β hβ0]`.

Distinguish the cases in `hc0 : c = 0`. Use `left`. Establish `hb0 : b = 0`. Establish `h` using `hwn w0`. Rewrite `h` using `[hc0, map_zero, norm_zero]`.

Establish `h2 : ‖w0.embedding b‖ ^ 2 = 0` using `mul_left_cancel₀ (pow_ne_zero 2 hTr.ne') (by rw [h]; ring)`. Establish `h3 : w0.embedding b = 0` using `norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)`. Conclude with `(map_eq_zero_iff _ w0.embedding.injective).mp h3`. Establish `ha1 : ∀ w : InfinitePlace E, ‖w.embedding a‖ = 1`. Introduce `w`.

Establish `h` using `hiso w.embedding 1 0`. Rewrite `h` using `[hb0, hc0]`. Simplify using `only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h`. Establish `h2 : (T : ℝ) * (‖w.embedding a‖ ^ 2 - 1) = 0` using `by linear_combination h`. Establish `h3` using `(mul_eq_zero.mp h2).resolve_left hTr.ne'`.

Use polynomial arithmetic with `[norm_nonneg (w.embedding a)]`. Establish `hd1 : ∀ w : InfinitePlace E, ‖w.embedding d‖ = 1`. Introduce `w`. Establish `h` using `hiso w.embedding 0 1`. Rewrite `h` using `[hb0, hc0]`.

Simplify using `only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h`. Establish `h2 : (T' : ℝ) * (‖w.embedding d‖ ^ 2 - 1) = 0` using `by linear_combination -h`. Establish `h3` using `(mul_eq_zero.mp h2).resolve_left hT'r.ne'`. Use polynomial arithmetic with `[norm_nonneg (w.embedding d)]`. Establish `ha : a = 1` using `unit1 a T hT (by convert isInt_add zz.2.2.2.2.1 hm1 using 1; rw [hb0]; ring) (fun P hP h => (hloc P hP (Or.inl h)).1) ha1`.

Establish `hd : d = 1` using `unit1 d T' hT' (by convert isInt_mul hm1 (isInt_add zz.2.2.2.2.2 h1) using 1; rw [hc0]; ring) (fun P hP h => (hloc P hP (Or.inr h)).2.2.2) hd1`. Conclude with `⟨ha, hb0, hc0, hd⟩`. Use `right`. Take `⟨s, hs1⟩ : ∃ s : E, s = (T' : E) * c * σ c / (T : E)` from `⟨_, rfl⟩`. Establish `hs2 : s = (T : E) * b * σ b / (T' : E)`.

Rewrite using `[hs1]`. Apply `w0.embedding.injective` to reduce the goal to its premises. Establish `hconj : ∀ z : E, w0.embedding z * w0.embedding (σ z) = ((‖w0.embedding z‖ ^ 2 : ℝ) : ℂ)`. Introduce `z`. Rewrite using `[hσ, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Simplify using `only [map_div₀, map_mul, map_natCast]`. Rewrite using `[mul_assoc, mul_assoc, hconj, hconj]`. Establish `hTc : (T : ℂ) ≠ 0` using `by exact_mod_cast hTpos.ne'`. Establish `hT'c : (T' : ℂ) ≠ 0` using `by exact_mod_cast hT'pos.ne'`. Rewrite using `[div_eq_div_iff hTc hT'c]`.

Establish `h'` using `congrArg (fun r : ℝ => (r : ℂ)) (hwn w0)`. Move the coercions through the operations in `at h' ⊢`. Take the linear combination `-h'`. Take `⟨β, hβ⟩` from `s_integrality E σ T T' g s b c hTpos hT'pos hs1 hs2 zz.2.1 zz.2.2.1 (fun P hP h => (hloc P hP (Or.inl h)).2.1) (fun P hP h => (hloc P hP (Or.inr h)).2.2.1)`. Establish `hs0 : s ≠ 0`.

Rewrite using `[hs1]`. Establish `hσc : σ c ≠ 0` using `fun h => hc0 (σ.injective (by rw [h, map_zero]))`. Establish `hT0 : (T : E) ≠ 0` using `Nat.cast_ne_zero.mpr hTpos.ne'`. Establish `hT'0 : (T' : E) ≠ 0` using `Nat.cast_ne_zero.mpr hT'pos.ne'`. Conclude with `div_ne_zero (mul_ne_zero (mul_ne_zero hT'0 hc0) hσc) hT0`.

Establish `hβ0 : β ≠ 0`. Introduce and unpack `rfl`. Establish `hg0 : (g : E) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Establish `h0 : (g : E) ^ 2 * s = 0` using `by rw [hβ]; simp`. Conclude with `hs0 ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hg0))`.

Use `set q : ℝ := (T : ℝ) * T' / (g : ℝ) ^ 2 with hq_def`. Establish `hq : 0 < q` using `div_pos (mul_pos hTr hT'r) (pow_pos hgr 2)`. Establish `key : ∀ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤ (x w ^ 2) ^ 2`. Introduce `w`. Establish `A : (g : ℝ) ^ 2 * ‖w.embedding s‖ = (T : ℝ) * T' * ‖w.embedding (β : E)‖`.

Establish `h` using `congrArg (fun y => ‖w.embedding y‖) hβ`. Simplify `h` using `[map_mul, map_pow, map_natCast, norm_mul, norm_pow]`. Establish `B : ‖w.embedding s‖ = (T' : ℝ) * ‖w.embedding c‖ ^ 2 / T`. Rewrite using `[hs1]`. Apply the tactic sequence `simp [hσ, norm_div] <;> ring`.

Establish `C` using `hxw w`. Rewrite `C` using `[hnw w c]`. Establish `hs_le : ‖w.embedding s‖ ≤ x w ^ 2` using `by rw [B]; exact C`. Establish `hs_eq : ‖w.embedding s‖ = q * ‖w.embedding (β : E)‖`. Rewrite using `[hq_def, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hgr.ne')]`.

Take the linear combination `A`. Rewrite using `[hnw w, ← mul_pow, ← hs_eq]`. Use `first`. Consider the case `exact pow_le_pow_left (norm_nonneg _) hs_le 2`. Consider the case `exact pow_le_pow_left₀ (norm_nonneg _) hs_le 2`.

Consider the case `nlinarith [norm_nonneg (w.embedding s)]`. Apply `complex_multiplication_root E q x hcx hq hx` to reduce the goal to its premises. Simplify using `only [hm]`. Rewrite using `[hn, pow_mul]`. Establish `hprod : ∏ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤ ∏ w : InfinitePlace E, (x w ^ 2) ^ 2` using `Finset.prod_le_prod (fun w _ => by positivity) (fun w _ => key w)`.

Rewrite `hprod` using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Establish `hqn : 0 ≤ (q ^ 2) ^ Fintype.card (InfinitePlace E)` using `by positivity`. Establish `h3` using `mul_le_mul_of_nonneg_left (normge β hβ0) hqn`. Rewrite `h3` using `[mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem theorem_B_statement : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ThmB := by
  intro E _ _ σ hσ hcx T T' g a b c d x hT hT' hg hiso hZZ hloc hx hxw
  have hTpos : 0 < T := by omega
  have hT'pos : 0 < T' := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hT'r : (0 : ℝ) < T' := by exact_mod_cast hT'pos
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    NumberField.InfinitePlace.mult_isComplex ⟨w, hcx w⟩
  have hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hne : Nonempty (InfinitePlace E) := by
    first
    | infer_instance
    | (apply Fintype.card_pos_iff.mp
       have := Module.finrank_pos (R := ℚ) (M := E)
       omega)
  obtain ⟨w0⟩ := hne
  have hcard : 1 ≤ Fintype.card (InfinitePlace E) := Fintype.card_pos_iff.mpr ⟨w0⟩
  have hnw : ∀ (w : InfinitePlace E) (y : E), w y = ‖w.embedding y‖ := fun w y =>
    (NumberField.InfinitePlace.norm_embedding_eq w y).symm
  have hI : ∀ y : 𝓞 E, IsInt (y : E) := fun y => by unfold IsInt; exact ⟨y, rfl⟩
  have hm1 : IsInt (-1 : E) := by simpa using hI (-1)
  have h1 : IsInt (1 : E) := by simpa using hI 1
  have normge : ∀ β : 𝓞 E, β ≠ 0 → 1 ≤ ∏ w : InfinitePlace E, (w (β : E)) ^ 2 := by
    intro β hβ
    have hp := NumberField.InfinitePlace.prod_eq_abs_norm (β : E)
    simp only [hm] at hp
    rw [hp, ← Algebra.coe_norm_int]
    have hn0 : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    have h2 : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs hn0
    exact_mod_cast h2
  have hwn : ∀ w : InfinitePlace E,
      (T : ℝ) ^ 2 * ‖w.embedding b‖ ^ 2 = (T' : ℝ) ^ 2 * ‖w.embedding c‖ ^ 2 := fun w =>
    formEq _ _ _ _ _ _ (hiso w.embedding)
  have zz := integer_group_preservation E g a b c d hZZ
  have unit1 : ∀ (y : E) (N : ℕ), 3 ≤ N → IsInt (y - 1) →
      (∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P (y - 1) N) →
      (∀ w : InfinitePlace E, ‖w.embedding y‖ = 1) → y = 1 := by
    intro y N hN hi hl hy
    obtain ⟨β, hβ⟩ := divGlob (y - 1) N (by omega) hi hl
    by_contra hne
    have hβ0 : β ≠ 0 := by
      rintro rfl
      apply hne
      have h0 : y - 1 = 0 := by rw [hβ]; simp
      exact sub_eq_zero.mp h0
    have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hb : ∀ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ 4 / 9 := by
      intro w
      have h5 : w.embedding y - 1 = (N : ℂ) * w.embedding (β : E) := by
        rw [← map_one w.embedding, ← map_sub, hβ, map_mul, map_natCast]
      have e1 : (N : ℝ) * ‖w.embedding (β : E)‖ = ‖w.embedding y - 1‖ := by
        rw [h5, norm_mul]
        simp
      have e2 : ‖w.embedding y - 1‖ ≤ 2 := by
        calc ‖w.embedding y - 1‖ ≤ ‖w.embedding y‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [hy w, norm_one]; norm_num
      have e3 : 0 ≤ ‖w.embedding (β : E)‖ := norm_nonneg _
      have e4 : ‖w.embedding (β : E)‖ ≤ 2 / 3 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hNr) e3]
      rw [hnw]
      nlinarith [mul_nonneg e3 (sub_nonneg.mpr e4)]
    have hprod : ∏ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ ∏ _w : InfinitePlace E, (4 / 9 : ℝ) :=
      Finset.prod_le_prod (fun w _ => sq_nonneg _) (fun w _ => hb w)
    rw [Finset.prod_const, Finset.card_univ] at hprod
    have h49 : (4 / 9 : ℝ) ^ Fintype.card (InfinitePlace E) ≤ 4 / 9 :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [normge β hβ0]
  by_cases hc0 : c = 0
  · left
    have hb0 : b = 0 := by
      have h := hwn w0
      rw [hc0, map_zero, norm_zero] at h
      have h2 : ‖w0.embedding b‖ ^ 2 = 0 :=
        mul_left_cancel₀ (pow_ne_zero 2 hTr.ne') (by rw [h]; ring)
      have h3 : w0.embedding b = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
      exact (map_eq_zero_iff _ w0.embedding.injective).mp h3
    have ha1 : ∀ w : InfinitePlace E, ‖w.embedding a‖ = 1 := by
      intro w
      have h := hiso w.embedding 1 0
      rw [hb0, hc0] at h
      simp only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h
      have h2 : (T : ℝ) * (‖w.embedding a‖ ^ 2 - 1) = 0 := by linear_combination h
      have h3 := (mul_eq_zero.mp h2).resolve_left hTr.ne'
      nlinarith [norm_nonneg (w.embedding a)]
    have hd1 : ∀ w : InfinitePlace E, ‖w.embedding d‖ = 1 := by
      intro w
      have h := hiso w.embedding 0 1
      rw [hb0, hc0] at h
      simp only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h
      have h2 : (T' : ℝ) * (‖w.embedding d‖ ^ 2 - 1) = 0 := by linear_combination -h
      have h3 := (mul_eq_zero.mp h2).resolve_left hT'r.ne'
      nlinarith [norm_nonneg (w.embedding d)]
    have ha : a = 1 := unit1 a T hT
      (by convert isInt_add zz.2.2.2.2.1 hm1 using 1; rw [hb0]; ring)
      (fun P hP h => (hloc P hP (Or.inl h)).1) ha1
    have hd : d = 1 := unit1 d T' hT'
      (by convert isInt_mul hm1 (isInt_add zz.2.2.2.2.2 h1) using 1; rw [hc0]; ring)
      (fun P hP h => (hloc P hP (Or.inr h)).2.2.2) hd1
    exact ⟨ha, hb0, hc0, hd⟩
  · right
    obtain ⟨s, hs1⟩ : ∃ s : E, s = (T' : E) * c * σ c / (T : E) := ⟨_, rfl⟩
    have hs2 : s = (T : E) * b * σ b / (T' : E) := by
      rw [hs1]
      apply w0.embedding.injective
      have hconj : ∀ z : E,
          w0.embedding z * w0.embedding (σ z) = ((‖w0.embedding z‖ ^ 2 : ℝ) : ℂ) := by
        intro z
        rw [hσ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [map_div₀, map_mul, map_natCast]
      rw [mul_assoc, mul_assoc, hconj, hconj]
      have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hTpos.ne'
      have hT'c : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'pos.ne'
      rw [div_eq_div_iff hTc hT'c]
      have h' := congrArg (fun r : ℝ => (r : ℂ)) (hwn w0)
      push_cast at h' ⊢
      linear_combination -h'
    obtain ⟨β, hβ⟩ := s_integrality E σ T T' g s b c hTpos hT'pos hs1 hs2 zz.2.1 zz.2.2.1
      (fun P hP h => (hloc P hP (Or.inl h)).2.1) (fun P hP h => (hloc P hP (Or.inr h)).2.2.1)
    have hs0 : s ≠ 0 := by
      rw [hs1]
      have hσc : σ c ≠ 0 := fun h => hc0 (σ.injective (by rw [h, map_zero]))
      have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hTpos.ne'
      have hT'0 : (T' : E) ≠ 0 := Nat.cast_ne_zero.mpr hT'pos.ne'
      exact div_ne_zero (mul_ne_zero (mul_ne_zero hT'0 hc0) hσc) hT0
    have hβ0 : β ≠ 0 := by
      rintro rfl
      have hg0 : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h0 : (g : E) ^ 2 * s = 0 := by rw [hβ]; simp
      exact hs0 ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hg0))
    set q : ℝ := (T : ℝ) * T' / (g : ℝ) ^ 2 with hq_def
    have hq : 0 < q := div_pos (mul_pos hTr hT'r) (pow_pos hgr 2)
    have key : ∀ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤ (x w ^ 2) ^ 2 := by
      intro w
      have A : (g : ℝ) ^ 2 * ‖w.embedding s‖ = (T : ℝ) * T' * ‖w.embedding (β : E)‖ := by
        have h := congrArg (fun y => ‖w.embedding y‖) hβ
        simpa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] using h
      have B : ‖w.embedding s‖ = (T' : ℝ) * ‖w.embedding c‖ ^ 2 / T := by
        rw [hs1]
        simp [hσ, norm_div] <;> ring
      have C := hxw w
      rw [hnw w c] at C
      have hs_le : ‖w.embedding s‖ ≤ x w ^ 2 := by rw [B]; exact C
      have hs_eq : ‖w.embedding s‖ = q * ‖w.embedding (β : E)‖ := by
        rw [hq_def, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hgr.ne')]
        linear_combination A
      rw [hnw w, ← mul_pow, ← hs_eq]
      first
      | exact pow_le_pow_left (norm_nonneg _) hs_le 2
      | exact pow_le_pow_left₀ (norm_nonneg _) hs_le 2
      | nlinarith [norm_nonneg (w.embedding s)]
    apply complex_multiplication_root E q x hcx hq hx
    simp only [hm]
    rw [hn, pow_mul]
    have hprod : ∏ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤
        ∏ w : InfinitePlace E, (x w ^ 2) ^ 2 :=
      Finset.prod_le_prod (fun w _ => by positivity) (fun w _ => key w)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hprod
    have hqn : 0 ≤ (q ^ 2) ^ Fintype.card (InfinitePlace E) := by positivity
    have h3 := mul_le_mul_of_nonneg_left (normge β hβ0) hqn
    rw [mul_one] at h3
    linarith

end Formalism.HermitianLatticeCounting.P
