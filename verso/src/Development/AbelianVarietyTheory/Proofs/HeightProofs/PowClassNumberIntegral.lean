import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsContinuousCircleCharExtension
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear

noncomputable section

namespace GlobalTheory.NormOneChar

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.CharFin
open scoped TensorProduct nonZeroDivisors

/- English proof (translation)
Set `_ : TopologicalSpace G` to `⊥`. Establish `: DiscreteTopology G` using `⟨rfl⟩`. Establish `h1 : x ≠ 1` using `fun h => hN (h ▸ N.one_mem)`. Apply the tactic sequence `let H : Subgroup G := { carrier := {y | y = 1 ∨ y = x} one_mem' := Or.inl rfl mul_mem' := by rintro _ _ (rfl | rfl) (rfl | rfl) <;> simp [hx] inv_mem' := by`. Introduce and unpack `_ (rfl | rfl)`.

Simplify using the standard rewrite rules. Conclude with `Or.inr (inv_eq_of_mul_eq_one_right hx) }`. Set `ψ : H →* Circle` to `{ toFun := fun y => if (y : G) = 1 then 1 else -1 map_one' := by simp map_mul' := by`. Apply the tactic sequence `rintro ⟨_, rfl | rfl⟩ ⟨_, rfl | rfl⟩ <;> simp [hx, h1] }`. Take `⟨χ, -, hχ, hψ⟩` from `GlobalTheory.exists_continuous_circle_char_extension G H N ψ (isOpen_discrete _) continuous_of_discreteTopology (by`.

Introduce and unpack `⟨_, rfl | rfl⟩ h`. Conclude with `if_pos rfl`. Conclude with `absurd h hN)`. Use `⟨Circle.toUnits.comp χ, fun y hy => by simp [hχ y hy], fun h => ?_⟩` and prove the remaining obligations. Establish `h2` using `hψ ⟨x, Or.inr rfl⟩`.

Simplify using `only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, if_neg h1] at h2`. Establish `h3` using `congrArg (fun u : ℂˣ => (u : ℂ)) h`. Simplify using `[h2] at h3`. Evaluate the numerical expressions using `at h3`.
-/
theorem exists_char {G : Type} [CommGroup G] (N : Subgroup G) (x : G) (hx : x * x = 1) (hN : x ∉ N) :
    ∃ χ : G →* ℂˣ, (∀ y ∈ N, χ y = 1) ∧ χ x ≠ 1 := by
  classical
  let _ : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  have h1 : x ≠ 1 := fun h => hN (h ▸ N.one_mem)
  let H : Subgroup G :=
    { carrier := {y | y = 1 ∨ y = x}
      one_mem' := Or.inl rfl
      mul_mem' := by rintro _ _ (rfl | rfl) (rfl | rfl) <;> simp [hx]
      inv_mem' := by
        rintro _ (rfl | rfl)
        · simp
        · exact Or.inr (inv_eq_of_mul_eq_one_right hx) }
  let ψ : H →* Circle :=
    { toFun := fun y => if (y : G) = 1 then 1 else -1
      map_one' := by simp
      map_mul' := by
        rintro ⟨_, rfl | rfl⟩ ⟨_, rfl | rfl⟩ <;> simp [hx, h1] }
  obtain ⟨χ, -, hχ, hψ⟩ := GlobalTheory.exists_continuous_circle_char_extension G H N ψ (isOpen_discrete _)
    continuous_of_discreteTopology (by
      rintro ⟨_, rfl | rfl⟩ h
      · exact if_pos rfl
      · exact absurd h hN)
  refine ⟨Circle.toUnits.comp χ, fun y hy => by simp [hχ y hy], fun h => ?_⟩
  have h2 := hψ ⟨x, Or.inr rfl⟩
  simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, if_neg h1] at h2
  have h3 := congrArg (fun u : ℂˣ => (u : ℂ)) h
  simp [h2] at h3
  norm_num at h3

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def diag : E →+* RA F E :=
  (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom

omit [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diag_apply (a : E) : diag F E a = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a := rfl

def diagInt : 𝓞 E →+* hatRing F E :=
  ((diag F E).comp (algebraMap (𝓞 E) E)).codRestrict _ fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩

/- English proof (translation)
Take `⟨x, h, hh, rfl⟩` from `GlobalTheory.AdIdem.exists_eq_one_tmul_add F E z`. Take `⟨N, hN, hx⟩` from `GlobalTheory.AdIdem.exists_nat_mul_integral E x`. Use `⟨N, hN, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add]`. Use `add_mem ?_ (mul_mem (natCast_mem _ N) hh)` and prove the remaining obligations.

Use `one_tmul_mem_adelicCompletionOfElementSet F hx` as an intermediate fact. Rewrite `this` using `[← diag_apply, map_mul, map_natCast]`. Conclude with `this`.
-/
theorem exists_denom (z : RA F E) : ∃ N : ℕ, 0 < N ∧ (N : RA F E) * z ∈ hatRing F E := by
  obtain ⟨x, h, hh, rfl⟩ := GlobalTheory.AdIdem.exists_eq_one_tmul_add F E z
  obtain ⟨N, hN, hx⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E x
  refine ⟨N, hN, ?_⟩
  rw [mul_add]
  refine add_mem ?_ (mul_mem (natCast_mem _ N) hh)
  have := one_tmul_mem_adelicCompletionOfElementSet F hx
  rw [← diag_apply, map_mul, map_natCast] at this
  exact this

omit [NumberField E] in
/- English proof (translation)
The claim follows from `(IsUnit.mk0 a ha).map _`.
-/
theorem isUnit_diag {a : E} (ha : a ≠ 0) : IsUnit (diag F E a) := (IsUnit.mk0 a ha).map _

/- English proof (translation)
Use `isUnit_diag F E (a := (N : E)) (by exact_mod_cast hN.ne')` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem isUnit_nat {N : ℕ} (hN : 0 < N) : IsUnit (N : RA F E) := by
  have := isUnit_diag F E (a := (N : E)) (by exact_mod_cast hN.ne')
  rwa [map_natCast] at this

/- English proof (translation)
Take `⟨u, hu⟩` from `hx`. Take `⟨M, hM, hMu⟩` from `exists_denom F E (u⁻¹ : (RA F E)ˣ)`. Set `I : Ideal (𝓞 E)` to `(Ideal.span {x}).comap (diagInt F E)`. Establish `hMx : (M : hatRing F E) ∈ Ideal.span {x}`. Rewrite using `[Ideal.mem_span_singleton]`.

Use `⟨⟨_, hMu⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [← hu, Subring.coe_natCast, Subring.coe_mul]`. Rewrite using `[mul_left_comm, Units.mul_inv, mul_one]`. Establish `hMI : (M : 𝓞 E) ∈ I`. Rewrite using `[Ideal.mem_comap, map_natCast]`.

Conclude with `hMx`. Establish `hI : I.map (diagInt F E) = Ideal.span {x}`. Use `le_antisymm Ideal.map_comap_le ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Take `⟨a, w, hw, e⟩` from `exists_int_add_nsmul F E M hM x x.2`.

Establish `e' : x = diagInt F E a + (M : hatRing F E) * ⟨w, hw⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[e, nsmul_eq_mul]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Establish `ha : a ∈ I`. Rewrite using `[Ideal.mem_comap, ← sub_eq_iff_eq_add.2 e']`. Conclude with `sub_mem (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hMx)`. Establish `hM'` using `Ideal.mem_map_of_mem (diagInt F E) hMI`. Rewrite `hM'` using `[map_natCast]`.

Rewrite using `[SetLike.mem_coe, e']`. Conclude with `add_mem (Ideal.mem_map_of_mem _ ha) (Ideal.mul_mem_right _ _ hM')`. Establish `hI0 : I ∈ (Ideal (𝓞 E))⁰`. Rewrite using `[mem_nonZeroDivisors_iff_ne_zero]`. Introduce `h`.

Rewrite `hMI` using `[h]`. Conclude with `(Nat.cast_ne_zero.2 hM.ne') (Ideal.mem_bot.1 hMI)`. Establish `hp : (I ^ classNumber E).IsPrincipal`. Rewrite using `[← ClassGroup.mk0_eq_one_iff (pow_mem hI0 _)]`. Establish `: (⟨I ^ classNumber E, pow_mem hI0 _⟩ : (Ideal (𝓞 E))⁰) = ⟨I, hI0⟩ ^ classNumber E` using `rfl`.

Rewrite using `[this, map_pow]`. Conclude with `pow_card_eq_one`. Take `⟨b, hb⟩` from `hp`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`.

Conclude with `mem_nonZeroDivisors_iff_ne_zero.1 (pow_mem hI0 (classNumber E)) (by rw [hb]; simp)`. Establish `h3 : Ideal.span {x ^ classNumber E} = Ideal.span {diagInt F E b}`. Rewrite using `[← Ideal.span_singleton_pow, ← hI, ← Ideal.map_pow, hb, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]`. Take `⟨s, hs⟩` from `Ideal.mem_span_singleton.1 (h3 ▸ Ideal.mem_span_singleton_self (x ^ classNumber E))`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton.1 (h3.symm ▸ Ideal.mem_span_singleton_self (diagInt F E b))`.

Use `⟨b, hb0, s, t, hs, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `hx' : IsUnit ((x ^ classNumber E : hatRing F E) : RA F E)`. Rewrite using `[SubmonoidClass.coe_pow, ← hu]`. Conclude with `u.isUnit.pow _`. Apply `hx'.mul_left_cancel` to reduce the goal to its premises.

Establish `: x ^ classNumber E * (s * t) = x ^ classNumber E * 1`. Take the linear combination `(-s) * ht - hs`. Conclude with `congrArg Subtype.val this`.
-/
theorem pow_classNumber_integral (x : hatRing F E) (hx : IsUnit (x : RA F E)) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ ∃ s t : hatRing F E, x ^ classNumber E = diagInt F E b * s ∧ s * t = 1 := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨M, hM, hMu⟩ := exists_denom F E (u⁻¹ : (RA F E)ˣ)
  let I : Ideal (𝓞 E) := (Ideal.span {x}).comap (diagInt F E)
  have hMx : (M : hatRing F E) ∈ Ideal.span {x} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨_, hMu⟩, Subtype.ext ?_⟩
    simp only [← hu, Subring.coe_natCast, Subring.coe_mul]
    rw [mul_left_comm, Units.mul_inv, mul_one]
  have hMI : (M : 𝓞 E) ∈ I := by
    rw [Ideal.mem_comap, map_natCast]; exact hMx
  have hI : I.map (diagInt F E) = Ideal.span {x} := by
    refine le_antisymm Ideal.map_comap_le ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    obtain ⟨a, w, hw, e⟩ := exists_int_add_nsmul F E M hM x x.2
    have e' : x = diagInt F E a + (M : hatRing F E) * ⟨w, hw⟩ := by
      apply Subtype.ext
      rw [e, nsmul_eq_mul]; simp; rfl
    have ha : a ∈ I := by
      rw [Ideal.mem_comap, ← sub_eq_iff_eq_add.2 e']
      exact sub_mem (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hMx)
    have hM' := Ideal.mem_map_of_mem (diagInt F E) hMI
    rw [map_natCast] at hM'
    rw [SetLike.mem_coe, e']
    exact add_mem (Ideal.mem_map_of_mem _ ha) (Ideal.mul_mem_right _ _ hM')
  have hI0 : I ∈ (Ideal (𝓞 E))⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    rw [h] at hMI
    exact (Nat.cast_ne_zero.2 hM.ne') (Ideal.mem_bot.1 hMI)
  have hp : (I ^ classNumber E).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hI0 _)]
    have : (⟨I ^ classNumber E, pow_mem hI0 _⟩ : (Ideal (𝓞 E))⁰) = ⟨I, hI0⟩ ^ classNumber E := rfl
    rw [this, map_pow]
    exact pow_card_eq_one
  obtain ⟨b, hb⟩ := hp
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact mem_nonZeroDivisors_iff_ne_zero.1 (pow_mem hI0 (classNumber E)) (by rw [hb]; simp)
  have h3 : Ideal.span {x ^ classNumber E} = Ideal.span {diagInt F E b} := by
    rw [← Ideal.span_singleton_pow, ← hI, ← Ideal.map_pow, hb, Ideal.submodule_span_eq, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 (h3 ▸ Ideal.mem_span_singleton_self (x ^ classNumber E))
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 (h3.symm ▸ Ideal.mem_span_singleton_self (diagInt F E b))
  refine ⟨b, hb0, s, t, hs, Subtype.ext ?_⟩
  have hx' : IsUnit ((x ^ classNumber E : hatRing F E) : RA F E) := by
    rw [SubmonoidClass.coe_pow, ← hu]; exact u.isUnit.pow _
  apply hx'.mul_left_cancel
  have : x ^ classNumber E * (s * t) = x ^ classNumber E * 1 := by
    linear_combination (-s) * ht - hs
  exact congrArg Subtype.val this

/- English proof (translation)
Take `⟨N, hN, hx⟩` from `exists_denom F E x`. Take `⟨b, hb, s, t, e, hst⟩` from `pow_classNumber_integral F E ⟨_, hx⟩ ((isUnit_nat F E hN).mul x.isUnit)`. Establish `hN' : (N : E) ^ classNumber E ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hN.ne')`. Use `⟨(b : E) / (N : E) ^ classNumber E, div_ne_zero (by simpa using hb) hN', s, t, ?_, hst⟩` and prove the remaining obligations. Apply `(isUnit_diag F E hN').mul_left_cancel` to reduce the goal to its premises.

Rewrite using `[← mul_assoc, ← map_mul, mul_div_cancel₀ _ hN', map_pow, map_natCast, ← mul_pow]`. Conclude with `congrArg Subtype.val e`.
-/
theorem pow_classNumber (x : (RA F E)ˣ) : ∃ b : E, b ≠ 0 ∧ ∃ s t : hatRing F E,
    (x : RA F E) ^ classNumber E = diag F E b * s ∧ s * t = 1 := by
  obtain ⟨N, hN, hx⟩ := exists_denom F E x
  obtain ⟨b, hb, s, t, e, hst⟩ := pow_classNumber_integral F E ⟨_, hx⟩ ((isUnit_nat F E hN).mul x.isUnit)
  have hN' : (N : E) ^ classNumber E ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN.ne')
  refine ⟨(b : E) / (N : E) ^ classNumber E, div_ne_zero (by simpa using hb) hN', s, t, ?_, hst⟩
  apply (isUnit_diag F E hN').mul_left_cancel
  rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hN', map_pow, map_natCast, ← mul_pow]
  exact congrArg Subtype.val e

/- English proof (translation)
Establish `hN' : (N : E) ≠ 0` using `by exact_mod_cast (by omega : N ≠ 0)`. Establish `h1 : diag F E (y / N) = w`. Apply `(isUnit_nat F E (N := N) (by omega)).mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← e, ← map_natCast (diag F E), ← map_mul, mul_div_cancel₀ _ hN']`. Take `⟨r, hr⟩` from `GlobalTheory.AdIdem.mem_range_of_one_tmul_mem F E (x := y / N) (by rw [← diag_apply, h1]; exact hw)`.

Establish `hlt : ∀ z : InfinitePlace E, z r < 1` using `fun z => by`. Establish `h2 : (2 : ℝ) < N` using `by exact_mod_cast hN`. Establish `h3 : (r : E) = y / N` using `hr`. Rewrite using `[← z.norm_embedding_eq, h3, map_div₀, map_natCast, norm_div, Complex.norm_natCast, div_lt_one (by linarith)]`. Conclude with `(hy _).trans_lt h2`.

Assume the negation of the conclusion as `h0`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Conclude with `div_ne_zero h0 hN' (by rw [← hr, map_zero])`. Take `⟨z⟩ : Nonempty (InfinitePlace E)` from `inferInstance`.

Conclude with `absurd (InfinitePlace.one_le_of_lt_one hr0 fun z _ => hlt z) (not_le.2 (hlt z))`.
-/
theorem eq_zero_of_small {N : ℕ} (hN : 2 < N) (y : E) (w : RA F E) (hw : w ∈ hatRing F E)
    (e : diag F E y = N * w) (hy : ∀ φ : E →+* ℂ, ‖φ y‖ ≤ 2) : y = 0 := by
  have hN' : (N : E) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h1 : diag F E (y / N) = w := by
    apply (isUnit_nat F E (N := N) (by omega)).mul_left_cancel
    rw [← e, ← map_natCast (diag F E), ← map_mul, mul_div_cancel₀ _ hN']
  obtain ⟨r, hr⟩ := GlobalTheory.AdIdem.mem_range_of_one_tmul_mem F E (x := y / N) (by rw [← diag_apply, h1]; exact hw)
  have hlt : ∀ z : InfinitePlace E, z r < 1 := fun z => by
    have h2 : (2 : ℝ) < N := by exact_mod_cast hN
    have h3 : (r : E) = y / N := hr
    rw [← z.norm_embedding_eq, h3, map_div₀, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    exact (hy _).trans_lt h2
  by_contra h0
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact div_ne_zero h0 hN' (by rw [← hr, map_zero])
  obtain ⟨z⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one hr0 fun z _ => hlt z) (not_le.2 (hlt z))

omit [NumberField E] in

/- English proof (translation)
Take `⟨e, f, h1, h2, h3⟩` from `RootNear.exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) p`. Take `⟨a, b, hab⟩` from `Nat.Coprime.cast (R := ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) h`. Take `⟨u, hu⟩` from `(h3 (-b)).exists_right_inv`. Establish `h4 : e = g * (e * a * u)`. Take the linear combination `(-e) * hu - e * u * hab - p * b * u * h1`.

Set `κ` to `(RootNear.intHat F E).subtype.comp (RootNear.inclHat F E)`. Establish `hκ : ∀ z, κ z ∈ hatRing F E` using `fun z => (RootNear.inclHat F E z).2`. Use `⟨RootNear.incl F e, κ f, hκ _, κ (e * a * u), hκ _, by rw [← map_mul, h1], ?_, ?_⟩` and prove the remaining obligations. Use `congrArg κ h2` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, map_mul, map_natCast]`. Then use the resulting hypothesis.

Use `congrArg κ h4` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast]`. Then use the resulting hypothesis.
-/
theorem exists_idem_at (g p : ℕ) (h : Nat.Coprime g p) : ∃ a : FiniteAdeleRing (𝓞 F) F,
    ∃ f ∈ hatRing F E, ∃ f' ∈ hatRing F E, a * a = a ∧
      1 - a ⊗ₜ[F] (1 : E) = (p : RA F E) * f ∧ a ⊗ₜ[F] (1 : E) = (g : RA F E) * f' := by
  obtain ⟨e, f, h1, h2, h3⟩ := RootNear.exists_idem
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) p
  obtain ⟨a, b, hab⟩ := Nat.Coprime.cast
    (R := ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) h
  obtain ⟨u, hu⟩ := (h3 (-b)).exists_right_inv
  have h4 : e = g * (e * a * u) := by
    linear_combination (-e) * hu - e * u * hab - p * b * u * h1
  let κ := (RootNear.intHat F E).subtype.comp (RootNear.inclHat F E)
  have hκ : ∀ z, κ z ∈ hatRing F E := fun z => (RootNear.inclHat F E z).2
  refine ⟨RootNear.incl F e, κ f, hκ _, κ (e * a * u), hκ _, by rw [← map_mul, h1], ?_, ?_⟩
  · have := congrArg κ h2
    rwa [map_sub, map_one, map_mul, map_natCast] at this
  · have := congrArg κ h4
    rwa [map_mul, map_natCast] at this

variable {F E} (c : E ≃ₐ[F] E)

abbrev bar : RA F E →ₐ[F] RA F E := sg (FiniteAdeleRing (𝓞 F) F) c

omit [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bar_tmul (a : FiniteAdeleRing (𝓞 F) F) (y : E) : bar c (a ⊗ₜ[F] y) = a ⊗ₜ[F] c y := rfl

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y => rw [bar_tmul, bar_tmul, hc]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem bar_bar (hc : ∀ y, c (c y) = y) (z : RA F E) : bar c (bar c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [bar_tmul, bar_tmul, hc]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [NumberField E] in
/- English proof (translation)
Use `galoisAut_mem_adelicCompletionOfElementSet F c ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨⟨_, (RingOfIntegers.isIntegral_coe x).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩`.
-/
theorem bar_mem {z : RA F E} (hz : z ∈ hatRing F E) : bar c z ∈ hatRing F E := by
  refine galoisAut_mem_adelicCompletionOfElementSet F c ?_ hz
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨_, (RingOfIntegers.isIntegral_coe x).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩

def ratOne : Subgroup (RA F E)ˣ where
  carrier := {x | (∃ a : E, (x : RA F E) = diag F E a) ∧ (x : RA F E) * bar c x = 1}
  one_mem' := ⟨⟨1, by simp⟩, by simp⟩
  mul_mem' := by
    rintro x y ⟨⟨a, ha⟩, hx⟩ ⟨⟨b, hb⟩, hy⟩
    refine ⟨⟨a * b, by rw [Units.val_mul, ha, hb, map_mul]⟩, ?_⟩
    rw [Units.val_mul, map_mul, mul_mul_mul_comm, hx, hy, mul_one]
  inv_mem' := by
    rintro x ⟨⟨a, ha⟩, hx⟩
    have h : ((x⁻¹ : (RA F E)ˣ) : RA F E) = bar c x := Units.inv_eq_of_mul_eq_one_right hx
    refine ⟨⟨c a, by rw [h, ha]; rfl⟩, ?_⟩
    nth_rewrite 1 [h]
    rw [← map_mul, Units.mul_inv, map_one]

def congOne (N : ℕ) : Subgroup (RA F E)ˣ where
  carrier := {x | (∃ w ∈ hatRing F E, (x : RA F E) - 1 = N * w) ∧ (x : RA F E) * bar c x = 1}
  one_mem' := ⟨⟨0, zero_mem _, by simp⟩, by simp⟩
  mul_mem' := by
    rintro x y ⟨⟨a, ha, ea⟩, hx⟩ ⟨⟨b, hb, eb⟩, hy⟩
    refine ⟨⟨a + b + N * (a * b), add_mem (add_mem ha hb) (mul_mem (natCast_mem _ N) (mul_mem ha hb)), ?_⟩, ?_⟩
    · rw [Units.val_mul]
      linear_combination (y : RA F E) * ea + (1 + N * a) * eb
    · rw [Units.val_mul, map_mul, mul_mul_mul_comm, hx, hy, mul_one]
  inv_mem' := by
    rintro x ⟨⟨a, ha, ea⟩, hx⟩
    have h : ((x⁻¹ : (RA F E)ˣ) : RA F E) = bar c x := Units.inv_eq_of_mul_eq_one_right hx
    refine ⟨⟨bar c a, bar_mem c ha, ?_⟩, ?_⟩
    · have := congrArg (bar c) ea
      rwa [map_sub, map_one, map_mul, map_natCast, ← h] at this
    · nth_rewrite 1 [h]
      rw [← map_mul, Units.mul_inv, map_one]

/- English proof (translation)
Use `finite_quotient_hatRing F E N hN` as an intermediate fact. Set `k` to `Nat.card (hatRing F E ⧸ Ideal.span {(N : hatRing F E)})ˣ`. Use `⟨classNumber E * 2 * k, Nat.mul_pos (Nat.mul_pos (classNumber_pos E) two_pos) Nat.card_pos, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨b, hb, s, t, e, hst⟩` from `pow_classNumber F E x`. Establish `hst' : (s : RA F E) * t = 1` using `congrArg Subtype.val hst`.

Establish `hbst : bar c s * bar c t = 1` using `by rw [← map_mul, hst', map_one]`. Establish `hcb : c b ≠ 0` using `by simpa using hb`. Establish `hq : b / c b ≠ 0` using `div_ne_zero hb hcb`. Set `r : (RA F E)ˣ` to `(isUnit_diag F E hq).unit`. Establish `hr : r ∈ ratOne c`.

Use `⟨⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `diag F E (b / c b) * diag F E (c (b / c b)) = 1`. Rewrite using `[← map_mul, map_div₀, hc, div_mul_div_comm, mul_comm b, div_self (mul_ne_zero hcb hb), map_one]`. Set `v : (hatRing F E)ˣ` to `Units.mkOfMulEqOne (s * ⟨_, bar_mem c t.2⟩) (t * ⟨_, bar_mem c s.2⟩) (Subtype.ext (by`. Express the relevant statement in the definitionally equal form `(s : RA F E) * bar c t * (t * bar c s) = 1`.

Take the linear combination `(bar c s * bar c t) * hst' + hbst))`. Set `u : (RA F E)ˣ` to `Units.map (hatRing F E).subtype.toMonoidHom v`. Establish `hu : (u : RA F E) = s * bar c t` using `rfl`. Establish `hun : (u : RA F E) * bar c u = 1`. Rewrite using `[hu, map_mul, bar_bar c hc]`.

Take the linear combination `(bar c s * bar c t) * hst' + hbst`. Establish `hx2 : x ^ (classNumber E * 2) = r * u`. Apply `Units.ext` to reduce the goal to its premises. Establish `h1 : (x : RA F E) ^ classNumber E * bar c ((x : RA F E) ^ classNumber E) = 1`. Rewrite using `[map_pow, ← mul_pow, hx, one_pow]`.

Establish `h2 : diag F E (b / c b) * diag F E (c b) = diag F E b`. Rewrite using `[← map_mul, div_mul_cancel₀ _ hcb]`. Establish `h3 : bar c (diag F E b) = diag F E (c b)` using `rfl`. Rewrite `h1` using `[e, map_mul, h3]`. Rewrite using `[Units.val_pow_eq_pow_val, pow_mul, e, Units.val_mul, hu]`.

Express the relevant statement in the definitionally equal form `_ = diag F E (b / c b) * _`. Take the linear combination `(diag F E (b / c b) * s * bar c t) * h1 - (diag F E b * s * s) * h2 - (diag F E (b / c b) * diag F E (c b) * diag F E b * s * s) * hbst`. Establish `huk : u ^ k ∈ congOne c N`. Use `⟨?_, by rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]⟩` and prove the remaining obligations. Establish `h1 : (Units.map (Ideal.Quotient.mk (Ideal.span {(N : hatRing F E)})).toMonoidHom v) ^ k = 1` using `pow_card_eq_one'`.

Establish `h2 : Ideal.Quotient.mk (Ideal.span {(N : hatRing F E)}) ((v : hatRing F E) ^ k) = Ideal.Quotient.mk _ 1`. Rewrite using `[map_pow, map_one]`. Conclude with `(Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val h1)`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h2)`. Use `⟨w, w.2, ?_⟩` and prove the remaining obligations.

Use `congrArg (hatRing F E).subtype hw` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, map_mul, map_natCast, map_pow]`. Then use the resulting hypothesis. Rewrite using `[pow_mul, hx2, mul_pow]`. Conclude with `Subgroup.mul_mem_sup (pow_mem hr k) huk`.
-/
theorem exists_exponent (hc : ∀ y, c (c y) = y) (N : ℕ) (hN : 0 < N) : ∃ m : ℕ, 0 < m ∧
    ∀ x : (RA F E)ˣ, (x : RA F E) * bar c x = 1 → x ^ m ∈ ratOne c ⊔ congOne c N := by
  have := finite_quotient_hatRing F E N hN
  let k := Nat.card (hatRing F E ⧸ Ideal.span {(N : hatRing F E)})ˣ
  refine ⟨classNumber E * 2 * k, Nat.mul_pos (Nat.mul_pos (classNumber_pos E) two_pos) Nat.card_pos,
    fun x hx => ?_⟩
  obtain ⟨b, hb, s, t, e, hst⟩ := pow_classNumber F E x
  have hst' : (s : RA F E) * t = 1 := congrArg Subtype.val hst
  have hbst : bar c s * bar c t = 1 := by rw [← map_mul, hst', map_one]
  have hcb : c b ≠ 0 := by simpa using hb
  have hq : b / c b ≠ 0 := div_ne_zero hb hcb
  let r : (RA F E)ˣ := (isUnit_diag F E hq).unit
  have hr : r ∈ ratOne c := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    change diag F E (b / c b) * diag F E (c (b / c b)) = 1
    rw [← map_mul, map_div₀, hc, div_mul_div_comm, mul_comm b, div_self (mul_ne_zero hcb hb), map_one]
  let v : (hatRing F E)ˣ := Units.mkOfMulEqOne (s * ⟨_, bar_mem c t.2⟩) (t * ⟨_, bar_mem c s.2⟩)
    (Subtype.ext (by
      change (s : RA F E) * bar c t * (t * bar c s) = 1
      linear_combination (bar c s * bar c t) * hst' + hbst))
  let u : (RA F E)ˣ := Units.map (hatRing F E).subtype.toMonoidHom v
  have hu : (u : RA F E) = s * bar c t := rfl
  have hun : (u : RA F E) * bar c u = 1 := by
    rw [hu, map_mul, bar_bar c hc]
    linear_combination (bar c s * bar c t) * hst' + hbst
  have hx2 : x ^ (classNumber E * 2) = r * u := by
    apply Units.ext
    have h1 : (x : RA F E) ^ classNumber E * bar c ((x : RA F E) ^ classNumber E) = 1 := by
      rw [map_pow, ← mul_pow, hx, one_pow]
    have h2 : diag F E (b / c b) * diag F E (c b) = diag F E b := by
      rw [← map_mul, div_mul_cancel₀ _ hcb]
    have h3 : bar c (diag F E b) = diag F E (c b) := rfl
    rw [e, map_mul, h3] at h1
    rw [Units.val_pow_eq_pow_val, pow_mul, e, Units.val_mul, hu]
    change _ = diag F E (b / c b) * _
    linear_combination (diag F E (b / c b) * s * bar c t) * h1 - (diag F E b * s * s) * h2
      - (diag F E (b / c b) * diag F E (c b) * diag F E b * s * s) * hbst
  have huk : u ^ k ∈ congOne c N := by
    refine ⟨?_, by rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]⟩
    have h1 : (Units.map (Ideal.Quotient.mk (Ideal.span {(N : hatRing F E)})).toMonoidHom v) ^ k = 1 :=
      pow_card_eq_one'
    have h2 : Ideal.Quotient.mk (Ideal.span {(N : hatRing F E)}) ((v : hatRing F E) ^ k) =
        Ideal.Quotient.mk _ 1 := by
      rw [map_pow, map_one]
      exact (Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val h1)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h2)
    refine ⟨w, w.2, ?_⟩
    have := congrArg (hatRing F E).subtype hw
    rwa [map_sub, map_one, map_mul, map_natCast, map_pow] at this
  rw [pow_mul, hx2, mul_pow]
  exact Subgroup.mul_mem_sup (pow_mem hr k) huk

/- English proof (translation)
Take `⟨a, f, hf, f', hf', h1, h2, h3⟩` from `exists_idem_at F E g p h`. Use `set e : RA F E := a ⊗ₜ[F] (1 : E) with he`. Establish `hee : e * e = e` using `by rw [he, Algebra.TensorProduct.tmul_mul_tmul, h1, mul_one]`. Establish `hbe : bar c e = e` using `by rw [he, bar_tmul, map_one]`. Establish `hsq : (1 - 2 * e) * (1 - 2 * e) = 1` using `by linear_combination 4 * hee`.

Establish `two : (2 : RA F E) ∈ hatRing F E` using `by exact_mod_cast natCast_mem (hatRing F E) 2`. Set `x : (RA F E)ˣ` to `Units.mkOfMulEqOne _ _ hsq`. Establish `hx : (x : RA F E) = 1 - 2 * e` using `rfl`. Establish `hxg : x ∈ congOne c g`. Use `⟨⟨-(2 * f'), neg_mem (mul_mem two hf'), ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hx]`. Take the linear combination `(-2) * h3`. Rewrite using `[hx, map_sub, map_one, map_mul, map_ofNat, hbe, hsq]`. Use `⟨x, Units.ext hsq, hxg, fun hm => ?_⟩` and prove the remaining obligations. Take `⟨r, ⟨⟨y, hy⟩, hr⟩, k, hk, hrk⟩` from `Subgroup.mem_sup.1 hm`.

Establish `hkg : k ∈ congOne c g`. Take `⟨⟨w, hw, ew⟩, hn⟩` from `hk`. Conclude with `⟨⟨p * w, mul_mem (natCast_mem _ p) hw, by rw [ew, Nat.cast_mul, mul_assoc]⟩, hn⟩`. Establish `hrg : r ∈ congOne c g`. Rewrite using `[eq_mul_inv_of_mul_eq hrk]`.

Conclude with `mul_mem hxg (inv_mem hkg)`. Establish `: Nontrivial (RA F E)` using `nontrivial_of_ne 1 0 fun h0 => one_ne_zero (eq_zero_of_small F E hg 1 0 (zero_mem _) (by rw [map_one, mul_zero, h0]) fun φ => by simp)`. Establish `hinj : Function.Injective (diag F E)` using `(diag F E).injective`. Establish `hyn : y * c y = 1` using `hinj (by rw [map_mul, map_one, ← hr, hy]; rfl)`. Take `⟨⟨w, hw, ew⟩, -⟩` from `hrg`.

Establish `hy1 : y - 1 = 0` using `eq_zero_of_small F E hg _ w hw (by rw [map_sub, map_one, ← hy, ew]) fun φ => by`. Establish `h4` using `congrArg (fun z => ‖φ z‖) hyn`. Simplify using `only [map_mul, hc, norm_mul, Complex.norm_conj, map_one, norm_one] at h4`. Establish `h5 : ‖φ y‖ = 1` using `by nlinarith [norm_nonneg (φ y)]`. Rewrite using `[map_sub, map_one]`.

Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[h5, norm_one]`. Evaluate the numerical expressions. Establish `hr1 : r = 1` using `Units.ext (by rw [hy, sub_eq_zero.1 hy1, map_one]; rfl)`. Rewrite `hrk` using `[hr1, one_mul]`.

Take `⟨⟨w', hw', ew'⟩, -⟩` from `hk`. Rewrite `ew'` using `[hrk, hx, Nat.cast_mul]`. Establish `h6 : (2 : E) = 0` using `eq_zero_of_small F E hp _ (2 * f - g * w') (sub_mem (mul_mem two hf) (mul_mem (natCast_mem _ g) hw')) (by rw [map_ofNat]; linear_combination 2 * h2 - ew') fun φ => by simp [map_ofNat]`. Conclude with `two_ne_zero h6`.
-/
theorem exists_involution (hc : ∀ (φ : E →+* ℂ) (y : E), φ (c y) = starRingEnd ℂ (φ y)) (g p : ℕ)
    (hg : 2 < g) (hp : 2 < p) (h : Nat.Coprime g p) :
    ∃ x : (RA F E)ˣ, x * x = 1 ∧ x ∈ congOne c g ∧ x ∉ ratOne c ⊔ congOne c (g * p) := by
  obtain ⟨a, f, hf, f', hf', h1, h2, h3⟩ := exists_idem_at F E g p h
  set e : RA F E := a ⊗ₜ[F] (1 : E) with he
  have hee : e * e = e := by rw [he, Algebra.TensorProduct.tmul_mul_tmul, h1, mul_one]
  have hbe : bar c e = e := by rw [he, bar_tmul, map_one]
  have hsq : (1 - 2 * e) * (1 - 2 * e) = 1 := by linear_combination 4 * hee
  have two : (2 : RA F E) ∈ hatRing F E := by exact_mod_cast natCast_mem (hatRing F E) 2
  let x : (RA F E)ˣ := Units.mkOfMulEqOne _ _ hsq
  have hx : (x : RA F E) = 1 - 2 * e := rfl
  have hxg : x ∈ congOne c g := by
    refine ⟨⟨-(2 * f'), neg_mem (mul_mem two hf'), ?_⟩, ?_⟩
    · rw [hx]; linear_combination (-2) * h3
    · rw [hx, map_sub, map_one, map_mul, map_ofNat, hbe, hsq]
  refine ⟨x, Units.ext hsq, hxg, fun hm => ?_⟩
  obtain ⟨r, ⟨⟨y, hy⟩, hr⟩, k, hk, hrk⟩ := Subgroup.mem_sup.1 hm
  have hkg : k ∈ congOne c g := by
    obtain ⟨⟨w, hw, ew⟩, hn⟩ := hk
    exact ⟨⟨p * w, mul_mem (natCast_mem _ p) hw, by rw [ew, Nat.cast_mul, mul_assoc]⟩, hn⟩
  have hrg : r ∈ congOne c g := by
    rw [eq_mul_inv_of_mul_eq hrk]; exact mul_mem hxg (inv_mem hkg)
  have : Nontrivial (RA F E) := nontrivial_of_ne 1 0 fun h0 => one_ne_zero
    (eq_zero_of_small F E hg 1 0 (zero_mem _) (by rw [map_one, mul_zero, h0]) fun φ => by simp)
  have hinj : Function.Injective (diag F E) := (diag F E).injective
  have hyn : y * c y = 1 := hinj (by rw [map_mul, map_one, ← hr, hy]; rfl)
  obtain ⟨⟨w, hw, ew⟩, -⟩ := hrg
  have hy1 : y - 1 = 0 := eq_zero_of_small F E hg _ w hw (by rw [map_sub, map_one, ← hy, ew]) fun φ => by
    have h4 := congrArg (fun z => ‖φ z‖) hyn
    simp only [map_mul, hc, norm_mul, Complex.norm_conj, map_one, norm_one] at h4
    have h5 : ‖φ y‖ = 1 := by nlinarith [norm_nonneg (φ y)]
    rw [map_sub, map_one]
    refine (norm_sub_le _ _).trans ?_
    rw [h5, norm_one]; norm_num
  have hr1 : r = 1 := Units.ext (by rw [hy, sub_eq_zero.1 hy1, map_one]; rfl)
  rw [hr1, one_mul] at hrk
  obtain ⟨⟨w', hw', ew'⟩, -⟩ := hk
  rw [hrk, hx, Nat.cast_mul] at ew'
  have h6 : (2 : E) = 0 := eq_zero_of_small F E hp _ (2 * f - g * w')
    (sub_mem (mul_mem two hf) (mul_mem (natCast_mem _ g) hw'))
    (by rw [map_ofNat]; linear_combination 2 * h2 - ew') fun φ => by simp [map_ofNat]
  exact two_ne_zero h6

/- English proof (translation)
Establish `: NeZero m` using `⟨hm.ne'⟩`. Take `⟨i, -, rfl⟩` from `(Complex.isPrimitiveRoot_exp m hm.ne').eq_pow_of_pow_eq_one hz`. Conclude with `pow_mem h i`.
-/
theorem mem_of_pow_eq_one {K : IntermediateField ℚ ℂ} {m : ℕ} (hm : 0 < m)
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta m ∈ K) {z : ℂ} (hz : z ^ m = 1) : z ∈ K := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨i, -, rfl⟩ := (Complex.isPrimitiveRoot_exp m hm.ne').eq_pow_of_pow_eq_one hz
  exact pow_mem h i

end GlobalTheory.NormOneChar

namespace GlobalTheory.NormOneChar

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.FinalJoin
open scoped TensorProduct

/- English proof (translation)
Introduce `D p hp`. Establish `hpp : p.Prime ∧ p % 15 = 1 ∧ ∀ i, p ≠ D.host.g i`. Break down `hp with rfl | rfl` into its components or cases. Conclude with `⟨D.host.pde_prime, D.host.pde_mod.1, fun i => (D.host.pde_ne_g i).1⟩`. Conclude with `⟨D.host.pde'_prime, D.host.pde_mod.2, fun i => (D.host.pde_ne_g i).2⟩`.

Establish `h2` using `hpp.1.two_le`. Establish `hp2 : 2 < p` using `by omega`. Establish `hg : 2 < D.host.g 0 * D.host.g 1`. Use polynomial arithmetic with `[(D.host.g_prime 0).two_le, (D.host.g_prime 1).two_le]`. Establish `hcop : Nat.Coprime (D.host.g 0 * D.host.g 1) p` using `Nat.Coprime.mul_left ((Nat.coprime_primes (D.host.g_prime 0) hpp.1).2 (hpp.2.2 0).symm) ((Nat.coprime_primes (D.host.g_prime 1) hpp.1).2 (hpp.2.2 1).symm)`.

Establish `hc : ∀ (φ : D.host.E →+* ℂ) (y : D.host.E), φ (GlobalTheory.Member.cF D y) = starRingEnd ℂ (φ y)` using `fun φ y => @IsCMField.complexEmbedding_complexConj D.host.E _ _ (D.host.isCMField_hostE) _ φ y`. Establish `hcc : ∀ y, GlobalTheory.Member.cF D (GlobalTheory.Member.cF D y) = y` using `fun y => D.host.φ₀.injective (by rw [hc, hc, Complex.conj_conj])`. Take `⟨m, hm, hexp⟩` from `exists_exponent (GlobalTheory.Member.cF D) hcc (D.host.g 0 * D.host.g 1 * p) (by positivity)`. Take `⟨x₀, hsq, hx₀, hN⟩` from `exists_involution (GlobalTheory.Member.cF D) hc _ p hg hp2 hcop`. Take `⟨χ, hχ, hχ₀⟩` from `exists_char _ x₀ hsq hN`.

Establish `hcong : ∀ (N : ℕ) (x : (AfE D)ˣ), x ∈ congOne (GlobalTheory.Member.cF D) N ↔ CongOne N x ∧ NormOne x`. Introduce `N x`. Unfold `CongOne`. Simplify using `only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]`. Conclude with `Iff.rfl`.

Establish `a1 : ∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → NormOne x → χ x = 1` using `fun x a h hn => hχ x (Subgroup.mem_sup_left ⟨⟨a, h⟩, hn⟩)`. Establish `a2 : ∀ x, NormOne x → CongOne (D.host.g 0 * D.host.g 1 * p) x → χ x = 1` using `fun x hn h => hχ x (Subgroup.mem_sup_right ((hcong _ x).2 ⟨h, hn⟩))`. Establish `a3 : ∃ x, NormOne x ∧ CongOne (D.host.g 0 * D.host.g 1) x ∧ χ x ≠ 1` using `⟨x₀, ((hcong _ _).1 hx₀).2, ((hcong _ _).1 hx₀).1, hχ₀⟩`. Establish `a4 : ∀ x, NormOne x → χ x ^ m = 1` using `fun x hn => by`. Rewrite using `[← map_pow]`.

Conclude with `hχ _ (hexp x hn)`. Use `⟨χ, m, hm, a1, a2, a3, a4, fun hz => ⟨a1, a2, a3, ⟨m, hm, a4⟩, fun x hn => ?_⟩⟩` and prove the remaining obligations. Conclude with `mem_of_pow_eq_one hm hz (by rw [← Units.val_pow_eq_pow_val, a4 x hn, Units.val_one])`.
-/
theorem exists_xi : ∀ (D : D7) (p : ℕ), (p = D.host.pde ∨ p = D.host.pde') → ∃ (xi : (AfE D)ˣ →* ℂˣ) (m : ℕ), 0 < m ∧ (∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → NormOne x → xi x = 1) ∧ (∀ x, NormOne x → CongOne (D.host.g 0 * D.host.g 1 * p) x → xi x = 1) ∧ (∃ x, NormOne x ∧ CongOne (D.host.g 0 * D.host.g 1) x ∧ xi x ≠ 1) ∧ (∀ x, NormOne x → xi x ^ m = 1) ∧ (zeta m ∈ FO D → XiOK D p xi) := by
  intro D p hp
  have hpp : p.Prime ∧ p % 15 = 1 ∧ ∀ i, p ≠ D.host.g i := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1, fun i => (D.host.pde_ne_g i).1⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2, fun i => (D.host.pde_ne_g i).2⟩
  have h2 := hpp.1.two_le
  have hp2 : 2 < p := by omega
  have hg : 2 < D.host.g 0 * D.host.g 1 := by
    nlinarith [(D.host.g_prime 0).two_le, (D.host.g_prime 1).two_le]
  have hcop : Nat.Coprime (D.host.g 0 * D.host.g 1) p :=
    Nat.Coprime.mul_left ((Nat.coprime_primes (D.host.g_prime 0) hpp.1).2 (hpp.2.2 0).symm)
      ((Nat.coprime_primes (D.host.g_prime 1) hpp.1).2 (hpp.2.2 1).symm)
  have hc : ∀ (φ : D.host.E →+* ℂ) (y : D.host.E), φ (GlobalTheory.Member.cF D y) = starRingEnd ℂ (φ y) :=
    fun φ y => @IsCMField.complexEmbedding_complexConj D.host.E _ _
      (D.host.isCMField_hostE) _ φ y
  have hcc : ∀ y, GlobalTheory.Member.cF D (GlobalTheory.Member.cF D y) = y := fun y =>
    D.host.φ₀.injective (by rw [hc, hc, Complex.conj_conj])
  obtain ⟨m, hm, hexp⟩ := exists_exponent (GlobalTheory.Member.cF D) hcc (D.host.g 0 * D.host.g 1 * p) (by positivity)
  obtain ⟨x₀, hsq, hx₀, hN⟩ := exists_involution (GlobalTheory.Member.cF D) hc _ p hg hp2 hcop
  obtain ⟨χ, hχ, hχ₀⟩ := exists_char _ x₀ hsq hN
  have hcong : ∀ (N : ℕ) (x : (AfE D)ˣ), x ∈ congOne (GlobalTheory.Member.cF D) N ↔ CongOne N x ∧ NormOne x := by
    intro N x
    unfold CongOne
    simp only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]
    exact Iff.rfl
  have a1 : ∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → NormOne x → χ x = 1 :=
    fun x a h hn => hχ x (Subgroup.mem_sup_left ⟨⟨a, h⟩, hn⟩)
  have a2 : ∀ x, NormOne x → CongOne (D.host.g 0 * D.host.g 1 * p) x → χ x = 1 :=
    fun x hn h => hχ x (Subgroup.mem_sup_right ((hcong _ x).2 ⟨h, hn⟩))
  have a3 : ∃ x, NormOne x ∧ CongOne (D.host.g 0 * D.host.g 1) x ∧ χ x ≠ 1 :=
    ⟨x₀, ((hcong _ _).1 hx₀).2, ((hcong _ _).1 hx₀).1, hχ₀⟩
  have a4 : ∀ x, NormOne x → χ x ^ m = 1 := fun x hn => by
    rw [← map_pow]; exact hχ _ (hexp x hn)
  refine ⟨χ, m, hm, a1, a2, a3, a4, fun hz => ⟨a1, a2, a3, ⟨m, hm, a4⟩, fun x hn => ?_⟩⟩
  exact mem_of_pow_eq_one hm hz (by rw [← Units.val_pow_eq_pow_val, a4 x hn, Units.val_one])

end GlobalTheory.NormOneChar
