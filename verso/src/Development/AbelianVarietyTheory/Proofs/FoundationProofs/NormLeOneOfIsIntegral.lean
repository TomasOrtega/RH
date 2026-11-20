import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CoefCoord

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Express the relevant statement in the definitionally equal form `spectralValue (minpoly ℚ_[l] x) ≤ 1`. Rewrite using `[spectralValue_le_one_iff (minpoly.monic hi)]`. Introduce `n`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]`.

Conclude with `PadicInt.norm_le_one _`.
-/
theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  change spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

/- English proof (translation)
The claim follows from `norm_le_one_of_isIntegral _ ((isIntegral_algHom_iff c.O.val Subtype.val_injective).2 (Algebra.IsIntegral.isIntegral x))`.
-/
theorem norm_le_one (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral _
    ((isIntegral_algHom_iff c.O.val Subtype.val_injective).2 (Algebra.IsIntegral.isIntegral x))

/- English proof (translation)
Establish `h1` using `norm_le_one c u`. Establish `h2` using `norm_le_one c (↑u⁻¹ : c.O)`. Establish `h3 : ((u : c.O) : PadicAlgCl l) * ((↑u⁻¹ : c.O) : PadicAlgCl l) = 1`. Rewrite using `[← Subalgebra.coe_mul, Units.mul_inv]`. Both sides reduce to the same expression.

Establish `h4` using `congrArg norm h3`. Rewrite `h4` using `[norm_mul, norm_one]`. Establish `h5 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ ≤ ‖((u : c.O) : PadicAlgCl l)‖` using `mul_le_of_le_one_right (norm_nonneg _) h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 := norm_le_one c u
  have h2 := norm_le_one c (↑u⁻¹ : c.O)
  have h3 : ((u : c.O) : PadicAlgCl l) * ((↑u⁻¹ : c.O) : PadicAlgCl l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  have h5 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ ≤ ‖((u : c.O) : PadicAlgCl l)‖ :=
    mul_le_of_le_one_right (norm_nonneg _) h2
  linarith

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends, Padic.norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`.
-/
theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

/- English proof (translation)
Use `show ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])‖ = ‖a‖`. Rewrite using `[PadicAlgCl.norm_extends]`. Both sides reduce to the same expression.
-/
theorem norm_algebraMap_padicInt (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  show ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])‖ = ‖a‖
  rw [PadicAlgCl.norm_extends]; rfl

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Conclude with `⟨0, by simp [h0]⟩`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`. Take `⟨k, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ`. Establish `hl0 : ((l : ℕ) : c.O) ≠ 0`.

Introduce `h`. Establish `h'` using `congrArg (fun y : c.O => (y : PadicAlgCl l)) h`. Simplify using `only [SubringClass.coe_natCast, ZeroMemClass.coe_zero] at h'`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h'`. Take `⟨e, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hπ`.

Use `set q := ‖(π : PadicAlgCl l)‖ with hqdef`. Establish `hlq : ‖((l : ℕ) : PadicAlgCl l)‖ = q ^ e`. Establish `h'` using `congrArg (fun y : c.O => ‖(y : PadicAlgCl l)‖) hw`. Simplify using `only [SubringClass.coe_natCast, Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow, norm_unit, one_mul] at h'`. Conclude with `h'`.

Establish `hq0 : 0 < q`. Rewrite using `[hqdef, norm_pos_iff]`. Introduce `h`. Conclude with `hπ.ne_zero (Subtype.ext h)`. Establish `hq1 : q < 1`.

Break down `(norm_le_one c π).lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Use `(norm_natCast_lt_one (l := l))` as an intermediate fact. Rewrite `this` using `[hlq, hqdef, h, one_pow]`.

Conclude with `lt_irrefl _ this`. Establish `hxq : ‖(((u : c.O) * π ^ k : c.O) : PadicAlgCl l)‖ = q ^ k`. Simplify using `only [Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]`. Both sides reduce to the same expression. Rewrite `hx` using `[hxq, norm_pow, hlq, ← pow_mul]`.

Establish `hk : e * m ≤ k` using `(pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).1 hx`. Take `⟨r, rfl⟩` from `Nat.exists_eq_add_of_le hk`. Use `⟨(u : c.O) * (↑w⁻¹ : c.O) ^ m * π ^ r, ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`. Establish `h2 : ((w : c.O) * (↑w⁻¹ : c.O)) ^ m = 1` using `by rw [Units.mul_inv, one_pow]`.

Take the linear combination `(-((u : c.O) * π ^ (e * m + r))) * h2`.
-/
theorem exists_eq_pow_mul (c : Coef l) (m : ℕ) (x : c.O)
    (hx : ‖(x : PadicAlgCl l)‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ m‖) : ∃ z : c.O, x = (l : c.O) ^ m * z := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun y : c.O => (y : PadicAlgCl l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h'
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hπ
  set q := ‖(π : PadicAlgCl l)‖ with hqdef
  have hlq : ‖((l : ℕ) : PadicAlgCl l)‖ = q ^ e := by
    have h' := congrArg (fun y : c.O => ‖(y : PadicAlgCl l)‖) hw
    simp only [SubringClass.coe_natCast, Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
      norm_unit, one_mul] at h'
    exact h'
  have hq0 : 0 < q := by
    rw [hqdef, norm_pos_iff]
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hq1 : q < 1 := by
    rcases (norm_le_one c π).lt_or_eq with h | h
    · exact h
    · exfalso
      have := (norm_natCast_lt_one (l := l))
      rw [hlq, hqdef, h, one_pow] at this
      exact lt_irrefl _ this
  have hxq : ‖(((u : c.O) * π ^ k : c.O) : PadicAlgCl l)‖ = q ^ k := by
    simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
    rfl
  rw [hxq, norm_pow, hlq, ← pow_mul] at hx
  have hk : e * m ≤ k := (pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).1 hx
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨(u : c.O) * (↑w⁻¹ : c.O) ^ m * π ^ r, ?_⟩
  rw [hw]
  have h2 : ((w : c.O) * (↑w⁻¹ : c.O)) ^ m = 1 := by rw [Units.mul_inv, one_pow]
  linear_combination (-((u : c.O) * π ^ (e * m + r))) * h2

/- English proof (translation)
Establish `hk : a - (((PadicInt.toZModPow m a).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p` using `l) m) := by`. Rewrite using `[RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]`. Rewrite `hk` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton']`. Take `⟨t, ht⟩` from `hk`. Establish `e : algebraMap ℤ_[l] (PadicAlgCl l) a - (((PadicInt.toZModPow m a).val : ℕ) : PadicAlgCl l) = algebraMap ℤ_[l] (PadicAlgCl l) t * ((l : ℕ) : PadicAlgCl l) ^ m`.

Use `congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) ht` as an intermediate fact. Simplify using `only [map_mul, map_pow, map_natCast, map_sub] at this`. Rewrite using `[this]`. Rewrite using `[e, norm_mul, norm_algebraMap_padicInt]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one t)`.
-/
theorem norm_sub_val_le (m : ℕ) (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a - (((PadicInt.toZModPow m a).val : ℕ) : PadicAlgCl l)‖
      ≤ ‖((l : ℕ) : PadicAlgCl l) ^ m‖ := by
  have hk : a - (((PadicInt.toZModPow m a).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨t, ht⟩ := hk
  have e : algebraMap ℤ_[l] (PadicAlgCl l) a - (((PadicInt.toZModPow m a).val : ℕ) : PadicAlgCl l)
      = algebraMap ℤ_[l] (PadicAlgCl l) t * ((l : ℕ) : PadicAlgCl l) ^ m := by
    have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) ht
    simp only [map_mul, map_pow, map_natCast, map_sub] at this
    rw [this]
  rw [e, norm_mul, norm_algebraMap_padicInt]
  exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one t)

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr y]`. Rewrite using `[AddSubmonoidClass.coe_finset_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Subalgebra.coe_smul, Algebra.smul_def, mul_comm]`.
-/
theorem coe_eq_sum {ι : Type} [Fintype ι] (c : Coef l) (b : Module.Basis ι ℤ_[l] c.O) (y : c.O) :
    (y : PadicAlgCl l) = ∑ i, ((b i : c.O) : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subalgebra.coe_smul, Algebra.smul_def, mul_comm]

/- English proof (translation)
Introduce `l _ c m`. Set `b` to `Module.Free.chooseBasis ℤ_[l] c.O`. Set `crd : Qbar l → Module.Free.ChooseBasisIndex ℤ_[l] c.O → ZMod (l ^ m)` to `fun x i => if hx : x ∈ c.O then PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i) else 0`. Establish `hcrd : ∀ (x : Qbar l) (hx : x ∈ c.O) i, crd x i = PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i)` using `fun x hx i => dif_pos hx`. Establish `hkill : ∀ x ∈ c.O, Cg m x 0 → crd x = 0`.

Introduce `x hx h`. Unfold `Cg at h`. Rewrite `h` using `[sub_zero]`. Take `⟨z, hz⟩` from `exists_eq_pow_mul c m ⟨x, hx⟩ h`. Use function extensionality and compare the values at `i`.

Rewrite using `[hcrd x hx i, hz]`. Establish `e : ((l : c.O) ^ m * z) = ((l : ℤ_[l]) ^ m) • z`. Rewrite using `[Algebra.smul_def, map_pow, map_natCast]`. Rewrite using `[e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]`. Both sides reduce to the same expression.

Use `⟨Module.Free.ChooseBasisIndex ℤ_[l] c.O, inferInstance, fun i => ((b i : c.O) : PadicAlgCl l), crd, fun i => ⟨(b i).2, norm_le_one c (b i)⟩, ?_, hkill, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy`. Use function extensionality and compare the values at `i`. Rewrite using `[hcrd _ (add_mem hx hy), Pi.add_apply, hcrd x hx, hcrd y hy, show (⟨x + y, add_mem hx hy⟩ : c.O) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, Finsupp.add_apply, map_add]`. Introduce `x hx`.

Unfold `Cg`. Establish `hx'` using `coe_eq_sum c b ⟨x, hx⟩`. Express the relevant statement in the definitionally equal form `x = _ at hx'`. Simplify using `only [hcrd x hx]`. Rewrite using `[congrArg (fun t => t - _) hx', ← Finset.sum_sub_distrib]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub, norm_mul]`. Conclude with `(mul_le_mul (norm_le_one c (b i)) (norm_sub_val_le m _) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])`. Introduce `n hn set y : Qbar l := ∑ i, ((b i : c.O) : PadicAlgCl l) * (((n i).val : ℕ) : Qbar l) with hydef`. Establish `hy : y ∈ c.O` using `Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (b i).2 (Subalgebra.natCast_mem _ _)`.

Establish `hyb : (⟨y, hy⟩ : c.O) = ∑ i, (((n i).val : ℕ) : ℤ_[l]) • b i`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubmonoidClass.coe_finset_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Subalgebra.coe_smul, Algebra.smul_def, map_natCast, mul_comm]`.

Establish `h0` using `hkill y hy hn`. Use function extensionality and compare the values at `i`. Use `congrFun h0 i` as an intermediate fact. Rewrite `this` using `[hcrd y hy i, hyb, b.repr_sum_self, map_natCast, ZMod.natCast_zmod_val]`. Conclude with `this`.
-/
theorem coord_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (m : ℕ), ∃ (ι : Type) (_ : Fintype ι) (o : ι → Qbar l)
    (crd : Qbar l → ι → ZMod (l ^ m)), (∀ i, o i ∈ c.O ∧ ‖o i‖ ≤ 1) ∧
    (∀ x ∈ c.O, ∀ y ∈ c.O, crd (x + y) = crd x + crd y) ∧ (∀ x ∈ c.O, Cg m x 0 → crd x = 0) ∧
    (∀ x ∈ c.O, Cg m x (∑ i, o i * ((crd x i).val : Qbar l))) ∧
    (∀ n : ι → ZMod (l ^ m), Cg m (∑ i, o i * ((n i).val : Qbar l)) 0 → n = 0) := by
  intro l _ c m
  classical
  let b := Module.Free.chooseBasis ℤ_[l] c.O
  let crd : Qbar l → Module.Free.ChooseBasisIndex ℤ_[l] c.O → ZMod (l ^ m) := fun x i =>
    if hx : x ∈ c.O then PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i) else 0
  have hcrd : ∀ (x : Qbar l) (hx : x ∈ c.O) i, crd x i = PadicInt.toZModPow m (b.repr ⟨x, hx⟩ i) :=
    fun x hx i => dif_pos hx
  have hkill : ∀ x ∈ c.O, Cg m x 0 → crd x = 0 := by
    intro x hx h
    unfold Cg at h
    rw [sub_zero] at h
    obtain ⟨z, hz⟩ := exists_eq_pow_mul c m ⟨x, hx⟩ h
    funext i
    rw [hcrd x hx i, hz]
    have e : ((l : c.O) ^ m * z) = ((l : ℤ_[l]) ^ m) • z := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow,
      ZMod.natCast_self, zero_mul]
    rfl
  refine ⟨Module.Free.ChooseBasisIndex ℤ_[l] c.O, inferInstance, fun i => ((b i : c.O) : PadicAlgCl l), crd,
    fun i => ⟨(b i).2, norm_le_one c (b i)⟩, ?_, hkill, ?_, ?_⟩
  · intro x hx y hy
    funext i
    rw [hcrd _ (add_mem hx hy), Pi.add_apply, hcrd x hx, hcrd y hy,
      show (⟨x + y, add_mem hx hy⟩ : c.O) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, Finsupp.add_apply, map_add]
  · intro x hx
    unfold Cg
    have hx' := coe_eq_sum c b ⟨x, hx⟩
    change x = _ at hx'
    simp only [hcrd x hx]
    rw [congrArg (fun t => t - _) hx', ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [← mul_sub, norm_mul]
    exact (mul_le_mul (norm_le_one c (b i)) (norm_sub_val_le m _) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
  · intro n hn
    set y : Qbar l := ∑ i, ((b i : c.O) : PadicAlgCl l) * (((n i).val : ℕ) : Qbar l) with hydef
    have hy : y ∈ c.O := Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (b i).2 (Subalgebra.natCast_mem _ _)
    have hyb : (⟨y, hy⟩ : c.O) = ∑ i, (((n i).val : ℕ) : ℤ_[l]) • b i := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Subalgebra.coe_smul, Algebra.smul_def, map_natCast, mul_comm]
    have h0 := hkill y hy hn
    funext i
    have := congrFun h0 i
    rw [hcrd y hy i, hyb, b.repr_sum_self, map_natCast, ZMod.natCast_zmod_val] at this
    exact this

end GlobalTheory.CoefCoord
