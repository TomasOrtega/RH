import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CoefCoord

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem norm_le_one_of_isIntegral (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  change spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem norm_le_one (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral _
    ((isIntegral_algHom_iff c.O.val Subtype.val_injective).2 (Algebra.IsIntegral.isIntegral x))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
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
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem norm_algebraMap_padicInt (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  show ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])‖ = ‖a‖
  rw [PadicAlgCl.norm_extends]; rfl

/- English proof (translation)
Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coe_eq_sum {ι : Type} [Fintype ι] (c : Coef l) (b : Module.Basis ι ℤ_[l] c.O) (y : c.O) :
    (y : PadicAlgCl l) = ∑ i, ((b i : c.O) : PadicAlgCl l) * algebraMap ℤ_[l] (PadicAlgCl l) (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subalgebra.coe_smul, Algebra.smul_def, mul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Replace the relevant objects with their definitions. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
