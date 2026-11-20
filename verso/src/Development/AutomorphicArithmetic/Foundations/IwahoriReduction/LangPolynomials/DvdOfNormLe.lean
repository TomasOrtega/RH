import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h1` using `GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) ((u : c.O)).2`. Establish `h2` using `GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) (((u⁻¹ : c.Oˣ) : c.O)).2`. Establish `h3 : ((u : c.O) : PadicAlgCl l) * (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l) = 1`. Rewrite using `[← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]`. Establish `h4 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1`.

Rewrite using `[← norm_mul, h3, norm_one]`. Use polynomial arithmetic with `[norm_nonneg ((u : c.O) : PadicAlgCl l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)]`.
-/
private theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) ((u : c.O)).2
  have h2 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (c := c) (((u⁻¹ : c.Oˣ) : c.O)).2
  have h3 : ((u : c.O) : PadicAlgCl l) * (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have h4 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, h3, norm_one]
  nlinarith [norm_nonneg ((u : c.O) : PadicAlgCl l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)]

/- English proof (translation)
Use `haveI := c.dvr`. Establish `hne : (ϖ : PadicAlgCl l) ≠ 0`. Introduce `h`. Conclude with `hϖ.ne_zero (Subtype.ext h)`. Use `⟨norm_pos_iff.2 hne, ?_⟩` and prove the remaining obligations.

Establish `hl : (l : c.O) ≠ 0`. Introduce `h`. Apply `(GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l))` to reduce the goal to its premises. Use `congrArg (fun z : c.O => (z : PadicAlgCl l)) h` as an intermediate fact. Simplify using `using this`.

Take `⟨e, u, he⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ`. Establish `h1 : ‖((l : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ e`. Rewrite using `[he]`. Use `push_cast`. Rewrite using `[norm_mul, norm_unit c u, one_mul, norm_pow]`.

Establish `h2 : ‖((l : c.O) : PadicAlgCl l)‖ < 1`. Use `GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)` as an intermediate fact. Simplify using `using this`. Establish `h3 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1` using `GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem ϖ.2`. Break down `h3.lt_or_eq with h | h` into its components or cases.

Conclude with `h`. Rewrite `h2` using `[h1, h, one_pow]`. Conclude with `absurd h2 (lt_irrefl 1)`.
-/
private theorem norm_pos_and_lt_one_of_irreducible (c : Coef l) (ϖ : c.O) (hϖ : Irreducible ϖ) :
    0 < ‖(ϖ : PadicAlgCl l)‖ ∧ ‖(ϖ : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  have hne : (ϖ : PadicAlgCl l) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  refine ⟨norm_pos_iff.2 hne, ?_⟩
  have hl : (l : c.O) ≠ 0 := by
    intro h
    apply (GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l))
    have := congrArg (fun z : c.O => (z : PadicAlgCl l)) h
    simpa using this
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  have h1 : ‖((l : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ e := by
    rw [he]
    push_cast
    rw [norm_mul, norm_unit c u, one_mul, norm_pow]
  have h2 : ‖((l : c.O) : PadicAlgCl l)‖ < 1 := by
    have := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)
    simpa using this
  have h3 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1 := GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem ϖ.2
  rcases h3.lt_or_eq with h | h
  · exact h
  · rw [h1, h, one_pow] at h2
    exact absurd h2 (lt_irrefl 1)

/- English proof (translation)
Use `haveI := c.dvr`. Distinguish the cases in `hx : x = 0`. Rewrite using `[hx]`. Conclude with `dvd_zero y`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`.

Take `⟨h0, h1⟩` from `norm_pos_and_lt_one_of_irreducible c ϖ hϖ`. Establish `hn : ∀ (k : ℕ) (w : c.Oˣ), ‖(((w : c.O) * ϖ ^ k : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ k`. Introduce `k w`. Use `push_cast`. Rewrite using `[norm_mul, norm_unit c w, one_mul, norm_pow]`.

Take `⟨a, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ`. Take `⟨b, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ`. Rewrite `h` using `[hn, hn]`. Establish `hba : b ≤ a` using `(pow_le_pow_iff_right_of_lt_one₀ h0 h1).1 h`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hba`.

Use `⟨((v⁻¹ : c.Oˣ) : c.O) * u * ϖ ^ k, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.mul_inv, one_mul]`. Use `_ = _ := by ring`.
-/
private theorem dvd_of_norm_le (c : Coef l) (x y : c.O) (hy : y ≠ 0)
    (h : ‖(x : PadicAlgCl l)‖ ≤ ‖(y : PadicAlgCl l)‖) : y ∣ x := by
  haveI := c.dvr
  by_cases hx : x = 0
  · rw [hx]
    exact dvd_zero y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨h0, h1⟩ := norm_pos_and_lt_one_of_irreducible c ϖ hϖ
  have hn : ∀ (k : ℕ) (w : c.Oˣ),
      ‖(((w : c.O) * ϖ ^ k : c.O) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ k := by
    intro k w
    push_cast
    rw [norm_mul, norm_unit c w, one_mul, norm_pow]
  obtain ⟨a, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨b, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [hn, hn] at h
  have hba : b ≤ a := (pow_le_pow_iff_right_of_lt_one₀ h0 h1).1 h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hba
  refine ⟨((v⁻¹ : c.Oˣ) : c.O) * u * ϖ ^ k, ?_⟩
  calc (u : c.O) * ϖ ^ (b + k) = ((v : c.O) * ((v⁻¹ : c.Oˣ) : c.O)) * u * ϖ ^ (b + k) := by
        rw [Units.mul_inv, one_mul]
    _ = _ := by ring

/- English proof (translation)
Establish `hl0 : (l : c.O) ≠ 0` using `fun h0 => GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l) (by simpa using congrArg Subtype.val h0)`. Use `dvd_of_norm_le c x _ (pow_ne_zero n hl0) ?_` and prove the remaining obligations. Simplify `h` using `[Cg]`.
-/
private theorem div_pow_of_cg (c : Coef l) (n : ℕ) (x : c.O) (h : Cg n (x : PadicAlgCl l) 0) :
    ∃ y : c.O, x = (l : c.O) ^ n * y := by
  have hl0 : (l : c.O) ≠ 0 := fun h0 => GlobalTheory.LambdaValuationPowers.natCast_ne_zero (l := l) (by simpa using congrArg Subtype.val h0)
  refine dvd_of_norm_le c x _ (pow_ne_zero n hl0) ?_
  simpa [Cg] using h

/- English proof (translation)
Introduce `l _ c`. Use `haveI := c.fin`. Use `haveI := c.dvr`. Use `⟨⟨⟨_, Module.finBasis ℤ_[l] c.O⟩⟩, fun β => ⟨fun i => GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (β.e i).2, ?_, fun n x h => div_pow_of_cg c n x h, ?_⟩⟩` and prove the remaining obligations. Introduce `n x h i`.

Establish `hzc : ((∑ j, x j • β.e j : c.O) : PadicAlgCl l) = ∑ j, β.val j * algebraMap ℤ_[l] (PadicAlgCl l) (x j)`. Simplify using `[Bas.val, Algebra.smul_def, mul_comm]`. Take `⟨y, hy⟩` from `div_pow_of_cg c n (∑ j, x j • β.e j) (by rw [hzc]; exact h)`. Establish `hs : (∑ j, x j • β.e j : c.O) = ((l : ℤ_[l]) ^ n) • y`. Rewrite using `[hy, Algebra.smul_def, map_pow, map_natCast]`.

Establish `hx : β.e.repr (∑ j, x j • β.e j) i = x i`. Rewrite using `[β.e.repr_sum_self]`. Use `⟨β.e.repr y i, ?_⟩` and prove the remaining obligations. Rewrite using `[← hx, hs, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Introduce `x hx h1`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h1`. Take `⟨z, hz⟩` from `dvd_of_norm_le c 1 ⟨x, hx⟩ (fun h0 => hx0 (by simpa using congrArg Subtype.val h0)) (by simp [h1])`. Establish `hz' : (1 : PadicAlgCl l) = x * (z : PadicAlgCl l)`.

Use `congrArg Subtype.val hz` as an intermediate fact. Simplify using `using this`. Rewrite using `[← eq_inv_of_mul_eq_one_right hz'.symm]`. Conclude with `z.2`.
-/
theorem pBasEx : SBasEx := by
  intro l _ c
  haveI := c.fin
  haveI := c.dvr
  refine ⟨⟨⟨_, Module.finBasis ℤ_[l] c.O⟩⟩, fun β => ⟨fun i => GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (β.e i).2,
    ?_, fun n x h => div_pow_of_cg c n x h, ?_⟩⟩
  · intro n x h i
    have hzc : ((∑ j, x j • β.e j : c.O) : PadicAlgCl l)
        = ∑ j, β.val j * algebraMap ℤ_[l] (PadicAlgCl l) (x j) := by
      simp [Bas.val, Algebra.smul_def, mul_comm]
    obtain ⟨y, hy⟩ := div_pow_of_cg c n (∑ j, x j • β.e j) (by rw [hzc]; exact h)
    have hs : (∑ j, x j • β.e j : c.O) = ((l : ℤ_[l]) ^ n) • y := by
      rw [hy, Algebra.smul_def, map_pow, map_natCast]
    have hx : β.e.repr (∑ j, x j • β.e j) i = x i := by
      rw [β.e.repr_sum_self]
    refine ⟨β.e.repr y i, ?_⟩
    rw [← hx, hs, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · intro x hx h1
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h1
    obtain ⟨z, hz⟩ := dvd_of_norm_le c 1 ⟨x, hx⟩
      (fun h0 => hx0 (by simpa using congrArg Subtype.val h0)) (by simp [h1])
    have hz' : (1 : PadicAlgCl l) = x * (z : PadicAlgCl l) := by
      have := congrArg Subtype.val hz
      simpa using this
    rw [← eq_inv_of_mul_eq_one_right hz'.symm]
    exact z.2

end UpperTheory.Kd.C7
