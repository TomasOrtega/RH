import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Unfold `hat`. Establish `step : ∀ i ∈ Finset.range N, φ (i : ZMod N) * cexp (2 * π * Complex.I * ((i : ℂ) * (d : ℂ)) / N) = φ (i : ZMod N) * ZMod.stdAddChar ((i : ZMod N) * (d : ZMod N))`. Introduce `i _`. Use `congr 1`. Establish `: ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N)` using `by push_cast; rfl`.

Rewrite using `[this, ZMod.stdAddChar_coe]`. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[Finset.sum_congr rfl step]`. Use `Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `i _`. Simplify using the standard rewrite rules. Introduce `y _`. Simplify using `[ZMod.val_lt]`. Introduce `i hi`.

Simplify using `only [Finset.mem_coe, Finset.mem_range] at hi`. Simplify using `[ZMod.val_cast_of_lt hi]`. Introduce `y _`. Simplify using the standard rewrite rules. Introduce `i _`.

Both sides reduce to the same expression.
-/
theorem hat_eq_sum_std {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (d : ℤ) :
    hat φ d = ∑ y : ZMod N, φ y * ZMod.stdAddChar (y * (d : ZMod N)) := by
  unfold hat
  have step : ∀ i ∈ Finset.range N, φ (i : ZMod N) * cexp (2 * π * Complex.I * ((i : ℂ) * (d : ℂ)) / N)
      = φ (i : ZMod N) * ZMod.stdAddChar ((i : ZMod N) * (d : ZMod N)) := by
    intro i _
    congr 1
    have : ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N) := by push_cast; rfl
    rw [this, ZMod.stdAddChar_coe]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl step]
  refine Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) ?_ ?_ ?_ ?_ ?_
  · intro i _; simp
  · intro y _; simp [ZMod.val_lt]
  · intro i hi; simp only [Finset.mem_coe, Finset.mem_range] at hi; simp [ZMod.val_cast_of_lt hi]
  · intro y _; simp
  · intro i _; rfl

/- English proof (translation)
Rewrite using `[hat_eq_sum_std, hat_eq_sum_std]`. Use `push_cast`. Simplify using the standard rewrite rules.
-/
theorem hat_add_period {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (x : ℤ) : hat φ (x + N) = hat φ x := by
  rw [hat_eq_sum_std, hat_eq_sum_std]
  push_cast
  simp

/- English proof (translation)
Establish `h` using `gaussSum_mulShift_eq θ ((ZMod.stdAddChar (N := N)).mulShift (x : ZMod N)) hd.unit`. Simplify using `only [gaussSum, AddChar.mulShift_apply, IsUnit.unit_spec] at h`. Rewrite using `[hat_eq_sum_std, hat_eq_sum_std]`. Unfold `ch`. Combine the equalities or inequalities in the displayed calculation.

Use `Fintype.sum_congr _ _ (fun y => ?_)` and prove the remaining obligations. Use `push_cast`. Put the polynomial expressions in normal form. Use `_ = θ⁻¹ (d : ZMod N) * ∑ y : ZMod N, θ y * ZMod.stdAddChar ((x : ZMod N) * y) := h`. Use `_ = _ := by`.

Use `congr 1`. Use `Fintype.sum_congr _ _ (fun y => ?_)` and prove the remaining obligations. Put the polynomial expressions in normal form.
-/
theorem hat_mul_unit {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (d x : ℤ) (hd : IsUnit (d : ZMod N)) :
    hat θ (x * d) = ch θ⁻¹ d * hat θ x := by
  have h := gaussSum_mulShift_eq θ ((ZMod.stdAddChar (N := N)).mulShift (x : ZMod N)) hd.unit
  simp only [gaussSum, AddChar.mulShift_apply, IsUnit.unit_spec] at h
  rw [hat_eq_sum_std, hat_eq_sum_std]
  unfold ch
  calc ∑ y : ZMod N, θ y * ZMod.stdAddChar (y * ((x * d : ℤ) : ZMod N))
      = ∑ y : ZMod N, θ y * ZMod.stdAddChar ((x : ZMod N) * ((d : ZMod N) * y)) := by
        refine Fintype.sum_congr _ _ (fun y => ?_); push_cast; ring_nf
    _ = θ⁻¹ (d : ZMod N) * ∑ y : ZMod N, θ y * ZMod.stdAddChar ((x : ZMod N) * y) := h
    _ = _ := by
        congr 1; refine Fintype.sum_congr _ _ (fun y => ?_); ring_nf

/- English proof (translation)
Rewrite using `[hat_eq_sum_std]`. Simplify using `only [Int.cast_zero, mul_zero, AddChar.map_zero_eq_one, mul_one]`. Conclude with `MulChar.sum_eq_zero_of_ne_one h`.
-/
theorem hat_zero_of_ne_one {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (h : θ ≠ 1) : hat θ 0 = 0 := by
  rw [hat_eq_sum_std]
  simp only [Int.cast_zero, mul_zero, AddChar.map_zero_eq_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one h

/- English proof (translation)
Take `⟨a, b, hab⟩` from `h`. Establish `: ((a * d + b * N : ℤ) : ZMod N) = 1` using `by rw [hab]; simp`. Move the coercions through the operations in `at this`. Rewrite `this` using `[ZMod.natCast_self, mul_zero, add_zero]`. Conclude with `IsUnit.of_mul_eq_one (a : ZMod N) (by rw [mul_comm]; exact this)`.
-/
theorem isUnit_of_isCoprime {N : ℕ} (d : ℤ) (h : IsCoprime d N) : IsUnit (d : ZMod N) := by
  obtain ⟨a, b, hab⟩ := h
  have : ((a * d + b * N : ℤ) : ZMod N) = 1 := by rw [hab]; simp
  push_cast at this
  rw [ZMod.natCast_self, mul_zero, add_zero] at this
  exact IsUnit.of_mul_eq_one (a : ZMod N) (by rw [mul_comm]; exact this)

/- English proof (translation)
Rewrite using `[hat_eq_sum_std]`. Establish `hterm : ∀ y : ZMod l, (1 : DirichletCharacter ℂ l) y * ZMod.stdAddChar (y * (x : ZMod l)) = ZMod.stdAddChar (y * (x : ZMod l)) - if y = 0 then 1 else 0`. Introduce `y`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality.

Rewrite using `[MulChar.map_zero]`. Simplify using the standard rewrite rules. Rewrite using `[MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)]`. Simplify using `[hy]`. Rewrite using `[Fintype.sum_congr _ _ hterm, Finset.sum_sub_distrib, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar l)]`.

Simplify using `[ZMod.card, ZMod.intCast_zmod_eq_zero_iff_dvd]`.
-/
theorem hat_prime_one {l : ℕ} [Fact l.Prime] (x : ℤ) :
    hat (1 : DirichletCharacter ℂ l) x = (if (l : ℤ) ∣ x then (l : ℂ) else 0) - 1 := by
  classical
  rw [hat_eq_sum_std]
  have hterm : ∀ y : ZMod l, (1 : DirichletCharacter ℂ l) y * ZMod.stdAddChar (y * (x : ZMod l))
      = ZMod.stdAddChar (y * (x : ZMod l)) - if y = 0 then 1 else 0 := by
    intro y
    by_cases hy : y = 0
    · subst hy; rw [MulChar.map_zero]; simp
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)]; simp [hy]
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_sub_distrib, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar l)]
  simp [ZMod.card, ZMod.intCast_zmod_eq_zero_iff_dvd]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `h` using `gaussSum_mul_gaussSum_eq_card hψ (ZMod.isPrimitive_stdAddChar l)`. Rewrite using `[hat_eq_sum_std]`. Introduce `h0`. Simplify using `only [Int.cast_one, mul_one] at h0`.

Rewrite `h` using `[gaussSum, h0, zero_mul, ZMod.card]`. Conclude with `(Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h.symm`. Introduce `x`. Distinguish the cases in `hx : (x : ZMod l) = 0`. Establish `h1 : hat ψ x = 0`.

Rewrite using `[hat_eq_sum_std, hx]`. Simplify using `only [mul_zero, AddChar.map_zero_eq_one, mul_one]`. Conclude with `MulChar.sum_eq_zero_of_ne_one hψ`. Rewrite using `[h1]`. Unfold `ch`.

Rewrite using `[hx, MulChar.map_zero, mul_zero]`. Use `hat_mul_unit ψ x 1 (isUnit_iff_ne_zero.mpr hx)` as an intermediate fact. Rewrite `this` using `[one_mul]`. Rewrite using `[this, mul_comm]`.
-/
theorem hat_prime_ne_one {l : ℕ} [Fact l.Prime] (ψ : DirichletCharacter ℂ l) (hψ : ψ ≠ 1) :
    hat ψ 1 ≠ 0 ∧ ∀ x, hat ψ x = hat ψ 1 * ch ψ⁻¹ x := by
  constructor
  · have h := gaussSum_mul_gaussSum_eq_card hψ (ZMod.isPrimitive_stdAddChar l)
    rw [hat_eq_sum_std]
    intro h0
    simp only [Int.cast_one, mul_one] at h0
    rw [gaussSum, h0, zero_mul, ZMod.card] at h
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h.symm
  · intro x
    by_cases hx : (x : ZMod l) = 0
    · have h1 : hat ψ x = 0 := by
        rw [hat_eq_sum_std, hx]
        simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
        exact MulChar.sum_eq_zero_of_ne_one hψ
      rw [h1]; unfold ch; rw [hx, MulChar.map_zero, mul_zero]
    · have := hat_mul_unit ψ x 1 (isUnit_iff_ne_zero.mpr hx)
      rw [one_mul] at this
      rw [this, mul_comm]

/- English proof (translation)
Establish `: a * (x : ZMod M) = (((a.val : ℤ) * x : ℤ) : ZMod M)` using `by push_cast; simp`. Rewrite using `[this, ZMod.stdAddChar_coe]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem stdAddChar_nat_mul_int {M : ℕ} [NeZero M] (a : ZMod M) (x : ℤ) :
    (ZMod.stdAddChar (a * (x : ZMod M)) : ℂ) = cexp (2 * π * Complex.I * ((a.val : ℂ) * x) / M) := by
  have : a * (x : ZMod M) = (((a.val : ℤ) * x : ℤ) : ZMod M) := by push_cast; simp
  rw [this, ZMod.stdAddChar_coe]; push_cast; ring_nf

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero l := ⟨hl.ne'⟩`. Use `haveI : NeZero (N * l) := ⟨(Nat.mul_pos hN hl).ne'⟩`. Set `f : ZMod N × ZMod l → ZMod (N * l)` to `fun p => ((p.1.val * l + p.2.val * N : ℕ) : ZMod (N * l))`. Establish `hcN : ∀ k : ℕ, ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (k : ZMod (N * l)) = (k : ZMod N)` using `fun k => map_natCast _ k`.

Establish `hcl : ∀ k : ℕ, ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (k : ZMod (N * l)) = (k : ZMod l)` using `fun k => map_natCast _ k`. Establish `hlu : IsUnit (l : ZMod N)` using `(ZMod.unitOfCoprime l hc.symm).isUnit`. Establish `hNu : IsUnit (N : ZMod l)` using `(ZMod.unitOfCoprime N hc).isUnit`. Establish `hinj : Function.Injective f`. Introduce `p q hpq`.

Establish `h1` using `congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hpq`. Establish `h2` using `congrArg (ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l)) hpq`. Simplify using `only [f, hcN, hcl] at h1 h2`. Move the coercions through the operations in `at h1 h2`. Simplify using `only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val] at h1 h2`.

Conclude with `Prod.ext (hlu.mul_right_cancel h1) (hNu.mul_right_cancel h2)`. Establish `hbij : Function.Bijective f`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Conclude with `⟨hinj, by simp [ZMod.card]⟩`. Rewrite using `[hat_eq_sum_std, hat_eq_sum_std, hat_eq_sum_std, ← Fintype.sum_bijective f hbij _ _ (fun _ => rfl), Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]`.

Use `Fintype.sum_congr _ _ (fun a => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_congr _ _ (fun b => ?_)` and prove the remaining obligations. Establish `hf : f (a, b) = (((a.val * l + b.val * N : ℕ) : ℤ) : ZMod (N * l))` using `by simp [f]`. Establish `hval : φ (f (a, b)) = θ a * θ l * (ψ b * ψ N)`.

Use `hφ ((a.val * l + b.val * N : ℕ) : ℤ)` as an intermediate fact. Unfold `ch at this`. Rewrite using `[hf, this]`. Use `push_cast`. Simplify using `only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val, map_mul]`.

Establish `he : (ZMod.stdAddChar (f (a, b) * (x : ZMod (N * l))) : ℂ) = ZMod.stdAddChar (a * (x : ZMod N)) * ZMod.stdAddChar (b * (x : ZMod l))`. Establish `: f (a, b) * (x : ZMod (N * l)) = ((((a.val * l + b.val * N : ℕ) : ℤ) * x : ℤ) : ZMod (N * l))`. Rewrite using `[hf]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[this, ZMod.stdAddChar_coe, stdAddChar_nat_mul_int a x, stdAddChar_nat_mul_int b x, ← Complex.exp_add]`. Use `congr 1`. Establish `hN' : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`. Establish `hl' : (l : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hl.ne'`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hval, he]`. Unfold `ch`. Simplify using `only [Int.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hat_mul_coprime (N l : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l)
    (φ : DirichletCharacter ℂ (N * l)) (hN : 0 < N) (hl : 0 < l) (hc : N.Coprime l)
    (hφ : ∀ d : ℤ, ch φ d = ch θ d * ch ψ d) (x : ℤ) :
    hat φ x = ch θ l * ch ψ N * (hat θ x * hat ψ x) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : NeZero (N * l) := ⟨(Nat.mul_pos hN hl).ne'⟩
  let f : ZMod N × ZMod l → ZMod (N * l) := fun p => ((p.1.val * l + p.2.val * N : ℕ) : ZMod (N * l))
  have hcN : ∀ k : ℕ, ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (k : ZMod (N * l)) = (k : ZMod N) :=
    fun k => map_natCast _ k
  have hcl : ∀ k : ℕ, ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (k : ZMod (N * l)) = (k : ZMod l) :=
    fun k => map_natCast _ k
  have hlu : IsUnit (l : ZMod N) := (ZMod.unitOfCoprime l hc.symm).isUnit
  have hNu : IsUnit (N : ZMod l) := (ZMod.unitOfCoprime N hc).isUnit
  have hinj : Function.Injective f := by
    intro p q hpq
    have h1 := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hpq
    have h2 := congrArg (ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l)) hpq
    simp only [f, hcN, hcl] at h1 h2
    push_cast at h1 h2
    simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val] at h1 h2
    exact Prod.ext (hlu.mul_right_cancel h1) (hNu.mul_right_cancel h2)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [ZMod.card]⟩
  rw [hat_eq_sum_std, hat_eq_sum_std, hat_eq_sum_std, ← Fintype.sum_bijective f hbij _ _ (fun _ => rfl),
    Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
  refine Fintype.sum_congr _ _ (fun a => ?_)
  rw [Finset.mul_sum]
  refine Fintype.sum_congr _ _ (fun b => ?_)
  have hf : f (a, b) = (((a.val * l + b.val * N : ℕ) : ℤ) : ZMod (N * l)) := by simp [f]
  have hval : φ (f (a, b)) = θ a * θ l * (ψ b * ψ N) := by
    have := hφ ((a.val * l + b.val * N : ℕ) : ℤ)
    unfold ch at this
    rw [hf, this]
    push_cast
    simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val, map_mul]
  have he : (ZMod.stdAddChar (f (a, b) * (x : ZMod (N * l))) : ℂ)
      = ZMod.stdAddChar (a * (x : ZMod N)) * ZMod.stdAddChar (b * (x : ZMod l)) := by
    have : f (a, b) * (x : ZMod (N * l)) = ((((a.val * l + b.val * N : ℕ) : ℤ) * x : ℤ) : ZMod (N * l)) := by
      rw [hf]; push_cast; rfl
    rw [this, ZMod.stdAddChar_coe, stdAddChar_nat_mul_int a x, stdAddChar_nat_mul_int b x, ← Complex.exp_add]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hl' : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
    push_cast
    field_simp
  rw [hval, he]
  unfold ch
  simp only [Int.cast_natCast]
  ring

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `N θ hN haveI : NeZero N := ⟨hN.ne'⟩`. Conclude with `⟨fun x => hat_add_period _ x, fun d x hd => hat_mul_unit θ d x (isUnit_of_isCoprime d hd), hat_zero_of_ne_one θ⟩`. Introduce `N l θ ψ φ hN hl hc hφ x`. Conclude with `hat_mul_coprime N l θ ψ φ hN hl hc hφ x`.

Introduce `l ψ hl haveI : Fact l.Prime := ⟨hl⟩`. Use `⟨hat_prime_ne_one ψ, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl x`. Conclude with `hat_prime_one x`.
-/
theorem hat_char_props : (∀ (N : ℕ) (θ : DirichletCharacter ℂ N), 0 < N → (∀ x : ℤ, hat θ (x + N) = hat θ x) ∧ (∀ d x : ℤ, IsCoprime d N → hat θ (x * d) = ch θ⁻¹ d * hat θ x) ∧ (θ ≠ 1 → hat θ 0 = 0)) ∧ (∀ (N l : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)), 0 < N → 0 < l → N.Coprime l → (∀ d : ℤ, ch φ d = ch θ d * ch ψ d) → ∀ x, hat φ x = ch θ l * ch ψ N * (hat θ x * hat ψ x)) ∧ ∀ (l : ℕ) (ψ : DirichletCharacter ℂ l), l.Prime → (ψ ≠ 1 → hat ψ 1 ≠ 0 ∧ ∀ x, hat ψ x = hat ψ 1 * ch ψ⁻¹ x) ∧ (ψ = 1 → ∀ x : ℤ, hat ψ x = (if (l : ℤ) ∣ x then (l : ℂ) else 0) - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N θ hN
    haveI : NeZero N := ⟨hN.ne'⟩
    exact ⟨fun x => hat_add_period _ x, fun d x hd => hat_mul_unit θ d x (isUnit_of_isCoprime d hd),
      hat_zero_of_ne_one θ⟩
  · intro N l θ ψ φ hN hl hc hφ x
    exact hat_mul_coprime N l θ ψ φ hN hl hc hφ x
  · intro l ψ hl
    haveI : Fact l.Prime := ⟨hl⟩
    refine ⟨hat_prime_ne_one ψ, ?_⟩
    rintro rfl x
    exact hat_prime_one x

end GlobalTheory.EisM
