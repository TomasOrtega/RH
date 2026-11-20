import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.LeadTerm

/- English proof (translation)
Establish `hlin : ∀ (n : ℕ) (y : X), q (n • m + y) = q (n • m) + q y + n * (q (m + y) - q m - q y)`. Introduce `n y`. Proceed by induction on `n with`. Consider the case `zero => simp [hz]`. Consider the case `succ n ih`.

Establish `h` using `hcub (n • m) m y`. Rewrite using `[succ_nsmul]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : q (m + m) = 4 * q m`.

Establish `h` using `hcub m m (-m)`. Simplify using `only [add_neg_cancel_right, add_neg_cancel, hneg, hz] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : ∀ n : ℕ, q (n • m) = (n : ℤ) ^ 2 * q m`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp [hz]`. Consider the case `succ n ih`. Establish `h` using `hlin n m`. Rewrite using `[succ_nsmul, h, ih, h2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Break down `(h0 m).lt_or_eq with hm | hm` into its components or cases. Establish `: (j : ℤ) ≤ j * q m` using `by nlinarith`. Combine the linear relations using `[h0 (m + α)]`.

Establish `hB : q α ≤ q (m + α)`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Use `set n : ℕ := (q α).toNat + 1 with hn`. Establish `hnz : (n : ℤ) = q α + 1`.

Rewrite using `[hn]`. Use `push_cast`. Rewrite using `[Int.toNat_of_nonneg (h0 α)]`. Establish `h` using `hlin n α`. Rewrite `h` using `[hsq n, ← hm]`.

Establish `hpos` using `h0 (n • m + α)`. Rewrite `h` using `[hnz]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[← hm]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem int_bound {X : Type} [AddCommGroup X] (q : X → ℤ) (h0 : ∀ x, 0 ≤ q x) (hz : q 0 = 0)
    (hneg : ∀ a, q (-a) = q a)
    (hcub : ∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b))
    (m α : X) (j : ℕ) (hj : q α ≤ j) : q α ≤ j * q m + q (m + α) := by
  have hlin : ∀ (n : ℕ) (y : X),
      q (n • m + y) = q (n • m) + q y + n * (q (m + y) - q m - q y) := by
    intro n y
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      have h := hcub (n • m) m y
      rw [succ_nsmul]
      push_cast
      linarith
  have h2 : q (m + m) = 4 * q m := by
    have h := hcub m m (-m)
    simp only [add_neg_cancel_right, add_neg_cancel, hneg, hz] at h
    linarith
  have hsq : ∀ n : ℕ, q (n • m) = (n : ℤ) ^ 2 * q m := by
    intro n
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      have h := hlin n m
      rw [succ_nsmul, h, ih, h2]
      push_cast
      ring
  rcases (h0 m).lt_or_eq with hm | hm
  · have : (j : ℤ) ≤ j * q m := by nlinarith
    linarith [h0 (m + α)]
  · have hB : q α ≤ q (m + α) := by
      by_contra hlt
      push_neg at hlt
      set n : ℕ := (q α).toNat + 1 with hn
      have hnz : (n : ℤ) = q α + 1 := by
        rw [hn]; push_cast; rw [Int.toNat_of_nonneg (h0 α)]
      have h := hlin n α
      rw [hsq n, ← hm] at h
      have hpos := h0 (n • m + α)
      rw [hnz] at h
      nlinarith
    rw [← hm]
    linarith

/- English proof (translation)
Take `⟨c, hc⟩` from `(IsDiscreteValuationRing.addVal_le_iff_dvd).mp h`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl c`. Establish `hinj` using `IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)`. Use `⟨s, s.2, a, hinj ?_⟩` and prove the remaining obligations. Establish `hs` using `IsLocalization.mk'_spec (Localization.AtPrime P) a s`.

Rewrite using `[map_mul, map_mul, hc, ← hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_eq_of_addVal_le {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)] (x y : R)
    (h : IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R _ y) ≤
      IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R _ x)) :
    ∃ s ∉ P, ∃ a : R, s * x = a * y := by
  obtain ⟨c, hc⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).mp h
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
  have hinj := IsLocalization.injective (Localization.AtPrime P)
    (Ideal.primeCompl_le_nonZeroDivisors P)
  refine ⟨s, s.2, a, hinj ?_⟩
  have hs := IsLocalization.mk'_spec (Localization.AtPrime P) a s
  rw [map_mul, map_mul, hc, ← hs]
  ring

/- English proof (translation)
Introduce `R _ _ _ _ _ X _ _ κ hneg hcub hmax α`. Use `set K := FractionRing R`. Establish `hinjK : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hκ0 : κ 0 = 1`. Establish `h` using `hcub 0 0 0`.

Simplify using `only [add_zero] at h`. Conclude with `mul_right_cancel (b := κ 0 * κ 0 * κ 0) (by simpa only [_root_.mul_assoc, _root_.one_mul] using h)`. Establish `hr : ∀ x, ∃ s : R, (κ x : K) = algebraMap R K s`. Introduce `x`. Distinguish the cases in `hx : x = 0`.

Conclude with `⟨1, by simp [hx, hκ0]⟩`. Take `⟨s, -, hs⟩` from `hmax x hx`. Conclude with `⟨s, hs⟩`. Use `choose r hr using hr`. Establish `hr0 : ∀ x, r x ≠ 0`.

Introduce `x h`. Use `hr x` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `(κ x).ne_zero this`. Establish `hrneg : ∀ a, r (-a) = r a`.

Introduce `a`. Apply `hinjK` to reduce the goal to its premises. Rewrite using `[← hr, ← hr, hneg]`. Establish `hrz : r 0 = 1`. Apply `hinjK` to reduce the goal to its premises.

Rewrite using `[← hr, hκ0]`. Simplify using the standard rewrite rules. Establish `hrcub : ∀ a a' b, r (a + a' + b) * r a * r a' * r b = r (a + a') * r (a + b) * r (a' + b)`. Introduce `a a' b`. Apply `hinjK` to reduce the goal to its premises.

Simplify using `only [map_mul, ← hr]`. Conclude with `congrArg Units.val (hcub a a' b)` after adjusting the coercions. Establish `hZ : ∀ (j : ℕ) (m : X), ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) = algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α)`. Introduce `j m`. Establish `hm0 : algebraMap R K (r m) ≠ 0` using `by rw [← hr]; exact (κ m).ne_zero`.

Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hr, map_mul, map_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `set Φ : Ideal R → ℕ → Prop := fun P j => ∀ m, ∃ s ∉ P, ∃ a : R, s * (r m ^ j * r (m + α)) = a * r α`. Establish `hloc : ∀ P : Ideal R, ∀ hP : P.IsPrime, P.height = 1 → ∃ J : ℕ, (r α ∉ P → J = 0) ∧ ∀ j ≥ J, Φ P j`.

Introduce `P hP h1`. Use `haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1`. Use `set D := Localization.AtPrime P`. Establish `hne : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) ≠ ⊤`. Introduce `x h`.

Rewrite `h` using `[IsDiscreteValuationRing.addVal_eq_top_iff]`. Conclude with `hr0 x (IsLocalization.injective D (Ideal.primeCompl_le_nonZeroDivisors P) (by rw [h, map_zero]))`. Use `set v : X → ℕ := fun x => (IsDiscreteValuationRing.addVal D (algebraMap R D (r x))).toNat`. Establish `he : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) = (v x : ℕ∞)` using `fun x => (ENat.coe_toNat (hne x)).symm`. Establish `hvz : v 0 = 0`.

Use `he 0` as an intermediate fact. Rewrite `this` using `[hrz, map_one, IsDiscreteValuationRing.addVal_one]`. Conclude with `this.symm` after adjusting the coercions. Establish `hvneg : ∀ a, v (-a) = v a` using `by intro a; simp only [v, hrneg]`. Establish `hvcub : ∀ a a' b, v (a + a' + b) + v a + v a' + v b = v (a + a') + v (a + b) + v (a' + b)`.

Introduce `a a' b`. Use `congrArg (fun t => IsDiscreteValuationRing.addVal D (algebraMap R D t)) (hrcub a a' b)` as an intermediate fact. Simplify using `only [map_mul, IsDiscreteValuationRing.addVal_mul, he] at this`. Conclude with `this` after adjusting the coercions. Use `⟨v α, fun hα => ?_, fun j hj m => ?_⟩` and prove the remaining obligations.

Establish `hu : IsUnit (algebraMap R D (r α))` using `(IsLocalization.AtPrime.isUnit_to_map_iff D P (r α)).mpr hα`. Use `he α` as an intermediate fact. Rewrite `this` using `[← hu.unit_spec, IsDiscreteValuationRing.addVal_eq_zero_of_unit]`. Conclude with `this.symm` after adjusting the coercions. Establish `hb` using `int_bound (fun x => (v x : ℤ)) (fun x => by positivity) (by simp [hvz]) (fun a => by simp [hvneg]) (fun a a' b => by exact_mod_cast hvcub a a' b) m α j (by exact_mod_cast hj)`.

Establish `hb' : v α ≤ j * v m + v (m + α)` using `by exact_mod_cast hb`. Apply `exists_mul_eq_of_addVal_le P` to reduce the goal to its premises. Rewrite using `[map_mul, map_pow, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, he, he, he, nsmul_eq_mul]`. Conclude with `hb'` after adjusting the coercions. Establish `hfin` using `ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one (hr0 α)`.

Establish `hev : ∀ P ∈ {P : Ideal R | P.IsPrime ∧ P.height = 1 ∧ r α ∈ P}, ∀ᶠ j in Filter.atTop, Φ P j`. Introduce and unpack `P ⟨hP, h1, -⟩`. Take `⟨J, -, hJ⟩` from `hloc P hP h1`. Conclude with `Filter.eventually_atTop.mpr ⟨J, hJ⟩`. Take `⟨J, hJ⟩` from `Filter.eventually_atTop.mp ((Filter.eventually_all_finite hfin).mpr hev)`.

Establish `hall : ∀ j ≥ J, ∀ P : Ideal R, P.IsPrime → P.height = 1 → Φ P j`. Introduce `j hj P hP h1`. Distinguish the cases in `hα : r α ∈ P`. Conclude with `hJ j hj P ⟨hP, h1, hα⟩`. Take `⟨J', hJ'0, hJ'⟩` from `hloc P hP h1`.

Conclude with `hJ' j (by rw [hJ'0 hα]; exact Nat.zero_le _)`. Establish `hint : ∀ j ≥ J, ∀ m, ∃ c : R, algebraMap R K c = ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K)`. Introduce `j hj m`. Rewrite using `[hZ]`. Establish `hα0 : algebraMap R K (r α) ≠ 0` using `by rw [← hr]; exact (κ α).ne_zero`.

Take `⟨c, hc⟩` from `ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (K := K) (algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α)) (by`. Introduce `P hP h1`. Take `⟨s, hs, a, ha⟩` from `hall j hj P hP h1 m`. Use `⟨s, hs, a, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_div_assoc', ← map_mul, ha, map_mul, mul_div_cancel_right₀ _ hα0])`.

Conclude with `⟨c, hc⟩`. Establish `hstep : ∀ k ≥ J + 2, ∀ m, ∃ c : R, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) = algebraMap R K (r m * c)`. Introduce `k hk m`. Take `⟨i, rfl⟩ : ∃ i, k = i + 1` from `⟨k - 1, by omega⟩`. Take `⟨c, hc⟩` from `hint (i - 1) (by omega) m`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hi : i - 1 + 1 = i` using `by omega`. Rewrite `hc` using `[hi]`. Rewrite using `[pow_succ', _root_.mul_assoc, Units.val_mul, ← hc, map_mul, hr]`. Use `⟨J + 2, fun k hk => ⟨fun m hm => ?_, fun n => ?_⟩⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `hstep k hk m`. Take `⟨s, hs, hsκ⟩` from `hmax m hm`. Establish `: r m = s` using `hinjK (by rw [← hr, hsκ])`. Conclude with `⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩`. Use `(GlobalTheory.T.finite_even_cubical_values_not_mem_maximalIdeal_pow R X κ hneg hcub hmax n).subset ?_` and prove the remaining obligations.

Introduce `m hm hm'`. Apply `hm` to reduce the goal to its premises. Take `⟨s, hs, hsκ⟩` from `hm'`. Take `⟨c, hc⟩` from `hstep k hk m`. Establish `: r m = s` using `hinjK (by rw [← hr, hsκ])`.

Conclude with `⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩`.
-/
theorem lead_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ α : X, ∃ k₀ : ℕ, ∀ k ≥ k₀, (∀ m, m ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {m | ¬ ∃ s ∈ maximalIdeal R ^ n, ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ κ hneg hcub hmax α
  set K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  have hκ0 : κ 0 = 1 := by
    have h := hcub 0 0 0
    simp only [add_zero] at h
    exact mul_right_cancel (b := κ 0 * κ 0 * κ 0)
      (by simpa only [_root_.mul_assoc, _root_.one_mul] using h)

  have hr : ∀ x, ∃ s : R, (κ x : K) = algebraMap R K s := by
    intro x
    by_cases hx : x = 0
    · exact ⟨1, by simp [hx, hκ0]⟩
    · obtain ⟨s, -, hs⟩ := hmax x hx
      exact ⟨s, hs⟩
  choose r hr using hr
  have hr0 : ∀ x, r x ≠ 0 := by
    intro x h
    have := hr x
    rw [h, map_zero] at this
    exact (κ x).ne_zero this
  have hrneg : ∀ a, r (-a) = r a := by
    intro a; apply hinjK; rw [← hr, ← hr, hneg]
  have hrz : r 0 = 1 := by
    apply hinjK; rw [← hr, hκ0]; simp
  have hrcub : ∀ a a' b, r (a + a' + b) * r a * r a' * r b = r (a + a') * r (a + b) * r (a' + b) := by
    intro a a' b
    apply hinjK
    simp only [map_mul, ← hr]
    exact_mod_cast congrArg Units.val (hcub a a' b)

  have hZ : ∀ (j : ℕ) (m : X), ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) =
      algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α) := by
    intro j m
    have hm0 : algebraMap R K (r m) ≠ 0 := by rw [← hr]; exact (κ m).ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hr, map_mul, map_pow]
    field_simp
    ring

  set Φ : Ideal R → ℕ → Prop := fun P j => ∀ m, ∃ s ∉ P, ∃ a : R, s * (r m ^ j * r (m + α)) = a * r α
  have hloc : ∀ P : Ideal R, ∀ hP : P.IsPrime, P.height = 1 →
      ∃ J : ℕ, (r α ∉ P → J = 0) ∧ ∀ j ≥ J, Φ P j := by
    intro P hP h1
    haveI := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R P h1
    set D := Localization.AtPrime P
    have hne : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) ≠ ⊤ := by
      intro x h
      rw [IsDiscreteValuationRing.addVal_eq_top_iff] at h
      exact hr0 x (IsLocalization.injective D (Ideal.primeCompl_le_nonZeroDivisors P)
        (by rw [h, map_zero]))
    set v : X → ℕ := fun x => (IsDiscreteValuationRing.addVal D (algebraMap R D (r x))).toNat
    have he : ∀ x, IsDiscreteValuationRing.addVal D (algebraMap R D (r x)) = (v x : ℕ∞) :=
      fun x => (ENat.coe_toNat (hne x)).symm
    have hvz : v 0 = 0 := by
      have := he 0
      rw [hrz, map_one, IsDiscreteValuationRing.addVal_one] at this
      exact_mod_cast this.symm
    have hvneg : ∀ a, v (-a) = v a := by intro a; simp only [v, hrneg]
    have hvcub : ∀ a a' b, v (a + a' + b) + v a + v a' + v b = v (a + a') + v (a + b) + v (a' + b) := by
      intro a a' b
      have := congrArg (fun t => IsDiscreteValuationRing.addVal D (algebraMap R D t)) (hrcub a a' b)
      simp only [map_mul, IsDiscreteValuationRing.addVal_mul, he] at this
      exact_mod_cast this
    refine ⟨v α, fun hα => ?_, fun j hj m => ?_⟩
    · have hu : IsUnit (algebraMap R D (r α)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff D P (r α)).mpr hα
      have := he α
      rw [← hu.unit_spec, IsDiscreteValuationRing.addVal_eq_zero_of_unit] at this
      exact_mod_cast this.symm
    · have hb := int_bound (fun x => (v x : ℤ)) (fun x => by positivity) (by simp [hvz])
        (fun a => by simp [hvneg]) (fun a a' b => by exact_mod_cast hvcub a a' b) m α j
        (by exact_mod_cast hj)
      have hb' : v α ≤ j * v m + v (m + α) := by exact_mod_cast hb
      apply exists_mul_eq_of_addVal_le P
      rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
        he, he, he, nsmul_eq_mul]
      exact_mod_cast hb'

  have hfin := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one (hr0 α)
  have hev : ∀ P ∈ {P : Ideal R | P.IsPrime ∧ P.height = 1 ∧ r α ∈ P},
      ∀ᶠ j in Filter.atTop, Φ P j := by
    rintro P ⟨hP, h1, -⟩
    obtain ⟨J, -, hJ⟩ := hloc P hP h1
    exact Filter.eventually_atTop.mpr ⟨J, hJ⟩
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp ((Filter.eventually_all_finite hfin).mpr hev)
  have hall : ∀ j ≥ J, ∀ P : Ideal R, P.IsPrime → P.height = 1 → Φ P j := by
    intro j hj P hP h1
    by_cases hα : r α ∈ P
    · exact hJ j hj P ⟨hP, h1, hα⟩
    · obtain ⟨J', hJ'0, hJ'⟩ := hloc P hP h1
      exact hJ' j (by rw [hJ'0 hα]; exact Nat.zero_le _)

  have hint : ∀ j ≥ J, ∀ m, ∃ c : R,
      algebraMap R K c = ((κ m ^ (j + 1) * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) := by
    intro j hj m
    rw [hZ]
    have hα0 : algebraMap R K (r α) ≠ 0 := by rw [← hr]; exact (κ α).ne_zero
    obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := R) (K := K)
      (algebraMap R K (r m ^ j * r (m + α)) / algebraMap R K (r α)) (by
        intro P hP h1
        obtain ⟨s, hs, a, ha⟩ := hall j hj P hP h1 m
        refine ⟨s, hs, a, ?_⟩
        rw [mul_div_assoc', ← map_mul, ha, map_mul, mul_div_cancel_right₀ _ hα0])
    exact ⟨c, hc⟩

  have hstep : ∀ k ≥ J + 2, ∀ m, ∃ c : R,
      ((κ m ^ k * (κ (m + α) * (κ m)⁻¹ * (κ α)⁻¹) : Kˣ) : K) = algebraMap R K (r m * c) := by
    intro k hk m
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    obtain ⟨c, hc⟩ := hint (i - 1) (by omega) m
    refine ⟨c, ?_⟩
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at hc
    rw [pow_succ', _root_.mul_assoc, Units.val_mul, ← hc, map_mul, hr]
  refine ⟨J + 2, fun k hk => ⟨fun m hm => ?_, fun n => ?_⟩⟩
  · obtain ⟨c, hc⟩ := hstep k hk m
    obtain ⟨s, hs, hsκ⟩ := hmax m hm
    have : r m = s := hinjK (by rw [← hr, hsκ])
    exact ⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩
  · refine (GlobalTheory.T.finite_even_cubical_values_not_mem_maximalIdeal_pow R X κ hneg hcub hmax n).subset ?_
    intro m hm hm'
    apply hm
    obtain ⟨s, hs, hsκ⟩ := hm'
    obtain ⟨c, hc⟩ := hstep k hk m
    have : r m = s := hinjK (by rw [← hr, hsκ])
    exact ⟨r m * c, by rw [this]; exact Ideal.mul_mem_right c _ hs, hc⟩

end GlobalTheory.LeadTerm
