import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.LatticeChoice

open scoped Pointwise

/- English proof (translation)
Establish `hf' : (0 : ℤ) < f` using `by exact_mod_cast hf`. Establish `h1` using `Int.emod_add_mul_ediv (-a) (f : ℤ)`. Establish `h2` using `Int.emod_nonneg (-a) hf'.ne'`. Establish `h3` using `Int.emod_lt_of_pos (-a) hf'`. Use `⟨-((-a) / (f : ℤ)), ?_, ?_⟩` and prove the remaining obligations.

Establish `: (f : ℤ) * (-((-a) / (f : ℤ))) = -((f : ℤ) * ((-a) / (f : ℤ)))` using `by ring`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (f : ℤ) * (-((-a) / (f : ℤ)) - 1) = -((f : ℤ) * ((-a) / (f : ℤ))) - f` using `by ring`. Rewrite using `[this]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_ceil_div (f : ℕ) (hf : 0 < f) (a : ℤ) :
    ∃ n : ℤ, a ≤ (f : ℤ) * n ∧ (f : ℤ) * (n - 1) < a := by
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  have h1 := Int.emod_add_mul_ediv (-a) (f : ℤ)
  have h2 := Int.emod_nonneg (-a) hf'.ne'
  have h3 := Int.emod_lt_of_pos (-a) hf'
  refine ⟨-((-a) / (f : ℤ)), ?_, ?_⟩
  · have : (f : ℤ) * (-((-a) / (f : ℤ))) = -((f : ℤ) * ((-a) / (f : ℤ))) := by ring
    rw [this]; linarith
  · have : (f : ℤ) * (-((-a) / (f : ℤ)) - 1) = -((f : ℤ) * ((-a) / (f : ℤ))) - f := by ring
    rw [this]; linarith

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

variable (F E) in

/- English proof (translation)
Establish `h` using `FiltrationCocycleLiftCriterion.WeilRep.residueCard_eq_pow (K := F) (E := E)`. Establish `h1` using `one_lt_residueCard (K := E)`. Break down `Nat.eq_zero_or_pos (residueDegree F E) with h0 | h0` into its components or cases. Rewrite `h` using `[h0, pow_zero]`. Use linear arithmetic over natural numbers and integers.

Conclude with `h0`.
-/
theorem residueDegree_pos' : 0 < residueDegree F E := by
  have h := FiltrationCocycleLiftCriterion.WeilRep.residueCard_eq_pow (K := F) (E := E)
  have h1 := one_lt_residueCard (K := E)
  rcases Nat.eq_zero_or_pos (residueDegree F E) with h0 | h0
  · rw [h0, pow_zero] at h; omega
  · exact h0

/- English proof (translation)
Break down `eq_or_ne r 0 with rfl | hr0` into its components or cases. Simplify using the standard rewrite rules. Establish `hN : Algebra.norm F r ≠ 0` using `Algebra.norm_ne_zero_iff.2 hr0`. Use `isTrivialOn_addCharConductor hχ hχ1 _ ((mem_valBall_iff_le_ord (mul_ne_zero hκ hN)).2 ?_)` and prove the remaining obligations. Rewrite using `[ord_mul hκ hN, ord_norm (K := F) (L := E) r]`.

Establish `h1 : n ≤ ord r` using `(mem_valBall_iff_le_ord hr0).1 hr`. Establish `h2 : (residueDegree F E : ℤ) * n ≤ (residueDegree F E : ℤ) * ord r` using `mul_le_mul_of_nonneg_left h1 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem char_norm_eq_one {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    {κ : F} (hκ : κ ≠ 0) {n : ℤ}
    (hn : addCharConductor χ - ord κ ≤ (residueDegree F E : ℤ) * n) {r : E}
    (hr : r ∈ valBall E n) : χ (κ * Algebra.norm F r) = 1 := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  have hN : Algebra.norm F r ≠ 0 := Algebra.norm_ne_zero_iff.2 hr0
  refine isTrivialOn_addCharConductor hχ hχ1 _ ((mem_valBall_iff_le_ord (mul_ne_zero hκ hN)).2 ?_)
  rw [ord_mul hκ hN, ord_norm (K := F) (L := E) r]
  have h1 : n ≤ ord r := (mem_valBall_iff_le_ord hr0).1 hr
  have h2 : (residueDegree F E : ℤ) * n ≤ (residueDegree F E : ℤ) * ord r :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

/- English proof (translation)
Use `(isTrivialOn_iff (continuous_traceChar hχ hχ1) (traceChar_ne_one hχ hχ1) _).1 ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : y ∈ x • (valBall E n : Set E)`. Rewrite using `[smul_valBall hx]`. Conclude with `hy`.

Take `⟨r, hr, rfl⟩` from `hy'`. Conclude with `h r hr`.
-/
theorem conductor_le_of_forall {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    {x : E} (hx : x ≠ 0) {n : ℤ}
    (h : ∀ r ∈ valBall E n, χ (Algebra.trace F E (x * r)) = 1) :
    addCharConductor (traceChar E χ) ≤ n + ord x := by
  refine (isTrivialOn_iff (continuous_traceChar hχ hχ1) (traceChar_ne_one hχ hχ1) _).1 ?_
  intro y hy
  have hy' : y ∈ x • (valBall E n : Set E) := by
    rw [smul_valBall hx]; exact hy
  obtain ⟨r, hr, rfl⟩ := hy'
  exact h r hr

/- English proof (translation)
Establish `hp : (1 : ℝ) < residueCard F` using `by exact_mod_cast one_lt_residueCard (K := F)`. Establish `hQ : (1 : ℝ) < residueCard E` using `by exact_mod_cast one_lt_residueCard (K := E)`. Establish `hp0 : (residueCard F : ℝ) ≠ 0` using `by positivity`. Establish `hQ0 : (residueCard E : ℝ) ≠ 0` using `by positivity`. Establish `hQp : (residueCard E : ℝ) = (residueCard F : ℝ) ^ (residueDegree F E : ℤ)`.

Rewrite using `[FiltrationCocycleLiftCriterion.WeilRep.residueCard_eq_pow (K := F) (E := E)]`. Use `push_cast`. Rewrite using `[zpow_natCast]`. Establish `hmod : (modulus κ : ℝ) = (residueCard F : ℝ) ^ (-ord κ)`. Rewrite using `[modulus_of_ne_zero hκ]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `h1 : (residueCard E : ℝ) ^ (n - 1) ≤ (residueCard F : ℝ) ^ (c - ord κ)` using `by conv_lhs => rw [hQp, ← zpow_mul]`. Conclude with `zpow_le_zpow_right₀ hp.le hn.le`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[zpow_sub_one₀ hQ0]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ (residueCard E : ℝ) * (residueCard F : ℝ) ^ (c - ord κ) := mul_le_mul_of_nonneg_left h1 (by positivity)`. Use `_ = _ := by rw [hmod, sub_eq_add_neg, zpow_add₀ hp0]; ring`.
-/
theorem residueCard_zpow_le {κ : F} (hκ : κ ≠ 0) {c n : ℤ}
    (hn : (residueDegree F E : ℤ) * (n - 1) < c - ord κ) :
    (residueCard E : ℝ) ^ n
      ≤ (residueCard E : ℝ) * (residueCard F : ℝ) ^ c * (modulus κ : ℝ) := by
  have hp : (1 : ℝ) < residueCard F := by exact_mod_cast one_lt_residueCard (K := F)
  have hQ : (1 : ℝ) < residueCard E := by exact_mod_cast one_lt_residueCard (K := E)
  have hp0 : (residueCard F : ℝ) ≠ 0 := by positivity
  have hQ0 : (residueCard E : ℝ) ≠ 0 := by positivity
  have hQp : (residueCard E : ℝ) = (residueCard F : ℝ) ^ (residueDegree F E : ℤ) := by
    rw [FiltrationCocycleLiftCriterion.WeilRep.residueCard_eq_pow (K := F) (E := E)]
    push_cast
    rw [zpow_natCast]
  have hmod : (modulus κ : ℝ) = (residueCard F : ℝ) ^ (-ord κ) := by
    rw [modulus_of_ne_zero hκ]
    push_cast
    rfl
  have h1 : (residueCard E : ℝ) ^ (n - 1) ≤ (residueCard F : ℝ) ^ (c - ord κ) := by
    conv_lhs => rw [hQp, ← zpow_mul]
    exact zpow_le_zpow_right₀ hp.le hn.le
  calc (residueCard E : ℝ) ^ n = (residueCard E : ℝ) * (residueCard E : ℝ) ^ (n - 1) := by
        rw [zpow_sub_one₀ hQ0]; field_simp
    _ ≤ (residueCard E : ℝ) * (residueCard F : ℝ) ^ (c - ord κ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by rw [hmod, sub_eq_add_neg, zpow_add₀ hp0]; ring

end

/- English proof (translation)
Introduce `F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 Φ hlc hcs`. Take `⟨n₀, -, hinv, -⟩` from `exists_invariant_of_mem_schwartzBruhat (K := E) (f := Φ) ⟨hlc, hcs⟩`. Establish `hQ : (1 : ℝ) < residueCard E` using `by exact_mod_cast one_lt_residueCard (K := E)`. Establish `hp : (1 : ℝ) < residueCard F` using `by exact_mod_cast one_lt_residueCard (K := F)`. Establish `hQ0 : (0 : ℝ) < residueCard E` using `by linarith`.

Establish `hp0 : (0 : ℝ) < residueCard F` using `by linarith`. Take `⟨A, hA⟩ : ∃ A : ℝ, A = max ((residueCard E : ℝ) ^ n₀) ((residueCard E : ℝ) * (residueCard F : ℝ) ^ addCharConductor χ)` from `⟨_, rfl⟩`. Establish `hA1 : (residueCard E : ℝ) ^ n₀ ≤ A` using `hA ▸ le_max_left _ _`. Establish `hA2 : (residueCard E : ℝ) * (residueCard F : ℝ) ^ addCharConductor χ ≤ A` using `hA ▸ le_max_right _ _`. Establish `hApos : 0 < A` using `lt_of_lt_of_le (zpow_pos hQ0 _) hA1`.

Use `⟨(residueCard E : ℝ) ^ (-addCharConductor (traceChar E χ)) * A, mul_pos (zpow_pos hQ0 _) hApos, fun κ => ?_⟩` and prove the remaining obligations. Establish `hn : ∃ n : ℤ, n₀ ≤ n ∧ (∀ r ∈ valBall E n, χ (κ * Algebra.norm F r) = 1) ∧ (residueCard E : ℝ) ^ n ≤ A * max 1 (modulus κ : ℝ)`. Break down `eq_or_ne κ 0 with rfl | hκ` into its components or cases. Use `⟨n₀, le_rfl, fun r _ => by simp, ?_⟩` and prove the remaining obligations. Simplify using `using hA1`.

Take `⟨n₁, hn₁, hn₁'⟩` from `exists_ceil_div (residueDegree F E) (residueDegree_pos' F E) (addCharConductor χ - ord κ)`. Establish `hf : (0 : ℤ) ≤ residueDegree F E` using `by positivity`. Use `⟨max n₀ n₁, le_max_left _ _, fun r hr => ?_, ?_⟩` and prove the remaining obligations. Conclude with `char_norm_eq_one hχ hχ1 hκ (hn₁.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hf)) hr`. Establish `hm : (1 : ℝ) ≤ max 1 (modulus κ : ℝ)` using `le_max_left _ _`.

Break down `max_cases n₀ n₁ with ⟨h, -⟩ | ⟨h, -⟩` into its components or cases. Rewrite using `[h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨n, hn0, hχr, hQn⟩` from `hn`. Use `⟨valBall E n, isCompact_valBall n, isOpen_valBall n, fun r hr u => hinv u r (valBall_antitone hn0 hr), hχr, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hbound : 0 ≤ (residueCard E : ℝ) ^ (-addCharConductor (traceChar E χ)) * A * max 1 (modulus κ : ℝ)` using `by positivity`. Break down `eq_or_ne x 0 with rfl | hx0` into its components or cases. Simplify using `using hbound`.

Establish `hc` using `conductor_le_of_forall hχ hχ1 hx0 hx`. Establish `hmod : (modulus x : ℝ) = (residueCard E : ℝ) ^ (-ord x)`. Rewrite using `[modulus_of_ne_zero hx0]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[hmod]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[zpow_add₀ hQ0.ne']`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by`.

Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left hQn (zpow_pos hQ0 _).le`.
-/
theorem exists_lattice_adapted : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ (Φ : E → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ → ∃ C : ℝ, 0 < C ∧ ∀ κ : F, ∃ M : AddSubgroup E, IsCompact (M : Set E) ∧ IsOpen (M : Set E) ∧ (∀ r ∈ M, ∀ u, Φ (u + r) = Φ u) ∧ (∀ r ∈ M, χ (κ * Algebra.norm F r) = 1) ∧ ∀ x : E, (∀ r ∈ M, χ (Algebra.trace F E (x * r)) = 1) → (modulus x : ℝ) ≤ C * max 1 (modulus κ : ℝ) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 Φ hlc hcs
  obtain ⟨n₀, -, hinv, -⟩ := exists_invariant_of_mem_schwartzBruhat (K := E) (f := Φ) ⟨hlc, hcs⟩
  have hQ : (1 : ℝ) < residueCard E := by exact_mod_cast one_lt_residueCard (K := E)
  have hp : (1 : ℝ) < residueCard F := by exact_mod_cast one_lt_residueCard (K := F)
  have hQ0 : (0 : ℝ) < residueCard E := by linarith
  have hp0 : (0 : ℝ) < residueCard F := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = max ((residueCard E : ℝ) ^ n₀)
      ((residueCard E : ℝ) * (residueCard F : ℝ) ^ addCharConductor χ) := ⟨_, rfl⟩
  have hA1 : (residueCard E : ℝ) ^ n₀ ≤ A := hA ▸ le_max_left _ _
  have hA2 : (residueCard E : ℝ) * (residueCard F : ℝ) ^ addCharConductor χ ≤ A :=
    hA ▸ le_max_right _ _
  have hApos : 0 < A := lt_of_lt_of_le (zpow_pos hQ0 _) hA1
  refine ⟨(residueCard E : ℝ) ^ (-addCharConductor (traceChar E χ)) * A,
    mul_pos (zpow_pos hQ0 _) hApos, fun κ => ?_⟩
  have hn : ∃ n : ℤ, n₀ ≤ n ∧ (∀ r ∈ valBall E n, χ (κ * Algebra.norm F r) = 1) ∧
      (residueCard E : ℝ) ^ n ≤ A * max 1 (modulus κ : ℝ) := by
    rcases eq_or_ne κ 0 with rfl | hκ
    · refine ⟨n₀, le_rfl, fun r _ => by simp, ?_⟩
      simpa using hA1
    obtain ⟨n₁, hn₁, hn₁'⟩ := exists_ceil_div (residueDegree F E) (residueDegree_pos' F E)
      (addCharConductor χ - ord κ)
    have hf : (0 : ℤ) ≤ residueDegree F E := by positivity
    refine ⟨max n₀ n₁, le_max_left _ _, fun r hr => ?_, ?_⟩
    · exact char_norm_eq_one hχ hχ1 hκ
        (hn₁.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hf)) hr
    · have hm : (1 : ℝ) ≤ max 1 (modulus κ : ℝ) := le_max_left _ _
      rcases max_cases n₀ n₁ with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
        calc (residueCard E : ℝ) ^ n₀ ≤ A := hA1
          _ ≤ A * max 1 (modulus κ : ℝ) := le_mul_of_one_le_right hApos.le hm
      · rw [h]
        calc (residueCard E : ℝ) ^ n₁
            ≤ (residueCard E : ℝ) * (residueCard F : ℝ) ^ addCharConductor χ * (modulus κ : ℝ) :=
              residueCard_zpow_le hκ hn₁'
          _ ≤ A * max 1 (modulus κ : ℝ) :=
              mul_le_mul hA2 (le_max_right _ _) (NNReal.coe_nonneg _) hApos.le
  obtain ⟨n, hn0, hχr, hQn⟩ := hn
  refine ⟨valBall E n, isCompact_valBall n, isOpen_valBall n,
    fun r hr u => hinv u r (valBall_antitone hn0 hr), hχr, fun x hx => ?_⟩
  have hbound : 0 ≤ (residueCard E : ℝ) ^ (-addCharConductor (traceChar E χ)) * A *
      max 1 (modulus κ : ℝ) := by positivity
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using hbound
  have hc := conductor_le_of_forall hχ hχ1 hx0 hx
  have hmod : (modulus x : ℝ) = (residueCard E : ℝ) ^ (-ord x) := by
    rw [modulus_of_ne_zero hx0]
    push_cast
    rfl
  rw [hmod]
  calc (residueCard E : ℝ) ^ (-ord x)
      ≤ (residueCard E : ℝ) ^ (n + -addCharConductor (traceChar E χ)) :=
        zpow_le_zpow_right₀ hQ.le (by omega)
    _ = (residueCard E : ℝ) ^ (-addCharConductor (traceChar E χ)) * (residueCard E : ℝ) ^ n := by
        rw [zpow_add₀ hQ0.ne']; ring
    _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hQn (zpow_pos hQ0 _).le

end GlobalTheory.CompanionTheory.LatticeChoice
