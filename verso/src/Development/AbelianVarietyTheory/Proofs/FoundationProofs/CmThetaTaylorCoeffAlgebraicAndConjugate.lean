import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTaylorThetaTranslateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaConj

def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}

noncomputable def topHom (σ : ℂ →+* ℂ) : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ :=
  σ.toRatAlgHom.comp (⊤ : IntermediateField ℚ ℂ).val

/- English proof (translation)
Simplify using `[cj, TaylorLogMetric.liftM, hx]`.
-/
theorem cj_of_mem (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {x : ℂ} (hx : x ∈ M) :
    cj M ρ x = ρ ⟨x, hx⟩ := by
  simp [cj, TaylorLogMetric.liftM, hx]

/- English proof (translation)
Rewrite using `[cj_of_mem _ _ (IntermediateField.mem_top)]`. Both sides reduce to the same expression.
-/
theorem cj_top (σ : ℂ →+* ℂ) (x : ℂ) : cj ⊤ (topHom σ) x = σ x := by
  rw [cj_of_mem _ _ (IntermediateField.mem_top)]
  rfl

/- English proof (translation)
Rewrite using `[cj_of_mem _ _ (IntermediateField.mem_top), cj_of_mem _ _ (IntermediateField.mem_top), cj_of_mem _ _ (IntermediateField.mem_top), ← map_div₀]`. Both sides reduce to the same expression.
-/
theorem cj_top_div (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (x y : ℂ) :
    cj ⊤ ρ (x / y) = cj ⊤ ρ x / cj ⊤ ρ y := by
  rw [cj_of_mem _ _ (IntermediateField.mem_top), cj_of_mem _ _ (IntermediateField.mem_top),
    cj_of_mem _ _ (IntermediateField.mem_top), ← map_div₀]
  rfl

/- English proof (translation)
Unfold `cj at h2 h3`. Unfold `lamConj`. Rewrite using `[h2, h3]`.
-/
theorem lamConj_congr {M M' : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {ρ' : M' →ₐ[ℚ] ℂ}
    {Λ : AddSubgroup ℂ} (h2 : cj M ρ (g2 Λ) = cj M' ρ' (g2 Λ)) (h3 : cj M ρ (g3 Λ) = cj M' ρ' (g3 Λ)) :
    lamConj M ρ Λ = lamConj M' ρ' Λ := by
  unfold cj at h2 h3
  unfold lamConj
  rw [h2, h3]

/- English proof (translation)
Take `⟨w₁, w₂, hi, rfl⟩` from `h`. Use `⟨⟨w₁, w₂, hi⟩, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]`. Simplify using `[zsmul_eq_mul]`.
-/
theorem IsLat.exists_periodPair {Λ : AddSubgroup ℂ} (h : IsLat Λ) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, hi, rfl⟩ := h
  refine ⟨⟨w₁, w₂, hi⟩, fun z => ?_⟩
  rw [AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
  simp [zsmul_eq_mul]

/- English proof (translation)
Take `⟨L, hL⟩` from `h.exists_periodPair`. Establish `hs` using `Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ => g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨Λ, h2.symm, h3.symm⟩`. Conclude with `(GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL).2.2.2.2.2.1 _ (hs.1.trans h2) (hs.2.trans h3)`.
-/
theorem lamConj_eq_self {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {Λ : AddSubgroup ℂ} (h : IsLat Λ)
    (h2 : cj M ρ (g2 Λ) = g2 Λ) (h3 : cj M ρ (g3 Λ) = g3 Λ) : lamConj M ρ Λ = Λ := by
  obtain ⟨L, hL⟩ := h.exists_periodPair
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨Λ, h2.symm, h3.symm⟩
  exact (GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL).2.2.2.2.2.1 _ (hs.1.trans h2) (hs.2.trans h3)

/- English proof (translation)
Unfold `coef1 GL3Theta.th0`. Rewrite using `[iteratedDeriv_div_const]`. Simplify using `only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylorCoeff_evenTheta_eq_normalised_translate (Λ : AddSubgroup ℂ) (t : ℂ) (n : ℕ) :
    coef1 (GL3Theta.th0 Λ t) n = coef1 (U1 Λ t (sgStar Λ)) n / coef1 (U1 Λ t (sgStar Λ)) 0 := by
  unfold coef1 GL3Theta.th0
  rw [iteratedDeriv_div_const]
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  ring

/- English proof (translation)
Use `⟨Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * (area Λ : ℂ))), Complex.exp_ne_zero _, fun z => ?_⟩` and prove the remaining obligations. Simplify using `only [U1]`. Rewrite using `[← add_assoc, mul_assoc (G _), ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]`. Use `congr 2`. Rewrite using `[map_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem latticeTranslationOperator_add_exists_const (Λ : AddSubgroup ℂ) (t ω : ℂ) (G : ℂ → ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, U1 Λ (t + ω) G z = c * U1 Λ t (U1 Λ ω G) z := by
  refine ⟨Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * (area Λ : ℂ))),
    Complex.exp_ne_zero _, fun z => ?_⟩
  simp only [U1]
  rw [← add_assoc, mul_assoc (G _), ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [map_add]
  ring

/- English proof (translation)
Take `⟨c, hc, hU⟩` from `latticeTranslationOperator_add_exists_const Λ t ω (sgStar Λ)`. Establish `h1` using `(GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.2 ω hω`. Use `set e : ℂ := (if ω / 2 ∈ Λ then 1 else -1) with he`. Apply the tactic sequence `have he0 : e ≠ 0 := by rw [he]; split_ifs <;> simp`. Establish `h2 : ∀ z, U1 Λ (t + ω) (sgStar Λ) z = (c * e) * U1 Λ t (sgStar Λ) z`.

Introduce `z`. Rewrite using `[hU]`. Simplify using `only [U1] at h1 ⊢`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.

Use function extensionality and compare the values at `z`. Simplify using `only [GL3Theta.th0]`. Rewrite using `[h2, h2, mul_div_mul_left _ _ (mul_ne_zero hc he0)]`.
-/
theorem evenTheta_add_lattice_mem {Λ : AddSubgroup ℂ} (h : IsLat Λ) (t : ℂ) {ω : ℂ} (hω : ω ∈ Λ) :
    GL3Theta.th0 Λ (t + ω) = GL3Theta.th0 Λ t := by
  obtain ⟨c, hc, hU⟩ := latticeTranslationOperator_add_exists_const Λ t ω (sgStar Λ)
  have h1 := (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.2 ω hω
  set e : ℂ := (if ω / 2 ∈ Λ then 1 else -1) with he
  have he0 : e ≠ 0 := by rw [he]; split_ifs <;> simp
  have h2 : ∀ z, U1 Λ (t + ω) (sgStar Λ) z = (c * e) * U1 Λ t (sgStar Λ) z := by
    intro z
    rw [hU]
    simp only [U1] at h1 ⊢
    rw [h1]; ring
  funext z
  simp only [GL3Theta.th0]
  rw [h2, h2, mul_div_mul_left _ _ (mul_ne_zero hc he0)]

/- English proof (translation)
Establish `hk : ∀ u, 2 * u ∈ Λ → w * (1 - w) * u ∈ Λ`. Introduce `u hu`. Use `Λ.zsmul_mem hu k` as an intermediate fact. Rewrite using `[hw]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs' : ∀ z ∈ Λ, (1 - w) * z ∈ Λ` using `fun z hz => by`. Use `Λ.sub_mem hz (hs z hz)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Establish `four : ∀ a b u : ℂ, 2 * a ∈ Λ → 2 * b ∈ Λ → 2 * u ∈ Λ → a ∉ Λ → b ∉ Λ → a - b ∉ Λ → u ∈ Λ ∨ u - a ∈ Λ ∨ u - b ∈ Λ ∨ u - a - b ∈ Λ`. Take `⟨w₁, w₂, hi, rfl⟩` from `h`. Introduce `a b u h1 h2 h3 ha hb hab`. Establish `red : ∀ (x : ℂ) (m n : ℤ), x = m * (w₁ / 2) + n * (w₂ / 2) → m % 2 = 0 → n % 2 = 0 → x ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)`.

Introduce `x m n hx hm hn`. Take `⟨m', rfl⟩ : ∃ m', m = 2 * m'` from `⟨m / 2, by omega⟩`. Take `⟨n', rfl⟩ : ∃ n', n = 2 * n'` from `⟨n / 2, by omega⟩`. Rewrite using `[AddSubgroup.mem_closure_pair]`. Use `⟨m', n', ?_⟩` and prove the remaining obligations.

Rewrite using `[hx]`. Simplify using `only [zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1`, `h2`, `h3` using `[AddSubgroup.mem_closure_pair]`.

Take `⟨a1, a2, ea⟩` from `h1`. Take `⟨b1, b2, eb⟩` from `h2`. Take `⟨u1, u2, eu⟩` from `h3`. Simplify using `only [zsmul_eq_mul] at ea eb eu`. Establish `ra` using `red a a1 a2 (by linear_combination (-1 / 2 : ℂ) * ea)`.

Establish `rb` using `red b b1 b2 (by linear_combination (-1 / 2 : ℂ) * eb)`. Establish `rab` using `red (a - b) (a1 - b1) (a2 - b2) (by push_cast; linear_combination (-1 / 2 : ℂ) * ea + (1 / 2 : ℂ) * eb)`. Establish `r0` using `red u u1 u2 (by linear_combination (-1 / 2 : ℂ) * eu)`. Establish `r1` using `red (u - a) (u1 - a1) (u2 - a2) (by push_cast; linear_combination (-1 / 2 : ℂ) * eu + (1 / 2 : ℂ) * ea)`. Establish `r2` using `red (u - b) (u1 - b1) (u2 - b2) (by push_cast; linear_combination (-1 / 2 : ℂ) * eu + (1 / 2 : ℂ) * eb)`.

Establish `r3` using `red (u - a - b) (u1 - a1 - b1) (u2 - a2 - b2) (by push_cast; linear_combination (-1 / 2 : ℂ) * eu + (1 / 2 : ℂ) * ea + (1 / 2 : ℂ) * eb)`. Establish `na : ¬ (a1 % 2 = 0 ∧ a2 % 2 = 0)` using `fun h => ha (ra h.1 h.2)`. Establish `nb : ¬ (b1 % 2 = 0 ∧ b2 % 2 = 0)` using `fun h => hb (rb h.1 h.2)`. Establish `nab : ¬ ((a1 - b1) % 2 = 0 ∧ (a2 - b2) % 2 = 0)` using `fun h => hab (rab h.1 h.2)`. Establish `: (u1 % 2 = 0 ∧ u2 % 2 = 0) ∨ ((u1 - a1) % 2 = 0 ∧ (u2 - a2) % 2 = 0) ∨ ((u1 - b1) % 2 = 0 ∧ (u2 - b2) % 2 = 0) ∨ ((u1 - a1 - b1) % 2 = 0 ∧ (u2 - a2 - b2) % 2 = 0)` using `by omega`.

Break down `this with h | h | h | h` into its components or cases. Conclude with `Or.inl (r0 h.1 h.2)`. Conclude with `Or.inr (Or.inl (r1 h.1 h.2))`. Conclude with `Or.inr (Or.inr (Or.inl (r2 h.1 h.2)))`. Conclude with `Or.inr (Or.inr (Or.inr (r3 h.1 h.2)))`.

Establish `hkt` using `hk t h2`. Establish `hab : w * t - (1 - w) * t ∉ Λ` using `fun h => ha (by`. Use `Λ.add_mem (Λ.add_mem (hs _ h) hkt) hkt` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`.

Break down `four (w * t) ((1 - w) * t) t' (by have := hs _ h2; convert this using 1; ring) (by have := hs' _ h2; convert this using 1; ring) h2' ha hb hab with h | h | h | h` into its components or cases. Conclude with `absurd (hs _ h) ha'`. Conclude with `absurd (by have := Λ.add_mem (hs' _ h) hkt; convert this using 1; ring) hb'`. Conclude with `absurd (by have := Λ.add_mem (hs _ h) hkt; convert this using 1; ring) ha'`. Use `Λ.neg_mem h` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_torsion_unique {Λ : AddSubgroup ℂ} (h : IsLat Λ) (w : ℂ) (k : ℤ)
    (hw : w * (1 - w) = 2 * k) {t t' : ℂ}
    (h2 : 2 * t ∈ Λ) (ha : w * t ∉ Λ) (hb : (1 - w) * t ∉ Λ)
    (h2' : 2 * t' ∈ Λ) (ha' : w * t' ∉ Λ) (hb' : (1 - w) * t' ∉ Λ)
    (hs : ∀ z ∈ Λ, w * z ∈ Λ) : t - t' ∈ Λ := by
  have hk : ∀ u, 2 * u ∈ Λ → w * (1 - w) * u ∈ Λ := by
    intro u hu
    have := Λ.zsmul_mem hu k
    rw [hw]; convert this using 1; rw [zsmul_eq_mul]; ring
  have hs' : ∀ z ∈ Λ, (1 - w) * z ∈ Λ := fun z hz => by
    have := Λ.sub_mem hz (hs z hz); convert this using 1; ring

  have four : ∀ a b u : ℂ, 2 * a ∈ Λ → 2 * b ∈ Λ → 2 * u ∈ Λ → a ∉ Λ → b ∉ Λ → a - b ∉ Λ →
      u ∈ Λ ∨ u - a ∈ Λ ∨ u - b ∈ Λ ∨ u - a - b ∈ Λ := by
    obtain ⟨w₁, w₂, hi, rfl⟩ := h
    intro a b u h1 h2 h3 ha hb hab
    have red : ∀ (x : ℂ) (m n : ℤ), x = m * (w₁ / 2) + n * (w₂ / 2) → m % 2 = 0 → n % 2 = 0 →
        x ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
      intro x m n hx hm hn
      obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = 2 * n' := ⟨n / 2, by omega⟩
      rw [AddSubgroup.mem_closure_pair]
      refine ⟨m', n', ?_⟩
      rw [hx]; simp only [zsmul_eq_mul]; push_cast; ring
    rw [AddSubgroup.mem_closure_pair] at h1 h2 h3
    obtain ⟨a1, a2, ea⟩ := h1
    obtain ⟨b1, b2, eb⟩ := h2
    obtain ⟨u1, u2, eu⟩ := h3
    simp only [zsmul_eq_mul] at ea eb eu
    have ra := red a a1 a2 (by linear_combination (-1 / 2 : ℂ) * ea)
    have rb := red b b1 b2 (by linear_combination (-1 / 2 : ℂ) * eb)
    have rab := red (a - b) (a1 - b1) (a2 - b2)
      (by push_cast; linear_combination (-1 / 2 : ℂ) * ea + (1 / 2 : ℂ) * eb)
    have r0 := red u u1 u2 (by linear_combination (-1 / 2 : ℂ) * eu)
    have r1 := red (u - a) (u1 - a1) (u2 - a2)
      (by push_cast; linear_combination (-1 / 2 : ℂ) * eu + (1 / 2 : ℂ) * ea)
    have r2 := red (u - b) (u1 - b1) (u2 - b2)
      (by push_cast; linear_combination (-1 / 2 : ℂ) * eu + (1 / 2 : ℂ) * eb)
    have r3 := red (u - a - b) (u1 - a1 - b1) (u2 - a2 - b2)
      (by push_cast; linear_combination (-1 / 2 : ℂ) * eu + (1 / 2 : ℂ) * ea + (1 / 2 : ℂ) * eb)
    have na : ¬ (a1 % 2 = 0 ∧ a2 % 2 = 0) := fun h => ha (ra h.1 h.2)
    have nb : ¬ (b1 % 2 = 0 ∧ b2 % 2 = 0) := fun h => hb (rb h.1 h.2)
    have nab : ¬ ((a1 - b1) % 2 = 0 ∧ (a2 - b2) % 2 = 0) := fun h => hab (rab h.1 h.2)
    have : (u1 % 2 = 0 ∧ u2 % 2 = 0) ∨ ((u1 - a1) % 2 = 0 ∧ (u2 - a2) % 2 = 0) ∨
        ((u1 - b1) % 2 = 0 ∧ (u2 - b2) % 2 = 0) ∨
        ((u1 - a1 - b1) % 2 = 0 ∧ (u2 - a2 - b2) % 2 = 0) := by omega
    rcases this with h | h | h | h
    · exact Or.inl (r0 h.1 h.2)
    · exact Or.inr (Or.inl (r1 h.1 h.2))
    · exact Or.inr (Or.inr (Or.inl (r2 h.1 h.2)))
    · exact Or.inr (Or.inr (Or.inr (r3 h.1 h.2)))
  have hkt := hk t h2
  have hab : w * t - (1 - w) * t ∉ Λ := fun h => ha (by
    have := Λ.add_mem (Λ.add_mem (hs _ h) hkt) hkt
    convert this using 1; ring)
  rcases four (w * t) ((1 - w) * t) t' (by have := hs _ h2; convert this using 1; ring)
    (by have := hs' _ h2; convert this using 1; ring) h2' ha hb hab with h | h | h | h
  · exact absurd (hs _ h) ha'
  · exact absurd (by have := Λ.add_mem (hs' _ h) hkt; convert this using 1; ring) hb'
  · exact absurd (by have := Λ.add_mem (hs _ h) hkt; convert this using 1; ring) ha'
  · have := Λ.neg_mem h; convert this using 1; ring

/- English proof (translation)
Unfold `area`. Use `congr 1`. Use extensionality with `a`. Simplify using `only [Set.mem_setOf_eq]`. Use `and_congr_right fun _ => ⟨?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨_, ⟨w₁, h₁, rfl⟩, _, ⟨w₂, h₂, rfl⟩, rfl⟩`. Use `⟨w₁, h₁, w₂, h₂, ?_⟩` and prove the remaining obligations. Rewrite using `[← abs_neg]`. Use `congr 1`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨w₁, h₁, w₂, h₂, rfl⟩`. Use `⟨_, ⟨w₁, h₁, rfl⟩, _, ⟨w₂, h₂, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← abs_neg]`. Use `congr 1`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem area_conj (Λ : AddSubgroup ℂ) : area (Λ.map (starRingEnd ℂ).toAddMonoidHom) = area Λ := by
  unfold area
  congr 1
  ext a
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨_, ⟨w₁, h₁, rfl⟩, _, ⟨w₂, h₂, rfl⟩, rfl⟩
    refine ⟨w₁, h₁, w₂, h₂, ?_⟩
    rw [← abs_neg]
    congr 1
    simp
    ring
  · rintro ⟨w₁, h₁, w₂, h₂, rfl⟩
    refine ⟨_, ⟨w₁, h₁, rfl⟩, _, ⟨w₂, h₂, rfl⟩, ?_⟩
    rw [← abs_neg]
    congr 1
    simp
    ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Simplify using `using hw`. Introduce `h`. Conclude with `⟨_, h, by simp⟩`.
-/
theorem mem_conj {Λ : AddSubgroup ℂ} {z : ℂ} :
    z ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ↔ (starRingEnd ℂ) z ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨_, h, by simp⟩

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [U1, area_conj, Function.comp, map_mul, map_add, ← Complex.exp_conj, map_sub, map_div₀, map_neg, Complex.conj_ofReal, Complex.conj_conj, map_ofNat]`.
-/
theorem thetaTranslate_conjugateLattice (Λ : AddSubgroup ℂ) (t : ℂ) (G : ℂ → ℂ) :
    U1 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t) (starRingEnd ℂ ∘ G ∘ starRingEnd ℂ) =
      starRingEnd ℂ ∘ U1 Λ t G ∘ starRingEnd ℂ := by
  funext z
  simp only [U1, area_conj, Function.comp, map_mul, map_add, ← Complex.exp_conj, map_sub, map_div₀,
    map_neg, Complex.conj_ofReal, Complex.conj_conj, map_ofNat]

/- English proof (translation)
Take `⟨w₁, w₂, hi, rfl⟩` from `h`. Use `⟨starRingEnd ℂ w₁, starRingEnd ℂ w₂, ?_, ?_⟩` and prove the remaining obligations. Use `hi.map' Complex.conjLIE.toLinearEquiv.toLinearMap (LinearEquiv.ker _)` as an intermediate fact. Establish `e : ![starRingEnd ℂ w₁, starRingEnd ℂ w₂] = Complex.conjLIE.toLinearEquiv.toLinearMap ∘ ![w₁, w₂]`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `fin_cases i <;> simp`. Rewrite using `[e]`. Conclude with `this`. Rewrite using `[AddMonoidHom.map_closure, Set.image_pair]`. Both sides reduce to the same expression.
-/
theorem IsLat.conj {Λ : AddSubgroup ℂ} (h : IsLat Λ) : IsLat (Λ.map (starRingEnd ℂ).toAddMonoidHom) := by
  obtain ⟨w₁, w₂, hi, rfl⟩ := h
  refine ⟨starRingEnd ℂ w₁, starRingEnd ℂ w₂, ?_, ?_⟩
  · have := hi.map' Complex.conjLIE.toLinearEquiv.toLinearMap (LinearEquiv.ker _)
    have e : ![starRingEnd ℂ w₁, starRingEnd ℂ w₂] =
        Complex.conjLIE.toLinearEquiv.toLinearMap ∘ ![w₁, w₂] := by
      funext i
      fin_cases i <;> simp
    rw [e]
    exact this
  · rw [AddMonoidHom.map_closure, Set.image_pair]
    rfl

/- English proof (translation)
Use extensionality with `z`. Rewrite using `[mem_conj, mem_conj, Complex.conj_conj]`.
-/
theorem conj_conj_lat (Λ : AddSubgroup ℂ) :
    (Λ.map (starRingEnd ℂ).toAddMonoidHom).map (starRingEnd ℂ).toAddMonoidHom = Λ := by
  ext z
  rw [mem_conj, mem_conj, Complex.conj_conj]

/- English proof (translation)
Take `⟨⟨hd, h1, -, hU⟩, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ h`. Establish `huniq` using `(GlobalTheory.OddTheta.sgStar_laws _ h.conj).2.2.1 (starRingEnd ℂ ∘ sgStar Λ ∘ starRingEnd ℂ) (fun z => differentiableAt_conj_conj_iff.mpr (hd _)) (by`. Introduce and unpack `_ ⟨ω, hω, rfl⟩ z`. Establish `e : (starRingEnd ℂ).toAddMonoidHom ω = starRingEnd ℂ ω` using `rfl`. Rewrite using `[e, thetaTranslate_conjugateLattice, mem_conj]`.

Simplify using `only [Function.comp, hU ω hω, map_mul, map_div₀, Complex.conj_conj, map_ofNat]`. Apply the tactic sequence `split_ifs <;> simp)`. Use function extensionality and compare the values at `z`. Rewrite using `[huniq z, deriv_conj_conj]`. Simplify using `[h1]`.
-/
theorem sgStar_conj {Λ : AddSubgroup ℂ} (h : IsLat Λ) :
    sgStar (Λ.map (starRingEnd ℂ).toAddMonoidHom) = starRingEnd ℂ ∘ sgStar Λ ∘ starRingEnd ℂ := by
  obtain ⟨⟨hd, h1, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ h
  have huniq := (GlobalTheory.OddTheta.sgStar_laws _ h.conj).2.2.1 (starRingEnd ℂ ∘ sgStar Λ ∘ starRingEnd ℂ)
    (fun z => differentiableAt_conj_conj_iff.mpr (hd _)) (by
      rintro _ ⟨ω, hω, rfl⟩ z
      have e : (starRingEnd ℂ).toAddMonoidHom ω = starRingEnd ℂ ω := rfl
      rw [e, thetaTranslate_conjugateLattice, mem_conj]
      simp only [Function.comp, hU ω hω, map_mul, map_div₀, Complex.conj_conj, map_ofNat]
      split_ifs <;> simp)
  funext z
  rw [huniq z, deriv_conj_conj]
  simp [h1]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [GL3Theta.th0]`. Rewrite using `[sgStar_conj h, thetaTranslate_conjugateLattice]`. Simplify using `[GL3Theta.th0]`.
-/
theorem evenTheta_conjugateLattice {Λ : AddSubgroup ℂ} (h : IsLat Λ) (t : ℂ) :
    GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ t) =
      starRingEnd ℂ ∘ GL3Theta.th0 Λ t ∘ starRingEnd ℂ := by
  funext z
  simp only [GL3Theta.th0]
  rw [sgStar_conj h, thetaTranslate_conjugateLattice]
  simp [GL3Theta.th0]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_conj_conj]`.
-/
theorem iteratedDeriv_conj_conj (n : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv n (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) =
      starRingEnd ℂ ∘ iteratedDeriv n f ∘ starRingEnd ℂ := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_conj_conj]

/- English proof (translation)
Simplify using `[coef1, iteratedDeriv_conj_conj]`.
-/
theorem taylorCoeff_complexConj_conjugate (f : ℂ → ℂ) (n : ℕ) :
    coef1 (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) n = starRingEnd ℂ (coef1 f n) := by
  simp [coef1, iteratedDeriv_conj_conj]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> rw [mem_conj]`. Simplify `h1` using `[map_ofNat]`. Simplify `h3` using `[map_ofNat, sub_eq_add_neg]`. Simplify `h2` using `[map_ofNat, sub_eq_add_neg]`.
-/
theorem twoTorsionCMPoint_complexConj {D : D7} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.IsTwoTorsionPointUnkilled D Λ t) :
    GL3Theta.IsTwoTorsionPointUnkilled D (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ t) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> rw [mem_conj]
  · simpa [map_ofNat] using h1
  · simpa [map_ofNat, sub_eq_add_neg] using h3
  · simpa [map_ofNat, sub_eq_add_neg] using h2

/- English proof (translation)
Establish `hc : Set.Countable ((M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ) : Set ℂ)` using `(Algebraic.countable ℚ ℂ).mono fun x hx => mem_algebraicClosure_iff.1 hx.2`. Use `haveI : Countable (M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ) := hc.to_subtype`. Take `⟨σ, hσ⟩` from `GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := (M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ)) (M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ).val.toRingHom (ρ.comp (IntermediateField.inclusion inf_le_left)).toRingHom`. Use `⟨σ.toRingHom, fun x h1 h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[cj_of_mem _ _ h1]`.

Conclude with `(hσ ⟨x, h1, h2⟩).symm`.
-/
theorem exists_ext (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ σ : ℂ →+* ℂ, ∀ x, x ∈ M → x ∈ TaylorLogMetric.Qbar → cj M ρ x = σ x := by
  have hc : Set.Countable ((M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ) : Set ℂ) :=
    (Algebraic.countable ℚ ℂ).mono fun x hx => mem_algebraicClosure_iff.1 hx.2
  haveI : Countable (M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ) := hc.to_subtype
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq
    (K := (M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ)) (M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ).val.toRingHom
    (ρ.comp (IntermediateField.inclusion inf_le_left)).toRingHom
  refine ⟨σ.toRingHom, fun x h1 h2 => ?_⟩
  rw [cj_of_mem _ _ h1]
  exact (hσ ⟨x, h1, h2⟩).symm

/- English proof (translation)
The claim follows from `(GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).1`.
-/
theorem isLat_lamOf {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) : IsLat (lamOf D cc δ) :=
  (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).1

/- English proof (translation)
Take `⟨⟨-, hg2, hg3⟩, htor⟩` from `(GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.InducedType.induced_type D).1).2 cc δ h`. Take `⟨m, hm, hmx⟩` from `hx`. Take `⟨y, hy⟩` from `GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := TaylorLogMetric.Qbar) (coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n) (fun σ => by`. Establish `hσ : ∀ z ∈ TaylorLogMetric.Qbar, cj ⊤ (topHom (σ : ℂ →+* ℂ)) z = z` using `fun z hz => by`. Rewrite using `[cj_top]`.

Conclude with `σ.commutes ⟨z, hz⟩`. Establish `hK : FixK D ⊤ (topHom (σ : ℂ →+* ℂ))` using `fun a => ⟨IntermediateField.mem_top, hσ _ (by`. Rewrite using `[mem_algebraicClosure_iff]`. Conclude with `(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (a : D.host.E)).algHom D.host.φ₀.toRatAlgHom)⟩`. Establish `hL` using `lamConj_eq_self (isLat_lamOf h) (hσ _ hg2) (hσ _ hg3)`.

Establish `hm0 : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hg` using `GlobalTheory.T.galois_conj_taylor_thetaTranslate D cc δ h ⊤ _ hK IntermediateField.mem_top IntermediateField.mem_top x x (2 * m) (by omega) (by convert hmx using 1; push_cast; ring) (by`. Unfold `Adp1 StarPt`. Rewrite using `[hL]`. Distinguish the cases in `hin : x / ((2 * (2 * m) : ℕ) : ℂ) ∈ lamOf D cc δ`.

Conclude with `Or.inl ⟨hin, hin⟩`. Take `⟨h1, h2⟩` from `htor _ ⟨m * (2 * (2 * m)), by positivity, by`. Use `hmx using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Use the proof step `field_simp⟩ hin`.

Conclude with `Or.inr ⟨hin, hin, IntermediateField.mem_top, IntermediateField.mem_top, (hσ _ h1).symm, (hσ _ h2).symm⟩) (fun _ => IntermediateField.mem_top) n`. Rewrite `hg` using `[hL, cj_top]`. Conclude with `hg)`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem coef_translate_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) {x : ℂ}
    (hx : InRationalLattice (lamOf D cc δ) x) (n : ℕ) :
    coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n ∈ TaylorLogMetric.Qbar := by
  obtain ⟨⟨-, hg2, hg3⟩, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.InducedType.induced_type D).1).2 cc δ h
  obtain ⟨m, hm, hmx⟩ := hx
  obtain ⟨y, hy⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := TaylorLogMetric.Qbar)
    (coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n) (fun σ => by
      have hσ : ∀ z ∈ TaylorLogMetric.Qbar, cj ⊤ (topHom (σ : ℂ →+* ℂ)) z = z := fun z hz => by
        rw [cj_top]; exact σ.commutes ⟨z, hz⟩
      have hK : FixK D ⊤ (topHom (σ : ℂ →+* ℂ)) := fun a => ⟨IntermediateField.mem_top, hσ _ (by
        rw [mem_algebraicClosure_iff]
        exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (a : D.host.E)).algHom D.host.φ₀.toRatAlgHom)⟩
      have hL := lamConj_eq_self (isLat_lamOf h) (hσ _ hg2) (hσ _ hg3)
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      have hg := GlobalTheory.T.galois_conj_taylor_thetaTranslate D cc δ h ⊤ _ hK IntermediateField.mem_top IntermediateField.mem_top x x (2 * m)
        (by omega) (by convert hmx using 1; push_cast; ring) (by
          unfold Adp1 StarPt
          rw [hL]
          by_cases hin : x / ((2 * (2 * m) : ℕ) : ℂ) ∈ lamOf D cc δ
          · exact Or.inl ⟨hin, hin⟩
          · obtain ⟨h1, h2⟩ := htor _ ⟨m * (2 * (2 * m)), by positivity, by
              convert hmx using 1; push_cast; field_simp⟩ hin
            exact Or.inr ⟨hin, hin, IntermediateField.mem_top, IntermediateField.mem_top, (hσ _ h1).symm,
              (hσ _ h2).symm⟩) (fun _ => IntermediateField.mem_top) n
      rw [hL, cj_top] at hg
      exact hg)
  rw [← hy]
  exact y.2

/- English proof (translation)
Establish `hx : InRationalLattice (lamOf D cc δ) t` using `⟨2, by norm_num, by exact_mod_cast ht.1⟩`. Rewrite using `[taylorCoeff_evenTheta_eq_normalised_translate]`. Conclude with `div_mem (coef_translate_mem h hx n) (coef_translate_mem h hx 0)`.
-/
theorem taylorCoeff_evenTheta_cmCurve_algebraic {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) {t : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) (n : ℕ) : coef1 (GL3Theta.th0 (lamOf D cc δ) t) n ∈ TaylorLogMetric.Qbar := by
  have hx : InRationalLattice (lamOf D cc δ) t := ⟨2, by norm_num, by exact_mod_cast ht.1⟩
  rw [taylorCoeff_evenTheta_eq_normalised_translate]
  exact div_mem (coef_translate_mem h hx n) (coef_translate_mem h hx 0)

/- English proof (translation)
Establish `hd16 : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`. Take `⟨m, hm⟩ : ∃ m : ℕ, D.host.d + 1 = 8 * m` from `⟨(D.host.d + 1) / 8, by omega⟩`. Establish `hm' : (D.host.d : ℂ) + 1 = 8 * (m : ℂ)` using `by exact_mod_cast hm`. Establish `hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = D.host.d`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`.

Simplify using the standard rewrite rules. Use `⟨m, ?_⟩` and prove the remaining obligations. Unfold `w0`. Use `push_cast`. Take the linear combination `(1 / 4 : ℂ) * hm' + (1 / 4 : ℂ) * hs - (1 / 4 : ℂ) * ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq`.
-/
theorem weylMatrix_mul_apply (D : D7) : ∃ k : ℤ, w0 D * (1 - w0 D) = 2 * k := by
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by omega⟩
  have hm' : (D.host.d : ℂ) + 1 = 8 * (m : ℂ) := by exact_mod_cast hm
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = D.host.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  refine ⟨m, ?_⟩
  unfold w0
  push_cast
  linear_combination (1 / 4 : ℂ) * hm' + (1 / 4 : ℂ) * hs -
    (1 / 4 : ℂ) * ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq

/- English proof (translation)
Establish `: 1 - w0 D = (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2` using `by unfold w0; ring`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem twoTorsionCMPoint_iff (D : D7) (Λ : AddSubgroup ℂ) (t : ℂ) :
    GL3Theta.IsTwoTorsionPointUnkilled D Λ t ↔ 2 * t ∈ Λ ∧ w0 D * t ∉ Λ ∧ (1 - w0 D) * t ∉ Λ := by
  have : 1 - w0 D = (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := by unfold w0; ring
  rw [this]
  rfl

/- English proof (translation)
Take `⟨hex, -, -, hadd, hmul, hord, -⟩` from `GlobalTheory.T.galStar_complexMultiplication_points D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top`. Take `⟨cc', δ', h', -, hL⟩` from `GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos`. Rewrite `ht`, `ht'` using `[twoTorsionCMPoint_iff]`. Take `⟨u, hu⟩` from `hex (t / 8) ⟨16, by norm_num, by convert ht.1 using 1; push_cast; ring⟩ (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)`. Apply the tactic sequence `have hg := GlobalTheory.T.galois_conj_taylor_thetaTranslate D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top t (8 * u) 4 (by norm_num) (by convert ht.1 using 1; push_cast; ring) (by unfold Adp1; convert hu using 1 <;> push_cast <;> ring) (fun _ => IntermediateF …`.

Establish `h2` using `hadd _ _ _ _ hu hu`. Establish `h4` using `hadd _ _ _ _ h2 h2`. Establish `h8 : StarPt ⊤ ρ (lamOf D cc δ) t (8 * u)`. Apply the tactic sequence `convert hadd _ _ _ _ h4 h4 using 1 <;> ring`. Take `⟨a, ha⟩` from `exists_integer_map_eq_w0 D`.

Establish `ha' : D.host.φ₀ ((((1 - a : 𝓞 D.host.K) : D.host.K) : D.host.E)) = 1 - w0 D`. Rewrite using `[← ha]`. Express the relevant statement in the definitionally equal form `D.host.φ₀ (algebraMap D.host.K D.host.E (algebraMap (𝓞 D.host.K) D.host.K (1 - a))) = _`. Rewrite using `[map_sub, map_sub, map_sub, map_one, map_one, map_one]`. Both sides reduce to the same expression.

Establish `e2` using `(hord 2 _ _ h8).1 (by exact_mod_cast ht.1)`. Establish `ea` using `(hord 1 _ _ (hmul a _ _ h8)).2`. Establish `eb` using `(hord 1 _ _ (hmul (1 - a) _ _ h8)).2`. Rewrite `ea` using `[ha]`. Rewrite `eb` using `[ha']`.

Simplify using `only [Nat.cast_one, one_mul, Nat.cast_ofNat] at e2 ea eb`. Take `⟨k, hk⟩` from `weylMatrix_mul_apply D`. Establish `hlat : IsLat (lamConj ⊤ ρ (lamOf D cc δ))` using `hL ▸ isLat_lamOf h'`. Establish `hdiff : t' - 8 * u ∈ lamConj ⊤ ρ (lamOf D cc δ)` using `two_torsion_unique hlat (w0 D) k hk ht'.1 ht'.2.1 ht'.2.2 e2 (fun hh => ht.2.1 (ea hh)) (fun hh => ht.2.2 (eb hh)) (by`. Rewrite using `[hL, ← ha]`.

Conclude with `(GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc' δ' h').2.2.2.2 a)`. Establish `hth` using `evenTheta_add_lattice_mem hlat (8 * u) hdiff`. Rewrite `hth` using `[add_sub_cancel]`. Rewrite using `[hth, taylorCoeff_evenTheta_eq_normalised_translate, taylorCoeff_evenTheta_eq_normalised_translate, cj_top_div, hg, hg]`.
-/
theorem embeddingConj_evenTheta_coeff_of_fixes_field {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') (n : ℕ) :
    cj ⊤ ρ (coef1 (GL3Theta.th0 (lamOf D cc δ) t) n) = coef1 (GL3Theta.th0 (lamConj ⊤ ρ (lamOf D cc δ)) t') n := by
  obtain ⟨hex, -, -, hadd, hmul, hord, -⟩ :=
    GlobalTheory.T.galStar_complexMultiplication_points D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨cc', δ', h', -, hL⟩ :=
    GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos
  rw [twoTorsionCMPoint_iff] at ht ht'
  obtain ⟨u, hu⟩ := hex (t / 8) ⟨16, by norm_num, by convert ht.1 using 1; push_cast; ring⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  have hg := GlobalTheory.T.galois_conj_taylor_thetaTranslate D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top t (8 * u) 4
    (by norm_num) (by convert ht.1 using 1; push_cast; ring)
    (by unfold Adp1; convert hu using 1 <;> push_cast <;> ring) (fun _ => IntermediateField.mem_top)
  have h2 := hadd _ _ _ _ hu hu
  have h4 := hadd _ _ _ _ h2 h2
  have h8 : StarPt ⊤ ρ (lamOf D cc δ) t (8 * u) := by
    convert hadd _ _ _ _ h4 h4 using 1 <;> ring
  obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
  have ha' : D.host.φ₀ ((((1 - a : 𝓞 D.host.K) : D.host.K) : D.host.E)) = 1 - w0 D := by
    rw [← ha]
    change D.host.φ₀ (algebraMap D.host.K D.host.E (algebraMap (𝓞 D.host.K) D.host.K (1 - a))) = _
    rw [map_sub, map_sub, map_sub, map_one, map_one, map_one]
    rfl
  have e2 := (hord 2 _ _ h8).1 (by exact_mod_cast ht.1)
  have ea := (hord 1 _ _ (hmul a _ _ h8)).2
  have eb := (hord 1 _ _ (hmul (1 - a) _ _ h8)).2
  rw [ha] at ea
  rw [ha'] at eb
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at e2 ea eb
  obtain ⟨k, hk⟩ := weylMatrix_mul_apply D
  have hlat : IsLat (lamConj ⊤ ρ (lamOf D cc δ)) := hL ▸ isLat_lamOf h'
  have hdiff : t' - 8 * u ∈ lamConj ⊤ ρ (lamOf D cc δ) :=
    two_torsion_unique hlat (w0 D) k hk ht'.1 ht'.2.1 ht'.2.2 e2 (fun hh => ht.2.1 (ea hh))
      (fun hh => ht.2.2 (eb hh)) (by
        rw [hL, ← ha]
        exact (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc' δ' h').2.2.2.2 a)
  have hth := evenTheta_add_lattice_mem hlat (8 * u) hdiff
  rw [add_sub_cancel] at hth
  rw [hth, taylorCoeff_evenTheta_eq_normalised_translate, taylorCoeff_evenTheta_eq_normalised_translate, cj_top_div, hg, hg]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cj_rhoBar (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) :
    cj M (rhoBar M ρ) x = starRingEnd ℂ (cj M ρ x) := rfl

/- English proof (translation)
Take `⟨hK, hT, -⟩` from `GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ h ⊤ ρ ⟨fun _ _ => IntermediateField.mem_top, IntermediateField.mem_top, IntermediateField.mem_top⟩`. Break down `hK with hK | hK` into its components or cases. Conclude with `embeddingConj_evenTheta_coeff_of_fixes_field h ρ hK ht ht' n`. Establish `hL : lamConj ⊤ (rhoBar ⊤ ρ) (lamOf D cc δ) = (lamConj ⊤ ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom` using `congrArg Tor.abelian₂ hT`. Take `⟨cc', δ', h', -, hL'⟩` from `GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ _ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos`.

Establish `hlat : IsLat (lamConj ⊤ ρ (lamOf D cc δ))`. Rewrite using `[← conj_conj_lat (lamConj ⊤ ρ (lamOf D cc δ)), ← hL, hL']`. Conclude with `(isLat_lamOf h').conj`. Establish `key` using `embeddingConj_evenTheta_coeff_of_fixes_field h _ hK (t' := starRingEnd ℂ t') ht (hL ▸ twoTorsionCMPoint_complexConj ht') n`. Rewrite `key` using `[hL, evenTheta_conjugateLattice hlat, taylorCoeff_complexConj_conjugate, cj_rhoBar]`.

Conclude with `(starRingEnd ℂ).injective key`.
-/
theorem embeddingConj_evenTheta_coeff_top {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') (n : ℕ) :
    cj ⊤ ρ (coef1 (GL3Theta.th0 (lamOf D cc δ) t) n) = coef1 (GL3Theta.th0 (lamConj ⊤ ρ (lamOf D cc δ)) t') n := by
  obtain ⟨hK, hT, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ h ⊤ ρ
    ⟨fun _ _ => IntermediateField.mem_top, IntermediateField.mem_top, IntermediateField.mem_top⟩
  rcases hK with hK | hK
  · exact embeddingConj_evenTheta_coeff_of_fixes_field h ρ hK ht ht' n
  · have hL : lamConj ⊤ (rhoBar ⊤ ρ) (lamOf D cc δ) =
        (lamConj ⊤ ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    obtain ⟨cc', δ', h', -, hL'⟩ :=
      GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ _ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos
    have hlat : IsLat (lamConj ⊤ ρ (lamOf D cc δ)) := by
      rw [← conj_conj_lat (lamConj ⊤ ρ (lamOf D cc δ)), ← hL, hL']
      exact (isLat_lamOf h').conj
    have key := embeddingConj_evenTheta_coeff_of_fixes_field h _ hK (t' := starRingEnd ℂ t') ht (hL ▸ twoTorsionCMPoint_complexConj ht') n
    rw [hL, evenTheta_conjugateLattice hlat, taylorCoeff_complexConj_conjugate, cj_rhoBar] at key
    exact (starRingEnd ℂ).injective key

/- English proof (translation)
Introduce `D cc δ h`. Use `⟨fun x hx n => coef_translate_mem h hx n, fun t ht n => taylorCoeff_evenTheta_cmCurve_algebraic h ht n, ?_⟩` and prove the remaining obligations. Introduce `M ρ h2 h3 t t' ht ht' hM n`. Take `⟨⟨-, hg2, hg3⟩, -⟩` from `(GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.InducedType.induced_type D).1).2 cc δ h`. Take `⟨σ, hσ⟩` from `exists_ext M ρ`.

Establish `hL : lamConj M ρ (lamOf D cc δ) = lamConj ⊤ (topHom σ) (lamOf D cc δ)` using `lamConj_congr (by rw [cj_top]; exact hσ _ h2 hg2) (by rw [cj_top]; exact hσ _ h3 hg3)`. Rewrite `ht'`, the goal using `[hL]`. Rewrite using `[hσ _ (hM n) (taylorCoeff_evenTheta_cmCurve_algebraic h ht n), ← cj_top]`. Conclude with `embeddingConj_evenTheta_coeff_top h _ ht ht' n`.
-/
theorem cmTheta_taylorCoeff_algebraic_and_conjugate : ∀ D : D7, use1 D := by
  intro D cc δ h
  refine ⟨fun x hx n => coef_translate_mem h hx n, fun t ht n => taylorCoeff_evenTheta_cmCurve_algebraic h ht n, ?_⟩
  intro M ρ h2 h3 t t' ht ht' hM n
  obtain ⟨⟨-, hg2, hg3⟩, -⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.InducedType.induced_type D).1).2 cc δ h
  obtain ⟨σ, hσ⟩ := exists_ext M ρ
  have hL : lamConj M ρ (lamOf D cc δ) = lamConj ⊤ (topHom σ) (lamOf D cc δ) :=
    lamConj_congr (by rw [cj_top]; exact hσ _ h2 hg2) (by rw [cj_top]; exact hσ _ h3 hg3)
  rw [hL] at ht' ⊢
  rw [hσ _ (hM n) (taylorCoeff_evenTheta_cmCurve_algebraic h ht n), ← cj_top]
  exact embeddingConj_evenTheta_coeff_top h _ ht ht' n

end GlobalTheory.ThetaConj
