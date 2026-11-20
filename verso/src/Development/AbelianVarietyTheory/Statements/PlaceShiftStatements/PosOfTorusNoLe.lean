import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SingleMemIntVec
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo

noncomputable section

namespace GlobalTheory.UCls.Model

open NumberField Matrix GlobalTheory.AdLat ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst
open GlobalTheory.Up.Definite

section Field

/- English proof (translation)
Establish `hi : IsIntegral ℤ x` using `⟨Polynomial.X ^ 2 + Polynomial.C (n : ℤ), by monicity!, by simp [Polynomial.eval₂_add, hs]⟩`. Establish `hw : IsIntegral ℤ ((1 + x) / 2)` using `by set c : E := (1 + x) / 2`. Establish `hc : c ^ 2 - c + (m : E) = 0`. Establish `e : (n : E) + 1 = 4 * (m : E)` using `by exact_mod_cast hm`. Simplify using `only [c]`.

Take the linear combination `(1 / 4 : E) * hs - (1 / 4 : E) * e`. Conclude with `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by`. Simplify using `[Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩`. Take `⟨y, hy⟩ : ∃ y : 𝓞 E, algebraMap _ E y = x` from `⟨⟨x, hi⟩, rfl⟩`. Take `⟨w, hw0⟩ : ∃ w : 𝓞 E, algebraMap _ E w = (1 + x) / 2` from `⟨⟨_, hw⟩, rfl⟩`.

Use `⟨y, w, ?_, ?_⟩` and prove the remaining obligations. Apply `IsFractionRing.injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[map_pow, map_neg, map_natCast, hy]`. Conclude with `hs`. Apply `IsFractionRing.injective (𝓞 E) E` to reduce the goal to its premises.

Rewrite using `[map_mul, map_add, map_one, map_ofNat, hy, hw0]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_half {E : Type} [Field E] [NumberField E] {x : E} {n m : ℕ} (hm : n + 1 = 4 * m) (hs : x ^ 2 = -(n : E)) :
    ∃ y w : 𝓞 E, y ^ 2 = -(n : 𝓞 E) ∧ 2 * w = 1 + y := by
  have hi : IsIntegral ℤ x :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (n : ℤ), by monicity!, by simp [Polynomial.eval₂_add, hs]⟩
  have hw : IsIntegral ℤ ((1 + x) / 2) := by
    set c : E := (1 + x) / 2
    have hc : c ^ 2 - c + (m : E) = 0 := by
      have e : (n : E) + 1 = 4 * (m : E) := by exact_mod_cast hm
      simp only [c]
      linear_combination (1 / 4 : E) * hs - (1 / 4 : E) * e
    exact ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, algebraMap _ E y = x := ⟨⟨x, hi⟩, rfl⟩
  obtain ⟨w, hw0⟩ : ∃ w : 𝓞 E, algebraMap _ E w = (1 + x) / 2 := ⟨⟨_, hw⟩, rfl⟩
  refine ⟨y, w, ?_, ?_⟩
  · apply IsFractionRing.injective (𝓞 E) E
    rw [map_pow, map_neg, map_natCast, hy]
    exact hs
  · apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, map_add, map_one, map_ofNat, hy, hw0]
    field_simp

/- English proof (translation)
Establish `hh : Formalism.FrobeniusOrbits.HostHyp 11 7` using `⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩`. Take `⟨L, _, _, ζ, a, b, h⟩` from `Formalism.TwoAdicCyclotomicDecomposition.layerExists (0 + 2) 11 7`. Use `Formalism.FrobeniusOrbits.isCMField_hostE hh.toHypOdd h` as an intermediate fact. Use `⟨Formalism.FrobeniusOrbits.hostE ζ a b, inferInstance, inferInstance, inferInstance, ?_, fun u hu => ?_⟩` and prove the remaining obligations. Establish `ha : Formalism.FrobeniusOrbits.aE ζ a b ^ 2 = -((11 : ℕ) : Formalism.FrobeniusOrbits.hostE ζ a b)`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `h.2.1`. Establish `hb : Formalism.FrobeniusOrbits.bE ζ a b ^ 2 = -((7 : ℕ) : Formalism.FrobeniusOrbits.hostE ζ a b)`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `h.2.2.1`.

Take `⟨y₁, w₁, h1, h2⟩` from `exists_half (m := 3) (by norm_num) ha`. Take `⟨y₂, w₂, h3, h4⟩` from `exists_half (m := 2) (by norm_num) hb`. Conclude with `GlobalTheory.HostModel.unramified_of_sqrt (by norm_num : Nat.Coprime 11 7) h1 h3 h2 h4`. Conclude with `Formalism.FrobeniusOrbits.hostMu 0 11 7 hh (by norm_num) L ζ a b h u (isOfFinOrder_iff_pow_eq_one.1 hu)`.
-/
theorem exists_field : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E),
    Unr E ∧ ∀ u : E, IsOfFinOrder u → u = 1 ∨ u = -1 := by
  have hh : Formalism.FrobeniusOrbits.HostHyp 11 7 := ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨L, _, _, ζ, a, b, h⟩ := Formalism.TwoAdicCyclotomicDecomposition.layerExists (0 + 2) 11 7
  have := Formalism.FrobeniusOrbits.isCMField_hostE hh.toHypOdd h
  refine ⟨Formalism.FrobeniusOrbits.hostE ζ a b, inferInstance, inferInstance, inferInstance, ?_, fun u hu => ?_⟩
  · have ha : Formalism.FrobeniusOrbits.aE ζ a b ^ 2 = -((11 : ℕ) : Formalism.FrobeniusOrbits.hostE ζ a b) := by
      apply Subtype.ext
      exact h.2.1
    have hb : Formalism.FrobeniusOrbits.bE ζ a b ^ 2 = -((7 : ℕ) : Formalism.FrobeniusOrbits.hostE ζ a b) := by
      apply Subtype.ext
      exact h.2.2.1
    obtain ⟨y₁, w₁, h1, h2⟩ := exists_half (m := 3) (by norm_num) ha
    obtain ⟨y₂, w₂, h3, h4⟩ := exists_half (m := 2) (by norm_num) hb
    exact GlobalTheory.HostModel.unramified_of_sqrt (by norm_num : Nat.Coprime 11 7) h1 h3 h2 h4
  · exact Formalism.FrobeniusOrbits.hostMu 0 11 7 hh (by norm_num) L ζ a b h u (isOfFinOrder_iff_pow_eq_one.1 hu)

end Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use `⟨(data E r).Gm_herm, by simp, (data E r).Λ_fg, (data E r).Λ_span, fun x => ⟨fun h => ?_, fun hx y hy => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[mem_intVec]`. Introduce `a`. Use `h _ (single_mem_intVec a)` as an intermediate fact. Rewrite `this` using `[Up.Definite.herm_one, Finset.sum_eq_single a]`.

Simplify `this` using `[cc_one]`. Introduce `b _ hb`. Simplify using `[hb, cc_zero]`. Simplify using the standard rewrite rules. Rewrite `hx`, `hy` using `[mem_intVec]`.

Rewrite using `[Up.Definite.herm_one]`. Conclude with `IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc (hy a))`.
-/
theorem selfDual_one : SelfDualLat (1 : Matrix (Fin r) (Fin r) E) (intVec E r) := by
  refine ⟨(data E r).Gm_herm, by simp, (data E r).Λ_fg, (data E r).Λ_span, fun x => ⟨fun h => ?_, fun hx y hy => ?_⟩⟩
  · rw [mem_intVec]
    intro a
    have := h _ (single_mem_intVec a)
    rw [Up.Definite.herm_one, Finset.sum_eq_single a] at this
    · simpa [cc_one] using this
    · intro b _ hb; simp [hb, cc_zero]
    · simp
  · rw [mem_intVec] at hx hy
    rw [Up.Definite.herm_one]
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc (hy a))

/- English proof (translation)
Rewrite using `[map_herm_one_self, Complex.ofReal_re]`. Take `⟨a, ha⟩` from `Function.ne_iff.1 hx`. Use `Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Establish `: τ (x a) ≠ 0` using `by simpa using ha`. Check the signs of the components of the expression.
-/
theorem pos_one (τ : E →+* ℂ) (x : Fin r → E) (hx : x ≠ 0) :
    0 < (τ (herm (1 : Matrix (Fin r) (Fin r) E) x x)).re := by
  rw [map_herm_one_self, Complex.ofReal_re]
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hx
  refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ _, ?_⟩
  have : τ (x a) ≠ 0 := by simpa using ha
  positivity

/- English proof (translation)
Establish `hh : ∀ x y : Fin 2 → E, herm (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) x y = x 0 * cc (y 1) + x 1 * cc (y 0)`. Introduce `x y`. Simplify using `[herm]`. Use `⟨⟨fun a b => ?_, by simp, (data E 2).Λ_fg, (data E 2).Λ_span, fun x => ⟨fun h => ?_, fun hx y hy => ?_⟩⟩, ![1, 0], by simp, by simp [hh, cc_zero]⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [cc_one, cc_zero]`.

Rewrite using `[mem_intVec]`. Introduce `a`. Use `fin_cases a`. Simplify `h _ (single_mem_intVec 1)` using `[hh, cc_one, cc_zero]`. Simplify `h _ (single_mem_intVec 0)` using `[hh, cc_one, cc_zero]`.

Rewrite `hx`, `hy` using `[mem_intVec]`. Rewrite using `[hh]`. Conclude with `((hx 0).mul (isIntegral_cc (hy 1))).add ((hx 1).mul (isIntegral_cc (hy 0)))`.
-/
theorem selfDual_hyp : SelfDualLat (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (intVec E 2) ∧
    ∃ z, z ≠ 0 ∧ herm (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) z z = 0 := by
  have hh : ∀ x y : Fin 2 → E, herm (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) x y = x 0 * cc (y 1) + x 1 * cc (y 0) := by
    intro x y; simp [herm]
  refine ⟨⟨fun a b => ?_, by simp, (data E 2).Λ_fg, (data E 2).Λ_span, fun x => ⟨fun h => ?_, fun hx y hy => ?_⟩⟩,
    ![1, 0], by simp, by simp [hh, cc_zero]⟩
  · fin_cases a <;> fin_cases b <;> simp [cc_one, cc_zero]
  · rw [mem_intVec]
    intro a
    fin_cases a
    · simpa [hh, cc_one, cc_zero] using h _ (single_mem_intVec 1)
    · simpa [hh, cc_one, cc_zero] using h _ (single_mem_intVec 0)
  · rw [mem_intVec] at hx hy
    rw [hh]
    exact ((hx 0).mul (isIntegral_cc (hy 1))).add ((hx 1).mul (isIntegral_cc (hy 0)))

/- English proof (translation)
Introduce and unpack `⟨-, -, -, -, h⟩`. Establish `h1` using `(mem_intVec _).1 ((h fun _ => 1 / 2).1 fun y hy => by`. Use `isIntegral_cc ((mem_intVec _).1 hy 0)` as an intermediate fact. Simplify `this) 0` using `[herm]`. Establish `h2 : IsIntegral ℤ (algebraMap ℚ E (1 / 2))` using `by simpa using h1`.

Rewrite `h2` using `[isIntegral_algebraMap_iff (algebraMap ℚ E).injective]`. Take `⟨k, hk⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral h2`. Establish `: (2 * k : ℤ) = 1`. Establish `: (2 * k : ℚ) = 1` using `by simp at hk; rw [hk]; norm_num`. Conclude with `this` after adjusting the coercions.

Use linear arithmetic over natural numbers and integers.
-/
theorem not_selfDual_two : ¬ SelfDualLat ((2 : E) • (1 : Matrix (Fin 1) (Fin 1) E)) (intVec E 1) := by
  rintro ⟨-, -, -, -, h⟩
  have h1 := (mem_intVec _).1 ((h fun _ => 1 / 2).1 fun y hy => by
    have := isIntegral_cc ((mem_intVec _).1 hy 0)
    simpa [herm] using this) 0
  have h2 : IsIntegral ℤ (algebraMap ℚ E (1 / 2)) := by simpa using h1
  rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at h2
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h2
  have : (2 * k : ℤ) = 1 := by
    have : (2 * k : ℚ) = 1 := by simp at hk; rw [hk]; norm_num
    exact_mod_cast this
  omega

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Take `⟨y, hy, he⟩` from `hc _ (single_mem_intVec b)`. Establish `hya` using `(mem_intVec _).1 hy a`. Establish `e : (γ : Matrix (Fin r) (Fin r) E) a b - (1 : Matrix (Fin r) (Fin r) E) a b = M * y a`.

Use `congrFun he a` as an intermediate fact. Simplify `this` using `[Matrix.one_apply, Pi.single_apply]`. Establish `hb : ∀ φ : E →+* ℂ, ‖φ (y a)‖ ≤ 2 / 3`. Introduce `φ`. Establish `hcol : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single b 1) = fun a => (γ : Matrix (Fin r) (Fin r) E) a b`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Establish `h1` using `congrArg φ (hγ.1 (Pi.single b 1) (Pi.single b 1))`. Rewrite `h1` using `[map_herm_one_self, map_herm_one_self, hcol]`. Establish `h2 : ∑ a, ‖φ ((Pi.single b 1 : Fin r → E) a)‖ ^ 2 = 1`.

Apply the tactic sequence `rw [Finset.sum_eq_single b] <;> simp +contextual`. Establish `h3` using `Complex.ofReal_injective h1`. Rewrite `h3` using `[h2]`. Establish `h4` using `Finset.single_le_sum (f := fun a => ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)`. Rewrite `h4` using `[h3]`.

Establish `h5 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1`. Use polynomial arithmetic with `[norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]`. Establish `h6 : ‖φ ((1 : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1`. Apply the tactic sequence `by_cases h : a = b <;> simp [Matrix.one_apply, h]`. Establish `h7` using `congrArg (fun z => ‖φ z‖) e`.

Simplify using `only [map_sub, map_mul, map_natCast, norm_mul, Complex.norm_natCast] at h7`. Establish `h8` using `norm_sub_le (φ ((γ : Matrix (Fin r) (Fin r) E) a b)) (φ ((1 : Matrix (Fin r) (Fin r) E) a b))`. Establish `h9 : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Use polynomial arithmetic with `[norm_nonneg (φ (y a))]`. Establish `h0 : y a = 0`.

Assume the negation of the conclusion as `hne`. Take `⟨n, hn, hp⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hne hya fun φ => (hb φ).trans (by norm_num)`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h1` using `congrArg (fun z => ‖φ z‖) hp`. Simplify using `only [map_pow, norm_pow, map_one, norm_one] at h1`.

Use `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1` as an intermediate fact. Combine the linear relations using `[hb φ]`. Rewrite `e` using `[h0, mul_zero, sub_eq_zero]`. Simplify using `using e`.
-/
theorem cong_trivial {M : ℕ} (hM : 3 ≤ M) (γ : GL (Fin r) E) (hγ : IsUStab 1 (intVec E r) γ)
    (hc : ∀ x ∈ intVec E r, ∃ y ∈ intVec E r, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) : γ = 1 := by
  apply Units.ext
  ext a b
  obtain ⟨y, hy, he⟩ := hc _ (single_mem_intVec b)
  have hya := (mem_intVec _).1 hy a
  have e : (γ : Matrix (Fin r) (Fin r) E) a b - (1 : Matrix (Fin r) (Fin r) E) a b = M * y a := by
    have := congrFun he a
    simpa [Matrix.one_apply, Pi.single_apply] using this
  have hb : ∀ φ : E →+* ℂ, ‖φ (y a)‖ ≤ 2 / 3 := by
    intro φ
    have hcol : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single b 1) =
        fun a => (γ : Matrix (Fin r) (Fin r) E) a b := by
      ext a; simp
    have h1 := congrArg φ (hγ.1 (Pi.single b 1) (Pi.single b 1))
    rw [map_herm_one_self, map_herm_one_self, hcol] at h1
    have h2 : ∑ a, ‖φ ((Pi.single b 1 : Fin r → E) a)‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single b] <;> simp +contextual
    have h3 := Complex.ofReal_injective h1
    rw [h2] at h3
    have h4 := Finset.single_le_sum (f := fun a => ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
    rw [h3] at h4
    have h5 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1 := by
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
    have h6 : ‖φ ((1 : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1 := by
      by_cases h : a = b <;> simp [Matrix.one_apply, h]
    have h7 := congrArg (fun z => ‖φ z‖) e
    simp only [map_sub, map_mul, map_natCast, norm_mul, Complex.norm_natCast] at h7
    have h8 := norm_sub_le (φ ((γ : Matrix (Fin r) (Fin r) E) a b)) (φ ((1 : Matrix (Fin r) (Fin r) E) a b))
    have h9 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [norm_nonneg (φ (y a))]
  have h0 : y a = 0 := by
    by_contra hne
    obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hne hya
      fun φ => (hb φ).trans (by norm_num)
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 := congrArg (fun z => ‖φ z‖) hp
    simp only [map_pow, norm_pow, map_one, norm_one] at h1
    have := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1
    linarith [hb φ]
  rw [h0, mul_zero, sub_eq_zero] at e
  simpa using e

/- English proof (translation)
Establish `ho : IsOrth (data E r) (x0F (data E r))` using `fun τ => ((data E r).signature τ).choose_spec.2`. Take `⟨FF, hF⟩` from `fundSet_holds r (data E r) _ ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r _)`. Use `⟨data E r, _, FF, (isKM_one _ _ ∅ 1).1, rfl, (GlobalTheory.Member.latOf_one_eq _ _ _ _ (data E r).Λ_fg (data E r).Λ_span).symm, fun γ => ⟨fun h => ?_, fun h => ?_⟩, ho, hF⟩` and prove the remaining obligations. Take `rfl` from `Subgroup.mem_bot.1 h`. Conclude with `⟨by simp [IsUStab], fun x _ => ⟨0, zero_mem _, by simp⟩⟩`.

Conclude with `Subgroup.mem_bot.2 (cong_trivial hM γ h.1 h.2)`.
-/
theorem component_hyp {M : ℕ} (hM : 3 ≤ M) :
    ∃ (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))),
      IsUA (IsCMField.complexConj E) (1 : Matrix (Fin r) (Fin r) E) 1 ∧ X.Gm = 1 ∧
      (X.Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) 1 (intVec E r : Set (Fin r → E)) ∧
      (∀ γ, γ ∈ X.Γ ↔ IsUStab 1 X.Λ γ ∧
        ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧
      IsOrth X x0 ∧ IsFundSet X x0 FF := by
  have ho : IsOrth (data E r) (x0F (data E r)) := fun τ => ((data E r).signature τ).choose_spec.2
  obtain ⟨FF, hF⟩ := fundSet_holds r (data E r) _ ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r _)
  refine ⟨data E r, _, FF, (isKM_one _ _ ∅ 1).1, rfl,
    (GlobalTheory.Member.latOf_one_eq _ _ _ _ (data E r).Λ_fg (data E r).Λ_span).symm, fun γ => ⟨fun h => ?_, fun h => ?_⟩, ho, hF⟩
  · obtain rfl := Subgroup.mem_bot.1 h
    exact ⟨by simp [IsUStab], fun x _ => ⟨0, zero_mem _, by simp⟩⟩
  · exact Subgroup.mem_bot.2 (cong_trivial hM γ h.1 h.2)

/- English proof (translation)
Take `⟨E, _, _, _, hU, hm⟩` from `exists_field`. Take `⟨X, x0, FF, h⟩` from `component_hyp (E := E) (r := r) hM`. Conclude with `⟨E, inferInstance, inferInstance, inferInstance, _, X, x0, FF, hU, hm, selfDual_one, pos_one, hT E r M 1 _ (by omega) (by omega) hU selfDual_one, h⟩`.
-/
theorem joint_hyp (hT : TorusBound) (r M : ℕ) (hr : 2 ≤ r) (hM : 3 ≤ M) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (h : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
      (FF : Set (V (nd X))),
      Unr E ∧ (∀ u : E, IsOfFinOrder u → u = 1 ∨ u = -1) ∧ SelfDualLat (1 : Matrix (Fin r) (Fin r) E) (intVec E r) ∧
      (∀ (τ : E →+* ℂ) (x : Fin r → E), x ≠ 0 → 0 < (τ (herm (1 : Matrix (Fin r) (Fin r) E) x x)).re) ∧
      torusNo (IsCMField.complexConj E) 1 (intVec E r : Set (Fin r → E)) M ≤ h ∧
      IsUA (IsCMField.complexConj E) (1 : Matrix (Fin r) (Fin r) E) 1 ∧ X.Gm = 1 ∧
      (X.Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) 1 (intVec E r : Set (Fin r → E)) ∧
      (∀ γ, γ ∈ X.Γ ↔ IsUStab 1 X.Λ γ ∧
        ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧
      IsOrth X x0 ∧ IsFundSet X x0 FF := by
  obtain ⟨E, _, _, _, hU, hm⟩ := exists_field
  obtain ⟨X, x0, FF, h⟩ := component_hyp (E := E) (r := r) hM
  exact ⟨E, inferInstance, inferInstance, inferInstance, _, X, x0, FF, hU, hm, selfDual_one, pos_one,
    hT E r M 1 _ (by omega) (by omega) hU selfDual_one, h⟩

/- English proof (translation)
Break down `Nat.eq_zero_or_pos h with rfl | h0` into its components or cases. It suffices to derive a contradiction. Establish `: Nonempty (Quot fun a b : {t // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1)` using `⟨Quot.mk _ ⟨1, by simp [IsTA]⟩⟩`. Establish `h1` using `ENat.card_pos (α := Quot fun a b : {t // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1)`. Conclude with `absurd (lt_of_lt_of_le h1 hh) (by simp)`.

Conclude with `h0`.
-/
theorem pos_of_torusNo_le (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M h : ℕ)
    (hh : torusNo (IsCMField.complexConj E) G L M ≤ h) : 0 < h := by
  rcases Nat.eq_zero_or_pos h with rfl | h0
  · exfalso
    have : Nonempty (Quot fun a b : {t // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G L M a.1 b.1) := ⟨Quot.mk _ ⟨1, by simp [IsTA]⟩⟩
    have h1 := ENat.card_pos (α := Quot fun a b : {t // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G L M a.1 b.1)
    exact absurd (lt_of_lt_of_le h1 hh) (by simp)
  · exact h0

end GlobalTheory.UCls.Model
