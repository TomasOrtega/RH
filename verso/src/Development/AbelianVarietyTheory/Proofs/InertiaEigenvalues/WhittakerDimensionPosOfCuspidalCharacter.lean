import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.Generic

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `[br, entN, i.isLt, j.isLt]`.
-/
theorem br_zero_self {d : ℕ} (M : Mt g d) : br 0 d M = M := by
  funext i j
  simp [br, entN, i.isLt, j.isLt]

/- English proof (translation)
Unfold `res`. Establish `hI : ∀ x : Gn g d, InPar 0 (x : Mt g d)` using `fun x i j hj _ => absurd hj (Nat.not_lt_zero _)`. Establish `hT : ∀ x : Gn g d, tl 0 (x : Mt g d) = ((1 : Gn g 0) : Mt g 0)` using `fun x => by`. Use function extensionality and compare the values at `i`. Conclude with `i.elim0`.

Simplify using `only [hI, hT, br_zero_self, true_and, zero_mul, pow_zero, inv_one, one_mul, Units.val_inj]`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.
-/
theorem res_zero_self {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g d) : res 0 d χ 1 h = χ h := by
  unfold res
  have hI : ∀ x : Gn g d, InPar 0 (x : Mt g d) := fun x i j hj _ => absurd hj (Nat.not_lt_zero _)
  have hT : ∀ x : Gn g d, tl 0 (x : Mt g d) = ((1 : Gn g 0) : Mt g 0) := fun x => by
    funext i; exact i.elim0
  simp only [hI, hT, br_zero_self, true_and, zero_mul, pow_zero, inv_one, one_mul, Units.val_inj]
  rw [Finset.sum_ite_eq']
  simp

/- English proof (translation)
Simplify using `[wh, tr]`.
-/
theorem wh_zero_fun (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : wh ψ (fun _ : Gn g n => (0 : ℂ)) = 0 := by
  simp [wh, tr]

/- English proof (translation)
Take `⟨V, _, hV⟩` from `h`. Introduce `x y`. Rewrite using `[← hV, ← hV]`. Conclude with `FDRep.char_conj V x y`.
-/
theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, _, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

end GlobalTheory.GLq.Generic

/- English proof (translation)
Introduce `g _ ψ hψ d χ hc`. Establish `hc'` using `hc`. Take `⟨hd, hirr, _⟩` from `hc'`. Establish `hder` using `GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (GlobalTheory.GLq.Generic.isClass_of_isIrr hirr)`. Rewrite `hder` using `[Finset.sum_eq_single 0]`.

Use `rotate_left`. Introduce `m hm hm0`. Establish `hmd : m < d` using `Finset.mem_range.mp hm`. Establish `hz : res m (d - m) χ 1 = fun _ => 0`. Use function extensionality and compare the values at `y`.

Conclude with `GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g d m χ hc (Nat.pos_of_ne_zero hm0) hmd 1 y`. Establish `: der ψ m χ 1 = 0` using `by show wh ψ (res m (d - m) χ 1) = 0`. Rewrite using `[hz]`. Conclude with `GlobalTheory.GLq.Generic.wh_zero_fun ψ _`. Rewrite using `[this, zero_mul]`.

Introduce `h0`. Conclude with `absurd (Finset.mem_range.mpr hd) h0`. Establish `h0 : der ψ 0 χ 1 = wh ψ χ`. Express the relevant statement in the definitionally equal form `wh ψ (n := d) (res 0 d χ 1) = wh ψ χ`. Use `congr 1`.

Use function extensionality and compare the values at `h`. Conclude with `GlobalTheory.GLq.Generic.res_zero_self χ h`. Rewrite `hder` using `[h0]`. Take `⟨V, _, hV⟩` from `hirr`. Establish `hchar : IsChar χ` using `⟨V, hV⟩`.

Take `⟨d', hd'pos, hd'⟩` from `(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).2.1 ⟨V, ‹_›, hV⟩`. Take `⟨n, hn⟩` from `(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g d 0 0 ψ).1 hchar`. Establish `hwh : wh ψ χ = n` using `hn`. Use `⟨n, Nat.pos_of_ne_zero ?_, hwh⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Rewrite `hder` using `[hwh, Nat.cast_zero, zero_mul, hd']`. Conclude with `absurd hder (by exact_mod_cast hd'pos.ne')`.
-/
theorem GlobalTheory.GLq.wh_cusp_pos : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := by
  intro g _ ψ hψ d χ hc
  have hc' := hc
  obtain ⟨hd, hirr, _⟩ := hc'
  have hder := GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (GlobalTheory.GLq.Generic.isClass_of_isIrr hirr)
  rw [Finset.sum_eq_single 0] at hder
  rotate_left
  · intro m hm hm0
    have hmd : m < d := Finset.mem_range.mp hm
    have hz : res m (d - m) χ 1 = fun _ => 0 := by
      funext y
      exact GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g d m χ hc (Nat.pos_of_ne_zero hm0) hmd 1 y
    have : der ψ m χ 1 = 0 := by
      show wh ψ (res m (d - m) χ 1) = 0
      rw [hz]
      exact GlobalTheory.GLq.Generic.wh_zero_fun ψ _
    rw [this, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr hd) h0
  have h0 : der ψ 0 χ 1 = wh ψ χ := by
    change wh ψ (n := d) (res 0 d χ 1) = wh ψ χ
    congr 1
    funext h
    exact GlobalTheory.GLq.Generic.res_zero_self χ h
  rw [h0] at hder
  obtain ⟨V, _, hV⟩ := hirr
  have hchar : IsChar χ := ⟨V, hV⟩
  obtain ⟨d', hd'pos, hd'⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).2.1 ⟨V, ‹_›, hV⟩
  obtain ⟨n, hn⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g d 0 0 ψ).1 hchar
  have hwh : wh ψ χ = n := hn
  refine ⟨n, Nat.pos_of_ne_zero ?_, hwh⟩
  rintro rfl
  rw [hwh, Nat.cast_zero, zero_mul, hd'] at hder
  exact absurd hder (by exact_mod_cast hd'pos.ne')

/- English proof (translation)
The claim follows from `GlobalTheory.GLq.wh_cusp_pos`.
-/
example : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := GlobalTheory.GLq.wh_cusp_pos
