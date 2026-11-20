import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.SelfDualFirstProjAny

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Use `⟨(π : v.adicCompletion F) ^ (-n), ?_⟩` and prove the remaining obligations. Rewrite using `[map_zpow₀, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]`. Simplify using `[← WithZero.exp_zsmul]`.
-/
theorem exists_valuation_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    ∃ a : v.adicCompletion F, Valued.v a = WithZero.exp n := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F) ^ (-n), ?_⟩
  rw [map_zpow₀, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  simp [← WithZero.exp_zsmul]

/- English proof (translation)
Introduce `F _ _ v κ _ ψ hcont hnorm hne Λ c hc hself hbd η hη`. Establish `hne' : ∃ t, ψ t ≠ 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (by ext t; simpa using h t)`.

Take `⟨n, hn⟩` from `GlobalTheory.CharConductor.exists_conductor_exponent F v ψ hcont hnorm hne'`. Take `⟨a, ha⟩` from `exists_valuation_eq F v n`. Establish `ha0 : a ≠ 0`. Introduce `h`. Rewrite `ha` using `[h, map_zero]`.

Conclude with `WithZero.zero_ne_coe ha`. Set `O` to `v.adicCompletionIntegers F`. Set `ψ₀ : AddChar (Fv F v) ℂ` to `ψ.mulShift a`. Establish `hψ₀ : ∀ x, ψ₀ x = ψ (a * x)` using `fun x => rfl`. Establish `hcond : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F`.

Introduce `x`. Use `hn (a * x)` as an intermediate fact. Simplify using `only [hψ₀, mul_assoc] at this ⊢`. Rewrite using `[this, map_mul, ha, HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `e : Valued.v x = WithZero.exp (-n) * (WithZero.exp n * Valued.v x)`.

Rewrite using `[← mul_assoc, ← WithZero.exp_add]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Set `f : ((κ → Fv F v) × (κ → Fv F v)) →+ ((κ → Fv F v) × (κ → Fv F v))` to `{ toFun := fun w => (w.1, a • w.2) map_zero' := by simp map_add' := by intro x y; simp [smul_add] }`. Set `Λ₀` to `Λ.comap f`.

Establish `hmem : ∀ w, w ∈ Λ₀ ↔ (w.1, a • w.2) ∈ Λ` using `fun w => Iff.rfl`. Establish `hback : ∀ l : (κ → Fv F v) × (κ → Fv F v), (l.1, a • (a⁻¹ • l.2)) = l`. Introduce `l`. Rewrite using `[smul_smul, mul_inv_cancel₀ ha0, one_smul]`. Establish `hself₀ : ∀ w, w ∈ Λ₀ ↔ ∀ l ∈ Λ₀, ψ₀ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1`.

Introduce `w`. Rewrite using `[hmem, hself]`. Prove the components needed by the constructor for the conclusion. Introduce `h l hl`. Use `h (l.1, a • l.2) hl` as an intermediate fact.

Rewrite using `[hψ₀]`. Use `this using 2` and compare the differences between its conclusion and the goal. Simplify using `only [mul_sub, dotProduct_smul, smul_eq_mul]`. Introduce `h l hl`. Establish `hl' : (l.1, a⁻¹ • l.2) ∈ Λ₀` using `by rw [hmem]; simpa [hback l] using hl`.

Use `h _ hl'` as an intermediate fact. Rewrite `this` using `[hψ₀]`. Use `this using 2` and compare the differences between its conclusion and the goal. Simplify using `only [mul_sub, dotProduct_smul, smul_eq_mul, smul_dotProduct]`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ ha0, one_mul]`.

Choose the witnesses or unpack the hypotheses as in `⟨c', hc', hbd₀⟩ : ∃ c' : Fv F v, c' ≠ 0 ∧ ∀ l ∈ Λ₀, ∀ i, c' * l.1 i ∈ v.adicCompletionIntegers F ∧ c' * l.2 i ∈ v.adicCompletionIntegers F := by`. Break down `O.mem_or_inv_mem a with haO | haO` into its components or cases. Use `⟨c * a, mul_ne_zero hc ha0, fun l hl i => ?_⟩` and prove the remaining obligations. Establish `h` using `hbd _ ((hmem l).1 hl) i`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : c * a * l.1 i = a * (c * l.1 i)` using `by ring`. Rewrite using `[e]`. Conclude with `O.toSubring.mul_mem haO h.1`. Establish `e : c * a * l.2 i = c * (a * l.2 i)` using `by ring`.

Rewrite using `[e]`. Conclude with `h.2`. Use `⟨c, hc, fun l hl i => ?_⟩` and prove the remaining obligations. Establish `h` using `hbd _ ((hmem l).1 hl) i`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h`.

Use `⟨h.1, ?_⟩` and prove the remaining obligations. Establish `e : c * l.2 i = a⁻¹ * (c * (a * l.2 i))`. Rewrite using `[mul_left_comm, ← mul_assoc a⁻¹ a, inv_mul_cancel₀ ha0, one_mul]`. Rewrite using `[e]`. Conclude with `O.toSubring.mul_mem haO h.2`.

Establish `hη₀ : ∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ₀ → ψ₀ (η ⬝ᵥ b) = 1`. Introduce `b hb`. Rewrite `hb` using `[hmem]`. Rewrite using `[hψ₀, ← smul_eq_mul, ← dotProduct_smul]`. Conclude with `hη _ hb`.

Take `⟨y, hy⟩` from `GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v ψ₀ Λ₀ c' hc' hcond hself₀ hbd₀ η hη₀`. Conclude with `⟨a • y, (hmem _).1 hy⟩`.
-/
theorem exists_pair_of_annihilator_any : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
    ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψ (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  intro F _ _ v κ _ ψ hcont hnorm hne Λ c hc hself hbd η hη
  classical
  have hne' : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (by ext t; simpa using h t)
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_conductor_exponent F v ψ hcont hnorm hne'
  obtain ⟨a, ha⟩ := exists_valuation_eq F v n
  have ha0 : a ≠ 0 := by
    intro h; rw [h, map_zero] at ha; exact WithZero.zero_ne_coe ha
  let O := v.adicCompletionIntegers F
  let ψ₀ : AddChar (Fv F v) ℂ := ψ.mulShift a
  have hψ₀ : ∀ x, ψ₀ x = ψ (a * x) := fun x => rfl

  have hcond : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) ↔
      x ∈ v.adicCompletionIntegers F := by
    intro x
    have := hn (a * x)
    simp only [hψ₀, mul_assoc] at this ⊢
    rw [this, map_mul, ha, HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : Valued.v x = WithZero.exp (-n) * (WithZero.exp n * Valued.v x) := by
      rw [← mul_assoc, ← WithZero.exp_add]; simp
    constructor
    · intro h
      rw [e]
      calc WithZero.exp (-n) * (WithZero.exp n * Valued.v x) ≤ WithZero.exp (-n) * WithZero.exp n := by gcongr
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · intro h
      calc WithZero.exp n * Valued.v x ≤ WithZero.exp n * 1 := by gcongr
        _ = WithZero.exp n := mul_one _

  let f : ((κ → Fv F v) × (κ → Fv F v)) →+ ((κ → Fv F v) × (κ → Fv F v)) :=
    { toFun := fun w => (w.1, a • w.2)
      map_zero' := by simp
      map_add' := by intro x y; simp [smul_add] }
  let Λ₀ := Λ.comap f
  have hmem : ∀ w, w ∈ Λ₀ ↔ (w.1, a • w.2) ∈ Λ := fun w => Iff.rfl
  have hback : ∀ l : (κ → Fv F v) × (κ → Fv F v), (l.1, a • (a⁻¹ • l.2)) = l := by
    intro l; rw [smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hself₀ : ∀ w, w ∈ Λ₀ ↔ ∀ l ∈ Λ₀, ψ₀ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
    intro w
    rw [hmem, hself]
    constructor
    · intro h l hl
      have := h (l.1, a • l.2) hl
      rw [hψ₀]
      convert this using 2
      simp only [mul_sub, dotProduct_smul, smul_eq_mul]
    · intro h l hl
      have hl' : (l.1, a⁻¹ • l.2) ∈ Λ₀ := by rw [hmem]; simpa [hback l] using hl
      have := h _ hl'
      rw [hψ₀] at this
      convert this using 2
      simp only [mul_sub, dotProduct_smul, smul_eq_mul, smul_dotProduct]
      rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]

  obtain ⟨c', hc', hbd₀⟩ : ∃ c' : Fv F v, c' ≠ 0 ∧ ∀ l ∈ Λ₀, ∀ i,
      c' * l.1 i ∈ v.adicCompletionIntegers F ∧ c' * l.2 i ∈ v.adicCompletionIntegers F := by
    rcases O.mem_or_inv_mem a with haO | haO
    · refine ⟨c * a, mul_ne_zero hc ha0, fun l hl i => ?_⟩
      have h := hbd _ ((hmem l).1 hl) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      refine ⟨?_, ?_⟩
      · have e : c * a * l.1 i = a * (c * l.1 i) := by ring
        rw [e]; exact O.toSubring.mul_mem haO h.1
      · have e : c * a * l.2 i = c * (a * l.2 i) := by ring
        rw [e]; exact h.2
    · refine ⟨c, hc, fun l hl i => ?_⟩
      have h := hbd _ ((hmem l).1 hl) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      refine ⟨h.1, ?_⟩
      have e : c * l.2 i = a⁻¹ * (c * (a * l.2 i)) := by
        rw [mul_left_comm, ← mul_assoc a⁻¹ a, inv_mul_cancel₀ ha0, one_mul]
      rw [e]; exact O.toSubring.mul_mem haO h.2
  have hη₀ : ∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ₀ → ψ₀ (η ⬝ᵥ b) = 1 := by
    intro b hb
    rw [hmem] at hb
    rw [hψ₀, ← smul_eq_mul, ← dotProduct_smul]
    exact hη _ hb
  obtain ⟨y, hy⟩ := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v ψ₀ Λ₀ c' hc' hcond hself₀ hbd₀ η hη₀
  exact ⟨a • y, (hmem _).1 hy⟩

end GlobalTheory.SelfDualFirstProjAny
