import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.SchrFixUniq

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]`. Rewrite using `[← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]`. Use `congr 2`. Simplify using `only [dotProduct_add, add_dotProduct]`.

Establish `h2 : (2 : R) * ⅟(2 : R) = 1` using `mul_invOf_self 2`. Take the linear combination `(-(w.1 ⬝ᵥ w'.2)) * h2`.
-/
theorem schr_comp {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [schr, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schr_smul' {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w : (κ → R) × (κ → R)) (a : ℂ) (φ : (κ → R) → ℂ) : schr ψ w (a • φ) = a • schr ψ w φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[schr]`.
-/
theorem schr_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (φ : (κ → R) → ℂ) : schr ψ 0 φ = φ := by
  funext x
  simp [schr]

/- English proof (translation)
Introduce `hx`. Establish `h2 : ψ (x + -x) = ψ x * ψ (-x)` using `AddChar.map_add_eq_mul ψ x (-x)`. Rewrite `h2` using `[add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul]`. Conclude with `one_ne_zero h2`.
-/
theorem char_ne_zero {R : Type} [CommRing R] (ψ : AddChar R ℂ) (x : R) : ψ x ≠ 0 := by
  intro hx
  have h2 : ψ (x + -x) = ψ x * ψ (-x) := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul] at h2
  exact one_ne_zero h2

/- English proof (translation)
Proceed by induction on `hl using AddSubgroup.closure_induction with`. Consider the case `mem s hs => exact ⟨1, one_ne_zero, by rw [hf s hs, one_smul], by rw [hg s hs, one_smul]⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [schr_zero', one_smul], by rw [schr_zero', one_smul]⟩`. Consider the case `add w w' _ _ h h'`. Take `⟨χ, hχ, h1, h2⟩` from `h`.

Take `⟨χ', hχ', h1', h2'⟩` from `h'`. Establish `hz` using `char_ne_zero ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2))`. Establish `key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ w' φ = χ' • φ → schr ψ (w + w') φ = ((ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)))⁻¹ * (χ' * χ)) • φ`. Introduce `φ a b`. Establish `e` using `schr_comp ψ w w' φ`.

Rewrite `e` using `[b, schr_smul', a, smul_smul]`. Rewrite using `[mul_smul, e, smul_smul, inv_mul_cancel₀ hz, one_smul]`. Conclude with `⟨_, mul_ne_zero (inv_ne_zero hz) (mul_ne_zero hχ' hχ), key f h1 h1', key g h2 h2'⟩`. Consider the case `neg w _ h`. Take `⟨χ, hχ, h1, h2⟩` from `h`.

Establish `key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ (-w) φ = χ⁻¹ • φ`. Introduce `φ a`. Establish `e` using `schr_comp ψ (-w) w φ`. Establish `e0 : ⅟(2 : R) * ((-w).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (-w).2) = 0`. Simplify using the standard rewrite rules.

Rewrite `e` using `[a, schr_smul', neg_add_cancel, schr_zero', e0, AddChar.map_zero_eq_one, one_smul]`. Use `conv_rhs => rw [← e]`. Rewrite using `[smul_smul, inv_mul_cancel₀ hχ, one_smul]`. Conclude with `⟨_, inv_ne_zero hχ, key f h1, key g h2⟩`.
-/
theorem common_eigen {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (S : Set ((κ → R) × (κ → R))) (f g : (κ → R) → ℂ) (hf : ∀ s ∈ S, schr ψ s f = f)
    (hg : ∀ s ∈ S, schr ψ s g = g) (l : (κ → R) × (κ → R)) (hl : l ∈ AddSubgroup.closure S) :
    ∃ χ : ℂ, χ ≠ 0 ∧ schr ψ l f = χ • f ∧ schr ψ l g = χ • g := by
  induction hl using AddSubgroup.closure_induction with
  | mem s hs => exact ⟨1, one_ne_zero, by rw [hf s hs, one_smul], by rw [hg s hs, one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [schr_zero', one_smul], by rw [schr_zero', one_smul]⟩
  | add w w' _ _ h h' =>
    obtain ⟨χ, hχ, h1, h2⟩ := h
    obtain ⟨χ', hχ', h1', h2'⟩ := h'
    have hz := char_ne_zero ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2))
    have key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ w' φ = χ' • φ →
        schr ψ (w + w') φ = ((ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)))⁻¹ * (χ' * χ)) • φ := by
      intro φ a b
      have e := schr_comp ψ w w' φ
      rw [b, schr_smul', a, smul_smul] at e
      rw [mul_smul, e, smul_smul, inv_mul_cancel₀ hz, one_smul]
    exact ⟨_, mul_ne_zero (inv_ne_zero hz) (mul_ne_zero hχ' hχ), key f h1 h1', key g h2 h2'⟩
  | neg w _ h =>
    obtain ⟨χ, hχ, h1, h2⟩ := h
    have key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ (-w) φ = χ⁻¹ • φ := by
      intro φ a
      have e := schr_comp ψ (-w) w φ
      have e0 : ⅟(2 : R) * ((-w).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (-w).2) = 0 := by
        simp
      rw [a, schr_smul', neg_add_cancel, schr_zero', e0, AddChar.map_zero_eq_one, one_smul] at e
      conv_rhs => rw [← e]
      rw [smul_smul, inv_mul_cancel₀ hχ, one_smul]
    exact ⟨_, inv_ne_zero hχ, key f h1, key g h2⟩

/- English proof (translation)
Establish `hne : ∃ t, ψk t ≠ 1`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `h1 (AddChar.ext _ _ fun t => by rw [h t, AddChar.one_apply])`. Take `⟨n, hn⟩` from `GlobalTheory.CharConductor.exists_exponent_of_valued ψk hc hne`.

Take `⟨a, ha⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)`. Establish `ha0 : (Valued.v a : WithZero (Multiplicative ℤ)) ≠ 0` using `by rw [ha]; exact WithZero.exp_ne_zero`. Use `⟨a, by simpa using ha0, fun x => ?_⟩` and prove the remaining obligations. Establish `h` using `hn (a * x)`. Rewrite `h` using `[← ha, map_mul, mul_le_iff_le_one_right (zero_lt_iff.2 ha0)]`.

Simplify `h` using `only [HeightOneSpectrum.mem_adicCompletionIntegers, mul_assoc]`.
-/
theorem exists_shift {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψk : AddChar (Fv F v) ℂ)
    (hc : Continuous ψk) (h1 : ψk ≠ 1) : ∃ a : Fv F v, a ≠ 0 ∧ ∀ x : Fv F v,
      (∀ y ∈ v.adicCompletionIntegers F, ψk (a * (x * y)) = 1) ↔ x ∈ v.adicCompletionIntegers F := by
  have hne : ∃ t, ψk t ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (AddChar.ext _ _ fun t => by rw [h t, AddChar.one_apply])
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_exponent_of_valued ψk hc hne
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have ha0 : (Valued.v a : WithZero (Multiplicative ℤ)) ≠ 0 := by rw [ha]; exact WithZero.exp_ne_zero
  refine ⟨a, by simpa using ha0, fun x => ?_⟩
  have h := hn (a * x)
  rw [← ha, map_mul, mul_le_iff_le_one_right (zero_lt_iff.2 ha0)] at h
  simpa only [HeightOneSpectrum.mem_adicCompletionIntegers, mul_assoc] using h

/- English proof (translation)
Take `⟨a, ha, hcond⟩` from `exists_shift v ψk hc h1`. Set `Λ' : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))` to `{ carrier := {w | (w.1, a • w.2) ∈ Λ} add_mem' := fun {x y} hx hy => by`. Use `Λ.add_mem hx hy` as an intermediate fact. Simplify `this` using `[smul_add]`. Use the proof step `zero_mem' := by show ((0 : κ → Fv F v), a • (0 : κ → Fv F v)) ∈ Λ`.

Rewrite using `[smul_zero]`. Conclude with `Λ.zero_mem`. Use the proof step `neg_mem' := fun {x} hx => by`. Use `Λ.neg_mem hx` as an intermediate fact. Simplify using `using this }`.

Establish `hΛ' : ∀ w, w ∈ Λ' ↔ (w.1, a • w.2) ∈ Λ` using `fun _ => Iff.rfl`. Establish `hbd' : ∃ c' : Fv F v, c' ≠ 0 ∧ ∀ l ∈ Λ', ∀ i, c' * l.1 i ∈ v.adicCompletionIntegers F ∧ c' * l.2 i ∈ v.adicCompletionIntegers F`. Break down `(v.adicCompletionIntegers F).mem_or_inv_mem a with h | h` into its components or cases. Use `⟨a * c, mul_ne_zero ha hc0, fun l hl i => ?_⟩` and prove the remaining obligations. Take `⟨p, q⟩` from `hbd _ ((hΛ' l).1 hl) i`.

Use `⟨by rw [mul_assoc]; exact mul_mem h p, ?_⟩` and prove the remaining obligations. Use `q using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨c, hc0, fun l hl i => ?_⟩` and prove the remaining obligations.

Take `⟨p, q⟩` from `hbd _ ((hΛ' l).1 hl) i`. Use `⟨p, ?_⟩` and prove the remaining obligations. Use `mul_mem h q using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Take `⟨c', hc', hb'⟩` from `hbd'`. Establish `hs' : ∀ w, w ∈ Λ' ↔ ∀ l ∈ Λ', (ψk.mulShift a) (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1`. Introduce `w`. Rewrite using `[hΛ', hself]`. Prove the components needed by the constructor for the conclusion.

Introduce `h l hl`. Use `h _ ((hΛ' l).1 hl)` as an intermediate fact. Simplify using `only [dotProduct_smul, smul_eq_mul] at this`. Rewrite using `[AddChar.mulShift_apply, mul_sub]`. Conclude with `this`.

Introduce `h l hl`. Use `h (l.1, a⁻¹ • l.2) (by rw [hΛ']; simpa [smul_smul, mul_inv_cancel₀ ha] using hl)` as an intermediate fact. Rewrite `this` using `[AddChar.mulShift_apply, mul_sub]`. Simplify using `only [dotProduct_smul, smul_eq_mul] at this ⊢`. Rewrite `this` using `[mul_inv_cancel_left₀ ha]`. Then use the resulting hypothesis.

Take `⟨y, hy⟩` from `GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (ψk.mulShift a) Λ' c' hc' (fun x => by simpa only [AddChar.mulShift_apply] using hcond x) hs' hb' η (fun b hb => by`. Use `hη _ ((hΛ' _).1 hb)` as an intermediate fact. Rewrite using `[dotProduct_smul, smul_eq_mul, ← AddChar.mulShift_apply] at this)` and apply the resulting hypothesis. Conclude with `⟨_, (hΛ' _).1 hy⟩`.
-/
theorem exists_pair {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (ψk : AddChar (Fv F v) ℂ) (hc : Continuous ψk) (h1 : ψk ≠ 1)
    (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v) (hc0 : c ≠ 0)
    (hself : ∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1)
    (hbd : ∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F)
    (η : κ → Fv F v) (hη : ∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) : ∃ y, (η, y) ∈ Λ := by
  classical
  obtain ⟨a, ha, hcond⟩ := exists_shift v ψk hc h1
  let Λ' : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := {w | (w.1, a • w.2) ∈ Λ}
      add_mem' := fun {x y} hx hy => by
        have := Λ.add_mem hx hy
        simpa [smul_add] using this
      zero_mem' := by
        show ((0 : κ → Fv F v), a • (0 : κ → Fv F v)) ∈ Λ
        rw [smul_zero]
        exact Λ.zero_mem
      neg_mem' := fun {x} hx => by
        have := Λ.neg_mem hx
        simpa using this }
  have hΛ' : ∀ w, w ∈ Λ' ↔ (w.1, a • w.2) ∈ Λ := fun _ => Iff.rfl
  have hbd' : ∃ c' : Fv F v, c' ≠ 0 ∧ ∀ l ∈ Λ', ∀ i,
      c' * l.1 i ∈ v.adicCompletionIntegers F ∧ c' * l.2 i ∈ v.adicCompletionIntegers F := by
    rcases (v.adicCompletionIntegers F).mem_or_inv_mem a with h | h
    · refine ⟨a * c, mul_ne_zero ha hc0, fun l hl i => ?_⟩
      obtain ⟨p, q⟩ := hbd _ ((hΛ' l).1 hl) i
      refine ⟨by rw [mul_assoc]; exact mul_mem h p, ?_⟩
      convert q using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · refine ⟨c, hc0, fun l hl i => ?_⟩
      obtain ⟨p, q⟩ := hbd _ ((hΛ' l).1 hl) i
      refine ⟨p, ?_⟩
      convert mul_mem h q using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  obtain ⟨c', hc', hb'⟩ := hbd'
  have hs' : ∀ w, w ∈ Λ' ↔ ∀ l ∈ Λ', (ψk.mulShift a) (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
    intro w
    rw [hΛ', hself]
    constructor
    · intro h l hl
      have := h _ ((hΛ' l).1 hl)
      simp only [dotProduct_smul, smul_eq_mul] at this
      rw [AddChar.mulShift_apply, mul_sub]
      exact this
    · intro h l hl
      have := h (l.1, a⁻¹ • l.2) (by rw [hΛ']; simpa [smul_smul, mul_inv_cancel₀ ha] using hl)
      rw [AddChar.mulShift_apply, mul_sub] at this
      simp only [dotProduct_smul, smul_eq_mul] at this ⊢
      rwa [mul_inv_cancel_left₀ ha] at this
  obtain ⟨y, hy⟩ := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (ψk.mulShift a) Λ' c' hc'
    (fun x => by simpa only [AddChar.mulShift_apply] using hcond x) hs' hb' η (fun b hb => by
      have := hη _ ((hΛ' _).1 hb)
      rwa [dotProduct_smul, smul_eq_mul, ← AddChar.mulShift_apply] at this)
  exact ⟨_, (hΛ' _).1 hy⟩

/- English proof (translation)
Introduce `F _ _ v κ _ ψk hc h1 S Λ c hS hc0 hself hbd f g hf hg hf0`. Establish `hall : ∀ l, ∃ χ : ℂ, l ∈ Λ → schr ψk l f = χ • f ∧ schr ψk l g = χ • g`. Introduce `l`. Distinguish the cases in `hl : l ∈ Λ`. Take `⟨χ, -, h⟩` from `common_eigen ψk S f g hf hg l (hS hl)`.

Conclude with `⟨χ, fun _ => h⟩`. Conclude with `⟨0, fun h => absurd h hl⟩`. Use `choose χ hχ using hall`. Use `GlobalTheory.heisenbergEigen_proportional ψk Λ χ f g (fun l hl ξ => ?_) (fun l hl ξ => ?_) hf0 (exists_pair v ψk hc h1 Λ c hc0 hself hbd)` and prove the remaining obligations. Use `congrFun (hχ l hl).1 ξ` as an intermediate fact.

Rewrite using `[← invOf_eq_inv]`. Conclude with `this`. Use `congrFun (hχ l hl).2 ξ` as an intermediate fact. Rewrite using `[← invOf_eq_inv]`. Conclude with `this`.
-/
theorem proportional_of_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ (S : Set ((κ → Fv F v) × (κ → Fv F v))) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v),
    Λ ≤ AddSubgroup.closure S → c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ f g : (κ → Fv F v) → ℂ, (∀ s ∈ S, schr ψk s f = f) → (∀ s ∈ S, schr ψk s g = g) → f ≠ 0 → ∃ a : ℂ, g = a • f := by
  intro F _ _ v κ _ ψk hc h1 S Λ c hS hc0 hself hbd f g hf hg hf0
  classical
  have hall : ∀ l, ∃ χ : ℂ, l ∈ Λ → schr ψk l f = χ • f ∧ schr ψk l g = χ • g := by
    intro l
    by_cases hl : l ∈ Λ
    · obtain ⟨χ, -, h⟩ := common_eigen ψk S f g hf hg l (hS hl)
      exact ⟨χ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose χ hχ using hall
  refine GlobalTheory.heisenbergEigen_proportional ψk Λ χ f g (fun l hl ξ => ?_) (fun l hl ξ => ?_) hf0
    (exists_pair v ψk hc h1 Λ c hc0 hself hbd)
  · have := congrFun (hχ l hl).1 ξ
    rw [← invOf_eq_inv]
    exact this
  · have := congrFun (hχ l hl).2 ξ
    rw [← invOf_eq_inv]
    exact this

end GlobalTheory.SchrFixUniq
