import Formalism.DoubleCosetMeasures.StatementZ

open MeasureTheory Matrix ComplexConjugate

namespace Formalism.DoubleCosetMeasures.P.LemmaU

open Formalism.DoubleCosetMeasures

section
variable {F : Type} [Field F] {a t : ℕ}

/- English proof (translation)
Establish `hs` using `Classical.choose_spec h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hs.trans e.symm`.
-/
theorem choose_eq {J' : Subgroup (GL (Fin a) F)} {y : Matrix (Fin a) (Fin a) F}
    (h : ∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = y) (k : J')
    (e : ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = y) : Classical.choose h = k := by
  have hs := Classical.choose_spec h
  apply Subtype.ext
  apply Units.ext
  exact hs.trans e.symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[toRows₁, Matrix.mul_apply]`.
-/
theorem toRows₁_mul (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₁ (x * g) = toRows₁ x * g := by
  ext i j
  simp [toRows₁, Matrix.mul_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[toRows₂, Matrix.mul_apply]`.
-/
theorem toRows₂_mul (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₂ (x * g) = toRows₂ x * g := by
  ext i j
  simp [toRows₂, Matrix.mul_apply]

/- English proof (translation)
Simplify using `only [Formalism.DoubleCosetMeasures.phiU]`. Rewrite using `[dif_neg h]`.
-/
private theorem phiU_eq_zero_of_not_mem_support {O : Subring F} {ϖ : F} {J' : Subgroup (GL (Fin a) F)}
    {ρ : J' →* ℂˣ} {x : Matrix (Fin a ⊕ Fin t) (Fin a) F}
    (h : ¬ ((∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧
      toRows₂ x ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)) :
    Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x = 0 := by
  simp only [Formalism.DoubleCosetMeasures.phiU]
  rw [dif_neg h]

/- English proof (translation)
Simplify using `only [Formalism.DoubleCosetMeasures.IIset, Set.mem_setOf_eq] at hy ⊢`. Use `choose o ho hyo using hy`. Introduce `i j`. Use `⟨∑ k, o i k * g k j, O.sum_mem fun k _ => O.mul_mem (ho i k) (hg k j), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hyo i k, mul_assoc]`.
-/
theorem II_mul (O : Subring F) (ϖ : F) (y : Matrix (Fin t) (Fin a) F) (hy : y ∈ IIset O ϖ)
    (g : Matrix (Fin a) (Fin a) F) (hg : ∀ i j, g i j ∈ O) : y * g ∈ IIset O ϖ := by
  simp only [Formalism.DoubleCosetMeasures.IIset, Set.mem_setOf_eq] at hy ⊢
  choose o ho hyo using hy
  intro i j
  refine ⟨∑ k, o i k * g k j, O.sum_mem fun k _ => O.mul_mem (ho i k) (hg k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hyo i k, mul_assoc]

end

/- English proof (translation)
Introduce `F _ _ a t O ϖ J' ρ χ nrm ν g hg`. Unfold `Formalism.DoubleCosetMeasures.weilIP`. Establish `hz : ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F, Formalism.DoubleCosetMeasures.omegaS χ nrm g (Formalism.DoubleCosetMeasures.phiU (t` using `t) O ϖ J' ρ) x * conj (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x) = 0 := by`. Introduce `x`. Distinguish the cases in `hx : ∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x`.

Take `⟨k, hk⟩` from `hx`. Establish `h0 : Formalism.DoubleCosetMeasures.phiU (t` using `t) O ϖ J' ρ (x * (g : Matrix (Fin a) (Fin a) F)) = 0 := by`. Apply `phiU_eq_zero_of_not_mem_support` to reduce the goal to its premises. Introduce and unpack `⟨⟨k', hk'⟩, -⟩`. Apply `hg` to reduce the goal to its premises.

Establish `e : ((k : GL (Fin a) F) * g : GL (Fin a) F) = k'`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, hk, hk', toRows₁_mul]`. Establish `hgk : g = (k : GL (Fin a) F)⁻¹ * k'`. Rewrite using `[← e, inv_mul_cancel_left]`.

Rewrite using `[hgk]`. Conclude with `J'.mul_mem (J'.inv_mem k.2) k'.2`. Simplify using `only [Formalism.DoubleCosetMeasures.omegaS, h0, mul_zero, zero_mul]`. Rewrite using `[phiU_eq_zero_of_not_mem_support (fun h => hx h.1)]`. Simplify using the standard rewrite rules.

Simplify using `only [hz, integral_zero]`.
-/
theorem suppJ' : SuppJ := by
  intro F _ _ a t O ϖ J' ρ χ nrm ν g hg
  unfold Formalism.DoubleCosetMeasures.weilIP
  have hz : ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
      Formalism.DoubleCosetMeasures.omegaS χ nrm g (Formalism.DoubleCosetMeasures.phiU (t := t) O ϖ J' ρ) x * conj (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x) = 0 := by
    intro x
    by_cases hx : ∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x
    · obtain ⟨k, hk⟩ := hx
      have h0 : Formalism.DoubleCosetMeasures.phiU (t := t) O ϖ J' ρ (x * (g : Matrix (Fin a) (Fin a) F)) = 0 := by
        apply phiU_eq_zero_of_not_mem_support
        rintro ⟨⟨k', hk'⟩, -⟩
        apply hg
        have e : ((k : GL (Fin a) F) * g : GL (Fin a) F) = k' := by
          apply Units.ext
          rw [Units.val_mul, hk, hk', toRows₁_mul]
        have hgk : g = (k : GL (Fin a) F)⁻¹ * k' := by
          rw [← e, inv_mul_cancel_left]
        rw [hgk]
        exact J'.mul_mem (J'.inv_mem k.2) k'.2
      simp only [Formalism.DoubleCosetMeasures.omegaS, h0, mul_zero, zero_mul]
    · rw [phiU_eq_zero_of_not_mem_support (fun h => hx h.1)]
      simp
  simp only [hz, integral_zero]

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ a t O hO ϖ hϖ J' hJc hJint ρ hρ χ nrm lam heq c hc μ ν₁ ν₂ _ _`. Establish `hMatrixOpensMeasurable : ∀ (m n : Type) [Fintype m] [Fintype n], OpensMeasurableSpace (Matrix m n F)` using `fun m n _ _ => inferInstanceAs (OpensMeasurableSpace (m → n → F))`. Use `haveI := hMatrixOpensMeasurable (Fin a) (Fin a)`. Establish `hJm : MeasurableSet (Jset J')` using `((hJc.image Units.continuous_val).isClosed).measurableSet`. Establish `hOpen1 : IsOpen {z : F | ∃ o ∈ O, z = ϖ * o}`.

Establish `: {z : F | ∃ o ∈ O, z = ϖ * o} = (fun z => ϖ⁻¹ * z) ⁻¹' (O : Set F)`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho, rfl⟩`.

Rewrite using `[← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]` and apply the resulting hypothesis. Introduce `h; exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]⟩`. Rewrite using `[this]`. Conclude with `hO.preimage (continuous_const.mul continuous_id)`. Establish `hIIm : MeasurableSet (IIset (a` using `a) (t := t) O ϖ) := by`.

Establish `: IIset (a` using `a) (t := t) O ϖ = ⋂ i, ⋂ j, (fun y : Matrix (Fin t) (Fin a) F => y i j) ⁻¹' {z : F | ∃ o ∈ O, z = ϖ * o} := by`. Use extensionality with `y`. Simplify using `[IIset]`. Rewrite using `[this]`. Use `MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_` and prove the remaining obligations.

Conclude with `(hOpen1.measurableSet).preimage ((measurable_pi_apply j).comp (measurable_pi_apply i))`. Establish `hR1 : Measurable (fun x : Matrix (Fin a ⊕ Fin t) (Fin a) F => toRows₁ x)` using `measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inl i)`. Establish `hR2 : Measurable (fun x : Matrix (Fin a ⊕ Fin t) (Fin a) F => toRows₂ x)` using `measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inr i)`. Establish `hFR : Measurable (fun p : Matrix (Fin a) (Fin a) F × Matrix (Fin t) (Fin a) F => Matrix.fromRows p.1 p.2)`. Use `measurable_pi_lambda _ fun i => ?_` and prove the remaining obligations.

Consider the cases of `i with`. Consider the case `inl i => exact (measurable_pi_apply i).comp measurable_fst`. Consider the case `inr i => exact (measurable_pi_apply i).comp measurable_snd`. Use `set S : Set (Matrix (Fin a ⊕ Fin t) (Fin a) F) := {x | toRows₁ x ∈ Jset J' ∧ toRows₂ x ∈ IIset O ϖ} with hSdef`. Establish `hSm : MeasurableSet S` using `(hR1 hJm).inter (hR2 hIIm)`.

Use `set ν := (ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2) with hνdef`. Establish `hνS : ν S = ν₁ (Jset J') * ν₂ (IIset O ϖ)`. Rewrite using `[hνdef, Measure.map_apply hFR hSm]`. Establish `: (fun p : Matrix (Fin a) (Fin a) F × Matrix (Fin t) (Fin a) F => Matrix.fromRows p.1 p.2) ⁻¹' S = Jset J' ×ˢ IIset O ϖ`. Use extensionality with `p`.

Simplify using `[hSdef]`. Rewrite using `[this, Measure.prod_prod]`. Establish `hW : ∀ g (hg : g ∈ J'), weilIP ν (omegaS χ nrm g (phiU O ϖ J' ρ)) (phiU O ϖ J' ρ) = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^ ((Fintype.card (Fin a ⊕ Fin t) : ℝ) / 2) : ℝ) : ℂ) * ((ρ ⟨g, hg⟩ : ℂˣ) : ℂ) * (((ν₁ (Jset …`. Introduce `g hg`. Unfold `weilIP`.

Establish `hpt : ∀ x, omegaS χ nrm g (phiU O ϖ J' ρ) x * conj (phiU O ϖ J' ρ x) = S.indicator (fun _ => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^ ((Fintype.card (Fin a ⊕ Fin t) : ℝ) / 2) : ℝ) : ℂ) * ((ρ ⟨g, hg⟩ : ℂˣ) : ℂ)) x`. Introduce `x`. Distinguish the cases in `hx : x ∈ S`. Rewrite using `[Set.indicator_of_mem hx]`. Take `⟨⟨k, hk, ek⟩, hxII⟩` from `hx`.

Establish `h1 : (∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧ toRows₂ x ∈ IIset O ϖ` using `⟨⟨⟨k, hk⟩, ek⟩, hxII⟩`. Establish `ekg : ((⟨k * g, J'.mul_mem hk hg⟩ : J') : GL (Fin a) F) = toRows₁ (x * (g : Matrix (Fin a) (Fin a) F))`. Simplify using `[toRows₁_mul, ← ek]`. Establish `h2 : (∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ (x * (g : Matrix (Fin a) (Fin a) F))) ∧ toRows₂ (x * (g : Matrix (Fin a) (Fin a) F)) ∈ IIset O ϖ` using `⟨⟨_, ekg⟩, by rw [toRows₂_mul]; exact II_mul O ϖ _ hxII _ (hJint g hg)⟩`. Unfold `omegaS phiU`.

Rewrite using `[dif_pos h1, dif_pos h2, choose_eq h1.1 ⟨k, hk⟩ ek, choose_eq h2.1 _ ekg]`. Establish `hmul : (⟨k * g, J'.mul_mem hk hg⟩ : J') = ⟨k, hk⟩ * ⟨g, hg⟩` using `rfl`. Rewrite using `[hmul, map_mul, Units.val_mul]`. Establish `hn : ((ρ ⟨k, hk⟩ : ℂˣ) : ℂ) * conj ((ρ ⟨k, hk⟩ : ℂˣ) : ℂ) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hρ]`.

Simplify using the standard rewrite rules. Take the linear combination `(((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^ ((Fintype.card (Fin a ⊕ Fin t) : ℝ) / 2) : ℝ) : ℂ) * ((ρ ⟨g, hg⟩ : ℂˣ) : ℂ)) * hn`. Rewrite using `[Set.indicator_of_notMem hx]`. Establish `hn : ¬ ((∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧ toRows₂ x ∈ IIset O ϖ)`. Introduce and unpack `⟨⟨k, ek⟩, h2⟩`.

Conclude with `hx ⟨⟨k, k.2, ek⟩, h2⟩`. Simplify using `only [phiU]`. Rewrite using `[dif_neg hn]`. Simplify using the standard rewrite rules. Repeatedly rewrite using `[hpt]`.

Rewrite using `[integral_indicator_const _ hSm]`. Simplify using `only [Measure.real, hνS, ENNReal.toReal_mul, Complex.real_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hJ'm : MeasurableSet (J' : Set (GL (Fin a) F))` using `hJc.isClosed.measurableSet`.

Establish `hint : ∀ g, weilIP ν (omegaS χ nrm g (phiU O ϖ J' ρ)) (phiU O ϖ J' ρ) * conj (c g) = (J' : Set (GL (Fin a) F)).indicator (fun _ => (((ν₁ (Jset J')).toReal * (ν₂ (IIset O ϖ)).toReal : ℝ) : ℂ) * conj (c 1)) g`. Introduce `g`. Distinguish the cases in `hg : g ∈ J'`. Rewrite using `[Set.indicator_of_mem (show g ∈ (J' : Set _) from hg), hW g hg]`. Establish `hcg : c g = ((lam ⟨g, hg⟩ : ℂˣ) : ℂ) * c 1`.

Use `hc 1 ⟨g, hg⟩` as an intermediate fact. Simplify using `using this`. Establish `he` using `heq ⟨g, hg⟩`. Establish `hcard : (Fintype.card (Fin a ⊕ Fin t) : ℝ) = ((a + t : ℕ) : ℝ)` using `by simp`. Rewrite using `[hcard, hcg, map_mul]`.

Simplify using `only at he`. Take the linear combination `((((ν₁ (Jset J')).toReal * (ν₂ (IIset O ϖ)).toReal : ℝ) : ℂ) * conj (c 1)) * he`. Rewrite using `[Set.indicator_of_notMem (show g ∉ (J' : Set _) from hg)]`. Use `Formalism.DoubleCosetMeasures.P.LemmaU.suppJ' F a t O ϖ J' ρ χ nrm ν g hg` as an intermediate fact. Rewrite using `[this, zero_mul]`.

Unfold `localZ`. Repeatedly rewrite using `[hint]`. Rewrite using `[integral_indicator_const _ hJ'm]`. Simplify using `only [Measure.real, Complex.real_smul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lemmaU : LemmaUSplit := by
  intro F _ _ _ _ _ _ _ a t O hO ϖ hϖ J' hJc hJint ρ hρ χ nrm lam heq c hc μ ν₁ ν₂ _ _

  have hMatrixOpensMeasurable : ∀ (m n : Type) [Fintype m] [Fintype n],
      OpensMeasurableSpace (Matrix m n F) := fun m n _ _ =>
    inferInstanceAs (OpensMeasurableSpace (m → n → F))
  haveI := hMatrixOpensMeasurable (Fin a) (Fin a)
  have hJm : MeasurableSet (Jset J') :=
    ((hJc.image Units.continuous_val).isClosed).measurableSet
  have hOpen1 : IsOpen {z : F | ∃ o ∈ O, z = ϖ * o} := by
    have : {z : F | ∃ o ∈ O, z = ϖ * o} = (fun z => ϖ⁻¹ * z) ⁻¹' (O : Set F) := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
      constructor
      · rintro ⟨o, ho, rfl⟩; rwa [← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]
      · intro h; exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]⟩
    rw [this]; exact hO.preimage (continuous_const.mul continuous_id)
  have hIIm : MeasurableSet (IIset (a := a) (t := t) O ϖ) := by
    have : IIset (a := a) (t := t) O ϖ = ⋂ i, ⋂ j, (fun y : Matrix (Fin t) (Fin a) F => y i j) ⁻¹'
        {z : F | ∃ o ∈ O, z = ϖ * o} := by
      ext y; simp [IIset]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    exact (hOpen1.measurableSet).preimage
      ((measurable_pi_apply j).comp (measurable_pi_apply i))
  have hR1 : Measurable (fun x : Matrix (Fin a ⊕ Fin t) (Fin a) F => toRows₁ x) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inl i)
  have hR2 : Measurable (fun x : Matrix (Fin a ⊕ Fin t) (Fin a) F => toRows₂ x) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inr i)
  have hFR : Measurable (fun p : Matrix (Fin a) (Fin a) F × Matrix (Fin t) (Fin a) F =>
      Matrix.fromRows p.1 p.2) := by
    refine measurable_pi_lambda _ fun i => ?_
    cases i with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr i => exact (measurable_pi_apply i).comp measurable_snd
  set S : Set (Matrix (Fin a ⊕ Fin t) (Fin a) F) :=
    {x | toRows₁ x ∈ Jset J' ∧ toRows₂ x ∈ IIset O ϖ} with hSdef
  have hSm : MeasurableSet S := (hR1 hJm).inter (hR2 hIIm)
  set ν := (ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2) with hνdef
  have hνS : ν S = ν₁ (Jset J') * ν₂ (IIset O ϖ) := by
    rw [hνdef, Measure.map_apply hFR hSm]
    have : (fun p : Matrix (Fin a) (Fin a) F × Matrix (Fin t) (Fin a) F =>
        Matrix.fromRows p.1 p.2) ⁻¹' S = Jset J' ×ˢ IIset O ϖ := by
      ext p; simp [hSdef]
    rw [this, Measure.prod_prod]

  have hW : ∀ g (hg : g ∈ J'), weilIP ν (omegaS χ nrm g (phiU O ϖ J' ρ)) (phiU O ϖ J' ρ) =
      ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^
        ((Fintype.card (Fin a ⊕ Fin t) : ℝ) / 2) : ℝ) : ℂ) * ((ρ ⟨g, hg⟩ : ℂˣ) : ℂ) *
      (((ν₁ (Jset J')).toReal * (ν₂ (IIset O ϖ)).toReal : ℝ) : ℂ) := by
    intro g hg
    unfold weilIP
    have hpt : ∀ x, omegaS χ nrm g (phiU O ϖ J' ρ) x * conj (phiU O ϖ J' ρ x) =
        S.indicator (fun _ => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^
        ((Fintype.card (Fin a ⊕ Fin t) : ℝ) / 2) : ℝ) : ℂ) * ((ρ ⟨g, hg⟩ : ℂˣ) : ℂ)) x := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        obtain ⟨⟨k, hk, ek⟩, hxII⟩ := hx
        have h1 : (∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧
            toRows₂ x ∈ IIset O ϖ := ⟨⟨⟨k, hk⟩, ek⟩, hxII⟩
        have ekg : ((⟨k * g, J'.mul_mem hk hg⟩ : J') : GL (Fin a) F) =
            toRows₁ (x * (g : Matrix (Fin a) (Fin a) F)) := by
          simp [toRows₁_mul, ← ek]
        have h2 : (∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) =
            toRows₁ (x * (g : Matrix (Fin a) (Fin a) F))) ∧
            toRows₂ (x * (g : Matrix (Fin a) (Fin a) F)) ∈ IIset O ϖ :=
          ⟨⟨_, ekg⟩, by rw [toRows₂_mul]; exact II_mul O ϖ _ hxII _ (hJint g hg)⟩
        unfold omegaS phiU
        rw [dif_pos h1, dif_pos h2, choose_eq h1.1 ⟨k, hk⟩ ek, choose_eq h2.1 _ ekg]
        have hmul : (⟨k * g, J'.mul_mem hk hg⟩ : J') = ⟨k, hk⟩ * ⟨g, hg⟩ := rfl
        rw [hmul, map_mul, Units.val_mul]
        have hn : ((ρ ⟨k, hk⟩ : ℂˣ) : ℂ) * conj ((ρ ⟨k, hk⟩ : ℂˣ) : ℂ) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hρ]; simp
        linear_combination (((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^
          ((Fintype.card (Fin a ⊕ Fin t) : ℝ) / 2) : ℝ) : ℂ) * ((ρ ⟨g, hg⟩ : ℂˣ) : ℂ)) * hn
      · rw [Set.indicator_of_notMem hx]
        have hn : ¬ ((∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧
            toRows₂ x ∈ IIset O ϖ) := by
          rintro ⟨⟨k, ek⟩, h2⟩; exact hx ⟨⟨k, k.2, ek⟩, h2⟩
        simp only [phiU]; rw [dif_neg hn]; simp
    simp_rw [hpt]
    rw [integral_indicator_const _ hSm]
    simp only [Measure.real, hνS, ENNReal.toReal_mul, Complex.real_smul]
    push_cast; ring

  have hJ'm : MeasurableSet (J' : Set (GL (Fin a) F)) := hJc.isClosed.measurableSet
  have hint : ∀ g, weilIP ν (omegaS χ nrm g (phiU O ϖ J' ρ)) (phiU O ϖ J' ρ) * conj (c g) =
      (J' : Set (GL (Fin a) F)).indicator (fun _ =>
        (((ν₁ (Jset J')).toReal * (ν₂ (IIset O ϖ)).toReal : ℝ) : ℂ) * conj (c 1)) g := by
    intro g
    by_cases hg : g ∈ J'
    · rw [Set.indicator_of_mem (show g ∈ (J' : Set _) from hg), hW g hg]
      have hcg : c g = ((lam ⟨g, hg⟩ : ℂˣ) : ℂ) * c 1 := by
        have := hc 1 ⟨g, hg⟩; simpa using this
      have he := heq ⟨g, hg⟩
      have hcard : (Fintype.card (Fin a ⊕ Fin t) : ℝ) = ((a + t : ℕ) : ℝ) := by simp
      rw [hcard, hcg, map_mul]
      simp only at he
      linear_combination ((((ν₁ (Jset J')).toReal * (ν₂ (IIset O ϖ)).toReal : ℝ) : ℂ) *
        conj (c 1)) * he
    · rw [Set.indicator_of_notMem (show g ∉ (J' : Set _) from hg)]
      have := Formalism.DoubleCosetMeasures.P.LemmaU.suppJ' F a t O ϖ J' ρ χ nrm ν g hg
      rw [this, zero_mul]
  unfold localZ
  simp_rw [hint]
  rw [integral_indicator_const _ hJ'm]
  simp only [Measure.real, Complex.real_smul]
  push_cast; ring

end Formalism.DoubleCosetMeasures.P.LemmaU

namespace Formalism.DoubleCosetMeasures.P

/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.LemmaU.suppJ'`.
-/
theorem suppJ : Formalism.DoubleCosetMeasures.SuppJ := Formalism.DoubleCosetMeasures.P.LemmaU.suppJ'
/- English proof (translation)
The claim follows from `Formalism.DoubleCosetMeasures.P.LemmaU.lemmaU`.
-/
theorem lemmaUSplit : Formalism.DoubleCosetMeasures.LemmaUSplit := Formalism.DoubleCosetMeasures.P.LemmaU.lemmaU

end Formalism.DoubleCosetMeasures.P
