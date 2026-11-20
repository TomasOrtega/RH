import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.QuadPhase

/- English proof (translation)
Set `M₀ : IntermediateField ℚ ℂ` to `IntermediateField.adjoin ℚ (S ∩ (M : Set ℂ))`. Establish `hle : M₀ ≤ M` using `IntermediateField.adjoin_le_iff.2 Set.inter_subset_right`. Establish `hc : Countable M₀`. Establish `h1` using `IntermediateField.cardinalMk_adjoin_le ℚ (S ∩ (M : Set ℂ))`. Establish `h2 : (S ∩ (M : Set ℂ)).Countable` using `hS.mono Set.inter_subset_left`.

Use `Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))` and prove the remaining obligations. Conclude with `Cardinal.mk_le_aleph0`. Conclude with `Cardinal.mk_le_aleph0_iff.2 h2`. Take `⟨σ, hσ⟩` from `GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M₀) (algebraMap M₀ ℂ) ((ρ.comp (IntermediateField.inclusion hle)).toRingHom)`. Use `⟨((σ : ℂ →+* ℂ).toRatAlgHom).comp (IntermediateField.val ⊤), fun x hx hxM => ?_⟩` and prove the remaining obligations.

Establish `hx0 : x ∈ M₀` using `IntermediateField.subset_adjoin ℚ _ ⟨hx, hxM⟩`. Establish `h` using `hσ ⟨x, hx0⟩`. Unfold `cj TaylorLogMetric.liftM`. Rewrite using `[dif_pos IntermediateField.mem_top, dif_pos hxM]`. Conclude with `h`.
-/
theorem exists_top_extension (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ) (hS : S.Countable) :
    ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  let M₀ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (S ∩ (M : Set ℂ))
  have hle : M₀ ≤ M := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  have hc : Countable M₀ := by
    have h1 := IntermediateField.cardinalMk_adjoin_le ℚ (S ∩ (M : Set ℂ))
    have h2 : (S ∩ (M : Set ℂ)).Countable := hS.mono Set.inter_subset_left
    refine Cardinal.mk_le_aleph0_iff.1 (h1.trans (max_le (max_le ?_ ?_) le_rfl))
    · exact Cardinal.mk_le_aleph0
    · exact Cardinal.mk_le_aleph0_iff.2 h2
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M₀)
    (algebraMap M₀ ℂ) ((ρ.comp (IntermediateField.inclusion hle)).toRingHom)
  refine ⟨((σ : ℂ →+* ℂ).toRatAlgHom).comp (IntermediateField.val ⊤), fun x hx hxM => ?_⟩
  have hx0 : x ∈ M₀ := IntermediateField.subset_adjoin ℚ _ ⟨hx, hxM⟩
  have h := hσ ⟨x, hx0⟩
  unfold cj TaylorLogMetric.liftM
  rw [dif_pos IntermediateField.mem_top, dif_pos hxM]
  exact h

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Simplify using `[ee]`.
-/
theorem ee_zero : ee 0 = 1 := by simp [ee]

/- English proof (translation)
Unfold `q1 gl3FieldFirst w0`. Rewrite using `[mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Simplify using `only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.add_im, Complex.one_im, Complex.I_re, Complex.I_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmQuadraticForm_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x = gl3FieldFirst Λ (w0 D * x) x := by
  unfold q1 gl3FieldFirst w0
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.add_im,
    Complex.one_im, Complex.I_re, Complex.I_im]
  ring

/- English proof (translation)
Rewrite using `[cmQuadraticForm_eq_alternatingForm]`. Unfold `gl3FieldFirst`. Rewrite using `[div_mul_eq_mul_div, Complex.div_ofNat_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmQuadraticForm_half_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x / 2 = gl3FieldFirst Λ (w0 D * x / 2) x := by
  rw [cmQuadraticForm_eq_alternatingForm]
  unfold gl3FieldFirst
  rw [div_mul_eq_mul_div, Complex.div_ofNat_im]
  ring

/- English proof (translation)
Rewrite using `[cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm]`. Unfold `gl3FieldFirst`. Rewrite using `[← add_div, ← add_div, ← add_div, ← Complex.add_im, ← Complex.add_im, ← Complex.add_im]`. Use `congr 2`. Simplify using `only [map_add, map_mul, map_natCast, map_ofNat]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmQuadraticForm_half_add_translation (D : D7) (Λ : AddSubgroup ℂ) (x l : ℂ) (m : ℕ) :
    q1 D Λ (x + 2 * (m : ℂ) * l) / 2 = q1 D Λ x / 2 + gl3FieldFirst Λ (w0 D * ((m : ℂ) * x)) l +
      gl3FieldFirst Λ (w0 D * l) ((m : ℂ) * x) + gl3FieldFirst Λ (w0 D * l) (((2 * m * m : ℕ) : ℂ) * l) := by
  rw [cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm]
  unfold gl3FieldFirst
  rw [← add_div, ← add_div, ← add_div, ← Complex.add_im, ← Complex.add_im, ← Complex.add_im]
  congr 2
  simp only [map_add, map_mul, map_natCast, map_ofNat]
  push_cast
  ring

/- English proof (translation)
Take `⟨hex, huniq, -, hadd, hmul, hord, -⟩` from `hS cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top`. Establish `hWP` using `hW cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top`. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Use `set Λ := lamOf D cc δ with hΛ`. Use `set Λ' := lamConj ⊤ ρ Λ with hΛ'`.

Establish `hm0 : (m₀ : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hmulw : ∀ t t', StarPt ⊤ ρ Λ t t' → StarPt ⊤ ρ Λ (w0 D * t) (w0 D * t')` using `fun t t' h => by`. Use `hmul a t t' h` as an intermediate fact. Rewrite `this` using `[ha]`. Then use the resulting hypothesis. Establish `hw : ∀ l ∈ Λ, w0 D * l ∈ Λ` using `fun l hl => by`.

Establish `h` using `hmulw l 0 (Or.inl ⟨hl, zero_mem _⟩)`. Break down `h with h | h` into its components or cases. Conclude with `h.1`. Conclude with `absurd (by rw [mul_zero]; exact zero_mem _) h.2.1`. Establish `hw' : ∀ l ∈ Λ', w0 D * l ∈ Λ'` using `fun l hl => by`.

Establish `h` using `hmulw 0 l (Or.inl ⟨zero_mem _, hl⟩)`. Break down `h with h | h` into its components or cases. Conclude with `h.2`. Conclude with `absurd (by rw [mul_zero]; exact zero_mem _) h.1`. Establish `hint : ∀ l ∈ Λ', ∀ l' ∈ Λ', ee (gl3FieldFirst Λ' l l') = 1` using `fun l hl l' hl' => by`.

Establish `h` using `hWP 0 0 l l' 1 one_pos (by simp) (by simp) (Or.inl ⟨by simp, by simpa using hl⟩) (Or.inl ⟨by simp, by simpa using hl'⟩) IntermediateField.mem_top`. Rewrite using `[← h]`. Establish `h0 : gl3FieldFirst Λ 0 0 = 0` using `by simp [gl3FieldFirst]`. Rewrite using `[h0, ee_zero]`. Unfold `cj TaylorLogMetric.liftM`.

Rewrite using `[dif_pos IntermediateField.mem_top]`. Conclude with `map_one ρ`. Establish `hnat : ∀ (A : AddSubgroup ℂ) (n : ℕ), ∀ l ∈ A, (n : ℂ) * l ∈ A` using `fun A n l hl => by`. Rewrite using `[← nsmul_eq_mul]`. Conclude with `nsmul_mem hl n`.

Establish `htn : ((4 * m₀ * m₀ : ℕ) : ℂ) * (x / (4 * (m₀ : ℂ))) = (m₀ : ℂ) * x`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take `⟨t', ht'⟩` from `hex (x / (4 * (m₀ : ℂ))) ⟨4 * m₀ * m₀, by positivity, htn ▸ hx⟩ (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)`. Use `set y : ℂ := 4 * (m₀ : ℂ) * t' with hy`.

Establish `hA2 : Adp1 ⊤ ρ Λ (2 * m₀) x y`. Establish `h` using `hadd _ _ _ _ ht' ht'`. Unfold `Adp1`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hA3 : Adp1 ⊤ ρ Λ (2 * m₀) (w0 D * x / 2) (w0 D * y / 2)`. Establish `h` using `hmulw _ _ ht'`. Unfold `Adp1`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hl` using `(huniq _ _ _ hA).1 hA2`. Establish `hμ : (m₀ : ℂ) * y ∈ Λ'`. Establish `h` using `(hord (4 * m₀ * m₀) _ _ ht').1 (htn ▸ hx)`.

Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hy]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set l : ℂ := x' / ((2 * m₀ : ℕ) : ℂ) - y / ((2 * m₀ : ℕ) : ℂ) with hldef`.

Establish `hx' : x' = y + 2 * (m₀ : ℂ) * l`. Rewrite using `[hldef]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hmain` using `hWP (w0 D * x / 2) x (w0 D * y / 2) y (2 * m₀) (by positivity) (by`. Use `hw _ hx using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Use the proof step `ring)`. Use the proof step `(by`.

Use `hnat Λ 2 _ hx using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Use the proof step `ring)`. Use `hA3 hA2 IntermediateField.mem_top`. Rewrite using `[hx', cmQuadraticForm_half_add_translation, ee_add, ee_add, ee_add, hint _ (hw' _ hμ) _ hl, hint _ (hw' _ hl) _ hμ, hint _ (hw' _ hl) _ (hnat Λ' _ _ hl), cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm, hmain]`.

Simplify using the standard rewrite rules.
-/
theorem phase_top (D : D7) (hS : galStar D) (hW : WeilPairingGaloisAlt D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hc : Crv D cc δ) (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ)
    (x x' : ℂ) (m₀ : ℕ) (hm : 0 < m₀) (hx : (m₀ : ℂ) * x ∈ lamOf D cc δ)
    (hA : Adp1 ⊤ ρ (lamOf D cc δ) (2 * m₀) x x') :
    cj ⊤ ρ (ee (q1 D (lamOf D cc δ) x / 2)) = ee (q1 D (lamConj ⊤ ρ (lamOf D cc δ)) x' / 2) := by
  obtain ⟨hex, huniq, -, hadd, hmul, hord, -⟩ :=
    hS cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  have hWP := hW cc δ hc ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  set Λ := lamOf D cc δ with hΛ
  set Λ' := lamConj ⊤ ρ Λ with hΛ'
  have hm0 : (m₀ : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmulw : ∀ t t', StarPt ⊤ ρ Λ t t' → StarPt ⊤ ρ Λ (w0 D * t) (w0 D * t') := fun t t' h => by
    have := hmul a t t' h
    rwa [ha] at this
  have hw : ∀ l ∈ Λ, w0 D * l ∈ Λ := fun l hl => by
    have h := hmulw l 0 (Or.inl ⟨hl, zero_mem _⟩)
    rcases h with h | h
    · exact h.1
    · exact absurd (by rw [mul_zero]; exact zero_mem _) h.2.1
  have hw' : ∀ l ∈ Λ', w0 D * l ∈ Λ' := fun l hl => by
    have h := hmulw 0 l (Or.inl ⟨zero_mem _, hl⟩)
    rcases h with h | h
    · exact h.2
    · exact absurd (by rw [mul_zero]; exact zero_mem _) h.1
  have hint : ∀ l ∈ Λ', ∀ l' ∈ Λ', ee (gl3FieldFirst Λ' l l') = 1 := fun l hl l' hl' => by
    have h := hWP 0 0 l l' 1 one_pos (by simp) (by simp)
      (Or.inl ⟨by simp, by simpa using hl⟩) (Or.inl ⟨by simp, by simpa using hl'⟩) IntermediateField.mem_top
    rw [← h]
    have h0 : gl3FieldFirst Λ 0 0 = 0 := by simp [gl3FieldFirst]
    rw [h0, ee_zero]
    unfold cj TaylorLogMetric.liftM
    rw [dif_pos IntermediateField.mem_top]
    exact map_one ρ
  have hnat : ∀ (A : AddSubgroup ℂ) (n : ℕ), ∀ l ∈ A, (n : ℂ) * l ∈ A := fun A n l hl => by
    rw [← nsmul_eq_mul]
    exact nsmul_mem hl n
  have htn : ((4 * m₀ * m₀ : ℕ) : ℂ) * (x / (4 * (m₀ : ℂ))) = (m₀ : ℂ) * x := by
    push_cast
    field_simp
  obtain ⟨t', ht'⟩ := hex (x / (4 * (m₀ : ℂ))) ⟨4 * m₀ * m₀, by positivity, htn ▸ hx⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  set y : ℂ := 4 * (m₀ : ℂ) * t' with hy
  have hA2 : Adp1 ⊤ ρ Λ (2 * m₀) x y := by
    have h := hadd _ _ _ _ ht' ht'
    unfold Adp1
    convert h using 1
    · push_cast
      field_simp
      ring
    · rw [hy]
      push_cast
      field_simp
      ring
  have hA3 : Adp1 ⊤ ρ Λ (2 * m₀) (w0 D * x / 2) (w0 D * y / 2) := by
    have h := hmulw _ _ ht'
    unfold Adp1
    convert h using 1
    · push_cast
      field_simp
      ring
    · rw [hy]
      push_cast
      field_simp
      ring
  have hl := (huniq _ _ _ hA).1 hA2
  have hμ : (m₀ : ℂ) * y ∈ Λ' := by
    have h := (hord (4 * m₀ * m₀) _ _ ht').1 (htn ▸ hx)
    convert h using 1
    rw [hy]
    push_cast
    ring
  set l : ℂ := x' / ((2 * m₀ : ℕ) : ℂ) - y / ((2 * m₀ : ℕ) : ℂ) with hldef
  have hx' : x' = y + 2 * (m₀ : ℂ) * l := by
    rw [hldef]
    push_cast
    field_simp
    ring
  have hmain := hWP (w0 D * x / 2) x (w0 D * y / 2) y (2 * m₀) (by positivity)
    (by
      convert hw _ hx using 1
      push_cast
      ring)
    (by
      convert hnat Λ 2 _ hx using 1
      push_cast
      ring)
    hA3 hA2 IntermediateField.mem_top
  rw [hx', cmQuadraticForm_half_add_translation, ee_add, ee_add, ee_add, hint _ (hw' _ hμ) _ hl, hint _ (hw' _ hl) _ hμ,
    hint _ (hw' _ hl) _ (hnat Λ' _ _ hl), cmQuadraticForm_half_eq_alternatingForm, cmQuadraticForm_half_eq_alternatingForm, hmain]
  simp

/- English proof (translation)
Introduce `cc δ hc`. Use `⟨fun x => cmQuadraticForm_eq_alternatingForm D _ x, fun M ρ hK h2 h3 x x' m₀ hm hx hA he => ?_⟩` and prove the remaining obligations. Use `set Λ := lamOf D cc δ with hΛ`. Establish `hKc : Countable D.host.K` using `Finsupp.Countable.of_moduleFinite (R := ℚ)`. Set `S : Set ℂ` to `Set.range (fun a : D.host.K => D.host.φ₀ (a : D.host.E)) ∪ {g2 Λ, g3 Λ, wpF Λ (x / ((2 * m₀ : ℕ) : ℂ)), wpD Λ (x / ((2 * m₀ : ℕ) : ℂ)), ee (q1 D Λ x / 2)}`.

Establish `hSc : S.Countable` using `(Set.countable_range _).union (Set.toFinite _).countable`. Take `⟨σ, hσ⟩` from `exists_top_extension M ρ S hSc`. Establish `hK' : FixK D ⊤ σ` using `fun a => ⟨IntermediateField.mem_top, by rw [hσ _ (Or.inl ⟨a, rfl⟩) (hK a).1, (hK a).2]⟩`. Establish `hl : lamConj ⊤ σ Λ = lamConj M ρ Λ`. Establish `e2` using `hσ (g2 Λ) (Or.inr (by simp)) h2`.

Establish `e3` using `hσ (g3 Λ) (Or.inr (by simp)) h3`. Unfold `cj at e2 e3`. Unfold `lamConj`. Rewrite using `[e2, e3]`. Establish `hA' : Adp1 ⊤ σ Λ (2 * m₀) x x'`.

Unfold `Adp1 StarPt at hA ⊢`. Rewrite using `[hl]`. Break down `hA with h | ⟨h1, h2', h3', h4, h5, h6⟩` into its components or cases. Conclude with `Or.inl h`. Use `Or.inr ⟨h1, h2', IntermediateField.mem_top, IntermediateField.mem_top, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[h5, hσ _ (Or.inr (by simp)) h3']`. Rewrite using `[h6, hσ _ (Or.inr (by simp)) h4]`. Establish `h` using `phase_top D hS hW cc δ hc σ hK' x x' m₀ hm hx hA'`. Rewrite `h` using `[← hΛ, hl, hσ _ (Or.inr (by simp)) he]`. Conclude with `h`.
-/
theorem galPh1_of (D : D7) (hS : galStar D) (hW : WeilPairingGaloisAlt D) : galPh1 D := by
  intro cc δ hc
  refine ⟨fun x => cmQuadraticForm_eq_alternatingForm D _ x, fun M ρ hK h2 h3 x x' m₀ hm hx hA he => ?_⟩
  set Λ := lamOf D cc δ with hΛ
  have hKc : Countable D.host.K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let S : Set ℂ := Set.range (fun a : D.host.K => D.host.φ₀ (a : D.host.E)) ∪
    {g2 Λ, g3 Λ, wpF Λ (x / ((2 * m₀ : ℕ) : ℂ)), wpD Λ (x / ((2 * m₀ : ℕ) : ℂ)), ee (q1 D Λ x / 2)}
  have hSc : S.Countable := (Set.countable_range _).union (Set.toFinite _).countable
  obtain ⟨σ, hσ⟩ := exists_top_extension M ρ S hSc
  have hK' : FixK D ⊤ σ := fun a =>
    ⟨IntermediateField.mem_top, by rw [hσ _ (Or.inl ⟨a, rfl⟩) (hK a).1, (hK a).2]⟩
  have hl : lamConj ⊤ σ Λ = lamConj M ρ Λ := by
    have e2 := hσ (g2 Λ) (Or.inr (by simp)) h2
    have e3 := hσ (g3 Λ) (Or.inr (by simp)) h3
    unfold cj at e2 e3
    unfold lamConj
    rw [e2, e3]
  have hA' : Adp1 ⊤ σ Λ (2 * m₀) x x' := by
    unfold Adp1 StarPt at hA ⊢
    rw [hl]
    rcases hA with h | ⟨h1, h2', h3', h4, h5, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2', IntermediateField.mem_top, IntermediateField.mem_top, ?_, ?_⟩
      · rw [h5, hσ _ (Or.inr (by simp)) h3']
      · rw [h6, hσ _ (Or.inr (by simp)) h4]
  have h := phase_top D hS hW cc δ hc σ hK' x x' m₀ hm hx hA'
  rw [← hΛ, hl, hσ _ (Or.inr (by simp)) he] at h
  exact h

/- English proof (translation)
Introduce `D` and use `galPh1_of D (GlobalTheory.T.galStar_complexMultiplication_points D) (GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion D)`.
-/
theorem galPh1_all : ∀ D : D7, galPh1 D := fun D =>
  galPh1_of D (GlobalTheory.T.galStar_complexMultiplication_points D) (GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion D)

end GlobalTheory.QuadPhase
