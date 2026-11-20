import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Formalism.LocalToGlobal.GlobalTheory.GL2.TotallyComplexOfNoReal

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `infer_instance`.
-/
theorem finite_realEmbeddings : Finite (F →+* ℝ) := by
  infer_instance

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨c, hc0, hc⟩ : ∃ c : 𝓞 F, c ≠ 0 ∧ c * a - 1 ∈ 𝔣 := by`. Establish `h1 : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ 𝔣` using `by rw [haq]; exact Submodule.mem_top`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 h1`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Distinguish the cases in `h : c = 0`.

Substitute `h` using the available equality. Establish `hz1 : (1 : 𝓞 F) ∈ 𝔣` using `by rw [← hyz]; simpa using hz`. Conclude with `⟨1, one_ne_zero, by simpa using 𝔣.mul_mem_left (1 * a - 1) hz1⟩`. Use `⟨c, h, ?_⟩` and prove the remaining obligations. Establish `: c * a - 1 = -z` using `by rw [← hyz]; ring`.

Rewrite using `[this]`. Conclude with `𝔣.neg_mem hz`. Establish `qb : Ideal.Quotient.mk 𝔣 b = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk 𝔣)]`. Conclude with `Ideal.Quotient.eq.2 hb1`.

Establish `qb' : Ideal.Quotient.mk 𝔣 b' = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk 𝔣)]`. Conclude with `Ideal.Quotient.eq.2 hb1'`. Establish `qa : Ideal.Quotient.mk 𝔣 a' = Ideal.Quotient.mk 𝔣 a` using `(Ideal.Quotient.eq.2 haa).symm`. Establish `qc : Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a = 1`.

Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk 𝔣)]`. Conclude with `Ideal.Quotient.eq.2 hc`. Establish `same : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → (0 < x ↔ 0 < y) → 0 < x * y`. Introduce `x y hx hy hxy`. Break down `lt_or_gt_of_ne hx with h | h` into its components or cases.

Establish `hy' : y < 0` using `lt_of_le_of_ne (not_lt.1 (fun h' => absurd (hxy.2 h') (not_lt.2 h.le))) hy`. Conclude with `mul_pos_of_neg_of_neg h hy'`. Conclude with `mul_pos h (hxy.1 h)`. Establish `coe0 : ∀ x : 𝓞 F, x ≠ 0 → ∀ σ : F →+* ℝ, σ (x : F) ≠ 0`. Introduce `x hx σ`.

Conclude with `(map_ne_zero σ).2 (by exact_mod_cast hx)`. Use `⟨(a * b' * c) ^ 2, a' * b * a * b' * c ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `pow_ne_zero 2 (mul_ne_zero (mul_ne_zero ha0 hb0') hc0)`. Conclude with `mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0' hb0) ha0) hb0') (pow_ne_zero 2 hc0)`. Apply `Ideal.Quotient.eq.1` to reduce the goal to its premises.

Simplify using `only [map_pow, map_mul, map_one, qb']`. Take the linear combination `(Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc`. Apply `Ideal.Quotient.eq.1` to reduce the goal to its premises. Simplify using `only [map_pow, map_mul, map_one, qb, qb', qa]`. Take the linear combination `(Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc`.

Introduce `σ`. Prove the components needed by the constructor for the conclusion. Establish `hx` using `coe0 _ (mul_ne_zero (mul_ne_zero ha0 hb0') hc0) σ`. Establish `: σ (((a * b' * c) ^ 2 : 𝓞 F) : F) = (σ ((a * b' * c : 𝓞 F) : F)) ^ 2` using `by push_cast; simp only [map_pow]`. Rewrite using `[this]`.

Conclude with `lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))`. Establish `h1` using `coe0 _ (mul_ne_zero ha0 hb0) σ`. Establish `h2` using `coe0 _ (mul_ne_zero ha0' hb0') σ`. Establish `h3` using `coe0 _ hc0 σ`. Establish `: σ ((a' * b * a * b' * c ^ 2 : 𝓞 F) : F) = σ ((a * b : 𝓞 F) : F) * σ ((a' * b' : 𝓞 F) : F) * (σ (c : F)) ^ 2` using `by push_cast; simp only [map_mul, map_pow]; ring`.

Rewrite using `[this]`. Conclude with `mul_pos (same _ _ h1 h2 (hs σ)) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h3)))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, Ideal.span_singleton_mul_span_singleton]`. Use `congr 2`.

Put the polynomial expressions in normal form. Use `_ = Ideal.span {a * b' ^ 2 * c ^ 2} * (Ideal.span {b} * R) := by rw [e1]`. Use `_ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {b'} * R) := by`. Rewrite using `[← mul_assoc, ← mul_assoc, Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]`. Use `congr 3`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {a'} * J) := by rw [e2]`. Use `_ = Ideal.span {a' * b * a * b' * c ^ 2} * J := by`. Rewrite using `[← mul_assoc, Ideal.span_singleton_mul_span_singleton]`. Use `congr 3`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rayRel_of_signs (𝔣 I J R : Ideal (𝓞 F)) (a a' b b' : 𝓞 F) (ha0 : a ≠ 0) (ha0' : a' ≠ 0) (hb0 : b ≠ 0) (hb0' : b' ≠ 0)
    (hb1 : b - 1 ∈ 𝔣) (hb1' : b' - 1 ∈ 𝔣) (haq : Ideal.span {a} ⊔ 𝔣 = ⊤) (haa : a - a' ∈ 𝔣)
    (hs : ∀ σ : F →+* ℝ, 0 < σ ((a * b : 𝓞 F) : F) ↔ 0 < σ ((a' * b' : 𝓞 F) : F))
    (e1 : Ideal.span {a} * I = Ideal.span {b} * R) (e2 : Ideal.span {a'} * J = Ideal.span {b'} * R) :
    RayRel F 𝔣 I J := by
  obtain ⟨c, hc0, hc⟩ : ∃ c : 𝓞 F, c ≠ 0 ∧ c * a - 1 ∈ 𝔣 := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ 𝔣 := by rw [haq]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    by_cases h : c = 0
    · subst h
      have hz1 : (1 : 𝓞 F) ∈ 𝔣 := by rw [← hyz]; simpa using hz
      exact ⟨1, one_ne_zero, by simpa using 𝔣.mul_mem_left (1 * a - 1) hz1⟩
    · refine ⟨c, h, ?_⟩
      have : c * a - 1 = -z := by rw [← hyz]; ring
      rw [this]; exact 𝔣.neg_mem hz
  have qb : Ideal.Quotient.mk 𝔣 b = 1 := by
    rw [← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hb1
  have qb' : Ideal.Quotient.mk 𝔣 b' = 1 := by
    rw [← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hb1'
  have qa : Ideal.Quotient.mk 𝔣 a' = Ideal.Quotient.mk 𝔣 a := (Ideal.Quotient.eq.2 haa).symm
  have qc : Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hc
  have same : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → (0 < x ↔ 0 < y) → 0 < x * y := by
    intro x y hx hy hxy
    rcases lt_or_gt_of_ne hx with h | h
    · have hy' : y < 0 := lt_of_le_of_ne (not_lt.1 (fun h' => absurd (hxy.2 h') (not_lt.2 h.le))) hy
      exact mul_pos_of_neg_of_neg h hy'
    · exact mul_pos h (hxy.1 h)
  have coe0 : ∀ x : 𝓞 F, x ≠ 0 → ∀ σ : F →+* ℝ, σ (x : F) ≠ 0 := by
    intro x hx σ
    exact (map_ne_zero σ).2 (by exact_mod_cast hx)
  refine ⟨(a * b' * c) ^ 2, a' * b * a * b' * c ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero ha0 hb0') hc0)
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0' hb0) ha0) hb0') (pow_ne_zero 2 hc0)
  · apply Ideal.Quotient.eq.1
    simp only [map_pow, map_mul, map_one, qb']
    linear_combination (Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc
  · apply Ideal.Quotient.eq.1
    simp only [map_pow, map_mul, map_one, qb, qb', qa]
    linear_combination (Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc
  · intro σ
    constructor
    · have hx := coe0 _ (mul_ne_zero (mul_ne_zero ha0 hb0') hc0) σ
      have : σ (((a * b' * c) ^ 2 : 𝓞 F) : F) = (σ ((a * b' * c : 𝓞 F) : F)) ^ 2 := by
        push_cast; simp only [map_pow]
      rw [this]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
    · have h1 := coe0 _ (mul_ne_zero ha0 hb0) σ
      have h2 := coe0 _ (mul_ne_zero ha0' hb0') σ
      have h3 := coe0 _ hc0 σ
      have : σ ((a' * b * a * b' * c ^ 2 : 𝓞 F) : F) =
          σ ((a * b : 𝓞 F) : F) * σ ((a' * b' : 𝓞 F) : F) * (σ (c : F)) ^ 2 := by
        push_cast; simp only [map_mul, map_pow]; ring
      rw [this]
      exact mul_pos (same _ _ h1 h2 (hs σ)) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h3)))
  · calc Ideal.span {(a * b' * c) ^ 2} * I
        = Ideal.span {a * b' ^ 2 * c ^ 2} * (Ideal.span {a} * I) := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton]; congr 2; ring_nf
      _ = Ideal.span {a * b' ^ 2 * c ^ 2} * (Ideal.span {b} * R) := by rw [e1]
      _ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {b'} * R) := by
          rw [← mul_assoc, ← mul_assoc, Ideal.span_singleton_mul_span_singleton,
            Ideal.span_singleton_mul_span_singleton]; congr 3; ring
      _ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {a'} * J) := by rw [e2]
      _ = Ideal.span {a' * b * a * b' * c ^ 2} * J := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton]; congr 3; ring

/- English proof (translation)
Use `haveI : Finite (F →+* ℝ) := finite_realEmbeddings`. Use `haveI : Finite (𝓞 F ⧸ 𝔣) := (Ideal.absNorm_ne_zero_iff 𝔣).1 (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`. Establish `key : ∀ A : Ideal (𝓞 F), A ≠ ⊥ → ∃ B : Ideal (𝓞 F), B ≠ ⊥ ∧ B ⊔ 𝔣 = ⊤ ∧ ∃ r : 𝓞 F, r ≠ 0 ∧ A * B = Ideal.span {r}`. Introduce `A hA`. Establish `hA' : A ≠ 0` using `by rwa [Ne, Ideal.zero_eq_bot]`.

Establish `h𝔣' : 𝔣 ≠ 0` using `by rwa [Ne, Ideal.zero_eq_bot]`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 F)`. Establish `hM0 : M ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot]`. Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)`.

Establish `hAg : A * (𝔣 * M) ≠ 0` using `mul_ne_zero hA' (mul_ne_zero h𝔣' hM0)`. Take `⟨r, hr⟩` from `IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : A * (𝔣 * M) ≤ A) hAg`. Take `⟨B, hB⟩ : A ∣ Ideal.span {r}` from `Ideal.dvd_iff_le.2 ((le_sup_right : Ideal.span {r} ≤ A * (𝔣 * M) ⊔ Ideal.span {r}).trans hr.le)`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hr` using `[Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq]`. Establish `h1 : 𝔣 * M = ⊤`. Apply `mul_left_cancel₀ hA'` to reduce the goal to its premises. Rewrite using `[hr, Ideal.mul_top]`. Establish `h2 : 𝔣 * M ≤ M` using `Ideal.mul_le_inf.trans inf_le_right`.

Rewrite `h2` using `[h1]`. Conclude with `hM.ne_top (top_le_iff.1 h2)`. Use `⟨B, ?_, ?_, r, hr0, hB.symm⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hB` using `[Ideal.mul_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hr0 hB`. Establish `h1 : A * (𝔣 * M ⊔ B) = A * ⊤`. Rewrite using `[Ideal.mul_sup, ← hB, hr, Ideal.mul_top]`. Establish `h2 : 𝔣 * M ⊔ B = ⊤` using `mul_left_cancel₀ hA' h1`. Rewrite using `[eq_top_iff, ← h2]`.

Conclude with `sup_le ((Ideal.mul_le_inf.trans inf_le_left).trans le_sup_right) le_sup_left`. Establish `rep : ∀ c : ClassGroup (𝓞 F), ∃ P : Ideal (𝓞 F), ∃ hP : P ∈ nonZeroDivisors (Ideal (𝓞 F)), P ⊔ 𝔣 = ⊤ ∧ ClassGroup.mk0 ⟨P, hP⟩ = c`. Introduce `c`. Take `⟨⟨A, hA⟩, hAc⟩` from `ClassGroup.mk0_surjective c⁻¹`. Establish `hA0 : A ≠ ⊥`.

Use `nonZeroDivisors.ne_zero hA` as an intermediate fact. Rewrite `this` using `[Ne, Ideal.zero_eq_bot]`. Then use the resulting hypothesis. Take `⟨B, hB0, hBf, r, hr0, hAB⟩` from `key A hA0`. Establish `hBm : B ∈ nonZeroDivisors (Ideal (𝓞 F))` using `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.zero_eq_bot])`. Use `⟨B, hBm, hBf, ?_⟩` and prove the remaining obligations.

Establish `hABm : A * B ∈ nonZeroDivisors (Ideal (𝓞 F))` using `Submonoid.mul_mem _ hA hBm`. Establish `h1 : ClassGroup.mk0 ⟨A * B, hABm⟩ = 1` using `(ClassGroup.mk0_eq_one_iff hABm).2 ⟨⟨r, hAB⟩⟩`. Establish `h2 : ClassGroup.mk0 ⟨A * B, hABm⟩ = ClassGroup.mk0 ⟨A, hA⟩ * ClassGroup.mk0 ⟨B, hBm⟩`. Rewrite using `[← map_mul]`. Both sides reduce to the same expression.

Rewrite `h1` using `[h2, hAc]`. Conclude with `(inv_mul_eq_one.1 h1).symm`. Use `choose P hPm hPf hPc using rep`. Establish `hPcop : ∀ c, CoprimeTo F 𝔣 (P c)`. Introduce `c`.

Use `nonZeroDivisors.ne_zero (hPm c)` as an intermediate fact. Rewrite `this` using `[Ne, Ideal.zero_eq_bot]`. Conclude with `(show P c ≠ ⊥ ∧ P c ⊔ 𝔣 = ⊤ from ⟨this, hPf c⟩)`. Establish `hcov : ∀ I : Ideal (𝓞 F), CoprimeTo F 𝔣 I → ∃ (c : ClassGroup (𝓞 F)) (a b : 𝓞 F), a ≠ 0 ∧ b ≠ 0 ∧ b - 1 ∈ 𝔣 ∧ Ideal.span {a} ⊔ 𝔣 = ⊤ ∧ Ideal.span {a} * I = Ideal.span {b} * P c`. Introduce `I hI`.

Establish `hI' : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤` using `hI`. Establish `hIm : I ∈ nonZeroDivisors (Ideal (𝓞 F))` using `mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.zero_eq_bot]; exact hI'.1)`. Take `⟨x, y, hx, hy, hxy⟩` from `ClassGroup.mk0_eq_mk0_iff.1 (hPc (ClassGroup.mk0 ⟨I, hIm⟩)).symm`. Take `⟨a, b, ha, hb, hb1, haq, he⟩` from `Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.exists_rel_of_class 𝔣 I (P (ClassGroup.mk0 ⟨I, hIm⟩)) hI (hPcop _) x y hx hy hxy`. Conclude with `⟨_, a, b, ha, hb, hb1, haq, he⟩`.

Use `choose cl a b ha hb hb1 haq he using hcov`. Take `⟨κ, hκ⟩ : ∃ κ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} → ClassGroup (𝓞 F) × (𝓞 F ⧸ 𝔣) × Set (F →+* ℝ), κ = fun I => (cl I.1 I.2, Ideal.Quotient.mk 𝔣 (a I.1 I.2), {σ : F →+* ℝ | 0 < σ ((a I.1 I.2 * b I.1 I.2 : 𝓞 F) : F)})` from `⟨_, rfl⟩`. Establish `hrel : ∀ I J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = κ J → RayRel F 𝔣 I.1 J.1`. Introduce `I J h`. Rewrite `h` using `[hκ]`.

Simplify using `only [Prod.mk.injEq] at h`. Take `⟨hc, hq, hs⟩` from `h`. Use `rayRel_of_signs 𝔣 I.1 J.1 (P (cl I.1 I.2)) (a I.1 I.2) (a J.1 J.2) (b I.1 I.2) (b J.1 J.2) (ha _ _) (ha _ _) (hb _ _) (hb _ _) (hb1 _ _) (hb1 _ _) (haq _ _) (Ideal.Quotient.eq.1 hq) (fun σ => Set.ext_iff.1 hs σ) (he _ _) ?_` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `he _ _`.

Use `haveI : Nonempty {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} := ⟨⟨⊤, show (⊤ : Ideal (𝓞 F)) ≠ ⊥ ∧ (⊤ : Ideal (𝓞 F)) ⊔ 𝔣 = ⊤ from ⟨top_ne_bot, top_sup_eq _⟩⟩⟩`. Establish `hfin : (Set.range κ).Finite` using `Set.toFinite _`. Establish `hne : ∀ d ∈ Set.range κ, ∃ I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = d` using `fun d hd => hd`. Use `choose! g hg using hne`. Choose the witnesses or unpack the hypotheses as in `⟨T, hTc, hTcov⟩ : ∃ T : Finset (Ideal (𝓞 F)), (∀ t ∈ T, CoprimeTo F 𝔣 t) ∧ ∀ I, CoprimeTo F 𝔣 I → ∃ t ∈ T, RayRel F 𝔣 I t := by`.

Use `⟨hfin.toFinset.image (fun d => (g d).1), ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨d, -, rfl⟩` from `Finset.mem_image.1 ht`. Conclude with `(g d).2`. Introduce `I hI`.

Establish `hd : κ ⟨I, hI⟩ ∈ Set.range κ` using `⟨_, rfl⟩`. Use `⟨(g (κ ⟨I, hI⟩)).1, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hd), ?_⟩` and prove the remaining obligations. Conclude with `hrel ⟨I, hI⟩ (g (κ ⟨I, hI⟩)) (hg _ hd).symm`. Take `⟨f, hf⟩ : ∃ f : Ideal (𝓞 F) → Ideal (𝓞 F), f = fun t => Classical.epsilon (fun s => s ∈ T ∧ RayRel F 𝔣 t s)` from `⟨_, rfl⟩`. Establish `hfT : ∀ t ∈ T, f t ∈ T ∧ RayRel F 𝔣 t (f t)`.

Introduce `t ht`. Rewrite using `[hf]`. Conclude with `Classical.epsilon_spec (p := fun s => s ∈ T ∧ RayRel F 𝔣 t s) ⟨t, ht, rayRel_refl t⟩`. Establish `hfeq : ∀ t t', RayRel F 𝔣 t t' → f t = f t'`. Introduce `t t' h`.

Simplify using `only [hf]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hs, h'⟩`. Conclude with `⟨hs, rayRel_trans (rayRel_symm h) h'⟩`. Introduce and unpack `⟨hs, h'⟩`. Conclude with `⟨hs, rayRel_trans h h'⟩`. Use `⟨T.image f, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s hs`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hs`. Conclude with `hTc _ (hfT t ht).1`. Introduce `s hs s' hs' h`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hs`.

Take `⟨t', ht', rfl⟩` from `Finset.mem_image.1 hs'`. Apply `hfeq` to reduce the goal to its premises. Conclude with `rayRel_trans (hfT t ht).2 (rayRel_trans h (rayRel_symm (hfT t' ht').2))`. Introduce `I hI`. Take `⟨t, ht, hIt⟩` from `hTcov I hI`.

Conclude with `⟨f t, Finset.mem_image_of_mem _ ht, rayRel_trans hIt (hfT t ht).2⟩`.
-/
theorem finRay (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) :
    ∃ S : Finset (Ideal (𝓞 F)), (∀ a ∈ S, CoprimeTo F 𝔣 a) ∧ (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) ∧
      ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a := by
  classical
  haveI : Finite (F →+* ℝ) := finite_realEmbeddings
  haveI : Finite (𝓞 F ⧸ 𝔣) :=
    (Ideal.absNorm_ne_zero_iff 𝔣).1 (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have key : ∀ A : Ideal (𝓞 F), A ≠ ⊥ → ∃ B : Ideal (𝓞 F), B ≠ ⊥ ∧ B ⊔ 𝔣 = ⊤ ∧
      ∃ r : 𝓞 F, r ≠ 0 ∧ A * B = Ideal.span {r} := by
    intro A hA
    have hA' : A ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
    have h𝔣' : 𝔣 ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    have hM0 : M ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot]
      exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
    have hAg : A * (𝔣 * M) ≠ 0 := mul_ne_zero hA' (mul_ne_zero h𝔣' hM0)
    obtain ⟨r, hr⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : A * (𝔣 * M) ≤ A) hAg
    obtain ⟨B, hB⟩ : A ∣ Ideal.span {r} :=
      Ideal.dvd_iff_le.2 ((le_sup_right : Ideal.span {r} ≤ A * (𝔣 * M) ⊔ Ideal.span {r}).trans hr.le)
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq] at hr
      have h1 : 𝔣 * M = ⊤ := by
        apply mul_left_cancel₀ hA'
        rw [hr, Ideal.mul_top]
      have h2 : 𝔣 * M ≤ M := Ideal.mul_le_inf.trans inf_le_right
      rw [h1] at h2
      exact hM.ne_top (top_le_iff.1 h2)
    refine ⟨B, ?_, ?_, r, hr0, hB.symm⟩
    · rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hB
      exact hr0 hB
    · have h1 : A * (𝔣 * M ⊔ B) = A * ⊤ := by
        rw [Ideal.mul_sup, ← hB, hr, Ideal.mul_top]
      have h2 : 𝔣 * M ⊔ B = ⊤ := mul_left_cancel₀ hA' h1
      rw [eq_top_iff, ← h2]
      exact sup_le ((Ideal.mul_le_inf.trans inf_le_left).trans le_sup_right) le_sup_left
  have rep : ∀ c : ClassGroup (𝓞 F), ∃ P : Ideal (𝓞 F), ∃ hP : P ∈ nonZeroDivisors (Ideal (𝓞 F)),
      P ⊔ 𝔣 = ⊤ ∧ ClassGroup.mk0 ⟨P, hP⟩ = c := by
    intro c
    obtain ⟨⟨A, hA⟩, hAc⟩ := ClassGroup.mk0_surjective c⁻¹
    have hA0 : A ≠ ⊥ := by
      have := nonZeroDivisors.ne_zero hA
      rwa [Ne, Ideal.zero_eq_bot] at this
    obtain ⟨B, hB0, hBf, r, hr0, hAB⟩ := key A hA0
    have hBm : B ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.zero_eq_bot])
    refine ⟨B, hBm, hBf, ?_⟩
    have hABm : A * B ∈ nonZeroDivisors (Ideal (𝓞 F)) := Submonoid.mul_mem _ hA hBm
    have h1 : ClassGroup.mk0 ⟨A * B, hABm⟩ = 1 := (ClassGroup.mk0_eq_one_iff hABm).2 ⟨⟨r, hAB⟩⟩
    have h2 : ClassGroup.mk0 ⟨A * B, hABm⟩ = ClassGroup.mk0 ⟨A, hA⟩ * ClassGroup.mk0 ⟨B, hBm⟩ := by
      rw [← map_mul]; rfl
    rw [h2, hAc] at h1
    exact (inv_mul_eq_one.1 h1).symm
  choose P hPm hPf hPc using rep
  have hPcop : ∀ c, CoprimeTo F 𝔣 (P c) := by
    intro c
    have := nonZeroDivisors.ne_zero (hPm c)
    rw [Ne, Ideal.zero_eq_bot] at this
    exact (show P c ≠ ⊥ ∧ P c ⊔ 𝔣 = ⊤ from ⟨this, hPf c⟩)
  have hcov : ∀ I : Ideal (𝓞 F), CoprimeTo F 𝔣 I → ∃ (c : ClassGroup (𝓞 F)) (a b : 𝓞 F),
      a ≠ 0 ∧ b ≠ 0 ∧ b - 1 ∈ 𝔣 ∧ Ideal.span {a} ⊔ 𝔣 = ⊤ ∧
        Ideal.span {a} * I = Ideal.span {b} * P c := by
    intro I hI
    have hI' : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤ := hI
    have hIm : I ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.zero_eq_bot]; exact hI'.1)
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hPc (ClassGroup.mk0 ⟨I, hIm⟩)).symm
    obtain ⟨a, b, ha, hb, hb1, haq, he⟩ :=
      Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.exists_rel_of_class 𝔣 I (P (ClassGroup.mk0 ⟨I, hIm⟩)) hI (hPcop _) x y hx hy hxy
    exact ⟨_, a, b, ha, hb, hb1, haq, he⟩
  choose cl a b ha hb hb1 haq he using hcov
  obtain ⟨κ, hκ⟩ : ∃ κ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} →
      ClassGroup (𝓞 F) × (𝓞 F ⧸ 𝔣) × Set (F →+* ℝ),
      κ = fun I => (cl I.1 I.2, Ideal.Quotient.mk 𝔣 (a I.1 I.2),
        {σ : F →+* ℝ | 0 < σ ((a I.1 I.2 * b I.1 I.2 : 𝓞 F) : F)}) := ⟨_, rfl⟩
  have hrel : ∀ I J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = κ J → RayRel F 𝔣 I.1 J.1 := by
    intro I J h
    rw [hκ] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hc, hq, hs⟩ := h
    refine rayRel_of_signs 𝔣 I.1 J.1 (P (cl I.1 I.2)) (a I.1 I.2) (a J.1 J.2) (b I.1 I.2) (b J.1 J.2)
      (ha _ _) (ha _ _) (hb _ _) (hb _ _) (hb1 _ _) (hb1 _ _) (haq _ _) (Ideal.Quotient.eq.1 hq)
      (fun σ => Set.ext_iff.1 hs σ) (he _ _) ?_
    rw [hc]; exact he _ _
  haveI : Nonempty {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} :=
    ⟨⟨⊤, show (⊤ : Ideal (𝓞 F)) ≠ ⊥ ∧ (⊤ : Ideal (𝓞 F)) ⊔ 𝔣 = ⊤ from ⟨top_ne_bot, top_sup_eq _⟩⟩⟩
  have hfin : (Set.range κ).Finite := Set.toFinite _
  have hne : ∀ d ∈ Set.range κ, ∃ I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = d := fun d hd => hd
  choose! g hg using hne
  obtain ⟨T, hTc, hTcov⟩ : ∃ T : Finset (Ideal (𝓞 F)), (∀ t ∈ T, CoprimeTo F 𝔣 t) ∧
      ∀ I, CoprimeTo F 𝔣 I → ∃ t ∈ T, RayRel F 𝔣 I t := by
    refine ⟨hfin.toFinset.image (fun d => (g d).1), ?_, ?_⟩
    · intro t ht
      obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 ht
      exact (g d).2
    · intro I hI
      have hd : κ ⟨I, hI⟩ ∈ Set.range κ := ⟨_, rfl⟩
      refine ⟨(g (κ ⟨I, hI⟩)).1, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hd), ?_⟩
      exact hrel ⟨I, hI⟩ (g (κ ⟨I, hI⟩)) (hg _ hd).symm
  obtain ⟨f, hf⟩ : ∃ f : Ideal (𝓞 F) → Ideal (𝓞 F),
      f = fun t => Classical.epsilon (fun s => s ∈ T ∧ RayRel F 𝔣 t s) := ⟨_, rfl⟩
  have hfT : ∀ t ∈ T, f t ∈ T ∧ RayRel F 𝔣 t (f t) := by
    intro t ht
    rw [hf]
    exact Classical.epsilon_spec (p := fun s => s ∈ T ∧ RayRel F 𝔣 t s) ⟨t, ht, rayRel_refl t⟩
  have hfeq : ∀ t t', RayRel F 𝔣 t t' → f t = f t' := by
    intro t t' h
    simp only [hf]
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨hs, h'⟩
      exact ⟨hs, rayRel_trans (rayRel_symm h) h'⟩
    · rintro ⟨hs, h'⟩
      exact ⟨hs, rayRel_trans h h'⟩
  refine ⟨T.image f, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    exact hTc _ (hfT t ht).1
  · intro s hs s' hs' h
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs'
    apply hfeq
    exact rayRel_trans (hfT t ht).2 (rayRel_trans h (rayRel_symm (hfT t' ht').2))
  · intro I hI
    obtain ⟨t, ht, hIt⟩ := hTcov I hI
    exact ⟨f t, Finset.mem_image_of_mem _ ht, rayRel_trans hIt (hfT t ht).2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
