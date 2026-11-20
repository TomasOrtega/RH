import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.UCls.NormOneMod

/- English proof (translation)
Proceed by induction on `hk using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Take `⟨u, b, hb, h⟩` from `(strong_approximation_mod_nat F M hM).2 a ha`. Establish `hu : IsIntegral ℤ (algebraMap F E (u : F))` using `u.isIntegral_coe.algebraMap`.

Use `⟨⟨algebraMap F E (u : F) * x, hu.mul hx⟩, b ⊗ₜ x, tmul_mem_adelicCompletion_of_integral F hb hx, ?_⟩` and prove the remaining obligations. Rewrite using `[h, TensorProduct.add_tmul, TensorProduct.smul_tmul']`. Use `congr 1`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]`. Both sides reduce to the same expression.

Consider the case `zero => exact ⟨0, 0, zero_mem _, by simp⟩`. Consider the case `add y z _ _ h1 h2`. Take `⟨x, y, hy, rfl⟩` from `h1`. Take `⟨x', y', hy', rfl⟩` from `h2`. Use `⟨x + x', y + y', add_mem hy hy', ?_⟩` and prove the remaining obligations.

Establish `: ((x + x' : 𝓞 E) : E) = x + x'` using `by simp`. Rewrite using `[this, TensorProduct.tmul_add, smul_add]`. Normalize the expressions using the abelian group laws. Consider the case `neg y _ h1`. Take `⟨x, y, hy, rfl⟩` from `h1`.

Use `⟨-x, -y, neg_mem hy, ?_⟩` and prove the remaining obligations. Establish `: ((-x : 𝓞 E) : E) = -x` using `by simp`. Rewrite using `[this, TensorProduct.tmul_neg, smul_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_integer_add_nsmul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (M : ℕ) (hM : 1 ≤ M) (k : RA F E) (hk : k ∈ hat1 F {x : E | IsIntegral ℤ x}) :
    ∃ x : 𝓞 E, ∃ y ∈ hat1 F {x : E | IsIntegral ℤ x},
      k = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) + M • y := by
  induction hk using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨u, b, hb, h⟩ := (strong_approximation_mod_nat F M hM).2 a ha
    have hu : IsIntegral ℤ (algebraMap F E (u : F)) := u.isIntegral_coe.algebraMap
    refine ⟨⟨algebraMap F E (u : F) * x, hu.mul hx⟩, b ⊗ₜ x, tmul_mem_adelicCompletion_of_integral F hb hx, ?_⟩
    rw [h, TensorProduct.add_tmul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
    rfl
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨x, y, hy, rfl⟩ := h1
    obtain ⟨x', y', hy', rfl⟩ := h2
    refine ⟨x + x', y + y', add_mem hy hy', ?_⟩
    have : ((x + x' : 𝓞 E) : E) = x + x' := by simp
    rw [this, TensorProduct.tmul_add, smul_add]
    abel
  | neg y _ h1 =>
    obtain ⟨x, y, hy, rfl⟩ := h1
    refine ⟨-x, -y, neg_mem hy, ?_⟩
    have : ((-x : 𝓞 E) : E) = -x := by simp
    rw [this, TensorProduct.tmul_neg, smul_neg]
    abel

/- English proof (translation)
Set `b` to `Module.finBasis ℤ (𝓞 E)`. Set `g : (Fin (Module.finrank ℤ (𝓞 E)) → Fin M) → 𝓞 E` to `fun f => ∑ i, ((f i : ℕ) : ℤ) • b i`. Use `⟨Finset.univ.image g, ?_, fun x => ?_⟩` and prove the remaining obligations. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Simplify using `[RingOfIntegers.rank]`.

Establish `hM0 : (0 : ℤ) < M` using `by exact_mod_cast hM`. Set `f : Fin (Module.finrank ℤ (𝓞 E)) → Fin M` to `fun i => ⟨(b.repr x i % M).toNat, by`. Establish `h1` using `Int.emod_nonneg (b.repr x i) hM0.ne'`. Establish `h2` using `Int.emod_lt_of_pos (b.repr x i) hM0`. Use the proof step `omega⟩`.

Use `⟨g f, Finset.mem_image_of_mem _ (Finset.mem_univ _), ∑ i, (b.repr x i / M) • b i, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr x]`. Simplify using `only [g, f, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg (Int.emod_nonneg _ hM0.ne'), ← natCast_zsmul, smul_smul, ← add_smul, Int.emod_add_mul_ediv]`.
-/
theorem exists_reps (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M) :
    ∃ T : Finset (𝓞 E), T.card ≤ M ^ Module.finrank ℚ E ∧
      ∀ x : 𝓞 E, ∃ t ∈ T, ∃ y : 𝓞 E, x = t + M • y := by
  classical
  let b := Module.finBasis ℤ (𝓞 E)
  let g : (Fin (Module.finrank ℤ (𝓞 E)) → Fin M) → 𝓞 E := fun f => ∑ i, ((f i : ℕ) : ℤ) • b i
  refine ⟨Finset.univ.image g, ?_, fun x => ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp [RingOfIntegers.rank]
  · have hM0 : (0 : ℤ) < M := by exact_mod_cast hM
    let f : Fin (Module.finrank ℤ (𝓞 E)) → Fin M := fun i =>
      ⟨(b.repr x i % M).toNat, by
        have h1 := Int.emod_nonneg (b.repr x i) hM0.ne'
        have h2 := Int.emod_lt_of_pos (b.repr x i) hM0
        omega⟩
    refine ⟨g f, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ∑ i, (b.repr x i / M) • b i, ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    simp only [g, f, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hM0.ne'), ← natCast_zsmul, smul_smul, ← add_smul,
      Int.emod_add_mul_ediv]

/- English proof (translation)
Establish `h` using `Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E`. Establish `h2 : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Rewrite `h` using `[h2]`. Unfold `fdeg`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_fdeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    2 * fdeg E = Module.finrank ℚ E := by
  have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rw [h2] at h
  unfold fdeg
  omega

/- English proof (translation)
Take `⟨T, hT, hT'⟩` from `exists_reps E M hM`. Set `P : 𝓞 E → RA F E → Prop` to `fun t k => IsTA c k ∧ k ∈ hat1 F {x : E | IsIntegral ℤ x} ∧ ∃ y ∈ hat1 F {x : E | IsIntegral ℤ x}, k = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (t : E) + M • y`. Set `s : 𝓞 E → RA F E` to `fun t => Classical.epsilon (P t)`. Use `⟨T.image s, Finset.card_image_le.trans hT, fun k hk hk' => ?_⟩` and prove the remaining obligations. Take `⟨x, y, hy, hxy⟩` from `exists_integer_add_nsmul F E M hM k hk'`.

Take `⟨t, ht, z, rfl⟩` from `hT' x`. Establish `hP : P t k`. Use `⟨hk, hk', (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (z : E) + y, add_mem (one_tmul_mem_adelicCompletionOfElementSet F z.isIntegral_coe) hy, ?_⟩` and prove the remaining obligations. Establish `: ((t + M • z : 𝓞 E) : E) = t + M • (z : E)` using `by simp`. Rewrite using `[hxy, this, TensorProduct.tmul_add, TensorProduct.tmul_smul, smul_add, add_assoc]`.

Take `⟨hs, hs', w, hw, hsw⟩ : P t (s t)` from `Classical.epsilon_spec ⟨k, hP⟩`. Take `⟨-, -, w', hw', hkw⟩` from `hP`. Establish `hc : sg (FiniteAdeleRing (𝓞 F) F) c (s t) ∈ hat1 F {x : E | IsIntegral ℤ x}` using `galoisAut_mem_adelicCompletionOfElementSet F c (fun x hx => IsIntegral.map (c : E →+* E).toIntAlgHom hx) hs'`. Use `⟨s t, Finset.mem_image_of_mem _ ht, hs, k * sg _ c (s t), ?_, ⟨(w' - w) * sg _ c (s t), mul_mem_adelicCompletionOfElementSet_of_mul_mem F (fun a ha b hb => IsIntegral.mul ha hb) (sub_mem hw' hw) hc, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) hs`.

Rewrite `h1` using `[map_mul, map_one]`. Unfold `IsTA at hk ⊢`. Rewrite using `[map_mul, mul_mul_mul_comm, hk, h1, one_mul]`. Establish `h1 : k - s t = M • (w' - w)`. Rewrite using `[smul_sub]`.

Use `conv_lhs => rw [hkw, hsw]`. Normalize the expressions using the abelian group laws. Unfold `IsTA at hs`. Rewrite using `[← smul_mul_assoc, ← h1, sub_mul, hs]`. Unfold `IsTA at hs`.

Rewrite using `[mul_left_comm, hs, mul_one]`.
-/
theorem exists_reps_normOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (M : ℕ) (hM : 1 ≤ M) :
    ∃ S : Finset (RA F E), S.card ≤ M ^ Module.finrank ℚ E ∧ ∀ k : RA F E, IsTA c k →
      k ∈ hat1 F {x : E | IsIntegral ℤ x} → ∃ s ∈ S, IsTA c s ∧ ∃ k', IsTA c k' ∧
        (∃ y ∈ hat1 F {x : E | IsIntegral ℤ x}, k' - 1 = M • y) ∧ k = s * k' := by
  classical
  obtain ⟨T, hT, hT'⟩ := exists_reps E M hM
  let P : 𝓞 E → RA F E → Prop := fun t k => IsTA c k ∧ k ∈ hat1 F {x : E | IsIntegral ℤ x} ∧
    ∃ y ∈ hat1 F {x : E | IsIntegral ℤ x},
      k = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (t : E) + M • y
  let s : 𝓞 E → RA F E := fun t => Classical.epsilon (P t)
  refine ⟨T.image s, Finset.card_image_le.trans hT, fun k hk hk' => ?_⟩
  obtain ⟨x, y, hy, hxy⟩ := exists_integer_add_nsmul F E M hM k hk'
  obtain ⟨t, ht, z, rfl⟩ := hT' x
  have hP : P t k := by
    refine ⟨hk, hk', (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (z : E) + y,
      add_mem (one_tmul_mem_adelicCompletionOfElementSet F z.isIntegral_coe) hy, ?_⟩
    have : ((t + M • z : 𝓞 E) : E) = t + M • (z : E) := by simp
    rw [hxy, this, TensorProduct.tmul_add, TensorProduct.tmul_smul, smul_add, add_assoc]
  obtain ⟨hs, hs', w, hw, hsw⟩ : P t (s t) := Classical.epsilon_spec ⟨k, hP⟩
  obtain ⟨-, -, w', hw', hkw⟩ := hP
  have hc : sg (FiniteAdeleRing (𝓞 F) F) c (s t) ∈ hat1 F {x : E | IsIntegral ℤ x} :=
    galoisAut_mem_adelicCompletionOfElementSet F c (fun x hx => IsIntegral.map (c : E →+* E).toIntAlgHom hx) hs'
  refine ⟨s t, Finset.mem_image_of_mem _ ht, hs, k * sg _ c (s t), ?_,
    ⟨(w' - w) * sg _ c (s t), mul_mem_adelicCompletionOfElementSet_of_mul_mem F (fun a ha b hb => IsIntegral.mul ha hb)
      (sub_mem hw' hw) hc, ?_⟩, ?_⟩
  · have h1 := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) hs
    rw [map_mul, map_one] at h1
    unfold IsTA at hk ⊢
    rw [map_mul, mul_mul_mul_comm, hk, h1, one_mul]
  · have h1 : k - s t = M • (w' - w) := by
      rw [smul_sub]
      conv_lhs => rw [hkw, hsw]
      abel
    unfold IsTA at hs
    rw [← smul_mul_assoc, ← h1, sub_mul, hs]
  · unfold IsTA at hs
    rw [mul_left_comm, hs, mul_one]

/- English proof (translation)
Introduce `E _ _ _ M hM`. Rewrite using `[two_mul_fdeg]`. Conclude with `exists_reps_normOne _ E _ M hM`.
-/
theorem normOne_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ), 1 ≤ M → ∃ S : Finset (RA (maximalRealSubfield E) E), S.card ≤ M ^ (2 * fdeg E) ∧ ∀ k : RA (maximalRealSubfield E) E, IsTA (IsCMField.complexConj E) k → k ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x} → ∃ s ∈ S, IsTA (IsCMField.complexConj E) s ∧ ∃ k', IsTA (IsCMField.complexConj E) k' ∧ (∃ y ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x}, k' - 1 = M • y) ∧ k = s * k' := by
  intro E _ _ _ M hM
  rw [two_mul_fdeg]
  exact exists_reps_normOne _ E _ M hM

end GlobalTheory.UCls.NormOneMod
