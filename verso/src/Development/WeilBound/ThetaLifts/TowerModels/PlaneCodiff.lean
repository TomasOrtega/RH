import Development.WeilBound.ThetaLifts.TowerModels.PlaneForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumEmbeddingsEqRealAddComplex

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYhb7.main y`.
-/
theorem trace_mixedEmbedding (y : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F y) = (Algebra.trace ℚ F y : ℝ) :=
  _root_.UpperTheory.Reformulated.B.DYhb7.main y

/- English proof (translation)
Establish `e : pairA F 0 (algebraMap F (Af F) x) = algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0`. Use `Prod.ext ?_ (add_zero _).symm` and prove the remaining obligations. Use `show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)`. Rewrite using `[map_neg, add_neg_cancel]`. Establish `hat : At (evI F) (pairA F (algebraMap F (Ainf F) (-x)) 0)`.

Introduce `u hu`. Establish `h1 : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 * _ = 0`. Rewrite using `[h1, zero_mul]`.

Express the relevant statement in the definitionally equal form `u.2 * 0 = 0`. Rewrite using `[mul_zero]`. Rewrite using `[e, AddChar.map_add_eq_mul, hψ.2.1, one_mul, hψ.2.2 _ hat]`. Establish `h2 : evI F (pairA F (algebraMap F (Ainf F) (-x)) 0) = mixedEmbedding F (-x)` using `by show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) (-x)) = _`. Rewrite using `[InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]`.

Rewrite using `[h2, trace_mixedEmbedding, map_neg]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have hat : At (evI F) (pairA F (algebraMap F (Ainf F) (-x)) 0) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  rw [e, AddChar.map_add_eq_mul, hψ.2.1, one_mul, hψ.2.2 _ hat]
  have h2 : evI F (pairA F (algebraMap F (Ainf F) (-x)) 0) = mixedEmbedding F (-x) := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) (-x)) = _
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rw [h2, trace_mixedEmbedding, map_neg]
  congr 1
  push_cast
  ring

/- English proof (translation)
Use `GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 t (fun a => ?_) α hα` and prove the remaining obligations. Take `⟨k, hk⟩` from `ht a`. Rewrite using `[psi_fin_rat hψ, hk, Complex.exp_eq_one_iff]`. Conclude with `⟨k, by push_cast; ring⟩`.
-/
theorem psi_int {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : F)
    (ht : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * t) = k) (α : Af F) (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) :
    ψ (pairA F 0 (α * algebraMap F (Af F) t)) = 1 := by
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 t (fun a => ?_) α hα
  obtain ⟨k, hk⟩ := ht a
  rw [psi_fin_rat hψ, hk, Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

/- English proof (translation)
Establish `h1` using `trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := x)`. Set `τ : E →ₐ[F] AlgebraicClosure E` to `IsScalarTower.toAlgHom F E _`. Establish `h2 : (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ}`. Use extensionality with `τ'`. Simplify using `using eq_or_eq_comp_conj h τ τ'`.

Rewrite `h1` using `[h2, Finset.sum_pair (comp_conj_ne h τ).symm]`. Apply `(algebraMap E (AlgebraicClosure E)).injective` to reduce the goal to its premises. Rewrite using `[← IsScalarTower.algebraMap_apply, h1, map_add]`. Both sides reduce to the same expression.
-/
theorem trace_cm (h : IsCMExt F E σ) (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have h1 := trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := x)
  let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  have h2 : (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} := by
    ext τ'
    simpa using eq_or_eq_comp_conj h τ τ'
  rw [h2, Finset.sum_pair (comp_conj_ne h τ).symm] at h1
  apply (algebraMap E (AlgebraicClosure E)).injective
  rw [← IsScalarTower.algebraMap_apply, h1, map_add]
  rfl

/- English proof (translation)
Establish `h2` using `psi_int hψ a fun o => by`. Take `⟨k, hk⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (ha o)`. Conclude with `⟨k, hk.symm⟩`. Use `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((hv _).1 fun y hy => ?_)` and prove the remaining obligations. Establish `h3` using `h2 (singleFin v y) fun w => by`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Express the relevant statement in the definitionally equal form `evalV _ w (singleFin w y) ∈ _`. Rewrite using `[evalV_singleFin_self]`. Conclude with `hy`.

Express the relevant statement in the definitionally equal form `evalV _ w (singleFin v y) ∈ _`. Rewrite using `[evalV_singleFin_ne hw]`. Conclude with `zero_mem _`. Establish `e : singleFin v y * algebraMap F (Af F) a = singleFin v (algebraMap F (Fv F v) a * y)`. Apply `af_ext` to reduce the goal to its premises.

Introduce `u`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality. Rewrite using `[map_mul, evalV_singleFin_self, evalV_singleFin_self, mul_comm]`. Both sides reduce to the same expression.

Rewrite using `[map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]`. Rewrite `h3` using `[e]`. Conclude with `h3`.
-/
theorem val_le_one_of_codiff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hv : PsiUnr ψ v) (a : F)
    (ha : ∀ o : 𝓞 F, IsIntegral ℤ (Algebra.trace ℚ F (o * a))) : Valued.v (algebraMap F (Fv F v) a) ≤ 1 := by
  have h2 := psi_int hψ a fun o => by
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 (ha o)
    exact ⟨k, hk.symm⟩
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((hv _).1 fun y hy => ?_)
  have h3 := h2 (singleFin v y) fun w => by
    by_cases hw : w = v
    · subst hw
      change evalV _ w (singleFin w y) ∈ _
      rw [evalV_singleFin_self]
      exact hy
    · change evalV _ w (singleFin v y) ∈ _
      rw [evalV_singleFin_ne hw]
      exact zero_mem _
  have e : singleFin v y * algebraMap F (Af F) a = singleFin v (algebraMap F (Fv F v) a * y) := by
    apply af_ext
    intro u
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, mul_comm]
      rfl
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]
  rw [e] at h3
  exact h3

variable (E) in

def codE : Submodule (𝓞 E) E where
  carrier := {c | ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * c))}
  zero_mem' o := by simpa using isIntegral_zero
  add_mem' ha hb o := by rw [mul_add, map_add]; exact (ha o).add (hb o)
  smul_mem' a c hc o := by
    have := hc (o * a)
    change IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (a : E) * c)) at this
    rwa [mul_assoc] at this

/- English proof (translation)
Introduce `o` and use `by rw [mul_one]; exact Algebra.isIntegral_trace o.isIntegral_coe`.
-/
theorem one_mem_codE : (1 : E) ∈ codE E := fun o => by
  rw [mul_one]; exact Algebra.isIntegral_trace o.isIntegral_coe

variable (E) in

def intE : Submodule (𝓞 E) E where
  carrier := {c | IsIntegral ℤ c}
  zero_mem' := isIntegral_zero
  add_mem' ha hb := ha.add hb
  smul_mem' a _ hc := a.isIntegral_coe.mul hc

/- English proof (translation)
The claim follows from `apply_coe_mem τ (⟨c, hc⟩ : 𝓞 E)`.
-/
theorem val_le_one_of_intE {v : Pl F} (τ : E →ₐ[F] Fv F v) (c : E) (hc : c ∈ intE E) : Valued.v (τ c) ≤ 1 :=
  apply_coe_mem τ (⟨c, hc⟩ : 𝓞 E)

/- English proof (translation)
Establish `h1 : ∀ o : 𝓞 E, Valued.v (τ (o * c) + τ (σ (o * c))) ≤ 1` using `fun o => by`. Rewrite using `[← map_add, ← trace_cm h, AlgHom.commutes]`. Use `val_le_one_of_codiff hψ hv _ fun a => ?_` and prove the remaining obligations. Use `hc (algebraMap (𝓞 F) (𝓞 E) a * o)` as an intermediate fact. Rewrite `this` using `[← Algebra.trace_trace (S := F)]`.

Use `this using 2` and compare the differences between its conclusion and the goal. Rewrite using `[← smul_eq_mul, ← map_smul, Algebra.smul_def, ← mul_assoc]`. Both sides reduce to the same expression. Establish `hne : ¬ (splitPrime (τ.comp σ)).asIdeal ≤ (splitPrime τ).asIdeal` using `fun hle => splitPrime_comp_ne h τ (HeightOneSpectrum.ext ((splitPrime (τ.comp σ)).isMaximal.eq_of_le (splitPrime τ).isPrime.ne_top hle))`. Take `⟨p, hp, hp'⟩` from `Set.not_subset.1 hne`.

Establish `a1 : Valued.v (τ (σ p)) < 1` using `(mem_splitPrime (τ.comp σ) p).1 hp`. Establish `a2 : Valued.v (τ p) = 1` using `le_antisymm (apply_coe_mem τ p) (not_lt.1 fun e => hp' ((mem_splitPrime τ p).2 e))`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℕ, Valued.v (τ (σ p)) ^ k * Valued.v (τ (σ c)) ≤ 1 := by`. Distinguish the cases in `h0 : Valued.v (τ (σ c)) = 0`. Conclude with `⟨0, by simp [h0]⟩`.

Take `⟨k, hk⟩` from `exists_pow_lt₀ a1 (Units.mk0 _ h0)⁻¹`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[Units.val_inv_eq_inv_val, Units.val_mk0]`. Combine the equalities or inequalities in the displayed calculation. Establish `b1` using `h1 (p ^ k)`.

Establish `b2 : Valued.v (τ (σ (((p ^ k : 𝓞 E) : E) * c))) ≤ 1`. Use `push_cast`. Simplify `hk` using `only [map_mul, map_pow]`. Establish `b3` using `Valuation.map_sub_le _ b1 b2`. Rewrite `b3` using `[add_sub_cancel_right]`.

Move the coercions through the operations in `at b3`. Simplify `b3` using `only [map_mul, map_pow, a2, one_pow, one_mul]`.
-/
theorem val_le_one_of_codE (h : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hv : PsiUnr ψ v)
    (τ : E →ₐ[F] Fv F v) (c : E) (hc : c ∈ codE E) : Valued.v (τ c) ≤ 1 := by
  have h1 : ∀ o : 𝓞 E, Valued.v (τ (o * c) + τ (σ (o * c))) ≤ 1 := fun o => by
    rw [← map_add, ← trace_cm h, AlgHom.commutes]
    refine val_le_one_of_codiff hψ hv _ fun a => ?_
    have := hc (algebraMap (𝓞 F) (𝓞 E) a * o)
    rw [← Algebra.trace_trace (S := F)] at this
    convert this using 2
    rw [← smul_eq_mul, ← map_smul, Algebra.smul_def, ← mul_assoc]
    rfl
  have hne : ¬ (splitPrime (τ.comp σ)).asIdeal ≤ (splitPrime τ).asIdeal := fun hle =>
    splitPrime_comp_ne h τ (HeightOneSpectrum.ext
      ((splitPrime (τ.comp σ)).isMaximal.eq_of_le (splitPrime τ).isPrime.ne_top hle))
  obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 hne
  have a1 : Valued.v (τ (σ p)) < 1 := (mem_splitPrime (τ.comp σ) p).1 hp
  have a2 : Valued.v (τ p) = 1 := le_antisymm (apply_coe_mem τ p) (not_lt.1 fun e => hp' ((mem_splitPrime τ p).2 e))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Valued.v (τ (σ p)) ^ k * Valued.v (τ (σ c)) ≤ 1 := by
    by_cases h0 : Valued.v (τ (σ c)) = 0
    · exact ⟨0, by simp [h0]⟩
    · obtain ⟨k, hk⟩ := exists_pow_lt₀ a1 (Units.mk0 _ h0)⁻¹
      refine ⟨k, ?_⟩
      rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hk
      calc _ ≤ (Valued.v (τ (σ c)))⁻¹ * Valued.v (τ (σ c)) := by gcongr
        _ = 1 := inv_mul_cancel₀ h0
  have b1 := h1 (p ^ k)
  have b2 : Valued.v (τ (σ (((p ^ k : 𝓞 E) : E) * c))) ≤ 1 := by
    push_cast
    simpa only [map_mul, map_pow] using hk
  have b3 := Valuation.map_sub_le _ b1 b2
  rw [add_sub_cancel_right] at b3
  push_cast at b3
  simpa only [map_mul, map_pow, a2, one_pow, one_mul] using b3

end PositivityTheory.ThKG.Tow.Pln

end
