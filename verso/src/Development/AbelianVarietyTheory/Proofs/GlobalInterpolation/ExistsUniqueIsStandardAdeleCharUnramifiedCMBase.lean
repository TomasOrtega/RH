import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.StdCharUnique

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Establish `h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x`. Establish `h` using `trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)`. Rewrite `h` using `[eq_ratCast]`. Rewrite using `[h]`. Conclude with `(Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ fun _ => rfl).symm`.

Establish `h2 : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re`. Rewrite using `[← Complex.re_sum, ← h1, Complex.ratCast_re]`. Rewrite using `[h2, ← Finset.sum_fiberwise Finset.univ (fun φ : F →+* ℂ => InfinitePlace.mk φ)]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← InfinitePlace.card_filter_mk_eq, ← nsmul_eq_mul, ← Finset.sum_const]`.

Use `Finset.sum_congr (by congr) fun φ hφ => ?_` and prove the remaining obligations. Establish `hw : InfinitePlace.mk φ = w` using `(Finset.mem_filter.1 hφ).2`. Substitute `hw` using the available equality. Break down `InfinitePlace.embedding_mk_eq φ with h | h` into its components or cases. Rewrite using `[h]`.

Rewrite using `[h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]`.
-/
theorem sum_mult_re_eq_trace (x : F) :
    ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  classical
  have h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ fun _ => rfl).symm
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  rw [h2, ← Finset.sum_fiberwise Finset.univ (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← InfinitePlace.card_filter_mk_eq, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr (by congr) fun φ hφ => ?_
  have hw : InfinitePlace.mk φ = w := (Finset.mem_filter.1 hφ).2
  subst hw
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

/- English proof (translation)
Rewrite using `[traceInf, traceInf, traceInf, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[show (x + y) w = x w + y w from rfl, map_add, Complex.add_re, mul_add]`.
-/
theorem traceInf_add (x y : Ainf F) : traceInf F (x + y) = traceInf F x + traceInf F y := by
  rw [traceInf, traceInf, traceInf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (x + y) w = x w + y w from rfl, map_add, Complex.add_re, mul_add]

/- English proof (translation)
Use `continuous_finset_sum _ fun w _ => continuous_const.mul (Complex.continuous_re.comp ?_)` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)`.
-/
theorem continuous_traceInf : Continuous (traceInf F) := by
  refine continuous_finset_sum _ fun w _ => continuous_const.mul (Complex.continuous_re.comp ?_)
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

/- English proof (translation)
Rewrite using `[← sum_mult_re_eq_trace, traceInf]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `congr 2`. Conclude with `InfinitePlace.Completion.extensionEmbedding_coe w _`.
-/
theorem traceInf_algebraMap (x : F) :
    traceInf F (algebraMap F (Ainf F) x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [← sum_mult_re_eq_trace, traceInf]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  exact InfinitePlace.Completion.extensionEmbedding_coe w _

/- English proof (translation)
Set `L : Ainf F →+ ℂ` to `AddMonoidHom.mk' (fun x => (traceInf F x : ℂ)) fun a b => by`. Rewrite using `[traceInf_add, Complex.ofReal_add]`. Take `⟨ψ, h1, h2⟩` from `GlobalTheory.StdAdelicChar.exists_char_of_trace F L (Complex.continuous_ofReal.comp (continuous_traceInf F)) fun x => by show ((traceInf F (algebraMap F (Ainf F) x) : ℝ) : ℂ) = _`. Rewrite using `[traceInf_algebraMap, Complex.ofReal_ratCast]`. Establish `hψ : IsStdChar F ψ` using `⟨h1, fun x => by`.

Rewrite using `[h2, stdInf]`. Use `congr 1`. Use `show _ * ((traceInf F x : ℝ) : ℂ) = _`. Use `push_cast`. Use the proof step `ring⟩`.

Conclude with `⟨ψ, hψ, fun ψ' h' => GlobalTheory.StdAdelicChar.eq_of_psiInf_eq h'.1 hψ.1 fun x => (h'.2 x).trans (hψ.2 x).symm⟩`.
-/
theorem existsUnique_isStdChar : ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ := by
  let L : Ainf F →+ ℂ := AddMonoidHom.mk' (fun x => (traceInf F x : ℂ)) fun a b => by
    rw [traceInf_add, Complex.ofReal_add]
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.StdAdelicChar.exists_char_of_trace F L
    (Complex.continuous_ofReal.comp (continuous_traceInf F)) fun x => by
      show ((traceInf F (algebraMap F (Ainf F) x) : ℝ) : ℂ) = _
      rw [traceInf_algebraMap, Complex.ofReal_ratCast]
  have hψ : IsStdChar F ψ := ⟨h1, fun x => by
    rw [h2, stdInf]
    congr 1
    show _ * ((traceInf F x : ℝ) : ℂ) = _
    push_cast
    ring⟩
  exact ⟨ψ, hψ, fun ψ' h' => GlobalTheory.StdAdelicChar.eq_of_psiInf_eq h'.1 hψ.1
    fun x => (h'.2 x).trans (hψ.2 x).symm⟩

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ _ _ _ _` and use `existsUnique_isStdChar F`.
-/
theorem existsUnique_isStdChar_cm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
      ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ :=
  fun F _ _ _ _ _ _ _ _ _ _ _ => existsUnique_isStdChar F

end GlobalTheory.StdCharUnique

end
