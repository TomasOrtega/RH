import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DivAbsBig

/- English proof (translation)
Introduce `F E _ _ _ _ _`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨b, h2⟩ : ∃ b : w.Completion, ‖b‖ = 2 := by`. Use `⟨_, (InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (2 : F))).trans ?_⟩` and prove the remaining obligations. Use `show w (2 : F) = 2`.

Rewrite using `[← InfinitePlace.mk_embedding w, InfinitePlace.apply, map_ofNat]`. Evaluate the numerical expressions. Establish `hne : b ≠ 0`. Introduce `h`. Rewrite `h2` using `[h, norm_zero]`.

Evaluate the numerical expressions using `at h2`. Set `a : (w.Completion)ˣ` to `Units.mk0 b hne`. Set `y : (w.Completion ⊗[F] E)ˣ` to `Units.map (algebraMap w.Completion (w.Completion ⊗[F] E)).toMonoidHom a`. Use `⟨GlobalTheory.Doubling.ideleAtInf F E w y, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.Doubling.absE_ideleAtInf, GlobalTheory.Doubling.absEw_apply]`.

Express the relevant statement in the definitionally equal form `1 < ((‖Algebra.norm w.Completion (algebraMap w.Completion (w.Completion ⊗[F] E) b)‖₊ ^ w.mult : ℝ≥0) : ℝ)`. Rewrite using `[Algebra.norm_algebraMap, Module.finrank_baseChange, NNReal.coe_pow, coe_nnnorm, norm_pow, h2, ← pow_mul]`. Establish `hn : 0 < Module.finrank F E` using `Module.finrank_pos`. Apply the tactic sequence `have hm : 0 < w.mult := by unfold InfinitePlace.mult; split_ifs <;> norm_num`. Conclude with `one_lt_pow₀ (by norm_num) (Nat.mul_ne_zero hn.ne' hm.ne')`.
-/
theorem exists_idele_absE_gt_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ t : (AE F E)ˣ, 1 < (absE F E t : ℝ) := by
  intro F E _ _ _ _ _
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨b, h2⟩ : ∃ b : w.Completion, ‖b‖ = 2 := by
    refine ⟨_, (InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (2 : F))).trans ?_⟩
    show w (2 : F) = 2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.apply, map_ofNat]
    norm_num
  have hne : b ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; norm_num at h2
  let a : (w.Completion)ˣ := Units.mk0 b hne
  let y : (w.Completion ⊗[F] E)ˣ := Units.map (algebraMap w.Completion (w.Completion ⊗[F] E)).toMonoidHom a
  refine ⟨GlobalTheory.Doubling.ideleAtInf F E w y, ?_⟩
  rw [GlobalTheory.Doubling.absE_ideleAtInf, GlobalTheory.Doubling.absEw_apply]
  change 1 < ((‖Algebra.norm w.Completion (algebraMap w.Completion (w.Completion ⊗[F] E) b)‖₊ ^ w.mult : ℝ≥0) : ℝ)
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, NNReal.coe_pow, coe_nnnorm, norm_pow, h2, ← pow_mul]
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  have hm : 0 < w.mult := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact one_lt_pow₀ (by norm_num) (Nat.mul_ne_zero hn.ne' hm.ne')

end GlobalTheory.DivAbsBig

end
