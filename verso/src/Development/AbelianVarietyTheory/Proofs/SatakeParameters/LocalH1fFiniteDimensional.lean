import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace GlobalTheory.LocalH1Finiteness

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matRep_apply' {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {k : ℕ}
    (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (g : ↥(GK K)) (v : Fin k → ↥LL.1) (a : Fin k) :
    matRep M g v a = ∑ b, M g a b * v b := rfl

/- English proof (translation)
Use `LL.2` as an intermediate fact. Use `K.2` as an intermediate fact. Set `φ : Formalism.GaloisCohomology.GK l K.1 →* ↥(GK K)` to `(IntermediateField.fixingSubgroupEquiv K.1).symm.toMonoidHom`. Establish `hφ : Continuous φ` using `(GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1).2`. Establish `hφs : Function.Surjective φ` using `(IntermediateField.fixingSubgroupEquiv K.1).symm.surjective`.

Establish `hc : ReciprocityTheory.Gal.ContAction (matRep M)`. Use `continuous_pi fun a => ?_` and prove the remaining obligations. Simplify using `only [matRep_apply']`. Use `continuous_finsetSum _ fun b _ => Continuous.mul ?_ ((continuous_apply b).comp continuous_snd)` and prove the remaining obligations. Conclude with `(hM.comp continuous_fst).matrix_elem a b`.

Establish `hn : ∀ g v, ‖matRep M g v‖ ≤ ‖v‖` using `fun g v => by`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun a => ?_` and prove the remaining obligations. Rewrite using `[matRep_apply']`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg v) fun b _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (hi g a b)).trans (norm_le_pi_norm v b)`. Conclude with `finite_cocycles_of_compact_cover (l := l) (matRep M) hc hn φ hφ hφs (fun r N _ _ _ _ _ rho hr hrho => (hK l K.1 K.2 r N rho hr hrho).2.1)`.
-/
theorem finite_continuous_cocycles_matRep (hK : Formalism.GaloisCohomology.LocalFinitenessK) {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hM : Continuous fun g => M g)
    (hi : ∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) :
    Module.Finite ↥LL.1 (continuousCocycles (matRep M)) := by
  have := LL.2
  have := K.2
  let φ : Formalism.GaloisCohomology.GK l K.1 →* ↥(GK K) :=
    (IntermediateField.fixingSubgroupEquiv K.1).symm.toMonoidHom
  have hφ : Continuous φ := (GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1).2
  have hφs : Function.Surjective φ := (IntermediateField.fixingSubgroupEquiv K.1).symm.surjective
  have hc : ReciprocityTheory.Gal.ContAction (matRep M) := by
    refine continuous_pi fun a => ?_
    simp only [matRep_apply']
    refine continuous_finsetSum _ fun b _ =>
      Continuous.mul ?_ ((continuous_apply b).comp continuous_snd)
    exact (hM.comp continuous_fst).matrix_elem a b
  have hn : ∀ g v, ‖matRep M g v‖ ≤ ‖v‖ := fun g v => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun a => ?_
    rw [matRep_apply']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg v) fun b _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hi g a b)).trans (norm_le_pi_norm v b)
  exact finite_cocycles_of_compact_cover (l := l) (matRep M) hc hn φ hφ hφs
    (fun r N _ _ _ _ _ rho hr hrho => (hK l K.1 K.2 r N rho hr hrho).2.1)

/- English proof (translation)
Introduce `hK l _ P K LL k M hM hi`. Establish `h1` using `finite_continuous_cocycles_matRep hK K LL M hM hi`. Establish `h2 : Module.Finite ↥LL.1 (finiteCocycles (P.PD K) (matRep M))` using `Module.Finite.of_injective (Submodule.inclusion (fun _ hx => hx.1 : finiteCocycles (P.PD K) (matRep M) ≤ continuousCocycles (matRep M))) (Submodule.inclusion_injective _)`. Conclude with `Module.Finite.quotient _ _`.
-/
theorem finite_H1fV_matRep : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K LL : FinExt l) (k : ℕ) (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1),
    Continuous (fun g => M g) → (∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) →
    Module.Finite ↥LL.1 (FiniteCohomology (P.PD K) (matRep M)) := by
  intro hK l _ P K LL k M hM hi
  have h1 := finite_continuous_cocycles_matRep hK K LL M hM hi
  have h2 : Module.Finite ↥LL.1 (finiteCocycles (P.PD K) (matRep M)) :=
    Module.Finite.of_injective (Submodule.inclusion (fun _ hx => hx.1 :
      finiteCocycles (P.PD K) (matRep M) ≤ continuousCocycles (matRep M))) (Submodule.inclusion_injective _)
  exact Module.Finite.quotient _ _

end GlobalTheory.LocalH1Finiteness
