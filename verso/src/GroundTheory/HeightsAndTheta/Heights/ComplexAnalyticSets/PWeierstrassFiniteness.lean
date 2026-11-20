import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassFiniteness
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloIntegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloEliminate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Introduce `σ _ x k f d A hf hpow g hg`. Set `L : Finset σ → (σ → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ)` to `fun S => ContinuousLinearMap.pi (Sum.elim (fun j => (ContinuousLinearMap.proj j).comp A) (fun l => if l ∈ S then ContinuousLinearMap.proj l else 0))`. Establish `hL : ∀ S z c, L S z c = Sum.elim (fun j => A z j) (fun l => if l ∈ S then z l else 0) c`. Introduce `S z c`. Break down `c with j | l` into its components or cases.

Simplify using `[L]`. Apply the tactic sequence `by_cases hl : l ∈ S <;> simp [L, hl]`. Establish `key : ∀ T : Finset σ, IsFiniteModuloOver x f (L (Finset.univ \ T))`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`.

Consider the case `empty`. Rewrite using `[Finset.sdiff_empty]`. Set `P : (Fin d ⊕ σ → ℂ) →L[ℂ] (σ → ℂ)` to `ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inr l)`. Establish `hPL : ∀ z, P (L Finset.univ z) = z` using `fun z => by`. Use function extensionality and compare the values at `l`.

Simplify using `[P, hL]`. Use `⟨1, fun _ _ => 1, fun _ => analyticAt_const, fun g hg => ?_⟩` and prove the remaining obligations. Use `⟨fun _ y => g (P y), fun _ _ => 0, fun _ => ?_, fun _ => analyticAt_const, Eventually.of_forall fun z => by simp only [hPL]; simp⟩` and prove the remaining obligations. Establish `hg' : AnalyticAt ℂ g (P (L Finset.univ x))` using `by rw [hPL]; exact hg`. Conclude with `hg'.comp (P.analyticAt _)`.

Consider the case `insert l T hl ih`. Establish `heq : L (Finset.univ \ insert l T) = (zeroCoordinate (Sum.inr l)).comp (L (Finset.univ \ T))`. Use extensionality with `z c`. Rewrite using `[ContinuousLinearMap.comp_apply, zeroCoordinate_apply, hL, hL]`. Break down `c with j | l'` into its components or cases.

Simplify using the standard rewrite rules. Distinguish the cases in `h1 : l' = l`. Substitute `h1` using the available equality. Simplify using the standard rewrite rules. Apply the tactic sequence `by_cases h2 : l' ∈ T <;> simp [h1, h2]`.

Rewrite using `[heq]`. Take `⟨r, h, h', hh, hh', hev⟩` from `hpow l`. Use `hE σ (Fin d ⊕ σ) x k f _ (Sum.inr l) hf ih ⟨r, h, Sum.elim h' (fun _ _ => 0), hh, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(j | l')`. Conclude with `hh' j`.

Conclude with `analyticAt_const`. Use `filter_upwards [hev] with z hz`. Simplify using `only [zeroCoordinate_apply, hL, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.mem_sdiff, Finset.mem_univ, hl, not_false_eq_true, and_self, if_true, reduceCtorEq, if_false, zero_mul, Finset.sum_const_zero, add_zero]`. Conclude with `hz`. Establish `hfin` using `key Finset.univ`.

Take `⟨N, a, h, ha, hh, hev⟩` from `hI σ (Fin d ⊕ σ) x k f _ hf hfin g hg`. Set `J : (Fin d → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ)` to `ContinuousLinearMap.pi (Sum.elim (fun j => ContinuousLinearMap.proj j) (fun _ => 0))`. Establish `hJ : ∀ z, J (A z) = L (Finset.univ \ Finset.univ) z` using `fun z => by`. Apply the tactic sequence `funext c; rcases c with j | l <;> simp [J, hL]`. Use `⟨N, fun j w => a j (J w), h, fun j => ?_, hh, ?_⟩` and prove the remaining obligations.

Establish `haj : AnalyticAt ℂ (a j) (J (A x))` using `by rw [hJ]; exact ha j`. Conclude with `haj.comp (J.analyticAt _)`. Use `filter_upwards [hev] with z hz`. Simplify `hz` using `only [hJ]`.
-/
theorem WeierstrassFiniteness.proof (hE : FiniteModuloEliminate.Statement)
    (hI : FiniteModuloIntegral.Statement) : WeierstrassFiniteness.Statement := by
  intro σ _ x k f d A hf hpow g hg
  classical

  let L : Finset σ → (σ → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) := fun S =>
    ContinuousLinearMap.pi (Sum.elim (fun j => (ContinuousLinearMap.proj j).comp A)
      (fun l => if l ∈ S then ContinuousLinearMap.proj l else 0))
  have hL : ∀ S z c, L S z c = Sum.elim (fun j => A z j) (fun l => if l ∈ S then z l else 0) c := by
    intro S z c
    rcases c with j | l
    · simp [L]
    · by_cases hl : l ∈ S <;> simp [L, hl]
  have key : ∀ T : Finset σ, IsFiniteModuloOver x f (L (Finset.univ \ T)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sdiff_empty]
      let P : (Fin d ⊕ σ → ℂ) →L[ℂ] (σ → ℂ) :=
        ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inr l)
      have hPL : ∀ z, P (L Finset.univ z) = z := fun z => by
        funext l; simp [P, hL]
      refine ⟨1, fun _ _ => 1, fun _ => analyticAt_const, fun g hg => ?_⟩
      refine ⟨fun _ y => g (P y), fun _ _ => 0, fun _ => ?_, fun _ => analyticAt_const,
        Eventually.of_forall fun z => by simp only [hPL]; simp⟩
      have hg' : AnalyticAt ℂ g (P (L Finset.univ x)) := by rw [hPL]; exact hg
      exact hg'.comp (P.analyticAt _)
    | insert l T hl ih =>
      have heq : L (Finset.univ \ insert l T) = (zeroCoordinate (Sum.inr l)).comp (L (Finset.univ \ T)) := by
        ext z c
        rw [ContinuousLinearMap.comp_apply, zeroCoordinate_apply, hL, hL]
        rcases c with j | l'
        · simp
        · by_cases h1 : l' = l
          · subst h1; simp
          · by_cases h2 : l' ∈ T <;> simp [h1, h2]
      rw [heq]
      obtain ⟨r, h, h', hh, hh', hev⟩ := hpow l
      refine hE σ (Fin d ⊕ σ) x k f _ (Sum.inr l) hf ih
        ⟨r, h, Sum.elim h' (fun _ _ => 0), hh, ?_, ?_⟩
      · rintro (j | l')
        · exact hh' j
        · exact analyticAt_const
      · filter_upwards [hev] with z hz
        simp only [zeroCoordinate_apply, hL, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Finset.mem_sdiff, Finset.mem_univ, hl, not_false_eq_true, and_self, if_true,
          reduceCtorEq, if_false, zero_mul, Finset.sum_const_zero, add_zero]
        exact hz
  have hfin := key Finset.univ
  obtain ⟨N, a, h, ha, hh, hev⟩ := hI σ (Fin d ⊕ σ) x k f _ hf hfin g hg

  let J : (Fin d → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) :=
    ContinuousLinearMap.pi (Sum.elim (fun j => ContinuousLinearMap.proj j) (fun _ => 0))
  have hJ : ∀ z, J (A z) = L (Finset.univ \ Finset.univ) z := fun z => by
    funext c; rcases c with j | l <;> simp [J, hL]
  refine ⟨N, fun j w => a j (J w), h, fun j => ?_, hh, ?_⟩
  · have haj : AnalyticAt ℂ (a j) (J (A x)) := by rw [hJ]; exact ha j
    exact haj.comp (J.analyticAt _)
  · filter_upwards [hev] with z hz
    simpa only [hJ] using hz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
