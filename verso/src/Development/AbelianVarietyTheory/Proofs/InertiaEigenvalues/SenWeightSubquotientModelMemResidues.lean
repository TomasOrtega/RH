import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicitySubquotientLatticeLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSenWeightMemWeightResiduesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightsCloseOfHeightGammaConditionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmeticStatement

namespace GlobalTheory.Models
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

/- English proof (translation)
Unfold `resCount at h`. Rewrite `h` using `[Ne, Multiset.card_eq_zero]`. Take `⟨u, hu⟩` from `Multiset.exists_mem_of_ne_zero h`. Rewrite `hu` using `[Multiset.mem_filter]`. Conclude with `⟨u, hu.1, hu.2⟩`.
-/
theorem exists_of_resCount_ne_zero_sq {k : Type} [Field k] {U : Multiset ℤ} {w : ℤ} {x : k}
    (h : resCount U w x ≠ 0) : ∃ u ∈ U, ((u - w : ℤ) : k) = x := by
  classical
  unfold resCount at h
  rw [Ne, Multiset.card_eq_zero] at h
  obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero h
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

/- English proof (translation)
Introduce `k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 A₁ A j p N hj hji hp hps hN i x hx`. Establish `hT` using `GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model`. Establish `hm1` using `GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ M.T j M.Nstd hj hji M.std_model`. Establish `hm` using `ModTh.model_push_of_surjective F M A₁ A p _ hp hps hm1`. Establish `habc0` using `(GlobalTheory.T.obj_and_abc_of_model F M A _ hm).2`.

Establish `habc` using `(GlobalTheory.T.obj_and_abc_of_model F M A N hN).2`. Take `⟨c, hc, hs⟩` from `GlobalTheory.T.senWeights_close_of_height_gamma_conditions (F.D A) Dt _ N habc0 habc i x hx`. Establish `hle` using `GlobalTheory.T.senMultiplicity_subquotient_lattice_le F M.T A₁ A j p Dt.w Dt.wst M.Nstd hT.1 hj hji hp hps hT.2 i (x + c)`. Establish `hs' : sen ((F.D M.T).γ i) (M.Nstd i) (x + c) ≠ 0` using `fun h0 => hs (by`. Rewrite `hle` using `[h0]`.

Conclude with `Nat.le_zero.mp hle)`. Rewrite `hs'` using `[M.std_sen]`. Take `⟨u, hu, hux⟩` from `exists_of_resCount_ne_zero_sq hs'`. Take `⟨u', hu', hux'⟩` from `GlobalTheory.T.model_senWeight_mem_weight_residues F M A N hN i x hx`. Break down `Multiset.mem_add.mp hu' with hU | hB` into its components or cases.

Conclude with `⟨u', hU, hux'⟩`. It suffices to derive a contradiction. Take `⟨hb1, hb2⟩` from `mem_block.mp hB`. Take `⟨hc1, hc2⟩` from `abs_le.mp hc`. Use `(GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt h1 h2 h3 i).2.1 u hu (u' + c) (by omega) (by omega) ?_` and prove the remaining obligations.

Rewrite `hux` using `[← hux']`. Move the coercions through the operations in `at hux ⊢`. Take the linear combination `hux`.
-/
theorem ModTh.sen_model_subquot_mem_U : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (N : Lats k n A.m), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) = x := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 A₁ A j p N hj hji hp hps hN i x hx
  have hT := GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model
  have hm1 := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ M.T j M.Nstd hj hji M.std_model
  have hm := ModTh.model_push_of_surjective F M A₁ A p _ hp hps hm1
  have habc0 := (GlobalTheory.T.obj_and_abc_of_model F M A _ hm).2
  have habc := (GlobalTheory.T.obj_and_abc_of_model F M A N hN).2
  obtain ⟨c, hc, hs⟩ := GlobalTheory.T.senWeights_close_of_height_gamma_conditions (F.D A) Dt _ N habc0 habc i x hx
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F M.T A₁ A j p Dt.w Dt.wst M.Nstd hT.1 hj hji hp hps hT.2 i (x + c)
  have hs' : sen ((F.D M.T).γ i) (M.Nstd i) (x + c) ≠ 0 := fun h0 => hs (by
    rw [h0] at hle; exact Nat.le_zero.mp hle)
  rw [M.std_sen] at hs'
  obtain ⟨u, hu, hux⟩ := exists_of_resCount_ne_zero_sq hs'
  obtain ⟨u', hu', hux'⟩ := GlobalTheory.T.model_senWeight_mem_weight_residues F M A N hN i x hx
  rcases Multiset.mem_add.mp hu' with hU | hB
  · exact ⟨u', hU, hux'⟩
  · exfalso
    obtain ⟨hb1, hb2⟩ := mem_block.mp hB
    obtain ⟨hc1, hc2⟩ := abs_le.mp hc
    refine (GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt h1 h2 h3 i).2.1 u hu (u' + c) (by omega) (by omega) ?_
    rw [← hux'] at hux
    push_cast at hux ⊢
    linear_combination hux

end GlobalTheory.Models
