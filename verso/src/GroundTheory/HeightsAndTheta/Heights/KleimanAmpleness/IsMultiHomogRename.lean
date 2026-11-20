import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

namespace RowChartAct

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, Pi.add_apply]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem isMultiHomog_rename [DecidableEq K] (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {f : MvPolynomial (Fin (N + 1)) S}
    {d : ℕ} (hf : f.IsHomogeneous d) :
    IsMultiHomog (rename (fun j => (⟨k₀, e.symm j⟩ : Σ k, ι k)) f) (Pi.single k₀ d) := by
  classical
  have hρ : Function.Injective (fun j => (⟨k₀, e.symm j⟩ : Σ k, ι k)) := fun j j' h =>
    e.symm.injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  intro m' hm' k
  rw [support_rename_of_injective hρ] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
  have hd := hf (mem_support_iff.mp hm)
  by_cases hk : k = k₀
  · subst hk
    have hval : ∀ i, Finsupp.mapDomain (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) m ⟨k, i⟩ = m (e i) := fun i => by
      have hi : (⟨k, i⟩ : Σ k, ι k) = (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) (e i) := by simp
      rw [hi, Finsupp.mapDomain_apply hρ]
    simp_rw [hval]
    rw [Pi.single_eq_same, Equiv.sum_comp e (fun j => m j), ← hd]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Pi.single_eq_of_ne hk]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨j, hj⟩
    exact hk (congrArg Sigma.fst hj).symm

end RowChartAct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem RowChartAct.proof : RowChartAct.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J I r a hr ha
  obtain ⟨f, s, d, hs, hf, hsd, rfl⟩ := hr
  set ρ : Fin (N + 1) → Σ k, ι k := fun j => ⟨k₀, e.symm j⟩ with hρ
  have hsmem : rename ρ s ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
    have hle : (Kleiman.monos (S := S) J.1).map (rename ρ : MvPolynomial _ S →ₐ[S] MRingOver S ι).toRingHom.toMonoidHom ≤
        ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
      rw [Kleiman.monos, MonoidHom.map_mclosure]
      refine Submonoid.closure_le.mpr ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      refine Submonoid.subset_closure ⟨k₀, e.symm j, ?_, by simp [ρ]⟩
      unfold baseCell
      rw [Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)
    exact hle ⟨s, hs, rfl⟩
  unfold cellSec at ha ⊢
  split_ifs at ha ⊢ with hM
  · induction ha using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, t, b, ht, htb, hγ, hg, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨rename ρ f * g, rename ρ s * t, b + Pi.single k₀ d, mul_mem hsmem ht, ?_, ?_, ?_, ?_⟩
      · rw [add_comm b]
        exact RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hsd) htb
      · intro k
        have h1 := hγ k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      · have h2 := RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hf) hg
        have heq : (Pi.single k₀ d + fun k => (γ k + b k).toNat) =
            fun k => (γ k + ((b + Pi.single k₀ d : K → ℕ) k : ℕ)).toNat := funext fun k => by
          have h1 := hγ k
          simp only [Pi.add_apply, Nat.cast_add]
          omega
        rw [heq] at h2
        exact h2
      · simp only [map_mul, aeval_rename]
        rw [div_mul_div_comm]
        rfl
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  · rw [Submodule.mem_bot] at ha ⊢
    rw [ha, mul_zero]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
