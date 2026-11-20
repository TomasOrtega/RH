import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

namespace RowChartAct

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm k`. Take `⟨m₁, hm₁, m₂, hm₂, rfl⟩` from `Finset.mem_add.mp (support_mul f g hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, Pi.add_apply]`.
-/
theorem isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, Pi.add_apply]

/- English proof (translation)
Establish `hρ : Function.Injective (fun j => (⟨k₀, e.symm j⟩ : Σ k, ι k))` using `fun j j' h => e.symm.injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)`. Introduce `m' hm' k`. Rewrite `hm'` using `[support_rename_of_injective hρ]`. Take `⟨m, hm, rfl⟩` from `Finset.mem_image.mp hm'`. Establish `hd` using `hf (mem_support_iff.mp hm)`.

Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Establish `hval : ∀ i, Finsupp.mapDomain (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) m ⟨k, i⟩ = m (e i)` using `fun i => by`. Establish `hi : (⟨k, i⟩ : Σ k, ι k) = (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) (e i)` using `by simp`. Rewrite using `[hi, Finsupp.mapDomain_apply hρ]`.

Repeatedly rewrite using `[hval]`. Rewrite using `[Pi.single_eq_same, Equiv.sum_comp e (fun j => m j), ← hd]`. Simplify using `[Finsupp.weight_apply, Finsupp.sum_fintype]`. Rewrite using `[Pi.single_eq_of_ne hk]`. Use `Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_` and prove the remaining obligations.

Introduce and unpack `⟨j, hj⟩`. Conclude with `hk (congrArg Sigma.fst hj).symm`.
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
Introduce `S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J I r a hr ha`. Take `⟨f, s, d, hs, hf, hsd, rfl⟩` from `hr`. Use `set ρ : Fin (N + 1) → Σ k, ι k := fun j => ⟨k₀, e.symm j⟩ with hρ`. Establish `hsmem : rename ρ s ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I)`. Establish `hle : (Kleiman.monos (S` using `S) J.1).map (rename ρ : MvPolynomial _ S →ₐ[S] MRingOver S ι).toRingHom.toMonoidHom ≤ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by`.

Rewrite using `[Kleiman.monos, MonoidHom.map_mclosure]`. Use `Submonoid.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨j, hj, rfl⟩, rfl⟩`. Use `Submonoid.subset_closure ⟨k₀, e.symm j, ?_, by simp [ρ]⟩` and prove the remaining obligations. Unfold `baseCell`.

Rewrite using `[Function.update_self]`. Conclude with `Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)`. Conclude with `hle ⟨s, hs, rfl⟩`. Unfold `cellSec at ha ⊢`. Use `split_ifs at ha ⊢ with hM`.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨g, t, b, ht, htb, hγ, hg, rfl⟩` from `hz`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨rename ρ f * g, rename ρ s * t, b + Pi.single k₀ d, mul_mem hsmem ht, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[add_comm b]`. Conclude with `RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hsd) htb`. Introduce `k`. Establish `h1` using `hγ k`. Simplify using `only [Pi.add_apply, Nat.cast_add]`.

Use linear arithmetic over natural numbers and integers. Establish `h2` using `RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hf) hg`. Establish `heq : (Pi.single k₀ d + fun k => (γ k + b k).toNat) = fun k => (γ k + ((b + Pi.single k₀ d : K → ℕ) k : ℕ)).toNat` using `funext fun k => by`. Establish `h1` using `hγ k`. Simplify using `only [Pi.add_apply, Nat.cast_add]`.

Use linear arithmetic over natural numbers and integers. Rewrite `h2` using `[heq]`. Conclude with `h2`. Simplify using `only [map_mul, aeval_rename]`. Rewrite using `[div_mul_div_comm]`.

Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [mul_add]`. Conclude with `add_mem hu hv`. Consider the case `smul c u _ hu => rw [mul_smul_comm]`.

Conclude with `Submodule.smul_mem _ c hu`. Rewrite `ha`, the goal using `[Submodule.mem_bot]`. Rewrite using `[ha, mul_zero]`.
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
