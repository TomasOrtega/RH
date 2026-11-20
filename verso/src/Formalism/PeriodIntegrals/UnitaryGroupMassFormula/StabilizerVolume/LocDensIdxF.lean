import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxE

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing IdxHW

/- English proof (translation)
Unfold `IdxH`. Introduce `F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 _ _ d b`. Take `⟨-, -, hrank, hstar⟩` from `id hCM`. Establish `hd : d = 2` using `by rw [← hrank, Module.finrank_eq_card_basis b, Fintype.card_fin]`. Substitute `hd` using the available equality.

Establish `hσ : ∀ x, σ (σ x) = x`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Introduce `x`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hstar, hstar, star_star]`.

Take `⟨x0, hx0⟩` from `IdxHW.sigma_ne_id σ hCM`. Establish `hC1 : IdxHW.Cmat b σ ≠ 1`. Introduce `hC`. Apply `hx0` to reduce the goal to its premises. Establish `hb : ∀ l, σ (b l) = b l`.

Introduce `l`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Establish `hkl` using `congrFun (congrFun hC k) l`. Simplify using `only [IdxHW.Cmat] at hkl`.

Rewrite using `[hkl, b.repr_self, Matrix.one_apply, Finsupp.single_apply]`. Distinguish the cases in `h : k = l`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.

Use `conv_lhs => rw [← b.sum_repr x0]`. Rewrite using `[map_sum]`. Use `conv_rhs => rw [← b.sum_repr x0]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.map_smul_of_tower, hb]`.

Establish `hu0 : (fun k => b.repr 1 k) ≠ 0`. Introduce `h`. Establish `h1 : b.repr (1 : E) = 0`. Use extensionality with `k`. Conclude with `congrFun h k`.

Conclude with `one_ne_zero (b.repr.injective (h1.trans (map_zero b.repr).symm))`. Establish `hCu : (IdxHW.Cmat b σ).mulVec (fun k => b.repr 1 k) = fun k => b.repr 1 k`. Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, IdxHW.Cmat]`. Establish `e : σ 1 = ∑ l, b.repr 1 l • σ (b l)` using `by conv_lhs => rw [← b.sum_repr 1]`.

Rewrite using `[map_sum]`. Simplify using `only [AlgHom.map_smul_of_tower]`. Rewrite `e` using `[map_one]`. Use `conv_rhs => rw [e]`. Simplify using `[mul_comm]`.

Take `⟨k0, k1, hk, hk0, ρ, hρfix⟩` from `fix2 (IdxHW.Cmat b σ) hC1 _ hu0 hCu`. Establish `hev : ∀ᶠ v in cofinite, (∀ k l, algebraMap F (Fv F v) (IdxHW.Cmat b σ k l) ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Fv F v) ρ ∈ v.adicCompletionIntegers F ∧ ∀ k, algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) ∈ v.adicCompletionIntegers F` using `(Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => IdxHW.eventually_int _).and ((IdxHW.eventually_int ρ).and (Filter.eventually_all.2 fun k => IdxHW.eventually_int _))`. Use `filter_upwards [hev] with v hv`. Take `⟨hC, hρ, hu⟩` from `hv`. Establish `hfix : ∀ x : Fin 2 → Fv F v, Matrix.mulVec ((IdxHW.Cmat b σ).map (algebraMap F (Fv F v))) x = x → x k1 = algebraMap F (Fv F v) ρ * x k0` using `hρfix (Fv F v)`.

Rewrite using `[AddSubgroup.relIndex, IdxHW.comap_eq b v σ a k0 k1 hk ρ hC hρ hfix, AddSubgroup.index_comap_of_surjective _ (IdxHW.psi_surj b v σ a k0 hσ hC hu hk0), AddSubgroup.index_pi, Finset.prod_const, IdxHW.index_max v]`. Simplify using `[sq]`.
-/
theorem idxH_holds : IdxH := by
  unfold IdxH
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 _ _ d b
  obtain ⟨-, -, hrank, hstar⟩ := id hCM
  have hd : d = 2 := by rw [← hrank, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd

  have hσ : ∀ x, σ (σ x) = x := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro x
    apply τ.injective
    rw [hstar, hstar, star_star]

  obtain ⟨x0, hx0⟩ := IdxHW.sigma_ne_id σ hCM
  have hC1 : IdxHW.Cmat b σ ≠ 1 := by
    intro hC
    apply hx0
    have hb : ∀ l, σ (b l) = b l := by
      intro l
      apply b.repr.injective
      ext k
      have hkl := congrFun (congrFun hC k) l
      simp only [IdxHW.Cmat] at hkl
      rw [hkl, b.repr_self, Matrix.one_apply, Finsupp.single_apply]
      by_cases h : k = l
      · subst h
        simp
      · simp [h, Ne.symm h]
    conv_lhs => rw [← b.sum_repr x0]
    rw [map_sum]
    conv_rhs => rw [← b.sum_repr x0]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [AlgHom.map_smul_of_tower, hb]

  have hu0 : (fun k => b.repr 1 k) ≠ 0 := by
    intro h
    have h1 : b.repr (1 : E) = 0 := by
      ext k
      exact congrFun h k
    exact one_ne_zero (b.repr.injective (h1.trans (map_zero b.repr).symm))
  have hCu : (IdxHW.Cmat b σ).mulVec (fun k => b.repr 1 k) = fun k => b.repr 1 k := by
    funext k
    simp only [Matrix.mulVec, dotProduct, IdxHW.Cmat]
    have e : σ 1 = ∑ l, b.repr 1 l • σ (b l) := by
      conv_lhs => rw [← b.sum_repr 1]
      rw [map_sum]
      simp only [AlgHom.map_smul_of_tower]
    rw [map_one] at e
    conv_rhs => rw [e]
    simp [mul_comm]
  obtain ⟨k0, k1, hk, hk0, ρ, hρfix⟩ := fix2 (IdxHW.Cmat b σ) hC1 _ hu0 hCu

  have hev : ∀ᶠ v in cofinite,
      (∀ k l, algebraMap F (Fv F v) (IdxHW.Cmat b σ k l) ∈ v.adicCompletionIntegers F) ∧
      algebraMap F (Fv F v) ρ ∈ v.adicCompletionIntegers F ∧
      ∀ k, algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => IdxHW.eventually_int _).and
      ((IdxHW.eventually_int ρ).and (Filter.eventually_all.2 fun k => IdxHW.eventually_int _))
  filter_upwards [hev] with v hv
  obtain ⟨hC, hρ, hu⟩ := hv
  have hfix : ∀ x : Fin 2 → Fv F v,
      Matrix.mulVec ((IdxHW.Cmat b σ).map (algebraMap F (Fv F v))) x = x →
        x k1 = algebraMap F (Fv F v) ρ * x k0 := hρfix (Fv F v)
  rw [AddSubgroup.relIndex, IdxHW.comap_eq b v σ a k0 k1 hk ρ hC hρ hfix,
    AddSubgroup.index_comap_of_surjective _ (IdxHW.psi_surj b v σ a k0 hσ hC hu hk0),
    AddSubgroup.index_pi, Finset.prod_const, IdxHW.index_max v]
  simp [sq]

end PI.VolStabS
