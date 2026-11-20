import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.HermFormShiftedVectorZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMassHolds

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

/- English proof (translation)
Establish `h1 : IsIntegral ℤ (star (o : K))` using `(NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom`. Conclude with `⟨⟨star (o : K), h1⟩, rfl⟩`.
-/
theorem star_int {K : Type} [Field K] [NumberField K] [StarRing K] (o : 𝓞 K) :
    ∃ o' : 𝓞 K, (o' : K) = star (o : K) := by
  have h1 : IsIntegral ℤ (star (o : K)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨star (o : K), h1⟩, rfl⟩

/- English proof (translation)
Establish `memM : ∀ x : W, x ∈ M ↔ ∀ m ∈ M, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = h m x`. Introduce `x`. Use `conv_lhs => rw [← hU]`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]`. Set `I : Ideal (𝓞 K)` to `{ carrier := {o | ∃ m ∈ M, h m z = star (o : K)} add_mem' := by`.

Introduce and unpack `a b ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩`. Use `⟨m₁ + m₂, M.add_mem hm₁ hm₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, LinearMap.add_apply, e₁, e₂]`. Use `show star (algebraMap (𝓞 K) K a) + star (algebraMap (𝓞 K) K b) = star (algebraMap (𝓞 K) K (a + b))`. Rewrite using `[map_add, star_add]`.

Use the proof step `zero_mem' := ⟨0, M.zero_mem, by`. Rewrite using `[map_zero, LinearMap.zero_apply]`. Use `show (0 : K) = star (algebraMap (𝓞 K) K 0)`. Rewrite using `[map_zero, star_zero]⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `a b ⟨m, hm, e⟩`. Use `⟨a • m, M.smul_mem a hm, ?_⟩` and prove the remaining obligations. Establish `ha : (a • m : W) = (algebraMap (𝓞 K) K a) • m` using `(algebraMap_smul K a m).symm`. Rewrite using `[ha, LinearMap.map_smulₛₗ, LinearMap.smul_apply, e]`. Simplify using `only [smul_eq_mul, starRingEnd_apply]`.

Use `show star (algebraMap (𝓞 K) K a) * star (algebraMap (𝓞 K) K b) = star (algebraMap (𝓞 K) K (a * b))`. Rewrite using `[map_mul, star_mul'] }`. Establish `memI : ∀ o : 𝓞 K, o ∈ I ↔ ∃ m ∈ M, h m z = star (o : K)` using `fun o => Iff.rfl`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Establish `hI : I ≠ ⊤`. Introduce `htop`. Establish `h1 : (1 : 𝓞 K) ∈ I` using `by rw [htop]; exact Submodule.mem_top`. Take `⟨m, hm, e⟩` from `(memI 1).1 h1`. Conclude with `hne m hm (by rw [e]; show star (algebraMap (𝓞 K) K 1) = 1; rw [map_one, star_one])`.

Take `⟨P, hPmax, hIP⟩` from `Ideal.exists_le_maximal I hI`. Establish `hP0 : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hPmax (NumberField.RingOfIntegers.not_isField K)`. Take `⟨c, hc, hc1⟩` from `FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hP0 hPmax.ne_top`. Establish `hPne : (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0`. Rewrite using `[ne_eq, FractionalIdeal.coeIdeal_eq_zero]` and apply the resulting hypothesis.

Rewrite `hc` using `[FractionalIdeal.mem_inv_iff hPne]`. Establish `hcz : (star c) • z ∈ M`. Rewrite using `[memM]`. Introduce `m hm`. Take `⟨t, ht⟩` from `(memM z).1 hz m hm`.

Take `⟨t', ht'⟩` from `star_int t`. Establish `e1 : h m z = star (t' : K)` using `by rw [ht', star_star]; exact ht.symm`. Establish `ht'I : t' ∈ I` using `(memI t').2 ⟨m, hm, e1⟩`. Establish `hcy` using `hc _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨t', hIP ht'I, rfl⟩)`. Rewrite `hcy` using `[FractionalIdeal.mem_one_iff]`.

Take `⟨s, hs⟩` from `hcy`. Take `⟨s', hs'⟩` from `star_int s`. Use `⟨s', ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, e1, ← star_mul']`. Express the relevant statement in the definitionally equal form `(s' : K) = _`.

Rewrite using `[hs']`. Use `congr 1`. Take `⟨o, ho⟩` from `hprim _ hcz`. Take `⟨o', ho'⟩` from `star_int o`. Apply `hc1` to reduce the goal to its premises.

Rewrite using `[FractionalIdeal.mem_one_iff]`. Conclude with `⟨o', by change (o' : K) = c; rw [ho', ho, star_star]⟩`.
-/
theorem exists_one {K : Type} [Field K] [NumberField K] [StarRing K]
    {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (h : W →ₗ⋆[K] W →ₗ[K] K) (M : Submodule (𝓞 K) W)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h M) {z : W} (hz : z ∈ M)
    (hprim : ∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c) : ∃ m ∈ M, h m z = 1 := by
  classical

  have memM : ∀ x : W, x ∈ M ↔ ∀ m ∈ M, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = h m x := by
    intro x
    conv_lhs => rw [← hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]

  let I : Ideal (𝓞 K) :=
    { carrier := {o | ∃ m ∈ M, h m z = star (o : K)}
      add_mem' := by
        rintro a b ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩
        refine ⟨m₁ + m₂, M.add_mem hm₁ hm₂, ?_⟩
        rw [map_add, LinearMap.add_apply, e₁, e₂]
        show star (algebraMap (𝓞 K) K a) + star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a + b))
        rw [map_add, star_add]
      zero_mem' := ⟨0, M.zero_mem, by
        rw [map_zero, LinearMap.zero_apply]
        show (0 : K) = star (algebraMap (𝓞 K) K 0)
        rw [map_zero, star_zero]⟩
      smul_mem' := by
        rintro a b ⟨m, hm, e⟩
        refine ⟨a • m, M.smul_mem a hm, ?_⟩
        have ha : (a • m : W) = (algebraMap (𝓞 K) K a) • m := (algebraMap_smul K a m).symm
        rw [ha, LinearMap.map_smulₛₗ, LinearMap.smul_apply, e]
        simp only [smul_eq_mul, starRingEnd_apply]
        show star (algebraMap (𝓞 K) K a) * star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a * b))
        rw [map_mul, star_mul'] }
  have memI : ∀ o : 𝓞 K, o ∈ I ↔ ∃ m ∈ M, h m z = star (o : K) := fun o => Iff.rfl
  by_contra hne
  push_neg at hne
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 K) ∈ I := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, e⟩ := (memI 1).1 h1
    exact hne m hm (by rw [e]; show star (algebraMap (𝓞 K) K 1) = 1; rw [map_one, star_one])
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I hI
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hPmax (NumberField.RingOfIntegers.not_isField K)
  obtain ⟨c, hc, hc1⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hP0 hPmax.ne_top
  have hPne : (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [FractionalIdeal.mem_inv_iff hPne] at hc

  have hcz : (star c) • z ∈ M := by
    rw [memM]
    intro m hm
    obtain ⟨t, ht⟩ := (memM z).1 hz m hm
    obtain ⟨t', ht'⟩ := star_int t
    have e1 : h m z = star (t' : K) := by rw [ht', star_star]; exact ht.symm
    have ht'I : t' ∈ I := (memI t').2 ⟨m, hm, e1⟩
    have hcy := hc _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨t', hIP ht'I, rfl⟩)
    rw [FractionalIdeal.mem_one_iff] at hcy
    obtain ⟨s, hs⟩ := hcy
    obtain ⟨s', hs'⟩ := star_int s
    refine ⟨s', ?_⟩
    rw [map_smul, smul_eq_mul, e1, ← star_mul']
    change (s' : K) = _
    rw [hs']
    congr 1
  obtain ⟨o, ho⟩ := hprim _ hcz
  obtain ⟨o', ho'⟩ := star_int o
  apply hc1
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨o', by change (o' : K) = c; rw [ho', ho, star_star]⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D u F0 Λ hrow`. Take `⟨_, hMU, hzM, hprim⟩` from `row_lattice_mass_holds D u F0 Λ hrow`. Take `⟨m, hm, hm1⟩` from `exists_one (hWb D F0) (Mof D F0 Λ) hMU hzM hprim`. Take `⟨a, haΛ, rfl⟩` from `(RowMPf.mem_Mof D F0 Λ m).1 hm`. Use `⟨a, haΛ, a.2, ?_⟩` and prove the remaining obligations.

Rewrite `hm1` using `[zbar, hWb_mk]`. Conclude with `hm1`.
-/
theorem row_unit_condition : RowZUnit := by
  intro D u F0 Λ hrow
  obtain ⟨_, hMU, hzM, hprim⟩ := row_lattice_mass_holds D u F0 Λ hrow
  obtain ⟨m, hm, hm1⟩ := exists_one (hWb D F0) (Mof D F0 Λ) hMU hzM hprim
  obtain ⟨a, haΛ, rfl⟩ := (RowMPf.mem_Mof D F0 Λ m).1 hm
  refine ⟨a, haΛ, a.2, ?_⟩
  rw [zbar, hWb_mk] at hm1
  exact hm1

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf.row_unit_condition`.
-/
theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_unit_condition : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnit := PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf.row_unit_condition
