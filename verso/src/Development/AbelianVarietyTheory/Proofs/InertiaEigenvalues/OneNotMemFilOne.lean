import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.JumpsSES

section Trivial

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

/- English proof (translation)
Proceed by induction on `b, h using Int.le_induction with`. Consider the case `base => exact le_rfl`. Consider the case `succ n _ ih => exact (PD.Fil_anti n).trans ih`.
-/
theorem fil_anti {a b : ℤ} (h : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  induction b, h using Int.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (PD.Fil_anti n).trans ih

/- English proof (translation)
Introduce `h`. Use `PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `PD.not_mem_filtration_two this`.
-/
theorem one_not_mem_fil_one : (1 : BdR) ∉ PD.Fil 1 := by
  intro h
  have := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h
  rw [mul_one] at this
  exact PD.not_mem_filtration_two this

/- English proof (translation)
Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx`. Set `e` to `Module.finBasis Qp V`. Set `c : Fin (finrank Qp V) → V ⊗[Qp] BdR →ₗ[Qp] BdR` to `fun i => (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (LinearMap.rTensor BdR (e.coord i))`. Establish `hsum : ∀ y : V ⊗[Qp] BdR, y = ∑ i, e i ⊗ₜ[Qp] c i y`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[c, TensorProduct.smul_tmul]`.

Consider the case `add a b ha hb`. Simplify using `only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]`. Establish `hc : ∀ i g y, c i (actVdR PD ρ g y) = PD.actdR g (c i y)`. Introduce `i g y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v b`. Use `((PD.actdR g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b` as an intermediate fact. Establish `h2 : PD.actdR g (e.coord i v • b) = e.coord i v • PD.actdR g b` using `this`. Simplify using `only [c, actVdR, LinearMap.comp_apply, AlgebraTensorModule.map_tmul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2, hρ]`.

Simplify using the standard rewrite rules. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hk : ∀ i, ∃ k : K, algebraMap K BdR k = c i x` using `fun i => PD.invdR (c i x) fun g => by rw [← hc, hx]`. Use `⟨?_, fun a ha => ?_, fun a ha hF => ?_⟩` and prove the remaining obligations. Rewrite using `[hsum x]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `hk i`. Conclude with `⟨e i ⊗ₜ k, by simp [hk]⟩`. Rewrite using `[hsum x]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Take `⟨k, hk⟩` from `hk i`. Establish `: c i x ∈ PD.Fil a`. Rewrite using `[← hk, Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ _ (fil_anti PD ha PD.one_mem)`. Conclude with `⟨e i ⊗ₜ ⟨c i x, this⟩, by simp⟩`.

Establish `hF' : ∀ i, ∀ y ∈ FilV PD (LL` using `LL) (V := V) a, c i y ∈ PD.Fil a := by`. Introduce and unpack `i _ ⟨y, rfl⟩`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`.

Establish `: (e.coord i v) • (b : BdR) ∈ (PD.Fil a).restrictScalars Qp` using `Submodule.smul_mem _ _ b.2`. Simplify `this` using `[c]`. Consider the case `add y z hy hz => rw [map_add, map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Rewrite using `[hsum x]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `hk i`. Distinguish the cases in `h0 : k = 0`. Rewrite using `[← hk, h0]`. Simplify using the standard rewrite rules.

It suffices to derive a contradiction. Apply `one_not_mem_fil_one PD` to reduce the goal to its premises. Establish `h1` using `Submodule.smul_mem _ k⁻¹ (fil_anti PD ha (hF' i x hF))`. Rewrite `h1` using `[← hk, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h0, one_smul]`. Then use the resulting hypothesis.
-/
theorem ddR_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K BdR).toLinearMap) ∧
    (∀ a ≤ 0, x ∈ FilV PD (LL := LL) (V := V) a) ∧
    (∀ a, 1 ≤ a → x ∈ FilV PD (LL := LL) (V := V) a → x = 0) := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx
  let e := Module.finBasis Qp V
  let c : Fin (finrank Qp V) → V ⊗[Qp] BdR →ₗ[Qp] BdR := fun i =>
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (LinearMap.rTensor BdR (e.coord i))
  have hsum : ∀ y : V ⊗[Qp] BdR, y = ∑ i, e i ⊗ₜ[Qp] c i y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c, TensorProduct.smul_tmul]
    | add a b ha hb =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]
  have hc : ∀ i g y, c i (actVdR PD ρ g y) = PD.actdR g (c i y) := by
    intro i g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have := ((PD.actdR g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b
      have h2 : PD.actdR g (e.coord i v • b) = e.coord i v • PD.actdR g b := this
      simp only [c, actVdR, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2, hρ]
      simp
    | add a b ha hb => simp only [map_add, ha, hb]
  have hk : ∀ i, ∃ k : K, algebraMap K BdR k = c i x := fun i =>
    PD.invdR (c i x) fun g => by rw [← hc, hx]
  refine ⟨?_, fun a ha => ?_, fun a ha hF => ?_⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    exact ⟨e i ⊗ₜ k, by simp [hk]⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    have : c i x ∈ PD.Fil a := by
      rw [← hk, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (fil_anti PD ha PD.one_mem)
    exact ⟨e i ⊗ₜ ⟨c i x, this⟩, by simp⟩
  · have hF' : ∀ i, ∀ y ∈ FilV PD (LL := LL) (V := V) a, c i y ∈ PD.Fil a := by
      rintro i _ ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have : (e.coord i v) • (b : BdR) ∈ (PD.Fil a).restrictScalars Qp := Submodule.smul_mem _ _ b.2
        simpa [c] using this
      | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz
    rw [hsum x]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    by_cases h0 : k = 0
    · rw [← hk, h0]; simp
    · exfalso
      apply one_not_mem_fil_one PD
      have h1 := Submodule.smul_mem _ k⁻¹ (fil_anti PD ha (hF' i x hF))
      rwa [← hk, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h0, one_smul] at h1

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Apply `ha` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [FildR, Submodule.mem_inf]`. Use `and_congr_right fun hx => ?_` and prove the remaining obligations.

Take `⟨-, h1, h2⟩` from `ddR_of_trivial PD ρ hρ x hx.1`. Break down `lt_or_gt_of_ne h0 with h | h` into its components or cases. Conclude with `⟨fun _ => h1 a (by omega), fun _ => h1 (a + 1) (by omega)⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _`.

Introduce `hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _`.
-/
theorem jumps_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (τ : K →ₐ[Qp] LL) (a : ℤ) (ha : IsJumpV PD ρ τ a) : a = 0 := by
  by_contra h0
  apply ha
  ext x
  simp only [FildR, Submodule.mem_inf]
  refine and_congr_right fun hx => ?_
  obtain ⟨-, h1, h2⟩ := ddR_of_trivial PD ρ hρ x hx.1
  rcases lt_or_gt_of_ne h0 with h | h
  · exact ⟨fun _ => h1 a (by omega), fun _ => h1 (a + 1) (by omega)⟩
  · constructor
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _

end Trivial

/- English proof (translation)
Introduce `D HW l _ K s LL h W T₀ T₁ T₂ ι π hc hS`. Use `⟨fun τ a => ?_, fun τ a ha => ?_⟩` and prove the remaining obligations. Establish `h0 : IsCrys ((D.loc l).PD K) T₀.ρ` using `(GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hS.1 hc`. Establish `h2 : IsCrys ((D.loc l).PD K) T₂.ρ` using `((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hS.2.1 hc).1`. Conclude with `GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l _ _ (D.locT l) K LL T₀ T₁ T₂ ι π hS h0 hc h2 τ a`.

Use `haveI := LL.2 haveI : FiniteDimensional ℚ_[l] W.one.V := Module.Finite.trans ↥LL.1 W.one.V`. Conclude with `jumps_of_trivial _ W.one.ρ W.one_triv τ a ha`.
-/
theorem jumps_ses_and_one : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsSESLat (Qp := ℚ_[l]) ι π → (∀ τ a, IsJumpV ((D.loc l).PD K) T₁.ρ τ a ↔ IsJumpV ((D.loc l).PD K) T₀.ρ τ a ∨ IsJumpV ((D.loc l).PD K) T₂.ρ τ a) ∧ ∀ τ a, IsJumpV ((D.loc l).PD K) W.one.ρ τ a → a = 0 := by
  intro D HW l _ K s LL h W T₀ T₁ T₂ ι π hc hS
  refine ⟨fun τ a => ?_, fun τ a ha => ?_⟩
  · have h0 : IsCrys ((D.loc l).PD K) T₀.ρ :=
      (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hS.1 hc
    have h2 : IsCrys ((D.loc l).PD K) T₂.ρ :=
      ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2
        hS.2.1 hc).1
    exact GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l _ _ (D.locT l) K LL T₀ T₁ T₂ ι π hS h0 hc h2 τ a
  · haveI := LL.2
    haveI : FiniteDimensional ℚ_[l] W.one.V := Module.Finite.trans ↥LL.1 W.one.V
    exact jumps_of_trivial _ W.one.ρ W.one_triv τ a ha

end GlobalTheory.NL.JumpsSES
