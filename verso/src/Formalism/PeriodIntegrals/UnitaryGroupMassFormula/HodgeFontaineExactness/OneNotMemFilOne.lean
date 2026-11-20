import Mathlib
import Formalism.PeriodIntegrals.HodgeOfFon

namespace PI.HodgeOfFon.W.Triv

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Module TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

/- English proof (translation)
The claim follows from `antitone_int_of_succ_le PD.Fil_anti`.
-/
theorem fil_antitone : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti

/- English proof (translation)
Introduce `h`. Establish `h2` using `PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h`. Rewrite `h2` using `[mul_one]`. Conclude with `PD.not_mem_filtration_two (by simpa using h2)`.
-/
theorem one_not_mem_fil_one : (1 : BdR) ∉ PD.Fil 1 := by
  intro h
  have h2 := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h
  rw [mul_one] at h2
  exact PD.not_mem_filtration_two (by simpa using h2)

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply Qp K BdR c, AlgEquiv.commutes]`.
-/
theorem actdR_smul (g : G) (c : Qp) (β : BdR) : PD.actdR g (c • β) = c • PD.actdR g β := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply Qp K BdR c,
    AlgEquiv.commutes]

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

section Coord

variable [DecidableEq (Basis.ofVectorSpaceIndex Qp V)]

noncomputable abbrev coordE (V : Type) [AddCommGroup V] [Module Qp V]
    [DecidableEq (Basis.ofVectorSpaceIndex Qp V)] :
    V ⊗[Qp] BdR ≃ₗ[Qp] (Basis.ofVectorSpaceIndex Qp V →₀ BdR) :=
  equivFinsuppOfBasisLeft (N := BdR) (Basis.ofVectorSpace Qp V)

/- English proof (translation)
Conclude with `TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply _ _ _ _`.
-/
theorem coordE_tmul (v : V) (β : BdR) (i) :
    coordE (BdR := BdR) V (v ⊗ₜ β) i = (Basis.ofVectorSpace Qp V).repr v i • β := by
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply _ _ _ _

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v β`. Rewrite using `[actVdR, TensorProduct.AlgebraTensorModule.map_tmul, hρ, coordE_tmul, coordE_tmul]`. Conclude with `(actdR_smul PD g _ β).symm`.

Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem coordE_act (ρ : Representation LL G V) (hρ : ∀ g x, ρ g x = x) (g : G)
    (x : V ⊗[Qp] BdR) (i) :
    coordE V (actVdR PD ρ g x) i = PD.actdR g (coordE V x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v β =>
    rw [actVdR, TensorProduct.AlgebraTensorModule.map_tmul, hρ, coordE_tmul, coordE_tmul]
    exact (actdR_smul PD g _ β).symm
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v f`. Rewrite using `[TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, coordE_tmul]`.

Conclude with `Submodule.smul_of_tower_mem _ _ f.2`. Consider the case `add y z hy hz`. Simplify using `only [map_add, Finsupp.add_apply]`. Conclude with `add_mem hy hz`.
-/
theorem coordE_mem_fil {a : ℤ} {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) (i) :
    coordE V x i ∈ PD.Fil a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v f =>
    rw [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, coordE_tmul]
    exact Submodule.smul_of_tower_mem _ _ f.2
  | add y z hy hz =>
    simp only [map_add, Finsupp.add_apply]
    exact add_mem hy hz

/- English proof (translation)
Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem mem_DdR_iff (ρ : Representation LL G V) {x : V ⊗[Qp] BdR} :
    x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

/- English proof (translation)
Use `PD.invdR _ fun g => ?_` and prove the remaining obligations. Rewrite using `[← coordE_act PD ρ hρ g x i, (mem_DdR_iff PD ρ).1 hx g]`.
-/
theorem coordE_fixed (ρ : Representation LL G V) (hρ : ∀ g x, ρ g x = x) {x : V ⊗[Qp] BdR}
    (hx : x ∈ DdR PD ρ) (i) : ∃ c : K, algebraMap K BdR c = coordE V x i := by
  refine PD.invdR _ fun g => ?_
  rw [← coordE_act PD ρ hρ g x i, (mem_DdR_iff PD ρ).1 hx g]

/- English proof (translation)
Establish `hx' : x = (coordE (BdR` using `BdR) V).symm (coordE V x) := (LinearEquiv.symm_apply_apply _ x).symm`. Rewrite using `[hx', TensorProduct.equivFinsuppOfBasisLeft_symm_apply]`. Rewrite using `[Finsupp.sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `coordE_fixed PD ρ hρ hx i`.

Establish `hmem : coordE V x i ∈ PD.Fil a`. Rewrite using `[← hc, Algebra.algebraMap_eq_smul_one]`. Conclude with `(fil_antitone PD ha) ((PD.Fil 0).smul_mem c PD.one_mem)`. Conclude with `⟨_ ⊗ₜ ⟨_, hmem⟩, by rw [TensorProduct.AlgebraTensorModule.map_tmul]; rfl⟩`.
-/
theorem DdR_le_filV (ρ : Representation LL G V) (hρ : ∀ g x, ρ g x = x) {a : ℤ} (ha : a ≤ 0)
    {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) : x ∈ FilV PD (LL := LL) (V := V) a := by
  have hx' : x = (coordE (BdR := BdR) V).symm (coordE V x) := (LinearEquiv.symm_apply_apply _ x).symm
  rw [hx', TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := coordE_fixed PD ρ hρ hx i
  have hmem : coordE V x i ∈ PD.Fil a := by
    rw [← hc, Algebra.algebraMap_eq_smul_one]
    exact (fil_antitone PD ha) ((PD.Fil 0).smul_mem c PD.one_mem)
  exact ⟨_ ⊗ₜ ⟨_, hmem⟩, by rw [TensorProduct.AlgebraTensorModule.map_tmul]; rfl⟩

/- English proof (translation)
Establish `hc : ∀ i, coordE V x i = 0`. Introduce `i`. Take `⟨c, hc⟩` from `coordE_fixed PD ρ hρ hx i`. Establish `hm : coordE V x i ∈ PD.Fil 1` using `fil_antitone PD ha (coordE_mem_fil PD hxF i)`. Assume the negation of the conclusion as `hne`.

Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hc, map_zero]`. Apply `one_not_mem_fil_one PD` to reduce the goal to its premises.

Establish `h1 : c⁻¹ • coordE V x i ∈ PD.Fil 1` using `(PD.Fil 1).smul_mem _ hm`. Rewrite `h1` using `[← hc, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one]`. Then use the resulting hypothesis. Establish `h0 : coordE (BdR` using `BdR) V x = 0 := Finsupp.ext hc`. Conclude with `(coordE (BdR := BdR) V).map_eq_zero_iff.1 h0`.
-/
theorem DdR_filV_eq_zero (ρ : Representation LL G V) (hρ : ∀ g x, ρ g x = x) {a : ℤ} (ha : 1 ≤ a)
    {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) (hxF : x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  have hc : ∀ i, coordE V x i = 0 := by
    intro i
    obtain ⟨c, hc⟩ := coordE_fixed PD ρ hρ hx i
    have hm : coordE V x i ∈ PD.Fil 1 := fil_antitone PD ha (coordE_mem_fil PD hxF i)
    by_contra hne
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hne
      rw [← hc, map_zero]
    apply one_not_mem_fil_one PD
    have h1 : c⁻¹ • coordE V x i ∈ PD.Fil 1 := (PD.Fil 1).smul_mem _ hm
    rwa [← hc, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one] at h1
  have h0 : coordE (BdR := BdR) V x = 0 := Finsupp.ext hc
  exact (coordE (BdR := BdR) V).map_eq_zero_iff.1 h0

end Coord

/- English proof (translation)
Assume the negation of the conclusion as `ha0`. Apply `h` to reduce the goal to its premises. Break down `lt_or_gt_of_ne ha0 with hlt | hgt` into its components or cases. Establish `e : ∀ b : ℤ, b ≤ 0 → FildR PD ρ τ b = DdRE PD ρ τ` using `fun b hb => inf_eq_left.2 fun x hx => DdR_le_filV PD ρ hρ hb hx.1`. Rewrite using `[e (a + 1) (by omega), e a (by omega)]`.

Establish `e : ∀ b : ℤ, 1 ≤ b → FildR PD ρ τ b = ⊥` using `fun b hb => eq_bot_iff.2 fun x hx => (Submodule.mem_bot _).2 (DdR_filV_eq_zero PD ρ hρ hb hx.1.1 hx.2)`. Rewrite using `[e (a + 1) (by omega), e a (by omega)]`.
-/
theorem no_jump (ρ : Representation LL G V) (hρ : ∀ g x, ρ g x = x) (τ : K →ₐ[Qp] LL) (a : ℤ)
    (h : IsJumpV PD ρ τ a) : a = 0 := by
  classical
  by_contra ha0
  apply h
  rcases lt_or_gt_of_ne ha0 with hlt | hgt
  · have e : ∀ b : ℤ, b ≤ 0 → FildR PD ρ τ b = DdRE PD ρ τ := fun b hb =>
      inf_eq_left.2 fun x hx => DdR_le_filV PD ρ hρ hb hx.1
    rw [e (a + 1) (by omega), e a (by omega)]
  · have e : ∀ b : ℤ, 1 ≤ b → FildR PD ρ τ b = ⊥ := fun b hb =>
      eq_bot_iff.2 fun x hx => (Submodule.mem_bot _).2 (DdR_filV_eq_zero PD ρ hρ hb hx.1.1 hx.2)
    rw [e (a + 1) (by omega), e a (by omega)]

end PI.HodgeOfFon.W.Triv

namespace PI.HodgeOfFon.W

end PI.HodgeOfFon.W
