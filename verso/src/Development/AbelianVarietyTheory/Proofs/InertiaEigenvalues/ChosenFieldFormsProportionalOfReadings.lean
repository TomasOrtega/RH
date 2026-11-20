import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y hx hy`. Take `⟨c, e⟩` from `hx`. Take `⟨c', e'⟩` from `hy`.

Use `⟨c + c', ?_⟩` and prove the remaining obligations. Rewrite using `[e, e']`. Simplify using `[TensorProduct.add_tmul, Finset.sum_add_distrib]`. Consider the case `tmul a f`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c`.

Use `choose y hy using hd`. Establish `e : (d : O) • (a ⊗ₜ[O] f) = ∑ c, (y c • a) ⊗ₜ[O] v c`. Rewrite using `[← TensorProduct.tmul_smul]`. Use `conv_lhs => rw [← v.sum_repr f]`. Rewrite using `[Finset.smul_sum, TensorProduct.tmul_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul, ← algebraMap_smul K (y c), hy, smul_assoc]`. Establish `h0` using `hinj d (nonZeroDivisors.coe_ne_zero d)`. Use `⟨fun c => (algebraMap O L d)⁻¹ • y c • a, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[← algebraMap_smul L (d : O)]`.

Rewrite using `[← inv_smul_smul₀ h0 (a ⊗ₜ[O] f), e, Finset.smul_sum]`. Simplify using `only [TensorProduct.smul_tmul']`.
-/
private theorem tensor_exists_basis_expansion {O K L M ι : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra O L] [AddCommGroup M] [Module O M] [Module K M] [IsScalarTower O K M] [Fintype ι]
    (hinj : ∀ d : O, d ≠ 0 → algebraMap O L d ≠ 0) (v : Module.Basis ι K M) (x : L ⊗[O] M) :
    ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨c, e⟩ := hx
    obtain ⟨c', e'⟩ := hy
    refine ⟨c + c', ?_⟩
    rw [e, e']
    simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    have e : (d : O) • (a ⊗ₜ[O] f) = ∑ c, (y c • a) ⊗ₜ[O] v c := by
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul K (y c), hy, smul_assoc]
    have h0 := hinj d (nonZeroDivisors.coe_ne_zero d)
    refine ⟨fun c => (algebraMap O L d)⁻¹ • y c • a, ?_⟩
    rw [← algebraMap_smul L (d : O)] at e
    rw [← inv_smul_smul₀ h0 (a ⊗ₜ[O] f), e, Finset.smul_sum]
    simp only [TensorProduct.smul_tmul']

/- English proof (translation)
Take `⟨α, rfl⟩` from `hsp A`. Establish `hind` using `Fintype.linearIndependent_iff.1 hli`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Rewrite `h` using `[map_zero, smul_zero, map_sum]`.

Simplify using `only [hR] at h`. Establish `h2 : ∀ a, α a = 0` using `fun a => ε.injective ((hind _ h a).trans (map_zero _).symm)`. Simplify using `[h2]`. Take `⟨β, rfl⟩` from `hsp B`. Introduce `hB`.

Rewrite `h` using `[map_sum, map_sum]`. Simplify using `only [hR] at h`. Establish `h1 : ∀ a, ε (α a) - z * ε (β a) = 0` using `hind (fun a => ε (α a) - z * ε (β a)) (by`. Simplify using `only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, h, sub_self])`. Establish `h2 : ∃ a, β a ≠ 0`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hB (by simp [hc])`. Take `⟨a0, ha0⟩` from `h2`. Establish `h3 : ε (β a0) ≠ 0` using `(map_ne_zero ε).2 ha0`.

Establish `ht : ε (α a0 / β a0) = z`. Rewrite using `[map_div₀, sub_eq_zero.1 (h1 a0), mul_div_cancel_right₀ _ h3]`. Use `⟨α a0 / β a0, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul]`. Use `congr 1`. Apply `ε.injective` to reduce the goal to its premises. Rewrite using `[map_mul, ht, sub_eq_zero.1 (h1 a)]`.
-/
private theorem tensor_scalar_relation {O L M N ι : Type*} [CommRing O] [Field L] [Algebra O L] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] (ε : L →+* ℂ) (v : ι → M) (r : M → N) (R : L ⊗[O] M →ₛₗ[ε] N)
    (hR : ∀ a f, R (a ⊗ₜ f) = ε a • r f) (hli : LinearIndependent ℂ fun c => r (v c))
    (hsp : ∀ x : L ⊗[O] M, ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a) (A B : L ⊗[O] M) (z : ℂ) (h : R A = z • R B) :
    (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : L, ε t = z ∧ A = t • B) := by
  obtain ⟨α, rfl⟩ := hsp A
  have hind := Fintype.linearIndependent_iff.1 hli
  constructor
  · rintro rfl
    rw [map_zero, smul_zero, map_sum] at h
    simp only [hR] at h
    have h2 : ∀ a, α a = 0 := fun a => ε.injective ((hind _ h a).trans (map_zero _).symm)
    simp [h2]
  · obtain ⟨β, rfl⟩ := hsp B
    intro hB
    rw [map_sum, map_sum] at h
    simp only [hR] at h
    have h1 : ∀ a, ε (α a) - z * ε (β a) = 0 := hind (fun a => ε (α a) - z * ε (β a)) (by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, h, sub_self])
    have h2 : ∃ a, β a ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hB (by simp [hc])
    obtain ⟨a0, ha0⟩ := h2
    have h3 : ε (β a0) ≠ 0 := (map_ne_zero ε).2 ha0
    have ht : ε (α a0 / β a0) = z := by
      rw [map_div₀, sub_eq_zero.1 (h1 a0), mul_div_cancel_right₀ _ h3]
    refine ⟨α a0 / β a0, ht, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    apply ε.injective
    rw [map_mul, ht, sub_eq_zero.1 (h1 a)]

/- English proof (translation)
Introduce `D c w ρ hρ j rd hF ε hε A B z h`. Set `v` to `Module.finBasis (FractionRing (D.ntw.O (c.twI w))) (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w))`. Establish `hinj : ∀ d : D.ntw.O (c.twI w), d ≠ 0 → algebraMap _ (KE c w) d ≠ 0` using `fun d hd h0 => by`. Establish `h1` using `congrArg ε h0`. Rewrite `h1` using `[IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply, hρ.ek_e, map_zero]`.

Conclude with `hd (ρ.eO_injective (c.twI w) (c.sd w) (h1.trans (map_zero _).symm))`. Conclude with `tensor_scalar_relation ε v rd (rdF rd hρ hε) (rdF_tmul hρ hε) (hF _ v v.linearIndependent) (tensor_exists_basis_expansion hinj v) A B z h`.
-/
theorem _root_.GlobalTheory.T.chosenField_forms_proportional_of_readings : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)), Faithful rd → ∀ (ε : KE c w →+* ℂ) (hε : Extends ρ ε) (A B : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w)) (z : ℂ),
  rdF rd hρ hε A = z • rdF rd hρ hε B → (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : KE c w, ε t = z ∧ A = t • B) := by
  intro D c w ρ hρ j rd hF ε hε A B z h
  let v := Module.finBasis (FractionRing (D.ntw.O (c.twI w))) (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w))
  have hinj : ∀ d : D.ntw.O (c.twI w), d ≠ 0 → algebraMap _ (KE c w) d ≠ 0 := fun d hd h0 => by
    have h1 := congrArg ε h0
    rw [IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply, hρ.ek_e, map_zero] at h1
    exact hd (ρ.eO_injective (c.twI w) (c.sd w) (h1.trans (map_zero _).symm))
  exact tensor_scalar_relation ε v rd (rdF rd hρ hε) (rdF_tmul hρ hε) (hF _ v v.linearIndependent) (tensor_exists_basis_expansion hinj v) A B z h
