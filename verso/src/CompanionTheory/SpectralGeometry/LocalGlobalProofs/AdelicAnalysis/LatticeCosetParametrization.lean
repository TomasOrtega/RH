import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

/- English proof (translation)
Introduce `F _ _ ι _ _ _ ρ b a N hN`. Establish `hOh` using `(GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1`. Establish `hN0 : (N : F) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`. Establish `hNu : IsUnit ((N : GlobalTheory.CompanionTheory.SW.Core.A F))`. Rewrite using `[← map_natCast (algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F))]`.

Conclude with `(isUnit_iff_ne_zero.mpr hN0).map _`. Establish `hcoe : ∀ c : InfinitePlace F → ℤ, ((b.equivFun.symm c : 𝓞 F) : F) = ∑ v, (c v : F) * (b v : F)`. Introduce `c`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Simplify using `[zsmul_eq_mul]`.

Use `⟨fun n i => a i + (N : F) * ∑ v, (n (i, v) : F) * (b v : F), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n m h`. Use function extensionality and compare the values at `p`. Take `⟨i, v⟩` from `p`. Establish `hi` using `congrFun h i`.

Simplify using `only [add_right_inj] at hi`. Establish `hi'` using `mul_left_cancel₀ hN0 hi`. Establish `hO : b.equivFun.symm (fun v => n (i, v)) = b.equivFun.symm (fun v => m (i, v))`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hcoe, hcoe]`.

Conclude with `hi'`. Conclude with `congrFun (b.equivFun.symm.injective hO) v`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hx' : ∀ i, ∃ y ∈ GlobalTheory.CompanionTheory.SW.Core.Oh F, (toA x - toA a) i = (N : GlobalTheory.CompanionTheory.SW.Core.A F) * y` using `hx`. Establish `hr : ∀ i, ∃ r : 𝓞 F, (r : F) = (x i - a i) / N`. Introduce `i`. Take `⟨y, hy, hxy⟩` from `hx' i`. Establish `hy' : y = algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) ((x i - a i) / N)`.

Apply `hNu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← hxy, ← map_natCast (algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F)), ← map_mul, mul_div_cancel₀ _ hN0, map_sub]`. Both sides reduce to the same expression. Conclude with `(hOh _).mp (hy' ▸ hy)`. Use `choose r hr using hr`.

Use `⟨fun p => b.equivFun (r p.1) p.2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show a i + (N : F) * ∑ v, ((b.equivFun (r i) v : ℤ) : F) * (b v : F) = x i`. Rewrite using `[← hcoe, LinearEquiv.symm_apply_apply, hr i]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨n, rfl⟩`. Introduce `i`. Use `⟨algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) (∑ v, (n (i, v) : F) * (b v : F)), (hOh _).mpr ⟨b.equivFun.symm (fun v => n (i, v)), hcoe _⟩, ?_⟩` and prove the remaining obligations. Use `show algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) (a i + (N : F) * ∑ v, (n (i, v) : F) * (b v : F)) - algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) (a i) = _`.

Rewrite using `[map_add, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Introduce `n`. Use function extensionality and compare the values at `p`. Take `⟨i, w⟩` from `p`.

Simplify using `only [emb, gM, EM, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Pi.add_apply, map_add, map_mul, map_sum, map_natCast, map_intCast, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_e …`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos rfl]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rational_coset_param : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (a : ι → F) (N : ℕ), 0 < N →
    ∃ e : (ι × InfinitePlace F → ℤ) → ι → F, Function.Injective e ∧
      (∀ x : ι → F, toA x - toA a ∈ latN F ι N ↔ x ∈ Set.range e) ∧
      ∀ n, emb ρ (e n) = emb ρ a + gM ρ (fun v => b v) N *ᵥ fun p => (n p : ℝ) := by
  intro F _ _ ι _ _ _ ρ b a N hN
  have hOh := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hNu : IsUnit ((N : GlobalTheory.CompanionTheory.SW.Core.A F)) := by
    rw [← map_natCast (algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F))]
    exact (isUnit_iff_ne_zero.mpr hN0).map _
  have hcoe : ∀ c : InfinitePlace F → ℤ,
      ((b.equivFun.symm c : 𝓞 F) : F) = ∑ v, (c v : F) * (b v : F) := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    simp [zsmul_eq_mul]
  refine ⟨fun n i => a i + (N : F) * ∑ v, (n (i, v) : F) * (b v : F), ?_, ?_, ?_⟩
  · intro n m h
    funext p
    obtain ⟨i, v⟩ := p
    have hi := congrFun h i
    simp only [add_right_inj] at hi
    have hi' := mul_left_cancel₀ hN0 hi
    have hO : b.equivFun.symm (fun v => n (i, v)) = b.equivFun.symm (fun v => m (i, v)) := by
      apply RingOfIntegers.ext
      rw [hcoe, hcoe]
      exact hi'
    exact congrFun (b.equivFun.symm.injective hO) v
  · intro x
    constructor
    · intro hx
      have hx' : ∀ i, ∃ y ∈ GlobalTheory.CompanionTheory.SW.Core.Oh F, (toA x - toA a) i = (N : GlobalTheory.CompanionTheory.SW.Core.A F) * y := hx
      have hr : ∀ i, ∃ r : 𝓞 F, (r : F) = (x i - a i) / N := by
        intro i
        obtain ⟨y, hy, hxy⟩ := hx' i
        have hy' : y = algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) ((x i - a i) / N) := by
          apply hNu.mul_left_cancel
          rw [← hxy, ← map_natCast (algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F)), ← map_mul,
            mul_div_cancel₀ _ hN0, map_sub]
          rfl
        exact (hOh _).mp (hy' ▸ hy)
      choose r hr using hr
      refine ⟨fun p => b.equivFun (r p.1) p.2, ?_⟩
      funext i
      show a i + (N : F) * ∑ v, ((b.equivFun (r i) v : ℤ) : F) * (b v : F) = x i
      rw [← hcoe, LinearEquiv.symm_apply_apply, hr i]
      field_simp
      ring
    · rintro ⟨n, rfl⟩
      intro i
      refine ⟨algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) (∑ v, (n (i, v) : F) * (b v : F)),
        (hOh _).mpr ⟨b.equivFun.symm (fun v => n (i, v)), hcoe _⟩, ?_⟩
      show algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) (a i + (N : F) * ∑ v, (n (i, v) : F) * (b v : F)) -
          algebraMap F (GlobalTheory.CompanionTheory.SW.Core.A F) (a i) = _
      rw [map_add, map_mul, map_natCast]
      ring
  · intro n
    funext p
    obtain ⟨i, w⟩ := p
    simp only [emb, gM, EM, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Pi.add_apply, map_add, map_mul, map_sum, map_natCast, map_intCast,
      Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      nsmul_eq_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [if_pos rfl]
    ring

end GlobalTheory.CompanionTheory.SW.ThW
