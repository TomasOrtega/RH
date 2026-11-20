import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsFiniteRepsScaledLatticeCardNorm

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

/- English proof (translation)
Introduce `F _ _ κ _ _ N Φ hN hSB`. Take `⟨hsupp, hper⟩` from `hSB`. Establish `memLL : ∀ y : κ → F, y ∈ LL F κ ↔ ∀ k, IsIntegral ℤ (y k)`. Introduce `y`. Simplify using `[LL, AddSubgroup.mem_pi, mem_integralClosure_iff]`.

Establish `memaL : ∀ (c : F) (x : κ → F), x ∈ aL κ c ↔ ∃ y ∈ LL F κ, c • y = x`. Introduce `c x`. Simplify using `[aL]`. Establish `intB : ∀ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, IsIntegral ℤ (∑ i, c i • integralBasis F i)`. Introduce `c`.

Establish `hmem : (∑ i, c i • integralBasis F i) ∈ Submodule.span ℤ (Set.range (integralBasis F))` using `(Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, rfl⟩`. Take `⟨a, ha⟩` from `(mem_span_integralBasis F).mp hmem`. Rewrite using `[← ha]`. Conclude with `RingOfIntegers.isIntegral_coe a`. Establish `decomp : ∀ z : F, IsIntegral ℤ z → ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • integralBasis F i = z`.

Introduce `z hz`. Establish `hmem : z ∈ Submodule.span ℤ (Set.range (integralBasis F))` using `(mem_span_integralBasis F).mpr ⟨⟨z, hz⟩, rfl⟩`. Conclude with `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem`. Establish `hNF : (N : F) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hM : (0 : ℤ) < ((N * N : ℕ) : ℤ)` using `by positivity`.

Set `g : (κ → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin (N * N)) → ℂ` to `fun r => Φ (fun k => (N : F)⁻¹ * ∑ i, (((r k i : ℕ) : ℤ) • integralBasis F i))`. Use `((Set.finite_range g).insert 0).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Set.mem_insert_iff]`. Distinguish the cases in `h0 : Φ x = 0`.

Conclude with `Or.inl h0`. Use `right`. Take `⟨y, hy, rfl⟩` from `(memaL _ x).mp (hsupp x h0)`. Establish `hyi` using `(memLL y).mp hy`. Use `choose c hc using fun k => decomp (y k) (hyi k)`.

Establish `hcast : ∀ k i, (((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) = c k i % ((N * N : ℕ) : ℤ)` using `fun k i => Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')`. Use `⟨fun k i => ⟨(c k i % ((N * N : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h2` using `Int.emod_lt_of_pos (c k i) hM`. Establish `h3` using `hcast k i`. Use linear arithmetic over natural numbers and integers.

Use `show Φ (fun k => (N : F)⁻¹ * ∑ i, ((((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) • integralBasis F i)) = Φ ((N : F)⁻¹ • y)`. Simplify using `only [hcast]`. Establish `hl : ((N : F)⁻¹ • y - fun k => (N : F)⁻¹ * ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) ∈ aL κ (N : F)`. Rewrite using `[memaL]`. Use `⟨fun k => ∑ i, (c k i / ((N * N : ℕ) : ℤ)) • integralBasis F i, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[memLL]`. Introduce `k`. Conclude with `intB _`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`.

Rewrite using `[← hc k, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Simplify using `only [zsmul_eq_mul]`. Establish `hdiv : ((c k i : ℤ) : F) = ((N : F) * N) * ((c k i / ((N * N : ℕ) : ℤ) : ℤ) : F) + ((c k i % ((N * N : ℕ) : ℤ) : ℤ) : F)`. Conclude with `(Int.mul_ediv_add_emod (c k i) ((N * N : ℕ) : ℤ)).symm` after adjusting the coercions.

Establish `key : ∀ (cF rF qF : F), cF = ((N : F) * N) * qF + rF → (N : F) * (qF * integralBasis F i) = (N : F)⁻¹ * (cF * integralBasis F i) - (N : F)⁻¹ * (rF * integralBasis F i)`. Introduce `cF rF qF h`. Rewrite using `[h]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Conclude with `key _ _ _ hdiv`. Establish `hp` using `hper (fun k => (N : F)⁻¹ * ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) _ hl`. Rewrite `hp` using `[add_sub_cancel]`. Conclude with `hp.symm`.
-/
theorem isSB_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ)
    (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  intro F _ _ κ _ _ N Φ hN hSB
  classical
  obtain ⟨hsupp, hper⟩ := hSB
  have memLL : ∀ y : κ → F, y ∈ LL F κ ↔ ∀ k, IsIntegral ℤ (y k) := by
    intro y
    simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]
  have memaL : ∀ (c : F) (x : κ → F), x ∈ aL κ c ↔ ∃ y ∈ LL F κ, c • y = x := by
    intro c x
    simp [aL]
  have intB : ∀ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ,
      IsIntegral ℤ (∑ i, c i • integralBasis F i) := by
    intro c
    have hmem : (∑ i, c i • integralBasis F i) ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, rfl⟩
    obtain ⟨a, ha⟩ := (mem_span_integralBasis F).mp hmem
    rw [← ha]
    exact RingOfIntegers.isIntegral_coe a
  have decomp : ∀ z : F, IsIntegral ℤ z →
      ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • integralBasis F i = z := by
    intro z hz
    have hmem : z ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (mem_span_integralBasis F).mpr ⟨⟨z, hz⟩, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hM : (0 : ℤ) < ((N * N : ℕ) : ℤ) := by positivity
  let g : (κ → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin (N * N)) → ℂ := fun r =>
    Φ (fun k => (N : F)⁻¹ * ∑ i, (((r k i : ℕ) : ℤ) • integralBasis F i))
  refine ((Set.finite_range g).insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  rw [Set.mem_insert_iff]
  by_cases h0 : Φ x = 0
  · exact Or.inl h0
  right
  obtain ⟨y, hy, rfl⟩ := (memaL _ x).mp (hsupp x h0)
  have hyi := (memLL y).mp hy
  choose c hc using fun k => decomp (y k) (hyi k)
  have hcast : ∀ k i, (((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) = c k i % ((N * N : ℕ) : ℤ) :=
    fun k i => Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  refine ⟨fun k i => ⟨(c k i % ((N * N : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
  · have h2 := Int.emod_lt_of_pos (c k i) hM
    have h3 := hcast k i
    omega
  · show Φ (fun k => (N : F)⁻¹ *
        ∑ i, ((((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) • integralBasis F i)) = Φ ((N : F)⁻¹ • y)
    simp only [hcast]
    have hl : ((N : F)⁻¹ • y - fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) ∈ aL κ (N : F) := by
      rw [memaL]
      refine ⟨fun k => ∑ i, (c k i / ((N * N : ℕ) : ℤ)) • integralBasis F i, ?_, ?_⟩
      · rw [memLL]
        intro k
        exact intB _
      · funext k
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [← hc k, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [zsmul_eq_mul]
        have hdiv : ((c k i : ℤ) : F) = ((N : F) * N) * ((c k i / ((N * N : ℕ) : ℤ) : ℤ) : F) +
            ((c k i % ((N * N : ℕ) : ℤ) : ℤ) : F) := by
          exact_mod_cast (Int.mul_ediv_add_emod (c k i) ((N * N : ℕ) : ℤ)).symm
        have key : ∀ (cF rF qF : F), cF = ((N : F) * N) * qF + rF →
            (N : F) * (qF * integralBasis F i) =
              (N : F)⁻¹ * (cF * integralBasis F i) - (N : F)⁻¹ * (rF * integralBasis F i) := by
          intro cF rF qF h
          rw [h]
          field_simp
          ring
        exact key _ _ _ hdiv
    have hp := hper (fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) _ hl
    rw [add_sub_cancel] at hp
    exact hp.symm

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.isSB_range_finite | exact GlobalTheory.HilbertThetaSeries.isSB_range_finite | (intros; apply GlobalTheory.HilbertThetaSeries.isSB_range_finite <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.lattice_periodic_function_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ) (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.isSB_range_finite | exact GlobalTheory.HilbertThetaSeries.isSB_range_finite | (intros; apply GlobalTheory.HilbertThetaSeries.isSB_range_finite <;> assumption)
