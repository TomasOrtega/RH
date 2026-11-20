import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzGenFun

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix MeasureTheory

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

/- English proof (translation)
It suffices to establish `key : ∀ F : Finset (GL (Fin m) k), (↑F ⊆ (unipB k (Fin m) : Set (GL (Fin m) k))) → ∃ Λ : Module.Dual ℂ (PS k m), (∀ u ∈ F, ∀ x, Λ (psOne k m u x) = thC ψ u * Λ x) ∧ Λ (cellVec hS1 hS4) ≠ 0 by`. Take `⟨l, hl, hlv⟩` from `exists_functional_of_finite (psOne k m) (unipB k (Fin m) : Set (GL (Fin m) k)) (thC ψ) (cellVec hS1 hS4) key`. Conclude with `⟨l, fun u hu x => hl u hu x, hlv⟩`. Introduce `F hF`. Take `⟨C, hCc, hCN, hFC⟩` from `exists_compact_unip F (fun u hu => hF hu)`.

Use `letI : MeasurableSpace C := borel C`. Use `haveI : BorelSpace C := ⟨rfl⟩`. Use `haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc`. Set `μ : Measure C` to `Measure.haar`. Set `Φ : PS k m → C → ℂ` to `fun f c => f.1.1 (wRev k m * (c : GL (Fin m) k)⁻¹) * thC ψ (c : GL (Fin m) k)`.

Establish `hΦc : ∀ f, Continuous (Φ f)` using `fun f => ((continuous_ps f).comp (continuous_const.mul continuous_subtype_val.inv)).mul ((continuous_thC ψ hψc).comp continuous_subtype_val)`. Establish `hΦi : ∀ f, Integrable (Φ f) μ` using `fun f => (hΦc f).integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))`. Set `Λ : Module.Dual ℂ (PS k m)` to `{ toFun := fun f => ∫ c, Φ f c ∂μ map_add' := fun f g => by`. Rewrite using `[← integral_add (hΦi f) (hΦi g)]`. Use `congr 1`.

Use function extensionality and compare the values at `c`. Simplify using `[Φ, add_mul]`. Use the proof step `map_smul' := fun a f => by`. Rewrite using `[RingHom.id_apply, smul_eq_mul, ← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `c`. Simplify using `[Φ, mul_assoc] }`. Use `⟨Λ, fun u hu x => ?_, ?_⟩` and prove the remaining obligations. Establish `huC : u ∈ C` using `hFC u hu`. Establish `huN : u ∈ unipB k (Fin m)` using `hCN huC`.

Set `uC : C` to `⟨u, huC⟩`. Use `show ∫ c, Φ (psOne k m u x) c ∂μ = thC ψ u * ∫ c, Φ x c ∂μ`. Rewrite using `[← integral_mul_left_eq_self (Φ x) uC⁻¹, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `c`.

Establish `hcN : (c : GL (Fin m) k) ∈ unipB k (Fin m)` using `hCN c.2`. Establish `e1 : ((uC⁻¹ * c : C) : GL (Fin m) k) = u⁻¹ * c` using `rfl`. Establish `e2 : thC ψ (c : GL (Fin m) k) = thC ψ u * thC ψ (u⁻¹ * (c : GL (Fin m) k))`. Rewrite using `[← thC_mul ψ huN (mul_mem (inv_mem huN) hcN), mul_inv_cancel_left]`. Simplify using `only [Φ, e1]`.

Rewrite using `[e2, _root_.mul_inv_rev, inv_inv]`. Use `show x.1.1 (wRev k m * (c : GL (Fin m) k)⁻¹ * u) * _ = _`. Rewrite using `[mul_assoc (wRev k m)]`. Expand and normalize the polynomial expressions, which then agree. Use `show ∫ c, Φ (cellVec hS1 hS4) c ∂μ ≠ 0 set s : Set C := {c | (c : GL (Fin m) k) ∈ KOne k (Fin m)} with hsdef`.

Establish `hs : IsOpen s` using `GlobalTheory.StepData.isOpen_KOne.preimage continuous_subtype_val`. Establish `hΦ : Φ (cellVec hS1 hS4) = s.indicator (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `c`. Simplify using `only [Φ, cellVec_apply]`. Rewrite using `[cellFun_wRev hS1 hS4 hS2 hS3 (hCN c.2)]`.

Distinguish the cases in `hcK : (c : GL (Fin m) k) ∈ KOne k (Fin m)`. Rewrite using `[if_pos hcK, Set.indicator_of_mem (show c ∈ s from hcK), thC_of_mem_KOne ψ hψ hcK, one_mul]`. Rewrite using `[if_neg hcK, Set.indicator_of_notMem (show c ∉ s from hcK), zero_mul]`. Rewrite using `[hΦ, integral_indicator_const _ hs.measurableSet]`. Establish `hpos : 0 < μ.real s` using `ENNReal.toReal_pos (hs.measure_ne_zero μ ⟨1, show ((1 : C) : GL (Fin m) k) ∈ KOne k (Fin m) from one_mem _⟩) (measure_ne_top μ s)`.

Rewrite using `[Complex.real_smul, mul_one]`. Conclude with `hpos.ne'` after adjusting the coercions.
-/
theorem exists_cell_functional {S : Subgroup (GL (Fin m) k)} (hS1 : KOne k (Fin m) ≤ S)
    (hS2 : S ≤ KO k (Fin m))
    (hS3 : ∀ y ∈ S, ∀ a b, a < b → valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b) < 1)
    (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)
    (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ : ∀ x, valuation k x < 1 → ψ x = 1) :
    ∃ l : Module.Dual ℂ (PS k m), IsFunctional ψ⁻¹ (psOne k m) l ∧ l (cellVec hS1 hS4) ≠ 0 := by
  suffices key : ∀ F : Finset (GL (Fin m) k), (↑F ⊆ (unipB k (Fin m) : Set (GL (Fin m) k))) →
      ∃ Λ : Module.Dual ℂ (PS k m), (∀ u ∈ F, ∀ x, Λ (psOne k m u x) = thC ψ u * Λ x) ∧ Λ (cellVec hS1 hS4) ≠ 0 by
    obtain ⟨l, hl, hlv⟩ := exists_functional_of_finite (psOne k m) (unipB k (Fin m) : Set (GL (Fin m) k)) (thC ψ)
      (cellVec hS1 hS4) key
    exact ⟨l, fun u hu x => hl u hu x, hlv⟩
  intro F hF
  obtain ⟨C, hCc, hCN, hFC⟩ := exists_compact_unip F (fun u hu => hF hu)
  letI : MeasurableSpace C := borel C
  haveI : BorelSpace C := ⟨rfl⟩
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  let μ : Measure C := Measure.haar
  let Φ : PS k m → C → ℂ := fun f c => f.1.1 (wRev k m * (c : GL (Fin m) k)⁻¹) * thC ψ (c : GL (Fin m) k)
  have hΦc : ∀ f, Continuous (Φ f) := fun f =>
    ((continuous_ps f).comp (continuous_const.mul continuous_subtype_val.inv)).mul
      ((continuous_thC ψ hψc).comp continuous_subtype_val)
  have hΦi : ∀ f, Integrable (Φ f) μ := fun f => (hΦc f).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  let Λ : Module.Dual ℂ (PS k m) :=
    { toFun := fun f => ∫ c, Φ f c ∂μ
      map_add' := fun f g => by
        rw [← integral_add (hΦi f) (hΦi g)]
        congr 1
        funext c
        simp [Φ, add_mul]
      map_smul' := fun a f => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext c
        simp [Φ, mul_assoc] }
  refine ⟨Λ, fun u hu x => ?_, ?_⟩
  · have huC : u ∈ C := hFC u hu
    have huN : u ∈ unipB k (Fin m) := hCN huC
    let uC : C := ⟨u, huC⟩
    show ∫ c, Φ (psOne k m u x) c ∂μ = thC ψ u * ∫ c, Φ x c ∂μ
    rw [← integral_mul_left_eq_self (Φ x) uC⁻¹, ← integral_const_mul]
    congr 1
    funext c
    have hcN : (c : GL (Fin m) k) ∈ unipB k (Fin m) := hCN c.2
    have e1 : ((uC⁻¹ * c : C) : GL (Fin m) k) = u⁻¹ * c := rfl
    have e2 : thC ψ (c : GL (Fin m) k) = thC ψ u * thC ψ (u⁻¹ * (c : GL (Fin m) k)) := by
      rw [← thC_mul ψ huN (mul_mem (inv_mem huN) hcN), mul_inv_cancel_left]
    simp only [Φ, e1]
    rw [e2, _root_.mul_inv_rev, inv_inv]
    show x.1.1 (wRev k m * (c : GL (Fin m) k)⁻¹ * u) * _ = _
    rw [mul_assoc (wRev k m)]
    ring
  · show ∫ c, Φ (cellVec hS1 hS4) c ∂μ ≠ 0
    set s : Set C := {c | (c : GL (Fin m) k) ∈ KOne k (Fin m)} with hsdef
    have hs : IsOpen s := GlobalTheory.StepData.isOpen_KOne.preimage continuous_subtype_val
    have hΦ : Φ (cellVec hS1 hS4) = s.indicator (fun _ => (1 : ℂ)) := by
      funext c
      simp only [Φ, cellVec_apply]
      rw [cellFun_wRev hS1 hS4 hS2 hS3 (hCN c.2)]
      by_cases hcK : (c : GL (Fin m) k) ∈ KOne k (Fin m)
      · rw [if_pos hcK, Set.indicator_of_mem (show c ∈ s from hcK), thC_of_mem_KOne ψ hψ hcK, one_mul]
      · rw [if_neg hcK, Set.indicator_of_notMem (show c ∉ s from hcK), zero_mul]
    rw [hΦ, integral_indicator_const _ hs.measurableSet]
    have hpos : 0 < μ.real s :=
      ENNReal.toReal_pos (hs.measure_ne_zero μ ⟨1, show ((1 : C) : GL (Fin m) k) ∈ KOne k (Fin m) from one_mem _⟩) (measure_ne_top μ s)
    rw [Complex.real_smul, mul_one]
    exact_mod_cast hpos.ne'

end DiscreteGroups.sglob.DzType
