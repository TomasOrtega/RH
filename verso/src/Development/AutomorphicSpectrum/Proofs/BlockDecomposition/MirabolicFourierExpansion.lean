import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerPolyBallLeOfValuationLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnSubsetOfMemNhds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRepsSumEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumTwOrbitEqZero

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [colMat]`. Use `split_ifs`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simpa using continuous_const`.

Consider the case `cast i => simpa [Function.comp_def] using (continuous_apply i).comp (continuous_toAdd (X := Fin n → k))`. Conclude with `continuous_const`.
-/
theorem continuous_colMat (n : ℕ) :
    Continuous (fun v : Multiplicative (Fin n → k) => colMat k n v.toAdd) := by
  refine continuous_matrix fun i j => ?_
  simp only [colMat]
  split_ifs
  · induction i using Fin.lastCases with
    | last => simpa using continuous_const
    | cast i => simpa [Function.comp_def] using (continuous_apply i).comp (continuous_toAdd (X := Fin n → k))
  · exact continuous_const

/- English proof (translation)
Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Conclude with `continuous_const.add (continuous_colMat n)`. Conclude with `continuous_const.sub (continuous_colMat n)`.
-/
theorem continuous_unipIn (n : ℕ) : Continuous (unipIn k n) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat n)
  · exact continuous_const.sub (continuous_colMat n)

/- English proof (translation)
Introduce `v` and use `(hτ v).preimage (continuous_unipIn n)`.
-/
theorem smooth_comp {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (hτ : IsSmooth τ) : IsSmooth (τ.comp (unipIn k n) : Representation ℂ (Multiplicative (Fin n → k)) V) :=
  fun v => (hτ v).preimage (continuous_unipIn n)

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨u, w₀, rfl⟩`. Use `set x : Multiplicative (Fin n → k) := (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u) with hx`. Establish `hu : unipIn k n x = (u : Mir k n)`. Establish `h` using `(unipEquiv k n).apply_symm_apply ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u)`.

Establish `h2` using `congrArg (Subtype.val : MirU k n → GL (Fin (n + 1)) k) h`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `h2`. Use `Submodule.subset_span ⟨⟨x, trivial⟩, w₀, ?_⟩` and prove the remaining obligations. Use `show τ (u : Mir k n) w₀ - _ = τ (unipIn k n x) w₀ - _`.

Rewrite using `[hu]`. Both sides reduce to the same expression.
-/
theorem twKer_le_top (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) (a : Fin n → k) :
    twKer τ (MirUin k n) (thetaA k ψ a) ≤
      twKer (τ.comp (unipIn k n) : Representation ℂ (Multiplicative (Fin n → k)) V) ⊤ (resChr ψ a ⊤) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, w₀, rfl⟩
  set x : Multiplicative (Fin n → k) :=
    (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u) with hx
  have hu : unipIn k n x = (u : Mir k n) := by
    have h := (unipEquiv k n).apply_symm_apply ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u)
    have h2 := congrArg (Subtype.val : MirU k n → GL (Fin (n + 1)) k) h
    apply Subtype.ext
    exact h2
  refine Submodule.subset_span ⟨⟨x, trivial⟩, w₀, ?_⟩
  show τ (u : Mir k n) w₀ - _ = τ (unipIn k n x) w₀ - _
  rw [hu]
  rfl

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_cball_addChar_eq_one ψ hψ`. Use `Subgroup.isOpen_mono (H₁ := polyBall n (t⁻¹ * c)) ?_ (isOpen_polyBall n _)` and prove the remaining obligations. Introduce `x hx a ha`. Use `hc _ ?_` and prove the remaining obligations. Use `Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_` and prove the remaining obligations.

Use `show valuation k (a.toAdd i * x.toAdd i) ≤ valuation k (c : k)`. Establish `h1 : (t : k) * ((t⁻¹ * c : kˣ) : k) = c` using `by simp`. Rewrite using `[map_mul, ← h1, map_mul (valuation k) (t : k)]`. Conclude with `mul_le_mul' (ha i) (hx i)`.
-/
theorem isOpen_ann (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (t : kˣ) :
    IsOpen (ann ψ n t : Set (Multiplicative (Fin n → k))) := by
  obtain ⟨c, hc⟩ := exists_cball_addChar_eq_one ψ hψ
  refine Subgroup.isOpen_mono (H₁ := polyBall n (t⁻¹ * c)) ?_ (isOpen_polyBall n _)
  intro x hx a ha
  refine hc _ ?_
  refine Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
  show valuation k (a.toAdd i * x.toAdd i) ≤ valuation k (c : k)
  have h1 : (t : k) * ((t⁻¹ * c : kˣ) : k) = c := by simp
  rw [map_mul, ← h1, map_mul (valuation k) (t : k)]
  exact mul_le_mul' (ha i) (hx i)

end GlobalTheory.CompanionTheory.MirFourier

open GlobalTheory.CompanionTheory.MirFourier in

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ h1 n V _ _ τ hτ v hv`. Establish `hρ` using `smooth_comp τ hτ`. Use `set ρ : Representation ℂ (Multiplicative (Fin n → k)) V := τ.comp (unipIn k n) with hρdef`. Establish `hv1 : ∀ a : Fin n → k, ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s))` using `fun a => exists_mem_twKer_polyBall ψ ρ a v (twKer_le_top ψ τ a (hv a))`. Establish `hS : {x | ρ x v = v} ∈ 𝓝 (1 : Multiplicative (Fin n → k))` using `(hρ v).mem_nhds (by simp)`.

Take `⟨t, ht⟩` from `ann_subset_of_mem_nhds ψ h1 n hS`. Take `⟨s, hs⟩` from `exists_polyBall_twKer_uniform ψ hψ ρ v t hv1`. Take `⟨R, hRne, hRt, hRsum⟩` from `exists_reps_sum_eq_zero ψ hψ n t s`. Use `GlobalTheory.CompanionTheory.FiniteFourier.eq_zero_of_twKer ρ hρ (polyBall n s) (isCompact_polyBall n s) ((ann ψ n t).subgroupOf _) ?_ v ?_ R hRne (fun a => resChr ψ a (polyBall n s)) ?_ (fun a ha => hs a (hRt a ha)) (fun x hx => hRsum x hx)` and prove the remaining obligations. Conclude with `(isOpen_ann ψ hψ n t).preimage continuous_subtype_val`.

Introduce `x hx`. Conclude with `ht hx`. Introduce `a ha x hx`. Establish `h2` using `hx (Multiplicative.ofAdd a) (hRt a ha)`. Use `show Circle.toUnits (ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)) = 1`.

Establish `h3 : ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1` using `h2`. Rewrite using `[h3, map_one]`.
-/
theorem GlobalTheory.CompanionTheory.MirFourier.fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.Fourier k := by
  intro k _ _ _ _ ψ hψ h1 n V _ _ τ hτ v hv
  have hρ := smooth_comp τ hτ
  set ρ : Representation ℂ (Multiplicative (Fin n → k)) V := τ.comp (unipIn k n) with hρdef
  have hv1 : ∀ a : Fin n → k, ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) :=
    fun a => exists_mem_twKer_polyBall ψ ρ a v (twKer_le_top ψ τ a (hv a))
  have hS : {x | ρ x v = v} ∈ 𝓝 (1 : Multiplicative (Fin n → k)) :=
    (hρ v).mem_nhds (by simp)
  obtain ⟨t, ht⟩ := ann_subset_of_mem_nhds ψ h1 n hS
  obtain ⟨s, hs⟩ := exists_polyBall_twKer_uniform ψ hψ ρ v t hv1
  obtain ⟨R, hRne, hRt, hRsum⟩ := exists_reps_sum_eq_zero ψ hψ n t s
  refine GlobalTheory.CompanionTheory.FiniteFourier.eq_zero_of_twKer ρ hρ (polyBall n s) (isCompact_polyBall n s) ((ann ψ n t).subgroupOf _) ?_ v ?_ R hRne
    (fun a => resChr ψ a (polyBall n s)) ?_ (fun a ha => hs a (hRt a ha)) (fun x hx => hRsum x hx)
  · exact (isOpen_ann ψ hψ n t).preimage continuous_subtype_val
  · intro x hx
    exact ht hx
  · intro a ha x hx
    have h2 := hx (Multiplicative.ofAdd a) (hRt a ha)
    show Circle.toUnits (ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)) = 1
    have h3 : ψ (a ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1 := h2
    rw [h3, map_one]

end
