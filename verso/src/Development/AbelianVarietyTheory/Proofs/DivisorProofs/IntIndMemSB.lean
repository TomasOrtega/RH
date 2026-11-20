import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def intInd (n d : ℕ) : Matrix (Fin n) (Fin d) k → ℂ := Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[k]} 1

def diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : GL (Fin n) k := SplitFlip.diagGL fun i => if i = i0 then x else 1

def cosetRep {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T : Fin d → SplitFlip.Res k 1) : Matrix (Fin n) (Fin d) k :=
  Matrix.of fun i j => if i = i0 then -((ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k)) else 0

/- English proof (translation)
Take `⟨_, _⟩` from `SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Establish `hc : IsCompact {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}` using `SplitFlip.isCompact_intMatrix`. Establish `ho : IsOpen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}` using `SplitFlip.isOpen_intMatrix`. Establish `hW : IsClopen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}` using `⟨hc.isClosed, ho⟩`. Use `⟨?_, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations.

Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}`. Use `filter_upwards [hW.isOpen.mem_nhds hx] with y hy`. Simplify using `only [Set.mem_setOf_eq] at hx`.

Simplify using `[intInd, Set.indicator_apply, hy, hx]`. Use `filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy`. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx hy`. Simplify using `[intInd, Set.indicator_apply, hy, hx]`.
-/
theorem intInd_mem_SB (n d : ℕ) : intInd k n d ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isCompact_intMatrix
  have ho : IsOpen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isOpen_intMatrix
  have hW : IsClopen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := ⟨hc.isClosed, ho⟩
  refine ⟨?_, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp only [Set.mem_setOf_eq] at hx
    simp [intInd, Set.indicator_apply, hy, hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx hy
    simp [intInd, Set.indicator_apply, hy, hx]

/- English proof (translation)
The claim follows from `Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) k) ∈ {Y | ∀ i j, Y i j ∈ 𝒪[k]} from fun _ _ => zero_mem _) _`.
-/
theorem intInd_zero (n d : ℕ) : intInd k n d 0 = 1 :=
  Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) k) ∈ {Y | ∀ i j, Y i j ∈ 𝒪[k]} from
    fun _ _ => zero_mem _) _

/- English proof (translation)
Rewrite using `[diagAt, SplitFlip.det_diagGL, Fintype.prod_eq_single i0 (fun i hi => if_neg hi), if_pos rfl]`.
-/
theorem det_diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : Matrix.GeneralLinearGroup.det (diagAt x i0) = x := by
  rw [diagAt, SplitFlip.det_diagGL, Fintype.prod_eq_single i0 (fun i hi => if_neg hi), if_pos rfl]

/- English proof (translation)
Rewrite using `[diagAt, SplitFlip.diagGL_val]`. Apply the tactic sequence `congr 1; funext i; split_ifs <;> simp`.
-/
theorem diagAt_val {n : ℕ} (x : kˣ) (i0 : Fin n) :
    (diagAt x i0).val = Matrix.diagonal fun i => if i = i0 then (x : k) else 1 := by
  rw [diagAt, SplitFlip.diagGL_val]
  congr 1; funext i; split_ifs <;> simp

end GlobalTheory.HeisUnit
