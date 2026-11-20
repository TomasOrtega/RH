import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerTer
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LineDegMono

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.LocalUnitApproximation.main`. Consider the case `exact _root_.GlobalTheory.LocalUnitApproximation.main`. Consider the case `(apply _root_.GlobalTheory.LocalUnitApproximation.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.LocalUnitApproximation.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.LocalUnitApproximation.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.LocalUnitApproximation.main ..)`.
-/
theorem exists_smul_mem (M : Submodule (𝓞 K) (Fin n → K)) {y : Fin n → K}
    (hy : y ∈ Submodule.span K (M : Set (Fin n → K))) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • y ∈ M := by
  first
  | exact @_root_.GlobalTheory.LocalUnitApproximation.main
  | exact _root_.GlobalTheory.LocalUnitApproximation.main
  | (apply _root_.GlobalTheory.LocalUnitApproximation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalUnitApproximation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalUnitApproximation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalUnitApproximation.main ..)

/- English proof (translation)
Unfold `latRank`. Establish `hle : Submodule.span K (lineLat L x : Set (Fin n → K)) ≤ Submodule.span K {x}`. Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Conclude with `(Submodule.mem_inf.mp hy).2`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem latRank_lineLat_le (L : Submodule (𝓞 K) (Fin n → K)) {x : Fin n → K} (hx : x ≠ 0) :
    latRank K (lineLat L x) ≤ 1 := by
  unfold latRank
  have hle : Submodule.span K (lineLat L x : Set (Fin n → K)) ≤ Submodule.span K {x} := by
    rw [Submodule.span_le]
    intro y hy
    exact (Submodule.mem_inf.mp hy).2
  calc Module.finrank K (Submodule.span K (lineLat L x : Set (Fin n → K)))
      ≤ Module.finrank K (Submodule.span K {x}) := Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hx

/- English proof (translation)
Unfold `latRank`. Establish `hle : Submodule.span K {y} ≤ Submodule.span K (E : Set (Fin n → K))` using `Submodule.span_mono (Set.singleton_subset_iff.mpr hy)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_latRank_of_mem {E : Submodule (𝓞 K) (Fin n → K)} {y : Fin n → K} (hy : y ∈ E) (hy0 : y ≠ 0) :
    1 ≤ latRank K E := by
  unfold latRank
  have hle : Submodule.span K {y} ≤ Submodule.span K (E : Set (Fin n → K)) :=
    Submodule.span_mono (Set.singleton_subset_iff.mpr hy)
  calc 1 = Module.finrank K (Submodule.span K {y}) := (finrank_span_singleton hy0).symm
    _ ≤ _ := Submodule.finrank_mono hle

/- English proof (translation)
Establish `hx : x ∈ Submodule.span K (M : Set (Fin n → K))` using `by rw [hM.2]; trivial`. Take `⟨d, hd, hdx⟩` from `exists_smul_mem M hx`. Use `⟨d, hd, Submodule.mem_inf.mpr ⟨hdx, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, ← algebraMap_smul K d x]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)`.
-/
theorem exists_smul_mem_lineLat {M : Submodule (𝓞 K) (Fin n → K)} (hM : Full M) (x : Fin n → K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ lineLat M x := by
  have hx : x ∈ Submodule.span K (M : Set (Fin n → K)) := by rw [hM.2]; trivial
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem M hx
  refine ⟨d, hd, Submodule.mem_inf.mpr ⟨hdx, ?_⟩⟩
  rw [Submodule.restrictScalars_mem, ← algebraMap_smul K d x]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

end GlobalTheory.LineDegMono

open GlobalTheory.LineDegMono in

/- English proof (translation)
Introduce `K' _ _ n m hW' h' β M' M x hβ hiso hM' hM hβM hx`. Establish `hβx : β x ≠ 0` using `fun h0 => hx (hβ (by rw [h0, map_zero]))`. Establish `hE'fg : (lineLat M' x).FG` using `Submodule.FG.of_le hM'.1 inf_le_left`. Establish `hEfg : (lineLat M (β x)).FG` using `Submodule.FG.of_le hM.1 inf_le_left`. Establish `hmap : ∀ y ∈ lineLat M' x, β y ∈ lineLat M (β x)`.

Introduce `y hy`. Take `⟨hy1, hy2⟩` from `Submodule.mem_inf.mp hy`. Rewrite `hy2` using `[Submodule.restrictScalars_mem, Submodule.mem_span_singleton]`. Take `⟨c, rfl⟩` from `hy2`. Use `Submodule.mem_inf.mpr ⟨hβM _ hy1, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.restrictScalars_mem, map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`. Take `⟨d, hd, hdx⟩` from `exists_smul_mem_lineLat hM' x`. Establish `hdK : algebraMap (𝓞 K') K' d ≠ 0` using `by simpa using hd`. Establish `hdx0 : d • x ≠ 0` using `by rw [← algebraMap_smul K' d x]; exact smul_ne_zero hdK hx`.

Establish `hβdx0 : β (d • x) ≠ 0` using `fun h0 => hdx0 (hβ (by rw [h0, map_zero]))`. Establish `hr' : latRank K' (lineLat M' x) = 1` using `le_antisymm (latRank_lineLat_le M' hx) (one_le_latRank_of_mem hdx hdx0)`. Establish `hr : latRank K' (lineLat M (β x)) = 1` using `le_antisymm (latRank_lineLat_le M hβx) (one_le_latRank_of_mem (hmap _ hdx) hβdx0)`. Take `⟨w, hw⟩` from `exists_isFrame (lineLat M (β x)) hEfg`. Establish `hnn : ∀ σ i, 0 ≤ h'.nrm σ (w i)` using `fun σ i => Real.sqrt_nonneg _`.

Establish `key` using `deg_le_deg_add hW' h' (lineLat M' x) (lineLat M (β x)) hE'fg hEfg β hβ hmap (fun _ => 1) (fun σ => 1 + ∑ i, h'.nrm σ (w i)) (fun _ => one_pos) (fun σ => add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => hnn σ i)) (fun σ k v => by`. Establish `: h'.gram σ (fun i => β (v i)) = hW'.gram σ v`. Use extensionality with `i j`. Simplify using `only [HermFam.gram, Matrix.of_apply, hiso]`. Rewrite using `[this]`.

Simplify using `using Matrix.PosSemidef.zero)`. Use `w hw (fun σ i => by`. Use `Finset.single_le_sum (fun j _ => hnn σ j) (Finset.mem_univ i)` as an intermediate fact. Use the proof step `linarith)`. Establish `hml : meanLog K' (fun _ => (1 : ℝ)) = 0` using `by simp [meanLog]`.

Establish `hrr : ((latRank K' (lineLat M (β x)) : ℝ) - latRank K' (lineLat M' x)) = 0`. Rewrite using `[hr, hr']`. Simplify using the standard rewrite rules. Rewrite `key` using `[hml, hrr]`. Simplify using `using key`.
-/
theorem GlobalTheory.deg_lineLat_le_deg_lineLat_map : ∀ (K' : Type) [Field K'] [NumberField K'] (n m : ℕ)
    (hW' : HermFam K' (Fin n → K')) (h' : HermFam K' (Fin m → K')) (β : (Fin n → K') →ₗ[K'] (Fin m → K'))
    (M' : Submodule (𝓞 K') (Fin n → K')) (M : Submodule (𝓞 K') (Fin m → K')) (x : Fin n → K'),
    Function.Injective β → (∀ σ y z, h'.form σ (β y) (β z) = hW'.form σ y z) → Full M' → Full M →
    (∀ y ∈ M', β y ∈ M) → x ≠ 0 → deg hW' (lineLat M' x) ≤ deg h' (lineLat M (β x)) := by
  intro K' _ _ n m hW' h' β M' M x hβ hiso hM' hM hβM hx
  have hβx : β x ≠ 0 := fun h0 => hx (hβ (by rw [h0, map_zero]))
  have hE'fg : (lineLat M' x).FG := Submodule.FG.of_le hM'.1 inf_le_left
  have hEfg : (lineLat M (β x)).FG := Submodule.FG.of_le hM.1 inf_le_left
  have hmap : ∀ y ∈ lineLat M' x, β y ∈ lineLat M (β x) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
    rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hy2
    obtain ⟨c, rfl⟩ := hy2
    refine Submodule.mem_inf.mpr ⟨hβM _ hy1, ?_⟩
    rw [Submodule.restrictScalars_mem, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem_lineLat hM' x
  have hdK : algebraMap (𝓞 K') K' d ≠ 0 := by simpa using hd
  have hdx0 : d • x ≠ 0 := by rw [← algebraMap_smul K' d x]; exact smul_ne_zero hdK hx
  have hβdx0 : β (d • x) ≠ 0 := fun h0 => hdx0 (hβ (by rw [h0, map_zero]))
  have hr' : latRank K' (lineLat M' x) = 1 :=
    le_antisymm (latRank_lineLat_le M' hx) (one_le_latRank_of_mem hdx hdx0)
  have hr : latRank K' (lineLat M (β x)) = 1 :=
    le_antisymm (latRank_lineLat_le M hβx) (one_le_latRank_of_mem (hmap _ hdx) hβdx0)
  obtain ⟨w, hw⟩ := exists_isFrame (lineLat M (β x)) hEfg
  have hnn : ∀ σ i, 0 ≤ h'.nrm σ (w i) := fun σ i => Real.sqrt_nonneg _
  have key := deg_le_deg_add hW' h' (lineLat M' x) (lineLat M (β x)) hE'fg hEfg β hβ hmap
    (fun _ => 1) (fun σ => 1 + ∑ i, h'.nrm σ (w i)) (fun _ => one_pos)
    (fun σ => add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => hnn σ i))
    (fun σ k v => by
      have : h'.gram σ (fun i => β (v i)) = hW'.gram σ v := by
        ext i j; simp only [HermFam.gram, Matrix.of_apply, hiso]
      rw [this]; simpa using Matrix.PosSemidef.zero)
    w hw (fun σ i => by
      have := Finset.single_le_sum (fun j _ => hnn σ j) (Finset.mem_univ i)
      linarith)
  have hml : meanLog K' (fun _ => (1 : ℝ)) = 0 := by simp [meanLog]
  have hrr : ((latRank K' (lineLat M (β x)) : ℝ) - latRank K' (lineLat M' x)) = 0 := by
    rw [hr, hr']; simp
  rw [hml, hrr] at key
  simpa using key
