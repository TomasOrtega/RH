import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LamBound

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Unfold `Et.etaK eta`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_etaK (A : Et F E) (t : A.K) : ‖A.etaK t‖ = 1 := by
  unfold Et.etaK eta
  split_ifs <;> simp

/- English proof (translation)
Unfold `Et.absK`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK
  split_ifs <;> simp

/- English proof (translation)
Set `T : Set (Matrix (Fin 2) (Fin 2) K)` to `{M | ∀ i j, M i j ∈ O} ∩ {M | M.det = 1}`. Establish `hT : IsCompact T`. Establish `h1 : IsCompact {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O}`. Use `isCompact_univ_pi (fun _ : Fin 2 => isCompact_univ_pi (fun _ : Fin 2 => hO))` as an intermediate fact. Establish `he : {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} = Set.univ.pi (fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => O)`.

Use extensionality with `M`. Conclude with `⟨fun h => Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => h i j, fun h i j => Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h i) j⟩`. Rewrite using `[he]`. Conclude with `this`. Conclude with `h1.inter_right (isClosed_eq (continuous_id.matrix_det) continuous_const)`.

Set `N : Matrix (Fin 2) (Fin 2) K → Set (Matrix (Fin 2) (Fin 2) K)` to `fun M => {M' | ∀ i j, (M.adjugate * M' - 1) i j ∈ U}`. Establish `hN : ∀ M ∈ T, N M ∈ 𝓝 M`. Introduce `M hM`. Establish `hc : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => M.adjugate * M' - 1)` using `(continuous_const.matrix_mul continuous_id).sub continuous_const`. Establish `h0 : M.adjugate * M - 1 = 0`.

Rewrite using `[Matrix.adjugate_mul, hM.2]`. Simplify using the standard rewrite rules. Establish `hij : ∀ i j, ∀ᶠ M' in 𝓝 M, (M.adjugate * M' - 1) i j ∈ U`. Introduce `i j`. Establish `hcij : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => (M.adjugate * M' - 1) i j)` using `hc.matrix_elem i j`.

Use `hcij.tendsto M` as an intermediate fact. Simplify using `only [h0, Matrix.zero_apply] at this`. Conclude with `this hU`. Conclude with `Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j`. Take `⟨t, htT, hcov⟩` from `hT.elim_nhds_subcover N hN`.

Set `g : Matrix (Fin 2) (Fin 2) K → ℝ` to `fun M => if h : M.det = 1 then ‖Ψ ⟨M, h⟩‖ else 0`. Use `⟨∑ M ∈ t, g M, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hkT : (k : Matrix (Fin 2) (Fin 2) K) ∈ T` using `⟨hk, k.2⟩`. Take `⟨M, hMt, hkM⟩` from `Set.mem_iUnion₂.1 (hcov hkT)`. Establish `hdet : M.det = 1` using `(htT M hMt).2`.

Set `k₀ : SpecialLinearGroup (Fin 2) K` to `⟨M, hdet⟩`. Establish `he : Ψ k = Ψ k₀`. Use `hΨ k₀ (k₀⁻¹ * k) (by` as an intermediate fact. Introduce `i j`. Use `hkM i j` as an intermediate fact.

Conclude with `this)`. Simplify using `using this`. Establish `hg : g M = ‖Ψ k₀‖` using `by simp only [g, dif_pos hdet]; rfl`. Rewrite using `[he, ← hg]`. Apply the tactic sequence `exact Finset.single_le_sum (f := g) (fun M _ => by simp only [g]; split_ifs <;> positivity) hMt`.
-/
theorem bdd_of_loc_const (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (O : Set K) (hO : IsCompact O) (Ψ : SpecialLinearGroup (Fin 2) K → ℂ) (U : Set K) (hU : U ∈ 𝓝 (0 : K))
    (hΨ : ∀ g k : SpecialLinearGroup (Fin 2) K, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) K) - 1) i j ∈ U) →
      Ψ (g * k) = Ψ g) :
    ∃ C : ℝ, ∀ k : SpecialLinearGroup (Fin 2) K, (∀ i j, (k : Matrix (Fin 2) (Fin 2) K) i j ∈ O) → ‖Ψ k‖ ≤ C := by
  classical
  let T : Set (Matrix (Fin 2) (Fin 2) K) := {M | ∀ i j, M i j ∈ O} ∩ {M | M.det = 1}
  have hT : IsCompact T := by
    have h1 : IsCompact {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} := by
      have := isCompact_univ_pi (fun _ : Fin 2 => isCompact_univ_pi (fun _ : Fin 2 => hO))
      have he : {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} =
          Set.univ.pi (fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => O) := by
        ext M
        exact ⟨fun h => Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => h i j,
          fun h i j => Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h i) j⟩
      rw [he]; exact this
    exact h1.inter_right (isClosed_eq (continuous_id.matrix_det) continuous_const)
  let N : Matrix (Fin 2) (Fin 2) K → Set (Matrix (Fin 2) (Fin 2) K) := fun M =>
    {M' | ∀ i j, (M.adjugate * M' - 1) i j ∈ U}
  have hN : ∀ M ∈ T, N M ∈ 𝓝 M := by
    intro M hM
    have hc : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => M.adjugate * M' - 1) :=
      (continuous_const.matrix_mul continuous_id).sub continuous_const
    have h0 : M.adjugate * M - 1 = 0 := by
      rw [Matrix.adjugate_mul, hM.2]; simp
    have hij : ∀ i j, ∀ᶠ M' in 𝓝 M, (M.adjugate * M' - 1) i j ∈ U := by
      intro i j
      have hcij : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => (M.adjugate * M' - 1) i j) :=
        hc.matrix_elem i j
      have := hcij.tendsto M
      simp only [h0, Matrix.zero_apply] at this
      exact this hU
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  obtain ⟨t, htT, hcov⟩ := hT.elim_nhds_subcover N hN
  let g : Matrix (Fin 2) (Fin 2) K → ℝ := fun M => if h : M.det = 1 then ‖Ψ ⟨M, h⟩‖ else 0
  refine ⟨∑ M ∈ t, g M, fun k hk => ?_⟩
  have hkT : (k : Matrix (Fin 2) (Fin 2) K) ∈ T := ⟨hk, k.2⟩
  obtain ⟨M, hMt, hkM⟩ := Set.mem_iUnion₂.1 (hcov hkT)
  have hdet : M.det = 1 := (htT M hMt).2
  let k₀ : SpecialLinearGroup (Fin 2) K := ⟨M, hdet⟩
  have he : Ψ k = Ψ k₀ := by
    have := hΨ k₀ (k₀⁻¹ * k) (by
      intro i j
      have := hkM i j
      exact this)
    simpa using this
  have hg : g M = ‖Ψ k₀‖ := by simp only [g, dif_pos hdet]; rfl
  rw [he, ← hg]
  exact Finset.single_le_sum (f := g) (fun M _ => by simp only [g]; split_ifs <;> positivity) hMt

/- English proof (translation)
Introduce `F E _ _ _ _ U A Ψ hΨ`. Use `U.ultraF` as an intermediate fact. Use `U.lcF` as an intermediate fact. Establish `: ProperSpace F` using `.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F`. Set `b` to `Module.finBasis F A.K`.

Establish `: T2Space A.K` using `.of_injective_continuous b.equivFun.injective (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)`. Take `⟨-, -, -, -, -, -, -, -, -, -, hcpt, R, hR⟩` from `GlobalTheory.T.etaleHermitianPair_structure_facts F E A`. Take `⟨V, hV, hloc⟩` from `hΨ.1`. Take `⟨C, hC⟩` from `bdd_of_loc_const A.K A.OK hcpt Ψ V hV hloc`. Use `⟨C, fun z s α β hα hβ hs hsz h => ?_⟩` and prove the remaining obligations.

Establish `hu : (s : A.K) * ((s⁻¹ : A.Kˣ) : A.K) = 1` using `Units.mul_inv s`. Set `k : SpecialLinearGroup (Fin 2) A.K` to `⟨!![-β, α; -(s : A.K), -((s : A.K) * z)], by`. Simplify using `[Matrix.det_fin_two]`. Take the linear combination `h⟩`. Establish `hk : wS A.K * nS z = nS (-((s : A.K) * β)) * mS s * k`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show !![(0 : A.K), 1; -1, 0] * !![1, z; 0, 1] = !![1, -((s : A.K) * β); 0, 1] * !![(s : A.K), 0; 0, ((s⁻¹ : A.Kˣ) : A.K)] * !![-β, α; -(s : A.K), -((s : A.K) * z)]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>`. Take the linear combination `(-1 : A.K) * h - (β * (s : A.K) * z) * hu`. Establish `hkO : ∀ i j, (k : Matrix (Fin 2) (Fin 2) A.K) i j ∈ A.OK`.

Rewrite using `[← hR]`. Establish `hα' : α ∈ R` using `by rw [← SetLike.mem_coe, hR]; exact hα`. Establish `hβ' : β ∈ R` using `by rw [← SetLike.mem_coe, hR]; exact hβ`. Establish `hs' : (s : A.K) ∈ R` using `by rw [← SetLike.mem_coe, hR]; exact hs`. Establish `hsz' : (s : A.K) * z ∈ R` using `by rw [← SetLike.mem_coe, hR]; exact hsz`.

Apply the tactic sequence `intro i j; fin_cases i <;> fin_cases j <;> simp [k, R.neg_mem, hα', hβ', hs', hsz']`. Rewrite using `[hk, hΨ.2, norm_mul, norm_mul, norm_etaK, Complex.norm_real, Real.norm_of_nonneg (absK_nonneg A _), one_mul, mul_comm C]`. Conclude with `mul_le_mul_of_nonneg_left (hC k hkO) (absK_nonneg A _)`.
-/
theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ), A.InI Ψ → ∃ C : ℝ, ∀ (z : A.K) (s : A.Kˣ) (α β : A.K), α ∈ A.OK → β ∈ A.OK → (s : A.K) ∈ A.OK → (s : A.K) * z ∈ A.OK → α * s + β * (s * z) = 1 → ‖Ψ (wS A.K * nS z)‖ ≤ C * A.absK s := by
  intro F E _ _ _ _ U A Ψ hΨ
  have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let b := Module.finBasis F A.K
  have : T2Space A.K := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨V, hV, hloc⟩ := hΨ.1
  obtain ⟨C, hC⟩ := bdd_of_loc_const A.K A.OK hcpt Ψ V hV hloc
  refine ⟨C, fun z s α β hα hβ hs hsz h => ?_⟩
  have hu : (s : A.K) * ((s⁻¹ : A.Kˣ) : A.K) = 1 := Units.mul_inv s
  let k : SpecialLinearGroup (Fin 2) A.K := ⟨!![-β, α; -(s : A.K), -((s : A.K) * z)], by
    simp [Matrix.det_fin_two]; linear_combination h⟩
  have hk : wS A.K * nS z = nS (-((s : A.K) * β)) * mS s * k := by
    apply Subtype.ext
    show !![(0 : A.K), 1; -1, 0] * !![1, z; 0, 1] =
      !![1, -((s : A.K) * β); 0, 1] * !![(s : A.K), 0; 0, ((s⁻¹ : A.Kˣ) : A.K)] * !![-β, α; -(s : A.K), -((s : A.K) * z)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination (-1 : A.K) * h - (β * (s : A.K) * z) * hu
  have hkO : ∀ i j, (k : Matrix (Fin 2) (Fin 2) A.K) i j ∈ A.OK := by
    rw [← hR]
    have hα' : α ∈ R := by rw [← SetLike.mem_coe, hR]; exact hα
    have hβ' : β ∈ R := by rw [← SetLike.mem_coe, hR]; exact hβ
    have hs' : (s : A.K) ∈ R := by rw [← SetLike.mem_coe, hR]; exact hs
    have hsz' : (s : A.K) * z ∈ R := by rw [← SetLike.mem_coe, hR]; exact hsz
    intro i j; fin_cases i <;> fin_cases j <;> simp [k, R.neg_mem, hα', hβ', hs', hsz']
  rw [hk, hΨ.2, norm_mul, norm_mul, norm_etaK, Complex.norm_real, Real.norm_of_nonneg (absK_nonneg A _), one_mul,
    mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC k hkO) (absK_nonneg A _)

end GlobalTheory.JR.LamBound
