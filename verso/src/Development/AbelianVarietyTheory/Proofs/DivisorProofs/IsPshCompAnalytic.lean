import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshLimitIsPshStatement

namespace GlobalTheory.PshPullback

open Metric Filter Topology ReciprocityTheory.AnForm.A
open scoped ContDiff

/- English proof (translation)
Introduce `D D' U V φ h hU hV hφ hh hmaps`. Take `⟨ρ⟩` from `mollifierInhabit_thm D`. Establish `hM` using `mollify_thm D ρ U φ hU hφ`. Use `set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε`. Establish `hεpos : ∀ n, 0 < ε n` using `fun n => by positivity`.

Establish `hcont : ContinuousOn h V` using `fun x hx => (hh x hx).continuousAt.continuousWithinAt`. Use `GlobalTheory.T.psh_limit_is_psh D' V (φ ∘ h) (fun n => molli ρ (ε n) φ ∘ h) (fun n => V ∩ h ⁻¹' shrink U (ε n)) hV (hφ.1.comp hcont hmaps) ?_ ?_ ?_` and prove the remaining obligations. Introduce `n`. Take `⟨hSo, hSc, hSp, -⟩` from `hM.1 (ε n) (hεpos n)`. Establish `hVo : IsOpen (V ∩ h ⁻¹' shrink U (ε n))` using `hcont.isOpen_inter_preimage hV hSo`.

Establish `hC2S : ContDiffOn ℝ 2 (molli ρ (ε n) φ) (shrink U (ε n))` using `hSc.of_le (WithTop.coe_le_coe.2 le_top)`. Establish `hLevi` using `(isPsh_iff_isLeviPsh_thm D _ _ hSo hC2S).1 hSp`. Establish `hat : ∀ x ∈ V ∩ h ⁻¹' shrink U (ε n), ContDiffAt ℝ 2 (molli ρ (ε n) φ) (h x)` using `fun x hx => hC2S.contDiffAt (hSo.mem_nhds hx.2)`. Establish `hC2 : ContDiffOn ℝ 2 (molli ρ (ε n) φ ∘ h) (V ∩ h ⁻¹' shrink U (ε n))`. Introduce `x hx`.

Conclude with `((hat x hx).comp x ((hh x hx.1).restrictScalars.contDiffAt)).contDiffWithinAt`. Use `(isPsh_iff_isLeviPsh_thm D' _ _ hVo hC2).2 ⟨hC2, fun x hx w => ?_⟩` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.AnForm.levi_comp w (hh x hx.1) (hat x hx)]`. Conclude with `hLevi.2 (h x) hx.2 _`. Introduce `K hK hKV`.

Establish `hhK : IsCompact (h '' K)` using `hK.image_of_continuousOn (hcont.mono hKV)`. Take `⟨δ, hδ, hδU⟩` from `hhK.exists_cthickening_subset_open hU (Set.image_subset_iff.2 fun x hx => hmaps (hKV hx))`. Establish `hCc : IsCompact (cthickening δ (h '' K))` using `hhK.cthickening`. Take `⟨M, hMb⟩` from `(hφ.1.mono hδU).bddAbove_of_isCompact hCc`. Take `⟨N, hN⟩` from `exists_nat_gt (1 / δ)`.

Use `⟨N, M, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hεδ : ε n ≤ δ`. Establish `hn' : (1 / δ : ℝ) < (n : ℝ) + 1`. Establish `: (N : ℝ) ≤ n` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [hε]`. Rewrite using `[div_le_iff₀ (by positivity)]`. Rewrite `hn'` using `[div_lt_iff₀ hδ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hball : ∀ z ∈ K, closedBall (h z) (ε n) ⊆ cthickening δ (h '' K)` using `fun z hz => (closedBall_subset_closedBall hεδ).trans (closedBall_subset_cthickening (Set.mem_image_of_mem h hz) δ)`.

Establish `hsh : ∀ z ∈ K, h z ∈ shrink U (ε n)` using `fun z hz => (hball z hz).trans hδU`. Use `⟨fun z hz => ⟨hKV hz, hsh z hz⟩, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨-, -, -, hb⟩` from `hM.1 (ε n) (hεpos n)`. Use `(hb (h z) (hsh z hz)).2.trans ?_` and prove the remaining obligations. Use `csSup_le ((nonempty_closedBall.2 (hεpos n).le).image φ) ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hMb ⟨y, hball z hz hy, rfl⟩`. Introduce `z hz`. Establish `h0 : Tendsto ε atTop (𝓝[>] 0)` using `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_one_div_add_atTop_nhds_zero_nat) (Eventually.of_forall hεpos)`. Conclude with `(hM.2 (h z) (hmaps hz)).comp h0`.
-/
theorem isPsh_comp : ∀ (D D' : ℕ) (U : Set (Fin D → ℂ)) (V : Set (Fin D' → ℂ))
    (φ : (Fin D → ℂ) → ℝ) (h : (Fin D' → ℂ) → (Fin D → ℂ)), IsOpen U → IsOpen V →
    ReciprocityTheory.AnForm.A.IsPsh U φ → AnalyticOnNhd ℂ h V → Set.MapsTo h V U →
    ReciprocityTheory.AnForm.A.IsPsh V (φ ∘ h) := by
  intro D D' U V φ h hU hV hφ hh hmaps
  obtain ⟨ρ⟩ := mollifierInhabit_thm D
  have hM := mollify_thm D ρ U φ hU hφ
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hcont : ContinuousOn h V := fun x hx => (hh x hx).continuousAt.continuousWithinAt
  refine GlobalTheory.T.psh_limit_is_psh D' V (φ ∘ h) (fun n => molli ρ (ε n) φ ∘ h)
    (fun n => V ∩ h ⁻¹' shrink U (ε n)) hV (hφ.1.comp hcont hmaps) ?_ ?_ ?_
  · intro n
    obtain ⟨hSo, hSc, hSp, -⟩ := hM.1 (ε n) (hεpos n)
    have hVo : IsOpen (V ∩ h ⁻¹' shrink U (ε n)) := hcont.isOpen_inter_preimage hV hSo
    have hC2S : ContDiffOn ℝ 2 (molli ρ (ε n) φ) (shrink U (ε n)) :=
      hSc.of_le (WithTop.coe_le_coe.2 le_top)
    have hLevi := (isPsh_iff_isLeviPsh_thm D _ _ hSo hC2S).1 hSp
    have hat : ∀ x ∈ V ∩ h ⁻¹' shrink U (ε n), ContDiffAt ℝ 2 (molli ρ (ε n) φ) (h x) :=
      fun x hx => hC2S.contDiffAt (hSo.mem_nhds hx.2)
    have hC2 : ContDiffOn ℝ 2 (molli ρ (ε n) φ ∘ h) (V ∩ h ⁻¹' shrink U (ε n)) := by
      intro x hx
      exact ((hat x hx).comp x ((hh x hx.1).restrictScalars.contDiffAt)).contDiffWithinAt
    refine (isPsh_iff_isLeviPsh_thm D' _ _ hVo hC2).2 ⟨hC2, fun x hx w => ?_⟩
    rw [ReciprocityTheory.AnForm.levi_comp w (hh x hx.1) (hat x hx)]
    exact hLevi.2 (h x) hx.2 _
  · intro K hK hKV
    have hhK : IsCompact (h '' K) := hK.image_of_continuousOn (hcont.mono hKV)
    obtain ⟨δ, hδ, hδU⟩ := hhK.exists_cthickening_subset_open hU
      (Set.image_subset_iff.2 fun x hx => hmaps (hKV hx))
    have hCc : IsCompact (cthickening δ (h '' K)) := hhK.cthickening
    obtain ⟨M, hMb⟩ := (hφ.1.mono hδU).bddAbove_of_isCompact hCc
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N, M, fun n hn => ?_⟩
    have hεδ : ε n ≤ δ := by
      have hn' : (1 / δ : ℝ) < (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp only [hε]
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at hn'
      linarith
    have hball : ∀ z ∈ K, closedBall (h z) (ε n) ⊆ cthickening δ (h '' K) := fun z hz =>
      (closedBall_subset_closedBall hεδ).trans
        (closedBall_subset_cthickening (Set.mem_image_of_mem h hz) δ)
    have hsh : ∀ z ∈ K, h z ∈ shrink U (ε n) := fun z hz => (hball z hz).trans hδU
    refine ⟨fun z hz => ⟨hKV hz, hsh z hz⟩, fun z hz => ?_⟩
    obtain ⟨-, -, -, hb⟩ := hM.1 (ε n) (hεpos n)
    refine (hb (h z) (hsh z hz)).2.trans ?_
    refine csSup_le ((nonempty_closedBall.2 (hεpos n).le).image φ) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hMb ⟨y, hball z hz hy, rfl⟩
  · intro z hz
    have h0 : Tendsto ε atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (tendsto_one_div_add_atTop_nhds_zero_nat) (Eventually.of_forall hεpos)
    exact (hM.2 (h z) (hmaps hz)).comp h0

end GlobalTheory.PshPullback
