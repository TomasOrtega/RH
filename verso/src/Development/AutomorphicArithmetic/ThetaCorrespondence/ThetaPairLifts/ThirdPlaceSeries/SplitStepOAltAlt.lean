import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.PartNormO
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.MuBlockLoc
/- English proof (translation)
Introduce `α hα`. Establish `hAut` using `ht.2.1`. Take `⟨ha1, hd1, hcsd⟩` from `hB.1 p hp`. Establish `hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (0 : ℂ))) ≤ D.nbc.infW j (D.nbc.wtAU j π) τ` using `fun τ => by`. Rewrite using `[← hB.2.2.2.2.2 τ]`.

Conclude with `mem_isoInf D Pa p hp hd1 τ`. Establish `hW` using `fun τ => D.nbc.infW_alg j (D.nbc.wtAU j π) τ`. Establish `hnd : ∀ τ, (D.naut.infG p.π τ).Nodup` using `fun τ => Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW τ).1)`. Establish `hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2`. Introduce `τ z hz`.

Take `⟨k, hk⟩` from `(hW τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))`. Conclude with `⟨k, by rw [← hk]; push_cast; ring⟩`. Break down `Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩` into its components or cases. Establish `hr : D.naut.ralg p.π` using `(D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by`. Take `⟨k, hk⟩` from `hint τ z hz`.

Use `⟨k + m, ?_⟩` and prove the remaining obligations. Establish `hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m`. Conclude with `hm` after adjusting the coercions. Move the coercions through the operations in `at hm' ⊢`. Take the linear combination `hk + (1 / 2 : ℂ) * hm'⟩`.

Conclude with `(_root_.UpperTheory.GalN.tempo' hT p.a p.π ha1 hcsd hr w).part hu α hα`. Establish `hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT)` using `(D.naut.ralg_def _).2 fun τ => by`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by`. Break down `(hAut.2.1 τ).1 with h | h` into its components or cases. Conclude with `⟨1 / 2, h, 0, by simp⟩`.

Conclude with `⟨-(1 / 2), h, -1, by push_cast; ring⟩`. Rewrite using `[D.naut.infG_tw _ _ τ s hs]`. Use `⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.mp hz`. Take `⟨k, hk⟩` from `hint τ y hy`.

Use `⟨k + k0 + m + 1, ?_⟩` and prove the remaining obligations. Establish `hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1`. Conclude with `hm` after adjusting the coercions. Move the coercions through the operations in `at hm' ⊢`. Rewrite using `[hk0]`.

Take the linear combination `hk + (1 / 2 : ℂ) * hm'`. Conclude with `(_root_.UpperTheory.GalN.tempo' hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w).part_tw hAut hu α hα`.
-/
theorem part_norm_o_alt (D : D7) (ht : SumRepresentations.tie0 D) (hT : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D) {j : ℕ} {π : D.nbc.AU j}
    {Pa : List (Part D.naut.CG)} (hB : SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa) (p : Part D.naut.CG) (hp : p ∈ Pa)
    (w : PlE D.host) (hu : D.naut.unr (D.naut.locG p.π w)) :
    ∀ α ∈ D.naut.frobEig (D.naut.locG p.π w), UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) α ∧ (p.a = 1 → ‖α‖ = 1) := by
  intro α hα
  have hAut := ht.2.1
  obtain ⟨ha1, hd1, hcsd⟩ := hB.1 p hp
  have hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (0 : ℂ))) ≤
      D.nbc.infW j (D.nbc.wtAU j π) τ := fun τ => by
    rw [← hB.2.2.2.2.2 τ]; exact mem_isoInf D Pa p hp hd1 τ
  have hW := fun τ => D.nbc.infW_alg j (D.nbc.wtAU j π) τ
  have hnd : ∀ τ, (D.naut.infG p.π τ).Nodup := fun τ =>
    Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW τ).1)
  have hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ z hz
    obtain ⟨k, hk⟩ := (hW τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; push_cast; ring⟩
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hr : D.naut.ralg p.π := (D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by
      obtain ⟨k, hk⟩ := hint τ z hz
      refine ⟨k + m, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      linear_combination hk + (1 / 2 : ℂ) * hm'⟩
    exact (_root_.UpperTheory.GalN.tempo' hT p.a p.π ha1 hcsd hr w).part hu α hα
  · have hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT) := (D.naut.ralg_def _).2 fun τ => by
      obtain ⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by
        rcases (hAut.2.1 τ).1 with h | h
        · exact ⟨1 / 2, h, 0, by simp⟩
        · exact ⟨-(1 / 2), h, -1, by push_cast; ring⟩
      rw [D.naut.infG_tw _ _ τ s hs]
      refine ⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨k, hk⟩ := hint τ y hy
      refine ⟨k + k0 + m + 1, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1 := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      rw [hk0]
      linear_combination hk + (1 / 2 : ℂ) * hm'
    exact (_root_.UpperTheory.GalN.tempo' hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w).part_tw hAut hu α hα
end GlobalTheory.MuBlockLoc
namespace GlobalTheory.MuBlockLoc
/- English proof (translation)
Establish `hT` using `hL.tie0`. Establish `hLP` using `hT.1`. Establish `hAut` using `hT.2.1`. Establish `heu` using `D.naut.etaT_unr w`. Establish `hed : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1` using `D.naut.locG_dim _ _`.

Take `⟨e, he⟩` from `GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ heu hed`. Establish `hen : ‖e‖ = 1` using `(D.naut.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; exact Multiset.mem_singleton_self e)`. Establish `he0 : e ≠ 0` using `by intro h; rw [h] at hen; simp at hen`. Take `⟨hbu, hbe⟩` from `D.naut.etaTinv_def w`. Establish `hbd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1` using `D.naut.locG_dim _ _`.

Establish `hb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {e⁻¹}` using `by rw [hbe, he]; simp`. Establish `hbn : ‖e⁻¹‖ = 1` using `by rw [norm_inv, hen, inv_one]`. Take `⟨m, hm⟩` from `GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ hμ (D.naut.locG_dim _ _)`. Establish `hmt` using `(_root_.UpperTheory.GalN.tempo' hL.temp 1 μ le_rfl hA.csd (mu_ralg D Rw j σ π μ hA) w).1 rfl`. Establish `hmn : ‖m‖ = 1` using `(D.naut.tempered_unr _ hμ).1 hmt m (by rw [hm]; exact Multiset.mem_singleton_self m)`.

Establish `htw : D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) = {m * e⁻¹}`. Rewrite using `[D.naut.locG_tw, D.naut.frobEig_char _ _ (e⁻¹) hμ hbu hbd hb, hm]`. Simplify using the standard rewrite rules. Establish `hV` using `hA.loc w hs`. Establish `hiso` using `GlobalTheory.MuBlock.frobEig_isoLoc D.nd D.naut Pa w hPa`.

Establish `hVu : D.naut.unr (D.nbc.locAU j π w)` using `by rw [← hB.2.2.2.1 w hs]; exact hiso.1`. Establish `hinv : D.naut.lpChar (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) = D.naut.lpUnr w {1}`. Establish `hu` using `D.naut.unr_char _ _ hed hbu heu`. Rewrite using `[D.naut.unr_eq_lpUnr _ hu, D.naut.frobEig_char _ _ e hbu heu hed he, hb]`. Simplify using `[he0]`.

Establish `hX : D.naut.lpChar (D.nbc.locAU j π w) (D.naut.locG D.naut.etaT w) = D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)`. Rewrite using `[hV, (hLP w (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (Rw.locR σ w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0 hbd hed).2.2.2.1, hinv]`. Conclude with `(hLP w _ (Rw.locR σ w) (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaT w) 0 hed hed).2.2.2.2.1`. Establish `hXu : D.naut.unr (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w))`. Rewrite using `[← hX]`.

Conclude with `D.naut.unr_char _ _ hed hVu heu`. Take `⟨hWu, hSu⟩` from `(D.naut.unr_sum _ _).1 hXu`. Establish `hmu` using `GlobalTheory.MuBlock.frobEig_spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w hμ`. Simplify using `only at hmu`. Establish `hVe : D.naut.frobEig (D.nbc.locAU j π w) = (D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹) + ((List.range D.R.t).map fun k => ({(m * e⁻¹) * ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum`.

Rewrite using `[hV, D.naut.frobEig_char _ _ _ hXu hbu hbd hb, D.naut.frobEig_sum _ _ hWu hSu, Multiset.map_add]`. Rewrite using `[hmu.2, hm]`. Use `congr 1`. Rewrite using `[← Multiset.coe_mapAddMonoidHom, map_list_sum, List.map_map]`. Use `congr 1`.

Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `k _`. Simplify using `only [Function.comp_apply, Multiset.coe_mapAddMonoidHom, Multiset.map_singleton]`. Put the polynomial expressions in normal form. Establish `key` using `UpperTheory.GalN.string_count (Formalism.ConjugateSelfDual.normV w) D.R.t (Pa.map fun p => (p.d, D.naut.frobEig (D.naut.locG p.π w))) ((D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹)) (m * e⁻¹) (by exact_mod_cast GlobalTheory.LocalInv.one_lt_normV w) D.R.t_odd.pos (by rw [norm_mul, …`.

Introduce `x hx`. Take `⟨α, hα, rfl⟩` from `Multiset.mem_map.1 hx`. Rewrite using `[norm_mul, hbn, mul_one]`. Use `(hR w hs hg).2 α hα` as an intermediate fact. Rewrite using `[GlobalTheory.MuBlock.absNorm_eq_normV] at this)` and apply the resulting hypothesis.

Use the proof step `(by`. Introduce `x hx`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 hx`. Establish `k` using `_root_.GlobalTheory.MuBlockLoc.part_norm_o_alt D hT hL.temp hB p hp w (hPa p hp)`. Use `⟨(hB.1 p hp).2.1, ?_, fun α hα => (k α hα).1, fun ht α hα => (k α hα).2 (UpperTheory.GalN.rank_one_of_long hB.2.2.1 hp (hB.1 p hp).1 ht)⟩` and prove the remaining obligations.

Introduce `h0`. Express the relevant statement in the definitionally equal form `D.naut.frobEig (D.naut.locG p.π w) = 0 at h0`. Establish `h1` using `D.naut.frobEig_card _ (hPa p hp)`. Rewrite `h1` using `[h0, D.naut.locG_dim]`. Use `(hB.1 p hp).1` as an intermediate fact.

Simplify using `at h1`. Use the proof step `omega)`. Use the proof step `(by`. Establish `hiso2` using `hiso.2`. Simplify using `only [GlobalTheory.LocalInv.list_coe, List.map_map] at hiso2`.

Rewrite using `[List.map_map]`. Conclude with `hiso2.symm.trans ((congrArg D.naut.frobEig (hB.2.2.2.1 w hs)).trans hVe))`. Use `⟨?_, fun p hp hpt => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hxt⟩` from `key.1`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `⟨p, hp, hxt⟩`. Take `⟨h1, h2⟩` from `key.2 _ (List.mem_map_of_mem (f := fun p : Part D.naut.CG => (p.d, D.naut.frobEig (D.naut.locG p.π w))) hp) hpt`. Conclude with `⟨h1, h2.trans htw.symm⟩`.
-/
theorem split_step_o_alt (D : D7) (Rw : RowSide D) (hL : _root_.GlobalTheory.HeightCounting.Up.ParityLaws D) (j : ℕ) (σ : D.what₂.FT) (π : D.nbc.AU j)
    (μ : D.naut.CG 1) (Pa : List (Part D.naut.CG)) (hA : LiftAt D Rw j σ π μ) (hR : RowLoc D Rw σ)
    (hB : SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa) (w : PlE D.host) (hs : IsSplitPl D.host w)
    (hg : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k))
    (hPa : ∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) (hμ : D.naut.unr (D.naut.locG μ w)) :
    (∃ p ∈ Pa, D.R.t ≤ p.d) ∧ ∀ p ∈ Pa, D.R.t ≤ p.d → p.d = D.R.t ∧
      D.naut.frobEig (D.naut.locG p.π w) = D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := by
  have hT := hL.tie0
  have hLP := hT.1
  have hAut := hT.2.1
  have heu := D.naut.etaT_unr w
  have hed : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ _
  obtain ⟨e, he⟩ := GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ heu hed
  have hen : ‖e‖ = 1 := (D.naut.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; exact Multiset.mem_singleton_self e)
  have he0 : e ≠ 0 := by intro h; rw [h] at hen; simp at hen
  obtain ⟨hbu, hbe⟩ := D.naut.etaTinv_def w
  have hbd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {e⁻¹} := by rw [hbe, he]; simp
  have hbn : ‖e⁻¹‖ = 1 := by rw [norm_inv, hen, inv_one]
  obtain ⟨m, hm⟩ := GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ hμ (D.naut.locG_dim _ _)
  have hmt := (_root_.UpperTheory.GalN.tempo' hL.temp 1 μ le_rfl hA.csd (mu_ralg D Rw j σ π μ hA) w).1 rfl
  have hmn : ‖m‖ = 1 := (D.naut.tempered_unr _ hμ).1 hmt m (by rw [hm]; exact Multiset.mem_singleton_self m)
  have htw : D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) = {m * e⁻¹} := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ (e⁻¹) hμ hbu hbd hb, hm]; simp
  have hV := hA.loc w hs
  have hiso := GlobalTheory.MuBlock.frobEig_isoLoc D.nd D.naut Pa w hPa
  have hVu : D.naut.unr (D.nbc.locAU j π w) := by rw [← hB.2.2.2.1 w hs]; exact hiso.1
  have hinv : D.naut.lpChar (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) = D.naut.lpUnr w {1} := by
    have hu := D.naut.unr_char _ _ hed hbu heu
    rw [D.naut.unr_eq_lpUnr _ hu, D.naut.frobEig_char _ _ e hbu heu hed he, hb]; simp [he0]
  have hX : D.naut.lpChar (D.nbc.locAU j π w) (D.naut.locG D.naut.etaT w) =
      D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) := by
    rw [hV, (hLP w (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w))
      (Rw.locR σ w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0 hbd hed).2.2.2.1, hinv]
    exact (hLP w _ (Rw.locR σ w) (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaT w) 0 hed hed).2.2.2.2.1
  have hXu : D.naut.unr (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) := by
    rw [← hX]; exact D.naut.unr_char _ _ hed hVu heu
  obtain ⟨hWu, hSu⟩ := (D.naut.unr_sum _ _).1 hXu
  have hmu := GlobalTheory.MuBlock.frobEig_spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w hμ
  dsimp only at hmu
  have hVe : D.naut.frobEig (D.nbc.locAU j π w) =
      (D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹) +
      ((List.range D.R.t).map fun k => ({(m * e⁻¹) * ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^
        (((((D.R.t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum := by
    rw [hV, D.naut.frobEig_char _ _ _ hXu hbu hbd hb, D.naut.frobEig_sum _ _ hWu hSu, Multiset.map_add]
    rw [hmu.2, hm]
    congr 1
    rw [← Multiset.coe_mapAddMonoidHom, map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Multiset.coe_mapAddMonoidHom, Multiset.map_singleton]
    ring_nf
  have key := UpperTheory.GalN.string_count (Formalism.ConjugateSelfDual.normV w) D.R.t
    (Pa.map fun p => (p.d, D.naut.frobEig (D.naut.locG p.π w)))
    ((D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹)) (m * e⁻¹)
    (by exact_mod_cast GlobalTheory.LocalInv.one_lt_normV w) D.R.t_odd.pos
    (by rw [norm_mul, hmn, hbn, one_mul])
    (by
      intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      rw [norm_mul, hbn, mul_one]
      have := (hR w hs hg).2 α hα
      rwa [GlobalTheory.MuBlock.absNorm_eq_normV] at this)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      have k := _root_.GlobalTheory.MuBlockLoc.part_norm_o_alt D hT hL.temp hB p hp w (hPa p hp)
      refine ⟨(hB.1 p hp).2.1, ?_, fun α hα => (k α hα).1, fun ht α hα =>
        (k α hα).2 (UpperTheory.GalN.rank_one_of_long hB.2.2.1 hp (hB.1 p hp).1 ht)⟩
      intro h0
      change D.naut.frobEig (D.naut.locG p.π w) = 0 at h0
      have h1 := D.naut.frobEig_card _ (hPa p hp)
      rw [h0, D.naut.locG_dim] at h1
      have := (hB.1 p hp).1
      simp at h1
      omega)
    (by
      have hiso2 := hiso.2
      simp only [GlobalTheory.LocalInv.list_coe, List.map_map] at hiso2
      rw [List.map_map]
      exact hiso2.symm.trans ((congrArg D.naut.frobEig (hB.2.2.2.1 w hs)).trans hVe))
  refine ⟨?_, fun p hp hpt => ?_⟩
  · obtain ⟨x, hx, hxt⟩ := key.1
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact ⟨p, hp, hxt⟩
  · obtain ⟨h1, h2⟩ := key.2 _ (List.mem_map_of_mem (f := fun p : Part D.naut.CG => (p.d, D.naut.frobEig (D.naut.locG p.π w))) hp) hpt
    exact ⟨h1, h2.trans htw.symm⟩
end GlobalTheory.MuBlockLoc
end
end
