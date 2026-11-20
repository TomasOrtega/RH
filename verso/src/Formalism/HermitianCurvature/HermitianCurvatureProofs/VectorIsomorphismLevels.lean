import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVpic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c g`. Distinguish the cases in `hy : (c, g) ∈ DomR k r z z'`. Conclude with `h (c, g) hy`. Rewrite using `[Φ.2.1 (c, g) hy, Ψ.2.1 (c, g) hy]`.
-/
theorem radSp_ext {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {Φ Ψ : RadSp k r z z' π π'}
    (h : ∀ y ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hy : (c, g) ∈ DomR k r z z'
  · exact h (c, g) hy
  · rw [Φ.2.1 (c, g) hy, Ψ.2.1 (c, g) hy]

/- English proof (translation)
Introduce `hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' ε hε hx hx'`. Use `⟨waveG_nice (p.T.bs j) ε s w x hx, ?_⟩` and prove the remaining obligations. Take `⟨hl1, hlk, -⟩` from `p.hl`. Set `jF : Fin (P.r + 1)` to `⟨j, by omega⟩`. Establish `hPl` using `Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP`.

Take `⟨X⟩` from `Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl`. Take `⟨L, st, h1, h2, h3, h4, h5, h6⟩` from `Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0`. Take `⟨μ0, hμ0⟩` from `Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)`. Establish `hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j))) L st p.l0` using `⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩`. Use `set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ`.

Take `⟨K, hThm, -, -, hJ⟩` from `hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0 (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl`. Take `⟨Cst, hC, hform⟩` from `Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD`. Establish `hwOK` using `Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2`. Use `choose Φ hΦK hΦ using fun a => hJ (x a) ε hε (hx a).2.1 (hx a).2.2`. Use `choose Φ' hΦ'K hΦ' using fun a => hJ (x' a) ε hε (hx' a).2.1 (hx' a).2.2`.

Establish `hnx` using `waveG_nice (p.T.bs j) ε s w x hx`. Establish `hnx'` using `waveG_nice (p.T.bs j) ε s w x' hx'`. Use `show D.formLev p.T (M.sgn P p.l0) jF w (KB.waveG (p.T.bs j) s w x) (KB.waveG (p.T.bs j) s w x') = D.formLev p.T (M.sgn P p.l0) jF w x x'`. Establish `hmem : ∀ (Wv Wv' : Module.End ℂ (RadSp (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π')) (Ψ' : Ix (Fin w.length) → RadSp (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'), (∀ e, ∀ y ∈ D …`. Introduce `_ _ Ψ' hΨ' e`.

Take `⟨Ψ0, hΨ0K, hΨ0⟩` from `hJ (KB.waveG (p.T.bs j) s w x' e) ε hε (hnx' e).2.1 (hnx' e).2.2`. Establish `: Ψ' e = Ψ0` using `radSp_ext (fun y hy => (hΨ' e y hy).trans (hΨ0 y hy).symm)`. Rewrite using `[this]`. Conclude with `hΨ0K`. Distinguish the cases in `hr : 0 < P.r - j`.

Take `⟨Wv, hW⟩` from `waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' ⟨0, hr⟩ s`. Take `⟨Wv', hW'⟩` from `waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' ⟨0, hr⟩ (-s)`. Establish `hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z', (fun (c : Fin (P.r - j) → ℂ) (_ : Mx P.k (P.r - j)) => fsv s (c ⟨0, hr⟩)) y.1 y.2 = fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2) ⟨1, by omega⟩)` using `fun y hy => by`. Simplify using `only []`. Rewrite using `[first_minor_cell_eq_coord (p.T.bs jF).z_mem (p.T.bs jF).z'_mem hr y.1 hy.2.1]`.

Establish `hΨ` using `radPic_wave (p.T.bs jF) ε s w x hx Φ hΦ _ (by omega) hm Wv Wv' hW`. Establish `hΨ'` using `radPic_wave (p.T.bs jF) ε s w x' hx' Φ' hΦ' _ (by omega) hm Wv Wv' hW`. Rewrite using `[hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hx hx' hΦ hΦ']`. Use `congr 1`. Establish `key` using `rr_wave_A (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr s Wv Wv' hW hW' Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)`.

Unfold `RRform at key`. Conclude with `(JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))`. Establish `hr0 : P.r - j = 0` using `by omega`. Take `⟨Wv, hW⟩` from `waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' s`. Take `⟨Wv', hW'⟩` from `waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' (-s)`.

Establish `hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z', (fun (_ : Fin (P.r - j) → ℂ) (g : Mx P.k (P.r - j)) => fsv s (P5.zeta P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' g)) y.1 y.2 = fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 …` using `fun y hy => by`. Simplify using `only []`. Rewrite using `[first_minor_top_eq_zeta hr0]`. Establish `hΨ` using `radPic_wave (p.T.bs jF) ε s w x hx Φ hΦ _ (by omega) hm Wv Wv' hW`. Establish `hΨ'` using `radPic_wave (p.T.bs jF) ε s w x' hx' Φ' hΦ' _ (by omega) hm Wv Wv' hW`.

Rewrite using `[hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hx hx' hΦ hΦ']`. Use `congr 1`. Establish `key` using `rr_wave_B (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr0 s Wv Wv' hW hW' Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)`. Unfold `RRform at key`. Conclude with `(JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))`.
-/
theorem vIso_main : Formalism.FourierDecayAlt.KB.VIso := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' ε hε hx hx'
  refine ⟨waveG_nice (p.T.bs j) ε s w x hx, ?_⟩
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2
  choose Φ hΦK hΦ using fun a => hJ (x a) ε hε (hx a).2.1 (hx a).2.2
  choose Φ' hΦ'K hΦ' using fun a => hJ (x' a) ε hε (hx' a).2.1 (hx' a).2.2
  have hnx := waveG_nice (p.T.bs j) ε s w x hx
  have hnx' := waveG_nice (p.T.bs j) ε s w x' hx'
  show D.formLev p.T (M.sgn P p.l0) jF w (KB.waveG (p.T.bs j) s w x) (KB.waveG (p.T.bs j) s w x') =
    D.formLev p.T (M.sgn P p.l0) jF w x x'
  have hmem : ∀ (Wv Wv' : Module.End ℂ (RadSp (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z'
      (p.T.bs jF).π (p.T.bs jF).π')) (Ψ' : Ix (Fin w.length) → RadSp (JC.parLev P jF).k (JC.parLev P jF).r
      (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'),
      (∀ e, ∀ y ∈ DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        (Ψ' e : Fn (JC.parLev P jF).k (JC.parLev P jF).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _) (B.JF (p.T.bs jF) (KB.waveG (p.T.bs j) s w x' e))
            y.1 y.2) → InK (K 0) Ψ' := by
    intro _ _ Ψ' hΨ' e
    obtain ⟨Ψ0, hΨ0K, hΨ0⟩ := hJ (KB.waveG (p.T.bs j) s w x' e) ε hε (hnx' e).2.1 (hnx' e).2.2
    have : Ψ' e = Ψ0 := radSp_ext (fun y hy => (hΨ' e y hy).trans (hΨ0 y hy).symm)
    rw [this]
    exact hΨ0K
  by_cases hr : 0 < P.r - j
  · obtain ⟨Wv, hW⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ s
    obtain ⟨Wv', hW'⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (c : Fin (P.r - j) → ℂ) (_ : Mx P.k (P.r - j)) => fsv s (c ⟨0, hr⟩)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_cell_eq_coord (p.T.bs jF).z_mem (p.T.bs jF).z'_mem hr y.1 hy.2.1]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hx Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx' Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hx hx' hΦ hΦ']
    congr 1
    have key := rr_wave_A (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))
  · have hr0 : P.r - j = 0 := by omega
    obtain ⟨Wv, hW⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' s
    obtain ⟨Wv', hW'⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (_ : Fin (P.r - j) → ℂ) (g : Mx P.k (P.r - j)) => fsv s (P5.zeta P.k (P.r - j) (p.T.bs jF).z
          (p.T.bs jF).z' g)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_top_eq_zeta hr0]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hx Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx' Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hx hx' hΦ hΦ']
    congr 1
    have key := rr_wave_B (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr0 s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))

end Formalism.FourierDecayAlt.P.PBFV

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.PBFV.vIso_main`.
-/
theorem vector_isomorphism_levels : Formalism.FourierDecayAlt.KB.VIso := Formalism.FourierDecayAlt.P.PBFV.vIso_main

end Formalism.FourierDecayAlt.P
