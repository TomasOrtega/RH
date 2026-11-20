import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay

open Matrix MeasureTheory Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cont

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Establish `hv : Continuous (fun A : Wq →L[ℂ] Wp => B.hsVec A)`. Unfold `B.hsVec`. Conclude with `(PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_eval_const _)`. Unfold `B.hsInner`. Conclude with `(hv.comp continuous_snd).inner (hv.comp continuous_fst)`.
-/
theorem continuous_hsInner [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] :
    Continuous fun q : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => B.hsInner q.1 q.2 := by
  have hv : Continuous (fun A : Wq →L[ℂ] Wp => B.hsVec A) := by
    unfold B.hsVec
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_eval_const _)
  unfold B.hsInner
  exact (hv.comp continuous_snd).inner (hv.comp continuous_fst)

/- English proof (translation)
Introduce `ζ₀ hζ₀`. Establish `hmem` using `Ψ.2`. Take `⟨-, hs, -⟩` from `hmem`. Take `⟨U, F, hU, hxU, hF, hΦ⟩` from `hs (c0, g ζ₀) (hdom ζ₀ hζ₀)`. Establish `hgA : ContinuousAt g ζ₀` using `hg.continuousAt (hO.mem_nhds hζ₀)`.

Establish `hpA : ContinuousAt (fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) ζ₀` using `continuousAt_const.prodMk hgA`. Establish `hev : ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ O ∧ ((c0, g ζ) : (Fin r → ℂ) × Mx k r) ∈ U` using `Filter.Eventually.and (hO.mem_nhds hζ₀) (hpA.preimage_mem_nhds (hU.mem_nhds hxU))`. Establish `hFc : ContinuousAt F (c0, g ζ₀)` using `hF.continuousOn.continuousAt (hU.mem_nhds hxU)`. Establish `hcomp : ContinuousAt (fun ζ => F (c0, g ζ)) ζ₀` using `ContinuousAt.comp (g := F) (f := fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) hFc hpA`. Use `(hcomp.congr ?_).continuousWithinAt` and prove the remaining obligations.

Use `filter_upwards [hev] with ζ hζ`. Conclude with `(hΦ (c0, g ζ) hζ.2 (hdom ζ hζ.1).2.1).symm`.
-/
theorem radSp_contOn {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (Ψ : RadSp k r z z' π π') (c0 : Fin r → ℂ) {g : ℂ → Mx k r} {O : Set ℂ}
    (hO : IsOpen O) (hg : ContinuousOn g O) (hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR k r z z') :
    ContinuousOn (fun ζ => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ)) O := by
  intro ζ₀ hζ₀
  have hmem := Ψ.2
  obtain ⟨-, hs, -⟩ := hmem
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c0, g ζ₀) (hdom ζ₀ hζ₀)
  have hgA : ContinuousAt g ζ₀ := hg.continuousAt (hO.mem_nhds hζ₀)
  have hpA : ContinuousAt (fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) ζ₀ :=
    continuousAt_const.prodMk hgA
  have hev : ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ O ∧ ((c0, g ζ) : (Fin r → ℂ) × Mx k r) ∈ U :=
    Filter.Eventually.and (hO.mem_nhds hζ₀) (hpA.preimage_mem_nhds (hU.mem_nhds hxU))
  have hFc : ContinuousAt F (c0, g ζ₀) := hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  have hcomp : ContinuousAt (fun ζ => F (c0, g ζ)) ζ₀ :=
    ContinuousAt.comp (g := F) (f := fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) hFc hpA
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [hev] with ζ hζ
  exact (hΦ (c0, g ζ) hζ.2 (hdom ζ hζ.1).2.1).symm

/- English proof (translation)
Establish `h1 : ∀ e, ContinuousOn (fun ζ => B.hsInner ((act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ)) ((act (Fr.ofWord L st w).F y e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ))) O`. Introduce `e`. Establish `ha` using `radSp_contOn (act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e) c0 hO hg hdom`. Establish `hb` using `radSp_contOn (act (Fr.ofWord L st w).F y e) c0 hO hg hdom`. Establish `hc` using `continuous_hsInner.comp_continuousOn (ha.prodMk hb)`.

Conclude with `hc`. Establish `h2` using `continuousOn_finset_sum Finset.univ (fun e _ => h1 e)`. Use `h2.congr fun ζ _ => ?_` and prove the remaining obligations. Unfold `topDens`. Both sides reduce to the same expression.
-/
theorem topDens_contOn {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (x y : Ix S → RadSp k r z z' π π') (c0 : Fin r → ℂ) {g : ℂ → Mx k r} {O : Set ℂ}
    (hO : IsOpen O) (hg : ContinuousOn g O) (hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR k r z z') :
    ContinuousOn (fun ζ => topDens L st w x y c0 (g ζ)) O := by
  have h1 : ∀ e, ContinuousOn (fun ζ => B.hsInner
      ((act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ))
      ((act (Fr.ofWord L st w).F y e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ))) O := by
    intro e
    have ha := radSp_contOn (act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e) c0 hO hg hdom
    have hb := radSp_contOn (act (Fr.ofWord L st w).F y e) c0 hO hg hdom
    have hc := continuous_hsInner.comp_continuousOn (ha.prodMk hb)
    exact hc
  have h2 := continuousOn_finset_sum Finset.univ (fun e _ => h1 e)
  refine h2.congr fun ζ _ => ?_
  unfold topDens
  rfl

end cont

/- English proof (translation)
Simplify using `[UWset, UH]`.
-/
theorem one_mem_UWset {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z := by
  simp [UWset, UH]

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' Cb hθ hF hw`. Take `⟨hl1, hlk, -⟩` from `p.hl`. Set `jF : Fin (P.r + 1)` to `⟨P.r, by omega⟩`. Establish `hPl` using `Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP`. Take `⟨X⟩` from `Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl`.

Take `⟨L, st, h1, h2, h3, h4, h5, h6⟩` from `Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0`. Take `⟨μ0, hμ0⟩` from `Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)`. Establish `hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r))) L st p.l0` using `⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩`. Use `set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r)) with hμ`. Take `⟨K, -, -, -, hJ⟩` from `hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0 (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl`.

Establish `hcx : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h hh.2 e)` using `fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h hh hF e`. Establish `hcx' : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h' hh'.2 e)` using `fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h' hh' hF e`. Use `choose Φ hΦK hΦ using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx e)`. Use `choose Φ' hΦ'K hΦ' using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx' e)`. Establish `hHTx` using `hHT Wp Wq P p F w h h' hh hh' X μ L st Cb Φ Φ' hD hθ hF hw hΦ hΦ'`.

Establish `hTT : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T * P.T'`. Establish `e1` using `hPl.2.2.2.1`. Establish `e2` using `hPl.2.2.2.2.1`. Conclude with `congrArg₂ (· * ·) e1 e2`. Set `O : Set ℂ` to `{c : ℂ | P.T * P.T' < Complex.normSq c}`.

Establish `hO : IsOpen O` using `isOpen_lt continuous_const Complex.continuous_normSq`. Set `g : ℂ → Mx P.k (P.r - P.r)` to `fun ζ => B2.embWb P.k (P.r - P.r) ((p.T.bs P.r).μsec ζ)`. Set `c0 : Fin (P.r - P.r) → ℂ` to `fun _ => 1`. Establish `hfacts : ∀ ζ ∈ O, g ζ ∈ B2.UWb P.k (P.r - P.r) ∧ herm (Hpk P.k (P.r - P.r)) (g ζ *ᵥ (p.T.bs P.r).z') (p.T.bs P.r).z = ζ`. Introduce `ζ hζ`.

Establish `hζ' : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' < Complex.normSq ζ` using `by rw [hTT]; exact hζ`. Use `Formalism.FourierDecayAlt.P.b2_rank_one_mem P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).μsec (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem (p.T.bs P.r).sec ζ hζ' 1 (one_mem_UWset _) 1 (one_mem_UWset _)` as an intermediate fact. Simplify using `using this`. Establish `hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z'`. Introduce `ζ hζ`.

Take `⟨hmem, hherm⟩` from `hfacts ζ hζ`. Use `⟨fun _ => one_ne_zero, Formalism.FourierDecayAlt.P.JCx2.rb_uwb_glev hmem, ?_⟩` and prove the remaining obligations. Unfold `Q.GGl`. Rewrite using `[P5.Rad.zetaL_last, hherm, hTT]`. Conclude with `sub_pos.2 hζ`.

Establish `hzeta : ∀ ζ ∈ O, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (g ζ) = ζ`. Introduce `ζ hζ`. Rewrite using `[P5.Rad.zetaL_last, (hfacts ζ hζ).2]`. Establish `hg : ContinuousOn g O`. Use `continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_` and prove the remaining obligations.

Simplify using `only [g, B2.embWb]`. Use `split_ifs`. Conclude with `((p.T.bs P.r).sec.1 _ _).continuousOn.mono (fun ζ hζ => by`. Simplify using `only [Set.mem_ofPred_eq]`. Rewrite using `[hTT]`.

Conclude with `hζ)`. Conclude with `continuousOn_const`. Conclude with `continuousOn_const`. Establish `hcont : ContinuousOn (fun ζ => topDens L st (D.positionted w) Φ Φ' c0 (g ζ)) O` using `topDens_contOn L st (D.positionted w) Φ Φ' c0 hO hg hdom`. Use `hcont.congr fun ζ hζ => ?_` and prove the remaining obligations.

Use `hHTx (c0, g ζ) (hdom ζ hζ)` as an intermediate fact. Simplify using `only [] at this`. Rewrite `this` using `[hzeta ζ hζ]`. Conclude with `this.symm`.
-/
theorem topContOn_of (hP : P5.ThmPActualCpt) (hHT : KB.HeadTop) : TopContOn := by
  intro Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' Cb hθ hF hw
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨P.r, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r)) with hμ
  obtain ⟨K, -, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hcx : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h hh.2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h hh hF e
  have hcx' : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h' hh'.2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h' hh' hF e
  choose Φ hΦK hΦ using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx e)
  choose Φ' hΦ'K hΦ' using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx' e)
  have hHTx := hHT Wp Wq P p F w h h' hh hh' X μ L st Cb Φ Φ' hD hθ hF hw hΦ hΦ'
  have hTT : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T * P.T' := by
    have e1 := hPl.2.2.2.1
    have e2 := hPl.2.2.2.2.1
    exact congrArg₂ (· * ·) e1 e2
  let O : Set ℂ := {c : ℂ | P.T * P.T' < Complex.normSq c}
  have hO : IsOpen O := isOpen_lt continuous_const Complex.continuous_normSq
  let g : ℂ → Mx P.k (P.r - P.r) := fun ζ => B2.embWb P.k (P.r - P.r) ((p.T.bs P.r).μsec ζ)
  let c0 : Fin (P.r - P.r) → ℂ := fun _ => 1
  have hfacts : ∀ ζ ∈ O, g ζ ∈ B2.UWb P.k (P.r - P.r) ∧
      herm (Hpk P.k (P.r - P.r)) (g ζ *ᵥ (p.T.bs P.r).z') (p.T.bs P.r).z = ζ := by
    intro ζ hζ
    have hζ' : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' < Complex.normSq ζ := by rw [hTT]; exact hζ
    have := Formalism.FourierDecayAlt.P.b2_rank_one_mem P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).μsec (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem (p.T.bs P.r).sec ζ hζ'
      1 (one_mem_UWset _) 1 (one_mem_UWset _)
    simpa using this
  have hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' := by
    intro ζ hζ
    obtain ⟨hmem, hherm⟩ := hfacts ζ hζ
    refine ⟨fun _ => one_ne_zero, Formalism.FourierDecayAlt.P.JCx2.rb_uwb_glev hmem, ?_⟩
    unfold Q.GGl
    rw [P5.Rad.zetaL_last, hherm, hTT]
    exact sub_pos.2 hζ
  have hzeta : ∀ ζ ∈ O, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (g ζ) = ζ := by
    intro ζ hζ
    rw [P5.Rad.zetaL_last, (hfacts ζ hζ).2]
  have hg : ContinuousOn g O := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    simp only [g, B2.embWb]
    split_ifs
    · exact ((p.T.bs P.r).sec.1 _ _).continuousOn.mono (fun ζ hζ => by
        simp only [Set.mem_ofPred_eq]; rw [hTT]; exact hζ)
    · exact continuousOn_const
    · exact continuousOn_const
  have hcont : ContinuousOn (fun ζ => topDens L st (D.positionted w) Φ Φ' c0 (g ζ)) O :=
    topDens_contOn L st (D.positionted w) Φ Φ' c0 hO hg hdom
  refine hcont.congr fun ζ hζ => ?_
  have := hHTx (c0, g ζ) (hdom ζ hζ)
  simp only [] at this
  rw [hzeta ζ hζ] at this
  exact this.symm

end Formalism.FourierDecayAlt.P.PBO
