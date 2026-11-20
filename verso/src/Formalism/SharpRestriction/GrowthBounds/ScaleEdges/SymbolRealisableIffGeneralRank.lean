import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ExistsPolFamilyOfMemGenOfVsDegLe
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.MultidegreeBoundLeA

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

/- English proof (translation)
Set `_ : Algebra (WF p n') O` to `algOfIdent j φ`. Use `⟨dvrOfStd_sq h, ?_, ?_⟩` and prove the remaining obligations. Use `show (j.comp (φ : WF p n' →+* W)).Finite`. Conclude with `RingHom.Finite.comp h.1.finite (RingHom.Finite.of_surjective _ φ.surjective)`. Use `show Function.Injective (j.comp (φ : WF p n' →+* W))`.

Establish `hj : Function.Injective j`. Introduce `a b hab`. Establish `h1 : algebraMap O Kf (j a) = algebraMap O Kf (j b)` using `congrArg _ hab`. Rewrite `h1` using `[← h.1.ι_comp, ← h.1.ι_comp]`. Use `h.1.frac_alt` as an intermediate fact.

Conclude with `IsFractionRing.injective W Qq (ι.injective h1)`. Conclude with `hj.comp φ.injective`.
-/
theorem oHyp_of {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w)
    (φ : WF p n' ≃+* W) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    OHyp p n' O (dvrOfStd h) := by
  let _ : Algebra (WF p n') O := algOfIdent j φ
  refine ⟨dvrOfStd_sq h, ?_, ?_⟩
  · show (j.comp (φ : WF p n' →+* W)).Finite
    exact RingHom.Finite.comp h.1.finite (RingHom.Finite.of_surjective _ φ.surjective)
  · show Function.Injective (j.comp (φ : WF p n' →+* W))
    have hj : Function.Injective j := by
      intro a b hab
      have h1 : algebraMap O Kf (j a) = algebraMap O Kf (j b) := congrArg _ hab
      rw [← h.1.ι_comp, ← h.1.ι_comp] at h1
      have := h.1.frac_alt
      exact IsFractionRing.injective W Qq (ι.injective h1)
    exact hj.comp φ.injective

def castVK {n' k r K : ℕ} (hk : k = r + K) : Fin n' × Fin (r + K) → Fin n' × Fin k :=
  fun v => (v.1, Fin.cast hk.symm v.2)

section Lift

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (w : O)

def SymbolRealisableGeneralRank {k r K : ℕ} [NeZero r] [NeZero K] (hk : k = r + K) (hrk : r ≤ k) (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (deg dTop : Fin n' → ℕ) (c' Q E₀ : ℕ) : Prop :=
  ∃ E' : Fin n' → ℕ, (∀ t ∈ F.TT, E' t ≤ E₀ ∧ E' t ≤ deg t) ∧
    ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
    ∀ P ∈ Gen O p K F XXs (G2d F deg E'), ∀ T : ℕ, (∀ mm ∈ P.support, vsDeg mm ≤ T) →
      ∃ Fs : ℕ → ↥((Pol (KK O) (ι := Fin n') k dTop).restrictScalars O),
        (∀ o, HasMultideg (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O))) dTop ∧
          InWj w (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O))) 0 ∧
          Realisable p n' w n' r g c' o (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O)))) ∧
        ∑ o ∈ Finset.range (T + 1), subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O)) =
          MvPolynomial.map (algebraMap O (KK O)) (rename (castVK hk) P) *
            subst p n' O w n' r g (SPtrue p n' O F hrk g c' Q)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem symbol_realisable_iff_general_rank {m r K : ℕ} [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (deg dTop : Fin n' → ℕ) (c' Q E₀ : ℕ) :
    SymbolRealisableAt p n' O w hk hrk F XXs deg dTop c' Q E₀ ↔ SymbolRealisableGeneralRank p n' O w hk hrk F XXs deg dTop c' Q E₀ := Iff.rfl

end Lift

/- English proof (translation)
Substitute `hk` using the available equality. Use `⟨eSP p n' F (r + K) c' (p ^ G'), hE1, ?_⟩` and prove the remaining obligations. Introduce `g hg P hP T hT'`. Set `X : Ctx p n' r K O` to `{ S := S, hO := hO, hH := hH, Fr := F, L₁ := L₁, N₁ := N₁, G' := G', hV := hV, hT := hT, hG := hG, hK := hK, g := g, hg := hg }`. Establish `hd : ∀ s, G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s + eSP p n' F (r + K) c' (p ^ G') s = dTop s`.

Introduce `s`. Unfold `G2d`. Rewrite using `[hdT s]`. Distinguish the cases in `hs : s ∈ F.TT`. Rewrite using `[if_pos hs, if_pos hs]`.

Use `(hE1 s hs).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hs, if_neg hs, hE0 s hs]`. Establish `hd0 : ∀ s, s ∉ F.TT → G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s = 0`. Introduce `s hs`.

Unfold `G2d`. Rewrite using `[if_neg hs]`. Establish `hren : rename (castVK (n'` using `n') (rfl : r + K = r + K)) P = P := by`. Establish `: (castVK (n'` using `n') (rfl : r + K = r + K)) = id := by`. Use function extensionality and compare the values at `v`.

Both sides reduce to the same expression. Rewrite using `[this, rename_id_apply]`. Rewrite using `[hren]`. Conclude with `exists_pol_family_of_mem_gen_of_vsDeg_le X D hW1 hW2 hMon c' mg th o hmg _ _ dTop hd hd0 (SPtrue_hom p n' O F hH.2.2.1 g c' (p ^ G')) P hP T hT'`.
-/
theorem symbol_realisable_general_rank (D : Formalism.BasicNotions.D7) (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (hMon : RestMon) {p n' : ℕ} [Fact p.Prime] [NeZero n']
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF p n') O] (S : UniformizedDVR p O)
    (hO : OHyp p n' O S) {k r K : ℕ} [NeZero r] [NeZero K] (hk : k = r + K) (hH : CommonHypotheses p n' r k) (F : Frames n' r)
    (L₁ N₁ G' : ℕ) (hV : F.Valid L₁ N₁) (hT : TwistBound p F (p ^ G')) (hG : ∀ j : ℤ, zF F j - F.fr (j - 1) 0 ≤ G')
    (hK : N₁ + 2 * r ≤ K) (mg : ℤ → ℤ → ℤ) (th o : ℤ → ℤ → ℝ) (hmg : ∀ j x, 0 ≤ mg j x) (deg dTop : Fin n' → ℕ)
    (c' E₀ : ℕ) (hdT : ∀ s, dTop s = if s ∈ F.TT then deg s else 0)
    (hE1 : ∀ t ∈ F.TT, eSP p n' F k c' (p ^ G') t ≤ E₀ ∧ eSP p n' F k c' (p ^ G') t ≤ deg t)
    (hE0 : ∀ t, t ∉ F.TT → eSP p n' F k c' (p ^ G') t = 0) :
    SymbolRealisableGeneralRank p n' O S.w hk hH.2.2.1 F (fun j => XX' O r K F j (mg j) (th j) (o j)) deg dTop c' (p ^ G') E₀ := by
  subst hk
  refine ⟨eSP p n' F (r + K) c' (p ^ G'), hE1, ?_⟩
  intro g hg P hP T hT'
  let X : Ctx p n' r K O :=
    { S := S, hO := hO, hH := hH, Fr := F, L₁ := L₁, N₁ := N₁, G' := G', hV := hV, hT := hT, hG := hG, hK := hK,
      g := g, hg := hg }
  have hd : ∀ s, G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s + eSP p n' F (r + K) c' (p ^ G') s = dTop s := by
    intro s
    unfold G2d
    rw [hdT s]
    by_cases hs : s ∈ F.TT
    · rw [if_pos hs, if_pos hs]
      have := (hE1 s hs).2
      omega
    · rw [if_neg hs, if_neg hs, hE0 s hs]
  have hd0 : ∀ s, s ∉ F.TT → G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s = 0 := by
    intro s hs
    unfold G2d
    rw [if_neg hs]
  have hren : rename (castVK (n' := n') (rfl : r + K = r + K)) P = P := by
    have : (castVK (n' := n') (rfl : r + K = r + K)) = id := by
      funext v
      rfl
    rw [this, rename_id_apply]
  rw [hren]
  exact exists_pol_family_of_mem_gen_of_vsDeg_le X D hW1 hW2 hMon c' mg th o hmg _ _ dTop hd hd0 (SPtrue_hom p n' O F hH.2.2.1 g c' (p ^ G')) P hP T hT'

/- English proof (translation)
Introduce `hA _`. Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a15, a16, a17, a18, _, a20, _⟩` from `hA`. Establish `hW1 : GeneratorSpanInclusion` using `generator_pair_conditions_of_admitted D a15 a16`. Establish `hW2 : GeneratorImageIsSymbol` using `generator_path_homogeneous_holds D a17 a18 a20`. Establish `hMon : RestMon` using `restMon D`.

Use `⟨30, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ _ K _ _ hk hrk F hF`. Set `_ : Algebra (WF p n') O` to `algOfIdent j φ`. Rewrite using `[symbol_realisable_iff_general_rank]`. Establish `hB` using `hyps_basic (C := C) (by linarith) H`.

Establish `hTT` using `hF.1`. Establish `hGn : goodG' r de h x ≤ n'` using `by have := H.2.2.1.2.2.2; omega`. Establish `hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r` using `H.2.2.2.2.2.2.2.1`. Establish `hH : CommonHypotheses p n' r (m + 1)` using `⟨H.1, H.2.1, hrk, hSet.1.two_le, hSet.1.even⟩`. Establish `eE : E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) = E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)` using `by rw [hk]`.

Rewrite using `[eE]`. Use `show SymbolRealisableGeneralRank p n' O (dvrOfStd hSet).w hk hH.2.2.1 F (fun j => XX' O r K F j _ _ _) _ _ _ _ _`. Use `symbol_realisable_general_rank D hW1 hW2 hMon O (dvrOfStd hSet) (oHyp_of hSet φ) hk hH F L₁ (orbitWindowCount r de h x) (goodG' r de h x) hF.2.1 (twist_of hF (by have := H.2.1; omega) hGn p (by have := H.1; omega)) (fun j => (hF.2.2.1 j).le) (by omega) _ _ _ ?_ (flatDeg lam0) (dT …` and prove the remaining obligations. Introduce `j x'`. Check the signs of the components of the expression.

Introduce `s`. Unfold `dT`. Rewrite using `[hTT]`. Introduce `t ht`. Conclude with `spdeg hC H hF t ht`.

Introduce `t ht`. Conclude with `eSP_off hF _ _ _ t ht`.
-/
theorem sources_realisable_holds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz : ℝ) : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz := by
  intro hA _
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a15, a16, a17, a18, _, a20, _⟩ := hA
  have hW1 : GeneratorSpanInclusion := generator_pair_conditions_of_admitted D a15 a16
  have hW2 : GeneratorImageIsSymbol := generator_path_homogeneous_holds D a17 a18 a20
  have hMon : RestMon := restMon D
  refine ⟨30, by norm_num, ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ _ K
    _ _ hk hrk F hF
  let _ : Algebra (WF p n') O := algOfIdent j φ
  rw [symbol_realisable_iff_general_rank]
  have hB := hyps_basic (C := C) (by linarith) H
  have hTT := hF.1
  have hGn : goodG' r de h x ≤ n' := by have := H.2.2.1.2.2.2; omega
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hH : CommonHypotheses p n' r (m + 1) := ⟨H.1, H.2.1, hrk, hSet.1.two_le, hSet.1.even⟩
  have eE : E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) =
      E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) := by rw [hk]
  rw [eE]
  show SymbolRealisableGeneralRank p n' O (dvrOfStd hSet).w hk hH.2.2.1 F (fun j => XX' O r K F j _ _ _) _ _ _ _ _
  refine symbol_realisable_general_rank D hW1 hW2 hMon O (dvrOfStd hSet) (oHyp_of hSet φ) hk hH F L₁ (orbitWindowCount r de h x) (goodG' r de h x)
    hF.2.1 (twist_of hF (by have := H.2.1; omega) hGn p (by have := H.1; omega))
    (fun j => (hF.2.2.1 j).le) (by omega) _ _ _ ?_ (flatDeg lam0) (dT TT lam0) (cPrime n' r TT.card c0 cpp cStar) _
    ?_ ?_ ?_
  · intro j x'
    positivity
  · intro s
    unfold dT
    rw [hTT]
  · intro t ht
    exact spdeg hC H hF t ht
  · intro t ht
    exact eSP_off hF _ _ _ t ht

end Formalism.MainNotions.Pf14
