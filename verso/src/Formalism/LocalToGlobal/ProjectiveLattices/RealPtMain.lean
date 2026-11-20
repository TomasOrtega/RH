import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D}

/- English proof (translation)
Establish `h1 : W ^ k * W⁻¹ ^ k = 1` using `by rw [← mul_pow, mul_inv_cancel₀ hW, one_pow]`. Rewrite using `[mul_inv, mul_pow, div_eq_mul_inv, ← inv_pow]`. Take the linear combination `(R * S⁻¹ ^ k) * h1`.
-/
theorem mul_ringHom_units_ratio {K : Type} [Field K] {W S R : K} (hW : W ≠ 0) (k : ℕ) :
    W ^ k * R * (W * S)⁻¹ ^ k = R / S ^ k := by
  have h1 : W ^ k * W⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hW, one_pow]
  rw [mul_inv, mul_pow, div_eq_mul_inv, ← inv_pow]
  linear_combination (R * S⁻¹ ^ k) * h1

set_option maxHeartbeats 4000000 in
/- English proof (translation)
Establish `hWD` using `h.toLawsCore.evalWD j hj`. Introduce `ζ`. Use `haveI hD : IsDVRAt (show Pts (Op (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.N) (OsK (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.w) from ζ) := ‹∀ ζ : PtsG G la, IsDVRAt ζ› ζ`. Use `haveI : CharZero (Loc ζ) := loc_charZero hU ζ`. Take `⟨Tc, ι, hloc, hunr⟩` from `complSt_holds (Loc ζ)`.

Establish `hι : AddValPres ζ ι` using `addVal_map_of_unr ι hunr`. Set `kap : Kp (recPlus h j hj) la G.N →+* Tc.Fr` to `kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι`. Use `letI instK : Algebra (Kp (recPlus h j hj) la G.N) Tc.Fr := kap.toAlgebra`. Set `φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] Tc.Fr` to `{ toRingHom := phiAt ζ Tc.Fr ι hU hι, commutes' := fun _ => by rfl }`. Take `⟨alg, y₀, ⟨Z, ψ, hψ⟩, halg, hs0, hrat⟩` from `hPt hwL Tc.Fr φ`.

Establish `halg' : alg = kap.comp ((@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _ (Kp.algKl (recPlus h j hj) la G.N)).comp (algebraMap (recB h.toLawsCore).KO ((recPlus h j hj).Kl la)))` using `RingHom.ext fun a => halg a`. Establish `ho : OverLa la Tc.V alg (ep (unifO (recPlus h j hj) la G.N) ζ)`. Rewrite using `[halg']`. Conclude with `overLa_kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι`. Take `⟨O, _, β, Y, -, hPI, hB⟩` from `hMod`.

Take `⟨b, hb⟩` from `hB Tc alg _ ho`. Use `letI := alg.toAlgebra`. Take `⟨y, t, hbor⟩` from `intFr_of_model hIF Tc alg Y hPI b hb y₀`. Take `⟨p, φ', y', hm⟩` from `hT Z`. Establish `hm2 : FrMap (ψ.comp φ') y' y₀` using `frMap_trans _ _ _ φ' ψ y' (genFr hG Z) y₀ hm hψ`.

Establish `hy₀T : FromTest (K` using `T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) y₀ := ⟨p, ψ.comp φ', y', hm2⟩`. Establish `hW : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), evI y (F : T.R j) = wchar (ex (T.Q.Dw j) (wtA w) w.n) t * evR (T.Q.Xo j) T.Q.c (F : T.R j) y₀` using `fun w F => hWt (wtA w) w.n (F : T.R j) (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)) Tc.Fr t y₀ y.1 hy₀T y.2.1 hbor`. Set `χ : (recPlus h j hj).Forms →+* Tc.Fr` to `chiI j y`. Set `ev : Rp (recPlus h j hj) la G.N →+* Tc.Fr` to `evRp la G.N kap χ (fun a f => by`. Establish `e` using `chiI_smul j y a f`.

Rewrite `e` using `[halg a]`. Conclude with `e)`. Establish `hev_k : ∀ c : Kp (recPlus h j hj) la G.N, ev (algebraMap _ (Rp (recPlus h j hj) la G.N) c) = kap c` using `evRp_alg la G.N kap χ _`. Establish `hev_inc : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), ev (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc w F)) = evI y (F : T.R j)`. Introduce `w F`.

Conclude with `(evRp_emb la G.N kap χ _ ((recPlus h j hj).inc w F)).trans (chiI_inc j h y w F)`. Establish `hev_sec : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) = ∑ k, kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) * evI y ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j)`. Unfold `Formalism.MainNotions.Gaps.EtaleWeightGaps.sec`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, map_mul, hev_k, hev_inc]`. Establish `hs0' : (∑ k, kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) * evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀) ≠ 0` using `hs0`. Establish `hev_s0 : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) = wchar (ex (T.Q.Dw j) (wtA wL) wL.n) t * ∑ k, kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) * evR (T.Q.Xo j) T.Q.c ((G.w k : (r …`. Rewrite using `[hev_sec, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hW wL (G.w k)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))` using `IsUnit.mk0 _ (by rw [hev_s0]; exact mul_ne_zero (wchar_ne_zero _ _) hs0')`. Set `yV : PtV (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) Unit (fun _ _ _ _ => True) la` to `PtV.mk la ho y trivial () trivial`. Set `yP : (extAll h j hj).Pt' la` to `⟨vAtV yV, yV, rfl⟩`.

Use `⟨yP, Tc, ι, hloc, hunr, ev, hu, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w F`. Rewrite using `[extAll_vAt_inc]`. Use `show vAtV yV (F : T.R j) = _`. Conclude with `congrArg (nval Tc.V (ep (unifO (recPlus h j hj) la G.N) ζ)) (hev_inc w F).symm`.

Introduce `x`. Take `⟨k, ⟨g, hg⟩, rfl⟩` from `exists_weightZero_fraction_eq _ _ _ x`. Rewrite using `[coe_weightZeroFraction, liftEv_frac]`. Establish `key : ∀ (g : Rp (recPlus h j hj) la G.N) (hg : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k)) (hg' : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k)), ev g * (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))⁻¹ ^ k = phiAt ζ Tc.Fr ι hU (ad …`. Introduce `g hg`.

Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg0`. Introduce `hg'`. Take `⟨F, rfl⟩` from `hg0`. Establish `hr` using `hrat k F`.

Establish `hr' : phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr) (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ F), hg'⟩)) = evR (T.Q.Xo j) T.Q.c ((F : T.R j)) y₀ / (∑ k', kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (rec …` using `hr`. Rewrite using `[hr', hev_inc, hW, ex_addL, wchar_nsmul, hev_s0]`. Conclude with `mul_ringHom_units_ratio (wchar_ne_zero (ex (T.Q.Dw j) (wtA wL) wL.n) t) k`. Consider the case `zero`. Introduce `hg'`.

Establish `e0 : fr0 (recPlus h j hj) la G.w k ⟨0, hg'⟩ = 0` using `Subtype.ext (by rw [coe_weightZeroFraction]; exact map_zero _)`. Rewrite using `[e0, map_zero, map_zero, map_zero, zero_mul]`. Consider the case `add a b ha hb iha ihb`. Introduce `hg'`. Establish `e1 : fr0 (recPlus h j hj) la G.w k ⟨a + b, hg'⟩ = fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩ + fr0 (recPlus h j hj) la G.w k ⟨b, hb⟩` using `Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_add, coe_weightZeroFraction, coe_weightZeroFraction]; exact map_add _ _ _)`.

Rewrite using `[e1, map_add (toOsK (recPlus h j hj) la G.w), map_add (phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr)), map_add ev, add_mul, iha ha, ihb hb]`. Consider the case `smul c a ha iha`. Introduce `hg'`. Establish `e1 : fr0 (recPlus h j hj) la G.w k ⟨c • a, hg'⟩ = c • fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩` using `Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_smul, coe_weightZeroFraction]; exact map_smul _ _ _)`. Rewrite using `[e1, map_smul (toOsK (recPlus h j hj) la G.w) c, Algebra.smul_def c (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩)), map_mul, ← iha ha, Algebra.smul_def c a, map_mul, hev_k, mul_assoc]`.

Both sides reduce to the same expression. Conclude with `key g hg hg`. Introduce `w F hNZ`. Rewrite using `[show ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = evI y (F : T.R j) from hev_inc w F, hW w F]`. Use `mul_ne_zero (wchar_ne_zero _ _) ?_` and prove the remaining obligations.

Establish `hnat` using `(cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)).1`. Rewrite using `[evR_eq_of_map hWD hnat y₀ p (ψ.comp φ') y' hm2, AlgHom.comp_apply]`. Establish `h2 : evC hG Z (F : T.R j) = φ' ((F : T.R j) p y')` using `evR_eq_of_map hWD hnat (genFr hG Z) p φ' y' hm`. Rewrite using `[← h2]`. Conclude with `(map_ne_zero_iff _ ψ.toRingHom.injective).2 (hNZ Z)`.
-/
theorem realPt_of (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hwL : 0 < wL.n) (hPt : PtOfSSt h j hj hG G la) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    (hIF : IntFramesSt (T.Q.Xo j) T.Q.c) (hWt : WtField (T.Q.Xo j) T.Q.c)
    (hMod : ModelAtSt (T.Q.Xo j) T.Q.c la) :
    RealPtNZSt h j hj hG G la hU := by
  have hWD := h.toLawsCore.evalWD j hj
  intro ζ
  haveI hD : IsDVRAt (show Pts (Op (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.N)
      (OsK (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.w) from ζ) :=
    ‹∀ ζ : PtsG G la, IsDVRAt ζ› ζ
  haveI : CharZero (Loc ζ) := loc_charZero hU ζ
  obtain ⟨Tc, ι, hloc, hunr⟩ := complSt_holds (Loc ζ)
  have hι : AddValPres ζ ι := addVal_map_of_unr ι hunr
  let kap : Kp (recPlus h j hj) la G.N →+* Tc.Fr :=
    kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι
  letI instK : Algebra (Kp (recPlus h j hj) la G.N) Tc.Fr := kap.toAlgebra
  let φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] Tc.Fr :=
    { toRingHom := phiAt ζ Tc.Fr ι hU hι, commutes' := fun _ => by rfl }
  obtain ⟨alg, y₀, ⟨Z, ψ, hψ⟩, halg, hs0, hrat⟩ := hPt hwL Tc.Fr φ
  have halg' : alg = kap.comp ((@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _
      (Kp.algKl (recPlus h j hj) la G.N)).comp (algebraMap (recB h.toLawsCore).KO ((recPlus h j hj).Kl la))) :=
    RingHom.ext fun a => halg a
  have ho : OverLa la Tc.V alg (ep (unifO (recPlus h j hj) la G.N) ζ) := by
    rw [halg']
    exact overLa_kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι
  obtain ⟨O, _, β, Y, -, hPI, hB⟩ := hMod
  obtain ⟨b, hb⟩ := hB Tc alg _ ho
  letI := alg.toAlgebra
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF Tc alg Y hPI b hb y₀
  obtain ⟨p, φ', y', hm⟩ := hT Z
  have hm2 : FrMap (ψ.comp φ') y' y₀ := frMap_trans _ _ _ φ' ψ y' (genFr hG Z) y₀ hm hψ
  have hy₀T : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) y₀ :=
    ⟨p, ψ.comp φ', y', hm2⟩
  have hW : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      evI y (F : T.R j) = wchar (ex (T.Q.Dw j) (wtA w) w.n) t * evR (T.Q.Xo j) T.Q.c (F : T.R j) y₀ := fun w F =>
    hWt (wtA w) w.n (F : T.R j) (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)) Tc.Fr t y₀ y.1 hy₀T y.2.1 hbor
  let χ : (recPlus h j hj).Forms →+* Tc.Fr := chiI j y
  let ev : Rp (recPlus h j hj) la G.N →+* Tc.Fr := evRp la G.N kap χ (fun a f => by
    have e := chiI_smul j y a f
    rw [halg a] at e
    exact e)
  have hev_k : ∀ c : Kp (recPlus h j hj) la G.N, ev (algebraMap _ (Rp (recPlus h j hj) la G.N) c) = kap c :=
    evRp_alg la G.N kap χ _
  have hev_inc : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      ev (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc w F)) = evI y (F : T.R j) := by
    intro w F
    exact (evRp_emb la G.N kap χ _ ((recPlus h j hj).inc w F)).trans (chiI_inc j h y w F)
  have hev_sec : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) =
      ∑ k, kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) *
        evI y ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) := by
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hev_k, hev_inc]
  have hs0' : (∑ k, kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) *
      evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀) ≠ 0 := hs0
  have hev_s0 : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) = wchar (ex (T.Q.Dw j) (wtA wL) wL.n) t *
      ∑ k, kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) *
        evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀ := by
    rw [hev_sec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hW wL (G.w k)]
    ring
  have hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0)) :=
    IsUnit.mk0 _ (by rw [hev_s0]; exact mul_ne_zero (wchar_ne_zero _ _) hs0')
  let yV : PtV (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho y trivial () trivial
  let yP : (extAll h j hj).Pt' la := ⟨vAtV yV, yV, rfl⟩
  refine ⟨yP, Tc, ι, hloc, hunr, ev, hu, ?_, ?_, ?_⟩
  · intro w F
    rw [extAll_vAt_inc]
    show vAtV yV (F : T.R j) = _
    exact congrArg (nval Tc.V (ep (unifO (recPlus h j hj) la G.N) ζ)) (hev_inc w F).symm
  · intro x
    obtain ⟨k, ⟨g, hg⟩, rfl⟩ := exists_weightZero_fraction_eq _ _ _ x
    rw [coe_weightZeroFraction, liftEv_frac]
    have key : ∀ (g : Rp (recPlus h j hj) la G.N) (hg : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k))
        (hg' : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k)),
        ev g * (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))⁻¹ ^ k =
          phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr)
            (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨g, hg'⟩)) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg0 =>
        intro hg'
        obtain ⟨F, rfl⟩ := hg0
        have hr := hrat k F
        have hr' : phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr) (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k
            ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ F), hg'⟩)) =
            evR (T.Q.Xo j) T.Q.c ((F : T.R j)) y₀ /
              (∑ k', kap (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k'))) *
                evR (T.Q.Xo j) T.Q.c ((G.w k' : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀) ^ k := hr
        rw [hr', hev_inc, hW, ex_addL, wchar_nsmul, hev_s0]
        exact mul_ringHom_units_ratio (wchar_ne_zero (ex (T.Q.Dw j) (wtA wL) wL.n) t) k
      | zero =>
        intro hg'
        have e0 : fr0 (recPlus h j hj) la G.w k ⟨0, hg'⟩ = 0 := Subtype.ext (by rw [coe_weightZeroFraction]; exact map_zero _)
        rw [e0, map_zero, map_zero, map_zero, zero_mul]
      | add a b ha hb iha ihb =>
        intro hg'
        have e1 : fr0 (recPlus h j hj) la G.w k ⟨a + b, hg'⟩ =
            fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩ + fr0 (recPlus h j hj) la G.w k ⟨b, hb⟩ :=
          Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_add, coe_weightZeroFraction, coe_weightZeroFraction]; exact map_add _ _ _)
        rw [e1, map_add (toOsK (recPlus h j hj) la G.w), map_add (phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr)),
          map_add ev, add_mul, iha ha, ihb hb]
      | smul c a ha iha =>
        intro hg'
        have e1 : fr0 (recPlus h j hj) la G.w k ⟨c • a, hg'⟩ = c • fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩ :=
          Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_smul, coe_weightZeroFraction]; exact map_smul _ _ _)
        rw [e1, map_smul (toOsK (recPlus h j hj) la G.w) c,
          Algebra.smul_def c (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩)),
          map_mul, ← iha ha, Algebra.smul_def c a, map_mul, hev_k, mul_assoc]
        rfl
    exact key g hg hg
  · intro w F hNZ
    rw [show ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = evI y (F : T.R j) from hev_inc w F, hW w F]
    refine mul_ne_zero (wchar_ne_zero _ _) ?_
    have hnat := (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)).1
    rw [evR_eq_of_map hWD hnat y₀ p (ψ.comp φ') y' hm2, AlgHom.comp_apply]
    have h2 : evC hG Z (F : T.R j) = φ' ((F : T.R j) p y') := evR_eq_of_map hWD hnat (genFr hG Z) p φ' y' hm
    rw [← h2]
    exact (map_ne_zero_iff _ ψ.toRingHom.injective).2 (hNZ Z)

end Formalism.L2.Pj
