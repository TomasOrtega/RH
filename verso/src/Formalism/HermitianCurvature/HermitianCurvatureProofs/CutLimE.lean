import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGerm

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [D.positionted, List.map_ofFn]`. Conclude with `List.nodup_ofFn.mpr (fun a b h => h)`. Introduce `l hl`. Simplify using `only [D.positionted, List.mem_ofFn] at hl`.

Take `⟨a, rfl⟩` from `hl`. Simplify using `[Complex.conj_ofReal]`. Rewrite using `[D.positionted, List.pairwise_ofFn]`. Introduce `a b hab`. Establish `key : ∀ u v : ℝ, 2 < |u - v| → ((u : ℂ) - v ≠ 1 ∧ (v : ℂ) - u ≠ 1)`.

Introduce `u v huv`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `congrArg Complex.re h`. Simplify using `only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at h'`.

Rewrite `huv` using `[h']`. Evaluate the numerical expressions using `at huv`. Introduce `h`. Establish `h'` using `congrArg Complex.re h`. Simplify using `only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at h'`.

Rewrite `huv` using `[abs_sub_comm, h']`. Evaluate the numerical expressions using `at huv`. Take `⟨k1, k2⟩` from `key _ _ (hw.2 a b (ne_of_lt hab))`. Simplify using `only [Wd.RegL]`. Use `split_ifs`.

Conclude with `k1`. Conclude with `k2`.
-/
theorem good_positioned_of_cut {P : M.Par} {l0 : ℕ} {w : List C.Letter} (hw : KB.CutWord P l0 w) :
    Wd.Good (D.positionted w) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [D.positionted, List.map_ofFn]
    exact List.nodup_ofFn.mpr (fun a b h => h)
  · intro l hl
    simp only [D.positionted, List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    simp [Complex.conj_ofReal]
  · rw [D.positionted, List.pairwise_ofFn]
    intro a b hab
    have key : ∀ u v : ℝ, 2 < |u - v| → ((u : ℂ) - v ≠ 1 ∧ (v : ℂ) - u ≠ 1) := by
      intro u v huv
      constructor
      · intro h
        have h' := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at h'
        rw [h'] at huv
        norm_num at huv
      · intro h
        have h' := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at h'
        rw [abs_sub_comm, h'] at huv
        norm_num at huv
    obtain ⟨k1, k2⟩ := key _ _ (hw.2 a b (ne_of_lt hab))
    simp only [Wd.RegL]
    split_ifs
    · exact k1
    · exact k2

/- English proof (translation)
The claim follows from `| [], _, _, h, x, hx => h x hx | a :: L, f, f₂, h, x, hx => by simp only [List.foldr_cons] have ih := foldCV_congr s L f f₂ h exact (Formalism.FourierDecayAlt.P.Dx1.LZ.good_Tc (k := k) (r := r) (E := E) s (a.2 : ℂ)).loc _ _ (fun y hy => ih y hy.1.1) x (Formalism.FourierDecayAlt.P …`.
-/
theorem foldCV_congr {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) :
    ∀ (L : List (Bool × ℝ)) (f f₂ : B.Mat k r → E), (∀ x ∈ B.GV k r, f x = f₂ x) →
      ∀ x ∈ B.GV k r, L.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) f x =
        L.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) f₂ x
  | [], _, _, h, x, hx => h x hx
  | a :: L, f, f₂, h, x, hx => by
    simp only [List.foldr_cons]
    have ih := foldCV_congr s L f f₂ h
    exact (Formalism.FourierDecayAlt.P.Dx1.LZ.good_Tc (k := k) (r := r) (E := E) s (a.2 : ℂ)).loc _ _
      (fun y hy => ih y hy.1.1) x (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hx)

section betaR

open Formalism.FourierDecayAlt.B

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Unfold `B.beta betaBig`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq Bs)] with q hq`. Distinguish the cases in `hQ : q ∈ B.Qset Bs`. Establish `hg : bigCell k r q.1 (Bs.μsec q.2) ∈ GV k r` using `(hq hQ).1 show (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * inner ℂ (hsVec (JF Bs G (bigCell k r q.1 (Bs.μsec q.2)))) (hsVec (JF Bs F (bigCell k r q.1 (Bs.μsec q.2)))) = (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * inner ℂ (hsVec (JF Bs G₂ (bigCell k r q.1 (Bs.μsec …`.

Rewrite using `[Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr Bs h hg]`. Establish `hw : bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q = 0` using `le_antisymm (not_lt.1 hQ) (Formalism.FourierDecayAlt.P.JCx2.sq_bcWeight_nonneg _ _ q) show (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * _ = (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * _`. Rewrite using `[hw]`. Simplify using the standard rewrite rules.
-/
theorem beta_congr_right (Bs : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, G g = G₂ g) : beta Bs F G = beta Bs F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq Bs)] with q hq
  by_cases hQ : q ∈ B.Qset Bs
  · have hg : bigCell k r q.1 (Bs.μsec q.2) ∈ GV k r := (hq hQ).1
    show (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * inner ℂ (hsVec (JF Bs G (bigCell k r q.1 (Bs.μsec q.2))))
        (hsVec (JF Bs F (bigCell k r q.1 (Bs.μsec q.2)))) =
      (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * inner ℂ (hsVec (JF Bs G₂ (bigCell k r q.1 (Bs.μsec q.2))))
        (hsVec (JF Bs F (bigCell k r q.1 (Bs.μsec q.2))))
    rw [Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr Bs h hg]
  · have hw : bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (Formalism.FourierDecayAlt.P.JCx2.sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * _ = (bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q : ℂ) * _
    rw [hw]
    simp

end betaR

/- English proof (translation)
Unfold `KB.Pl.RR`. Rewrite using `[Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hF (good_positioned_of_cut hw), Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hF₂ (good_positioned_of_cut hw)]`. Unfold `C7.principalHermitianLattice`. Rewrite using `[Formalism.FourierDecayAlt.P.JCx2.sq_beta_congr _ (foldCV_congr _ w F F₂ h), beta_congr_right _ h]`.
-/
theorem residual_pairing_congr_on_group {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (hF₂ : B.CkOn ⊤ (B.GV P.k P.r) F₂)
    (h : ∀ g ∈ B.GV P.k P.r, F g = F₂ g) {w : List C.Letter} (hw : KB.CutWord P p.l0 w) :
    p.RR F 0 w [] [] = p.RR F₂ 0 w [] [] := by
  unfold KB.Pl.RR
  rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hF (good_positioned_of_cut hw),
    Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hF₂ (good_positioned_of_cut hw)]
  unfold C7.principalHermitianLattice
  rw [Formalism.FourierDecayAlt.P.JCx2.sq_beta_congr _ (foldCV_congr _ w F F₂ h), beta_congr_right _ h]

/- English proof (translation)
Introduce `g hg`. Simplify using `only [D.cutF]`. Distinguish the cases in `hF : F g = 0`. Rewrite using `[hF, smul_zero]`. Establish `h1 : 1 ≤ Gf k r Bs.z Bs.z' g / ε`.

Rewrite using `[le_div_iff₀ hε]`. Combine the linear relations using `[hG g hg hF]`. Rewrite using `[hχ.2.2 _ h1]`. Simplify using the standard rewrite rules.
-/
theorem cutF_eq_on_gv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} {δ : ℝ} (hG : ∀ g ∈ B.GV k r, F g ≠ 0 → δ ≤ Gf k r Bs.z Bs.z' g) {ε : ℝ}
    (hε : 0 < ε) (hεδ : ε ≤ δ) : ∀ g ∈ B.GV k r, D.cutF Bs χ F ε g = F g := by
  intro g hg
  simp only [D.cutF]
  by_cases hF : F g = 0
  · rw [hF, smul_zero]
  · have h1 : 1 ≤ Gf k r Bs.z Bs.z' g / ε := by
      rw [le_div_iff₀ hε]
      linarith [hG g hg hF]
    rw [hχ.2.2 _ h1]
    simp

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def LimEv (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re = (p.RR F 0 w [] []).re

def LimPos (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → 0 ≤ (p.RR F 0 w [] []).re

def LimBd (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    (p.RR F 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re

/- English proof (translation)
Introduce `w hw _`. Take `⟨hCk, _, δ, hδ, hG⟩` from `hF`. Use `filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε`. Rewrite using `[residual_pairing_congr_on_group p (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hCk ε) hCk (cutF_eq_on_gv p.T.base hχ hG hε.1 hε.2.le) hw.1]`.
-/
theorem truncated_limit_evaluation_holds (p : KB.Pl P Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) (Y : Finset ℝ) (N : ℕ) : LimEv p χ F Y N := by
  intro w hw _
  obtain ⟨hCk, _, δ, hδ, hG⟩ := hF
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  rw [residual_pairing_congr_on_group p (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hCk ε) hCk
    (cutF_eq_on_gv p.T.base hχ hG hε.1 hε.2.le) hw.1]

/- English proof (translation)
Introduce `w hw _`. Establish `hh : D.IsLocPt ([] : C.LPt) 0` using `⟨by simp, rfl⟩`. Rewrite using `[PBL.rr_eq_form p F 0 (Nat.zero_le _) w [] [] hh hh]`. Take `⟨ε, hε, hnv⟩` from `PBL.slv_nv p hF 0 (Nat.zero_le _) w [] hh`. Conclude with `Formalism.FourierDecayAlt.P.TBBx5.form_re_nonneg p (Formalism.FourierDecayAlt.P.TBBx5.formNonneg_of hA (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p) 0 (Nat.zero_le _) w hw.1 hε _ hnv`.
-/
theorem truncated_limit_positivity_holds (hA : P5.ThmPActual) (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) (Y : Finset ℝ) (N : ℕ) : LimPos p F Y N := by
  intro w hw _
  have hh : D.IsLocPt ([] : C.LPt) 0 := ⟨by simp, rfl⟩
  rw [PBL.rr_eq_form p F 0 (Nat.zero_le _) w [] [] hh hh]
  obtain ⟨ε, hε, hnv⟩ := PBL.slv_nv p hF 0 (Nat.zero_le _) w [] hh
  exact Formalism.FourierDecayAlt.P.TBBx5.form_re_nonneg p
    (Formalism.FourierDecayAlt.P.TBBx5.formNonneg_of hA (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p) 0 (Nat.zero_le _) w hw.1 hε _ hnv

/- English proof (translation)
Introduce `w hw hl`. Establish `hE` using `hEv w hw hl`. Establish `hP` using `hPos w hw hl`. Establish `hB` using `hBd w hw hl`. Establish `hN : 0 ≤ TBB.normC nn w`.

Unfold `TBB.normC`. Conclude with `List.prod_nonneg (fun x hx => by`. Take `⟨l, _, rfl⟩` from `List.mem_map.1 hx`. Conclude with `hnn _)`. Distinguish the cases in `hb : 0 < (B.beta p.T.base F F).re`.

Use `⟨(p.RR F 0 w [] []).re / (B.beta p.T.base F F).re, div_nonneg hP hb.le, (div_le_iff₀ hb).2 hB, ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_cancel₀ _ hb.ne']`. Use `Filter.Tendsto.congr' ?_ tendsto_const_nhds` and prove the remaining obligations. Conclude with `hE.mono fun ε h => h.symm`. Establish `hb' : (B.beta p.T.base F F).re ≤ 0` using `not_lt.1 hb`.

Establish `hR0 : (p.RR F 0 w [] []).re = 0` using `le_antisymm (hB.trans (mul_nonpos_of_nonneg_of_nonpos hN hb')) hP`. Use `⟨0, le_refl 0, hN, ?_⟩` and prove the remaining obligations. Rewrite using `[zero_mul]`. Use `Filter.Tendsto.congr' ?_ tendsto_const_nhds` and prove the remaining obligations. Conclude with `hE.mono fun ε h => (h.trans hR0).symm`.
-/
theorem limE_of_parts (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y) (hEv : LimEv p χ F Y N) (hPos : LimPos p F Y N)
    (hBd : LimBd p nn F Y N) : LimE p nn χ F Y N := by
  intro w hw hl
  have hE := hEv w hw hl
  have hP := hPos w hw hl
  have hB := hBd w hw hl
  have hN : 0 ≤ TBB.normC nn w := by
    unfold TBB.normC
    exact List.prod_nonneg (fun x hx => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
      exact hnn _)
  by_cases hb : 0 < (B.beta p.T.base F F).re
  · refine ⟨(p.RR F 0 w [] []).re / (B.beta p.T.base F F).re, div_nonneg hP hb.le, (div_le_iff₀ hb).2 hB, ?_⟩
    rw [div_mul_cancel₀ _ hb.ne']
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    exact hE.mono fun ε h => h.symm
  · have hb' : (B.beta p.T.base F F).re ≤ 0 := not_lt.1 hb
    have hR0 : (p.RR F 0 w [] []).re = 0 :=
      le_antisymm (hB.trans (mul_nonpos_of_nonneg_of_nonpos hN hb')) hP
    refine ⟨0, le_refl 0, hN, ?_⟩
    rw [zero_mul]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    exact hE.mono fun ε h => (h.trans hR0).symm

/- English proof (translation)
The claim follows from `limE_of_parts p nn χ F Y N hnn (truncated_limit_evaluation_holds p hχ hF Y N) (truncated_limit_positivity_holds hA p hF Y N) hBd`.
-/
theorem truncated_limit_equality_holds (hA : P5.ThmPActual) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y)
    (hF : KB.CptCoef p.T.base F) (hBd : LimBd p nn F Y N) : LimE p nn χ F Y N :=
  limE_of_parts p nn χ F Y N hnn (truncated_limit_evaluation_holds p hχ hF Y N) (truncated_limit_positivity_holds hA p hF Y N) hBd

end place

/- English proof (translation)
Take `⟨C₄, hC₄⟩` from `thmBpAt_of_leaves' hA C₃ CΛ C₀ Cκ hC₃ hCΛ hC₀`. Use `⟨C₄, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26`. Conclude with `hC₄ Wp Wq P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 (truncated_limit_equality_holds hA p nn h11 _ Y N (fun y => (h12 y).le) (cptCoef_fpm_of p p₀ h14 h15) h23) (truncated_limit_equality_holds hA …`.
-/
theorem thmBpAt_of_leaves_limBd (hA : P5.ThmPActual) (C₃ CΛ C₀ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
      (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b Λ κ₀ : ℝ) (n₀ p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ)
      (Cb : ℝ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ TBB.Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base f →
      B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      Amaps p f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      GermCutPD p nn χ (TBBx4.fpm p f Ap p₀) Y K N → GermCutPD p nn χ (TBBx4.fpm p f Am p₀) Y K N →
      LimBd p nn (TBBx4.fpm p f Ap p₀) Y N → LimBd p nn (TBBx4.fpm p f Am p₀) Y N →
      LemB p (TBBx4.fpm p f Ap p₀) κ₀ → LemB p (TBBx4.fpm p f Am p₀) κ₀ →
      TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₄, hC₄⟩ := thmBpAt_of_leaves' hA C₃ CΛ C₀ Cκ hC₃ hCΛ hC₀
  refine ⟨C₄, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26
  exact hC₄ Wp Wq P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    (truncated_limit_equality_holds hA p nn h11 _ Y N (fun y => (h12 y).le) (cptCoef_fpm_of p p₀ h14 h15) h23)
    (truncated_limit_equality_holds hA p nn h11 _ Y N (fun y => (h12 y).le) (cptCoef_fpm_of p p₀ h14 h16) h24) h25 h26

end

end Formalism.FourierDecayAlt.P.CutBP
