import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGermW

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

namespace GLG

/- English proof (translation)
Distinguish the cases in `hl : D.IsLocPt a i ∧ D.IsLocPt b i`. Unfold `KB.Pl.RR D.RRplace`. Rewrite using `[dif_pos hl, dif_pos hl, dif_pos hi, dif_pos hi]`. Establish `hU : ∀ (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV P.k P.r, D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e g = D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e g` using `fun e g hg => (Formalism.FourierDecayAlt.P.CutEXUw.uwG_congrG p.T.base.z p.T.base.z' i hi isOpen_univ (fun x _ hx => (hE x hx).symm) w e g (Set.mem_univ _) hg)`. Establish `hS : ∀ (q : C.LPt), D.IsLocPt q i → ∀ (e : Wd.Ix (Fin w.length)), ∀ γ ∈ B.GV P.k (P.r - D.ptSize q), D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e) q γ = D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ …`.

Introduce `q hq e γ hγ`. Establish `h1` using `Formalism.FourierDecayAlt.P.PBG.sliceAt_lincomb P.k P.r Wp Wq p.T F hF i hi hi1 q hq ({()} : Finset Unit) (fun _ => 1) (fun _ => w) (fun _ => e) (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e) (fun g hg _ => by simp [hU e g hg]) γ hγ`. Simplify using `only [Finset.sum_singleton, one_smul] at h1`. Conclude with `h1.symm`. Use `Formalism.FourierDecayAlt.P.PBG.formLev_congrGV p.T _ _ w _ _ _ _ (fun e g hg => ?_) (fun e g hg => ?_)` and prove the remaining obligations.

Simplify using `only [D.castF]`. Conclude with `hS a hl.1 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)`. Simplify using `only [D.castF]`. Conclude with `hS b hl.2 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)`. Rewrite using `[PBL.rr_zero_of_not p F i w a b hl, PBL.rr_zero_of_not p F₂ i w a b hl]`.
-/
theorem rr_congr_belowG {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F)
    (hE : ∀ g ∈ B.GV P.k P.r, F g = F₂ g) (i : ℕ) (hi : i ≤ P.r) (hi1 : 1 ≤ i) (w : List C.Letter)
    (a b : C.LPt) : p.RR F i w a b = p.RR F₂ i w a b := by
  by_cases hl : D.IsLocPt a i ∧ D.IsLocPt b i
  · unfold KB.Pl.RR D.RRplace
    rw [dif_pos hl, dif_pos hl, dif_pos hi, dif_pos hi]
    have hU : ∀ (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV P.k P.r,
        D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e g = D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e g :=
      fun e g hg => (Formalism.FourierDecayAlt.P.CutEXUw.uwG_congrG p.T.base.z p.T.base.z' i hi isOpen_univ
        (fun x _ hx => (hE x hx).symm) w e g (Set.mem_univ _) hg)
    have hS : ∀ (q : C.LPt), D.IsLocPt q i → ∀ (e : Wd.Ix (Fin w.length)),
        ∀ γ ∈ B.GV P.k (P.r - D.ptSize q),
        D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e) q γ =
          D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e) q γ := by
      intro q hq e γ hγ
      have h1 := Formalism.FourierDecayAlt.P.PBG.sliceAt_lincomb P.k P.r Wp Wq p.T F hF i hi hi1 q hq ({()} : Finset Unit)
        (fun _ => 1) (fun _ => w) (fun _ => e) (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e)
        (fun g hg _ => by simp [hU e g hg]) γ hγ
      simp only [Finset.sum_singleton, one_smul] at h1
      exact h1.symm
    refine Formalism.FourierDecayAlt.P.PBG.formLev_congrGV p.T _ _ w _ _ _ _ (fun e g hg => ?_) (fun e g hg => ?_)
    · simp only [D.castF]
      exact hS a hl.1 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
    · simp only [D.castF]
      exact hS b hl.2 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
  · rw [PBL.rr_zero_of_not p F i w a b hl, PBL.rr_zero_of_not p F₂ i w a b hl]

def PP (m : ℕ) (h : C.LPt) (x Dv : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * Dv)]
  | some z => h ++ [(m + 2, z)]

def qG (m : ℕ) (x Dv : ℂ) : Option ℂ → (ℂ × ℂ) ⊕ ℂ
  | none => Sum.inl (x⁻¹, x ^ (m + 1) * Dv)
  | some z => Sum.inr z

/- English proof (translation)
Apply the tactic sequence `cases j <;> rfl`.
-/
theorem PP_eq (m : ℕ) (h : C.LPt) (x Dv : ℂ) (j : Option ℂ) : PP m h x Dv j = FormNormSumIdentities.ptG h m (qG m x Dv j) := by
  cases j <;> rfl

/- English proof (translation)
The claim follows from `FormNormSumIdentities.mem_rootSet4 (by omega)`.
-/
theorem mem_root {m : ℕ} {a z : ℂ} : z ∈ G.rootSet (m + 2) a ↔ z ^ (m + 2) = a :=
  FormNormSumIdentities.mem_rootSet4 (by omega)

/- English proof (translation)
Take `⟨hloc, hsz⟩` from `hh`. Consider the cases of `j with`. Consider the case `none`. Use `⟨fun y hy => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [PP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy`.

Break down `hy with hy | rfl | rfl` into its components or cases. Conclude with `hloc y hy`. Conclude with `⟨by omega, inv_ne_zero hx⟩`. Conclude with `⟨le_rfl, mul_ne_zero (pow_ne_zero _ hx) hD⟩`. Simplify using `[PP, D.ptSize, List.map_append, List.sum_append] at hsz ⊢`.

Use linear arithmetic over natural numbers and integers. Consider the case `some z`. Establish `hj' : z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)` using `Finset.mem_insertNone.1 hj z rfl`. Establish `hz` using `mem_root.1 hj'`. Establish `hz0 : z ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow (by omega)]`. Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) hD hz.symm`. Use `⟨fun y hy => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [PP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy`.

Break down `hy with hy | rfl` into its components or cases. Conclude with `hloc y hy`. Conclude with `⟨by omega, hz0⟩`. Simplify using `[PP, D.ptSize, List.map_append, List.sum_append] at hsz ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem isLocPt_PP (m : ℕ) (b : ℕ) (hb : 1 ≤ b) (h : C.LPt) (hh : D.IsLocPt h (b - 1)) (x Dv : ℂ) (hx : x ≠ 0)
    (hD : Dv ≠ 0) (j : Option ℂ) (hj : j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv))) :
    D.IsLocPt (PP m h x Dv j) (b + (m + 2) - 1) := by
  obtain ⟨hloc, hsz⟩ := hh
  cases j with
  | none =>
    refine ⟨fun y hy => ?_, ?_⟩
    · simp only [PP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | rfl | rfl
      · exact hloc y hy
      · exact ⟨by omega, inv_ne_zero hx⟩
      · exact ⟨le_rfl, mul_ne_zero (pow_ne_zero _ hx) hD⟩
    · simp [PP, D.ptSize, List.map_append, List.sum_append] at hsz ⊢; omega
  | some z =>
    have hj' : z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv) := Finset.mem_insertNone.1 hj z rfl
    have hz := mem_root.1 hj'
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hD hz.symm
    refine ⟨fun y hy => ?_, ?_⟩
    · simp only [PP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | rfl
      · exact hloc y hy
      · exact ⟨by omega, hz0⟩
    · simp [PP, D.ptSize, List.map_append, List.sum_append] at hsz ⊢; omega

/- English proof (translation)
Consider the cases of `j with`. Consider the case `none`. Use `⟨inv_ne_zero hx, ?_⟩` and prove the remaining obligations. Establish `e : x ^ (m + 1) * Dv * x⁻¹ ^ (m + 1) = Dv` using `by rw [inv_pow]; field_simp`. Use `show x ^ (m + 1) * Dv * x⁻¹ ^ (m + 1) ∈ K`.

Rewrite using `[e]`. Conclude with `hD`. Consider the case `some z`. Establish `hj' : z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)` using `Finset.mem_insertNone.1 hj z rfl`. Conclude with `⟨Dv, hD, mem_root.1 hj'⟩`.
-/
theorem okG_qG (m : ℕ) (K : Set ℂ) (x Dv : ℂ) (hx : x ≠ 0) (hD : Dv ∈ K) (j : Option ℂ)
    (hj : j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv))) : FormNormSumIdentities.okG m K (qG m x Dv j) := by
  cases j with
  | none =>
    refine ⟨inv_ne_zero hx, ?_⟩
    have e : x ^ (m + 1) * Dv * x⁻¹ ^ (m + 1) = Dv := by rw [inv_pow]; field_simp
    show x ^ (m + 1) * Dv * x⁻¹ ^ (m + 1) ∈ K
    rw [e]; exact hD
  | some z =>
    have hj' : z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv) := Finset.mem_insertNone.1 hj z rfl
    exact ⟨Dv, hD, mem_root.1 hj'⟩

end GLG

namespace GLG

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Unfold `KB.Pl.RR D.RRplace`. Rewrite using `[dif_pos ⟨ha, hb⟩, dif_pos hi]`. Both sides reduce to the same expression.
-/
theorem rr_eq_formLev (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (hi : i ≤ P.r)
    (w : List C.Letter) (a b : C.LPt) (ha : D.IsLocPt a i) (hb : D.IsLocPt b i) :
    p.RR F i w a b = D.formLev p.T (M.sgn P p.l0) ⟨i, by omega⟩ w (KB.slv p.T F i hi w a ha.2)
      (KB.slv p.T F i hi w b hb.2) := by
  unfold KB.Pl.RR D.RRplace
  rw [dif_pos ⟨ha, hb⟩, dif_pos hi]
  rfl

def lam (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (w : List C.Letter) (a : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) a) / √(TBB.normC nn w)

/- English proof (translation)
Unfold `TBB.normC`. Use `List.prod_pos fun x hx => ?_` and prove the remaining obligations. Take `⟨l, _, rfl⟩` from `List.mem_map.1 hx`. Conclude with `hnn _`.
-/
theorem normC_pos (nn : ℝ → ℝ) (hnn : ∀ y, 0 < nn y) (w : List C.Letter) : 0 < TBB.normC nn w := by
  unfold TBB.normC
  refine List.prod_pos fun x hx => ?_
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
  exact hnn _

/- English proof (translation)
Unfold `TBB.NP lam`. Use `congr 2`. Establish `hc` using `normC_pos nn hnn w`. Rewrite using `[div_mul_div_comm, Real.mul_self_sqrt hc.le]`.
-/
theorem np_eq_lam (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (hnn : ∀ y, 0 < nn y) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (i : ℕ) (w : List C.Letter) (a b : C.LPt) :
    TBB.NP p nn F i w a b = ((lam p nn w a * lam p nn w b : ℝ) : ℂ) * p.RR F i w a b := by
  unfold TBB.NP lam
  congr 2
  have hc := normC_pos nn hnn w
  rw [div_mul_div_comm, Real.mul_self_sqrt hc.le]

/- English proof (translation)
Introduce `j hj l hl`. Establish `hPj` using `isLocPt_PP m b hb h hh x Dv hx hD j hj`. Establish `hPl` using `isLocPt_PP m b hb h hh x Dv hx hD l hl`. Rewrite using `[np_eq_lam p nn hnn, hRR, rr_eq_formLev p F' _ hi w _ _ hPj hPl, FormNormSumIdentities.slv_congr _ _ _ _ _ (PP_eq m h x Dv j) _ (by rw [FormNormSumIdentities.ptSize_ptG, hsz]), FormNormSumIdentities.slv_congr _ _ _ _ _ (PP_eq m h x Dv l) _ (by rw [FormNormSumIdentities.ptSize_ptG …`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Complex.conj_ofReal]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem np_PP (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (hnn : ∀ y, 0 < nn y) (F F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (w : List C.Letter) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r)
    (hRR : ∀ a a', p.RR F (b + (m + 2) - 1) w a a' = p.RR F' (b + (m + 2) - 1) w a a')
    (h : C.LPt) (hh : D.IsLocPt h (b - 1)) (hsz : D.ptSize h + (m + 2) = b + (m + 2) - 1)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : G.Mat (m + 2) → V)
    (K : Set ℂ)
    (hker : ∀ q1 q2, FormNormSumIdentities.okG m K q1 → FormNormSumIdentities.okG m K q2 →
      D.formLev p.T (M.sgn P p.l0) ⟨b + (m + 2) - 1, by omega⟩ w
        (KB.slv p.T F' (b + (m + 2) - 1) hi w (FormNormSumIdentities.ptG h m q1) (by rw [FormNormSumIdentities.ptSize_ptG, hsz]))
        (KB.slv p.T F' (b + (m + 2) - 1) hi w (FormNormSumIdentities.ptG h m q2) (by rw [FormNormSumIdentities.ptSize_ptG, hsz])) =
      Bf (FormNormSumIdentities.yG U.betaU m Φ q1) (FormNormSumIdentities.yG U.betaU m Φ q2))
    (x Dv : ℂ) (hx : x ≠ 0) (hDK : Dv ∈ K) (hD : Dv ≠ 0) :
    ∀ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)),
    ∀ l ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)),
      TBB.NP p nn F (b + (m + 2) - 1) w (PP m h x Dv j) (PP m h x Dv l) =
        Bf (((lam p nn w (PP m h x Dv j) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qG m x Dv j))
          (((lam p nn w (PP m h x Dv l) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qG m x Dv l)) := by
  intro j hj l hl
  have hPj := isLocPt_PP m b hb h hh x Dv hx hD j hj
  have hPl := isLocPt_PP m b hb h hh x Dv hx hD l hl
  rw [np_eq_lam p nn hnn, hRR, rr_eq_formLev p F' _ hi w _ _ hPj hPl,
    FormNormSumIdentities.slv_congr _ _ _ _ _ (PP_eq m h x Dv j) _ (by rw [FormNormSumIdentities.ptSize_ptG, hsz]),
    FormNormSumIdentities.slv_congr _ _ _ _ _ (PP_eq m h x Dv l) _ (by rw [FormNormSumIdentities.ptSize_ptG, hsz]),
    hker _ _ (okG_qG m K x Dv hx hDK j hj) (okG_qG m K x Dv hx hDK l hl)]
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Complex.conj_ofReal]
  push_cast
  ring

end GLG

namespace GLG

def aC (m : ℕ) (x : ℂ) : Option ℂ → ℂ
  | none => (((Real.pi ^ (m + 1))⁻¹ * ‖x‖ ^ (m + 1) : ℝ) : ℂ)
  | some z => -(G.psi (-U.betaU) (((m + 2 : ℕ) : ℂ) * z * x) * (((((m + 2 : ℕ) : ℝ) * ‖z‖ ^ (m + 1))⁻¹ : ℝ) : ℂ))

/- English proof (translation)
Establish `e : G.psi (-β) w = G.psi β (-w)` using `by unfold G.psi; congr 1; simp [neg_mul, mul_neg]`. Rewrite using `[e, FormNormSumIdentities.psi_conj, neg_neg]`.
-/
theorem psi_neg_conj (β w : ℂ) : conj (G.psi (-β) w) = G.psi β w := by
  have e : G.psi (-β) w = G.psi β (-w) := by unfold G.psi; congr 1; simp [neg_mul, mul_neg]
  rw [e, FormNormSumIdentities.psi_conj, neg_neg]

/- English proof (translation)
Unfold `FormNormSumIdentities.kapB`. Rewrite using `[← pow_add]`. Use `congr 1`. Establish `e : (m + 1) * (m + 4) = (m + 2) * (m + 1) + 2 * (m + 1)` using `by ring`. Rewrite using `[e, Nat.add_mul_div_left _ _ two_pos]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem kapB_eq (m : ℕ) : FormNormSumIdentities.kapB m = Real.pi ^ (m + 1) * Real.pi ^ ((m + 2) * (m + 1) / 2) := by
  unfold FormNormSumIdentities.kapB
  rw [← pow_add]
  congr 1
  have e : (m + 1) * (m + 4) = (m + 2) * (m + 1) + 2 * (m + 1) := by ring
  rw [e, Nat.add_mul_div_left _ _ two_pos]
  omega

/- English proof (translation)
Take `⟨M', rfl⟩ : ∃ M', M = M' + 2` from `⟨M - 2, by omega⟩`. Establish `eM1 : M' + 2 - 2 = M'` using `by omega`. Establish `eM2 : M' + 2 + m - 1 = M' + m + 1` using `by omega`. Rewrite `h1` using `[eM1]`. Rewrite `h2` using `[eM2]`.

Establish `hpi : (0 : ℝ) < Real.pi` using `Real.pi_pos`. Establish `hxn : (0 : ℝ) < ‖x‖` using `norm_pos_iff.mpr hx`. Rewrite using `[Finset.sum_insertNone, smul_sub, sub_eq_add_neg]`. Use `congr 1`. Use `show conj (aC m x none) • (((lam none : ℝ) : ℂ) • (((FormNormSumIdentities.kapB m : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Φ x⁻¹ (x ^ (m + 1) * Dv))) = _`.

Unfold `U.uD`. Establish `hc : Dv / x⁻¹ ^ (m + 1) = x ^ (m + 1) * Dv` using `by rw [inv_pow]; field_simp`. Rewrite using `[hc, eM1]`. Simplify using `only [aC, Complex.conj_ofReal, smul_smul, ← Complex.ofReal_mul]`. Use `congr 2`.

Rewrite using `[h1, kapB_eq, norm_inv]`. Simplify using `only [inv_pow, inv_inv]`. Clear the denominators using the available nonvanishing facts. Unfold `U.aD G.mainTerm`. Rewrite using `[eM1, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun z hz => ?_` and prove the remaining obligations. Establish `hz'` using `mem_root.1 hz`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz'` using `[zero_pow (by omega)]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) hD hz'.symm`. Establish `hzn : (0 : ℝ) < ‖z‖` using `norm_pos_iff.mpr hz0`. Establish `hDn : ‖Dv‖ = ‖z‖ ^ (m + 2)`. Rewrite using `[← norm_pow, hz', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Simplify using `only [aC, qG, FormNormSumIdentities.yG, smul_smul, ← neg_smul]`.

Use `congr 1`. Rewrite using `[map_neg, map_mul, psi_neg_conj, Complex.conj_ofReal, h2 z hz, hDn]`. Establish `hψ : ((m : ℂ) + 2) * z / x⁻¹ = ((m + 2 : ℕ) : ℂ) * z * x` using `by push_cast; field_simp`. Rewrite using `[hψ]`. Establish `hz1 : ((‖z‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hzn.ne'`.

Establish `hm2 : (m : ℂ) + 2 ≠ 0` using `by exact_mod_cast (show (m + 2 : ℕ) ≠ 0 by omega)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conjSum_TBB {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (m M : ℕ) (hM : 2 ≤ M)
    (Φ : G.Mat (m + 2) → V) (x Dv : ℂ) (hx : x ≠ 0) (hD : Dv ≠ 0) (μ0 : ℝ) (lam : Option ℂ → ℝ)
    (h1 : lam none = μ0 * ((‖x⁻¹‖ ^ ((m + 1) * (M + m))) * ‖x ^ (m + 1) * Dv‖ ^ (M - 2)))
    (h2 : ∀ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv), lam (some z) = μ0 * ‖z‖ ^ ((m + 2) * (M + m - 1))) :
    ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)),
        conj (aC m x j) • (((lam j : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qG m x Dv j)) =
      (((μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)) : ℝ) : ℂ) •
        (U.uD U.betaU m M Φ x⁻¹ Dv - U.aD U.betaU m M Φ x⁻¹ Dv) := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
  have eM1 : M' + 2 - 2 = M' := by omega
  have eM2 : M' + 2 + m - 1 = M' + m + 1 := by omega
  rw [eM1] at h1
  rw [eM2] at h2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  rw [Finset.sum_insertNone, smul_sub, sub_eq_add_neg]
  congr 1
  ·
    show conj (aC m x none) • (((lam none : ℝ) : ℂ) • (((FormNormSumIdentities.kapB m : ℝ) : ℂ) •
        G.OmBlock U.betaU (m + 1) Φ x⁻¹ (x ^ (m + 1) * Dv))) = _
    unfold U.uD
    have hc : Dv / x⁻¹ ^ (m + 1) = x ^ (m + 1) * Dv := by rw [inv_pow]; field_simp
    rw [hc, eM1]
    simp only [aC, Complex.conj_ofReal, smul_smul, ← Complex.ofReal_mul]
    congr 2
    rw [h1, kapB_eq, norm_inv]
    simp only [inv_pow, inv_inv]
    field_simp
  ·
    unfold U.aD G.mainTerm
    rw [eM1, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := mem_root.1 hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz'
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hD hz'.symm
    have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    have hDn : ‖Dv‖ = ‖z‖ ^ (m + 2) := by
      rw [← norm_pow, hz', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    simp only [aC, qG, FormNormSumIdentities.yG, smul_smul, ← neg_smul]
    congr 1
    rw [map_neg, map_mul, psi_neg_conj, Complex.conj_ofReal, h2 z hz, hDn]
    have hψ : ((m : ℂ) + 2) * z / x⁻¹ = ((m + 2 : ℕ) : ℂ) * z * x := by push_cast; field_simp
    rw [hψ]
    have hz1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
    have hm2 : (m : ℂ) + 2 ≠ 0 := by exact_mod_cast (show (m + 2 : ℕ) ≠ 0 by omega)
    push_cast
    field_simp
    ring

end GLG

namespace GLG

/- English proof (translation)
Rewrite using `[Finset.sum_insertNone, sub_eq_add_neg, ← Finset.sum_neg_distrib, show m + 2 + 1 = m + 3 from rfl]`. Use `congr 1`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [aC, PP, neg_smul, mul_smul]`. Both sides reduce to the same expression.
-/
theorem lhs_eq_sum {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℕ) (h : C.LPt) (Vec : C.LPt → H)
    (x Dv : ℂ) :
    ((((Real.pi ^ (m + 2 - 1))⁻¹ * ‖x‖ ^ (m + 2 - 1) : ℝ) : ℂ) •
        Vec (h ++ [(m + 2 - 1, x⁻¹), (1, x ^ (m + 2 - 1) * Dv)])) -
      ∑ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * Dv),
        G.psi (-U.betaU) (((m + 2 : ℕ) : ℂ) * z * x) •
          (((((m + 2 : ℕ) : ℝ) * ‖z‖ ^ (m + 2 - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(m + 2, z)]) =
      ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)), aC m x j • Vec (PP m h x Dv j) := by
  rw [Finset.sum_insertNone, sub_eq_add_neg, ← Finset.sum_neg_distrib, show m + 2 + 1 = m + 3 from rfl]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [aC, PP, neg_smul, mul_smul]
  rfl

end GLG

open GLG in
/- English proof (translation)
Introduce `_hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb _hCb hF hnn b s hb hs hbs h hh w _hw _hN H _ _ _ Vec hVec K hK hK0`. Take `⟨m, rfl⟩ : ∃ m, s = m + 2` from `⟨s - 2, by omega⟩`. Establish `hF0` using `hF`. Take `⟨hCk, hsupp, δ, hδ, hG⟩` from `hF`. Establish `heq : ∀ g ∈ B.GV P.k P.r, D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ g = F g` using `cutF_eq_on_gv p.T.base Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hG hδ le_rfl`.

Establish `hRR : ∀ a a', p.RR F (b + (m + 2) - 1) w a a' = p.RR (D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ) (b + (m + 2) - 1) w a a'` using `fun a a' => rr_congr_belowG p hF0 (fun g hg => (heq g hg).symm) _ hbs (by omega) w a a'`. Establish `hsz : D.ptSize h + (m + 2) = b + (m + 2) - 1` using `by rw [hh.2]; omega`. Establish `hloc : D.IsLocPt h (D.ptSize h)` using `⟨hh.1, rfl⟩`. Take `⟨V, i1, i2, i3, Bf, Φ, Cp, Cst, hCp, hBf, hker, hgerm⟩` from `Formalism.FourierDecayAlt.P.germ_at_place Wp Wq P p.T (M.sgn P p.l0) w F Formalism.FourierDecayAlt.P.Topx2.chi0 δ h m (b + (m + 2) - 1) hbs hsz hCk hsupp Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hδ p.hl.2.2 hloc K hK hK0`. Use `set Mv : ℕ := U.Mlev P.k (P.r - (b + (m + 2) - 1)) with hMv`.

Establish `hM : 2 ≤ Mv` using `by rw [hMv]; unfold U.Mlev; omega`. Use `set nH : ℝ := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hnH`. Establish `hnH0 : 0 ≤ nH` using `Formalism.FourierDecayAlt.P.FormNormSumIdentities.weight_product_nonneg P.k P.r (fun _ _ => 1) (fun _ _ => zero_le_one) 1 h`. Use `set μ0 : ℝ := √nH / √(TBB.normC nn w) with hμ0`. Use `⟨Cp * |μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| * Cst, fun x hx Dv hDv => ?_⟩` and prove the remaining obligations.

Establish `hD0 : Dv ≠ 0` using `fun e => hK0 (e ▸ hDv)`. Rewrite using `[lhs_eq_sum]`. Establish `hy` using `np_PP p nn hnn F _ w b m hb hbs hRR h hh hsz Bf Φ K hker x Dv hx hDv hD0`. Establish `hle` using `Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sum_le_of_form (TBB.NP p nn F (b + (m + 2) - 1) w) Vec hVec Bf Cp hCp hBf (Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv))) (aC m x) (PP m h x Dv) (fun j => ((lam p nn w (PP m h x Dv j) : ℝ) : ℂ) • FormNormSumIden …`. Establish `hl1 : lam p nn w (PP m h x Dv none) = μ0 * ((‖x⁻¹‖ ^ ((m + 1) * (Mv + m))) * ‖x ^ (m + 1) * Dv‖ ^ (Mv - 2))` using `by show √(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * Dv)])) / √(TBB.normC nn w) = _`.

Rewrite using `[nPt_block (TBB.TTp p) b m hb hbs h hh.2, Real.sqrt_mul hnH0, ← mul_pow, Real.sqrt_sq (by positivity), hμ0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hl2 : ∀ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv), lam p nn w (PP m h x Dv (some z)) = μ0 * ‖z‖ ^ ((m + 2) * (Mv + m - 1))`. Introduce `z _`. Use `show √(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 2, z)])) / √(TBB.normC nn w) = _`.

Rewrite using `[nPt_long (TBB.TTp p) b m hb hbs h hh.2, Real.sqrt_mul hnH0, Real.sqrt_sq (by positivity), hμ0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcs` using `conjSum_TBB m Mv hM Φ x Dv hx hD0 μ0 (fun j => lam p nn w (PP m h x Dv j)) hl1 hl2`. Rewrite `hle` using `[hcs, norm_smul, Complex.norm_real, Real.norm_eq_abs]`. Establish `hg'` using `hgerm x⁻¹ Dv (inv_ne_zero hx) hDv`.

Rewrite `hg'` using `[norm_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem low_level_germ : GLGerm := by
  intro _hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb _hCb hF hnn b s hb hs hbs h hh w _hw _hN H _ _ _ Vec hVec K hK hK0
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have hF0 := hF
  obtain ⟨hCk, hsupp, δ, hδ, hG⟩ := hF
  have heq : ∀ g ∈ B.GV P.k P.r, D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ g = F g :=
    cutF_eq_on_gv p.T.base Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hG hδ le_rfl
  have hRR : ∀ a a', p.RR F (b + (m + 2) - 1) w a a' =
      p.RR (D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ) (b + (m + 2) - 1) w a a' :=
    fun a a' => rr_congr_belowG p hF0 (fun g hg => (heq g hg).symm) _ hbs (by omega) w a a'
  have hsz : D.ptSize h + (m + 2) = b + (m + 2) - 1 := by rw [hh.2]; omega
  have hloc : D.IsLocPt h (D.ptSize h) := ⟨hh.1, rfl⟩
  obtain ⟨V, i1, i2, i3, Bf, Φ, Cp, Cst, hCp, hBf, hker, hgerm⟩ :=
    Formalism.FourierDecayAlt.P.germ_at_place Wp Wq P p.T (M.sgn P p.l0) w F Formalism.FourierDecayAlt.P.Topx2.chi0 δ h m (b + (m + 2) - 1) hbs
      hsz hCk hsupp Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hδ p.hl.2.2 hloc K hK hK0
  set Mv : ℕ := U.Mlev P.k (P.r - (b + (m + 2) - 1)) with hMv
  have hM : 2 ≤ Mv := by rw [hMv]; unfold U.Mlev; omega
  set nH : ℝ := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hnH
  have hnH0 : 0 ≤ nH := Formalism.FourierDecayAlt.P.FormNormSumIdentities.weight_product_nonneg P.k P.r (fun _ _ => 1) (fun _ _ => zero_le_one) 1 h
  set μ0 : ℝ := √nH / √(TBB.normC nn w) with hμ0
  refine ⟨Cp * |μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| * Cst, fun x hx Dv hDv => ?_⟩
  have hD0 : Dv ≠ 0 := fun e => hK0 (e ▸ hDv)
  rw [lhs_eq_sum]
  have hy := np_PP p nn hnn F _ w b m hb hbs hRR h hh hsz Bf Φ K hker x Dv hx hDv hD0
  have hle := Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sum_le_of_form (TBB.NP p nn F (b + (m + 2) - 1) w) Vec hVec Bf Cp hCp hBf
    (Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv))) (aC m x) (PP m h x Dv)
    (fun j => ((lam p nn w (PP m h x Dv j) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qG m x Dv j)) hy
  have hl1 : lam p nn w (PP m h x Dv none) =
      μ0 * ((‖x⁻¹‖ ^ ((m + 1) * (Mv + m))) * ‖x ^ (m + 1) * Dv‖ ^ (Mv - 2)) := by
    show √(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * Dv)])) / √(TBB.normC nn w) = _
    rw [nPt_block (TBB.TTp p) b m hb hbs h hh.2, Real.sqrt_mul hnH0, ← mul_pow, Real.sqrt_sq (by positivity), hμ0]
    ring
  have hl2 : ∀ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv),
      lam p nn w (PP m h x Dv (some z)) = μ0 * ‖z‖ ^ ((m + 2) * (Mv + m - 1)) := by
    intro z _
    show √(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 2, z)])) / √(TBB.normC nn w) = _
    rw [nPt_long (TBB.TTp p) b m hb hbs h hh.2, Real.sqrt_mul hnH0, Real.sqrt_sq (by positivity), hμ0]
    ring
  have hcs := conjSum_TBB m Mv hM Φ x Dv hx hD0 μ0 (fun j => lam p nn w (PP m h x Dv j)) hl1 hl2
  rw [hcs, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hle
  have hg' := hgerm x⁻¹ Dv (inv_ne_zero hx) hDv
  rw [norm_inv] at hg'
  calc _ ≤ Cp * (|μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| *
        ‖U.uD U.betaU m Mv Φ x⁻¹ Dv - U.aD U.betaU m Mv Φ x⁻¹ Dv‖) := hle
    _ ≤ Cp * (|μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| * (Cst * ‖x‖⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg' (abs_nonneg _)) hCp
    _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.CutBP
