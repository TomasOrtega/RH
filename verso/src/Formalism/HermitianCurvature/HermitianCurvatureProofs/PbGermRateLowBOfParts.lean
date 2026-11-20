import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizePtG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizeToStd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSumLeOfForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateSplit

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section frame

/- English proof (translation)
Unfold `GermFibreKernels.fs`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fs_eq (r : ℕ) (g : ℝ) (b s : ℕ) (t : ℂ) : GermFibreKernels.fs r g b s t = GermFibreKernels.fs r g b s 1 * t := by
  unfold GermFibreKernels.fs; ring

/- English proof (translation)
Unfold `GermFibreKernels.fs`. Establish `h1 : (((g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (zpow_pos (div_pos hg (by positivity)) _).ne'`. Simplify using `only [mul_one]`. Conclude with `mul_ne_zero h1 (pow_ne_zero _ Complex.I_ne_zero)`.
-/
theorem fs_one_ne (r : ℕ) {g : ℝ} (hg : 0 < g) (b s : ℕ) : GermFibreKernels.fs r g b s 1 ≠ 0 := by
  unfold GermFibreKernels.fs
  have h1 : (((g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zpow_pos (div_pos hg (by positivity)) _).ne'
  simp only [mul_one]
  exact mul_ne_zero h1 (pow_ne_zero _ Complex.I_ne_zero)

/- English proof (translation)
Rewrite using `[fs_eq]`. Conclude with `mul_ne_zero (fs_one_ne r hg b s) ht`.
-/
theorem fs_ne_zero (r : ℕ) {g : ℝ} (hg : 0 < g) (b s : ℕ) {t : ℂ} (ht : t ≠ 0) : GermFibreKernels.fs r g b s t ≠ 0 := by
  rw [fs_eq]; exact mul_ne_zero (fs_one_ne r hg b s) ht

/- English proof (translation)
The claim follows from `| _, [] => by simp [D.toStd] | b, (s, t) :: rest => by have ih := toStd_blocks r hg (b + s) rest simp only [D.toStd, List.mem_cons, forall_eq_or_imp] rw [ih] have hf : ((((g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1) * t ≠ 0) ↔ t ≠ 0 := …`.
-/
theorem toStd_blocks (r : ℕ) {g : ℝ} (hg : 0 < g) : ∀ (b : ℕ) (P : C.LPt),
    (∀ x ∈ D.toStd r g b P, 1 ≤ x.1 ∧ x.2 ≠ 0) ↔ (∀ x ∈ P, 1 ≤ x.1 ∧ x.2 ≠ 0)
  | _, [] => by simp [D.toStd]
  | b, (s, t) :: rest => by
    have ih := toStd_blocks r hg (b + s) rest
    simp only [D.toStd, List.mem_cons, forall_eq_or_imp]
    rw [ih]
    have hf : ((((g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1) * t ≠ 0)
        ↔ t ≠ 0 := by
      have := fs_ne_zero r hg b s (t := t)
      constructor
      · intro h ht; apply h; rw [ht, mul_zero]
      · intro ht; exact this ht
    simp only [hf]

/- English proof (translation)
Unfold `D.IsLocPt`. Rewrite using `[toStd_blocks r hg b P, ptSize_toStd]`.
-/
theorem isLocPt_toStdD (r : ℕ) {g : ℝ} (hg : 0 < g) (b : ℕ) (P : C.LPt) (i : ℕ) :
    D.IsLocPt (D.toStd r g b P) i ↔ D.IsLocPt P i := by
  unfold D.IsLocPt
  rw [toStd_blocks r hg b P, ptSize_toStd]

end frame

section cut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [PBASM.cutSeq, D.cutF]`. Rewrite using `[smul_comm]`.
-/
theorem cutSeq_eq (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (n : ℕ) (v : Fin S.f)
    (ε : ℝ) :
    PBASM.cutSeq S p f χ n v ε = D.cutF (p v).T.base χ (fun g => PBASM.cutN n g • f v g) ε := by
  funext g
  simp only [PBASM.cutSeq, D.cutF]
  rw [smul_comm]

/- English proof (translation)
Unfold `KB.gN C.HidaSetting.gramLoc PBL.setC KB.withRR`. Simplify using `only`. Unfold `PBL.rrC KB.Pl.RR D.RRplace`. Rewrite using `[dif_neg (fun h => hP ((isLocPt_toStdD S.G.r hg 1 P i).1 h.1))]`. Simplify using the standard rewrite rules.
-/
theorem gN_setC_zero (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hg : (0 : ℝ) < (S.g : ℝ))
    (v : Fin S.f) (ε : ℝ) (i : ℕ) (a : List C.Letter) (P Q : C.LPt) (hP : ¬ D.IsLocPt P i) :
    KB.gN (PBL.setC S p F) v ε i a P Q = 0 := by
  unfold KB.gN C.HidaSetting.gramLoc PBL.setC KB.withRR
  simp only
  unfold PBL.rrC KB.Pl.RR D.RRplace
  rw [dif_neg (fun h => hP ((isLocPt_toStdD S.G.r hg 1 P i).1 h.1))]
  simp

end cut

section psi

/- English proof (translation)
Unfold `G.psi`. Rewrite using `[← Complex.exp_conj]`. Use `congr 1`. Simplify using `only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_neg, Complex.neg_re, Complex.ofReal_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_conj (β w : ℂ) : conj (G.psi β w) = G.psi β (-w) := by
  unfold G.psi
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_neg, Complex.neg_re, Complex.ofReal_neg]
  ring

/- English proof (translation)
Simplify using `[G.rootSet, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hs)]`.
-/
theorem mem_rootSet4 {s : ℕ} (hs : s ≠ 0) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by
  simp [G.rootSet, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hs)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

/- English proof (translation)
Rewrite using `[GermFibreKernels.char_std S hg b s hs x⁻¹ z (inv_ne_zero hx), psi_conj, ← GermRealisation.psi_betaL, inv_inv]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem char_conj (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < (S.g : ℝ)) (b s : ℕ) (hs : 2 ≤ s) (x z : ℂ)
    (hx : x ≠ 0) :
    conj (G.psi (GermRealisation.betaL S) ((s : ℂ) * z * x)) =
      G.psi U.betaU ((s : ℂ) * GermFibreKernels.fs S.G.r (S.g : ℝ) b s z / GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹) := by
  rw [GermFibreKernels.char_std S hg b s hs x⁻¹ z (inv_ne_zero hx), psi_conj, ← GermRealisation.psi_betaL, inv_inv]
  congr 1
  ring

end psi

section roots

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `by omega`. Use extensionality with `w`. Rewrite using `[mem_rootSet4 hs0, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `hw`.

Use `⟨w / GermFibreKernels.fs r g b s 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_rootSet4 hs0]`. Establish `e : GermFibreKernels.fs r g b s (w / GermFibreKernels.fs r g b s 1) = w`. Rewrite using `[fs_eq]`. Clear denominators, using `[fs_one_ne r hg b s]` for the nonvanishing conditions.

Use `(GermFibreKernels.roots_std r g hg b s hs t c (w / GermFibreKernels.fs r g b s 1)).1` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this hw`. Rewrite using `[fs_eq]`. Clear denominators, using `[fs_one_ne r hg b s]` for the nonvanishing conditions.

Introduce and unpack `⟨z, hz, rfl⟩`. Rewrite `hz` using `[mem_rootSet4 hs0]`. Conclude with `(GermFibreKernels.roots_std r g hg b s hs t c z).2 hz`.
-/
theorem rootSet_std (r : ℕ) {g : ℝ} (hg : 0 < g) (b s : ℕ) (hs : 2 ≤ s) (t c : ℂ) :
    G.rootSet s ((-1) ^ (s + 1) * (GermFibreKernels.fs r g (b + (s - 1)) 1 c * GermFibreKernels.fs r g b (s - 1) t ^ (s - 1))) =
      (G.rootSet s (c * t ^ (s - 1))).image (fun z => GermFibreKernels.fs r g b s z) := by
  have hs0 : s ≠ 0 := by omega
  ext w
  rw [mem_rootSet4 hs0, Finset.mem_image]
  constructor
  · intro hw
    refine ⟨w / GermFibreKernels.fs r g b s 1, ?_, ?_⟩
    · rw [mem_rootSet4 hs0]
      have e : GermFibreKernels.fs r g b s (w / GermFibreKernels.fs r g b s 1) = w := by
        rw [fs_eq]; field_simp [fs_one_ne r hg b s]
      have := (GermFibreKernels.roots_std r g hg b s hs t c (w / GermFibreKernels.fs r g b s 1)).1
      rw [e] at this
      exact this hw
    · rw [fs_eq]; field_simp [fs_one_ne r hg b s]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_rootSet4 hs0] at hz
    exact (GermFibreKernels.roots_std r g hg b s hs t c z).2 hz

end roots

section cutn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => PBASM.cutN n g)`. Establish `e : (fun g : B.Mat k r => PBASM.cutN n g) = fun g => 1 - JCx2.pdPsi ((n : ℝ) + 1) g`. Use function extensionality and compare the values at `fun g => PBE.cut_eq (fun n g => PBASM.cutN n g) (fun n g => rfl) n g`. Rewrite using `[e]`. Conclude with `contDiff_const.sub (JCx2.pd_psi_cd _)`.

Conclude with `JCx2.pd_smooth_smul hcs hf`.
-/
theorem cutN_smooth {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn (⊤ : ℕ∞) (B.GV k r) f) (n : ℕ) :
    B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => PBASM.cutN n g • f g) := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => PBASM.cutN n g) := by
    have e : (fun g : B.Mat k r => PBASM.cutN n g) = fun g => 1 - JCx2.pdPsi ((n : ℝ) + 1) g :=
      funext fun g => PBE.cut_eq (fun n g => PBASM.cutN n g) (fun n g => rfl) n g
    rw [e]
    exact contDiff_const.sub (JCx2.pd_psi_cd _)
  exact JCx2.pd_smooth_smul hcs hf

/- English proof (translation)
Introduce `g _ hne`. Establish `hc : PBASM.cutN n g ≠ 0` using `by intro h0; apply hne; simp [h0]`. Unfold `PBASM.cutN at hc`. Establish `hpos : 0 < (4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3`. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Apply `hc` to reduce the goal to its premises. Rewrite using `[Real.smoothTransition.zero_of_nonpos hle]`. Simplify using the standard rewrite rules. Establish `hn1 : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`.

Establish `hsum : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) = ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlt : ∑ i, ∑ j, Complex.normSq (g i j) < 4 * ((n : ℝ) + 1) ^ 2`. Rewrite `hpos` using `[hsum]`. Establish `h1 : ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) < 4` using `by linarith`.

Establish `h2 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) = ∑ i, ∑ j, Complex.normSq (g i j)`. Clear the denominators using the available nonvanishing facts. Establish `h3 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) < ((n : ℝ) + 1) ^ 2 * 4` using `mul_lt_mul_of_pos_left h1 (by positivity)`. Rewrite `h3` using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `B.gN`. Rewrite using `[show (2 * ((n : ℝ) + 1)) = Real.sqrt ((2 * ((n : ℝ) + 1)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]`. Conclude with `Real.sqrt_le_sqrt (by nlinarith)`.
-/
theorem cutN_supp {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E) (n : ℕ) :
    ∀ g ∈ B.GV k r, PBASM.cutN n g • f g ≠ 0 → B.gN g ≤ 2 * ((n : ℝ) + 1) := by
  intro g _ hne
  have hc : PBASM.cutN n g ≠ 0 := by intro h0; apply hne; simp [h0]
  unfold PBASM.cutN at hc
  have hpos : 0 < (4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3 := by
    by_contra hle
    push_neg at hle
    apply hc
    rw [Real.smoothTransition.zero_of_nonpos hle]
    simp
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsum : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) =
      ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have hlt : ∑ i, ∑ j, Complex.normSq (g i j) < 4 * ((n : ℝ) + 1) ^ 2 := by
    rw [hsum] at hpos
    have h1 : ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) < 4 := by linarith
    have h2 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) =
        ∑ i, ∑ j, Complex.normSq (g i j) := by
      field_simp
    have h3 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) <
        ((n : ℝ) + 1) ^ 2 * 4 :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    rw [h2] at h3
    linarith
  unfold B.gN
  rw [show (2 * ((n : ℝ) + 1)) = Real.sqrt ((2 * ((n : ℝ) + 1)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  exact Real.sqrt_le_sqrt (by nlinarith)

end cutn

section decomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def PPt (s : ℕ) (h : C.LPt) (x D : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]
  | some z => h ++ [(s, z)]

def aCo (S : C.HidaSetting E Wp Wq) (s : ℕ) (dl1 dl2 : ℝ) (x : ℂ) : Option ℂ → ℂ
  | none => ((‖x‖ ^ (s - 1) * (√dl1)⁻¹ : ℝ) : ℂ)
  | some z => -(G.psi (GermRealisation.betaL S) ((s : ℂ) * z * x) * ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√dl2)⁻¹ : ℝ) : ℂ))

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `by omega`. Rewrite using `[Finset.sum_insertNone]`. Unfold `GermRealisation.utOf GermFibreKernels.vOf GermRealisation.ptX PBK.mainD`. Simplify using `only [aCo, PPt, one_mul, one_smul]`. Rewrite using `[sub_eq_add_neg, ← Finset.sum_neg_distrib, smul_smul, ← Complex.ofReal_mul]`.

Use `congr 1`. Simplify using `only [List.append_assoc, List.cons_append, List.nil_append]`. Use `Finset.sum_congr rfl fun z hz => ?_` and prove the remaining obligations. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hz` using `[mem_rootSet4 hs0, zero_pow hs0]`. Conclude with `hD hz.symm`. Simplify using `only [GermFibreKernels.btOf, if_neg hz0, smul_smul, neg_smul]`.
-/
theorem utOf_sub_mainD {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : C.HidaSetting E Wp Wq) (s : ℕ) (hs : 2 ≤ s) (dl1 dl2 : ℝ) (Vec : C.LPt → H) (h : C.LPt) (x D : ℂ)
    (hD : D ≠ 0) :
    GermRealisation.utOf s (GermFibreKernels.vOf dl1 Vec) h x D -
                   PBK.mainD s (GermRealisation.betaL S) 1 (fun z => (fun _ => (1 : ℂ)) z • GermFibreKernels.btOf s dl2 Vec h z) x D =
      ∑ j ∈ Finset.insertNone (G.rootSet s D), aCo S s dl1 dl2 x j • Vec (PPt s h x D j) := by
  have hs0 : s ≠ 0 := by omega
  rw [Finset.sum_insertNone]
  unfold GermRealisation.utOf GermFibreKernels.vOf GermRealisation.ptX PBK.mainD
  simp only [aCo, PPt, one_mul, one_smul]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, smul_smul, ← Complex.ofReal_mul]
  congr 1
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [mem_rootSet4 hs0, zero_pow hs0] at hz
      exact hD hz.symm
    simp only [GermFibreKernels.btOf, if_neg hz0, smul_smul, neg_smul]

end decomp

section frame2

def qq (r : ℕ) (g : ℝ) (b s : ℕ) (x D : ℂ) : Option ℂ → (ℂ × ℂ) ⊕ ℂ
  | none => Sum.inl (GermFibreKernels.fs r g b (s - 1) x⁻¹, GermFibreKernels.fs r g (b + s - 1) 1 (x ^ (s - 1) * D))
  | some z => Sum.inr (GermFibreKernels.fs r g b s z)

def kapD (r : ℕ) (g : ℝ) (b s : ℕ) : ℂ := GermFibreKernels.fs r g (b + s - 1) 1 1 * GermFibreKernels.fs r g b (s - 1) 1 ^ (s - 1)

/- English proof (translation)
The claim follows from `mul_ne_zero (fs_one_ne r hg _ _) (pow_ne_zero _ (fs_one_ne r hg _ _))`.
-/
theorem kapD_ne (r : ℕ) {g : ℝ} (hg : 0 < g) (b s : ℕ) : kapD r g b s ≠ 0 :=
  mul_ne_zero (fs_one_ne r hg _ _) (pow_ne_zero _ (fs_one_ne r hg _ _))

/- English proof (translation)
Establish `e1 : 1 + D.ptSize h = b` using `by omega`. Establish `e2 : 1 + D.ptSize h + (s - 1) = b + s - 1` using `by omega`. Establish `e3 : s - 2 + 1 = s - 1` using `by omega`. Establish `e4 : s - 2 + 2 = s` using `by omega`. Consider the cases of `j with`.

Consider the case `none`. Simplify using `only [PPt, ptG, qq]`. Rewrite using `[(GermFibreKernels.toStd_germPts r g h s x⁻¹ (x ^ (s - 1) * Dc) 0).1, e1, e3, show b + (s - 1) = b + s - 1 by omega]`. Consider the case `some z`. Simplify using `only [PPt, ptG, qq]`.

Rewrite using `[(GermFibreKernels.toStd_germPts r g h s 1 1 z).2, e1, e4]`.
-/
theorem toStd_PPt (r : ℕ) (g : ℝ) (b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s) (h : C.LPt) (hh : D.ptSize h = b - 1)
    (x Dc : ℂ) (j : Option ℂ) :
    D.toStd r g 1 (PPt s h x Dc j) = ptG (D.toStd r g 1 h) (s - 2) (qq r g b s x Dc j) := by
  have e1 : 1 + D.ptSize h = b := by omega
  have e2 : 1 + D.ptSize h + (s - 1) = b + s - 1 := by omega
  have e3 : s - 2 + 1 = s - 1 := by omega
  have e4 : s - 2 + 2 = s := by omega
  cases j with
  | none =>
    simp only [PPt, ptG, qq]
    rw [(GermFibreKernels.toStd_germPts r g h s x⁻¹ (x ^ (s - 1) * Dc) 0).1, e1, e3, show b + (s - 1) = b + s - 1 by omega]
  | some z =>
    simp only [PPt, ptG, qq]
    rw [(GermFibreKernels.toStd_germPts r g h s 1 1 z).2, e1, e4]

/- English proof (translation)
Unfold `kapD`. Rewrite using `[fs_eq r g (b + s - 1) 1, fs_eq r g b (s - 1) x⁻¹, mul_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem cD_eq (r : ℕ) {g : ℝ} (b s : ℕ) (hs : 2 ≤ s) (x D : ℂ) (hx : x ≠ 0) :
    GermFibreKernels.fs r g (b + s - 1) 1 (x ^ (s - 1) * D) * GermFibreKernels.fs r g b (s - 1) x⁻¹ ^ (s - 1) = kapD r g b s * D := by
  unfold kapD
  rw [fs_eq r g (b + s - 1) 1, fs_eq r g b (s - 1) x⁻¹, mul_pow, inv_pow]
  field_simp

/- English proof (translation)
Establish `e3 : s - 2 + 1 = s - 1` using `by omega`. Establish `e4 : s - 2 + 2 = s` using `by omega`. Establish `e5 : s - 2 + 3 = s + 1` using `by omega`. Consider the cases of `j with`. Consider the case `none`.

Simplify using `only [qq, okG]`. Use `⟨fs_ne_zero r hg b (s - 1) (inv_ne_zero hx), ⟨D, hD, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[e3, cD_eq r b s hs x D hx]`. Consider the case `some z`. Simplify using `only [qq, okG]`.

Establish `hj' : z ∈ G.rootSet s D` using `Finset.mem_insertNone.1 hj z rfl`. Establish `hz` using `(mem_rootSet4 (by omega : s ≠ 0)).1 hj'`. Use `⟨kapD r g b s * D, ⟨D, hD, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hb1 : b + (s - 1) = b + s - 1` using `by omega`. Establish `key` using `(GermFibreKernels.roots_std r g hg b s hs x⁻¹ (x ^ (s - 1) * D) z).2 (by`.

Rewrite using `[hz, inv_pow]`. Use the proof step `field_simp)`. Rewrite `key` using `[hb1, cD_eq r b s hs x D hx]`. Rewrite using `[e4, e5]`. Conclude with `key`.
-/
theorem okG_qq (r : ℕ) {g : ℝ} (hg : 0 < g) (b s : ℕ) (hs : 2 ≤ s) (K : Set ℂ) (x D : ℂ) (hx : x ≠ 0)
    (hD : D ∈ K) (j : Option ℂ) (hj : j ∈ Finset.insertNone (G.rootSet s D)) :
    okG (s - 2) ((fun D => kapD r g b s * D) '' K) (qq r g b s x D j) := by
  have e3 : s - 2 + 1 = s - 1 := by omega
  have e4 : s - 2 + 2 = s := by omega
  have e5 : s - 2 + 3 = s + 1 := by omega
  cases j with
  | none =>
    simp only [qq, okG]
    refine ⟨fs_ne_zero r hg b (s - 1) (inv_ne_zero hx), ⟨D, hD, ?_⟩⟩
    rw [e3, cD_eq r b s hs x D hx]
  | some z =>
    simp only [qq, okG]
    have hj' : z ∈ G.rootSet s D := Finset.mem_insertNone.1 hj z rfl
    have hz := (mem_rootSet4 (by omega : s ≠ 0)).1 hj'
    refine ⟨kapD r g b s * D, ⟨D, hD, rfl⟩, ?_⟩
    have hb1 : b + (s - 1) = b + s - 1 := by omega
    have key := (GermFibreKernels.roots_std r g hg b s hs x⁻¹ (x ^ (s - 1) * D) z).2 (by
      rw [hz, inv_pow]; field_simp)
    rw [hb1, cD_eq r b s hs x D hx] at key
    rw [e4, e5]
    exact key

end frame2

section conjsum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

/- English proof (translation)
Use `set T1 := GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹ with hT1`. Use `set C1 := GermFibreKernels.fs S.G.r (S.g : ℝ) (b + (m + 1)) 1 (x ^ (m + 1) * D) with hC1`. Establish `hT0 : T1 ≠ 0` using `fs_ne_zero _ hg _ _ (inv_ne_zero hx)`. Rewrite using `[Finset.sum_insertNone, smul_sub, sub_eq_add_neg]`. Use `congr 1`.

Use `show conj (((‖x‖ ^ (m + 1) * (√dl1)⁻¹ : ℝ) : ℂ)) • (((lam none : ℝ) : ℂ) • (((kapB m : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Φ T1 C1)) = _`. Unfold `U.uD`. Establish `hc : C1 * T1 ^ (m + 1) / T1 ^ (m + 1) = C1` using `by field_simp`. Rewrite using `[hc, Complex.conj_ofReal, smul_smul, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, h1]`. Establish `hR : G.rootSet (m + 2) ((-1) ^ (m + 3) * (C1 * T1 ^ (m + 1))) = (G.rootSet (m + 2) D).image (fun z => GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 2) z)`.

Establish `h0` using `rootSet_std S.G.r hg b (m + 2) (by omega) x⁻¹ (x ^ (m + 1) * D)`. Establish `e : x ^ (m + 1) * D * x⁻¹ ^ (m + 2 - 1) = D` using `by show x ^ (m + 1) * D * x⁻¹ ^ (m + 1) = D`. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite `h0` using `[e]`.

Conclude with `h0`. Establish `hinj : Set.InjOn (fun z => GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 2) z) (G.rootSet (m + 2) D)`. Introduce `z1 _ z2 _ h`. Simplify using `only at h`. Rewrite `h` using `[fs_eq, fs_eq S.G.r (S.g : ℝ) b (m + 2) z2]`.

Conclude with `mul_left_cancel₀ (fs_one_ne _ hg _ _) h`. Unfold `U.aD G.mainTerm`. Rewrite using `[hR, Finset.sum_image hinj, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun z hz => ?_` and prove the remaining obligations. Simplify using `only [aCo, qq, yG, smul_smul, ← neg_smul]`.

Use `congr 1`. Establish `hc' : conj (G.psi (GermRealisation.betaL S) (((m + 2 : ℕ) : ℂ) * z * x)) = G.psi U.betaU (((m + 2 : ℕ) : ℂ) * GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 2) z / T1)` using `char_conj S hg b (m + 2) (by omega) x z hx`. Rewrite using `[map_neg, map_mul, Complex.conj_ofReal, hc', show m + 2 - 1 = m + 1 from rfl]`. Establish `key` using `congrArg (fun r : ℝ => (r : ℂ)) (h2 z hz)`. Move the coercions through the operations in `at key ⊢`.

Take the linear combination `(-(G.psi U.betaU (((m : ℂ) + 2) * GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 2) z / T1))) * key`.
-/
theorem conjSum_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (S : C.HidaSetting E Wp Wq)
    (hg : (0 : ℝ) < (S.g : ℝ)) (b m : ℕ) (dl1 dl2 μ₀ : ℝ) (Φ : G.Mat (m + 2) → V) (M : ℕ) (x D : ℂ)
    (hx : x ≠ 0) (hD : D ≠ 0) (lam : Option ℂ → ℝ)
    (h1 : ‖x‖ ^ (m + 1) * (√dl1)⁻¹ * lam none * kapB m =
      μ₀ * ((‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹‖ ^ (m + 1))⁻¹ *
        ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹‖ ^ ((m + 1) * (M + m)) *
        ‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + (m + 1)) 1 (x ^ (m + 1) * D)‖ ^ (M - 2)))
    (h2 : ∀ z ∈ G.rootSet (m + 2) D, (((m + 2 : ℕ) : ℝ) * ‖z‖ ^ (m + 1))⁻¹ * (√dl2)⁻¹ * lam (some z) *
        Real.pi ^ ((m + 2) * (m + 1) / 2) =
      μ₀ * (‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + (m + 1)) 1 (x ^ (m + 1) * D) *
          GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹ ^ (m + 1)‖ ^ (M - 2) *
        ((((m + 2 : ℕ) : ℝ))⁻¹ * ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 2) z‖ ^ ((m + 1) ^ 2)))) :
    ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) D),
        conj (aCo S (m + 2) dl1 dl2 x j) • (((lam j : ℝ) : ℂ) • yG U.betaU m Φ (qq S.G.r (S.g : ℝ) b (m + 2) x D j)) =
      (μ₀ : ℂ) • (U.uD U.betaU m M Φ (GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹)
          (GermFibreKernels.fs S.G.r (S.g : ℝ) (b + (m + 1)) 1 (x ^ (m + 1) * D) * GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹ ^ (m + 1)) -
        U.aD U.betaU m M Φ (GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹)
          (GermFibreKernels.fs S.G.r (S.g : ℝ) (b + (m + 1)) 1 (x ^ (m + 1) * D) * GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹ ^ (m + 1))) := by
  set T1 := GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹ with hT1
  set C1 := GermFibreKernels.fs S.G.r (S.g : ℝ) (b + (m + 1)) 1 (x ^ (m + 1) * D) with hC1
  have hT0 : T1 ≠ 0 := fs_ne_zero _ hg _ _ (inv_ne_zero hx)
  rw [Finset.sum_insertNone, smul_sub, sub_eq_add_neg]
  congr 1
  ·
    show conj (((‖x‖ ^ (m + 1) * (√dl1)⁻¹ : ℝ) : ℂ)) • (((lam none : ℝ) : ℂ) • (((kapB m : ℝ) : ℂ) •
        G.OmBlock U.betaU (m + 1) Φ T1 C1)) = _
    unfold U.uD
    have hc : C1 * T1 ^ (m + 1) / T1 ^ (m + 1) = C1 := by field_simp
    rw [hc, Complex.conj_ofReal, smul_smul, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, h1]
  ·
    have hR : G.rootSet (m + 2) ((-1) ^ (m + 3) * (C1 * T1 ^ (m + 1))) =
        (G.rootSet (m + 2) D).image (fun z => GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 2) z) := by
      have h0 := rootSet_std S.G.r hg b (m + 2) (by omega) x⁻¹ (x ^ (m + 1) * D)
      have e : x ^ (m + 1) * D * x⁻¹ ^ (m + 2 - 1) = D := by
        show x ^ (m + 1) * D * x⁻¹ ^ (m + 1) = D
        rw [inv_pow]; field_simp
      rw [e] at h0
      exact h0
    have hinj : Set.InjOn (fun z => GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 2) z) (G.rootSet (m + 2) D) := by
      intro z1 _ z2 _ h
      simp only at h
      rw [fs_eq, fs_eq S.G.r (S.g : ℝ) b (m + 2) z2] at h
      exact mul_left_cancel₀ (fs_one_ne _ hg _ _) h
    unfold U.aD G.mainTerm
    rw [hR, Finset.sum_image hinj, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    simp only [aCo, qq, yG, smul_smul, ← neg_smul]
    congr 1
    have hc' : conj (G.psi (GermRealisation.betaL S) (((m + 2 : ℕ) : ℂ) * z * x)) =
        G.psi U.betaU (((m + 2 : ℕ) : ℂ) * GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 2) z / T1) :=
      char_conj S hg b (m + 2) (by omega) x z hx
    rw [map_neg, map_mul, Complex.conj_ofReal, hc', show m + 2 - 1 = m + 1 from rfl]
    have key := congrArg (fun r : ℝ => (r : ℂ)) (h2 z hz)
    push_cast at key ⊢
    linear_combination (-(G.psi U.betaU (((m : ℂ) + 2) * GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 2) z / T1))) * key

end conjsum

section main

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem slv_congr {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (i : ℕ) (hi : i ≤ r) (w : List C.Letter) {P P' : C.LPt} (e : P = P') (hp : D.ptSize P = i)
    (hp' : D.ptSize P' = i) : KB.slv T F i hi w P hp = KB.slv T F i hi w P' hp' := by
  subst e; rfl

/- English proof (translation)
Consider the cases of `j with`. Consider the case `none`. Use `⟨fun y hy => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [PPt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy`. Break down `hy with hy | rfl | rfl` into its components or cases.

Conclude with `hloc y hy`. Conclude with `⟨by omega, inv_ne_zero hx⟩`. Conclude with `⟨le_rfl, mul_ne_zero (pow_ne_zero _ hx) hD⟩`. Simplify using `[PPt, D.ptSize, List.map_append, List.sum_append] at hh ⊢`. Use linear arithmetic over natural numbers and integers.

Consider the case `some z`. Establish `hj' : z ∈ G.rootSet s Dc` using `Finset.mem_insertNone.1 hj z rfl`. Establish `hz` using `(mem_rootSet4 (by omega : s ≠ 0)).1 hj'`. Establish `hz0 : z ≠ 0` using `by rintro rfl; rw [zero_pow (by omega)] at hz; exact hD hz.symm`. Use `⟨fun y hy => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [PPt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy`. Break down `hy with hy | rfl` into its components or cases. Conclude with `hloc y hy`. Conclude with `⟨by omega, hz0⟩`. Simplify using `[PPt, D.ptSize, List.map_append, List.sum_append] at hh ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
theorem isLocPt_PPt (s : ℕ) (hs : 2 ≤ s) (b : ℕ) (hb : 1 ≤ b) (h : C.LPt) (hh : D.ptSize h = b - 1)
    (hloc : ∀ y ∈ h, 1 ≤ y.1 ∧ y.2 ≠ 0) (x Dc : ℂ) (hx : x ≠ 0) (hD : Dc ≠ 0) (j : Option ℂ)
    (hj : j ∈ Finset.insertNone (G.rootSet s Dc)) : D.IsLocPt (PPt s h x Dc j) (b + s - 1) := by
  cases j with
  | none =>
    refine ⟨fun y hy => ?_, ?_⟩
    · simp only [PPt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | rfl | rfl
      · exact hloc y hy
      · exact ⟨by omega, inv_ne_zero hx⟩
      · exact ⟨le_rfl, mul_ne_zero (pow_ne_zero _ hx) hD⟩
    · simp [PPt, D.ptSize, List.map_append, List.sum_append] at hh ⊢; omega
  | some z =>
    have hj' : z ∈ G.rootSet s Dc := Finset.mem_insertNone.1 hj z rfl
    have hz := (mem_rootSet4 (by omega : s ≠ 0)).1 hj'
    have hz0 : z ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hz; exact hD hz.symm
    refine ⟨fun y hy => ?_, ?_⟩
    · simp only [PPt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | rfl
      · exact hloc y hy
      · exact ⟨by omega, hz0⟩
    · simp [PPt, D.ptSize, List.map_append, List.sum_append] at hh ⊢; omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

/- English proof (translation)
Introduce `j hj l hl`. Establish `hPj` using `isLocPt_PPt s hs b hb h hh hloc x Dc hx hD j hj`. Establish `hPl` using `isLocPt_PPt s hs b hb h hh hloc x Dc hx hD l hl`. Rewrite using `[hGN E Wp Wq S p (PBASM.cutSeq S p f χ n) v ε (b + s - 1) hi a _ _ hPj hPl]`. Simplify using `only [cutSeq_eq]`.

Rewrite using `[slv_congr _ _ _ _ _ (toStd_PPt S.G.r (S.g : ℝ) b s hb hs h hh x Dc j) _ (by rw [ptSize_ptG, hsz]), slv_congr _ _ _ _ _ (toStd_PPt S.G.r (S.g : ℝ) b s hb hs h hh x Dc l) _ (by rw [ptSize_ptG, hsz]), hker _ _ (hKc j hj) (hKc l hl)]`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kernel_PPt (hGN : GNSetC) (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (n : ℕ) (v : Fin S.f)
    (ε : ℝ) (hg : (0 : ℝ) < (S.g : ℝ)) (b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s) (hi : b + s - 1 ≤ S.G.r)
    (a : List C.Letter) (h : C.LPt) (hh : D.ptSize h = b - 1) (hloc : ∀ y ∈ h, 1 ≤ y.1 ∧ y.2 ≠ 0) (x Dc : ℂ)
    (hx : x ≠ 0) (hD : Dc ≠ 0) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : G.Mat (s - 2 + 2) → V) (Kc : Set ℂ)
    (hKc : ∀ j ∈ Finset.insertNone (G.rootSet s Dc), okG (s - 2) Kc (qq S.G.r (S.g : ℝ) b s x Dc j))
    (hsz : D.ptSize (D.toStd S.G.r (S.g : ℝ) 1 h) + (s - 2 + 2) = b + s - 1)
    (hker : ∀ q1 q2, okG (s - 2) Kc q1 → okG (s - 2) Kc q2 →
      D.formLev (p v).T (M.sgn (D.parOf S v) (p v).l0) ⟨b + s - 1, by have e : (D.parOf S v).r = S.G.r := rfl; omega⟩ a
        (KB.slv (p v).T (D.cutF (p v).T.base χ (fun g => PBASM.cutN n g • f v g) ε) (b + s - 1) hi a
          (ptG (D.toStd S.G.r (S.g : ℝ) 1 h) (s - 2) q1) (by rw [ptSize_ptG, hsz]))
        (KB.slv (p v).T (D.cutF (p v).T.base χ (fun g => PBASM.cutN n g • f v g) ε) (b + s - 1) hi a
          (ptG (D.toStd S.G.r (S.g : ℝ) 1 h) (s - 2) q2) (by rw [ptSize_ptG, hsz])) =
      Bf (yG U.betaU (s - 2) Φ q1) (yG U.betaU (s - 2) Φ q2)) :
    ∀ j ∈ Finset.insertNone (G.rootSet s Dc), ∀ l ∈ Finset.insertNone (G.rootSet s Dc),
      KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + s - 1) a (PPt s h x Dc j) (PPt s h x Dc l) =
        Bf (((lamP S v a (b + s - 1) (PPt s h x Dc j) : ℝ) : ℂ) • yG U.betaU (s - 2) Φ (qq S.G.r (S.g : ℝ) b s x Dc j))
          (((lamP S v a (b + s - 1) (PPt s h x Dc l) : ℝ) : ℂ) • yG U.betaU (s - 2) Φ (qq S.G.r (S.g : ℝ) b s x Dc l)) := by
  intro j hj l hl
  have hPj := isLocPt_PPt s hs b hb h hh hloc x Dc hx hD j hj
  have hPl := isLocPt_PPt s hs b hb h hh hloc x Dc hx hD l hl
  rw [hGN E Wp Wq S p (PBASM.cutSeq S p f χ n) v ε (b + s - 1) hi a _ _ hPj hPl]
  simp only [cutSeq_eq]
  rw [slv_congr _ _ _ _ _ (toStd_PPt S.G.r (S.g : ℝ) b s hb hs h hh x Dc j) _ (by rw [ptSize_ptG, hsz]),
    slv_congr _ _ _ _ _ (toStd_PPt S.G.r (S.g : ℝ) b s hb hs h hh x Dc l) _ (by rw [ptSize_ptG, hsz]),
    hker _ _ (hKc j hj) (hKc l hl)]
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Complex.conj_ofReal]
  push_cast
  ring

end main

section final

/- English proof (translation)
Introduce `_hA Cb`. Use `⟨0, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v`. Take `⟨hg1, hg2, -, hχ, -, -, -, -, -, -, -, -, -, -, -, hv⟩` from `hB`. Take `⟨-, -, -, hf, -⟩` from `hv v`.

Establish `hg : (0 : ℝ) < (S.g : ℝ)` using `by unfold C.HidaSetting.g; exact_mod_cast Nat.mul_pos hg1 hg2`. Introduce `ε hε b s hb hs hbs a _ha H _ _ _ Vec hVec`. Use `⟨1, fun _ => 1, by simp, fun _ => by simp, continuousOn_const, ?_⟩` and prove the remaining obligations. Introduce `h hh K hK hK0`. Establish `hr : (PBL.setC S p (PBASM.cutSeq S p f χ n)).G.r = S.G.r` using `rfl`.

Establish `hi : b + s - 1 ≤ S.G.r` using `by omega`. Distinguish the cases in `hloc : ∀ y ∈ h, 1 ≤ y.1 ∧ y.2 ≠ 0`. Use `swap`. Use `⟨0, fun x _ Dv hD => ?_⟩` and prove the remaining obligations. Establish `hD0 : Dv ≠ 0` using `fun h0 => hK0 (h0 ▸ hD)`.

Rewrite using `[utOf_sub_mainD _ s hs _ _ Vec h x Dv hD0]`. Establish `hz : ∀ j, Vec (PPt s h x Dv j) = 0`. Introduce `j`. Establish `hnl : ¬ D.IsLocPt (PPt s h x Dv j) (b + s - 1)`. Apply the tactic sequence `intro hl; apply hloc; intro y hy; exact hl.1 y (by cases j <;> simp [PPt, hy])`.

Establish `h0` using `gN_setC_zero S p (PBASM.cutSeq S p f χ n) hg v ε (b + s - 1) a _ (PPt s h x Dv j) hnl`. Rewrite `h0` using `[hVec]`. Conclude with `inner_self_eq_zero.1 h0`. Simplify using `[hz]`. Take `⟨m, rfl⟩ : ∃ m, s = m + 2` from `⟨s - 2, by omega⟩`.

Establish `hsz : D.ptSize (D.toStd S.G.r (S.g : ℝ) 1 h) + (m + 2 - 2 + 2) = b + (m + 2) - 1`. Rewrite using `[ptSize_toStd, hh]`. Use linear arithmetic over natural numbers and integers. Establish `hlocStd : D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 h) (D.ptSize (D.toStd S.G.r (S.g : ℝ) 1 h))` using `(isLocPt_toStdD _ hg 1 h _).2 ⟨hloc, (ptSize_toStd _ _ 1 h).symm⟩`. Use `set Kc : Set ℂ := (fun D => kapD S.G.r (S.g : ℝ) b (m + 2) * D) '' K with hKcdef`.

Establish `hKc : IsCompact Kc` using `hK.image (continuous_const.mul continuous_id)`. Establish `hKc0 : (0 : ℂ) ∉ Kc`. Introduce and unpack `⟨D, hD, hD0⟩`. Use `mul_eq_zero.1 hD0` as an intermediate fact. Break down `this with h1 | h1` into its components or cases.

Conclude with `kapD_ne _ hg _ _ h1`. Conclude with `hK0 (h1 ▸ hD)`. Take `⟨V, i1, i2, i3, Bf, Φ, Cp, Cst, hCp, hBf, hker, hgerm⟩` from `hGP (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v).T (M.sgn (D.parOf S v) (p v).l0) a (fun g => PBASM.cutN n g • f v g) χ ε (D.toStd S.G.r (S.g : ℝ) 1 h) (m + 2 - 2) (b + (m + 2) - 1) hi hsz (cutN_smooth hf n) ⟨_, cutN_supp (f v) n⟩ hχ hε (p v).hl.2.2 hlocStd Kc hKc hKc0`. Take `⟨μ₀, hμ⟩` from `hGC E Wp Wq (PBL.setC S p (PBASM.cutSeq S p f χ n)) v a b (m + 2) hg1 hg2 hb hs hi h hh`. Use `⟨Cp * |μ₀| * Cst * ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) 1‖, fun x hx D hD => ?_⟩` and prove the remaining obligations.

Establish `hD0 : D ≠ 0` using `fun h0 => hK0 (h0 ▸ hD)`. Take `⟨z0, hz0⟩` from `IsAlgClosed.exists_pow_nat_eq D (by omega : 0 < m + 2)`. Rewrite using `[utOf_sub_mainD _ (m + 2) hs _ _ Vec h x D hD0]`. Establish `hKcj` using `fun j hj => okG_qq S.G.r hg b (m + 2) hs K x D hx hD j hj`. Establish `hyy` using `kernel_PPt hGN S p f χ n v ε hg b (m + 2) hb hs hi a h hh hloc x D hx hD0 Bf Φ Kc hKcj hsz hker`.

Establish `hle` using `norm_sum_le_of_form (KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + (m + 2) - 1) a) Vec hVec Bf Cp hCp hBf (Finset.insertNone (G.rootSet (m + 2) D)) (aCo (PBL.setC S p (PBASM.cutSeq S p f χ n)) (m + 2) (KB.dlB (PBL.setC S p (PBASM.cutSeq S p f χ n)) (b + (m + 2) - 1) 1) ( …`. Establish `hcs` using `conjSum_eq (V := V) (PBL.setC S p (PBASM.cutSeq S p f χ n)) hg b m (KB.dlB (PBL.setC S p (PBASM.cutSeq S p f χ n)) (b + (m + 2) - 1) 1) (KB.dlB (PBL.setC S p (PBASM.cutSeq S p f χ n)) b (m + 2)) μ₀ Φ (U.Mlev S.G.k (S.G.r - (b + (m + 2) - 1))) x D hx hD0 (fun j => lamP S v a (b + …`. Establish `hT0 : GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹ ≠ 0` using `fs_ne_zero _ hg _ _ (inv_ne_zero hx)`. Establish `hg'` using `hgerm _ _ hT0 ⟨D, hD, (cD_eq S.G.r b (m + 2) hs x D hx).symm⟩`. Establish `hle2` using `hle.trans_eq (congrArg (fun X => Cp * ‖X‖) hcs)`.

Simplify using `only [norm_smul, Complex.norm_real, Real.norm_eq_abs] at hle2`. Establish `hnT : ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹‖ = ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) 1‖ * ‖x‖⁻¹`. Rewrite using `[fs_eq, norm_mul, norm_inv]`. Use `hle2.trans ?_` and prove the remaining obligations. Establish `hμ0 : 0 ≤ |μ₀|` using `abs_nonneg _`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hnT]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem germRateLowB_of (hGP : GermPlace) (hGN : GNSetC) (hGC : GermConst) : GermRateSplit.GermRateLowB := by
  intro _hA Cb
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  obtain ⟨hg1, hg2, -, hχ, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB
  obtain ⟨-, -, -, hf, -⟩ := hv v
  have hg : (0 : ℝ) < (S.g : ℝ) := by unfold C.HidaSetting.g; exact_mod_cast Nat.mul_pos hg1 hg2
  intro ε hε b s hb hs hbs a _ha H _ _ _ Vec hVec
  refine ⟨1, fun _ => 1, by simp, fun _ => by simp, continuousOn_const, ?_⟩
  intro h hh K hK hK0
  have hr : (PBL.setC S p (PBASM.cutSeq S p f χ n)).G.r = S.G.r := rfl
  have hi : b + s - 1 ≤ S.G.r := by omega
  by_cases hloc : ∀ y ∈ h, 1 ≤ y.1 ∧ y.2 ≠ 0
  swap
  ·
    refine ⟨0, fun x _ Dv hD => ?_⟩
    have hD0 : Dv ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
    rw [utOf_sub_mainD _ s hs _ _ Vec h x Dv hD0]
    have hz : ∀ j, Vec (PPt s h x Dv j) = 0 := by
      intro j
      have hnl : ¬ D.IsLocPt (PPt s h x Dv j) (b + s - 1) := by
        intro hl; apply hloc; intro y hy; exact hl.1 y (by cases j <;> simp [PPt, hy])
      have h0 := gN_setC_zero S p (PBASM.cutSeq S p f χ n) hg v ε (b + s - 1) a _ (PPt s h x Dv j) hnl
      rw [hVec] at h0
      exact inner_self_eq_zero.1 h0
    simp [hz]
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have hsz : D.ptSize (D.toStd S.G.r (S.g : ℝ) 1 h) + (m + 2 - 2 + 2) = b + (m + 2) - 1 := by
    rw [ptSize_toStd, hh]; omega
  have hlocStd : D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 h) (D.ptSize (D.toStd S.G.r (S.g : ℝ) 1 h)) :=
    (isLocPt_toStdD _ hg 1 h _).2 ⟨hloc, (ptSize_toStd _ _ 1 h).symm⟩
  set Kc : Set ℂ := (fun D => kapD S.G.r (S.g : ℝ) b (m + 2) * D) '' K with hKcdef
  have hKc : IsCompact Kc := hK.image (continuous_const.mul continuous_id)
  have hKc0 : (0 : ℂ) ∉ Kc := by
    rintro ⟨D, hD, hD0⟩
    have := mul_eq_zero.1 hD0
    rcases this with h1 | h1
    · exact kapD_ne _ hg _ _ h1
    · exact hK0 (h1 ▸ hD)
  obtain ⟨V, i1, i2, i3, Bf, Φ, Cp, Cst, hCp, hBf, hker, hgerm⟩ :=
    hGP (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v).T (M.sgn (D.parOf S v) (p v).l0) a
      (fun g => PBASM.cutN n g • f v g) χ ε (D.toStd S.G.r (S.g : ℝ) 1 h) (m + 2 - 2) (b + (m + 2) - 1) hi hsz
      (cutN_smooth hf n) ⟨_, cutN_supp (f v) n⟩ hχ hε (p v).hl.2.2 hlocStd Kc hKc hKc0
  obtain ⟨μ₀, hμ⟩ := hGC E Wp Wq (PBL.setC S p (PBASM.cutSeq S p f χ n)) v a b (m + 2) hg1 hg2 hb hs hi h hh
  refine ⟨Cp * |μ₀| * Cst * ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) 1‖, fun x hx D hD => ?_⟩
  have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
  obtain ⟨z0, hz0⟩ := IsAlgClosed.exists_pow_nat_eq D (by omega : 0 < m + 2)
  rw [utOf_sub_mainD _ (m + 2) hs _ _ Vec h x D hD0]
  have hKcj := fun j hj => okG_qq S.G.r hg b (m + 2) hs K x D hx hD j hj
  have hyy := kernel_PPt hGN S p f χ n v ε hg b (m + 2) hb hs hi a h hh hloc x D hx hD0 Bf Φ Kc hKcj hsz hker
  have hle := norm_sum_le_of_form (KB.gN (PBL.setC S p (PBASM.cutSeq S p f χ n)) v ε (b + (m + 2) - 1) a) Vec hVec
    Bf Cp hCp hBf (Finset.insertNone (G.rootSet (m + 2) D))
    (aCo (PBL.setC S p (PBASM.cutSeq S p f χ n)) (m + 2)
      (KB.dlB (PBL.setC S p (PBASM.cutSeq S p f χ n)) (b + (m + 2) - 1) 1)
      (KB.dlB (PBL.setC S p (PBASM.cutSeq S p f χ n)) b (m + 2)) x) (PPt (m + 2) h x D) _ hyy
  have hcs := conjSum_eq (V := V) (PBL.setC S p (PBASM.cutSeq S p f χ n)) hg b m
    (KB.dlB (PBL.setC S p (PBASM.cutSeq S p f χ n)) (b + (m + 2) - 1) 1)
    (KB.dlB (PBL.setC S p (PBASM.cutSeq S p f χ n)) b (m + 2)) μ₀ Φ
    (U.Mlev S.G.k (S.G.r - (b + (m + 2) - 1))) x D hx hD0
    (fun j => lamP S v a (b + (m + 2) - 1) (PPt (m + 2) h x D j)) (hμ x D z0 hx hD0 hz0).1
    (fun z hz => (hμ x D z hx hD0 ((mem_rootSet4 (by omega)).1 hz)).2)
  have hT0 : GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹ ≠ 0 := fs_ne_zero _ hg _ _ (inv_ne_zero hx)
  have hg' := hgerm _ _ hT0 ⟨D, hD, (cD_eq S.G.r b (m + 2) hs x D hx).symm⟩
  have hle2 := hle.trans_eq (congrArg (fun X => Cp * ‖X‖) hcs)
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs] at hle2
  have hnT : ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹‖ = ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) 1‖ * ‖x‖⁻¹ := by
    rw [fs_eq, norm_mul, norm_inv]
  refine hle2.trans ?_
  have hμ0 : 0 ≤ |μ₀| := abs_nonneg _
  calc Cp * (|μ₀| * ‖_‖) ≤ Cp * (|μ₀| * (Cst * ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) x⁻¹‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg' hμ0) hCp
    _ = Cp * |μ₀| * Cst * ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (m + 1) 1‖ * ‖x‖⁻¹ := by
        rw [hnT]; ring

end final

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FormNormSumIdentities.germRateLowB_of`.
-/
theorem Formalism.FourierDecayAlt.P.pb_germRateLowB_of_parts :
    Formalism.FourierDecayAlt.P.FormNormSumIdentities.GermPlace → Formalism.FourierDecayAlt.P.FormNormSumIdentities.GNSetC → Formalism.FourierDecayAlt.P.FormNormSumIdentities.GermConst →
      Formalism.FourierDecayAlt.P.GermRateSplit.GermRateLowB :=
  Formalism.FourierDecayAlt.P.FormNormSumIdentities.germRateLowB_of
