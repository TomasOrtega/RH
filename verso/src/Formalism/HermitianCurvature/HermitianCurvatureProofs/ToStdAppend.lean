import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNegBetaL

namespace Formalism.FourierDecayAlt.P.GermFibreKernels

open Formalism.FourierDecayAlt NumberField

noncomputable section

def fs (r : ℕ) (g : ℝ) (b s : ℕ) (t : ℂ) : ℂ :=
  (((g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1) * t

/- English proof (translation)
The claim follows from `| [], Q, b => by simp [D.toStd, D.ptSize] | (s, t) :: rest, Q, b => by have ih := toStd_append' r g rest Q (b + s) simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]`.
-/
theorem toStd_append' (r : ℕ) (g : ℝ) : ∀ (P Q : C.LPt) (b : ℕ),
    D.toStd r g b (P ++ Q) = D.toStd r g b P ++ D.toStd r g (b + D.ptSize P) Q
  | [], Q, b => by simp [D.toStd, D.ptSize]
  | (s, t) :: rest, Q, b => by
    have ih := toStd_append' r g rest Q (b + s)
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[toStd_append']`. Simplify using `[D.toStd, fs]`. Rewrite using `[toStd_append']`. Simplify using `[D.toStd, fs]`.
-/
theorem toStd_germPts (r : ℕ) (g : ℝ) (h : C.LPt) (s : ℕ) (t c z : ℂ) :
    D.toStd r g 1 (h ++ [(s - 1, t), (1, c)]) =
      D.toStd r g 1 h ++ [(s - 1, fs r g (1 + D.ptSize h) (s - 1) t), (1, fs r g (1 + D.ptSize h + (s - 1)) 1 c)] ∧
    D.toStd r g 1 (h ++ [(s, z)]) = D.toStd r g 1 h ++ [(s, fs r g (1 + D.ptSize h) s z)] := by
  constructor
  · rw [toStd_append']
    simp [D.toStd, fs]
  · rw [toStd_append']
    simp [D.toStd, fs]

/- English proof (translation)
Check the signs of the components of the expression.
-/
theorem lam_pos (g : ℝ) (hg : 0 < g) (n : ℤ) : 0 < (g / (2 * Real.pi)) ^ n := by positivity

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, s = m + 2` from `⟨s - 2, by omega⟩`. Establish `e1 : m + 2 - 1 = m + 1` using `by omega`. Establish `e2 : m + 1 - 1 = m` using `by omega`. Simplify using `only [e1]`. Unfold `fs`.

Simplify using `only [e1, e2, Nat.sub_self, pow_zero, mul_one]`. Use `set q := g / (2 * Real.pi) with hq`. Establish `hq0 : q ≠ 0` using `(div_pos hg (by positivity)).ne'`. Use `set L3 := ((q ^ S6.nuBlock (r : ℤ) (b : ℤ) ((m + 2 : ℕ) : ℤ) : ℝ) : ℂ) with hL3d`. Use `set L2 := ((q ^ S6.nuBlock (r : ℤ) ((b + (m + 1) : ℕ) : ℤ) ((1 : ℕ) : ℤ) : ℝ) : ℂ) with hL2d`.

Use `set L1 := ((q ^ S6.nuBlock (r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) with hL1d`. Establish `hL : L3 ^ (m + 2) = L2 * L1 ^ (m + 1)`. Rewrite using `[hL3d, hL2d, hL1d, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]`. Use `congr 1`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq0]`.

Use `congr 1`. Unfold `S6.nuBlock`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hI : (Complex.I ^ (m + 1)) ^ (m + 2) = (-1) ^ (m + 2 + 1) * (Complex.I ^ m) ^ (m + 1)`.

Rewrite using `[← pow_mul, ← pow_mul]`. Establish `: (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1)` using `by ring`. Rewrite using `[this, pow_add, pow_mul Complex.I 2, Complex.I_sq]`. Establish `h3 : (-1 : ℂ) ^ (m + 2 + 1) = (-1) ^ (m + 1)`. Rewrite using `[show m + 2 + 1 = (m + 1) + 2 by ring, pow_add]; norm_num`.

Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hL3 : L3 ≠ 0` using `Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ hq0)`. Use `set K := L3 ^ (m + 2) * (Complex.I ^ (m + 1)) ^ (m + 2) with hK`. Establish `eL : (L3 * Complex.I ^ (m + 1) * z) ^ (m + 2) = K * z ^ (m + 2)` using `by rw [hK]; ring`.

Establish `eR : (-1) ^ (m + 2 + 1) * (L2 * c * (L1 * Complex.I ^ m * t) ^ (m + 1)) = K * (c * t ^ (m + 1))`. Rewrite using `[hK, hI, hL]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eL, eR]`. Establish `h0 : K ≠ 0` using `mul_ne_zero (pow_ne_zero _ hL3) (pow_ne_zero _ (pow_ne_zero _ Complex.I_ne_zero))`.

Conclude with `mul_right_inj' h0`.
-/
theorem roots_std (r : ℕ) (g : ℝ) (hg : 0 < g) (b s : ℕ) (hs : 2 ≤ s) (t c z : ℂ) :
    fs r g b s z ^ s = (-1) ^ (s + 1) * (fs r g (b + (s - 1)) 1 c * fs r g b (s - 1) t ^ (s - 1)) ↔
      z ^ s = c * t ^ (s - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  simp only [e1]
  unfold fs
  simp only [e1, e2, Nat.sub_self, pow_zero, mul_one]
  set q := g / (2 * Real.pi) with hq
  have hq0 : q ≠ 0 := (div_pos hg (by positivity)).ne'
  set L3 := ((q ^ S6.nuBlock (r : ℤ) (b : ℤ) ((m + 2 : ℕ) : ℤ) : ℝ) : ℂ) with hL3d
  set L2 := ((q ^ S6.nuBlock (r : ℤ) ((b + (m + 1) : ℕ) : ℤ) ((1 : ℕ) : ℤ) : ℝ) : ℂ) with hL2d
  set L1 := ((q ^ S6.nuBlock (r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) with hL1d
  have hL : L3 ^ (m + 2) = L2 * L1 ^ (m + 1) := by
    rw [hL3d, hL2d, hL1d, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq0]
    congr 1
    unfold S6.nuBlock
    push_cast; ring
  have hI : (Complex.I ^ (m + 1)) ^ (m + 2) = (-1) ^ (m + 2 + 1) * (Complex.I ^ m) ^ (m + 1) := by
    rw [← pow_mul, ← pow_mul]
    have : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
    rw [this, pow_add, pow_mul Complex.I 2, Complex.I_sq]
    have h3 : (-1 : ℂ) ^ (m + 2 + 1) = (-1) ^ (m + 1) := by
      rw [show m + 2 + 1 = (m + 1) + 2 by ring, pow_add]; norm_num
    rw [h3]; ring
  have hL3 : L3 ≠ 0 := Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ hq0)
  set K := L3 ^ (m + 2) * (Complex.I ^ (m + 1)) ^ (m + 2) with hK
  have eL : (L3 * Complex.I ^ (m + 1) * z) ^ (m + 2) = K * z ^ (m + 2) := by rw [hK]; ring
  have eR : (-1) ^ (m + 2 + 1) * (L2 * c * (L1 * Complex.I ^ m * t) ^ (m + 1)) = K * (c * t ^ (m + 1)) := by
    rw [hK, hI, hL]; ring
  rw [eL, eR]
  have h0 : K ≠ 0 := mul_ne_zero (pow_ne_zero _ hL3) (pow_ne_zero _ (pow_ne_zero _ Complex.I_ne_zero))
  exact mul_right_inj' h0

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

/- English proof (translation)
Simplify using `[U.betaU, Formalism.QuantumDeterminants.cStd]`.
-/
theorem betaU_eq : U.betaU = 2 * Complex.I := by
  simp [U.betaU, Formalism.QuantumDeterminants.cStd]

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, s = m + 2` from `⟨s - 2, by omega⟩`. Establish `e1 : m + 2 - 1 = m + 1` using `by omega`. Establish `e2 : m + 1 - 1 = m` using `by omega`. Rewrite using `[← GermRealisation.psi_neg_betaL]`. Unfold `fs`.

Simplify using `only [e1, e2]`. Use `set q := (S.g : ℝ) / (2 * Real.pi) with hq`. Establish `hq0 : 0 < q` using `div_pos hg (by positivity)`. Establish `hL : q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 2 : ℕ) : ℤ) = q⁻¹ * q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ)`. Rewrite using `[← zpow_neg_one, ← zpow_add₀ hq0.ne']`.

Use `congr 1`. Unfold `S6.nuBlock`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hL1 : (q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) ≠ 0` using `(zpow_pos hq0 _).ne'`.

Rewrite using `[hL]`. Unfold `G.psi`. Use `congr 3`. Rewrite using `[betaU_eq]`. Unfold `GermRealisation.betaL`.

Establish `hq' : (q : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr hq0.ne'`. Establish `hL1' : ((q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr hL1`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr Real.pi_ne_zero`. Establish `hgc : ((S.g : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr hg.ne'`. Simplify using `only [Complex.ofReal_mul, Complex.ofReal_inv]`.

Generalize the expression as in `((q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) = L at hL1' ⊢`. Use `congr 1`. Rewrite using `[hq]`. Use `push_cast`. Rewrite using `[pow_succ]`.

Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem char_std (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < (S.g : ℝ)) (b s : ℕ) (hs : 2 ≤ s) (t z : ℂ) (ht : t ≠ 0) :
    G.psi U.betaU ((s : ℂ) * fs S.G.r (S.g : ℝ) b s z / fs S.G.r (S.g : ℝ) b (s - 1) t) =
      KB.psiL S (-((s : ℂ) * t⁻¹)) z := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [← GermRealisation.psi_neg_betaL]
  unfold fs
  simp only [e1, e2]
  set q := (S.g : ℝ) / (2 * Real.pi) with hq
  have hq0 : 0 < q := div_pos hg (by positivity)
  have hL : q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 2 : ℕ) : ℤ) =
      q⁻¹ * q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) := by
    rw [← zpow_neg_one, ← zpow_add₀ hq0.ne']
    congr 1
    unfold S6.nuBlock; push_cast; ring
  have hL1 : (q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) ≠ 0 := (zpow_pos hq0 _).ne'
  rw [hL]
  unfold G.psi
  congr 3
  rw [betaU_eq]
  unfold GermRealisation.betaL
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0.ne'
  have hL1' : ((q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hgc : ((S.g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  generalize ((q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) = L at hL1' ⊢
  congr 1
  rw [hq]
  push_cast
  rw [pow_succ]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end loc

end

end Formalism.FourierDecayAlt.P.GermFibreKernels
