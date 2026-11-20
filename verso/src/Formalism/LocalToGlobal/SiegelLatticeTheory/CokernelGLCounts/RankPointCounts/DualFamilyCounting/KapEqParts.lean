import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameZZEqNegT

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem spanLt_eq {n r : ℕ} (e : Fin r → Fin n → ℂ) (a : ℕ) :
    spanLt e a = Submodule.span ℂ (e '' {b | b.1 < a}) := rfl

/- English proof (translation)
Establish `h1` using `hN.1.1 b`. Rewrite `h1` using `[spanLt_eq]`. Establish `h2 : eV X v b ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS})` using `Submodule.subset_span ⟨b, b.2, rfl⟩`. Establish `h3 : Submodule.span ℂ (eV X v '' {c | c.1 < b.1}) ≤ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS})` using `Submodule.span_mono (Set.image_mono fun c _ => c.2)`. Establish `h4 : g *ᵥ eV X v b = (g - 1) *ᵥ eV X v b + eV X v b`.

Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]`. Rewrite using `[h4]`. Conclude with `Submodule.add_mem _ (h3 h1) h2`.
-/
theorem ge_mem {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ}
    (hN : InN (X.B.I.ε v) (eV X v) (zV X u v) g) (b : Fin D.R.rS) :
    g *ᵥ eV X v b ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS}) := by
  have h1 := hN.1.1 b
  rw [spanLt_eq] at h1
  have h2 : eV X v b ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS}) :=
    Submodule.subset_span ⟨b, b.2, rfl⟩
  have h3 : Submodule.span ℂ (eV X v '' {c | c.1 < b.1}) ≤
      Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS}) :=
    Submodule.span_mono (Set.image_mono fun c _ => c.2)
  have h4 : g *ᵥ eV X v b = (g - 1) *ᵥ eV X v b + eV X v b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  rw [h4]
  exact Submodule.add_mem _ (h3 h1) h2

/- English proof (translation)
Establish `hadd1 : ∀ a b z : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) (a + b) z = hJ (X.B.I.ε v) a z + hJ (X.B.I.ε v) b z`. Introduce `a b z`. Simplify using `only [hJ, star_add, add_dotProduct]`. Establish `hadd2 : ∀ a b z : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) z (a + b) = hJ (X.B.I.ε v) z a + hJ (X.B.I.ε v) z b`. Introduce `a b z`.

Simplify using `only [hJ, mulVec_add, dotProduct_add]`. Establish `hsm1 : ∀ (t : ℂ) (a z : Fin X.B.I.n → ℂ), hJ (X.B.I.ε v) (t • a) z = star t * hJ (X.B.I.ε v) a z`. Introduce `t a z`. Simplify using `only [hJ, star_smul, smul_dotProduct, smul_eq_mul]`. Establish `hsm2 : ∀ (t : ℂ) (a z : Fin X.B.I.n → ℂ), hJ (X.B.I.ε v) z (t • a) = t * hJ (X.B.I.ε v) z a`.

Introduce `t a z`. Simplify using `only [hJ, mulVec_smul, dotProduct_smul, smul_eq_mul]`. Establish `hz1 : ∀ z, hJ (X.B.I.ε v) 0 z = 0`. Introduce `z`. Simplify using `[hJ]`.

Establish `hz2 : ∀ z, hJ (X.B.I.ε v) z 0 = 0`. Introduce `z`. Simplify using `[hJ]`. Establish `key : ∀ w ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS}), hJ (X.B.I.ε v) w y = ∑ c, star (hJ (X.B.I.ε v) (fV X v c) w) * hJ (X.B.I.ε v) (eV X v c) y`. Introduce `w hw`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨b, -, rfl⟩` from `hw`. Rewrite using `[Finset.sum_eq_single b (fun c _ hc => by rw [fr_fe, if_neg hc, star_zero, zero_mul]) (fun h => absurd (Finset.mem_univ b) h), fr_fe, if_pos rfl, star_one, one_mul]`. Consider the case `zero => simp only [hz1, hz2, star_zero, zero_mul, Finset.sum_const_zero]`.

Consider the case `add a b _ _ ha hb`. Rewrite using `[hadd1, ha, hb, ← Finset.sum_add_distrib]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Rewrite using `[hadd2, star_add, add_mul]`.

Consider the case `smul t a _ ha`. Rewrite using `[hsm1, ha, Finset.mul_sum]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Rewrite using `[hsm2, star_mul', mul_assoc]`.

Establish `hg : g *ᵥ x = x + (g - 1) *ᵥ x`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]`. Rewrite using `[hg, hadd1, key _ hx]`.
-/
theorem pair_of_X {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ} {x : Fin X.B.I.n → ℂ}
    (hx : (g - 1) *ᵥ x ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS})) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε v) (g *ᵥ x) y = hJ (X.B.I.ε v) x y +
      ∑ c, star (hJ (X.B.I.ε v) (fV X v c) ((g - 1) *ᵥ x)) * hJ (X.B.I.ε v) (eV X v c) y := by
  have hadd1 : ∀ a b z : Fin X.B.I.n → ℂ,
      hJ (X.B.I.ε v) (a + b) z = hJ (X.B.I.ε v) a z + hJ (X.B.I.ε v) b z := by
    intro a b z
    simp only [hJ, star_add, add_dotProduct]
  have hadd2 : ∀ a b z : Fin X.B.I.n → ℂ,
      hJ (X.B.I.ε v) z (a + b) = hJ (X.B.I.ε v) z a + hJ (X.B.I.ε v) z b := by
    intro a b z
    simp only [hJ, mulVec_add, dotProduct_add]
  have hsm1 : ∀ (t : ℂ) (a z : Fin X.B.I.n → ℂ), hJ (X.B.I.ε v) (t • a) z = star t * hJ (X.B.I.ε v) a z := by
    intro t a z
    simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul]
  have hsm2 : ∀ (t : ℂ) (a z : Fin X.B.I.n → ℂ), hJ (X.B.I.ε v) z (t • a) = t * hJ (X.B.I.ε v) z a := by
    intro t a z
    simp only [hJ, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hz1 : ∀ z, hJ (X.B.I.ε v) 0 z = 0 := by
    intro z
    simp [hJ]
  have hz2 : ∀ z, hJ (X.B.I.ε v) z 0 = 0 := by
    intro z
    simp [hJ]
  have key : ∀ w ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS}),
      hJ (X.B.I.ε v) w y = ∑ c, star (hJ (X.B.I.ε v) (fV X v c) w) * hJ (X.B.I.ε v) (eV X v c) y := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, -, rfl⟩ := hw
      rw [Finset.sum_eq_single b (fun c _ hc => by rw [fr_fe, if_neg hc, star_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ b) h), fr_fe, if_pos rfl, star_one, one_mul]
    | zero => simp only [hz1, hz2, star_zero, zero_mul, Finset.sum_const_zero]
    | add a b _ _ ha hb =>
      rw [hadd1, ha, hb, ← Finset.sum_add_distrib]
      congr 1
      funext c
      rw [hadd2, star_add, add_mul]
    | smul t a _ ha =>
      rw [hsm1, ha, Finset.mul_sum]
      congr 1
      funext c
      rw [hsm2, star_mul', mul_assoc]
  have hg : g *ᵥ x = x + (g - 1) *ᵥ x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  rw [hg, hadd1, key _ hx]

/- English proof (translation)
Establish `h : ∀ i, kapV X u v s i = kapV X u v s' i` using `fun i => congrFun hk (v, i)`. Establish `hc : ∀ z z' : ℂ, (∀ t, reim z t = reim z' t) → z = z'` using `fun z z' H => Complex.ext (by simpa [reim] using H false) (by simpa [reim] using H true)`. Conclude with `⟨fun b a hba => hc _ _ (fun t => h (Sum.inl (Sum.inl (⟨(b, a), hba⟩, t)))), fun b => hc _ _ (fun t => h (Sum.inl (Sum.inr (b, t)))), fun b j => hc _ _ (fun t => h (Sum.inr (Sum.inl (b, j, t)))), fun b a hba => hc _ _ (fun t => h (Sum.inr (Sum.inr (Sum.inl (⟨(b, a), hba⟩, t))))), …`.
-/
theorem kap_eq_parts {s s' : X.B.I.Ginf} (hk : kap X u s = kap X u s') :
    (∀ b a : Fin D.R.rS, b < a → xMat X v s b a = xMat X v s' b a) ∧
    (∀ b, yVec X u v s b = yVec X u v s' b) ∧
    (∀ b j, phiMat X u v s b j = phiMat X u v s' b j) ∧
    (∀ b a : Fin D.R.rS, b < a → (mMat X v s b a - star (mMat X v s a b)) / 2 =
      (mMat X v s' b a - star (mMat X v s' a b)) / 2) ∧
    ∀ a, (mMat X v s a a).im = (mMat X v s' a a).im := by
  have h : ∀ i, kapV X u v s i = kapV X u v s' i := fun i => congrFun hk (v, i)
  have hc : ∀ z z' : ℂ, (∀ t, reim z t = reim z' t) → z = z' := fun z z' H =>
    Complex.ext (by simpa [reim] using H false) (by simpa [reim] using H true)
  exact ⟨fun b a hba => hc _ _ (fun t => h (Sum.inl (Sum.inl (⟨(b, a), hba⟩, t)))),
    fun b => hc _ _ (fun t => h (Sum.inl (Sum.inr (b, t)))),
    fun b j => hc _ _ (fun t => h (Sum.inr (Sum.inl (b, j, t)))),
    fun b a hba => hc _ _ (fun t => h (Sum.inr (Sum.inr (Sum.inl (⟨(b, a), hba⟩, t))))),
    fun a => h (Sum.inr (Sum.inr (Sum.inr a)))⟩

/- English proof (translation)
Establish `hN : InN (X.B.I.ε v) (eV X v) (zV X u v) (uMat (s v))` using `hs v`. Establish `hN' : InN (X.B.I.ε v) (eV X v) (zV X u v) (uMat (s' v))` using `hs' v`. Establish `hU : Formalism.REAL.inUJ (X.B.I.ε v) (uMat (s v))` using `(s v).2`. Establish `hU' : Formalism.REAL.inUJ (X.B.I.ε v) (uMat (s' v))` using `(s' v).2`. Take `⟨cx, cy, cphi, cskew, cdiag⟩` from `kap_eq_parts X u v hk`.

Establish `he : ∀ a, uMat (s v) *ᵥ eV X v a = uMat (s' v) *ᵥ eV X v a`. Introduce `a`. Establish `d1` using `hN.1.1 a`. Establish `d1'` using `hN'.1.1 a`. Rewrite `d1`, `d1'` using `[spanLt_eq]`.

Apply `hJ_test (X.B.I.ε v) (fam X u v) (fam_span X u v)` to reduce the goal to its premises. Apply the tactic sequence `rintro (b | b | j | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, span_perp _ _ _ _ (fun c _ => fr_ee X v b c) d1, span_perp _ _ _ _ (fun c _ => fr_ee X v b c) d1']`. Distinguish the cases in `hba : b < a`. Conclude with `cx b a hba`.

Establish `hz : ∀ c ∈ {c : Fin D.R.rS | c.1 < a.1}, hJ (X.B.I.ε v) (fV X v b) (eV X v c) = 0`. Introduce `c hc`. Rewrite using `[fr_fe, if_neg]`. Introduce and unpack `rfl`. Conclude with `hba hc`.

Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, span_perp _ _ _ _ hz d1, span_perp _ _ _ _ hz d1']`. Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, span_perp _ _ _ _ (fun c _ => fr_we X u v j c) d1, span_perp _ _ _ _ (fun c _ => fr_we X u v j c) d1']`. Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, span_perp _ _ _ _ (fun c _ => fr_ze X u v c) d1, span_perp _ _ _ _ (fun c _ => fr_ze X u v c) d1']`. Establish `hzX : (uMat (s v) - 1) *ᵥ zV X u v ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS})` using `hN.1.2`. Establish `hzX' : (uMat (s' v) - 1) *ᵥ zV X u v ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS})` using `hN'.1.2`.

Establish `hwX : ∀ j, (uMat (s v) - 1) *ᵥ X.wfr u v j ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS})` using `fun j => hN.2 _ fun a => fr_ew X u v a j`. Establish `hwX' : ∀ j, (uMat (s' v) - 1) *ᵥ X.wfr u v j ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS})` using `fun j => hN'.2 _ fun a => fr_ew X u v a j`. Establish `hX1 : ∀ x, (x ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS})) → ∀ y, (∀ c, hJ (X.B.I.ε v) y (eV X v c) = 0) → hJ (X.B.I.ε v) y x = 0` using `fun x hx y hy => span_perp _ _ _ _ (fun c _ => hy c) hx`. Establish `hz : uMat (s v) *ᵥ zV X u v = uMat (s' v) *ᵥ zV X u v`. Apply `hJ_test (X.B.I.ε v) (fam X u v) (fam_span X u v)` to reduce the goal to its premises.

Apply the tactic sequence `rintro (b | b | j | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, hX1 _ hzX _ (fr_ee X v b), hX1 _ hzX' _ (fr_ee X v b)]`. Conclude with `cy b`. Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, hX1 _ hzX _ (fr_we X u v j), hX1 _ hzX' _ (fr_we X u v j)]`. Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, hX1 _ hzX _ (fr_ze X u v), hX1 _ hzX' _ (fr_ze X u v)]`.

Establish `hw : ∀ j, uMat (s v) *ᵥ X.wfr u v j = uMat (s' v) *ᵥ X.wfr u v j`. Introduce `j`. Apply `hJ_test (X.B.I.ε v) (fam X u v) (fam_span X u v)` to reduce the goal to its premises. Apply the tactic sequence `rintro (b | b | i | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, hX1 _ (hwX j) _ (fr_ee X v b), hX1 _ (hwX' j) _ (fr_ee X v b)]`.

Conclude with `cphi b j`. Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, hX1 _ (hwX j) _ (fr_we X u v i), hX1 _ (hwX' j) _ (fr_we X u v i)]`. Rewrite using `[mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa, hX1 _ (hwX j) _ (fr_ze X u v), hX1 _ (hwX' j) _ (fr_ze X u v)]`. Establish `hXfull : ∀ b a, xMat X v s b a = xMat X v s' b a`. Introduce `b a`.

Use `show hJ _ _ (uMat (s v) *ᵥ eV X v a) = hJ _ _ (uMat (s' v) *ᵥ eV X v a)`. Rewrite using `[he a]`. Establish `hxX : xMat X v s' = xMat X v s`. Use extensionality with `b a`. Conclude with `(hXfull b a).symm`.

Establish `hexp : ∀ (b : Fin D.R.rS) y, hJ (X.B.I.ε v) (uMat (s v) *ᵥ eV X v b) y = ∑ c, star (xMat X v s c b) * hJ (X.B.I.ε v) (eV X v c) y`. Introduce `b y`. Use `conv_lhs => rw [span_recon (X.B.I.ε v) (eV X v) (fV X v) _ (fr_fe X v) (ge_mem X u v hN b)]`. Rewrite using `[hJsuml]`. Both sides reduce to the same expression.

Take `⟨αm, hαm⟩ : ∃ αm : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ, ∀ c a, αm c a = hJ (X.B.I.ε v) (eV X v c) (uMat (s v) *ᵥ fV X v a)` from `⟨fun c a => hJ (X.B.I.ε v) (eV X v c) (uMat (s v) *ᵥ fV X v a), fun _ _ => rfl⟩`. Establish `hXα : (xMat X v s)ᴴ * αm = 1`. Use extensionality with `b a`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.conjTranspose_apply, hαm]`.

Rewrite using `[← hexp b, Formalism.L2.SG.Pf.hJ_inUJ _ hU, fr_ef]`. Establish `hαX : αm * (xMat X v s)ᴴ = 1`. Rewrite using `[← Matrix.inv_eq_right_inv hXα]`. Conclude with `Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse hXα)`. Establish `hαX' : αmᴴ * xMat X v s = 1`.

Establish `h` using `congrArg Matrix.conjTranspose hXα`. Rewrite `h` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one]`. Then use the resulting hypothesis. Establish `hXαh : xMat X v s * αmᴴ = 1`. Rewrite using `[← Matrix.inv_eq_left_inv hαX']`. Conclude with `Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hαX')`.

Establish `hinv : (xMat X v s)⁻¹ = αmᴴ` using `Matrix.inv_eq_left_inv hαX'`. Establish `key : ∀ w : Fin D.R.rS → ℂ, (xMat X v s)ᴴ *ᵥ w = 0 → w = 0`. Introduce `w hw`. Combine the equalities or inequalities in the displayed calculation. Take `⟨d, hd⟩ : ∃ d : Fin D.R.rS → Fin X.B.I.n → ℂ, ∀ a, d a = uMat (s v) *ᵥ fV X v a - uMat (s' v) *ᵥ fV X v a` from `⟨fun a => uMat (s v) *ᵥ fV X v a - uMat (s' v) *ᵥ fV X v a, fun _ => rfl⟩`.

Establish `hgd : ∀ x, uMat (s v) *ᵥ x = uMat (s' v) *ᵥ x → ∀ a, hJ (X.B.I.ε v) (uMat (s v) *ᵥ x) (d a) = 0`. Introduce `x hx a`. Rewrite using `[hd a, hJsub, Formalism.L2.SG.Pf.hJ_inUJ _ hU, hx, Formalism.L2.SG.Pf.hJ_inUJ _ hU', sub_self]`. Establish `hde : ∀ a c, hJ (X.B.I.ε v) (eV X v c) (d a) = 0`. Introduce `a`.

Establish `hXu : (xMat X v s)ᴴ *ᵥ (fun c => hJ (X.B.I.ε v) (eV X v c) (d a)) = 0`. Use function extensionality and compare the values at `b`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.zero_apply]`. Rewrite using `[← hexp b]`. Conclude with `hgd _ (he b) a`.

Introduce `c`. Conclude with `congrFun (key _ hXu) c`. Establish `hdz : ∀ a, hJ (X.B.I.ε v) (zV X u v) (d a) = 0`. Introduce `a`. Establish `h` using `hgd _ hz a`.

Rewrite `h` using `[pair_of_X X v hzX]`. Simplify `h` using `[hde a]`. Establish `hdw : ∀ a j, hJ (X.B.I.ε v) (X.wfr u v j) (d a) = 0`. Introduce `a j`. Establish `h` using `hgd _ (hw j) a`.

Rewrite `h` using `[pair_of_X X v (hwX j)]`. Simplify `h` using `[hde a]`. Take `⟨Δ, hΔ⟩ : ∃ Δ : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ, ∀ b a, Δ b a = hJ (X.B.I.ε v) (fV X v b) (d a)` from `⟨fun b a => hJ (X.B.I.ε v) (fV X v b) (d a), fun _ _ => rfl⟩`. Establish `hdrec : ∀ a, d a = ∑ c, Δ c a • eV X v c`. Introduce `a`.

Apply `hJ_test (X.B.I.ε v) (fam X u v) (fam_span X u v)` to reduce the goal to its premises. Apply the tactic sequence `rintro (b | b | j | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr, hJsumr]`. Rewrite using `[hde a b]`. Simplify using `[fr_ee]`. Rewrite using `[← hΔ b a]`.

Simplify using `only [fr_fe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[hdw a j]`. Simplify using `[fr_we]`. Rewrite using `[hdz a]`. Simplify using `[fr_ze]`.

Establish `hsk : ∀ b a, (αmᴴ * Δ) b a + (Δᴴ * αm) b a = 0`. Introduce `b a`. Establish `h0 : hJ (X.B.I.ε v) (uMat (s' v) *ᵥ fV X v b) (uMat (s' v) *ᵥ fV X v a) = 0`. Rewrite using `[Formalism.L2.SG.Pf.hJ_inUJ _ hU', fr_ff]`. Establish `e1 : ∀ c, uMat (s' v) *ᵥ fV X v c = uMat (s v) *ᵥ fV X v c - d c`.

Introduce `c`. Rewrite using `[hd c, sub_sub_cancel]`. Rewrite `h0` using `[e1 b, e1 a, hJsubl, hJsub, hJsub]`. Establish `hff : hJ (X.B.I.ε v) (uMat (s v) *ᵥ fV X v b) (uMat (s v) *ᵥ fV X v a) = 0`. Rewrite using `[Formalism.L2.SG.Pf.hJ_inUJ _ hU, fr_ff]`.

Establish `t1 : hJ (X.B.I.ε v) (d b) (uMat (s v) *ᵥ fV X v a) = (Δᴴ * αm) b a`. Rewrite using `[hdrec b, hJsuml, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_apply, hαm]`. Establish `t2 : hJ (X.B.I.ε v) (uMat (s v) *ᵥ fV X v b) (d a) = (αmᴴ * Δ) b a`.

Rewrite using `[hdrec a, hJsumr, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_apply, hαm, hJswap (X.B.I.ε v) (eV X v c) (uMat (s v) *ᵥ fV X v b), mul_comm]`. Establish `t3 : hJ (X.B.I.ε v) (d b) (d a) = 0`. Rewrite using `[hdrec b, hJsuml]`.

Simplify using `[hde a]`. Rewrite `h0` using `[hff, t1, t2, t3]`. Take the linear combination `-h0`. Establish `hNm : mMat X v s - mMat X v s' = αmᴴ * Δ`. Unfold `mMat`.

Rewrite using `[hxX, hinv, ← Matrix.mul_sub]`. Use `congr 1`. Use extensionality with `b a`. Rewrite using `[Matrix.sub_apply, hΔ, hd, hJsub]`. Both sides reduce to the same expression.

Establish `hNe : ∀ b a, (αmᴴ * Δ) b a = mMat X v s b a - mMat X v s' b a`. Introduce `b a`. Rewrite using `[← hNm, Matrix.sub_apply]`. Establish `hstar : Δᴴ * αm = (αmᴴ * Δ)ᴴ`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`.

Establish `hskew : ∀ b a, (αmᴴ * Δ) b a + star ((αmᴴ * Δ) a b) = 0`. Introduce `b a`. Establish `h` using `hsk b a`. Rewrite `h` using `[hstar, Matrix.conjTranspose_apply]`. Conclude with `h`.

Establish `hlt : ∀ b a : Fin D.R.rS, b < a → (αmᴴ * Δ) b a = 0`. Introduce `b a hba`. Establish `h1` using `hskew b a`. Establish `h2` using `cskew b a hba`. Rewrite `h1` using `[hNe, hNe, star_sub]`.

Rewrite using `[hNe]`. Take the linear combination `(h1 + 2 * h2) / 2`. Establish `hN0 : ∀ b a, (αmᴴ * Δ) b a = 0`. Introduce `b a`. Break down `lt_trichotomy b a with hba | rfl | hab` into its components or cases.

Conclude with `hlt b a hba`. Establish `h1` using `hskew b b`. Apply `Complex.ext` to reduce the goal to its premises. Establish `h3` using `congrArg Complex.re h1`. Simplify using `only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h3`.

Simplify using `only [Complex.zero_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hNe, Complex.sub_im, cdiag b, sub_self, Complex.zero_im]`. Establish `h1` using `hskew b a`. Rewrite `h1` using `[hlt a b hab, star_zero, add_zero]`.

Conclude with `h1`. Establish `hΔ0 : Δ = 0`. Establish `hz0 : αmᴴ * Δ = 0` using `Matrix.ext fun b a => by rw [hN0 b a]; rfl`. Combine the equalities or inequalities in the displayed calculation. Establish `hf : ∀ a, uMat (s v) *ᵥ fV X v a = uMat (s' v) *ᵥ fV X v a`.

Introduce `a`. Establish `h0 : d a = 0`. Rewrite using `[hdrec a]`. Simplify using `[hΔ0]`. Rewrite `h0` using `[hd a]`.

Conclude with `sub_eq_zero.1 h0`. Establish `hall : ∀ i, uMat (s v) *ᵥ fam X u v i = uMat (s' v) *ᵥ fam X u v i`. Apply the tactic sequence `rintro (b | b | j | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr]`. Use `exacts [he b, hf b, hw j, hz]`. Conclude with `Matrix.toLin'.injective (LinearMap.ext_on_range (fam_span X u v) fun i => by`.

Simplify `hall i)` using `[Matrix.toLin'_apply]`.
-/
theorem inj_at {s s' : X.B.I.Ginf} (hs : s ∈ X.NinfU u) (hs' : s' ∈ X.NinfU u)
    (hk : kap X u s = kap X u s') : uMat (s v) = uMat (s' v) := by
  have hN : InN (X.B.I.ε v) (eV X v) (zV X u v) (uMat (s v)) := hs v
  have hN' : InN (X.B.I.ε v) (eV X v) (zV X u v) (uMat (s' v)) := hs' v
  have hU : Formalism.REAL.inUJ (X.B.I.ε v) (uMat (s v)) := (s v).2
  have hU' : Formalism.REAL.inUJ (X.B.I.ε v) (uMat (s' v)) := (s' v).2
  obtain ⟨cx, cy, cphi, cskew, cdiag⟩ := kap_eq_parts X u v hk

  have he : ∀ a, uMat (s v) *ᵥ eV X v a = uMat (s' v) *ᵥ eV X v a := by
    intro a
    have d1 := hN.1.1 a
    have d1' := hN'.1.1 a
    rw [spanLt_eq] at d1 d1'
    apply hJ_test (X.B.I.ε v) (fam X u v) (fam_span X u v)
    rintro (b | b | j | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr]
    · rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
        span_perp _ _ _ _ (fun c _ => fr_ee X v b c) d1, span_perp _ _ _ _ (fun c _ => fr_ee X v b c) d1']
    · by_cases hba : b < a
      · exact cx b a hba
      · have hz : ∀ c ∈ {c : Fin D.R.rS | c.1 < a.1}, hJ (X.B.I.ε v) (fV X v b) (eV X v c) = 0 := by
          intro c hc
          rw [fr_fe, if_neg]
          rintro rfl
          exact hba hc
        rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
          span_perp _ _ _ _ hz d1, span_perp _ _ _ _ hz d1']
    · rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
        span_perp _ _ _ _ (fun c _ => fr_we X u v j c) d1, span_perp _ _ _ _ (fun c _ => fr_we X u v j c) d1']
    · rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
        span_perp _ _ _ _ (fun c _ => fr_ze X u v c) d1, span_perp _ _ _ _ (fun c _ => fr_ze X u v c) d1']
  have hzX : (uMat (s v) - 1) *ᵥ zV X u v ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS}) := hN.1.2
  have hzX' : (uMat (s' v) - 1) *ᵥ zV X u v ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS}) := hN'.1.2
  have hwX : ∀ j, (uMat (s v) - 1) *ᵥ X.wfr u v j ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS}) :=
    fun j => hN.2 _ fun a => fr_ew X u v a j
  have hwX' : ∀ j, (uMat (s' v) - 1) *ᵥ X.wfr u v j ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS}) :=
    fun j => hN'.2 _ fun a => fr_ew X u v a j
  have hX1 : ∀ x, (x ∈ Submodule.span ℂ (eV X v '' {c | c.1 < D.R.rS})) → ∀ y, (∀ c, hJ (X.B.I.ε v) y (eV X v c) = 0) →
      hJ (X.B.I.ε v) y x = 0 := fun x hx y hy => span_perp _ _ _ _ (fun c _ => hy c) hx
  have hz : uMat (s v) *ᵥ zV X u v = uMat (s' v) *ᵥ zV X u v := by
    apply hJ_test (X.B.I.ε v) (fam X u v) (fam_span X u v)
    rintro (b | b | j | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr]
    · rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
        hX1 _ hzX _ (fr_ee X v b), hX1 _ hzX' _ (fr_ee X v b)]
    · exact cy b
    · rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
        hX1 _ hzX _ (fr_we X u v j), hX1 _ hzX' _ (fr_we X u v j)]
    · rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
        hX1 _ hzX _ (fr_ze X u v), hX1 _ hzX' _ (fr_ze X u v)]
  have hw : ∀ j, uMat (s v) *ᵥ X.wfr u v j = uMat (s' v) *ᵥ X.wfr u v j := by
    intro j
    apply hJ_test (X.B.I.ε v) (fam X u v) (fam_span X u v)
    rintro (b | b | i | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr]
    · rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
        hX1 _ (hwX j) _ (fr_ee X v b), hX1 _ (hwX' j) _ (fr_ee X v b)]
    · exact cphi b j
    · rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
        hX1 _ (hwX j) _ (fr_we X u v i), hX1 _ (hwX' j) _ (fr_we X u v i)]
    · rw [mulVec_split (uMat (s v)), mulVec_split (uMat (s' v)), hJa, hJa,
        hX1 _ (hwX j) _ (fr_ze X u v), hX1 _ (hwX' j) _ (fr_ze X u v)]
  have hXfull : ∀ b a, xMat X v s b a = xMat X v s' b a := by
    intro b a
    show hJ _ _ (uMat (s v) *ᵥ eV X v a) = hJ _ _ (uMat (s' v) *ᵥ eV X v a)
    rw [he a]
  have hxX : xMat X v s' = xMat X v s := by
    ext b a
    exact (hXfull b a).symm
  have hexp : ∀ (b : Fin D.R.rS) y, hJ (X.B.I.ε v) (uMat (s v) *ᵥ eV X v b) y =
      ∑ c, star (xMat X v s c b) * hJ (X.B.I.ε v) (eV X v c) y := by
    intro b y
    conv_lhs => rw [span_recon (X.B.I.ε v) (eV X v) (fV X v) _ (fr_fe X v) (ge_mem X u v hN b)]
    rw [hJsuml]
    rfl
  obtain ⟨αm, hαm⟩ : ∃ αm : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ,
      ∀ c a, αm c a = hJ (X.B.I.ε v) (eV X v c) (uMat (s v) *ᵥ fV X v a) :=
    ⟨fun c a => hJ (X.B.I.ε v) (eV X v c) (uMat (s v) *ᵥ fV X v a), fun _ _ => rfl⟩
  have hXα : (xMat X v s)ᴴ * αm = 1 := by
    ext b a
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply, hαm]
    rw [← hexp b, Formalism.L2.SG.Pf.hJ_inUJ _ hU, fr_ef]
  have hαX : αm * (xMat X v s)ᴴ = 1 := by
    rw [← Matrix.inv_eq_right_inv hXα]
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse hXα)
  have hαX' : αmᴴ * xMat X v s = 1 := by
    have h := congrArg Matrix.conjTranspose hXα
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
  have hXαh : xMat X v s * αmᴴ = 1 := by
    rw [← Matrix.inv_eq_left_inv hαX']
    exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hαX')
  have hinv : (xMat X v s)⁻¹ = αmᴴ := Matrix.inv_eq_left_inv hαX'
  have key : ∀ w : Fin D.R.rS → ℂ, (xMat X v s)ᴴ *ᵥ w = 0 → w = 0 := by
    intro w hw
    calc w = (αm * (xMat X v s)ᴴ) *ᵥ w := by rw [hαX, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  obtain ⟨d, hd⟩ : ∃ d : Fin D.R.rS → Fin X.B.I.n → ℂ,
      ∀ a, d a = uMat (s v) *ᵥ fV X v a - uMat (s' v) *ᵥ fV X v a :=
    ⟨fun a => uMat (s v) *ᵥ fV X v a - uMat (s' v) *ᵥ fV X v a, fun _ => rfl⟩
  have hgd : ∀ x, uMat (s v) *ᵥ x = uMat (s' v) *ᵥ x → ∀ a,
      hJ (X.B.I.ε v) (uMat (s v) *ᵥ x) (d a) = 0 := by
    intro x hx a
    rw [hd a, hJsub, Formalism.L2.SG.Pf.hJ_inUJ _ hU, hx, Formalism.L2.SG.Pf.hJ_inUJ _ hU', sub_self]
  have hde : ∀ a c, hJ (X.B.I.ε v) (eV X v c) (d a) = 0 := by
    intro a
    have hXu : (xMat X v s)ᴴ *ᵥ (fun c => hJ (X.B.I.ε v) (eV X v c) (d a)) = 0 := by
      funext b
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.zero_apply]
      rw [← hexp b]
      exact hgd _ (he b) a
    intro c
    exact congrFun (key _ hXu) c
  have hdz : ∀ a, hJ (X.B.I.ε v) (zV X u v) (d a) = 0 := by
    intro a
    have h := hgd _ hz a
    rw [pair_of_X X v hzX] at h
    simpa [hde a] using h
  have hdw : ∀ a j, hJ (X.B.I.ε v) (X.wfr u v j) (d a) = 0 := by
    intro a j
    have h := hgd _ (hw j) a
    rw [pair_of_X X v (hwX j)] at h
    simpa [hde a] using h
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ,
      ∀ b a, Δ b a = hJ (X.B.I.ε v) (fV X v b) (d a) :=
    ⟨fun b a => hJ (X.B.I.ε v) (fV X v b) (d a), fun _ _ => rfl⟩
  have hdrec : ∀ a, d a = ∑ c, Δ c a • eV X v c := by
    intro a
    apply hJ_test (X.B.I.ε v) (fam X u v) (fam_span X u v)
    rintro (b | b | j | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr, hJsumr]
    · rw [hde a b]
      simp [fr_ee]
    · rw [← hΔ b a]
      simp only [fr_fe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · rw [hdw a j]
      simp [fr_we]
    · rw [hdz a]
      simp [fr_ze]
  have hsk : ∀ b a, (αmᴴ * Δ) b a + (Δᴴ * αm) b a = 0 := by
    intro b a
    have h0 : hJ (X.B.I.ε v) (uMat (s' v) *ᵥ fV X v b) (uMat (s' v) *ᵥ fV X v a) = 0 := by
      rw [Formalism.L2.SG.Pf.hJ_inUJ _ hU', fr_ff]
    have e1 : ∀ c, uMat (s' v) *ᵥ fV X v c = uMat (s v) *ᵥ fV X v c - d c := by
      intro c
      rw [hd c, sub_sub_cancel]
    rw [e1 b, e1 a, hJsubl, hJsub, hJsub] at h0
    have hff : hJ (X.B.I.ε v) (uMat (s v) *ᵥ fV X v b) (uMat (s v) *ᵥ fV X v a) = 0 := by
      rw [Formalism.L2.SG.Pf.hJ_inUJ _ hU, fr_ff]
    have t1 : hJ (X.B.I.ε v) (d b) (uMat (s v) *ᵥ fV X v a) = (Δᴴ * αm) b a := by
      rw [hdrec b, hJsuml, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.conjTranspose_apply, hαm]
    have t2 : hJ (X.B.I.ε v) (uMat (s v) *ᵥ fV X v b) (d a) = (αmᴴ * Δ) b a := by
      rw [hdrec a, hJsumr, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.conjTranspose_apply, hαm, hJswap (X.B.I.ε v) (eV X v c) (uMat (s v) *ᵥ fV X v b), mul_comm]
    have t3 : hJ (X.B.I.ε v) (d b) (d a) = 0 := by
      rw [hdrec b, hJsuml]
      simp [hde a]
    rw [hff, t1, t2, t3] at h0
    linear_combination -h0
  have hNm : mMat X v s - mMat X v s' = αmᴴ * Δ := by
    unfold mMat
    rw [hxX, hinv, ← Matrix.mul_sub]
    congr 1
    ext b a
    rw [Matrix.sub_apply, hΔ, hd, hJsub]
    rfl
  have hNe : ∀ b a, (αmᴴ * Δ) b a = mMat X v s b a - mMat X v s' b a := by
    intro b a
    rw [← hNm, Matrix.sub_apply]
  have hstar : Δᴴ * αm = (αmᴴ * Δ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hskew : ∀ b a, (αmᴴ * Δ) b a + star ((αmᴴ * Δ) a b) = 0 := by
    intro b a
    have h := hsk b a
    rw [hstar, Matrix.conjTranspose_apply] at h
    exact h
  have hlt : ∀ b a : Fin D.R.rS, b < a → (αmᴴ * Δ) b a = 0 := by
    intro b a hba
    have h1 := hskew b a
    have h2 := cskew b a hba
    rw [hNe, hNe, star_sub] at h1
    rw [hNe]
    linear_combination (h1 + 2 * h2) / 2
  have hN0 : ∀ b a, (αmᴴ * Δ) b a = 0 := by
    intro b a
    rcases lt_trichotomy b a with hba | rfl | hab
    · exact hlt b a hba
    · have h1 := hskew b b
      apply Complex.ext
      · have h3 := congrArg Complex.re h1
        simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h3
        simp only [Complex.zero_re]
        linarith
      · rw [hNe, Complex.sub_im, cdiag b, sub_self, Complex.zero_im]
    · have h1 := hskew b a
      rw [hlt a b hab, star_zero, add_zero] at h1
      exact h1
  have hΔ0 : Δ = 0 := by
    have hz0 : αmᴴ * Δ = 0 := Matrix.ext fun b a => by rw [hN0 b a]; rfl
    calc Δ = (xMat X v s * αmᴴ) * Δ := by rw [hXαh, Matrix.one_mul]
      _ = xMat X v s * (αmᴴ * Δ) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hz0, Matrix.mul_zero]
  have hf : ∀ a, uMat (s v) *ᵥ fV X v a = uMat (s' v) *ᵥ fV X v a := by
    intro a
    have h0 : d a = 0 := by
      rw [hdrec a]
      simp [hΔ0]
    rw [hd a] at h0
    exact sub_eq_zero.1 h0
  have hall : ∀ i, uMat (s v) *ᵥ fam X u v i = uMat (s' v) *ᵥ fam X u v i := by
    rintro (b | b | j | ⟨⟩) <;> simp only [fam, Sum.elim_inl, Sum.elim_inr]
    exacts [he b, hf b, hw j, hz]
  exact Matrix.toLin'.injective (LinearMap.ext_on_range (fam_span X u v) fun i => by
    simpa [Matrix.toLin'_apply] using hall i)

/- English proof (translation)
Introduce `D X u s hs s' hs' hk`. Use function extensionality and compare the values at `v`. Conclude with `Subtype.ext (Units.ext (inj_at X u v hs hs' hk))`.
-/
theorem kapInj : KapInj := by
  intro D X u s hs s' hs' hk
  funext v
  exact Subtype.ext (Units.ext (inj_at X u v hs hs' hk))

end Formalism.L2.SG.Pf.LsNc5
