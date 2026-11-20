import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVGeo

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `| [], x, hx => by simp at hx | (t, s) :: bs, x, hx => by simp only [List.map_cons, List.sum_cons] at hx rw [ptPar_cons] by_cases hxs : x < s · rw [if_pos hxs]; simp only [blkOf]; rw [if_pos (by omega), if_pos hxs] · rw [if_neg hxs]; simp only [blkOf] rw [if_neg (by omega), if_neg …`.
-/
theorem blkOf_ptPar {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (x : ℕ), x < (bs.map Prod.snd).sum →
    blkOf bs (ptPar bs x) = blkOf bs x
  | [], x, hx => by simp at hx
  | (t, s) :: bs, x, hx => by
    simp only [List.map_cons, List.sum_cons] at hx
    rw [ptPar_cons]
    by_cases hxs : x < s
    · rw [if_pos hxs]; simp only [blkOf]; rw [if_pos (by omega), if_pos hxs]
    · rw [if_neg hxs]; simp only [blkOf]
      rw [if_neg (by omega), if_neg hxs, show s + ptPar bs (x - s) - s = ptPar bs (x - s) by omega,
        blkOf_ptPar bs (x - s) (by omega)]

/- English proof (translation)
The claim follows from `| [], x, _, hx, _, _ => by simp at hx | (t, s) :: bs, x, y, hx, hy, h => by simp only [List.map_cons, List.sum_cons] at hx hy simp only [blkOf] at h rw [ptPar_cons, ptPar_cons] by_cases hxs : x < s · by_cases hys : y < s · rw [if_pos hxs, if_pos hys] at h; omega · rw [if_pos hxs, …`.
-/
theorem ptPar_lt_of_blk {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (x y : ℕ), x < (bs.map Prod.snd).sum →
    y < (bs.map Prod.snd).sum → blkOf bs x < blkOf bs y → ptPar bs x < ptPar bs y
  | [], x, _, hx, _, _ => by simp at hx
  | (t, s) :: bs, x, y, hx, hy, h => by
    simp only [List.map_cons, List.sum_cons] at hx hy
    simp only [blkOf] at h
    rw [ptPar_cons, ptPar_cons]
    by_cases hxs : x < s
    · by_cases hys : y < s
      · rw [if_pos hxs, if_pos hys] at h; omega
      · rw [if_pos hxs, if_neg hys]; omega
    · by_cases hys : y < s
      · rw [if_neg hxs, if_pos hys] at h; omega
      · rw [if_neg hxs, if_neg hys] at h ⊢
        have := ptPar_lt_of_blk bs (x - s) (y - s) (by omega) (by omega) (by omega)
        omega

def StVFix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F, ∀ y ∈ StV X u u' (gamW X u u' w) v,
    (∀ a, uMat y *ᵥ fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) a =
      fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) a) →
    (∀ b, uMat y *ᵥ (uMat (gamW X u u' w v) *ᵥ
        fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) b) =
      uMat (gamW X u u' w v) *ᵥ
        fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) b) →
    y = 1

/- English proof (translation)
Establish `hA` using `relA_loc ε e f z z' hfe hfz hfz' S Si G T hSi hT hadj hrel`. Establish `hTc : ∀ (c : Fin r) (b : Fin (r + 1)), c.castSucc < b → Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) = 0`. Introduce `c b hcb`. Break down `hfree c b hcb with hlt | h0` into its components or cases. Establish `h` using `hA (π c.castSucc) b`.

Establish `hL : (∑ c' : Fin r, if c'.castSucc < π c.castSucc then conj (Formalism.L2.SG.HidaSetting.hJ ε (f c') (Si *ᵥ fam e z (π c.castSucc))) * Zhat ε (fam e z) (fam e z') G c'.castSucc b else 0) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c' _`. Use `split_ifs with h1`. Establish `hz : Zhat ε (fam e z) (fam e z') G c'.castSucc b = 0`.

Assume the negation of the conclusion as `hne`. Rewrite `h1` using `[(hZ _ _).1 hne]`. Conclude with `lt_irrefl _ (lt_trans h1 hlt)`. Rewrite using `[hz, mul_zero]`. Both sides reduce to the same expression.

Establish `hR : (∑ c' : Fin r, if c'.castSucc < b then Formalism.L2.SG.HidaSetting.hJ ε (f c') (T *ᵥ fam e z' b) * Zhat ε (fam e z) (fam e z') G (π c.castSucc) c'.castSucc else 0) = Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) * Zhat ε (fam e z) (fam e z') G (π c.castSucc) c.cas …`. Rewrite using `[Finset.sum_eq_single c]`. Rewrite using `[if_pos hcb]`. Introduce `c' _ hc' split_ifs`. Establish `hz : Zhat ε (fam e z) (fam e z') G (π c.castSucc) c'.castSucc = 0`.

Assume the negation of the conclusion as `hne`. Establish `h2` using `(hZ _ _).1 hne`. Establish `h3 : c.castSucc = c'.castSucc` using `by rw [← hπ c.castSucc, h2, hπ]`. Conclude with `hc' (Fin.castSucc_injective _ h3).symm`. Rewrite using `[hz, mul_zero]`.

Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`. Rewrite `h` using `[hL, hR]`. Conclude with `(mul_eq_zero.1 h.symm).resolve_right ((hZ _ _).2 rfl)`.

Conclude with `h0`. Establish `hSc : ∀ (c : Fin r) (a : Fin (r + 1)), c.castSucc < a → Formalism.L2.SG.HidaSetting.hJ ε (f c) (Si *ᵥ fam e z a) = 0`. Introduce `c a hca`. Establish `h` using `hA a (π c.castSucc)`. Establish `hR : (∑ c' : Fin r, if c'.castSucc < π c.castSucc then Formalism.L2.SG.HidaSetting.hJ ε (f c') (T *ᵥ fam e z' (π c.castSucc)) * Zhat ε (fam e z) (fam e z') G a c'.castSucc else 0) = 0`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c' _`. Use `split_ifs with h1`. Rewrite using `[hTc c' _ h1, zero_mul]`. Both sides reduce to the same expression.

Establish `hL : (∑ c' : Fin r, if c'.castSucc < a then conj (Formalism.L2.SG.HidaSetting.hJ ε (f c') (Si *ᵥ fam e z a)) * Zhat ε (fam e z) (fam e z') G c'.castSucc (π c.castSucc) else 0) = conj (Formalism.L2.SG.HidaSetting.hJ ε (f c) (Si *ᵥ fam e z a)) * Zhat ε (fam e z) (fam e z') G c.cast …`. Rewrite using `[Finset.sum_eq_single c]`. Rewrite using `[if_pos hca]`. Introduce `c' _ hc' split_ifs`. Establish `hz : Zhat ε (fam e z) (fam e z') G c'.castSucc (π c.castSucc) = 0`.

Assume the negation of the conclusion as `hne`. Establish `h2` using `(hZ _ _).1 hne`. Rewrite `h2` using `[hπ]`. Conclude with `hc' (Fin.castSucc_injective _ h2)`. Rewrite using `[hz, mul_zero]`.

Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`. Rewrite `h` using `[hL, hR]`. Establish `h4` using `(mul_eq_zero.1 h).resolve_right ((hZ _ _).2 (hπ _).symm)`.

Simplify using `using h4`. Use `⟨fun b => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[flag_expand ε e f z' hfe hfz' T hT b] conv_rhs => rw [← add_zero (fam e z' b)]`. Use `congr 1`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `c _`. Use `split_ifs with h1`. Rewrite using `[hTc c b h1, zero_smul]`. Rewrite using `[zero_smul]`. Rewrite using `[flag_expand ε e f z hfe hfz Si hSi a] conv_rhs => rw [← add_zero (fam e z a)]`.

Use `congr 1`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c _`. Use `split_ifs with h1`. Rewrite using `[hSc c a h1, zero_smul]`.

Rewrite using `[zero_smul]`.
-/
private theorem flag_fix_lemma {n r : ℕ} (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (f a) (e b) = if b = a then 1 else 0)
    (hfz : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z = 0) (hfz' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z' = 0)
    (S Si G T : Matrix (Fin n) (Fin n) ℂ) (hSi : Formalism.L2.SG.HidaSetting.InS e z Si)
    (hT : Formalism.L2.SG.HidaSetting.InS e z' T)
    (hadj : ∀ x y, Formalism.L2.SG.HidaSetting.hJ ε x (S *ᵥ y) = Formalism.L2.SG.HidaSetting.hJ ε (Si *ᵥ x) y)
    (hrel : S * G = G * T) (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hZ : ∀ c b, Zhat ε (fam e z) (fam e z') G c b ≠ 0 ↔ c = π b)
    (hfree : ∀ (c : Fin r) (b : Fin (r + 1)), c.castSucc < b →
      π c.castSucc < π b ∨ Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) = 0) :
    (∀ b, T *ᵥ fam e z' b = fam e z' b) ∧ (∀ a, Si *ᵥ fam e z a = fam e z a) := by
  have hA := relA_loc ε e f z z' hfe hfz hfz' S Si G T hSi hT hadj hrel
  have hTc : ∀ (c : Fin r) (b : Fin (r + 1)), c.castSucc < b →
      Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) = 0 := by
    intro c b hcb
    rcases hfree c b hcb with hlt | h0
    · have h := hA (π c.castSucc) b
      have hL : (∑ c' : Fin r, if c'.castSucc < π c.castSucc then
          conj (Formalism.L2.SG.HidaSetting.hJ ε (f c') (Si *ᵥ fam e z (π c.castSucc))) * Zhat ε (fam e z) (fam e z') G c'.castSucc b
          else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro c' _
        split_ifs with h1
        · have hz : Zhat ε (fam e z) (fam e z') G c'.castSucc b = 0 := by
            by_contra hne
            rw [(hZ _ _).1 hne] at h1
            exact lt_irrefl _ (lt_trans h1 hlt)
          rw [hz, mul_zero]
        · rfl
      have hR : (∑ c' : Fin r, if c'.castSucc < b then
          Formalism.L2.SG.HidaSetting.hJ ε (f c') (T *ᵥ fam e z' b) * Zhat ε (fam e z) (fam e z') G (π c.castSucc) c'.castSucc else 0) =
          Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) * Zhat ε (fam e z) (fam e z') G (π c.castSucc) c.castSucc := by
        rw [Finset.sum_eq_single c]
        · rw [if_pos hcb]
        · intro c' _ hc'
          split_ifs
          · have hz : Zhat ε (fam e z) (fam e z') G (π c.castSucc) c'.castSucc = 0 := by
              by_contra hne
              have h2 := (hZ _ _).1 hne
              have h3 : c.castSucc = c'.castSucc := by rw [← hπ c.castSucc, h2, hπ]
              exact hc' (Fin.castSucc_injective _ h3).symm
            rw [hz, mul_zero]
          · rfl
        · intro h; exact absurd (Finset.mem_univ c) h
      rw [hL, hR] at h
      exact (mul_eq_zero.1 h.symm).resolve_right ((hZ _ _).2 rfl)
    · exact h0
  have hSc : ∀ (c : Fin r) (a : Fin (r + 1)), c.castSucc < a →
      Formalism.L2.SG.HidaSetting.hJ ε (f c) (Si *ᵥ fam e z a) = 0 := by
    intro c a hca
    have h := hA a (π c.castSucc)
    have hR : (∑ c' : Fin r, if c'.castSucc < π c.castSucc then
        Formalism.L2.SG.HidaSetting.hJ ε (f c') (T *ᵥ fam e z' (π c.castSucc)) * Zhat ε (fam e z) (fam e z') G a c'.castSucc else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro c' _
      split_ifs with h1
      · rw [hTc c' _ h1, zero_mul]
      · rfl
    have hL : (∑ c' : Fin r, if c'.castSucc < a then
        conj (Formalism.L2.SG.HidaSetting.hJ ε (f c') (Si *ᵥ fam e z a)) * Zhat ε (fam e z) (fam e z') G c'.castSucc (π c.castSucc) else 0) =
        conj (Formalism.L2.SG.HidaSetting.hJ ε (f c) (Si *ᵥ fam e z a)) * Zhat ε (fam e z) (fam e z') G c.castSucc (π c.castSucc) := by
      rw [Finset.sum_eq_single c]
      · rw [if_pos hca]
      · intro c' _ hc'
        split_ifs
        · have hz : Zhat ε (fam e z) (fam e z') G c'.castSucc (π c.castSucc) = 0 := by
            by_contra hne
            have h2 := (hZ _ _).1 hne
            rw [hπ] at h2
            exact hc' (Fin.castSucc_injective _ h2)
          rw [hz, mul_zero]
        · rfl
      · intro h; exact absurd (Finset.mem_univ c) h
    rw [hL, hR] at h
    have h4 := (mul_eq_zero.1 h).resolve_right ((hZ _ _).2 (hπ _).symm)
    simpa using h4
  refine ⟨fun b => ?_, fun a => ?_⟩
  · rw [flag_expand ε e f z' hfe hfz' T hT b]
    conv_rhs => rw [← add_zero (fam e z' b)]
    congr 1
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with h1
    · rw [hTc c b h1, zero_smul]
    · rw [zero_smul]
  · rw [flag_expand ε e f z hfe hfz Si hSi a]
    conv_rhs => rw [← add_zero (fam e z a)]
    congr 1
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with h1
    · rw [hSc c a h1, zero_smul]
    · rw [zero_smul]

/- English proof (translation)
Introduce `w hw v y hy h0`. Establish `hγ : IsPtRep X u u' w (gamW X u u' w)`. Unfold `gamW`. Rewrite using `[dif_pos hw.1]`. Conclude with `hw.1.choose_spec`.

Establish `hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR b)) = if b = a then 1 else 0`. Introduce `a b`. Express the relevant statement in the definitionally equal form `Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.fY a))) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.eX b))) = _`. Rewrite using `[Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v (X.fY a) (X.eX b), Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X a b]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hfz : ∀ (u₀ : D.what₂.Word) a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u₀)) = 0`. Introduce `u₀ a`. Express the relevant statement in the definitionally equal form `Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.fY a))) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.zu u₀))) = 0`. Rewrite using `[Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v (X.fY a) (X.zu u₀), (X.zu_orth u₀ a).2, map_zero]`. Establish `hy'` using `hy`.

Take `⟨hyN, hyN'⟩` from `hy'`. Establish `hSi : Formalism.L2.SG.HidaSetting.InS (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (uMat y⁻¹)`. Take `⟨h1, _⟩` from `nV_inv X u v y hyN`. Conclude with `h1`. Establish `hT : Formalism.L2.SG.HidaSetting.InS (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v))`.

Take `⟨h1, _⟩` from `hyN'`. Conclude with `h1`. Establish `hrel : uMat y * uMat (gamW X u u' w v) = uMat (gamW X u u' w v) * uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v)`. Rewrite using `[← Formalism.L2.SG.PoincareInHH.Cut.uMat_mul, ← Formalism.L2.SG.PoincareInHH.Cut.uMat_mul]`. Use `congr 1`.

Use `group`. Establish `hlen : ∀ b : Fin (D.R.rS + 1), b.1 < (w.1.map Prod.snd).sum` using `fun b => by`. Rewrite using `[w.2.2]`. Conclude with `b.2`. Set `π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)` to `fun b => ⟨ptPar w.1 b.1, by have h := ptPar_lt w.1 b.1 (hlen b); rwa [w.2.2] at h⟩`.

Establish `hπ : ∀ a, π (π a) = a` using `fun a => Fin.ext (ptPar_invol w.1 a.1 (hlen a))`. Establish `hZ : ∀ c b, Zhat (X.B.I.ε v) (fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u))) (fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u'))) (uMat (gamW X u u' w …`. Introduce `c b`. Establish `h1` using `congrFun (congrFun (hγ v) c) b`. Simplify using `only [RealObj.ZhatO, ZX, frm, famSc_one, ptC, Matrix.map_apply, ptMat] at h1`.

Rewrite `h1` using `[ptEntry_eq w.1 c.1 b.1 (hlen b)]`. Establish `hsgn : ((-1 : ℂ) ^ (D.R.rS - b.1)) ≠ 0` using `pow_ne_zero _ (by norm_num)`. Prove the components needed by the constructor for the conclusion. Introduce `hne`. Assume the negation of the conclusion as `hcb`.

Establish `hv : c.1 ≠ ptPar w.1 b.1` using `fun h => hcb (Fin.ext h)`. Rewrite `h1` using `[if_neg hv, map_zero, map_zero]`. Conclude with `hne ((mul_eq_zero.1 h1).resolve_left hsgn)`. Introduce `hcb hz`. Establish `hv : c.1 = ptPar w.1 b.1` using `congrArg Fin.val hcb`.

Rewrite `h1` using `[if_pos hv, hz, mul_zero]`. Conclude with `ptSc_ne w.1 (fun x hx => w.2.1 x hx) b.1 (hlen b) (by simpa using h1.symm)`. Establish `hfree : ∀ (c : Fin D.R.rS) (b : Fin (D.R.rS + 1)), c.castSucc < b → π c.castSucc < π b ∨ Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR c)) (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) *ᵥ fam (fun c => Formalism.L2.SG.HidaSetting.rv …`. Introduce `c b hcb`. Distinguish the cases in `hbl : blkOf w.1 c.castSucc.1 = blkOf w.1 b.1`.

Use `right`. Establish `hp` using `congrFun h0 ⟨(c.castSucc, b), hcb, hbl⟩`. Simplify using `only [stCoordV, frm, famSc, Matrix.mulVec_smul, hJ_smul_r, Fin.val_castSucc, Fin.eta] at hp`. Establish `hrd : (D.host.rdE : ℂ) ≠ 0` using `by exact_mod_cast (rdE_pos_c (D := D)).ne'`. Break down `mul_eq_zero.1 hp with h | h` into its components or cases.

Conclude with `absurd h (pow_ne_zero _ hrd)`. Break down `mul_eq_zero.1 h with h' | h'` into its components or cases. Conclude with `absurd h' (inv_ne_zero (pow_ne_zero _ hrd))`. Conclude with `h'`. Use `left`.

Establish `hle : blkOf w.1 c.castSucc.1 ≤ blkOf w.1 b.1` using `blkOf_mono w.1 _ _ (le_of_lt hcb)`. Conclude with `ptPar_lt_of_blk w.1 _ _ (hlen _) (hlen _) (lt_of_le_of_ne hle hbl)`. Take `⟨hTfix, hSfix⟩` from `flag_fix_lemma (X.B.I.ε v) (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) hfe (hfz u) (hfz u') (uMat y) (uMa …`. Establish `hyy : uMat y * uMat y⁻¹ = 1`. Establish `h` using `Formalism.L2.SG.PoincareInHH.Cut.uMat_inv_mul y⁻¹`.

Rewrite `h` using `[inv_inv]`. Then use the resulting hypothesis. Use `hFx w hw v y hy (fun a => ?_) (fun b => ?_)` and prove the remaining obligations. Rewrite using `[← hSfix a, Matrix.mulVec_mulVec, hyy, Matrix.one_mulVec, hSfix a]`. Rewrite using `[Matrix.mulVec_mulVec, hrel, ← Matrix.mulVec_mulVec, hTfix b]`.
-/
theorem stVKer_of_fix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hFx : StVFix X u u') :
    StVKer X u u' := by
  intro w hw v y hy h0
  have hγ : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dif_pos hw.1]
    exact hw.1.choose_spec
  have hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR b)) = if b = a then 1 else 0 := by
    intro a b
    change Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.fY a)))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.eX b))) = _
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v (X.fY a) (X.eX b), Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X a b]
    split_ifs <;> simp
  have hfz : ∀ (u₀ : D.what₂.Word) a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v)
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u₀)) = 0 := by
    intro u₀ a
    change Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.fY a)))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.zu u₀))) = 0
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v (X.fY a) (X.zu u₀), (X.zu_orth u₀ a).2, map_zero]
  have hy' := hy
  obtain ⟨hyN, hyN'⟩ := hy'
  have hSi : Formalism.L2.SG.HidaSetting.InS (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (uMat y⁻¹) := by
    obtain ⟨h1, _⟩ := nV_inv X u v y hyN
    exact h1
  have hT : Formalism.L2.SG.HidaSetting.InS (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v)) := by
    obtain ⟨h1, _⟩ := hyN'
    exact h1
  have hrel : uMat y * uMat (gamW X u u' w v) =
      uMat (gamW X u u' w v) * uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) := by
    rw [← Formalism.L2.SG.PoincareInHH.Cut.uMat_mul, ← Formalism.L2.SG.PoincareInHH.Cut.uMat_mul]
    congr 1
    group
  have hlen : ∀ b : Fin (D.R.rS + 1), b.1 < (w.1.map Prod.snd).sum := fun b => by
    rw [w.2.2]; exact b.2
  let π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
    ⟨ptPar w.1 b.1, by have h := ptPar_lt w.1 b.1 (hlen b); rwa [w.2.2] at h⟩
  have hπ : ∀ a, π (π a) = a := fun a => Fin.ext (ptPar_invol w.1 a.1 (hlen a))
  have hZ : ∀ c b, Zhat (X.B.I.ε v) (fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u))) (fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u'))) (uMat (gamW X u u' w v)) c b ≠ 0 ↔ c = π b := by
    intro c b
    have h1 := congrFun (congrFun (hγ v) c) b
    simp only [RealObj.ZhatO, ZX, frm, famSc_one, ptC, Matrix.map_apply, ptMat] at h1
    rw [ptEntry_eq w.1 c.1 b.1 (hlen b)] at h1
    have hsgn : ((-1 : ℂ) ^ (D.R.rS - b.1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    constructor
    · intro hne
      by_contra hcb
      have hv : c.1 ≠ ptPar w.1 b.1 := fun h => hcb (Fin.ext h)
      rw [if_neg hv, map_zero, map_zero] at h1
      exact hne ((mul_eq_zero.1 h1).resolve_left hsgn)
    · intro hcb hz
      have hv : c.1 = ptPar w.1 b.1 := congrArg Fin.val hcb
      rw [if_pos hv, hz, mul_zero] at h1
      exact ptSc_ne w.1 (fun x hx => w.2.1 x hx) b.1 (hlen b) (by simpa using h1.symm)
  have hfree : ∀ (c : Fin D.R.rS) (b : Fin (D.R.rS + 1)), c.castSucc < b →
      π c.castSucc < π b ∨ Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR c))
        (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) *ᵥ
          fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) b) = 0 := by
    intro c b hcb
    by_cases hbl : blkOf w.1 c.castSucc.1 = blkOf w.1 b.1
    · right
      have hp := congrFun h0 ⟨(c.castSucc, b), hcb, hbl⟩
      simp only [stCoordV, frm, famSc, Matrix.mulVec_smul, hJ_smul_r, Fin.val_castSucc,
        Fin.eta] at hp
      have hrd : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (rdE_pos_c (D := D)).ne'
      rcases mul_eq_zero.1 hp with h | h
      · exact absurd h (pow_ne_zero _ hrd)
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' (inv_ne_zero (pow_ne_zero _ hrd))
        · exact h'
    · left
      have hle : blkOf w.1 c.castSucc.1 ≤ blkOf w.1 b.1 := blkOf_mono w.1 _ _ (le_of_lt hcb)
      exact ptPar_lt_of_blk w.1 _ _ (hlen _) (hlen _) (lt_of_le_of_ne hle hbl)
  obtain ⟨hTfix, hSfix⟩ := flag_fix_lemma (X.B.I.ε v) (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
    (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u))
    (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) hfe (hfz u) (hfz u') (uMat y) (uMat y⁻¹)
    (uMat (gamW X u u' w v)) (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v)) hSi hT
    (fun x x' => Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj y x x') hrel π hπ hZ hfree
  have hyy : uMat y * uMat y⁻¹ = 1 := by
    have h := Formalism.L2.SG.PoincareInHH.Cut.uMat_inv_mul y⁻¹
    rwa [inv_inv] at h
  refine hFx w hw v y hy (fun a => ?_) (fun b => ?_)
  · rw [← hSfix a, Matrix.mulVec_mulVec, hyy, Matrix.one_mulVec, hSfix a]
  · rw [Matrix.mulVec_mulVec, hrel, ← Matrix.mulVec_mulVec, hTfix b]

/- English proof (translation)
The claim follows from `stVGeo_of_ker_sec X u u' (stVKer_of_fix X u u' hFx) hS`.
-/
theorem stVGeo_of_fix_sec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hFx : StVFix X u u')
    (hS : StVSec X u u') : StVGeo X u u' :=
  stVGeo_of_ker_sec X u u' (stVKer_of_fix X u u' hFx) hS

end Formalism.L2.SG.Pf.Carrier.JointQuot
