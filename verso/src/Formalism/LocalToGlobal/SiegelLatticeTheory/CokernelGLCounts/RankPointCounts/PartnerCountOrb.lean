import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.DeterminantFormIdentity
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKS

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BlockList

variable {K : Type*} [Zero K]

/- English proof (translation)
Proceed by induction on `bs generalizing i j with`. Consider the case `nil => simp at hi`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [List.map_cons, List.sum_cons] at hi`.

Distinguish the cases in `hi' : i < s`. Establish `hst : pSt ((t, s) :: bs) i = 0` using `by simp [pSt, hi']`. Establish `hsz : pSz ((t, s) :: bs) i = s` using `by simp [pSz, hi']`. Rewrite `h2` using `[hst, hsz]`. Establish `hj : j < s` using `by omega`.

Simplify using `[pSt, pSz, pTau, hi', hj]`. Establish `hst : pSt ((t, s) :: bs) i = s + pSt bs (i - s)` using `by simp [pSt, hi']`. Establish `hsz : pSz ((t, s) :: bs) i = pSz bs (i - s)` using `by simp [pSz, hi']`. Rewrite `h1`, `h2` using `[hst]`. Rewrite `h2` using `[hsz]`.

Establish `hj : ¬ j < s` using `by omega`. Take `⟨e1, e2, e3⟩` from `ih (i - s) (j - s) (by omega) (by omega) (by omega)`. Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> simp [pSt, pSz, pTau, hj, hi', e1, e2, e3]`.
-/
theorem pSt_interval (bs : List (K × ℕ)) (i j : ℕ) (hi : i < (bs.map Prod.snd).sum)
    (h1 : pSt bs i ≤ j) (h2 : j < pSt bs i + pSz bs i) :
    pSt bs j = pSt bs i ∧ pSz bs j = pSz bs i ∧ pTau bs j = pTau bs i := by
  induction bs generalizing i j with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hi
    by_cases hi' : i < s
    · have hst : pSt ((t, s) :: bs) i = 0 := by simp [pSt, hi']
      have hsz : pSz ((t, s) :: bs) i = s := by simp [pSz, hi']
      rw [hst, hsz] at h2
      have hj : j < s := by omega
      simp [pSt, pSz, pTau, hi', hj]
    · have hst : pSt ((t, s) :: bs) i = s + pSt bs (i - s) := by simp [pSt, hi']
      have hsz : pSz ((t, s) :: bs) i = pSz bs (i - s) := by simp [pSz, hi']
      rw [hst] at h1 h2
      rw [hsz] at h2
      have hj : ¬ j < s := by omega
      obtain ⟨e1, e2, e3⟩ := ih (i - s) (j - s) (by omega) (by omega) (by omega)
      refine ⟨?_, ?_, ?_⟩ <;> simp [pSt, pSz, pTau, hj, hi', e1, e2, e3]

/- English proof (translation)
Proceed by induction on `bs generalizing i j with`. Consider the case `nil => simp at hi`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Establish `hs : 1 ≤ s` using `hbs (t, s) List.mem_cons_self`.

Simplify using `only [List.map_cons, List.sum_cons] at hi hj`. Apply the tactic sequence `by_cases hi' : i < s <;> by_cases hj' : j < s`. Simplify using `[pSz, pTau, hi', hj']`. Simplify using `only [pSt, hi', hj', if_true, if_false] at h`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [pSt, hi', hj', if_true, if_false] at h`. Use linear arithmetic over natural numbers and integers. Simplify using `only [pSt, hi', hj', if_false] at h`. Take `⟨e1, e2⟩` from `ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) (i - s) (j - s) (by omega) (by omega) (by omega)`. Simplify using `[pSz, pTau, hi', hj', e1, e2]`.
-/
theorem pSt_same (bs : List (K × ℕ)) (hbs : ∀ b ∈ bs, 1 ≤ b.2) (i j : ℕ) (hi : i < (bs.map Prod.snd).sum)
    (hj : j < (bs.map Prod.snd).sum) (h : pSt bs i = pSt bs j) :
    pSz bs i = pSz bs j ∧ pTau bs i = pTau bs j := by
  induction bs generalizing i j with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have hs : 1 ≤ s := hbs (t, s) List.mem_cons_self
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases hi' : i < s <;> by_cases hj' : j < s
    · simp [pSz, pTau, hi', hj']
    · simp only [pSt, hi', hj', if_true, if_false] at h; omega
    · simp only [pSt, hi', hj', if_true, if_false] at h; omega
    · simp only [pSt, hi', hj', if_false] at h
      obtain ⟨e1, e2⟩ := ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) (i - s) (j - s) (by omega) (by omega)
        (by omega)
      simp [pSz, pTau, hi', hj', e1, e2]

/- English proof (translation)
Take `⟨b1, b2, b3, -, -⟩` from `pBlock bs i hi`. Conclude with `(pSt_interval bs i (pSig bs i) hi (by omega) (by omega)).1`.
-/
theorem pSt_pSig (bs : List (K × ℕ)) (i : ℕ) (hi : i < (bs.map Prod.snd).sum) :
    pSt bs (pSig bs i) = pSt bs i := by
  obtain ⟨b1, b2, b3, -, -⟩ := pBlock bs i hi
  exact (pSt_interval bs i (pSig bs i) hi (by omega) (by omega)).1

/- English proof (translation)
Proceed by induction on `bs generalizing cs a b with`. Consider the case `nil`. Consider the cases of `cs with`. Consider the case `nil => simp at ha`. Consider the case `cons c cs => simp at hsz`.

Consider the case `cons x bs ih`. Consider the cases of `cs with`. Consider the case `nil => simp at hsz`. Consider the case `cons c cs`. Take `⟨u, s⟩` from `x`.

Take `⟨t, s'⟩` from `c`. Simplify using `only [List.map_cons, List.cons.injEq] at hsz`. Take `⟨hs, hrest⟩` from `hsz`. Simplify using `only [List.map_cons, List.sum_cons] at ha hb`. Establish `s1 : 1 ≤ s'` using `by rw [← hs]; exact s.2`.

Simplify using `only [Loc.sameBlock, pSt]`. Rewrite using `[hs]`. Apply the tactic sequence `by_cases ha' : a < s' <;> by_cases hb' : b < s'`. Simplify using `[ha', hb']`. Simplify using `only [ha', hb', if_true, if_false]`.

Simplify using `[ha', hb']`. Use linear arithmetic over natural numbers and integers. Simplify using `only [ha', hb', if_true, if_false]`. Simplify using `[ha', hb']`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [ha', hb', if_false]`. Establish `hx` using `ih cs hrest (a - s') (b - s') (by omega) (by omega)`. Simplify using `only [not_lt.1 ha', not_lt.1 hb', and_self, decide_true, Bool.true_and, decide_false, Bool.false_or, and_false, Bool.false_and, true_and]`. Rewrite using `[hx]`. Apply the tactic sequence `constructor <;> intro h <;> omega`.
-/
theorem sameBlock_iff {E' : Type} [CommRing E'] (bs : List (E'ˣ × ℕ+)) (cs : List (K × ℕ))
    (hsz : bs.map (fun x => (x.2 : ℕ)) = cs.map Prod.snd) (a b : ℕ) (ha : a < (cs.map Prod.snd).sum)
    (hb : b < (cs.map Prod.snd).sum) : Loc.sameBlock bs a b = true ↔ pSt cs a = pSt cs b := by
  induction bs generalizing cs a b with
  | nil =>
    cases cs with
    | nil => simp at ha
    | cons c cs => simp at hsz
  | cons x bs ih =>
    cases cs with
    | nil => simp at hsz
    | cons c cs =>
      obtain ⟨u, s⟩ := x
      obtain ⟨t, s'⟩ := c
      simp only [List.map_cons, List.cons.injEq] at hsz
      obtain ⟨hs, hrest⟩ := hsz
      simp only [List.map_cons, List.sum_cons] at ha hb
      have s1 : 1 ≤ s' := by rw [← hs]; exact s.2
      simp only [Loc.sameBlock, pSt]
      rw [hs]
      by_cases ha' : a < s' <;> by_cases hb' : b < s'
      · simp [ha', hb']
      · simp only [ha', hb', if_true, if_false]; simp [ha', hb']; omega
      · simp only [ha', hb', if_true, if_false]; simp [ha', hb']; omega
      · simp only [ha', hb', if_false]
        have hx := ih cs hrest (a - s') (b - s') (by omega) (by omega)
        simp only [not_lt.1 ha', not_lt.1 hb', and_self, decide_true, Bool.true_and, decide_false, Bool.false_or,
          and_false, Bool.false_and, true_and]
        rw [hx]
        constructor <;> intro h <;> omega

end BlockList

section Decomp

variable {D : Formalism.BasicNotions.D7}

def bdM {N : ℕ} {R : Type*} [CommRing R] (blk : Fin N → ℕ) (X : Matrix (Fin N) (Fin N) R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun a b => if blk a = blk b then X a b else 0

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [bdM, Matrix.of_apply, Matrix.mul_apply]`. Distinguish the cases in `hab : blk a = blk b`. Rewrite using `[if_pos hab]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hc : blk a = blk c`. Rewrite using `[if_pos (hc.symm.trans hab)]`. Rewrite using `[hA a c hc, zero_mul, zero_mul]`. Rewrite using `[if_neg hab]`. Use `symm`.

Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : blk a = blk c`. Rewrite using `[if_neg (fun h => hab (hc.trans h)), mul_zero]`. Rewrite using `[hA a c hc, zero_mul]`.
-/
theorem bdM_mul {N : ℕ} {R : Type*} [CommRing R] (blk : Fin N → ℕ) (A X : Matrix (Fin N) (Fin N) R)
    (hA : ∀ a c, blk a ≠ blk c → A a c = 0) : bdM blk (A * X) = A * bdM blk X := by
  ext a b
  simp only [bdM, Matrix.of_apply, Matrix.mul_apply]
  by_cases hab : blk a = blk b
  · rw [if_pos hab]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : blk a = blk c
    · rw [if_pos (hc.symm.trans hab)]
    · rw [hA a c hc, zero_mul, zero_mul]
  · rw [if_neg hab]
    symm
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : blk a = blk c
    · rw [if_neg (fun h => hab (hc.trans h)), mul_zero]
    · rw [hA a c hc, zero_mul]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [bdM, Matrix.of_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules.

Apply the tactic sequence `rw [Matrix.one_apply_ne hab]; split_ifs <;> rfl`.
-/
theorem bdM_one {N : ℕ} {R : Type*} [CommRing R] (blk : Fin N → ℕ) : bdM blk (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  ext a b
  simp only [bdM, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab]; split_ifs <;> rfl

/- English proof (translation)
Take `⟨uL, uU, hd, hz, hY⟩` from `h`. Establish `hL : IsLo uL` using `⟨fun a => (hd a).1, fun a b hab => (hz a b hab).1⟩`. Establish `hU : IsUp uU` using `⟨fun a => (hd a).2, fun a b hab => (hz a b hab).2⟩`. Establish `hsum : (w.1.map Prod.snd).sum = D.R.rS + 1` using `w.2.2`. Establish `hbs : ∀ b ∈ w.1, 1 ≤ b.2` using `fun b hb => (w.2.1 b hb).2`.

Use `set blk : Fin (D.R.rS + 1) → ℕ := fun a => pSt w.1 a.val with hblk`. Use `set σ := sgF w`. Establish `hσσ : ∀ a, σ (σ a) = a` using `sgF_sgF w`. Establish `hσblk : ∀ a, blk (σ a) = blk a` using `fun a => pSt_pSig w.1 a.val (by rw [hsum]; exact a.2)`. Establish `hτ : ∀ a b, blk a = blk b → pSz w.1 a.val = pSz w.1 b.val ∧ pTau w.1 a.val = pTau w.1 b.val` using `fun a b h => pSt_same w.1 hbs a.val b.val (by rw [hsum]; exact a.2) (by rw [hsum]; exact b.2) h`.

Establish `hrev : ∀ a b, blk a = blk b → a < b → σ b < σ a`. Introduce `a b hab hlt`. Take `⟨-, -, ea, -, -⟩` from `pBlock w.1 a.val (by rw [hsum]; exact a.2)`. Take `⟨-, -, eb, -, -⟩` from `pBlock w.1 b.val (by rw [hsum]; exact b.2)`. Establish `hs` using `(hτ a b hab).1`.

Establish `h1 : blk a = blk b` using `hab`. Simplify using `only [hblk] at h1`. Use `show (σ b).val < (σ a).val`. Simplify using `only [σ, sgF]`. Establish `: a.val < b.val` using `hlt`.

Use linear arithmetic over natural numbers and integers. Use `set W := modMat δ T T' p w`. Establish `hW : ∀ a b, W a b = if b = σ a then blkMod δ T T' p (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val) else 0` using `fun a b => modMat_apply' δ T T' p w a b`. Use `set β : MatP D p := bdM blk uU`. Use `set β' : MatP D p := Matrix.of fun a b => β (σ a) (σ b)`.

Establish `hβU : IsUp β`. Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Simplify using `only [β, bdM, Matrix.of_apply, if_true, hU.1]`. Apply the tactic sequence `simp only [β, bdM, Matrix.of_apply]; split_ifs <;> simp [hU.2 a b hab]`. Establish `hβ'L : IsLo β'`.

Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Simplify using `only [β', Matrix.of_apply]`. Conclude with `hβU.1 _`. Simplify using `only [β', β, bdM, Matrix.of_apply] split_ifs with hb`. Rewrite `hb` using `[hσblk, hσblk]`.

Conclude with `hU.2 _ _ (hrev a b hb hab)`. Both sides reduce to the same expression. Establish `hWβ : W * β = β' * W`. Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply]`.

Rewrite using `[Finset.sum_eq_single (σ a), Finset.sum_eq_single (σ b)]`. Rewrite using `[hW a (σ a), if_pos rfl, hW (σ b) b, if_pos (hσσ b).symm]`. Simplify using `only [β', Matrix.of_apply, hσσ, β, bdM]`. Use `split_ifs with hb`. Establish `hab : blk a = blk (σ b)` using `(hσblk a).symm.trans (hb.trans (hσblk b).symm)`.

Take `⟨e1, e2⟩` from `hτ a (σ b) hab`. Establish `e0 : pSt w.1 a.val = pSt w.1 (σ b).val` using `hab`. Rewrite using `[e0, e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_zero, zero_mul]`.

Introduce `c _ hc; rw [hW c b, if_neg (fun h => hc (by rw [h, hσσ])), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `c _ hc`. Rewrite using `[hW a c, if_neg hc, zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hβdet : IsUnit β.det` using `by rw [det_up' hβU]; exact isUnit_one`. Establish `hβblk : ∀ a c, blk a ≠ blk c → β a c = 0` using `fun a c h => by simp [β, bdM, h]`. Establish `hβi : bdM blk β⁻¹ = β⁻¹`.

Establish `h1` using `bdM_mul blk β β⁻¹ hβblk`. Rewrite `h1` using `[Matrix.mul_nonsing_inv _ hβdet, bdM_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hβdet, Matrix.one_mul]`. Use `_ = β⁻¹ := by rw [← h1, Matrix.mul_one]`.

Establish `hβiblk : ∀ a c, blk a ≠ blk c → β⁻¹ a c = 0` using `fun a c h => by`. Rewrite using `[← hβi]`. Simplify using `[bdM, h]`. Take `⟨n, hn⟩ : ∃ n : MatP D p, n = β⁻¹ * uU` from `⟨_, rfl⟩`. Establish `hn1 : bdM blk n = 1`.

Rewrite using `[hn, bdM_mul blk β⁻¹ uU hβiblk]`. Use `show β⁻¹ * β = 1`. Conclude with `Matrix.nonsing_inv_mul _ hβdet`. Establish `hnU : IsUp n` using `by rw [hn]; exact isUp_mul (isUp_inv hβU) hU`. Establish `huU : uU = β * n`.

Rewrite using `[hn, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hβdet, Matrix.one_mul]`. Establish `hY2 : Y = (uL * β') * W * n`. Rewrite using `[hY, huU]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc W β n, hWβ]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `hLβ : IsLo (uL * β')` using `isLo_mul hL hβ'L`. Establish `hsz : w₀.blocks.map (fun x => (x.2 : ℕ)) = w.1.map Prod.snd`. Establish `h1` using `modPt_blocks δ T T' p w w₀ hw₀`. Establish `h2` using `congrArg (List.map Prod.snd) h1`.

Simplify using `only [List.map_map] at h2`. Rewrite `h2` using `[PI.SupportDatumW.mapBlocks_snd]`. Conclude with `h2`. Use `⟨w₀, hw₀, (fun x => (uL * β') x.1.1 x.1.2, fun y => n y.1.1 y.1.2), ?_⟩` and prove the remaining obligations. Rewrite using `[hY2]`.

Use `congr 2`. Use extensionality with `a b`. Simplify using `only [Loc.uLow]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Rewrite using `[if_pos rfl, hLβ.1]`. Rewrite using `[if_neg hab]`. Distinguish the cases in `hlt : b < a`. Rewrite using `[dif_pos hlt]`. Rewrite using `[dif_neg hlt]`.

Conclude with `hLβ.2 a b (lt_of_le_of_ne (not_lt.1 hlt) hab)`. Use extensionality with `a b`. Simplify using `only [Loc.uUp]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Rewrite using `[if_pos rfl]`. Use `congrFun (congrFun hn1 a) a` as an intermediate fact. Simplify `this` using `[bdM]`. Rewrite using `[if_neg hab]`. Distinguish the cases in `hc : a < b ∧ Loc.sameBlock w₀.blocks a b = false`.

Rewrite using `[dif_pos hc]`. Rewrite using `[dif_neg hc]`. Distinguish the cases in `hlt : a < b`. Establish `hsb : Loc.sameBlock w₀.blocks a b = true`. Assume the negation of the conclusion as `hf; exact hc ⟨hlt, by simpa using hf⟩`.

Establish `hb'` using `(sameBlock_iff w₀.blocks w.1 hsz a.val b.val (by rw [hsum]; exact a.2) (by rw [hsum]; exact b.2)).1 hsb`. Use `congrFun (congrFun hn1 a) b` as an intermediate fact. Simplify using `only [bdM, Matrix.of_apply] at this`. Rewrite `this` using `[if_pos hb', Matrix.one_apply_ne hab]`. Conclude with `this`.

Conclude with `hnU.2 b a (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hab))`.
-/
theorem inOrbP_of_orb {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)}
    {w₀ : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)} (hw₀ : modPt δ T T' p w = some w₀) {Y : MatP D p}
    (h : ∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      Y = uL * modMat δ T T' p w * uU) : InOrbP δ T T' p w Y := by
  obtain ⟨uL, uU, hd, hz, hY⟩ := h
  have hL : IsLo uL := ⟨fun a => (hd a).1, fun a b hab => (hz a b hab).1⟩
  have hU : IsUp uU := ⟨fun a => (hd a).2, fun a b hab => (hz a b hab).2⟩
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hbs : ∀ b ∈ w.1, 1 ≤ b.2 := fun b hb => (w.2.1 b hb).2
  set blk : Fin (D.R.rS + 1) → ℕ := fun a => pSt w.1 a.val with hblk
  set σ := sgF w
  have hσσ : ∀ a, σ (σ a) = a := sgF_sgF w
  have hσblk : ∀ a, blk (σ a) = blk a := fun a => pSt_pSig w.1 a.val (by rw [hsum]; exact a.2)
  have hτ : ∀ a b, blk a = blk b → pSz w.1 a.val = pSz w.1 b.val ∧ pTau w.1 a.val = pTau w.1 b.val :=
    fun a b h => pSt_same w.1 hbs a.val b.val (by rw [hsum]; exact a.2) (by rw [hsum]; exact b.2) h
  have hrev : ∀ a b, blk a = blk b → a < b → σ b < σ a := by
    intro a b hab hlt
    obtain ⟨-, -, ea, -, -⟩ := pBlock w.1 a.val (by rw [hsum]; exact a.2)
    obtain ⟨-, -, eb, -, -⟩ := pBlock w.1 b.val (by rw [hsum]; exact b.2)
    have hs := (hτ a b hab).1
    have h1 : blk a = blk b := hab
    simp only [hblk] at h1
    show (σ b).val < (σ a).val
    simp only [σ, sgF]
    have : a.val < b.val := hlt
    omega
  set W := modMat δ T T' p w
  have hW : ∀ a b, W a b = if b = σ a then
      blkMod δ T T' p (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val) else 0 := fun a b => modMat_apply' δ T T' p w a b
  set β : MatP D p := bdM blk uU
  set β' : MatP D p := Matrix.of fun a b => β (σ a) (σ b)
  have hβU : IsUp β := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [β, bdM, Matrix.of_apply, if_true, hU.1]
    · simp only [β, bdM, Matrix.of_apply]; split_ifs <;> simp [hU.2 a b hab]
  have hβ'L : IsLo β' := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [β', Matrix.of_apply]; exact hβU.1 _
    · simp only [β', β, bdM, Matrix.of_apply]
      split_ifs with hb
      · rw [hσblk, hσblk] at hb
        exact hU.2 _ _ (hrev a b hb hab)
      · rfl
  have hWβ : W * β = β' * W := by
    ext a b
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single (σ a), Finset.sum_eq_single (σ b)]
    · rw [hW a (σ a), if_pos rfl, hW (σ b) b, if_pos (hσσ b).symm]
      simp only [β', Matrix.of_apply, hσσ, β, bdM]
      split_ifs with hb
      · have hab : blk a = blk (σ b) := (hσblk a).symm.trans (hb.trans (hσblk b).symm)
        obtain ⟨e1, e2⟩ := hτ a (σ b) hab
        have e0 : pSt w.1 a.val = pSt w.1 (σ b).val := hab
        rw [e0, e1, e2]; ring
      · rw [mul_zero, zero_mul]
    · intro c _ hc; rw [hW c b, if_neg (fun h => hc (by rw [h, hσσ])), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hc; rw [hW a c, if_neg hc, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hβdet : IsUnit β.det := by rw [det_up' hβU]; exact isUnit_one
  have hβblk : ∀ a c, blk a ≠ blk c → β a c = 0 := fun a c h => by simp [β, bdM, h]
  have hβi : bdM blk β⁻¹ = β⁻¹ := by
    have h1 := bdM_mul blk β β⁻¹ hβblk
    rw [Matrix.mul_nonsing_inv _ hβdet, bdM_one] at h1
    calc bdM blk β⁻¹ = β⁻¹ * (β * bdM blk β⁻¹) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hβdet, Matrix.one_mul]
      _ = β⁻¹ := by rw [← h1, Matrix.mul_one]
  have hβiblk : ∀ a c, blk a ≠ blk c → β⁻¹ a c = 0 := fun a c h => by
    rw [← hβi]; simp [bdM, h]
  obtain ⟨n, hn⟩ : ∃ n : MatP D p, n = β⁻¹ * uU := ⟨_, rfl⟩
  have hn1 : bdM blk n = 1 := by
    rw [hn, bdM_mul blk β⁻¹ uU hβiblk]
    show β⁻¹ * β = 1
    exact Matrix.nonsing_inv_mul _ hβdet
  have hnU : IsUp n := by rw [hn]; exact isUp_mul (isUp_inv hβU) hU
  have huU : uU = β * n := by
    rw [hn, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hβdet, Matrix.one_mul]
  have hY2 : Y = (uL * β') * W * n := by
    rw [hY, huU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc W β n, hWβ]
    simp only [Matrix.mul_assoc]
  have hLβ : IsLo (uL * β') := isLo_mul hL hβ'L
  have hsz : w₀.blocks.map (fun x => (x.2 : ℕ)) = w.1.map Prod.snd := by
    have h1 := modPt_blocks δ T T' p w w₀ hw₀
    have h2 := congrArg (List.map Prod.snd) h1
    simp only [List.map_map] at h2
    rw [PI.SupportDatumW.mapBlocks_snd] at h2
    exact h2
  refine ⟨w₀, hw₀, (fun x => (uL * β') x.1.1 x.1.2, fun y => n y.1.1 y.1.2), ?_⟩
  rw [hY2]
  congr 2
  · ext a b
    simp only [Loc.uLow]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, hLβ.1]
    · rw [if_neg hab]
      by_cases hlt : b < a
      · rw [dif_pos hlt]
      · rw [dif_neg hlt]
        exact hLβ.2 a b (lt_of_le_of_ne (not_lt.1 hlt) hab)
  · ext a b
    simp only [Loc.uUp]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl]
      have := congrFun (congrFun hn1 a) a
      simpa [bdM] using this
    · rw [if_neg hab]
      by_cases hc : a < b ∧ Loc.sameBlock w₀.blocks a b = false
      · rw [dif_pos hc]
      · rw [dif_neg hc]
        by_cases hlt : a < b
        · have hsb : Loc.sameBlock w₀.blocks a b = true := by
            by_contra hf; exact hc ⟨hlt, by simpa using hf⟩
          have hb' := (sameBlock_iff w₀.blocks w.1 hsz a.val b.val (by rw [hsum]; exact a.2)
            (by rw [hsum]; exact b.2)).1 hsb
          have := congrFun (congrFun hn1 a) b
          simp only [bdM, Matrix.of_apply] at this
          rw [if_pos hb', Matrix.one_apply_ne hab] at this
          exact this
        · exact hnU.2 b a (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hab))

/- English proof (translation)
Break down `hs : (D.s.atP p).split with _ | sg` into its components or cases. Conclude with `⟨0, by simpa using hns hs⟩`. Use `(D.s.atP p).char0` as an intermediate fact. Assume the negation of the conclusion as `H`. Use `push Not at H`.

Establish `key : ∀ n : ℕ, n < 3 → (sg.e c).1 + n = 0 ∨ (sg.e c).2 + n = 0`. Introduce `n hn`. Establish `h1` using `H ⟨n, hn⟩`. Simplify using `only at h1`. Rewrite `h1` using `[← MulEquiv.isUnit_map sg.e.toRingEquiv.toMulEquiv]`.

Simplify using `only [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, AlgEquiv.coe_ringEquiv, map_add, map_natCast, Prod.isUnit_iff, Prod.fst_add, Prod.snd_add, Prod.fst_natCast, Prod.snd_natCast, isUnit_iff_ne_zero, not_and_or, not_not] at h1`. Conclude with `h1`. Establish `h0` using `key 0 (by norm_num)`. Establish `h1` using `key 1 (by norm_num)`. Establish `h2` using `key 2 (by norm_num)`.

Move the coercions through the operations in `at h0 h1 h2`. Establish `o1 : (1 : (D.s.atP p).Fp) ≠ 0` using `one_ne_zero`. Establish `o2 : (2 : (D.s.atP p).Fp) ≠ 0` using `two_ne_zero`. Apply the tactic sequence `rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2`. Apply the tactic sequence `all_goals first`.

Consider the case `exact o1 (by linear_combination h1 - h0)`. Consider the case `exact o2 (by linear_combination h2 - h0)`. Consider the case `exact o1 (by linear_combination h2 - h1)`.
-/
theorem exists_shift_gen (p : PlF D) (c : (D.s.atP p).Ep) (hns : (D.s.atP p).split = none → IsUnit c) :
    ∃ n : Fin 3, IsUnit (c + (((n : Fin 3) : ℕ) : (D.s.atP p).Ep)) := by
  rcases hs : (D.s.atP p).split with _ | sg
  · exact ⟨0, by simpa using hns hs⟩
  · have := (D.s.atP p).char0
    by_contra H
    push Not at H
    have key : ∀ n : ℕ, n < 3 → (sg.e c).1 + n = 0 ∨ (sg.e c).2 + n = 0 := by
      intro n hn
      have h1 := H ⟨n, hn⟩
      simp only at h1
      rw [← MulEquiv.isUnit_map sg.e.toRingEquiv.toMulEquiv] at h1
      simp only [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, AlgEquiv.coe_ringEquiv, map_add, map_natCast,
        Prod.isUnit_iff, Prod.fst_add, Prod.snd_add, Prod.fst_natCast, Prod.snd_natCast, isUnit_iff_ne_zero, not_and_or,
        not_not] at h1
      exact h1
    have h0 := key 0 (by norm_num)
    have h1 := key 1 (by norm_num)
    have h2 := key 2 (by norm_num)
    push_cast at h0 h1 h2
    have o1 : (1 : (D.s.atP p).Fp) ≠ 0 := one_ne_zero
    have o2 : (2 : (D.s.atP p).Fp) ≠ 0 := two_ne_zero
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    all_goals first
      | exact o1 (by linear_combination h1 - h0)
      | exact o2 (by linear_combination h2 - h0)
      | exact o1 (by linear_combination h2 - h1)

/- English proof (translation)
The claim follows from `| a, [], _ => ⟨[], rfl⟩ | a, (t, s) :: rest, hb => by have h1 := hb (t, s) List.mem_cons_self have hu : IsUnit (blkTop δ T T' p a s t) := by by_cases hnt : a + s - 1 = D.R.rS + 1 ∧ s = 1 · have hx : ∃ n : Fin 3, IsUnit (blkMod δ T T' p a s t + (((n : Fin 3) : ℕ) : (D.s.atP p).Ep) …`.
-/
theorem modBlocks_full {δ : ∀ p : PlF D, (D.s.atP p).Fp} (T T' : ℕ) (p : PlF D) (hδ : δ p ≠ 0) :
    ∀ (a : ℕ) (l : List (D.host.E × ℕ)), (∀ b ∈ l, b.1 ≠ 0 ∧ 1 ≤ b.2) →
      ∃ l', modBlocks (blkTop δ T T' p) a l = some l'
  | a, [], _ => ⟨[], rfl⟩
  | a, (t, s) :: rest, hb => by
    have h1 := hb (t, s) List.mem_cons_self
    have hu : IsUnit (blkTop δ T T' p a s t) := by
      by_cases hnt : a + s - 1 = D.R.rS + 1 ∧ s = 1
      · have hx : ∃ n : Fin 3, IsUnit (blkMod δ T T' p a s t + (((n : Fin 3) : ℕ) : (D.s.atP p).Ep)) := by
          refine exists_shift_gen p _ fun hs => ?_
          unfold blkMod
          rw [if_pos hnt, LMK.tauZero_of_not_split hs, sub_zero, LMK.tMod_eq]
          exact (LMK.isUnit_ιE p h1.1).mul (LMK.isUnit_hF p hδ _ _)
        unfold blkTop
        rw [if_pos hnt]
        exact LMK.nSh_unit hx
      · rw [LMK.blkTop_nonTop δ T T' p hnt]
        exact (LMK.isUnit_ιE p h1.1).mul (LMK.isUnit_hF p hδ _ _)
    obtain ⟨l', hl'⟩ := modBlocks_full T T' p hδ (a + s) rest fun b hb' => hb b (List.mem_cons_of_mem _ hb')
    have hs0 : 0 < s := by omega
    have e : modBlocks (blkTop δ T T' p) a ((t, s) :: rest) = some ((hu.unit, ⟨s, hs0⟩) :: l') := by
      simp only [modBlocks]
      rw [dif_pos ⟨hu, hs0⟩, hl']
      rfl
    exact ⟨_, e⟩

/- English proof (translation)
Take `⟨l, hl⟩` from `modBlocks_full T T' p hδ 1 w.1 w.2.1`. Establish `hs : (l.map (fun b => (b.2 : ℕ))).sum = D.R.rS + 1`. Establish `h1` using `PI.SupportDatumW.modBlocks_some _ _ _ _ hl`. Establish `h2 : l.map (fun b => (b.2 : ℕ)) = (l.map (fun x => ((x.1 : (D.s.atP p).Ep), (x.2 : ℕ)))).map Prod.snd`. Simplify using the standard rewrite rules.

Rewrite using `[h2, h1, PI.SupportDatumW.mapBlocks_snd]`. Conclude with `w.2.2`. Conclude with `⟨_, LMK.modPt_of_blocks hl hs⟩`.
-/
theorem modPt_full {δ : ∀ p : PlF D, (D.s.atP p).Fp} (T T' : ℕ) (p : PlF D) (hδ : δ p ≠ 0)
    (w : Point D.host.E (D.R.rS + 1)) : ∃ a, modPt δ T T' p w = some a := by
  obtain ⟨l, hl⟩ := modBlocks_full T T' p hδ 1 w.1 w.2.1
  have hs : (l.map (fun b => (b.2 : ℕ))).sum = D.R.rS + 1 := by
    have h1 := PI.SupportDatumW.modBlocks_some _ _ _ _ hl
    have h2 : l.map (fun b => (b.2 : ℕ)) = (l.map (fun x => ((x.1 : (D.s.atP p).Ep), (x.2 : ℕ)))).map Prod.snd := by
      simp
    rw [h2, h1, PI.SupportDatumW.mapBlocks_snd]
    exact w.2.2
  exact ⟨_, LMK.modPt_of_blocks hl hs⟩

/- English proof (translation)
Introduce `w Z hZ p`. Take `⟨w₀, hw₀⟩` from `modPt_full (D.mem u).A.T (D.mem u').A.T p (Zd.agree p).2.1 w`. Conclude with `inOrbP_of_orb hw₀ (zzpSgn_orb Zd u u' hZ p)`.
-/
theorem inOrbZ_holds (Zd : LocDat D) (u u' : D.what₂.Word) : InOrbZ Zd u u' := by
  intro w Z hZ p
  obtain ⟨w₀, hw₀⟩ := modPt_full (D.mem u).A.T (D.mem u').A.T p (Zd.agree p).2.1 w
  exact inOrbP_of_orb hw₀ (zzpSgn_orb Zd u u' hZ p)

end Decomp

end Formalism.L2.SG.Pf.PCount
