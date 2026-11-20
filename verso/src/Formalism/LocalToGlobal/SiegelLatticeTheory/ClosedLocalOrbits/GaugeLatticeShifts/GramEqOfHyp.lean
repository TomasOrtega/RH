import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SurjOfIndep

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool)

def frm3 (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Fin r ⊕ (Fin r ⊕ Unit) → Fin n → ℂ :=
  Sum.elim e (Sum.elim f (fun _ => z))

structure Hyp (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (T : ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (f a) z = 0
  zz : hJ ε z z = -T

/- English proof (translation)
Rewrite using `[hJ_conj, h.ef]`. Distinguish the cases in `hab : b = a`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hab, if_neg (Ne.symm hab), map_zero]`.
-/
theorem Hyp.fe {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a b : Fin r) :
    hJ ε (f a) (e b) = if a = b then 1 else 0 := by
  rw [hJ_conj, h.ef]; by_cases hab : b = a
  · subst hab; simp
  · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]

/- English proof (translation)
Rewrite using `[hJ_conj, h.ez, map_zero]`.
-/
theorem Hyp.ze {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (e a) = 0 := by rw [hJ_conj, h.ez, map_zero]

/- English proof (translation)
Rewrite using `[hJ_conj, h.fz, map_zero]`.
-/
theorem Hyp.zf {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (f a) = 0 := by rw [hJ_conj, h.fz, map_zero]

/- English proof (translation)
Apply the tactic sequence `rcases i with a | a | _ <;> rcases j with b | b | _ <;>`. Simplify using `only [frm3, Sum.elim_inl, Sum.elim_inr, h.ee, h'.ee, h.ef, h'.ef, h.ff, h'.ff, h.ez, h'.ez, h.fz, h'.fz, h.zz, h'.zz, h.fe, h'.fe, h.ze, h'.ze, h.zf, h'.zf]`.
-/
theorem gram_eq_of_hyp {e f e' f' : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T : ℂ}
    (h : Hyp ε e f z T) (h' : Hyp ε e' f' z' T) (i j : Fin r ⊕ (Fin r ⊕ Unit)) :
    hJ ε (frm3 e f z i) (frm3 e f z j) = hJ ε (frm3 e' f' z' i) (frm3 e' f' z' j) := by
  rcases i with a | a | _ <;> rcases j with b | b | _ <;>
    simp only [frm3, Sum.elim_inl, Sum.elim_inr, h.ee, h'.ee, h.ef, h'.ef, h.ff, h'.ff, h.ez, h'.ez, h.fz, h'.fz,
      h.zz, h'.zz, h.fe, h'.fe, h.ze, h'.ze, h.zf, h'.zf]

/- English proof (translation)
Introduce `hdet`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Apply `hw0` to reduce the goal to its premises. Establish `row : ∀ i, ∑ j, hJ ε (frm3 e f z i) (frm3 e f z j) * w j = 0` using `fun i => by`. Use `congrFun hw i` as an intermediate fact.

Simplify `this` using `[mulVec, dotProduct]`. Use function extensionality and compare the values at `i`. Break down `i with a | a | u` into its components or cases. Use `row (Sum.inr (Sum.inl a))` as an intermediate fact. Simplify `this` using `[Fintype.sum_sum_type, frm3, h.fe, h.ff, h.fz]`.

Use `row (Sum.inl a)` as an intermediate fact. Simplify `this` using `[Fintype.sum_sum_type, frm3, h.ee, h.ef, h.ez]`. Use `row (Sum.inr (Sum.inr u))` as an intermediate fact. Simplify using `[Fintype.sum_sum_type, frm3, h.ze, h.zf, h.zz] at this`. Break down `this with h1 | h1` into its components or cases.

Conclude with `absurd h1 hT`. Simplify using `using h1`.
-/
theorem gram_nd_of_hyp {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (hT : T ≠ 0) (h : Hyp ε e f z T) :
    (Matrix.of fun i j => hJ ε (frm3 e f z i) (frm3 e f z j)).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hw0
  have row : ∀ i, ∑ j, hJ ε (frm3 e f z i) (frm3 e f z j) * w j = 0 := fun i => by
    have := congrFun hw i
    simpa [mulVec, dotProduct] using this
  funext i
  rcases i with a | a | u
  · have := row (Sum.inr (Sum.inl a))
    simpa [Fintype.sum_sum_type, frm3, h.fe, h.ff, h.fz] using this
  · have := row (Sum.inl a)
    simpa [Fintype.sum_sum_type, frm3, h.ee, h.ef, h.ez] using this
  · have := row (Sum.inr (Sum.inr u))
    simp [Fintype.sum_sum_type, frm3, h.ze, h.zf, h.zz] at this
    rcases this with h1 | h1
    · exact absurd h1 hT
    · simpa using h1

/- English proof (translation)
Use `set sN := Finset.univ.filter (fun i : Fin n => ε i = false) with hsN`. Use `set sP := Finset.univ.filter (fun i : Fin n => ε i = true) with hsP`. Establish `hcard : sP.card + sN.card = n`. Use `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => ε i = true)` as an intermediate fact. Simplify using `only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this`.

Conclude with `this`. Establish `hP : sP.card = r + k` using `by omega`. Set `eN` to `sN.equivFinOfCardEq hsig`. Set `eP` to `sP.equivFinOfCardEq hP`. Use `⟨fun y => (eN.symm y).1, fun x => (eP.symm x).1, ?_, ?_, fun y => ?_, fun x => ?_⟩` and prove the remaining obligations.

Conclude with `Subtype.val_injective.comp eN.symm.injective`. Conclude with `Subtype.val_injective.comp eP.symm.injective`. Conclude with `(Finset.mem_filter.1 (eN.symm y).2).2`. Conclude with `(Finset.mem_filter.1 (eP.symm x).2).2`.
-/
theorem coord_inj {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ (N : Fin (r + 1) → Fin n) (P : Fin (r + k) → Fin n), Function.Injective N ∧ Function.Injective P ∧
      (∀ y, ε (N y) = false) ∧ (∀ x, ε (P x) = true) := by
  set sN := Finset.univ.filter (fun i : Fin n => ε i = false) with hsN
  set sP := Finset.univ.filter (fun i : Fin n => ε i = true) with hsP
  have hcard : sP.card + sN.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => ε i = true)
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
    exact this
  have hP : sP.card = r + k := by omega
  let eN := sN.equivFinOfCardEq hsig
  let eP := sP.equivFinOfCardEq hP
  refine ⟨fun y => (eN.symm y).1, fun x => (eP.symm x).1, ?_, ?_, fun y => ?_, fun x => ?_⟩
  · exact Subtype.val_injective.comp eN.symm.injective
  · exact Subtype.val_injective.comp eP.symm.injective
  · exact (Finset.mem_filter.1 (eN.symm y).2).2
  · exact (Finset.mem_filter.1 (eP.symm x).2).2

/- English proof (translation)
Take `⟨N, P, hN, hP, hNs, hPs⟩` from `coord_inj ε hdim hsig`. Establish `hNP : ∀ y x, N y ≠ P x` using `fun y x h => by have := hNs y; rw [h, hPs x] at this; exact Bool.noConfusion this`. Use `set sq : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hsq`. Establish `hsqc : conj sq = sq` using `Complex.conj_ofReal _`. Establish `hsq2 : sq * sq = 1 / 2`.

Rewrite using `[hsq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `p : Fin r → Fin n` to `fun c => P (Fin.castAdd k c)`. Set `q : Fin r → Fin n` to `fun c => N (Fin.castSucc c)`.

Set `qz : Fin n` to `N (Fin.last r)`. Set `wi : Fin k → Fin n` to `fun j => P (Fin.natAdd r j)`. Set `e0 : Fin r → Fin n → ℂ` to `fun c => sq • (dl (p c) + dl (q c))`. Set `f0 : Fin r → Fin n → ℂ` to `fun c => sq • (dl (p c) - dl (q c))`. Set `z0 : Fin n → ℂ` to `((Real.sqrt T : ℝ) : ℂ) • dl qz`.

Set `w0 : Fin k → Fin n → ℂ` to `fun j => dl (wi j)`. Establish `hp : Function.Injective p` using `hP.comp (Fin.castAdd_injective r k)`. Establish `hq : Function.Injective q` using `hN.comp (Fin.castSucc_injective r)`. Establish `hqz : ∀ c, q c ≠ qz` using `fun c h => Fin.castSucc_ne_last c (hN h)`. Establish `hwi : Function.Injective wi` using `hP.comp (Fin.natAdd_injective k r)`.

Establish `hpw : ∀ c j, p c ≠ wi j` using `fun c j h => by`. Establish `h1` using `congrArg Fin.val (hP h)`. Simplify using `only [Fin.coe_castAdd, Fin.coe_natAdd] at h1`. Use linear arithmetic over natural numbers and integers. Establish `hd : ∀ i j, hJ ε (dl i) (dl j) = if i = j then (if ε i then 1 else -1) else 0` using `hJ_dl ε`.

Establish `pp : ∀ a b, hJ ε (dl (p a)) (dl (p b)) = if a = b then 1 else 0` using `fun a b => by`. Rewrite using `[hd]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[p, hPs]`.

Rewrite using `[if_neg (hp.ne hab), if_neg hab]`. Establish `qq : ∀ a b, hJ ε (dl (q a)) (dl (q b)) = if a = b then -1 else 0` using `fun a b => by`. Rewrite using `[hd]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[q, hNs]`. Rewrite using `[if_neg (hq.ne hab), if_neg hab]`. Establish `pq : ∀ a b, hJ ε (dl (p a)) (dl (q b)) = 0` using `fun a b => by rw [hd, if_neg (hNP _ _).symm]`. Establish `qp : ∀ a b, hJ ε (dl (q a)) (dl (p b)) = 0` using `fun a b => by rw [hd, if_neg (hNP _ _)]`. Establish `h0 : Hyp ε e0 f0 z0 (T : ℂ)`.

Use `⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `simp only [e0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_add_right, pp, qq, pq, qp, hsqc] split_ifs <;> ring`. Simplify using `only [e0, f0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_sub_right, pp, qq, pq, qp, hsqc] split_ifs`. Take the linear combination `2 * hsq2`. Expand and normalize the polynomial expressions, which then agree.

Apply the tactic sequence `simp only [f0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hJ_sub_right, pp, qq, pq, qp, hsqc] split_ifs <;> ring`. Establish `h1 : p a ≠ qz` using `(hNP _ _).symm`. Simplify using `only [e0, z0, hJ_smul_left, hJ_smul_right, hJ_add_left, hd, if_neg h1, if_neg (hqz a)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : p a ≠ qz` using `(hNP _ _).symm`.

Simplify using `only [f0, z0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hd, if_neg h1, if_neg (hqz a)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ)`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]`. Establish `hq0 : ε qz = false` using `hNs _`.

Simplify using `only [z0, hJ_smul_left, hJ_smul_right, hd, if_true, Complex.conj_ofReal, hq0, Bool.false_eq_true, if_false]`. Take the linear combination `(-1 : ℂ) * hs`. Take `⟨g, hg⟩` from `witt_of_gram' ε (frm3 e0 f0 z0) (frm3 e f z) (gram_eq_of_hyp ε h0 h) (gram_nd_of_hyp ε (by exact_mod_cast hT.ne') h0)`. Establish `hiso` using `isIsom_uMat ε g`. Establish `he : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ e0 c = e c` using `fun c => hg (Sum.inl c)`.

Establish `hf : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ f0 c = f c` using `fun c => hg (Sum.inr (Sum.inl c))`. Establish `hz : Formalism.MainNotions.S.uMat g *ᵥ z0 = z` using `hg (Sum.inr (Sum.inr ()))`. Establish `ww : ∀ a b, hJ ε (w0 a) (w0 b) = if a = b then 1 else 0` using `fun a b => by`. Simplify using `only [w0]`. Rewrite using `[hd]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[wi, hPs]`. Rewrite using `[if_neg (hwi.ne hab), if_neg hab]`. Establish `pw : ∀ c j, hJ ε (dl (p c)) (w0 j) = 0` using `fun c j => by simp only [w0]; rw [hd, if_neg (hpw c j)]`.

Establish `qw : ∀ c j, hJ ε (dl (q c)) (w0 j) = 0` using `fun c j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]`. Establish `zw : ∀ j, hJ ε (dl qz) (w0 j) = 0` using `fun j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]`. Use `⟨fun j => Formalism.MainNotions.S.uMat g *ᵥ w0 j, fun a b => by rw [hiso, ww], fun c a => ?_, fun c a => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← he, hiso]`. Simplify using `only [e0, hJ_smul_left, hJ_add_left, pw, qw]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hf, hiso]`. Simplify using `only [f0, hJ_smul_left, hJ_sub_left, pw, qw]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hz, hiso]`.

Simplify using `only [z0, hJ_smul_left, zw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem complement {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1)
    {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ} (hT : 0 < T) (h : Hyp ε e f z (T : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      (∀ c a, hJ ε (e c) (w a) = 0) ∧ (∀ c a, hJ ε (f c) (w a) = 0) ∧ (∀ a, hJ ε z (w a) = 0) := by
  obtain ⟨N, P, hN, hP, hNs, hPs⟩ := coord_inj ε hdim hsig
  have hNP : ∀ y x, N y ≠ P x := fun y x h => by have := hNs y; rw [h, hPs x] at this; exact Bool.noConfusion this
  set sq : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hsq
  have hsqc : conj sq = sq := Complex.conj_ofReal _
  have hsq2 : sq * sq = 1 / 2 := by
    rw [hsq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let p : Fin r → Fin n := fun c => P (Fin.castAdd k c)
  let q : Fin r → Fin n := fun c => N (Fin.castSucc c)
  let qz : Fin n := N (Fin.last r)
  let wi : Fin k → Fin n := fun j => P (Fin.natAdd r j)
  let e0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) + dl (q c))
  let f0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) - dl (q c))
  let z0 : Fin n → ℂ := ((Real.sqrt T : ℝ) : ℂ) • dl qz
  let w0 : Fin k → Fin n → ℂ := fun j => dl (wi j)
  have hp : Function.Injective p := hP.comp (Fin.castAdd_injective r k)
  have hq : Function.Injective q := hN.comp (Fin.castSucc_injective r)
  have hqz : ∀ c, q c ≠ qz := fun c h => Fin.castSucc_ne_last c (hN h)
  have hwi : Function.Injective wi := hP.comp (Fin.natAdd_injective k r)
  have hpw : ∀ c j, p c ≠ wi j := fun c j h => by
    have h1 := congrArg Fin.val (hP h)
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
    omega
  have hd : ∀ i j, hJ ε (dl i) (dl j) = if i = j then (if ε i then 1 else -1) else 0 := hJ_dl ε
  have pp : ∀ a b, hJ ε (dl (p a)) (dl (p b)) = if a = b then 1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [p, hPs]
    · rw [if_neg (hp.ne hab), if_neg hab]
  have qq : ∀ a b, hJ ε (dl (q a)) (dl (q b)) = if a = b then -1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [q, hNs]
    · rw [if_neg (hq.ne hab), if_neg hab]
  have pq : ∀ a b, hJ ε (dl (p a)) (dl (q b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _).symm]
  have qp : ∀ a b, hJ ε (dl (q a)) (dl (p b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _)]
  have h0 : Hyp ε e0 f0 z0 (T : ℂ) := by
    refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_⟩
    · simp only [e0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_add_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · simp only [e0, f0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs
      · linear_combination 2 * hsq2
      · ring
    · simp only [f0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [e0, z0, hJ_smul_left, hJ_smul_right, hJ_add_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [f0, z0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have hs : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
      have hq0 : ε qz = false := hNs _
      simp only [z0, hJ_smul_left, hJ_smul_right, hd, if_true, Complex.conj_ofReal, hq0, Bool.false_eq_true,
        if_false]
      linear_combination (-1 : ℂ) * hs
  obtain ⟨g, hg⟩ := witt_of_gram' ε (frm3 e0 f0 z0) (frm3 e f z) (gram_eq_of_hyp ε h0 h)
    (gram_nd_of_hyp ε (by exact_mod_cast hT.ne') h0)
  have hiso := isIsom_uMat ε g
  have he : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ e0 c = e c := fun c => hg (Sum.inl c)
  have hf : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ f0 c = f c := fun c => hg (Sum.inr (Sum.inl c))
  have hz : Formalism.MainNotions.S.uMat g *ᵥ z0 = z := hg (Sum.inr (Sum.inr ()))
  have ww : ∀ a b, hJ ε (w0 a) (w0 b) = if a = b then 1 else 0 := fun a b => by
    simp only [w0]; rw [hd]; by_cases hab : a = b
    · subst hab; simp [wi, hPs]
    · rw [if_neg (hwi.ne hab), if_neg hab]
  have pw : ∀ c j, hJ ε (dl (p c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hpw c j)]
  have qw : ∀ c j, hJ ε (dl (q c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  have zw : ∀ j, hJ ε (dl qz) (w0 j) = 0 := fun j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  refine ⟨fun j => Formalism.MainNotions.S.uMat g *ᵥ w0 j, fun a b => by rw [hiso, ww], fun c a => ?_, fun c a => ?_, fun a => ?_⟩
  · rw [← he, hiso]; simp only [e0, hJ_smul_left, hJ_add_left, pw, qw]; ring
  · rw [← hf, hiso]; simp only [f0, hJ_smul_left, hJ_sub_left, pw, qw]; ring
  · rw [← hz, hiso]; simp only [z0, hJ_smul_left, zw]; ring

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
