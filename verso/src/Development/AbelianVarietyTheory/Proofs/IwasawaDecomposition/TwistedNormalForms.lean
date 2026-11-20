import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ToLinNfMatEqSumNfGen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeSandwichOfLatticeNormalForm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.Proof.TwistedNormalForms

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.QNormal

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Consider the cases of `c with`. Consider the case `zero => simp [Loc.atN]`. Consider the case `succ c`. Rewrite using `[Fin.sum_univ_succ]`. Establish `h0 : ∀ i : Fin c, ¬ ((Fin.succ i).1 = 0)` using `fun i => by simp`.

Simplify using `only [Fin.val_zero, if_true, h0, if_false, Finset.sum_const_zero, add_zero]`. Unfold `Loc.atN`. Rewrite using `[dif_pos (by omega)]`. Use `congr 1`.
-/
theorem sum_ite_zero_eq_atN {n c : ℕ} (y : Fin (n + c) → E) :
    ∑ i : Fin c, (if i.1 = 0 then y (Fin.natAdd n i) else 0) = Loc.atN y n := by
  cases c with
  | zero => simp [Loc.atN]
  | succ c =>
    rw [Fin.sum_univ_succ]
    have h0 : ∀ i : Fin c, ¬ ((Fin.succ i).1 = 0) := fun i => by simp
    simp only [Fin.val_zero, if_true, h0, if_false, Finset.sum_const_zero, add_zero]
    unfold Loc.atN
    rw [dif_pos (by omega)]
    congr 1

/- English proof (translation)
Establish `hx : ∀ w : Sp E n, Loc.inX E n c w (Fin.natAdd n b) = 0` using `fun w => by`. Rewrite using `[inX_apply, dif_neg (by simp)]`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nfGen, smul_eq_mul, hx, zero_add]`. Rewrite using `[Finset.sum_eq_single b]`. Apply the tactic sequence `have : (if b.1 = 0 then Loc.inX E n c z else 0) (Fin.natAdd n b) = 0 := by split_ifs <;> simp [hx]`.

Simplify using `[Loc.eN, this]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i _ hib`. Establish `hne : ¬ ((Fin.natAdd n b).1 = n + i.1)`. Introduce `h`.

Apply `hib` to reduce the goal to its premises. Use `ext`. Simplify using `at h`. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `have : (if i.1 = 0 then Loc.inX E n c z else 0) (Fin.natAdd n b) = 0 := by split_ifs <;> simp [hx]`.

Establish `hne' : ¬ (b.1 = i.1)` using `fun h => hib (Fin.ext h).symm`. Simplify using `[Loc.eN, hne', this]`. Simplify using the standard rewrite rules.
-/
theorem comb_natAdd (q : ℕ) {n c : ℕ} (e : Fin c → ℤ) (z : Sp E n) (l : Sp E n) (s : Fin c → E) (b : Fin c) :
    (Loc.inX E n c l + ∑ i, s i • nfGen q n c e z i) (Fin.natAdd n b) = (q : E) ^ e b * s b := by
  have hx : ∀ w : Sp E n, Loc.inX E n c w (Fin.natAdd n b) = 0 := fun w => by
    rw [inX_apply, dif_neg (by simp)]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nfGen, smul_eq_mul, hx, zero_add]
  rw [Finset.sum_eq_single b]
  · have : (if b.1 = 0 then Loc.inX E n c z else 0) (Fin.natAdd n b) = 0 := by
      split_ifs <;> simp [hx]
    simp [Loc.eN, this]
    ring
  · intro i _ hib
    have hne : ¬ ((Fin.natAdd n b).1 = n + i.1) := by
      intro h; apply hib; ext; simp at h; omega
    have : (if i.1 = 0 then Loc.inX E n c z else 0) (Fin.natAdd n b) = 0 := by
      split_ifs <;> simp [hx]
    have hne' : ¬ (b.1 = i.1) := fun h => hib (Fin.ext h).symm
    simp [Loc.eN, hne', this]
  · simp

/- English proof (translation)
Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nfGen, smul_eq_mul, inX_castAdd, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hne : ¬ (a.1 = n + i.1)` using `by omega`. Use `split_ifs with hi`.

Simplify using `[Loc.eN, hne, inX_castAdd]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Loc.eN, hne]`.
-/
theorem comb_castAdd (q : ℕ) {n c : ℕ} (e : Fin c → ℤ) (z : Sp E n) (l : Sp E n) (s : Fin c → E) (a : Fin n) :
    (Loc.inX E n c l + ∑ i, s i • nfGen q n c e z i) (Fin.castAdd c a) =
      l a + (∑ i : Fin c, (if i.1 = 0 then (q : E) ^ e i * s i else 0)) * z a := by
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nfGen, smul_eq_mul, inX_castAdd, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : ¬ (a.1 = n + i.1) := by omega
  split_ifs with hi
  · simp [Loc.eN, hne, inX_castAdd]; ring
  · simp [Loc.eN, hne]

end Lattice

/- English proof (translation)
Introduce `X Pr R j P hP h hT`. Use `(GlobalTheory.QNF.nf_iff_matNF X Pr R j P hP h).1 ?_` and prove the remaining obligations. Take `⟨n, z, hn, hz, hcrit⟩` from `hT`. Use `⟨fun i => n i.1, z, fun i => hn i.1, hz, ?_⟩` and prove the remaining obligations. Establish `hq` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P`.

Establish `hzV` using `(mem_stdAt_iff z).1 hz`. Use extensionality with `y`. Establish `hmem : y ∈ h '' (lamYat (Pr` using `Pr) (R := R) j P : Set _) ↔ h⁻¹ y ∈ lamYat (Pr := Pr) (R := R) j P := by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Simplify using `using hx`. Introduce `hy`. Conclude with `⟨h⁻¹ y, hy, by simp⟩`. Rewrite using `[hmem, hcrit y]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hX, hN⟩`. Use `⟨fun a => y (Fin.castAdd _ a) - Loc.atN y (R.N j) * z a, (mem_stdAt_iff _).2 hX, fun i => ((qOf P : X.E) ^ n i.1)⁻¹ * y (Fin.natAdd _ i), hN, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) p` and prove the remaining obligations. Rewrite using `[comb_castAdd]`.

Establish `: ∀ i : Fin (cOf R j), (if i.1 = 0 then (qOf P : X.E) ^ n i.1 * (((qOf P : X.E) ^ n i.1)⁻¹ * y (Fin.natAdd _ i)) else 0) = (if i.1 = 0 then y (Fin.natAdd _ i) else 0)` using `fun i => by`. Rewrite using `[mul_inv_cancel_left₀ (zpow_ne_zero _ hq)]`. Simplify using `only [this, sum_ite_zero_eq_atN]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[comb_natAdd, mul_inv_cancel_left₀ (zpow_ne_zero _ hq)]`.

Introduce and unpack `⟨l, hl, s, hs, rfl⟩`. Establish `hlV` using `(mem_stdAt_iff l).1 hl`. Establish `hb` using `comb_natAdd (qOf P) (fun i : Fin (cOf R j) => n i.1) z l s`. Establish `hat : Loc.atN (Loc.inX X.E (R.N j) (cOf R j) l + ∑ i, s i • nfGen (qOf P) (R.N j) (cOf R j) (fun i => n i.1) z i) (R.N j) = ∑ i : Fin (cOf R j), (if i.1 = 0 then (qOf P : X.E) ^ n i.1 * s i else 0)`. Rewrite using `[← sum_ite_zero_eq_atN]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hb i]`. Use `⟨fun a => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[comb_castAdd, hat, add_sub_cancel_right]`. Conclude with `hlV a`.

Rewrite using `[hb i, inv_mul_cancel_left₀ (zpow_ne_zero _ hq)]`. Conclude with `hs i`.
-/
theorem twNF_imp_matNF : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)),
    P ∉ Pr.vGs → ∀ h : AutY X R j, TwNF (Pr := Pr) j P h → GlobalTheory.QNF.MatNF Pr R j P h := by
  intro X Pr R j P hP h hT
  refine (GlobalTheory.QNF.nf_iff_matNF X Pr R j P hP h).1 ?_
  obtain ⟨n, z, hn, hz, hcrit⟩ := hT
  refine ⟨fun i => n i.1, z, fun i => hn i.1, hz, ?_⟩
  have hq := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  have hzV := (mem_stdAt_iff z).1 hz
  ext y
  have hmem : y ∈ h '' (lamYat (Pr := Pr) (R := R) j P : Set _) ↔ h⁻¹ y ∈ lamYat (Pr := Pr) (R := R) j P := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨h⁻¹ y, hy, by simp⟩
  rw [hmem, hcrit y]
  constructor
  · rintro ⟨hX, hN⟩
    refine ⟨fun a => y (Fin.castAdd _ a) - Loc.atN y (R.N j) * z a, (mem_stdAt_iff _).2 hX,
      fun i => ((qOf P : X.E) ^ n i.1)⁻¹ * y (Fin.natAdd _ i), hN, ?_⟩
    funext p
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · rw [comb_castAdd]
      have : ∀ i : Fin (cOf R j), (if i.1 = 0 then (qOf P : X.E) ^ n i.1 * (((qOf P : X.E) ^ n i.1)⁻¹ * y (Fin.natAdd _ i)) else 0)
          = (if i.1 = 0 then y (Fin.natAdd _ i) else 0) := fun i => by
        rw [mul_inv_cancel_left₀ (zpow_ne_zero _ hq)]
      simp only [this, sum_ite_zero_eq_atN]
      ring
    · rw [comb_natAdd, mul_inv_cancel_left₀ (zpow_ne_zero _ hq)]
  · rintro ⟨l, hl, s, hs, rfl⟩
    have hlV := (mem_stdAt_iff l).1 hl
    have hb := comb_natAdd (qOf P) (fun i : Fin (cOf R j) => n i.1) z l s
    have hat : Loc.atN (Loc.inX X.E (R.N j) (cOf R j) l + ∑ i, s i • nfGen (qOf P) (R.N j) (cOf R j) (fun i => n i.1) z i) (R.N j)
        = ∑ i : Fin (cOf R j), (if i.1 = 0 then (qOf P : X.E) ^ n i.1 * s i else 0) := by
      rw [← sum_ite_zero_eq_atN]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb i]
    refine ⟨fun a => ?_, fun i => ?_⟩
    · rw [comb_castAdd, hat, add_sub_cancel_right]
      exact hlV a
    · rw [hb i, inv_mul_cancel_left₀ (zpow_ne_zero _ hq)]
      exact hs i

end GlobalTheory.Proof.TwistedNormalForms
