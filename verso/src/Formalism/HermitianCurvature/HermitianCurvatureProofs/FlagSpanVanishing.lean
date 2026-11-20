import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearChangeOfVariablesBis

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace FlagSpanVanishing

open C2x5 C2x7

variable {k r : ℕ}

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨b, hb⟩, rfl⟩` from `hx`. Establish `hbr : b.val < r` using `by have := a.isLt; rw [Fin.lt_def] at hb; omega`. Simplify using `only [fvec, dif_pos hbr, bvec, Pi.single_apply, eI]`.

Rewrite using `[if_neg]`. Introduce `e`. Rewrite `hb` using `[Fin.lt_def]`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Consider the case `zero => rfl`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul c x _ hx => simp [hx]`.
-/
lemma flagSpan_vanish (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : v ∈ C2.flagSpan k r z a) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) : v i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    have hbr : b.val < r := by have := a.isLt; rw [Fin.lt_def] at hb; omega
    simp only [fvec, dif_pos hbr, bvec, Pi.single_apply, eI]
    rw [if_neg]
    intro e; rw [Fin.lt_def] at hb; have := congrArg Fin.val e; simp at this; omega
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
lemma mulVec_bvec (M : B.Mat k r) (x : Fin (2 * r + k + 1)) : M *ᵥ bvec x = fun i => M i x := by
  funext i; simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def wpart (s : B.Mat k r) : B.Mat k r := fun i j =>
  if r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ j.val ∧ j.val ≤ r + k then s i j else if i = j then 1 else 0

/- English proof (translation)
Establish `hU : sᴴ * Hpk k r * s = Hpk k r` using `hs`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `a ha`.

Establish `e` using `congrFun (congrFun hU (eI k r a)) j`. Rewrite `e` using `[Matrix.mul_assoc, Matrix.mul_apply]`. Simplify using `only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e`. Establish `hH : Hpk k r (eI k r a) j = 0`. Rewrite using `[GBasic.Hpk_eq, if_neg]`.

Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Rewrite using `[GBasic.sig_lo _ _ _ (by simp [eI])] at this; simp [eI] at this; omega`. Rewrite `e` using `[hH, Finset.sum_eq_single (eI k r a)]`. Rewrite `e` using `[hcol a _ (by simp [eI]), if_pos rfl, star_one, one_mul]`.

Establish `hsig : GBasic.sig k r (eI k r a) = esI k r a`. Apply `Fin.ext; rw [GBasic.sig_lo _ _ _ (by simp [eI])]; simp [eI, esI]` to reduce the goal to its premises. Establish `hsg : GBasic.sgn k r (eI k r a) = 1`. Unfold `GBasic.sgn`. Rewrite using `[if_neg]`.

Simplify using `[eI]`. Use linear arithmetic over natural numbers and integers. Rewrite `e` using `[hsig, hsg, one_mul]`. Conclude with `e`. Introduce `p _ hp`.

Distinguish the cases in `hpa : a.val ≤ p.val`. Rewrite using `[hcol a p hpa, if_neg hp, star_zero, zero_mul]`. Use `push_neg at hpa`. Establish `hpr : p.val < r` using `by omega`. Establish `hsig : GBasic.sig k r p = esI k r ⟨p.val, hpr⟩`.

Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[GBasic.sig_lo _ _ _ hpr]`. Simplify using `[esI]`. Rewrite using `[hsig, ih p.val (by omega) ⟨p.val, hpr⟩ rfl, mul_zero, mul_zero]`. Simplify using the standard rewrite rules.
-/
lemma zero_block (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0)
    (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    ∀ n : ℕ, ∀ a : Fin r, a.val = n → s (esI k r a) j = 0 := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha
    have e := congrFun (congrFun hU (eI k r a)) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at e
    simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
    have hH : Hpk k r (eI k r a) j = 0 := by
      rw [GBasic.Hpk_eq, if_neg]
      intro h'; have := congrArg Fin.val h'
      rw [GBasic.sig_lo _ _ _ (by simp [eI])] at this; simp [eI] at this; omega
    rw [hH, Finset.sum_eq_single (eI k r a)] at e
    · rw [hcol a _ (by simp [eI]), if_pos rfl, star_one, one_mul] at e
      have hsig : GBasic.sig k r (eI k r a) = esI k r a := by
        apply Fin.ext; rw [GBasic.sig_lo _ _ _ (by simp [eI])]; simp [eI, esI]
      have hsg : GBasic.sgn k r (eI k r a) = 1 := by
        unfold GBasic.sgn; rw [if_neg]; simp [eI]; omega
      rw [hsig, hsg, one_mul] at e
      exact e
    · intro p _ hp
      by_cases hpa : a.val ≤ p.val
      · rw [hcol a p hpa, if_neg hp, star_zero, zero_mul]
      · push_neg at hpa
        have hpr : p.val < r := by omega
        have hsig : GBasic.sig k r p = esI k r ⟨p.val, hpr⟩ := by
          apply Fin.ext; rw [GBasic.sig_lo _ _ _ hpr]; simp [esI]
        rw [hsig, ih p.val (by omega) ⟨p.val, hpr⟩ rfl, mul_zero, mul_zero]
    · simp

end FlagSpanVanishing

namespace FlagSpanVanishing

open C2x5 C2x7

variable {k r : ℕ}

/- English proof (translation)
Use `GBasic.sig_val k r x` as an intermediate fact. Establish `hx'` using `x.isLt`. Apply the tactic sequence `split_ifs at this <;> omega`.
-/
lemma sig_notW (x : Fin (2 * r + k + 1)) (hx : ¬ (r ≤ x.val ∧ x.val ≤ r + k)) :
    ¬ (r ≤ (GBasic.sig k r x).val ∧ (GBasic.sig k r x).val ≤ r + k) := by
  have := GBasic.sig_val k r x
  have hx' := x.isLt
  split_ifs at this <;> omega

/- English proof (translation)
The claim follows from `GBasic.sig_mid k r x hx.1 hx.2`.
-/
lemma sig_fixes_middle_block (x : Fin (2 * r + k + 1)) (hx : r ≤ x.val ∧ x.val ≤ r + k) : GBasic.sig k r x = x :=
  GBasic.sig_mid k r x hx.1 hx.2

/- English proof (translation)
Establish `hU : sᴴ * Hpk k r * s = Hpk k r` using `hs`. Use `show (wpart s)ᴴ * Hpk k r * wpart s = Hpk k r`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_apply]`. Simplify using `only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply]`.

Distinguish the cases in `hi : r ≤ i.val ∧ i.val ≤ r + k`. Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`. Establish `e` using `congrFun (congrFun hU i) j`. Rewrite `e` using `[Matrix.mul_assoc, Matrix.mul_apply]`. Simplify using `only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e`.

Rewrite using `[← e]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : r ≤ p.val ∧ p.val ≤ r + k`. Rewrite using `[sig_fixes_middle_block p hp]`. Simplify using `only [wpart, if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hi.1 hi.2))), if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hj.1 hj.2)))]`.

Establish `h1 : wpart s p i = 0`. Simplify using `only [wpart]`. Rewrite using `[if_neg (fun h => hp ⟨h.1, h.2.1⟩), if_neg]`. Introduce `e`. Rewrite `hp` using `[e]`.

Conclude with `hp hi`. Rewrite using `[h1, star_zero, zero_mul]`. Distinguish the cases in `hpr : p.val < r`. Establish `: r + k < (GBasic.sig k r p).val` using `by rw [GBasic.sig_lo _ _ _ hpr]; omega`. Rewrite using `[hA _ j this hj.1 hj.2, mul_zero, mul_zero]`.

Establish `: r + k < p.val` using `by omega`. Rewrite using `[hA p i this hi.1 hi.2, star_zero, zero_mul]`. Rewrite using `[Finset.sum_eq_single (GBasic.sig k r j)]`. Establish `h1 : wpart s (GBasic.sig k r j) i = 0`. Simplify using `only [wpart]`.

Rewrite using `[if_neg (fun h => sig_notW j hj ⟨h.1, h.2.1⟩), if_neg]`. Introduce `e`. Rewrite `hi` using `[← e]`. Conclude with `sig_notW j hj hi`. Rewrite using `[h1, star_zero, zero_mul, GBasic.Hpk_eq, if_neg]`.

Introduce `e`. Rewrite `e` using `[sig_fixes_middle_block i hi]`. Rewrite `hj` using `[e]`. Conclude with `hj hi`. Introduce `p _ hp`.

Establish `: wpart s (GBasic.sig k r p) j = 0`. Simplify using `only [wpart]`. Rewrite using `[if_neg (fun h => hj ⟨h.2.2.1, h.2.2.2⟩), if_neg]`. Introduce `e`. Apply `hp` to reduce the goal to its premises.

Rewrite using `[← e, GBasic.sig_sig]`. Rewrite using `[this, mul_zero, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_single i]`. Establish `h1 : wpart s i i = 1`.

Simplify using `only [wpart]`. Rewrite using `[if_neg (fun h => hi ⟨h.1, h.2.1⟩)]`. Simplify using the standard rewrite rules. Establish `h2 : wpart s (GBasic.sig k r i) j = if GBasic.sig k r i = j then 1 else 0`. Simplify using `only [wpart]`.

Rewrite using `[if_neg (fun h => sig_notW i hi ⟨h.1, h.2.1⟩)]`. Rewrite using `[h1, star_one, one_mul, h2, GBasic.Hpk_eq]`. Distinguish the cases in `e : GBasic.sig k r i = j`. Rewrite using `[if_pos e, if_pos e.symm, mul_one]`. Rewrite using `[if_neg e, if_neg (fun h => e h.symm), mul_zero]`.

Introduce `p _ hp`. Establish `: wpart s p i = 0`. Simplify using `only [wpart]`. Rewrite using `[if_neg (fun h => hi ⟨h.2.2.1, h.2.2.2⟩), if_neg hp]`. Rewrite using `[this, star_zero, zero_mul]`.

Simplify using the standard rewrite rules.
-/
lemma wpart_uh (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0) :
    wpart s ∈ UH (Hpk k r) := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  show (wpart s)ᴴ * Hpk k r * wpart s = Hpk k r
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · have e := congrFun (congrFun hU i) j
      rw [Matrix.mul_assoc, Matrix.mul_apply] at e
      simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
      rw [← e]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [sig_fixes_middle_block p hp]
        simp only [wpart, if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hi.1 hi.2))),
          if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hj.1 hj.2)))]
      · have h1 : wpart s p i = 0 := by
          simp only [wpart]; rw [if_neg (fun h => hp ⟨h.1, h.2.1⟩), if_neg]
          intro e; rw [e] at hp; exact hp hi
        rw [h1, star_zero, zero_mul]
        by_cases hpr : p.val < r
        · have : r + k < (GBasic.sig k r p).val := by rw [GBasic.sig_lo _ _ _ hpr]; omega
          rw [hA _ j this hj.1 hj.2, mul_zero, mul_zero]
        · have : r + k < p.val := by omega
          rw [hA p i this hi.1 hi.2, star_zero, zero_mul]
    · rw [Finset.sum_eq_single (GBasic.sig k r j)]
      · have h1 : wpart s (GBasic.sig k r j) i = 0 := by
          simp only [wpart]
          rw [if_neg (fun h => sig_notW j hj ⟨h.1, h.2.1⟩), if_neg]
          intro e; rw [← e] at hi; exact sig_notW j hj hi
        rw [h1, star_zero, zero_mul, GBasic.Hpk_eq, if_neg]
        intro e; rw [sig_fixes_middle_block i hi] at e; rw [e] at hj; exact hj hi
      · intro p _ hp
        have : wpart s (GBasic.sig k r p) j = 0 := by
          simp only [wpart]; rw [if_neg (fun h => hj ⟨h.2.2.1, h.2.2.2⟩), if_neg]
          intro e; apply hp; rw [← e, GBasic.sig_sig]
        rw [this, mul_zero, mul_zero]
      · simp
  · rw [Finset.sum_eq_single i]
    · have h1 : wpart s i i = 1 := by
        simp only [wpart]; rw [if_neg (fun h => hi ⟨h.1, h.2.1⟩)]; simp
      have h2 : wpart s (GBasic.sig k r i) j = if GBasic.sig k r i = j then 1 else 0 := by
        simp only [wpart]; rw [if_neg (fun h => sig_notW i hi ⟨h.1, h.2.1⟩)]
      rw [h1, star_one, one_mul, h2, GBasic.Hpk_eq]
      by_cases e : GBasic.sig k r i = j
      · rw [if_pos e, if_pos e.symm, mul_one]
      · rw [if_neg e, if_neg (fun h => e h.symm), mul_zero]
    · intro p _ hp
      have : wpart s p i = 0 := by
        simp only [wpart]; rw [if_neg (fun h => hi ⟨h.2.2.1, h.2.2.2⟩), if_neg hp]
      rw [this, star_zero, zero_mul]
    · simp

end FlagSpanVanishing

open C2x5 C2x7 FlagSpanVanishing

/- English proof (translation)
Introduce `k r z hz`. Use extensionality with `s`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hs, hfl⟩`. Establish `hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0`.

Introduce `a i hi`. Establish `h` using `flagSpan_vanish z (Fin.castSucc a) _ (hfl (Fin.castSucc a)) i (by simpa using hi)`. Establish `hf : fvec k r z (Fin.castSucc a) = bvec (eI k r a)` using `by rw [fvec, dif_pos (by simp)]; rfl`. Rewrite `h` using `[hf, mulVec_bvec, Pi.sub_apply, sub_eq_zero]`. Rewrite using `[h]`.

Simplify using `[bvec, Pi.single_apply]`. Establish `hzc : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (s *ᵥ z) i = z i`. Introduce `i hi`. Establish `h` using `flagSpan_vanish z (Fin.last r) _ (hfl (Fin.last r)) i (by simpa using hi)`. Establish `hf : fvec k r z (Fin.last r) = z` using `by rw [fvec, dif_neg (by simp)]`.

Rewrite `h` using `[hf, Pi.sub_apply, sub_eq_zero]`. Conclude with `h`. Establish `hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0`. Introduce `p j hp hj1 hj2`. Establish `hpa : 2 * r + k - p.val < r` using `by omega`.

Establish `e : esI k r ⟨2 * r + k - p.val, hpa⟩ = p` using `Fin.ext (by simp [esI]; omega)`. Rewrite using `[← e]`. Conclude with `zero_block s hs hcol j hj1 hj2 _ _ rfl`. Establish `hhU` using `wpart_uh s hs hA`. Use `set h := wpart s with hh`.

Establish `hhW : h ∈ UWset k r z`. Use `⟨hhU, fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_bvec]`. Use function extensionality and compare the values at `i`. Simplify using `only [hh, wpart, bvec, Pi.single_apply]`.

Rewrite using `[if_neg (by intro h'; have := h'.2.2.1; simp only [eI] at this; omega)]`. Rewrite using `[mulVec_bvec]`. Use function extensionality and compare the values at `i`. Simplify using `only [hh, wpart, bvec, Pi.single_apply]`. Rewrite using `[if_neg (by intro h'; have := h'.2.2.2; simp only [esI] at this; omega)]`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : r ≤ i.val ∧ i.val ≤ r + k`. Rewrite using `[← hzc i hi.1]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`. Simplify using `only [hh, wpart, if_pos (And.intro hi.1 (And.intro hi.2 hj))]`. Establish `hzj : z j = 0` using `hz.1 j (by omega)`. Rewrite using `[hzj, mul_zero, mul_zero]`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using `only [hh, wpart]`. Rewrite using `[if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩)]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `only [hh, wpart]`. Rewrite using `[if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩), if_neg (Ne.symm hj), zero_mul]`. Simplify using the standard rewrite rules. Establish `hhu : IsUnit h.det` using `WeylGroupFacts.isUnit_of_uh hhU`. Establish `hblk` using `WeylGroupFacts.uw_block (WeylGroupFacts.uw_inv hhW)`.

Use `⟨h, hhW, h⁻¹ * s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[WeylGroupFacts.nset_iff]`. Use `⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hhU) hs, fun i j hj hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hjr : j.val < r`.

Establish `e : eI k r ⟨j.val, hjr⟩ = j` using `Fin.ext rfl`. Establish `hterm : ∀ p, h⁻¹ i p * s p j = (if i = p then 1 else 0) * s p j`. Introduce `p`. Distinguish the cases in `hpr : p.val < r`. Rewrite using `[hblk.1 i p (Or.inl hpr)]`.

Use `hcol ⟨j.val, hjr⟩ p (by simp; omega)` as an intermediate fact. Rewrite `this` using `[e, if_neg (fun e' => hpr (by rw [e']; exact hjr))]`. Rewrite using `[this, mul_zero, mul_zero]`. Simplify using `only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `hcol ⟨j.val, hjr⟩ i (by simp; omega)` as an intermediate fact.

Rewrite `this` using `[e]`. Conclude with `this`. Establish `hir : r ≤ i.val` using `by omega`. Establish `hterm : ∀ p, h⁻¹ i p * s p j = h⁻¹ i p * h p j`. Introduce `p`.

Distinguish the cases in `hpr : p.val < r`. Rewrite using `[hblk.1 i p (Or.inl hpr), if_neg (fun e' => by rw [e'] at hir; omega), zero_mul, zero_mul]`. Distinguish the cases in `hpk : p.val ≤ r + k`. Simplify using `only [hh, wpart]`. Rewrite using `[if_pos ⟨by omega, hpk, by omega, hj⟩]`.

Rewrite using `[hA p j (by omega) (by omega) hj]`. Simplify using `only [hh, wpart]`. Rewrite using `[if_neg (fun h' => hpk h'.2.1), if_neg (fun e' => by rw [e'] at hpk; exact hpk hj)]`. Simplify using `only [hterm]`. Rewrite using `[← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hhu, Matrix.one_apply]`.

Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]`. Introduce `hs`. Use `⟨Sset_UH hs, fun a => ?_⟩` and prove the remaining obligations. Take `⟨U, hU1, hU2, hsF⟩` from `S_F hz.1 hs`. Rewrite using `[colEq hsF a]`.

Establish `hfa : fvec k r z a = ∑ c, (if c = a then (1 : ℂ) else 0) • fvec k r z c`. Simplify using `[ite_smul]`. Rewrite using `[hfa, ← Finset.sum_sub_distrib]`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `c _`.

Rewrite using `[← sub_smul]`. Distinguish the cases in `hca : c < a`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hca⟩, rfl⟩)`. Establish `: U c a - (if c = a then 1 else 0) = 0`. Break down `eq_or_lt_of_le (not_lt.mp hca) with e | e` into its components or cases.

Rewrite using `[← e, hU2, if_pos rfl, sub_self]`. Rewrite using `[hU1 c a e, if_neg (ne_of_gt e), sub_self]`. Rewrite using `[this, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem standard_flag_property : C2.SFlag := by
  intro k r z hz
  ext s
  constructor
  · rintro ⟨hs, hfl⟩
    have hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        s i (eI k r a) = if i = eI k r a then 1 else 0 := by
      intro a i hi
      have h := flagSpan_vanish z (Fin.castSucc a) _ (hfl (Fin.castSucc a)) i (by simpa using hi)
      have hf : fvec k r z (Fin.castSucc a) = bvec (eI k r a) := by rw [fvec, dif_pos (by simp)]; rfl
      rw [hf, mulVec_bvec, Pi.sub_apply, sub_eq_zero] at h
      rw [h]; simp [bvec, Pi.single_apply]
    have hzc : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (s *ᵥ z) i = z i := by
      intro i hi
      have h := flagSpan_vanish z (Fin.last r) _ (hfl (Fin.last r)) i (by simpa using hi)
      have hf : fvec k r z (Fin.last r) = z := by rw [fvec, dif_neg (by simp)]
      rw [hf, Pi.sub_apply, sub_eq_zero] at h; exact h
    have hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0 := by
      intro p j hp hj1 hj2
      have hpa : 2 * r + k - p.val < r := by omega
      have e : esI k r ⟨2 * r + k - p.val, hpa⟩ = p := Fin.ext (by simp [esI]; omega)
      rw [← e]; exact zero_block s hs hcol j hj1 hj2 _ _ rfl
    have hhU := wpart_uh s hs hA
    set h := wpart s with hh
    have hhW : h ∈ UWset k r z := by
      refine ⟨hhU, fun a => ⟨?_, ?_⟩, ?_⟩
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [if_neg (by intro h'; have := h'.2.2.1; simp only [eI] at this; omega)]
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [if_neg (by intro h'; have := h'.2.2.2; simp only [esI] at this; omega)]
      · funext i
        by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
        · rw [← hzc i hi.1]
          simp only [Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
          · simp only [hh, wpart, if_pos (And.intro hi.1 (And.intro hi.2 hj))]
          · have hzj : z j = 0 := hz.1 j (by omega)
            rw [hzj, mul_zero, mul_zero]
        · simp only [Matrix.mulVec, dotProduct]
          rw [Finset.sum_eq_single i]
          · simp only [hh, wpart]; rw [if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩)]; simp
          · intro j _ hj
            simp only [hh, wpart]; rw [if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩), if_neg (Ne.symm hj), zero_mul]
          · simp
    have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hhU
    have hblk := WeylGroupFacts.uw_block (WeylGroupFacts.uw_inv hhW)
    refine ⟨h, hhW, h⁻¹ * s, ?_, ?_⟩
    · rw [WeylGroupFacts.nset_iff]
      refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hhU) hs, fun i j hj hij => ?_⟩
      rw [Matrix.mul_apply]
      by_cases hjr : j.val < r
      · have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
        have hterm : ∀ p, h⁻¹ i p * s p j = (if i = p then 1 else 0) * s p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr)]
          · have := hcol ⟨j.val, hjr⟩ p (by simp; omega)
            rw [e, if_neg (fun e' => hpr (by rw [e']; exact hjr))] at this
            rw [this, mul_zero, mul_zero]
        simp only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        have := hcol ⟨j.val, hjr⟩ i (by simp; omega)
        rw [e] at this; exact this
      · have hir : r ≤ i.val := by omega
        have hterm : ∀ p, h⁻¹ i p * s p j = h⁻¹ i p * h p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr), if_neg (fun e' => by rw [e'] at hir; omega), zero_mul, zero_mul]
          · by_cases hpk : p.val ≤ r + k
            · simp only [hh, wpart]
              rw [if_pos ⟨by omega, hpk, by omega, hj⟩]
            · rw [hA p j (by omega) (by omega) hj]
              simp only [hh, wpart]
              rw [if_neg (fun h' => hpk h'.2.1), if_neg (fun e' => by rw [e'] at hpk; exact hpk hj)]
        simp only [hterm]
        rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hhu, Matrix.one_apply]
    · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  · intro hs
    refine ⟨Sset_UH hs, fun a => ?_⟩
    obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    rw [colEq hsF a]
    have hfa : fvec k r z a = ∑ c, (if c = a then (1 : ℂ) else 0) • fvec k r z c := by
      simp [ite_smul]
    rw [hfa, ← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro c _
    rw [← sub_smul]
    by_cases hca : c < a
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hca⟩, rfl⟩)
    · have : U c a - (if c = a then 1 else 0) = 0 := by
        rcases eq_or_lt_of_le (not_lt.mp hca) with e | e
        · rw [← e, hU2, if_pos rfl, sub_self]
        · rw [hU1 c a e, if_neg (ne_of_gt e), sub_self]
      rw [this, zero_smul]; exact Submodule.zero_mem _

end Formalism.FourierDecayAlt.P
