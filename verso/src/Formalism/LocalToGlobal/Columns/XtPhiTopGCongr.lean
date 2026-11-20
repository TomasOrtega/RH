import Formalism.LocalToGlobal.Columns.XiTopTilRefHolds
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TopG

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure TopNum (R : Ranks) (i : ℕ) : Prop where
  a_eq : R.r + (i + 1 - 1) * R.t = R.N i
  a_le : R.r + (i + 1 - 1) * R.t ≤ (R.N (i + 1) - 1) + 0
  c0 : cOf R i = 0

/- English proof (translation)
Establish `h` using `xt_a_eq (R := R) hm`. Establish `e : R.m - 1 = m2 + 1 + 1 - 1` using `by omega`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Use `a_le := by`. Establish `h` using `xt_a_eq (R := R) hm`.

Establish `e : R.m - 1 = m2 + 1 + 1 - 1` using `by omega`. Rewrite `h` using `[e]`. Rewrite using `[h]`. Unfold `Ranks.N`. Establish `e2 : (m2 + 1 + 1) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1)` using `by ring`.

Use linear arithmetic over natural numbers and integers. Use `c0 := xt_cOf hm`.
-/
theorem topNum_of {m2 : ℕ} (hm : R.m = m2 + 2) : TopNum R (m2 + 1) where
  a_eq := by
    have h := xt_a_eq (R := R) hm
    have e : R.m - 1 = m2 + 1 + 1 - 1 := by omega
    rwa [e] at h
  a_le := by
    have h := xt_a_eq (R := R) hm
    have e : R.m - 1 = m2 + 1 + 1 - 1 := by omega
    rw [e] at h
    rw [h]
    unfold Ranks.N
    have e2 : (m2 + 1 + 1) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1) := by ring
    omega
  c0 := xt_cOf hm

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

/- English proof (translation)
Establish `hu` using `ciQ_notMem_sq hX hPr hP`. Establish `hq` using `ciQ_mem P`. Establish `hq0 : ((qOf P : ℕ) : X.E) ≠ 0` using `ciQ_ne_zero hu`. Establish `hkr : R.k ≤ R.r` using `by unfold Ranks.r; have := R.two_le_m; omega`. Unfold `PhiTopG`.

Rewrite using `[if_pos hP]`. Consider the cases of `sharp`. Simplify using `only [Bool.false_eq_true, if_false]`. Use `ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')` and prove the remaining obligations. Unfold `Ranks.r`.

Use `R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Unfold `Ranks.r`. Use `R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [if_true]`. Conclude with `xtPhiGS_congr hq hq0 _ _ x x' hkr hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')`.
-/
theorem xtPhiTopG_congr (hX : X.Ok) (hPr : Pr.Ok) {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x x' : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hD : ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i → ∃ d, IntAt P d ∧
      LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p' + (qOf P : X.E) * d) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x' = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  have hu := ciQ_notMem_sq hX hPr hP
  have hq := ciQ_mem P
  have hq0 : ((qOf P : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have hkr : R.k ≤ R.r := by unfold Ranks.r; have := R.two_le_m; omega
  unfold PhiTopG
  rw [if_pos hP]
  cases sharp
  · simp only [Bool.false_eq_true, if_false]
    refine ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')
    · unfold Ranks.r; have := R.two_le_m; omega
    · unfold Ranks.r; have := R.two_le_m; omega
  · simp only [if_true]
    exact xtPhiGS_congr hq hq0 _ _ x x' hkr hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')

/- English proof (translation)
Unfold `PhiTopG at h`. Rewrite `h` using `[if_pos hP]`. Introduce `p p' hp hp'`. Consider the cases of `sharp`. Simplify using `only [Bool.false_eq_true, if_false] at h`.

Conclude with `ciPhiG_int _ _ false x h p p' hp (hn.a_eq.symm ▸ hp')`. Simplify using `only [if_true] at h`. Conclude with `xtPhiGS_int _ _ x h p p' hp (hn.a_eq.symm ▸ hp')`.
-/
theorem xtPhiTopG_int {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0)) (h : PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x ≠ 0) :
    ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i →
      IntAt P (LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p') := by
  unfold PhiTopG at h
  rw [if_pos hP] at h
  intro p p' hp hp'
  cases sharp
  · simp only [Bool.false_eq_true, if_false] at h
    exact ciPhiG_int _ _ false x h p p' hp (hn.a_eq.symm ▸ hp')
  · simp only [if_true] at h
    exact xtPhiGS_int _ _ x h p p' hp (hn.a_eq.symm ▸ hp')

def topDat (i : ℕ) (P : rowSG Pr sel mu) (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) : X.K :=
  PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1 (prXpG X.E (R.N (i + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
    ftY sel mu cst P (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y) y''

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem XiTop_eq {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiTop Ch sel mu cst i p Y p' x = phiT X.K p.deco.1 p'.deco.1 x *
      ∏ P : rowSG Pr sel mu, topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

/- English proof (translation)
Use `R.N_pos j` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem xt_last_lt (R : Ranks) (j : ℕ) : R.N j - 1 < R.N j := by have := R.N_pos j; omega

/- English proof (translation)
Unfold `atNL`. Rewrite using `[dif_pos (xt_last_lt R j)]`. Both sides reduce to the same expression.
-/
theorem xt_atNL (j : ℕ) (a : Sp X.E (R.N j)) : atNL X.E (R.N j) (R.N j - 1) a = a ⟨R.N j - 1, xt_last_lt R j⟩ := by
  unfold atNL
  rw [dif_pos (xt_last_lt R j)]
  rfl

/- English proof (translation)
Rewrite using `[xt_atNL]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun i => h _, h _⟩`. Introduce and unpack `⟨h1, h2⟩ i`.

Distinguish the cases in `hi : i.1 < R.N j - 1`. Conclude with `h1 ⟨i.1, by omega⟩`. Establish `: i = ⟨R.N j - 1, xt_last_lt R j⟩` using `Fin.ext (by show i.1 = R.N j - 1; have := i.2; omega)`. Rewrite using `[this]`. Conclude with `h2`.
-/
theorem xt_split {P : HeightOneSpectrum (𝓞 X.E)} (j : ℕ) (a : Sp X.E (R.N j)) :
    (∀ i, IntAt P (a i)) ↔ (∀ i, IntAt P (prXpG X.E (R.N j) a i)) ∧ IntAt P (atNL X.E (R.N j) (R.N j - 1) a) := by
  rw [xt_atNL]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i.1 < R.N j - 1
    · exact h1 ⟨i.1, by omega⟩
    · have : i = ⟨R.N j - 1, xt_last_lt R j⟩ := Fin.ext (by show i.1 = R.N j - 1; have := i.2; omega)
      rw [this]
      exact h2

/- English proof (translation)
Establish `key` using `xtLocal (K := X.K) (P := P.1) (q := qOf P.1) (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (k₀ := R.k) (c' := cOf R i) (n' := R.N i) (n := R.N (i + 1) - 1) (N := R.N (i + 1)) hn.c0 (PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1) (fun x x' h => xtPhiTopG_congr Ch mu hX hPr hn cst. …`. Rewrite using `[xt_atNL, xt_atNL]`. Conclude with `(H j).2 hall _⟩⟩) y'' hy`. Unfold `topDat ftY`. Rewrite using `[if_pos hP, if_pos hP]`.

Conclude with `key`.
-/
theorem topDat_congr (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y y₁ : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (hy : ∀ j, IntAt P.1 ((qOf P.1 : X.E) * y'' j))
    (H : ∀ j : Fin (R.N i), ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) ↔ ∀ l, IntAt P.1 (y₁ (Pi.single j 1) l)) ∧
      ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) → ∀ l, redP P.1 (y (Pi.single j 1) l) = redP P.1 (y₁ (Pi.single j 1) l))) :
    topDat Ch sel mu cst i P y y'' = topDat Ch sel mu cst i P y₁ y'' := by
  classical
  have key := xtLocal (K := X.K) (P := P.1) (q := qOf P.1) (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (k₀ := R.k) (c' := cOf R i)
    (n' := R.N i) (n := R.N (i + 1) - 1) (N := R.N (i + 1)) hn.c0 (PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1)
    (fun x x' h => xtPhiTopG_congr Ch mu hX hPr hn cst.sharp hP x x' h) (fun x h => xtPhiTopG_int Ch mu hn cst.sharp hP x h)
    (cst.psi P) (cst.D P) (hc.D_pos P) (hc.psi_add P) (hc.psi_int P) epsSg (prXpG X.E (R.N (i + 1))) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1))
    (fun a => xt_split (i + 1) a) y (prXpG X.E (R.N (i + 1)) ∘ₗ y₁) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y₁)
    (fun j => ⟨(H j).1.trans (xt_split (i + 1) _), fun hall => ⟨fun l => (H j).2 hall _, by
      show redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _) = redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _)
      rw [xt_atNL, xt_atNL]
      exact (H j).2 hall _⟩⟩) y'' hy
  unfold topDat ftY
  rw [if_pos hP, if_pos hP]
  exact key

/- English proof (translation)
Establish `h1` using `left_ne_zero_of_mul h`. Establish `h2` using `right_ne_zero_of_mul h`. Use `(xt_split (i + 1) (y (Pi.single j 1))).2 ⟨fun l => ?_, ?_⟩ l` and prove the remaining obligations. Use `xtPhiTopG_int Ch mu hn cst.sharp hP _ h1 l.1 j.1 l.2 j.2` as an intermediate fact. Rewrite `this` using `[xtEntB hn.c0 _ (by have := l.2; omega) j.2, LinearMap.comp_apply, LinearMap.comp_apply, xtRes j.2]`. Then use the resulting hypothesis.

Unfold `ftY at h2`. Rewrite `h2` using `[if_pos hP]`. Assume the negation of the conclusion as `h3`. Conclude with `h2 (if_neg fun hh => h3 (hh j))`.
-/
theorem topDat_int {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (h : topDat Ch sel mu cst i P y y'' ≠ 0) (j : Fin (R.N i)) (l : Fin (R.N (i + 1))) :
    IntAt P.1 (y (Pi.single j 1) l) := by
  classical
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  refine (xt_split (i + 1) (y (Pi.single j 1))).2 ⟨fun l => ?_, ?_⟩ l
  · have := xtPhiTopG_int Ch mu hn cst.sharp hP _ h1 l.1 j.1 l.2 j.2
    rwa [xtEntB hn.c0 _ (by have := l.2; omega) j.2, LinearMap.comp_apply, LinearMap.comp_apply, xtRes j.2] at this
  · unfold ftY at h2
    rw [if_pos hP] at h2
    by_contra h3
    exact h2 (if_neg fun hh => h3 (hh j))

end TopG

end Formalism.L2.Col
