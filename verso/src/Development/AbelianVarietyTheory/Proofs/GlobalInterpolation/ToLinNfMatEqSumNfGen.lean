import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.QNF

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

/- English proof (translation)
Use function extensionality and compare the values at `p`. Rewrite using `[Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Pi.add_apply, Finset.sum_apply]`. Use `congr 1`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) p` and prove the remaining obligations. Simplify using `[nfMat, Loc.inX]`.

Establish `: ∀ a : Fin n, Fin.natAdd n b ≠ Fin.castAdd c a` using `fun a h => by`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Simplify using `[nfMat, Loc.inX, this]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `Fin.addCases (fun a => ?_) (fun b => ?_) p` and prove the remaining obligations. Establish `h1 : Fin.castAdd c a ≠ Fin.natAdd n i` using `fun h => by`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : ¬ (a.1 = n + i.1)` using `by omega`. Distinguish the cases in `hi : i.1 = 0`. Establish `h0 : ∀ h, (⟨0, h⟩ : Fin c) = i` using `fun h => Fin.ext hi.symm`. Establish `h3 : ¬ (a.1 = n)` using `by omega`.

Simplify using `[nfMat, nfGen, Loc.inX, Loc.eN, h1, h3, hi, h0]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[nfMat, nfGen, Loc.eN, h1, h2, hi]`. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality.

Simplify using `[nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, mul_comm]`. Establish `: ¬ (b.1 = i.1)` using `fun h => hb (Fin.ext h)`. Simplify using `[nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, hb, this]`.
-/
theorem toLin'_nfMat_eq_sum_nfGen {E : Type} [Field E] [NumberField E] [StarRing E] (q n c : ℕ) (e : Fin c → ℤ) (z : Fin n → E)
    (y : Fin (n + c) → E) :
    Matrix.toLin' (nfMat n c (q : E) e z) y =
      Loc.inX E n c (fun a => y (Fin.castAdd c a)) + ∑ i, y (Fin.natAdd n i) • nfGen q n c e z i := by
  funext p
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Pi.add_apply, Finset.sum_apply]
  congr 1
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · simp [nfMat, Loc.inX]
    · have : ∀ a : Fin n, Fin.natAdd n b ≠ Fin.castAdd c a := fun a h => by
        have := congrArg Fin.val h
        simp at this; omega
      simp [nfMat, Loc.inX, this]
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · have h1 : Fin.castAdd c a ≠ Fin.natAdd n i := fun h => by
        have := congrArg Fin.val h
        simp at this; omega
      have h2 : ¬ (a.1 = n + i.1) := by omega
      by_cases hi : i.1 = 0
      · have h0 : ∀ h, (⟨0, h⟩ : Fin c) = i := fun h => Fin.ext hi.symm
        have h3 : ¬ (a.1 = n) := by omega
        simp [nfMat, nfGen, Loc.inX, Loc.eN, h1, h3, hi, h0]
        ring
      · simp [nfMat, nfGen, Loc.eN, h1, h2, hi]
    · by_cases hb : b = i
      · subst hb
        simp [nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, mul_comm]
      · have : ¬ (b.1 = i.1) := fun h => hb (Fin.ext h)
        simp [nfMat, nfGen, Loc.inX, Loc.eN, ite_apply, hb, this]

variable {X : Fields} {Pr : Primes X} {R : Ranks}

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Set.mem_image, SetLike.mem_coe, mem_lamYat hP, nfLat, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨fun a => x (Fin.castAdd _ a), (mem_localization_standardLattice _ _).2 fun a => hx _, fun b => x (Fin.natAdd _ b), fun b => hx _, toLin'_nfMat_eq_sum_nfGen _ _ _ _ _ _⟩`.

Introduce and unpack `⟨l, hl, s, hs, rfl⟩`. Use `⟨Fin.addCases (motive := fun _ => X.E) l s, fun p => ?_, ?_⟩` and prove the remaining obligations. Use `Fin.addCases (fun a => ?_) (fun b => ?_) p` and prove the remaining obligations. Simplify using `using (mem_localization_standardLattice _ _).1 hl a`. Simplify using `using hs b`.

Rewrite using `[toLin'_nfMat_eq_sum_nfGen]`. Simplify using the standard rewrite rules.
-/
theorem image_lamYat_nfMat {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (e : Fin (cOf R j) → ℤ)
    (z : Fin (R.N j) → X.E) :
    (Matrix.toLin' (nfMat (R.N j) (cOf R j) ((qOf P : ℕ) : X.E) e z)) ''
        (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = nfLat P (R.N j) (cOf R j) e z := by
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, mem_lamYat hP, nfLat, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun a => x (Fin.castAdd _ a), (mem_localization_standardLattice _ _).2 fun a => hx _, fun b => x (Fin.natAdd _ b),
      fun b => hx _, toLin'_nfMat_eq_sum_nfGen _ _ _ _ _ _⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    refine ⟨Fin.addCases (motive := fun _ => X.E) l s, fun p => ?_, ?_⟩
    · refine Fin.addCases (fun a => ?_) (fun b => ?_) p
      · simpa using (mem_localization_standardLattice _ _).1 hl a
      · simpa using hs b
    · rw [toLin'_nfMat_eq_sum_nfGen]
      simp

/- English proof (translation)
Rewrite using `[mem_lamYat hP]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(mem_localization_standardLattice _ _).2 fun a => ?_` and prove the remaining obligations. Simplify using `using h (Fin.castAdd _ a)`.

Introduce `h l`. Distinguish the cases in `hl : l.1 < R.N j`. Simplify `(mem_localization_standardLattice _ _).1 h ⟨l.1, hl⟩` using `[hl]`. Simplify `(mem_lamYat (R := R) (j := j) hP 0).1 (zero_mem _) l` using `[hl]`.
-/
theorem pad_mem_lamYat_iff {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (z : Fin (R.N j) → X.E) :
    (fun l : Fin (R.N j + cOf R j) => if h : l.1 < R.N j then z ⟨l.1, h⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P ↔
      z ∈ stdAt X.E (R.N j) P := by
  rw [mem_lamYat hP]
  constructor
  · intro h
    refine (mem_localization_standardLattice _ _).2 fun a => ?_
    simpa using h (Fin.castAdd _ a)
  · intro h l
    by_cases hl : l.1 < R.N j
    · simpa [hl] using (mem_localization_standardLattice _ _).1 h ⟨l.1, hl⟩
    · simpa [hl] using (mem_lamYat (R := R) (j := j) hP 0).1 (zero_mem _) l

/- English proof (translation)
Introduce `X Pr R j P hP h`. Unfold `NF MatNF`. Use `exists_congr fun e => exists_congr fun z => and_congr_right fun _ => and_congr (pad_mem_lamYat_iff hP z).symm ?_` and prove the remaining obligations. Rewrite using `[← image_lamYat_nfMat hP]`. Use `Iff.trans ?_ SetLike.ext'_iff.symm` and prove the remaining obligations.

Rewrite using `[Submodule.map_coe, Submodule.map_coe]`. Both sides reduce to the same expression.
-/
theorem nf_iff_matNF : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs →
    ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h ↔ GlobalTheory.QNF.MatNF Pr R j P h := by
  intro X Pr R j P hP h
  unfold NF MatNF
  refine exists_congr fun e => exists_congr fun z => and_congr_right fun _ => and_congr (pad_mem_lamYat_iff hP z).symm ?_
  rw [← image_lamYat_nfMat hP]
  refine Iff.trans ?_ SetLike.ext'_iff.symm
  rw [Submodule.map_coe, Submodule.map_coe]
  rfl

end GlobalTheory.QNF

end
