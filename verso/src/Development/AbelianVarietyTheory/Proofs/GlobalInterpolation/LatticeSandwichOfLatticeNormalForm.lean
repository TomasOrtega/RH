import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Use `lift e to ℕ using he`. Rewrite using `[zpow_natCast]`. Conclude with `GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul e ha`.
-/
theorem intAt_zpow_mul {P : HeightOneSpectrum (𝓞 E)} {e : ℤ} (he : 0 ≤ e) {a : E} (ha : IntAt P a) :
    IntAt P ((qOf P : E) ^ e * a) := by
  lift e to ℕ using he
  rw [zpow_natCast]
  exact GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul e ha

/- English proof (translation)
Introduce `l`. Rewrite using `[inX_apply]`. Use `split_ifs`. Conclude with `hz _`. Conclude with `⟨0, 1, one_notMem P, by simp⟩`.
-/
theorem intV_inX {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {z : Fin n → E} (hz : IntV P z) : IntV P (Loc.inX E n c z) := by
  intro l
  rw [inX_apply]
  split_ifs
  · exact hz _
  · exact ⟨0, 1, one_notMem P, by simp⟩

/- English proof (translation)
Introduce `l`. Simplify using `only [Loc.eN]`. Use `split_ifs`. Conclude with `intAt_one P`. Conclude with `⟨0, 1, one_notMem P, by simp⟩`.
-/
theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : IntV P (Loc.eN E N i) := by
  intro l
  simp only [Loc.eN]
  split_ifs
  · exact intAt_one P
  · exact ⟨0, 1, one_notMem P, by simp⟩

/- English proof (translation)
Introduce `l`. Rewrite using `[Finset.sum_apply]`. Conclude with `intAt_sum s _ (fun i hi => h i hi l)`.
-/
theorem intV_sum {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {ι : Type} (s : Finset ι) (f : ι → Fin N → E)
    (h : ∀ i ∈ s, IntV P (f i)) : IntV P (∑ i ∈ s, f i) := by
  intro l
  rw [Finset.sum_apply]
  exact intAt_sum s _ (fun i hi => h i hi l)

/- English proof (translation)
Use `split_ifs`. Conclude with `intV_inX hz`. Conclude with `IntV.zero P`.
-/
theorem intV_glue {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {z : Fin n → E} (hz : IntV P z) (i : Fin c) :
    IntV P (if i.1 = 0 then Loc.inX E n c z else 0) := by
  split_ifs
  · exact intV_inX hz
  · exact IntV.zero P

/- English proof (translation)
Use function extensionality and compare the values at `l`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) l` and prove the remaining obligations. Establish `h1 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0`. Introduce `i`. Simplify using `only [Loc.eN, Fin.val_castAdd]`.

Rewrite using `[if_neg]`. Use linear arithmetic over natural numbers and integers. Simplify using `[inX_castAdd, Finset.sum_apply, h1]`. Establish `h2 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.natAdd n b) = if i = b then 1 else 0`. Introduce `i`.

Distinguish the cases in `hib : i = b`. Substitute `hib` using the available equality. Simplify using `[Loc.eN]`. Simplify using `only [Loc.eN, Fin.val_natAdd, if_neg hib]`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `hib` to reduce the goal to its premises. Use `ext`. Use linear arithmetic over natural numbers and integers. Establish `h3 : Loc.inX E n c (fun a => x (Fin.castAdd c a)) (Fin.natAdd n b) = 0`.

Rewrite using `[inX_apply, dif_neg (by simp)]`. Simplify using `[Finset.sum_apply, h2, h3]`.
-/
theorem decomp {n c : ℕ} (x : Fin (n + c) → E) :
    x = Loc.inX E n c (fun a => x (Fin.castAdd c a)) + ∑ i : Fin c, x (Fin.natAdd n i) • Loc.eN E (n + c) (n + i.1) := by
  funext l
  refine Fin.addCases (fun a => ?_) (fun b => ?_) l
  · have h1 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.castAdd c a) = 0 := by
      intro i
      simp only [Loc.eN, Fin.val_castAdd]
      rw [if_neg]
      omega
    simp [inX_castAdd, Finset.sum_apply, h1]
  · have h2 : ∀ i : Fin c, Loc.eN E (n + c) (n + i.1) (Fin.natAdd n b) = if i = b then 1 else 0 := by
      intro i
      by_cases hib : i = b
      · subst hib
        simp [Loc.eN]
      · simp only [Loc.eN, Fin.val_natAdd, if_neg hib]
        rw [if_neg]
        intro h
        apply hib
        ext
        omega
    have h3 : Loc.inX E n c (fun a => x (Fin.castAdd c a)) (Fin.natAdd n b) = 0 := by
      rw [inX_apply, dif_neg (by simp)]
    simp [Finset.sum_apply, h2, h3]

/- English proof (translation)
Establish `hq : (qOf P : E) ≠ 0` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P`. Use `set w : Sp E n := ∑ i : Fin c, x (Fin.natAdd n i) • (if i.1 = 0 then z else 0) with hw`. Use `⟨(fun a => x (Fin.castAdd c a)) - w, ?_, fun i => x (Fin.natAdd n i) * (qOf P : E) ^ (-e i), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_stdAt_iff, sub_eq_add_neg]`. Use `IntV.add (fun l => hx _) (IntV.neg ?_)` and prove the remaining obligations.

Use `intV_sum _ _ (fun i _ => IntV.smul (hx _) ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `hz`. Conclude with `IntV.zero P`. Introduce `i show IntAt P (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i))`.

Rewrite using `[mul_comm]`. Conclude with `intAt_zpow_mul (by linarith [he i]) (hx _)`. Establish `hs : ∀ i : Fin c, (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i)) • nfGen (qOf P) n c e z i = x (Fin.natAdd n i) • Loc.eN E (n + c) (n + i.1) + Loc.inX E n c (x (Fin.natAdd n i) • (if i.1 = 0 then z else 0))`. Introduce `i`. Simplify using `only [nfGen, smul_smul, mul_assoc, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, mul_one, smul_add]`.

Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, ← map_sum, ← hw, map_sub]`. Use `conv_lhs => rw [decomp x]`. Normalize the expressions using the abelian group laws.
-/
theorem mem_nfLat {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {e : Fin c → ℤ} (he : ∀ i, e i ≤ 0) {z : Sp E n}
    (hz : IntV P z) {x : Sp E (n + c)} (hx : IntV P x) : x ∈ nfLat P n c e z := by
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  set w : Sp E n := ∑ i : Fin c, x (Fin.natAdd n i) • (if i.1 = 0 then z else 0) with hw
  refine ⟨(fun a => x (Fin.castAdd c a)) - w, ?_, fun i => x (Fin.natAdd n i) * (qOf P : E) ^ (-e i), ?_, ?_⟩
  · rw [mem_stdAt_iff, sub_eq_add_neg]
    refine IntV.add (fun l => hx _) (IntV.neg ?_)
    refine intV_sum _ _ (fun i _ => IntV.smul (hx _) ?_)
    split_ifs
    · exact hz
    · exact IntV.zero P
  · intro i
    show IntAt P (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i))
    rw [mul_comm]
    exact intAt_zpow_mul (by linarith [he i]) (hx _)
  · have hs : ∀ i : Fin c, (x (Fin.natAdd n i) * (qOf P : E) ^ (-e i)) • nfGen (qOf P) n c e z i =
        x (Fin.natAdd n i) • Loc.eN E (n + c) (n + i.1) +
          Loc.inX E n c (x (Fin.natAdd n i) • (if i.1 = 0 then z else 0)) := by
      intro i
      simp only [nfGen, smul_smul, mul_assoc, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, mul_one, smul_add]
      congr 1
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_add_distrib, ← map_sum, ← hw, map_sub]
    conv_lhs => rw [decomp x]
    abel

/- English proof (translation)
Take `⟨l, hl, s, hs, rfl⟩` from `hx`. Establish `hq : (qOf P : E) ≠ 0` using `GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P`. Rewrite `hl` using `[mem_stdAt_iff]`. Establish `key : ∀ i : Fin c, ((qOf P : E) ^ j) • (s i • nfGen (qOf P) n c e z i) = ((qOf P : E) ^ ((j : ℤ) + e i) * s i) • (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0)`. Introduce `i`.

Simplify using `only [nfGen, smul_smul]`. Use `congr 1`. Rewrite using `[zpow_add₀ hq, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[smul_add, Finset.smul_sum, ← LinearMap.map_smul (Loc.inX E n c)]`.

Use `IntV.add (intV_inX (fun k => ?_)) (intV_sum _ _ (fun i _ => ?_))` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul j (hl k)`. Rewrite using `[key i]`. Use `IntV.smul ?_ (IntV.add (intV_eN P _ _) (intV_glue hz i))` and prove the remaining obligations.

Conclude with `intAt_zpow_mul (by linarith [he i]) (hs i)`.
-/
theorem smul_int_of_mem_nfLat {P : HeightOneSpectrum (𝓞 E)} {n c j : ℕ} {e : Fin c → ℤ} (he : ∀ i, -(j : ℤ) ≤ e i)
    {z : Sp E n} (hz : IntV P z) {x : Sp E (n + c)} (hx : x ∈ nfLat P n c e z) : IntV P (((qOf P : E) ^ j) • x) := by
  obtain ⟨l, hl, s, hs, rfl⟩ := hx
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  rw [mem_stdAt_iff] at hl
  have key : ∀ i : Fin c, ((qOf P : E) ^ j) • (s i • nfGen (qOf P) n c e z i) =
      ((qOf P : E) ^ ((j : ℤ) + e i) * s i) •
        (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0) := by
    intro i
    simp only [nfGen, smul_smul]
    congr 1
    rw [zpow_add₀ hq, zpow_natCast]
    ring
  rw [smul_add, Finset.smul_sum, ← LinearMap.map_smul (Loc.inX E n c)]
  refine IntV.add (intV_inX (fun k => ?_)) (intV_sum _ _ (fun i _ => ?_))
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul j (hl k)
  · rw [key i]
    refine IntV.smul ?_ (IntV.add (intV_eN P _ _) (intV_glue hz i))
    exact intAt_zpow_mul (by linarith [he i]) (hs i)

end Lattice

/- English proof (translation)
Introduce `j P hP h k hNF hk`. Take `⟨e, z, he, hz, himg⟩` from `hNF`. Establish `hk' : ∀ x, k x ∈ lamYat (Pr` using `Pr) (R := R) j P ↔ x ∈ lamYat (Pr := Pr) (R := R) j P := hk`. Rewrite `hz` using `[mem_stdAt_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `x hx`. Establish `hxi : IntV P x` using `(mem_lamYat (R := R) hP x).1 hx`. Establish `hmem : x ∈ nfLat P (R.N j) (cOf R j) e z` using `mem_nfLat (fun i => (he i).2) hz hxi`. Rewrite `hmem` using `[← himg]`. Take `⟨y', hy', rfl⟩` from `hmem`.

Use `⟨k.symm y', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk']`. Simplify using `using hy'`. Simplify using `[LinearEquiv.mul_apply]`. Introduce `x hx`.

Establish `h1 : h (k x) ∈ nfLat P (R.N j) (cOf R j) e z`. Rewrite using `[← himg]`. Conclude with `⟨k x, (hk' x).2 hx, rfl⟩`. Establish `h2` using `smul_int_of_mem_nfLat (fun i => (he i).1) hz h1`. Rewrite using `[mem_lamYat hP]`.

Introduce `l`. Establish `h3` using `h2 l`. Simplify `h3` using `[LinearEquiv.mul_apply]`.
-/
theorem inclAt (X : Fields) (Pr : Primes X) (R : Ranks) : InclAt Pr R := by
  intro j P hP h k hNF hk
  obtain ⟨e, z, he, hz, himg⟩ := hNF
  have hk' : ∀ x, k x ∈ lamYat (Pr := Pr) (R := R) j P ↔ x ∈ lamYat (Pr := Pr) (R := R) j P := hk
  rw [mem_stdAt_iff] at hz
  constructor
  · intro x hx
    have hxi : IntV P x := (mem_lamYat (R := R) hP x).1 hx
    have hmem : x ∈ nfLat P (R.N j) (cOf R j) e z := mem_nfLat (fun i => (he i).2) hz hxi
    rw [← himg] at hmem
    obtain ⟨y', hy', rfl⟩ := hmem
    refine ⟨k.symm y', ?_, ?_⟩
    · rw [← hk']
      simpa using hy'
    · simp [LinearEquiv.mul_apply]
  · intro x hx
    have h1 : h (k x) ∈ nfLat P (R.N j) (cOf R j) e z := by
      rw [← himg]
      exact ⟨k x, (hk' x).2 hx, rfl⟩
    have h2 := smul_int_of_mem_nfLat (fun i => (he i).1) hz h1
    rw [mem_lamYat hP]
    intro l
    have h3 := h2 l
    simpa [LinearEquiv.mul_apply] using h3

end GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm
