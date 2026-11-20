import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ThmIUnique

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Unfold `recR`. Use `congr 1`. Use `finsum_mem_congr rfl fun W hW => ?_` and prove the remaining obligations. Distinguish the cases in `hh : IsHorizontal W`. Rewrite using `[if_pos hh, if_pos hh, h W hW hh]`.

Rewrite using `[if_neg hh, if_neg hh]`.
-/
theorem recR_congr {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (h : ∀ W ∈ divSupp P s, IsHorizontal W → I W n L = J W n L) :
    recR I P L A s = recR J P L A s := by
  classical
  unfold recR
  congr 1
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · rw [if_pos hh, if_pos hh, h W hW hh]
  · rw [if_neg hh, if_neg hh]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.support_one, Finset.mem_singleton]`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_one' : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

/- English proof (translation)
Introduce `m hm k`. Take `⟨m1, hm1, m2, hm2, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul f g hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]`.
-/
theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

open Classical in

/- English proof (translation)
Introduce `m hm k'`. Rewrite `hm` using `[MvPolynomial.support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality.

Simplify using `[Finsupp.single_apply]`. Establish `: ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩` using `fun j e => h (congrArg Sigma.fst e).symm`. Simplify using `[Finsupp.single_apply, this, h, Pi.single_apply]`.
-/
theorem isMultiHomog_X' (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using (isMultiHomog_one' (ι := ι))`. Consider the case `succ n ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `isMultiHomog_mul' ih hf`.
-/
theorem isMultiHomog_pow' {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (isMultiHomog_one' (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul' ih hf

/- English proof (translation)
Establish `key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k) (∑ k ∈ s, d k • Pi.single k 1)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (isMultiHomog_one' (ι := ι))`. Consider the case `insert k s hk ih`.

Rewrite using `[Finset.prod_insert hk, Finset.sum_insert hk]`. Conclude with `isMultiHomog_mul' (isMultiHomog_pow' (isMultiHomog_X' k (c k)) _) ih`. Establish `e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `key Finset.univ` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem isMultiHomog_coordMonomial (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isMultiHomog_one' (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul' (isMultiHomog_pow' (isMultiHomog_X' k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

/- English proof (translation)
Introduce `h`. Take `⟨k, -, hk⟩` from `(hP.prod_mem_iff).mp h`. Conclude with `hc k (hP.mem_of_pow_mem _ hk)`.
-/
theorem coordMonomial_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := (hP.prod_mem_iff).mp h
  exact hc k (hP.mem_of_pow_mem _ hk)

/- English proof (translation)
Establish `hPp : P.IsPrime` using `hP.2.1.1`. Use `choose c hc using hP.2.1.2.2`. Set `b : K → ℕ` to `fun k => (-A.a k).toNat`. Set `e : K → ℕ` to `fun k => (A.a k + (b k : ℤ)).toNat`. Set `B : HermLine ι` to `HermLine.sqMetric b`.

Establish `hB : IsSmoothHerm B` using `isSmoothHerm_sqMetric b`. Establish `hC : IsSmoothHerm (A.tensor B)` using `isSmoothHerm_tensor hA hB`. Establish `hBa : ∀ k, B.a k = (b k : ℤ)` using `fun k => rfl`. Establish `hCa : ∀ k, (A.tensor B).a k = (e k : ℤ)`. Introduce `k`.

Establish `h0 : (0 : ℤ) ≤ A.a k + ((-A.a k).toNat : ℤ)`. Rewrite using `[Int.toNat_eq_max]`. Use linear arithmetic over natural numbers and integers. Conclude with `(Int.toNat_of_nonneg h0).symm`. Set `sB : MRing ι` to `∏ k, (X ⟨k, c k⟩ : MRing ι) ^ b k`.

Set `sC : MRing ι` to `∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k`. Establish `hsB : IsMultiHomog sB b` using `isMultiHomog_coordMonomial c b`. Establish `hsC : IsMultiHomog sC e` using `isMultiHomog_coordMonomial c e`. Establish `hsBP : sB ∉ P` using `coordMonomial_not_mem hPp c hc b`. Establish `hsCP : sC ∉ P` using `coordMonomial_not_mem hPp c hc e`.

Establish `diff : ∀ F : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ, IsRFamily F → F P (m + 1) (Fin.snoc L A) = recR F P L (A.tensor B) sC - recR F P L B sB`. Introduce `F hF`. Establish `h1` using `hF.1 P m L A B hP hL hA hB`. Rewrite `h1` using `[hF.2 P m L (A.tensor B) sC e hP hL hC hCa hsC hsCP, hF.2 P m L B sB b hP hL hB hBa hsB hsBP]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hor : ∀ (X' : HermLine ι) (s : MRing ι), IsSectionOn P X' s → ∀ W ∈ divSupp P s, IsHorizontal W → I W m L = J W m L` using `fun X' s hs W hW hh => hlow W ((divSuppArith K ι P m X' s W hP hs hW).1 hh)`. Rewrite using `[diff I hI, diff J hJ, recR_congr P L (A.tensor B) sC (hor _ sC ⟨e, hCa, hsC, hsCP⟩), recR_congr P L B sB (hor _ sB ⟨b, hBa, hsB, hsBP⟩)]`.
-/
theorem eq_of_lower {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsRFamily I) (hJ : IsRFamily J) {P : Ideal (MRing ι)} {m : ℕ}
    (L : Fin m → HermLine ι) (A : HermLine ι) (hP : IsArithVar P (m + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hlow : ∀ W, IsArithVar W m → I W m L = J W m L) :
    I P (m + 1) (Fin.snoc L A) = J P (m + 1) (Fin.snoc L A) := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose c hc using hP.2.1.2.2

  let b : K → ℕ := fun k => (-A.a k).toNat
  let e : K → ℕ := fun k => (A.a k + (b k : ℤ)).toNat
  let B : HermLine ι := HermLine.sqMetric b
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric b
  have hC : IsSmoothHerm (A.tensor B) := isSmoothHerm_tensor hA hB
  have hBa : ∀ k, B.a k = (b k : ℤ) := fun k => rfl
  have hCa : ∀ k, (A.tensor B).a k = (e k : ℤ) := by
    intro k
    have h0 : (0 : ℤ) ≤ A.a k + ((-A.a k).toNat : ℤ) := by
      rw [Int.toNat_eq_max]
      omega
    exact (Int.toNat_of_nonneg h0).symm
  let sB : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ b k
  let sC : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k
  have hsB : IsMultiHomog sB b := isMultiHomog_coordMonomial c b
  have hsC : IsMultiHomog sC e := isMultiHomog_coordMonomial c e
  have hsBP : sB ∉ P := coordMonomial_not_mem hPp c hc b
  have hsCP : sC ∉ P := coordMonomial_not_mem hPp c hc e

  have diff : ∀ F : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ, IsRFamily F →
      F P (m + 1) (Fin.snoc L A) = recR F P L (A.tensor B) sC - recR F P L B sB := by
    intro F hF
    have h1 := hF.1 P m L A B hP hL hA hB
    rw [hF.2 P m L (A.tensor B) sC e hP hL hC hCa hsC hsCP,
      hF.2 P m L B sB b hP hL hB hBa hsB hsBP] at h1
    linarith
  have hor : ∀ (X' : HermLine ι) (s : MRing ι), IsSectionOn P X' s →
      ∀ W ∈ divSupp P s, IsHorizontal W → I W m L = J W m L := fun X' s hs W hW hh =>
    hlow W ((divSuppArith K ι P m X' s W hP hs hW).1 hh)
  rw [diff I hI, diff J hJ,
    recR_congr P L (A.tensor B) sC (hor _ sC ⟨e, hCa, hsC, hsCP⟩),
    recR_congr P L B sB (hor _ sB ⟨b, hBa, hsB, hsBP⟩)]

end ThmIUnique

/- English proof (translation)
Unfold `ThmIUnique.Statement UniqueStatement`. Introduce `K _ ι _ I J hI hJ`. Establish `key : ∀ (m : ℕ) (P : Ideal (MRing ι)) (L : Fin (m + 1) → HermLine ι), IsArithVar P (m + 1) → (∀ j, IsSmoothHerm (L j)) → I P (m + 1) L = J P (m + 1) L`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero`. Introduce `P L hP hL`. Rewrite using `[← Fin.snoc_init_self L]`. Conclude with `ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _) fun W hW => absurd hW (h₀ K ι W)`. Consider the case `succ m ih`.

Introduce `P L hP hL`. Rewrite using `[← Fin.snoc_init_self L]`. Conclude with `ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _) fun W hW => ih W _ hW fun j => hL j.castSucc`. Introduce `P n L hn hP hL`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`.

Conclude with `key m P L hP hL`.
-/
theorem ThmIUnique.proof (h₀ : ArithVarZeroStatement) : ThmIUnique.Statement := by
  unfold ThmIUnique.Statement UniqueStatement
  intro K _ ι _ I J hI hJ
  have key : ∀ (m : ℕ) (P : Ideal (MRing ι)) (L : Fin (m + 1) → HermLine ι), IsArithVar P (m + 1) →
      (∀ j, IsSmoothHerm (L j)) → I P (m + 1) L = J P (m + 1) L := by
    intro m
    induction m with
    | zero =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => absurd hW (h₀ K ι W)
    | succ m ih =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => ih W _ hW fun j => hL j.castSucc
  intro P n L hn hP hL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m P L hP hL

end

end GroundTheory.Heights₂.Heights.Inter
