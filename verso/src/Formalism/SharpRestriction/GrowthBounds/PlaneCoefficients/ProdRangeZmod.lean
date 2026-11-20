import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.FrRevInj
import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.PlMonPsiExpPAdd
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundJoint
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.NormalSetCounting
  Formalism.MainNotions.TraceSpectra

/- English proof (translation)
The claim follows from `Formalism.MainNotions.NormalSetCounting.restSpec`.
-/
theorem restSpec : RestSpec := Formalism.MainNotions.NormalSetCounting.restSpec

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, J = n + 1` from `⟨J - 1, by have := NeZero.ne J; omega⟩`. Conclude with `(Fin.prod_univ_eq_prod_range f (n + 1)).symm`.
-/
theorem prod_range_zmod {M : Type*} [CommMonoid M] (J : ℕ) [NeZero J] (f : ℕ → M) :
    ∏ i ∈ Finset.range J, f i = ∏ j : ZMod J, f j.val := by
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by have := NeZero.ne J; omega⟩
  exact (Fin.prod_univ_eq_prod_range f (n + 1)).symm

/- English proof (translation)
Establish `hsp` using `Formalism.MainNotions.NormalSetCounting.restSpec n' r Fr L₁ N₁ hV J Dt.nL hnL j`. Take `⟨-, hper, hmono, hgap, -⟩` from `hV`. Establish `hr : 1 ≤ r` using `Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)`. Rewrite `hA` using `[MvPolynomial.supported_eq_adjoin_X]`. Proceed by induction on `hA using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Take `⟨⟨y, a⟩, hy, rfl⟩` from `hx`. Establish `hy' : y ∈ Fr.letters (segZ j)` using `hy`. Simplify using `only [plEmb, phSeg, chi, rename_X, aeval_X, map_pow, map_X, if_pos hy']`. Break down `hsp y hy' with ⟨l, rfl, hml⟩ | ⟨mm, rfl, hml⟩ | ⟨mm, rfl, hml⟩` into its components or cases.

Rewrite using `[hml]`. Simplify using `only [SignedChainData.ph, PsiP, aeval_X]`. Both sides reduce to the same expression. Rewrite using `[hml]`. Simplify using `only [SignedChainData.ph, PsiP, aeval_X]`.

Both sides reduce to the same expression. Rewrite using `[hml]`. Simplify using `only [SignedChainData.ph, PsiP, aeval_X, map_pow, ← pow_mul, SignedChainData.P]`. Take `⟨s, hs, hsh⟩` from `Formalism.MainNotions.Proposition5Numerics.DdG.shift Fr hper hJ (j - 1)`. Simplify using `only [sub_add_cancel] at hsh`.

Establish `hA1 : ∀ k, Fr.fr (segZ (j - 1)) k = Fr.fr (segZ j - 1) k + s` using `fun k => (hsh k).1`. Establish `hA2 : ∀ k, Fr.fr (segZ (j - 1) + 1) k = Fr.fr (segZ j) k + s` using `fun k => (hsh k).2`. Establish `e1 : plVar Fr hk Dt.nL (⟨j - 1, Sum.inr mm⟩ : TL J Dt.nL r) a = castV hk (posOf n' (Fr.fr (segZ j - 1) (r - 1 - mm.val)), Fin.castAdd K a)` using `by show (posOf n' (Fr.fr (segZ (j - 1)) (r - 1 - mm.val)), Fin.cast hk.symm (Fin.castAdd K a)) = _`. Rewrite using `[hA1]`. Break down `hs with rfl | rfl` into its components or cases.

Rewrite using `[add_zero]`. Both sides reduce to the same expression. Rewrite using `[Formalism.MainNotions.Proposition5Numerics.DdG.posOf_add_n]`. Both sides reduce to the same expression. Establish `e2 : lowP Fr p (⟨j - 1, Sum.inr mm⟩ : TL J Dt.nL r) * p ^ Dt.gP (j - 1) mm = p ^ Fr.dist (segZ j) (Fr.fr (segZ j - 1) (r - 1 - mm.val))` using `by show p ^ Fr.dist (segZ (j - 1)) (Fr.fr (segZ (j - 1)) (r - 1 - mm.val)) * p ^ Dt.gP (j - 1) mm = _`.

Rewrite using `[← pow_add, hgP]`. Use `congr 1`. Simplify using `only [Frames.dist, hA1, hA2]`. Establish `h1` using `Formalism.MainNotions.Proposition5Numerics.DdG.fr_le Fr hmono (segZ j - 1) (Nat.sub_le (r - 1) mm.val) (by omega)`. Establish `h2` using `hgap (segZ j - 1)`.

Simplify using `only [sub_add_cancel] at h2`. Establish `h3` using `Formalism.MainNotions.Proposition5Numerics.DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (r - 1)) (by omega)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e1, e2]`. Consider the case `algebraMap c`.

Simplify using `only [MvPolynomial.algebraMap_eq, MvPolynomial.algHom_C, map_C]`. Consider the case `add x y _ _ hx hy`. Simplify using `only [map_add]`. Rewrite using `[hx, hy]`. Consider the case `mul x y _ _ hx hy`.

Simplify using `only [map_mul]`. Rewrite using `[hx, hy]`.
-/
theorem seg_PsiP (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) {J : ℕ}
    [NeZero J] (Dt : SignedChainData p O r J) (hJ : J = Fr.J) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) (hA : A ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)}) :
    MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) (phSeg O K p Fr (segZ j) (plEmb O r K A))) =
      PsiP (O := O) Fr p hk Dt.nL (Dt.ph (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) A))) := by
  have hsp := Formalism.MainNotions.NormalSetCounting.restSpec n' r Fr L₁ N₁ hV J Dt.nL hnL j
  obtain ⟨-, hper, hmono, hgap, -⟩ := hV
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  rw [MvPolynomial.supported_eq_adjoin_X] at hA
  induction hA using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨y, a⟩, hy, rfl⟩ := hx
    have hy' : y ∈ Fr.letters (segZ j) := hy
    simp only [plEmb, phSeg, chi, rename_X, aeval_X, map_pow, map_X, if_pos hy']
    rcases hsp y hy' with ⟨l, rfl, hml⟩ | ⟨mm, rfl, hml⟩ | ⟨mm, rfl, hml⟩
    · rw [hml]
      simp only [SignedChainData.ph, PsiP, aeval_X]
      rfl
    · rw [hml]
      simp only [SignedChainData.ph, PsiP, aeval_X]
      rfl
    · rw [hml]
      simp only [SignedChainData.ph, PsiP, aeval_X, map_pow, ← pow_mul, SignedChainData.P]
      obtain ⟨s, hs, hsh⟩ := Formalism.MainNotions.Proposition5Numerics.DdG.shift Fr hper hJ (j - 1)
      simp only [sub_add_cancel] at hsh
      have hA1 : ∀ k, Fr.fr (segZ (j - 1)) k = Fr.fr (segZ j - 1) k + s := fun k => (hsh k).1
      have hA2 : ∀ k, Fr.fr (segZ (j - 1) + 1) k = Fr.fr (segZ j) k + s := fun k => (hsh k).2
      have e1 : plVar Fr hk Dt.nL (⟨j - 1, Sum.inr mm⟩ : TL J Dt.nL r) a =
          castV hk (posOf n' (Fr.fr (segZ j - 1) (r - 1 - mm.val)), Fin.castAdd K a) := by
        show (posOf n' (Fr.fr (segZ (j - 1)) (r - 1 - mm.val)), Fin.cast hk.symm (Fin.castAdd K a)) = _
        rw [hA1]
        rcases hs with rfl | rfl
        · rw [add_zero]
          rfl
        · rw [Formalism.MainNotions.Proposition5Numerics.DdG.posOf_add_n]
          rfl
      have e2 : lowP Fr p (⟨j - 1, Sum.inr mm⟩ : TL J Dt.nL r) * p ^ Dt.gP (j - 1) mm =
          p ^ Fr.dist (segZ j) (Fr.fr (segZ j - 1) (r - 1 - mm.val)) := by
        show p ^ Fr.dist (segZ (j - 1)) (Fr.fr (segZ (j - 1)) (r - 1 - mm.val)) * p ^ Dt.gP (j - 1) mm = _
        rw [← pow_add, hgP]
        congr 1
        simp only [Frames.dist, hA1, hA2]
        have h1 := Formalism.MainNotions.Proposition5Numerics.DdG.fr_le Fr hmono (segZ j - 1) (Nat.sub_le (r - 1) mm.val) (by omega)
        have h2 := hgap (segZ j - 1)
        simp only [sub_add_cancel] at h2
        have h3 := Formalism.MainNotions.Proposition5Numerics.DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (r - 1)) (by omega)
        omega
      rw [e1, e2]
  | algebraMap c =>
    simp only [MvPolynomial.algebraMap_eq, MvPolynomial.algHom_C, map_C]
  | add x y _ _ hx hy =>
    simp only [map_add]
    rw [hx, hy]
  | mul x y _ _ hx hy =>
    simp only [map_mul]
    rw [hx, hy]

/- English proof (translation)
Unfold `RestTr`. Introduce `p _ n' r K m _ _ _ O _ _ _ hk Fr L₁ N₁ hV hn' J _ Dt hT A hA l hl ga hPE`. Take `⟨hJ, hnL, hsgn, hgP, -, -⟩` from `hT`. Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Establish `hr : 1 ≤ r` using `Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hseg : ∀ j : ZMod J, MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) (phSeg O K p Fr ((j.val : ℕ) : ℤ) (plEmb O r K (A ((j.val : ℕ) : ℤ))))) = PsiP (O` using `O) Fr p hk Dt.nL (Dt.ph (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j))))) := by`. Introduce `j`. Establish `hj : j.val < Fr.J`. Rewrite using `[← hJ]`.

Conclude with `ZMod.val_lt j`. Conclude with `seg_PsiP p O hk Fr L₁ N₁ hV Dt hJ hnL hgP j (A (segZ j)) (hA j.val hj)`. Establish `hz : zPl p O hk Fr A l ga = PsiP (O` using `O) Fr p hk Dt.nL (∏ j : ZMod J, Dt.ph (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j))))) * monomial (l.mapDomain (castV hk) + ga) 1 := by`. Unfold `zPl`. Simplify using `only [map_mul, map_prod, rename_monomial, map_monomial, map_one]`.

Rewrite using `[mul_assoc, monomial_mul, one_mul, ← hJ, prod_range_zmod J]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl (fun j _ => hseg j)`. Rewrite using `[hz, Formalism.MainNotions.NormalSetCounting.levelAtPrime_character_mul p hk hp hV hr hJ hnL]`. Introduce `j ll a hs`.

Establish `hs'` using `hsgn j ll`. Rewrite `hs'` using `[hs]`. Establish `hodd : ¬ Even (llPos Fr (segZ j) ll.val)` using `of_decide_eq_false hs'.symm`. Establish `hll : ll.val < (Fr.LLset (segZ j)).card`. Rewrite using `[← hnL]`.

Conclude with `ll.isLt`. Establish `hmem` using `Formalism.MainNotions.Proposition5Numerics.DdG.llPos_mem Fr (segZ j) ll.val hll`. Take `⟨hlet, hW⟩` from `Formalism.MainNotions.Proposition5Numerics.LL_sub_letters hV hr (segZ j) _ hmem`. Establish `hlab` using `hl (segZ j) _ hlet hW (Fin.castAdd K a)`. Establish `hinj : Function.Injective (castV (n'` using `n') hk) := by`.

Introduce `v w h`. Simplify using `only [castV, Prod.mk.injEq] at h`. Conclude with `Prod.ext h.1 (Fin.ext (by simpa using congrArg Fin.val h.2))`. Establish `hpv : plVar Fr hk Dt.nL (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) a = castV hk (posOf n' (llPos Fr (segZ j) ll.val), Fin.castAdd K a)` using `rfl`. Establish `hgz : ga (plVar Fr hk Dt.nL (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) a) = 0`.

Assume the negation of the conclusion as `hne`. Establish `hev : Even (posOf n' (llPos Fr (segZ j) ll.val)).val` using `(hPE _ hne).2`. Apply `hodd` to reduce the goal to its premises. Establish `hn0 : (n' : ℤ) ≠ 0` using `by exact_mod_cast NeZero.ne n'`. Establish `hnn : 0 ≤ llPos Fr (segZ j) ll.val % (n' : ℤ)` using `Int.emod_nonneg _ hn0`.

Establish `hlt : llPos Fr (segZ j) ll.val % (n' : ℤ) < n'` using `Int.emod_lt_of_pos _ (by exact_mod_cast NeZero.pos n')`. Establish `hv : ((posOf n' (llPos Fr (segZ j) ll.val)).val : ℤ) = llPos Fr (segZ j) ll.val % (n' : ℤ)` using `by show (((llPos Fr (segZ j) ll.val % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = _`. Establish `hlt' : (llPos Fr (segZ j) ll.val % (n' : ℤ)).toNat < n'` using `by omega`. Rewrite using `[Nat.mod_eq_of_lt hlt', Int.toNat_of_nonneg hnn]`. Establish `h2 : (2 : ℤ) ∣ n'` using `by exact_mod_cast (even_iff_two_dvd.mp hn')`.

Rewrite using `[Int.even_iff, ← Int.emod_emod_of_dvd _ h2, ← hv]`. Conclude with `Int.even_iff.mp (Int.even_coe_nat _ |>.mpr hev)`. Use `show (l.mapDomain (castV hk) + ga) (plVar Fr hk Dt.nL (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) a) / lowP Fr p (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) = 0`. Rewrite using `[Finsupp.add_apply, hgz, add_zero, hpv, Finsupp.mapDomain_apply hinj]`. Conclude with `Nat.div_eq_of_lt hlab`.
-/
theorem restTr : RestTr := by
  unfold RestTr
  intro p _ n' r K m _ _ _ O _ _ _ hk Fr L₁ N₁ hV hn' J _ Dt hT A hA l hl ga hPE
  obtain ⟨hJ, hnL, hsgn, hgP, -, -⟩ := hT
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  refine ⟨?_, ?_⟩
  · have hseg : ∀ j : ZMod J,
        MvPolynomial.map (algebraMap O (KK O))
          (rename (castV hk) (phSeg O K p Fr ((j.val : ℕ) : ℤ) (plEmb O r K (A ((j.val : ℕ) : ℤ))))) =
        PsiP (O := O) Fr p hk Dt.nL
          (Dt.ph (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j))))) := by
      intro j
      have hj : j.val < Fr.J := by
        rw [← hJ]
        exact ZMod.val_lt j
      exact seg_PsiP p O hk Fr L₁ N₁ hV Dt hJ hnL hgP j (A (segZ j)) (hA j.val hj)
    have hz : zPl p O hk Fr A l ga =
        PsiP (O := O) Fr p hk Dt.nL (∏ j : ZMod J,
          Dt.ph (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j))))) *
        monomial (l.mapDomain (castV hk) + ga) 1 := by
      unfold zPl
      simp only [map_mul, map_prod, rename_monomial, map_monomial, map_one]
      rw [mul_assoc, monomial_mul, one_mul, ← hJ, prod_range_zmod J]
      congr 1
      exact Finset.prod_congr rfl (fun j _ => hseg j)
    rw [hz, Formalism.MainNotions.NormalSetCounting.levelAtPrime_character_mul p hk hp hV hr hJ hnL]
  · intro j ll a hs
    have hs' := hsgn j ll
    rw [hs] at hs'
    have hodd : ¬ Even (llPos Fr (segZ j) ll.val) := of_decide_eq_false hs'.symm
    have hll : ll.val < (Fr.LLset (segZ j)).card := by
      rw [← hnL]
      exact ll.isLt
    have hmem := Formalism.MainNotions.Proposition5Numerics.DdG.llPos_mem Fr (segZ j) ll.val hll
    obtain ⟨hlet, hW⟩ := Formalism.MainNotions.Proposition5Numerics.LL_sub_letters hV hr (segZ j) _ hmem
    have hlab := hl (segZ j) _ hlet hW (Fin.castAdd K a)
    have hinj : Function.Injective (castV (n' := n') hk) := by
      intro v w h
      simp only [castV, Prod.mk.injEq] at h
      exact Prod.ext h.1 (Fin.ext (by simpa using congrArg Fin.val h.2))
    have hpv : plVar Fr hk Dt.nL (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) a =
        castV hk (posOf n' (llPos Fr (segZ j) ll.val), Fin.castAdd K a) := rfl
    have hgz : ga (plVar Fr hk Dt.nL (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) a) = 0 := by
      by_contra hne
      have hev : Even (posOf n' (llPos Fr (segZ j) ll.val)).val := (hPE _ hne).2
      apply hodd
      have hn0 : (n' : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n'
      have hnn : 0 ≤ llPos Fr (segZ j) ll.val % (n' : ℤ) := Int.emod_nonneg _ hn0
      have hlt : llPos Fr (segZ j) ll.val % (n' : ℤ) < n' :=
        Int.emod_lt_of_pos _ (by exact_mod_cast NeZero.pos n')
      have hv : ((posOf n' (llPos Fr (segZ j) ll.val)).val : ℤ) = llPos Fr (segZ j) ll.val % (n' : ℤ) := by
        show (((llPos Fr (segZ j) ll.val % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = _
        have hlt' : (llPos Fr (segZ j) ll.val % (n' : ℤ)).toNat < n' := by omega
        rw [Nat.mod_eq_of_lt hlt', Int.toNat_of_nonneg hnn]
      have h2 : (2 : ℤ) ∣ n' := by exact_mod_cast (even_iff_two_dvd.mp hn')
      rw [Int.even_iff, ← Int.emod_emod_of_dvd _ h2, ← hv]
      exact Int.even_iff.mp (Int.even_coe_nat _ |>.mpr hev)
    show (l.mapDomain (castV hk) + ga) (plVar Fr hk Dt.nL (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) a) /
      lowP Fr p (⟨j, Sum.inl ll⟩ : TL J Dt.nL r) = 0
    rw [Finsupp.add_apply, hgz, add_zero, hpv, Finsupp.mapDomain_apply hinj]
    exact Nat.div_eq_of_lt hlab

end Formalism.MainNotions.PairMembershipBlocks
