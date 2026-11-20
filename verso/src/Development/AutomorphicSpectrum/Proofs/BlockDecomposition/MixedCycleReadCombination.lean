import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepDualInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTrivialLineBundle

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MixZ

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a)
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

/- English proof (translation)
Introduce `k` and use `⟨c k, ((hz k (c k)).1).1 (CxPts.ptsIn_mono (inf_le_right.trans (mchart_le c k)) hy)⟩`.
-/
theorem multicone_of_isUnder {U : (MP ℤ m n).Opens} {c : ∀ k, Bk n k} {y : CxPts (mpStr ℤ m n) σ₀}
    {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder y z) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (U ⊓ mchart c)) :
    ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun k =>
  ⟨c k, ((hz k (c k)).1).1 (CxPts.ptsIn_mono (inf_le_right.trans (mchart_le c k)) hy)⟩

/- English proof (translation)
Take `⟨u, h₁, h₂, h₃⟩` from `hM`. Use `⟨u, h₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha]`. Conclude with `h₂`. Introduce `i c y z hz hy`.

Rewrite using `[← hh z (multicone_of_isUnder hz hy), ← ha]`. Conclude with `h₃ i c y z hz hy`.
-/
theorem isHermRep_congr {M : HermLB (mpStr ℤ m n)} {A B : HermLine (Bk n)} (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z)
    (hM : IsHermRep M A) : IsHermRep M B := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hM
  refine ⟨u, h₁, ?_, ?_⟩
  · rw [← ha]
    exact h₂
  · intro i c y z hz hy
    rw [← hh z (multicone_of_isUnder hz hy), ← ha]
    exact h₃ i c y z hz hy

/- English proof (translation)
Use `⟨(powLine A e.toNat).tensor (powLine A (-e).toNat).inv, isHermRep_tens _ _ _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM) (isHermRep_dual _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM)), ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Establish `e₁ : ((e.toNat : ℤ) - ((-e).toNat : ℤ)) = e` using `by omega`. Simplify using `only [HermLine.tensor, HermLine.inv, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, powLine_a, smul_eq_mul]`. Take the linear combination `(A.a k) * e₁`.

Introduce `z hz`. Establish `hp` using `(A.pos z hz).ne'`. Simplify using `only [HermLine.tensor, HermLine.inv, PowRep.h_powLine]`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hp]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem isHermRep_zp {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} (hM : IsHermRep M A) (e : ℤ) :
    ∃ B : HermLine (Bk n), IsHermRep (zp M e) B ∧ B.a = e • A.a ∧
      ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = A.h z ^ e := by
  refine ⟨(powLine A e.toNat).tensor (powLine A (-e).toNat).inv,
    isHermRep_tens _ _ _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM)
      (isHermRep_dual _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM)), ?_, ?_⟩
  · funext k
    have e₁ : ((e.toNat : ℤ) - ((-e).toNat : ℤ)) = e := by omega
    simp only [HermLine.tensor, HermLine.inv, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, powLine_a, smul_eq_mul]
    linear_combination (A.a k) * e₁
  · intro z hz
    have hp := (A.pos z hz).ne'
    simp only [HermLine.tensor, HermLine.inv, PowRep.h_powLine]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hp]
    congr 1
    omega

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Conclude with `⟨_, isHermRep_triv m n, by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine], fun z _ => by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]⟩`. Consider the case `cons o l ih`. Take `⟨B, hB, ha, hh⟩` from `ih`.

Take `⟨C, hC, ca, ch⟩` from `isHermRep_zp (hM o) (a o)`. Use `⟨C.tensor B, isHermRep_tens _ _ _ _ _ _ hC hB, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [HermLine.tensor, List.map_cons, List.sum_cons, ca, ha]`. Simplify using `only [HermLine.tensor, List.map_cons, List.prod_cons, ch z hz, hh z hz]`.
-/
theorem isHermRep_foldr {κ : Type} (M : κ → HermLB (mpStr ℤ m n)) (A : κ → HermLine (Bk n))
    (hM : ∀ o, IsHermRep (M o) (A o)) (a : κ → ℤ) (l : List κ) :
    ∃ B : HermLine (Bk n), IsHermRep (l.foldr (fun i N => (zp (M i) (a i)).tens N) (HermLB.triv (mpStr ℤ m n))) B ∧
      B.a = (l.map fun o => a o • (A o).a).sum ∧
      ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = (l.map fun o => (A o).h z ^ a o).prod := by
  induction l with
  | nil =>
    exact ⟨_, isHermRep_triv m n, by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine], fun z _ => by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]⟩
  | cons o l ih =>
    obtain ⟨B, hB, ha, hh⟩ := ih
    obtain ⟨C, hC, ca, ch⟩ := isHermRep_zp (hM o) (a o)
    refine ⟨C.tensor B, isHermRep_tens _ _ _ _ _ _ hC hB, ?_, fun z hz => ?_⟩
    · simp only [HermLine.tensor, List.map_cons, List.sum_cons, ca, ha]
    · simp only [HermLine.tensor, List.map_cons, List.prod_cons, ch z hz, hh z hz]

/- English proof (translation)
Introduce `m n κ _ M A hM a`. Take `⟨B, hB, ha, hh⟩` from `isHermRep_foldr M A hM a (Finset.univ : Finset κ).toList`. Use `isHermRep_congr ?_ (fun z hz => ?_) hB` and prove the remaining obligations. Rewrite using `[ha, Finset.sum_map_toList]`. Both sides reduce to the same expression.

Rewrite using `[hh z hz, Finset.prod_map_toList]`. Conclude with `(if_pos hz).symm`.
-/
theorem readComb : ReadComb := by
  intro m n κ _ M A hM a
  obtain ⟨B, hB, ha, hh⟩ := isHermRep_foldr M A hM a (Finset.univ : Finset κ).toList
  refine isHermRep_congr ?_ (fun z hz => ?_) hB
  · rw [ha, Finset.sum_map_toList]
    rfl
  · rw [hh z hz, Finset.prod_map_toList]
    exact (if_pos hz).symm

end GlobalTheory.CompanionTheory.MixZ
