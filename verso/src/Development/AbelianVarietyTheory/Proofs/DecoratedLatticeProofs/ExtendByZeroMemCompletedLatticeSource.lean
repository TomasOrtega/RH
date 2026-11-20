import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZeroLat

variable {D : D7}

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)`.
-/
theorem mxAt_mul {P : Pl D → Prop} {a b c : ℕ} {x : Mx D a b} (hx : MxAt P x) (y : Mx D b c) : MxAt P (x ⬝ y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

/- English proof (translation)
Simplify using `only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]`.
-/
theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Simplify using `only [symplO, hO, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Establish `h0 : cA D e * cA D (cA D e) = 0` using `(GlobalTheory.SplitScalar.isSplitIdem_conj he).2.1`. Establish `: hO S T x y = 0`. Unfold `hO`. Use `Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← hx d a, ← hy c b, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[symplO, this, mul_zero, map_zero]`.
-/
theorem symplO_conjHalf {S T : HSp D} {e : AE D} (he : IsSplitIdem D e) {x y : WO S T}
    (hx : IsHalf (cA D e) x) (hy : IsHalf (cA D e) y) : symplO S T x y = 0 := by
  have h0 : cA D e * cA D (cA D e) = 0 := (GlobalTheory.SplitScalar.isSplitIdem_conj he).2.1
  have : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hx d a, ← hy c b, map_mul]
    calc incA D (S.gram⁻¹ a b) * (cA D (cA D e) * cA D (y c b)) * incA D (T.gram c d) * (cA D e * x d a)
        = (cA D e * cA D (cA D e)) * (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := by ring
      _ = 0 := by rw [h0, zero_mul]
  rw [symplO, this, mul_zero, map_zero]

/- English proof (translation)
Rewrite using `[o.symplO_resS, AddEquiv.apply_symm_apply]`. Establish `h0 : symplO L T 0 ((o.resS T) t).2 = 0` using `by simp [symplO, hO]`. Rewrite using `[h0, add_zero]`. Both sides reduce to the same expression.
-/
theorem symplO_resS_symm_left {S A L T : HSp D} (o : OrthDec S A L) (a : WO A T) (t : WO S T) :
    symplO S T ((o.resS T).symm (a, 0)) t = symplO A T a (t ⬝ o.jA) := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  have h0 : symplO L T 0 ((o.resS T) t).2 = 0 := by simp [symplO, hO]
  rw [h0, add_zero]; rfl

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]`.
-/
theorem smul_isHalf {e : AE D} (he : e * e = e) {m n : ℕ} (u : Mx D m n) : IsHalf e (e • u) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

/- English proof (translation)
The claim follows from `GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])`.
-/
theorem finPart_idem_mem {e : AE D} (he : e * e = e) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])

end GlobalTheory.FinPl.ExtZeroLat

open GlobalTheory.FinPl.ExtZeroLat in

/- English proof (translation)
Introduce `D k _ _ _ _ p n _ _ ψ S A L T o ζ β LA LS LT ΛT hA hS hfac u hu`. Use `set ΛA := latO A T (LA : Set _) (LT : Set _) (· = p.v) with hΛA`. Use `set ΛS := latO S T (LS : Set _) (LT : Set _) (· = p.v) with hΛS`. Establish `he` using `p.split`. Establish `hce` using `GlobalTheory.SplitScalar.isSplitIdem_conj he`.

Take `⟨ε, hε, hsum⟩` from `p.above`. Establish `hact` using `(GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1`. Establish `hsplit : ∀ {m n : ℕ} (x : Mx D m n), MxAt (· = p.v) x → p.e • x + cA D p.e • x = x`. Introduce `m n x hx`. Rewrite using `[← add_smul, hsum]`.

Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `(hact _).1 (hx i j)`. Establish `hcol0 : GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT) 0 = 1`. Establish `hz : GlobalTheory.FinPl.ExtZero.zcol β ζ (0 : WO L T) = 0`.

Simplify using `only [GlobalTheory.FinPl.ExtZero.zcol, Matrix.zero_mulVec, Pi.zero_apply, map_zero]`. Conclude with `Matrix.mulVec_zero _`. Establish `h0 : IsHalf p.e (0 : WO L T)` using `fun i j => by simp`. Simplify using `[GlobalTheory.FinPl.ExtZero.colFun, hz, vecInd, h0]`. Establish `hext : ∀ a ∈ ΛA, IsHalf p.e a → (o.resS T).symm (a, 0) ∈ ΛS`.

Introduce `a ha hah`. Establish `h1` using `congrFun hfac ((o.resS T).symm (a, 0))`. Rewrite `h1` using `[OrthDec.boxS, AddEquiv.apply_symm_apply, hcol0, mul_one]`. Establish `h2 : halfInd p.e ΛA a = 1` using `by simp [halfInd, ha, hah]`. Rewrite `h1` using `[h2]`.

Unfold `halfInd at h1`. Assume the negation of the conclusion as `hn`. Rewrite `h1` using `[if_neg fun h => hn h.1]`. Conclude with `zero_ne_one h1`. Establish `hres : ∀ t ∈ ΛS, IsHalf p.e t → t ⬝ o.jA ∈ ΛA`.

Introduce `t ht hth`. Establish `h1` using `congrFun hfac t`. Establish `h2 : halfInd p.e ΛS t = 1` using `by simp [halfInd, ht, hth]`. Rewrite `h1` using `[h2, OrthDec.boxS]`. Assume the negation of the conclusion as `hn`.

Establish `: halfInd p.e ΛA ((o.resS T) t).1 = 0`. Unfold `halfInd`. Rewrite using `[if_neg fun h => hn h.1]`. Rewrite `h1` using `[this, zero_mul]`. Conclude with `one_ne_zero h1`.

Establish `huM : MxAt (· = p.v) u` using `GlobalTheory.FinPl.LatMem.latO_mxAt hu`. Establish `heu : p.e • u ∈ ΛA` using `GlobalTheory.LatticeStable.smul_mem_latO D A T _ _ _ _ (finPart_idem_mem he.1) u hu`. Establish `hι : (o.resS T).symm (p.e • u, 0) ∈ ΛS` using `hext _ heu (smul_isHalf he.1 u)`. Establish `hιM : MxAt (· = p.v) ((o.resS T).symm (u, 0))`. Rewrite using `[OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]`.

Conclude with `mxAt_mul huM _`. Use `(hS _ hιM).2 fun u' hu' => ?_` and prove the remaining obligations. Establish `hu'M : MxAt (· = p.v) u'` using `GlobalTheory.FinPl.LatMem.latO_mxAt hu'`. Establish `heu' : p.e • u' ∈ ΛS` using `GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem he.1) u' hu'`. Establish `hceu' : cA D p.e • u' ∈ ΛS` using `GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem hce.1) u' hu'`.

Rewrite using `[symplO_resS_symm_left, ← hsplit u' hu'M, Matrix.add_mul, symplO_add_right, AddChar.map_add_eq_mul]`. Establish `part1 : ψ (symplO A T u ((p.e • u') ⬝ o.jA)) = 1` using `(hA u huM).1 hu _ (hres _ heu' (smul_isHalf he.1 u'))`. Establish `part2 : ψ (symplO A T u ((cA D p.e • u') ⬝ o.jA)) = 1`. Rewrite using `[← hsplit u huM, symplO_add_left, AddChar.map_add_eq_mul]`. Establish `hz : symplO A T (cA D p.e • u) ((cA D p.e • u') ⬝ o.jA) = 0`.

Use `symplO_conjHalf he (smul_isHalf hce.1 u) ?_` and prove the remaining obligations. Introduce `i j`. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, (smul_isHalf hce.1 u') i l]`.

Rewrite using `[hz, AddChar.map_zero_eq_one, mul_one, ← symplO_resS_symm_left]`. Conclude with `(hS _ (GlobalTheory.FinPl.LatMem.latO_mxAt hι)).1 hι _ hceu'`. Rewrite using `[part1, part2, one_mul]`.
-/
theorem GlobalTheory.FinPl.ExtZero.extZero_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO A T, MxAt (· = p.v) u → (u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), ψ (symplO A T u u') = 1)) → (∀ u : WO S T, MxAt (· = p.v) u → (u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), ψ (symplO S T u u') = 1)) → halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), (o.resS T).symm (u, 0) ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n _ _ ψ S A L T o ζ β LA LS LT ΛT hA hS hfac u hu
  classical
  set ΛA := latO A T (LA : Set _) (LT : Set _) (· = p.v) with hΛA
  set ΛS := latO S T (LS : Set _) (LT : Set _) (· = p.v) with hΛS
  have he := p.split
  have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hact := (GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1

  have hsplit : ∀ {m n : ℕ} (x : Mx D m n), MxAt (· = p.v) x → p.e • x + cA D p.e • x = x := by
    intro m n x hx
    rw [← add_smul, hsum]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hact _).1 (hx i j)

  have hcol0 : GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT) 0 = 1 := by
    have hz : GlobalTheory.FinPl.ExtZero.zcol β ζ (0 : WO L T) = 0 := by
      simp only [GlobalTheory.FinPl.ExtZero.zcol, Matrix.zero_mulVec, Pi.zero_apply, map_zero]
      exact Matrix.mulVec_zero _
    have h0 : IsHalf p.e (0 : WO L T) := fun i j => by simp
    simp [GlobalTheory.FinPl.ExtZero.colFun, hz, vecInd, h0]

  have hext : ∀ a ∈ ΛA, IsHalf p.e a → (o.resS T).symm (a, 0) ∈ ΛS := by
    intro a ha hah
    have h1 := congrFun hfac ((o.resS T).symm (a, 0))
    rw [OrthDec.boxS, AddEquiv.apply_symm_apply, hcol0, mul_one] at h1
    have h2 : halfInd p.e ΛA a = 1 := by simp [halfInd, ha, hah]
    rw [h2] at h1
    unfold halfInd at h1
    by_contra hn
    rw [if_neg fun h => hn h.1] at h1
    exact zero_ne_one h1

  have hres : ∀ t ∈ ΛS, IsHalf p.e t → t ⬝ o.jA ∈ ΛA := by
    intro t ht hth
    have h1 := congrFun hfac t
    have h2 : halfInd p.e ΛS t = 1 := by simp [halfInd, ht, hth]
    rw [h2, OrthDec.boxS] at h1
    by_contra hn
    have : halfInd p.e ΛA ((o.resS T) t).1 = 0 := by
      unfold halfInd; rw [if_neg fun h => hn h.1]
    rw [this, zero_mul] at h1
    exact one_ne_zero h1
  have huM : MxAt (· = p.v) u := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have heu : p.e • u ∈ ΛA := GlobalTheory.LatticeStable.smul_mem_latO D A T _ _ _ _ (finPart_idem_mem he.1) u hu
  have hι : (o.resS T).symm (p.e • u, 0) ∈ ΛS := hext _ heu (smul_isHalf he.1 u)
  have hιM : MxAt (· = p.v) ((o.resS T).symm (u, 0)) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
    exact mxAt_mul huM _
  refine (hS _ hιM).2 fun u' hu' => ?_
  have hu'M : MxAt (· = p.v) u' := GlobalTheory.FinPl.LatMem.latO_mxAt hu'
  have heu' : p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem he.1) u' hu'
  have hceu' : cA D p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem hce.1) u' hu'
  rw [symplO_resS_symm_left, ← hsplit u' hu'M, Matrix.add_mul, symplO_add_right, AddChar.map_add_eq_mul]
  have part1 : ψ (symplO A T u ((p.e • u') ⬝ o.jA)) = 1 :=
    (hA u huM).1 hu _ (hres _ heu' (smul_isHalf he.1 u'))
  have part2 : ψ (symplO A T u ((cA D p.e • u') ⬝ o.jA)) = 1 := by
    rw [← hsplit u huM, symplO_add_left, AddChar.map_add_eq_mul]
    have hz : symplO A T (cA D p.e • u) ((cA D p.e • u') ⬝ o.jA) = 0 := by
      refine symplO_conjHalf he (smul_isHalf hce.1 u) ?_
      intro i j
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, (smul_isHalf hce.1 u') i l]
    rw [hz, AddChar.map_zero_eq_one, mul_one, ← symplO_resS_symm_left]
    exact (hS _ (GlobalTheory.FinPl.LatMem.latO_mxAt hι)).1 hι _ hceu'
  rw [part1, part2, one_mul]

end
