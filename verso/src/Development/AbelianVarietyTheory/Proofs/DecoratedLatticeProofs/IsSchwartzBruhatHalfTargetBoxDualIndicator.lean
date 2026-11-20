import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

namespace RowSB

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.add_apply, mul_add, hx i j, hy i j]`.
-/
theorem isHalf_add_of {e : AE D} {a b : ℕ} {x y : Mx D a b} (hx : IsHalf e x) (hy : IsHalf e y) :
    IsHalf e (x + y) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

/- English proof (translation)
Introduce `i j`. Rewrite using `[show (m • x) i j = m • x i j from rfl, nsmul_eq_mul, mul_left_comm, hx i j]`.
-/
theorem isHalf_nsmul_of {e : AE D} {a b : ℕ} {x : Mx D a b} (hx : IsHalf e x) (m : ℕ) : IsHalf e (m • x) := by
  intro i j
  rw [show (m • x) i j = m • x i j from rfl, nsmul_eq_mul, mul_left_comm, hx i j]

/- English proof (translation)
Introduce `i j`. Establish `h` using `hxy i j`. Rewrite `h` using `[Matrix.add_apply, mul_add, hy i j]`. Conclude with `add_right_cancel h`.
-/
theorem isHalf_of_add {e : AE D} {a b : ℕ} {x y : Mx D a b} (hxy : IsHalf e (x + y)) (hy : IsHalf e y) :
    IsHalf e x := by
  intro i j
  have h := hxy i j
  rw [Matrix.add_apply, mul_add, hy i j] at h
  exact add_right_cancel h

/- English proof (translation)
Introduce `i j`. Rewrite using `[OrthDec.resT_symm_apply]`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, ha]`.

Conclude with `Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, hb]`.
-/
theorem isHalf_resT_symm_pair {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {e : AE D} {a : WO T A} {b : WO T L}
    (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e ((o.resT T).symm (a, b)) := by
  intro i j
  rw [OrthDec.resT_symm_apply]
  simp only [Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, ha]
  · exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, hb]

/- English proof (translation)
Simplify using `only [zrow, Matrix.vecMul_add, Pi.add_apply, map_add]`. Rewrite using `[← smul_add, ← Matrix.add_vecMul]`. Both sides reduce to the same expression.
-/
theorem zrow_add' {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (x y : WO T L) :
    zrow β ζ (x + y) = zrow β ζ x + zrow β ζ y := by
  simp only [zrow, Matrix.vecMul_add, Pi.add_apply, map_add]
  rw [← smul_add, ← Matrix.add_vecMul]
  rfl

def zrowHom {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) : WO T L →+ (n → k) :=
  AddMonoidHom.mk' (zrow β ζ) (zrow_add' β ζ)

/- English proof (translation)
The claim follows from `map_nsmul (zrowHom β ζ) m x`.
-/
theorem zrow_nsmul' {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (m : ℕ) (x : WO T L) :
    zrow β ζ (m • x) = m • zrow β ζ x :=
  map_nsmul (zrowHom β ζ) m x

/- English proof (translation)
Introduce `y hy` and use `by rw [add_dotProduct]; exact add_mem (h y hy) (h' y hy)`.
-/
theorem inDual_add' {Λ : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual Λ η) (h' : InDual Λ ξ) :
    InDual Λ (η + ξ) := fun y hy => by
  rw [add_dotProduct]; exact add_mem (h y hy) (h' y hy)

/- English proof (translation)
Introduce `y hy` and use `by rw [sub_dotProduct]; exact sub_mem (h y hy) (h' y hy)`.
-/
theorem inDual_sub' {Λ : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual Λ η) (h' : InDual Λ ξ) :
    InDual Λ (η - ξ) := fun y hy => by
  rw [sub_dotProduct]; exact sub_mem (h y hy) (h' y hy)

/- English proof (translation)
Introduce `y hy` and use `by rw [smul_dotProduct]; exact nsmul_mem (h y hy) m`.
-/
theorem inDual_nsmul' {Λ : Submodule 𝒪[k] (n → k)} {η : n → k} (h : InDual Λ η) (m : ℕ) :
    InDual Λ (m • η) := fun y hy => by
  rw [smul_dotProduct]; exact nsmul_mem (h y hy) m

/- English proof (translation)
Unfold `rowFun dualInd at h`. Distinguish the cases in `hy : IsHalf p.e y`. Rewrite `h` using `[if_pos hy]`. Distinguish the cases in `hd : InDual ΛT (zrow β ζ y)`. Conclude with `⟨hy, hd⟩`.

Rewrite `h` using `[if_neg hd]`. Conclude with `absurd rfl h`. Rewrite `h` using `[if_neg hy]`. Conclude with `absurd rfl h`.
-/
theorem rowFun_dualInd_ne_zero {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (h : rowFun β ζ (dualInd ΛT) y ≠ 0) :
    IsHalf p.e y ∧ InDual ΛT (zrow β ζ y) := by
  unfold rowFun dualInd at h
  by_cases hy : IsHalf p.e y
  · rw [if_pos hy] at h
    by_cases hd : InDual ΛT (zrow β ζ y)
    · exact ⟨hy, hd⟩
    · rw [if_neg hd] at h; exact absurd rfl h
  · rw [if_neg hy] at h; exact absurd rfl h

/- English proof (translation)
Unfold `rowFun dualInd`. Rewrite using `[if_pos hy, if_pos hd]`.
-/
theorem rowFun_dualInd_eq_one {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (hy : IsHalf p.e y) (hd : InDual ΛT (zrow β ζ y)) :
    rowFun β ζ (dualInd ΛT) y = 1 := by
  unfold rowFun dualInd
  rw [if_pos hy, if_pos hd]

/- English proof (translation)
Establish `hz : zrow β ζ (x + m • y) = zrow β ζ x + m • zrow β ζ y`. Rewrite using `[zrow_add', zrow_nsmul']`. Establish `hm` using `inDual_nsmul' hd m`. Unfold `rowFun dualInd`. Distinguish the cases in `hx : IsHalf p.e x`.

Rewrite using `[if_pos (isHalf_add_of hx (isHalf_nsmul_of hy m)), if_pos hx, hz]`. Establish `hiff : InDual ΛT (zrow β ζ x + m • zrow β ζ y) ↔ InDual ΛT (zrow β ζ x)` using `⟨fun h => by simpa using inDual_sub' h hm, fun h => inDual_add' h hm⟩`. Distinguish the cases in `hd' : InDual ΛT (zrow β ζ x)`. Rewrite using `[if_pos hd', if_pos (hiff.2 hd')]`. Rewrite using `[if_neg hd', if_neg (fun h => hd' (hiff.1 h))]`.

Rewrite using `[if_neg hx, if_neg (fun h => hx (isHalf_of_add h (isHalf_nsmul_of hy m)))]`.
-/
theorem rowFun_dualInd_add_nsmul {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (hy : IsHalf p.e y) (hd : InDual ΛT (zrow β ζ y)) (m : ℕ)
    (x : WO T L) : rowFun β ζ (dualInd ΛT) (x + m • y) = rowFun β ζ (dualInd ΛT) x := by
  have hz : zrow β ζ (x + m • y) = zrow β ζ x + m • zrow β ζ y := by
    rw [zrow_add', zrow_nsmul']
  have hm := inDual_nsmul' hd m
  unfold rowFun dualInd
  by_cases hx : IsHalf p.e x
  · rw [if_pos (isHalf_add_of hx (isHalf_nsmul_of hy m)), if_pos hx, hz]
    have hiff : InDual ΛT (zrow β ζ x + m • zrow β ζ y) ↔ InDual ΛT (zrow β ζ x) :=
      ⟨fun h => by simpa using inDual_sub' h hm, fun h => inDual_add' h hm⟩
    by_cases hd' : InDual ΛT (zrow β ζ x)
    · rw [if_pos hd', if_pos (hiff.2 hd')]
    · rw [if_neg hd', if_neg (fun h => hd' (hiff.1 h))]
  · rw [if_neg hx, if_neg (fun h => hx (isHalf_of_add h (isHalf_nsmul_of hy m)))]

/- English proof (translation)
Unfold `halfInd`. Apply the tactic sequence `split_ifs with h <;> simp [h]`.
-/
theorem halfInd_eq_one_iff' {e : AE D} {a b : ℕ} (Λ : AddSubgroup (Mx D a b)) (t : Mx D a b) :
    halfInd e Λ t = 1 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  split_ifs with h <;> simp [h]

/- English proof (translation)
Unfold `halfInd`. Apply the tactic sequence `split_ifs with h <;> simp [h]`.
-/
theorem halfInd_ne_zero_iff' {e : AE D} {a b : ℕ} (Λ : AddSubgroup (Mx D a b)) (t : Mx D a b) :
    halfInd e Λ t ≠ 0 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  split_ifs with h <;> simp [h]

end RowSB

open RowSB

/- English proof (translation)
Introduce `D k _ _ _ _ p n _ _ S A L T o ζ β LA LS LT ΛT H Φ hΦ`. Take `⟨hsupp, m, hm, hinv, hlat⟩` from `hΦ`. Establish `hH : ∀ w, halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) w = halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) (o.resT T w).1 * rowFun β ζ (dualInd ΛT) (o.resT T w).2` using `fun w => congrFun H w`. Establish `hbox : ∀ w, o.boxT T Φ (rowFun β ζ (dualInd ΛT)) w = Φ (o.resT T w).1 * rowFun β ζ (dualInd ΛT) (o.resT T w).2` using `fun w => rfl`. Use `⟨fun t ht => ?_, m, hm, fun u hu hhu t => ?_, fun t ht => ?_⟩` and prove the remaining obligations.

Rewrite `ht` using `[hbox]`. Establish `h1` using `hsupp _ (left_ne_zero_of_mul ht)`. Establish `h2` using `(rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)).1`. Use `isHalf_resT_symm_pair o T h1 h2` as an intermediate fact. Rewrite `this` using `[Prod.mk.eta, AddEquiv.symm_apply_apply]`. Then use the resulting hypothesis.

Establish `hu1 : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) u = 1` using `(halfInd_eq_one_iff' _ _).2 ⟨hu, hhu⟩`. Rewrite `hu1` using `[hH]`. Establish `hA` using `(halfInd_ne_zero_iff' _ _).1 (left_ne_zero_of_mul_eq_one hu1)`. Establish `hR` using `rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul_eq_one hu1)`. Rewrite using `[hbox, hbox, map_add, map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, hinv _ hA.1 hA.2, rowFun_dualInd_add_nsmul β ζ ΛT hR.1 hR.2]`.

Rewrite `ht` using `[hbox]`. Establish `hΦt` using `left_ne_zero_of_mul ht`. Establish `h1` using `hsupp _ hΦt`. Establish `hR` using `rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)`. Establish `hmt : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (m • t) = 1`.

Rewrite using `[hH, map_nsmul, Prod.smul_fst, Prod.smul_snd, (halfInd_eq_one_iff' _ _).2 ⟨hlat _ hΦt, isHalf_nsmul_of h1 m⟩, rowFun_dualInd_eq_one β ζ ΛT (isHalf_nsmul_of hR.1 m) (by rw [zrow_nsmul']; exact inDual_nsmul' hR.2 m), one_mul]`. Conclude with `((halfInd_eq_one_iff' _ _).1 hmt).1`.
-/
theorem isSBHalf_boxT_rowFun_dualInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (o.boxT T Φ (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT))) := by
  intro D k _ _ _ _ p n _ _ S A L T o ζ β LA LS LT ΛT H Φ hΦ
  obtain ⟨hsupp, m, hm, hinv, hlat⟩ := hΦ
  have hH : ∀ w, halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) w =
      halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) (o.resT T w).1 *
        rowFun β ζ (dualInd ΛT) (o.resT T w).2 := fun w => congrFun H w
  have hbox : ∀ w, o.boxT T Φ (rowFun β ζ (dualInd ΛT)) w =
      Φ (o.resT T w).1 * rowFun β ζ (dualInd ΛT) (o.resT T w).2 := fun w => rfl
  refine ⟨fun t ht => ?_, m, hm, fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [hbox] at ht
    have h1 := hsupp _ (left_ne_zero_of_mul ht)
    have h2 := (rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)).1
    have := isHalf_resT_symm_pair o T h1 h2
    rwa [Prod.mk.eta, AddEquiv.symm_apply_apply] at this
  · have hu1 : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) u = 1 :=
      (halfInd_eq_one_iff' _ _).2 ⟨hu, hhu⟩
    rw [hH] at hu1
    have hA := (halfInd_ne_zero_iff' _ _).1 (left_ne_zero_of_mul_eq_one hu1)
    have hR := rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul_eq_one hu1)
    rw [hbox, hbox, map_add, map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      hinv _ hA.1 hA.2, rowFun_dualInd_add_nsmul β ζ ΛT hR.1 hR.2]
  · rw [hbox] at ht
    have hΦt := left_ne_zero_of_mul ht
    have h1 := hsupp _ hΦt
    have hR := rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)
    have hmt : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (m • t) = 1 := by
      rw [hH, map_nsmul, Prod.smul_fst, Prod.smul_snd,
        (halfInd_eq_one_iff' _ _).2 ⟨hlat _ hΦt, isHalf_nsmul_of h1 m⟩,
        rowFun_dualInd_eq_one β ζ ΛT (isHalf_nsmul_of hR.1 m) (by rw [zrow_nsmul']; exact inDual_nsmul' hR.2 m),
        one_mul]
    exact ((halfInd_eq_one_iff' _ _).1 hmt).1

end GlobalTheory.FinPl.ExtZero

end
