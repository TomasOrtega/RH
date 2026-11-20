import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.CauchyBinet

/- English proof (translation)
Establish `h1 : ∑ q, lform D ρ q * plk u e q = ∑ f : Fin k → Fin (M + 1), (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det` using `Equiv.sum_comp (plE M k) (fun f : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det)`. Rewrite using `[h1]`. Simplify using `only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lform_plk (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h1 : ∑ q, lform D ρ q * plk u e q =
      ∑ f : Fin k → Fin (M + 1), (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det :=
    Equiv.sum_comp (plE M k)
      (fun f : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det)
  rw [h1]
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

variable {T : Type} {m : T → ℕ} {S : Type} [CommRing S] {M : ℕ} {D c : Let m → Fin (M + 1) → S}

/- English proof (translation)
Simplify using `only [cellVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_cellVec (w : Pm m) (x : CellVar m → S) (y z : Let m) :
    ∑ r, D y r * cellVec c w x z r = ∑ i, cell x z.1 i z.2 * ∑ r, D y r * c ⟨z.1, w z.1 i⟩ r := by
  simp only [cellVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  ring

/- English proof (translation)
Rewrite using `[pair_cellVec, Finset.sum_eq_single a]`. Rewrite using `[h]`. Simplify using `[wLet]`. Introduce `i _ hi`. Rewrite using `[h, if_neg, mul_zero]`.

Introduce `he`. Simplify using `only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he`. Conclude with `hi ((w τ).injective he).symm`. Simplify using the standard rewrite rules.
-/
theorem pair_same (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (τ : T) (a b : Fin (m τ)) :
    ∑ r, D (wLet w ⟨τ, a⟩) r * cellVec c w x ⟨τ, b⟩ r = cell x τ a b := by
  rw [pair_cellVec, Finset.sum_eq_single a]
  · rw [h]
    simp [wLet]
  · intro i _ hi
    rw [h, if_neg, mul_zero]
    intro he
    simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
    exact hi ((w τ).injective he).symm
  · simp

/- English proof (translation)
Rewrite using `[pair_cellVec]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h, if_neg, mul_zero]`. Introduce `he`. Establish `h2` using `congrArg Sigma.fst he`.

Conclude with `hne h2`.
-/
theorem pair_ne (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (y z : Let m) (hne : y.1 ≠ z.1) :
    ∑ r, D (wLet w y) r * cellVec c w x z r = 0 := by
  rw [pair_cellVec]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [h, if_neg, mul_zero]
  intro he
  have h2 := congrArg Sigma.fst he
  exact hne h2

/- English proof (translation)
Take `⟨τ, a⟩` from `z`. Rewrite using `[pair_same h]`. Simplify using `[cell]`.
-/
theorem pair_self (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (z : Let m) :
    ∑ r, D (wLet w z) r * cellVec c w x z r = 1 := by
  obtain ⟨τ, a⟩ := z
  rw [pair_same h]
  simp [cell]

/- English proof (translation)
Distinguish the cases in `h1 : y.1 = z.1`. Take `⟨τ, a⟩` from `y`. Take `⟨τ', b⟩` from `z`. Simplify using `only at h1 hle`. Substitute `h1` using the available equality.

Rewrite using `[pair_same h]`. Establish `hab : a ≠ b` using `fun e => hne (by rw [e])`. Establish `hlt : ¬ b < a` using `not_lt.2 hle`. Simplify using `[cell, hab, hlt]`. Conclude with `pair_ne h w x y z h1`.
-/
theorem pair_zero (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (y z : Let m) (hne : y ≠ z)
    (hle : (y.2 : ℕ) ≤ z.2) : ∑ r, D (wLet w y) r * cellVec c w x z r = 0 := by
  by_cases h1 : y.1 = z.1
  · obtain ⟨τ, a⟩ := y
    obtain ⟨τ', b⟩ := z
    dsimp only at h1 hle
    subst h1
    rw [pair_same h]
    have hab : a ≠ b := fun e => hne (by rw [e])
    have hlt : ¬ b < a := not_lt.2 hle
    simp [cell, hab, hlt]
  · exact pair_ne h w x y z h1

/- English proof (translation)
Establish `hb : N.BlockTriangular b` using `fun l l' hl => h0 l l' (fun e => by subst e; exact lt_irrefl _ hl) hl.le`. Rewrite using `[hb.det]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Establish `: N.toSquareBlock b a = 1`. Use extensionality with `⟨l, hl⟩ ⟨l', hl'⟩`.

Rewrite using `[Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]`. Use `split_ifs with he`. Take `rfl : l = l'` from `congrArg Subtype.val he`. Conclude with `h1 l`. Conclude with `h0 l l' (fun e => he (Subtype.ext e)) (by rw [hl, hl'])`.

Rewrite using `[this, Matrix.det_one]`.
-/
theorem det_eq_one_of_unitri {k : ℕ} (N : Matrix (Fin k) (Fin k) S) (b : Fin k → ℕ) (h1 : ∀ l, N l l = 1)
    (h0 : ∀ l l', l ≠ l' → b l' ≤ b l → N l l' = 0) : N.det = 1 := by
  have hb : N.BlockTriangular b := fun l l' hl =>
    h0 l l' (fun e => by subst e; exact lt_irrefl _ hl) hl.le
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : N.toSquareBlock b a = 1 := by
    ext ⟨l, hl⟩ ⟨l', hl'⟩
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    split_ifs with he
    · obtain rfl : l = l' := congrArg Subtype.val he
      exact h1 l
    · exact h0 l l' (fun e => he (Subtype.ext e)) (by rw [hl, hl'])
  rw [this, Matrix.det_one]

/- English proof (translation)
Rewrite using `[lform_plk]`. Use `det_eq_one_of_unitri _ (fun l => ((e l).2 : ℕ)) (fun l => pair_self h w x (e l)) fun l l' hl hb => ?_` and prove the remaining obligations. Conclude with `pair_zero h w x (e l') (e l) (fun e' => hl (he.1 e').symm) hb`.
-/
theorem lform_plk_down (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (k : ℕ) (e : Fin k → Let m)
    (he : Down e) : ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1 := by
  rw [lform_plk]
  refine det_eq_one_of_unitri _ (fun l => ((e l).2 : ℕ)) (fun l => pair_self h w x (e l)) fun l l' hl hb => ?_
  exact pair_zero h w x (e l') (e l) (fun e' => hl (he.1 e').symm) hb

/- English proof (translation)
Rewrite using `[lform_plk]`. Simplify using `only [std, pair_same hD]`. Rewrite using `[Matrix.det_of_upperTriangular]`. Rewrite using `[Fin.prod_univ_castSucc, Finset.prod_eq_one, one_mul]`. Establish `: Fin.castLE (Nat.succ_le_of_lt j.2) (Fin.last j) = j` using `Fin.ext rfl`.

Simplify using `only [Matrix.of_apply, Fin.val_last, if_true, this, cell, dif_pos h]`. Introduce `l _`. Establish `hl : ((l.castSucc : Fin (j + 1)) : ℕ) ≠ j` using `ne_of_lt l.2`. Simplify using `only [Matrix.of_apply, if_neg hl, cell, lt_irrefl, dif_neg, if_true, not_false_eq_true]`. Introduce `l l' hl`.

Establish `hl2 : (l' : ℕ) < l` using `hl`. Establish `hl' : (l' : ℕ) ≠ j` using `by have := l.2; omega`. Establish `hn : ¬ Fin.castLE (Nat.succ_le_of_lt j.2) l < Fin.castLE (Nat.succ_le_of_lt j.2) l'` using `not_lt.2 (le_of_lt hl2)`. Establish `hne : Fin.castLE (Nat.succ_le_of_lt j.2) l' ≠ Fin.castLE (Nat.succ_le_of_lt j.2) l` using `ne_of_lt hl2`. Simplify using `only [Matrix.of_apply, if_neg hl', cell, dif_neg hn, if_neg hne]`.
-/
theorem lform_plk_coord (hD : LeftInv D c) (w : Pm m) (x : CellVar m → S) (τ : T) (i j : Fin (m τ)) (h : j < i) :
    ∑ q, lform D (fun l : Fin (j + 1) =>
        wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q *
      plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ := by
  rw [lform_plk]
  simp only [std, pair_same hD]
  rw [Matrix.det_of_upperTriangular]
  · rw [Fin.prod_univ_castSucc, Finset.prod_eq_one, one_mul]
    · have : Fin.castLE (Nat.succ_le_of_lt j.2) (Fin.last j) = j := Fin.ext rfl
      simp only [Matrix.of_apply, Fin.val_last, if_true, this, cell, dif_pos h]
    · intro l _
      have hl : ((l.castSucc : Fin (j + 1)) : ℕ) ≠ j := ne_of_lt l.2
      simp only [Matrix.of_apply, if_neg hl, cell, lt_irrefl, dif_neg, if_true, not_false_eq_true]
  · intro l l' hl
    have hl2 : (l' : ℕ) < l := hl
    have hl' : (l' : ℕ) ≠ j := by have := l.2; omega
    have hn : ¬ Fin.castLE (Nat.succ_le_of_lt j.2) l < Fin.castLE (Nat.succ_le_of_lt j.2) l' :=
      not_lt.2 (le_of_lt hl2)
    have hne : Fin.castLE (Nat.succ_le_of_lt j.2) l' ≠ Fin.castLE (Nat.succ_le_of_lt j.2) l :=
      ne_of_lt hl2
    simp only [Matrix.of_apply, if_neg hl', cell, dif_neg hn, if_neg hne]

/- English proof (translation)
Assemble the required witnesses or components as `⟨lform_plk, fun _ _ _ _ _ _ _ w x h => ⟨lform_plk_down h w x, lform_plk_coord h w x⟩⟩`.
-/
theorem main : (∀ (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S) (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι), ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det) ∧ ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (D c : Let m → Fin (M + 1) → S) (w : Pm m) (x : CellVar m → S), LeftInv D c → (∀ (k : ℕ) (e : Fin k → Let m), Down e → ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1) ∧ ∀ (τ : T) (i j : Fin (m τ)) (h : j < i), ∑ q, lform D (fun l : Fin (j + 1) => wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q * plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ :=
  ⟨lform_plk, fun _ _ _ _ _ _ _ w x h =>
    ⟨lform_plk_down h w x, lform_plk_coord h w x⟩⟩

end GlobalTheory.FlagEmb.CauchyBinet
