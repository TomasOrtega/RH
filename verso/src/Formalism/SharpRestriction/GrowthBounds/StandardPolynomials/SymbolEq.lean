import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NotCostlyZero
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.LemmaBAlt.B2

namespace Formalism.MainNotions.ColumnSystems.Pf.Col

variable {N K : ℕ} {vecc : Fin N → Bool} {B : Fin N → ℕ} {ka : Fin (N + 1) → Fin K → ℤ} {nu : ℕ → ℤ}

def Jc (nu : ℕ → ℤ) (N : ℕ) (c : ℤ) (I'' : Finset (Fin K)) : Finset (Fin (1 + K)) :=
  joinI (fun _ => if 1 ≤ c ∧ c ≤ nu (N + 1) then ({0} : Finset (Fin 1)) else ∅) (fun _ => I'') c

/- English proof (translation)
Unfold `colH`. Use `split_ifs with h`. Rewrite using `[Finset.filter_true_of_mem (fun m _ => h)]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.filter_false_of_mem (fun m _ => h)]`.

Simplify using the standard rewrite rules.
-/
theorem colH_one (a c : ℤ) : colH (fun _ : Fin 1 => a) c = if c ≤ a then 1 else 0 := by
  unfold colH
  split_ifs with h
  · rw [Finset.filter_true_of_mem (fun m _ => h)]; simp
  · rw [Finset.filter_false_of_mem (fun m _ => h)]; simp

/- English proof (translation)
Unfold `hsOf`. Establish `: (⟨min (j + 1) (N + 1), by omega⟩ : Fin (N + 1 + 1)) = Fin.succ ⟨min j N, by omega⟩` using `Fin.ext (by simp [Nat.succ_min_succ])`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem hsOf_kaS (ka : Fin (N + 1) → Fin K → ℤ) (c : ℤ) (j : ℕ) : hsOf (kaS ka) c (j + 1) = hsOf ka c j := by
  unfold hsOf
  have : (⟨min (j + 1) (N + 1), by omega⟩ : Fin (N + 1 + 1)) = Fin.succ ⟨min j N, by omega⟩ :=
    Fin.ext (by simp [Nat.succ_min_succ])
  rw [this]; rfl

/- English proof (translation)
Unfold `plTanCol Jc`. Rewrite using `[joinI_pl, joinI_tan, map_mul]`. Establish `hpl : plPart (muP nu ka) = fun t _ => nu t.val`. Use function extensionality and compare the values at `t a`. Simplify using `[plPart, muP, joinPT]`.

Establish `htan : tanPart (muP nu ka) = kaS ka` using `tanPart_join _ _`. Rewrite using `[hpl, htan]`. Use `congr 1`. Rewrite using `[Kcol_eq_KG R (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c (N + 1) le_rfl]`. Establish `e1` using `map_KG (Ψ.comp (rename (plVar (N := N + 1) (r := 1) (K := K))).toRingHom) c (hsOf (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c) (xOf R (N + 1) 1) (N + 1) (if 1 ≤ c ∧ c ≤ nu (N + 1) then ({0} : Finset (Fin 1)) else ∅)`.

Establish `e1' : Ψ (rename (plVar (N` using `N + 1) (r := 1) (K := K)) (KG c (hsOf (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c) (xOf R (N + 1) 1) (N + 1) (if 1 ≤ c ∧ c ≤ nu (N + 1) then ({0} : Finset (Fin 1)) else ∅))) = _ := e1`. Rewrite using `[e1']`. Establish `e2` using `KG_one (P := P) c (fun t => nu (min t (N + 1))) (by simpa using h.nu0) (fun t => by`. Break down `Nat.lt_or_ge t (N + 1) with ht | ht` into its components or cases. Rewrite using `[Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]; exact h.numono t`.

Rewrite using `[Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)])`. Use the proof step `(hsOf (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c)`. Use the proof step `(fun t => by unfold hsOf; exact colH_one _ _)`. Use the proof step `(fun j m => (Ψ.comp (rename (plVar (N := N + 1) (r := 1) (K := K))).toRingHom) (xOf R (N + 1) 1 j m)) (N + 1)`. Simplify using `only [Nat.min_self] at e2`.

Rewrite using `[e2]`. Use `Finset.prod_congr rfl fun t ht => ?_` and prove the remaining obligations. Establish `ht' : t < N + 1` using `Finset.mem_range.1 ht`. Rewrite using `[Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]`. Use `congr 1`.

Simplify using `[xOf, ht', plVar]`. Rewrite using `[Kcol_eq_KG R (kaS ka) c (N + 1) le_rfl]`. Establish `e1` using `map_KG (Ψ.comp (rename (tanVar (N := N + 1) (r := 1) (K := K))).toRingHom) c (hsOf (kaS ka) c) (xOf R (N + 1) K) (N + 1) I''`. Establish `e1' : Ψ (rename (tanVar (N` using `N + 1) (r := 1) (K := K)) (KG c (hsOf (kaS ka) c) (xOf R (N + 1) K) (N + 1) I'')) = _ := e1`. Rewrite using `[e1']`.

Establish `h01 : hsOf (kaS ka) c 0 = hsOf (kaS ka) c 1`. Rewrite using `[hsOf_kaS]`. Unfold `hsOf`. Use `show colH (0 : Fin K → ℤ) c = colH (ka ⟨min 0 N, by omega⟩) c`. Establish `: (⟨min 0 N, by omega⟩ : Fin (N + 1)) = 0` using `Fin.ext (by simp)`.

Rewrite using `[this, h.ka0]`. Rewrite using `[KG_shift c _ _ h01 N]`. Establish `e3` using `KG_congr (P := P) c (hs := fun j => hsOf (kaS ka) c (j + 1)) (hs' := hsOf ka c) (x := fun j => (fun m => (Ψ.comp (rename (tanVar (N := N + 1) (r := 1) (K := K))).toRingHom) (xOf R (N + 1) K (j + 1) m))) (x' := fun a b => Ψ (xOf R (N + 1) (1 + K) (a + 1) (Fin.natAdd 1 b))) N (fun …`. Use function extensionality and compare the values at `m`. Establish `: j + 1 < N + 1` using `by omega`.

Simplify using `[xOf, this, tanVar])`. Rewrite using `[e3]`.
-/
theorem symbol_eq (h : PH vecc B ka nu) (R : Type) [CommRing R] {P : Type} [CommRing P]
    (Ψ : MvPolynomial (Fin (N + 1) × Fin (1 + K)) R →+* P) (c : ℤ) (I'' : Finset (Fin K)) :
    Ψ (plTanCol R (muP nu ka) c (Jc nu N c I'')) =
      (∏ t ∈ range (N + 1), if nu t < c ∧ c ≤ nu (t + 1) then Ψ (xOf R (N + 1) (1 + K) t (Fin.castAdd K 0)) else 1) *
        KG c (hsOf ka c) (fun a b => Ψ (xOf R (N + 1) (1 + K) (a + 1) (Fin.natAdd 1 b))) N I'' := by
  unfold plTanCol Jc
  rw [joinI_pl, joinI_tan, map_mul]
  have hpl : plPart (muP nu ka) = fun t _ => nu t.val := by
    funext t a; simp [plPart, muP, joinPT]
  have htan : tanPart (muP nu ka) = kaS ka := tanPart_join _ _
  rw [hpl, htan]
  congr 1
  ·
    rw [Kcol_eq_KG R (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c (N + 1) le_rfl]
    have e1 := map_KG (Ψ.comp (rename (plVar (N := N + 1) (r := 1) (K := K))).toRingHom) c
      (hsOf (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c) (xOf R (N + 1) 1) (N + 1)
      (if 1 ≤ c ∧ c ≤ nu (N + 1) then ({0} : Finset (Fin 1)) else ∅)
    have e1' : Ψ (rename (plVar (N := N + 1) (r := 1) (K := K)) (KG c
        (hsOf (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c) (xOf R (N + 1) 1) (N + 1)
        (if 1 ≤ c ∧ c ≤ nu (N + 1) then ({0} : Finset (Fin 1)) else ∅))) = _ := e1
    rw [e1']
    have e2 := KG_one (P := P) c (fun t => nu (min t (N + 1))) (by simpa using h.nu0)
      (fun t => by
        rcases Nat.lt_or_ge t (N + 1) with ht | ht
        · rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]; exact h.numono t
        · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)])
      (hsOf (fun (t : Fin (N + 1 + 1)) (_ : Fin 1) => nu t.val) c)
      (fun t => by unfold hsOf; exact colH_one _ _)
      (fun j m => (Ψ.comp (rename (plVar (N := N + 1) (r := 1) (K := K))).toRingHom) (xOf R (N + 1) 1 j m)) (N + 1)
    simp only [Nat.min_self] at e2
    rw [e2]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' : t < N + 1 := Finset.mem_range.1 ht
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    congr 1
    simp [xOf, ht', plVar]
  ·
    rw [Kcol_eq_KG R (kaS ka) c (N + 1) le_rfl]
    have e1 := map_KG (Ψ.comp (rename (tanVar (N := N + 1) (r := 1) (K := K))).toRingHom) c
      (hsOf (kaS ka) c) (xOf R (N + 1) K) (N + 1) I''
    have e1' : Ψ (rename (tanVar (N := N + 1) (r := 1) (K := K)) (KG c (hsOf (kaS ka) c) (xOf R (N + 1) K) (N + 1) I'')) = _ := e1
    rw [e1']
    have h01 : hsOf (kaS ka) c 0 = hsOf (kaS ka) c 1 := by
      rw [hsOf_kaS]
      unfold hsOf
      show colH (0 : Fin K → ℤ) c = colH (ka ⟨min 0 N, by omega⟩) c
      have : (⟨min 0 N, by omega⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
      rw [this, h.ka0]
    rw [KG_shift c _ _ h01 N]
    have e3 := KG_congr (P := P) c (hs := fun j => hsOf (kaS ka) c (j + 1)) (hs' := hsOf ka c)
      (x := fun j => (fun m => (Ψ.comp (rename (tanVar (N := N + 1) (r := 1) (K := K))).toRingHom) (xOf R (N + 1) K (j + 1) m)))
      (x' := fun a b => Ψ (xOf R (N + 1) (1 + K) (a + 1) (Fin.natAdd 1 b))) N
      (fun j _ => hsOf_kaS ka c j)
      (fun j hj => by
        funext m
        have : j + 1 < N + 1 := by omega
        simp [xOf, this, tanVar])
    rw [e3]

end Formalism.MainNotions.ColumnSystems.Pf.Col
