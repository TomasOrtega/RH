import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLeadingCoeffPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

section Numbers

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (hR : GenericPointSectionInput.Statement.{u, w})

include hR in

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `pp L hW hnef _`. Establish `h1 : (fun i => (L i).toSubSystem) = ![(L 0).toSubSystem]`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `hnef pp bot_le hW`.

Consider the case `succ n ih`. Introduce `pp L hW hnef hL`. Establish `hlast : Fin.last (n + 1) ≠ 0` using `fun h => by simpa using congrArg Fin.val h`. Take `⟨s, hs, hsI⟩` from `exists_sec_not_mem (L (Fin.last (n + 1))) (hL _ hlast) hW`. Establish `hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α` using `fun _ => SubSystem k x Ω) (fun i : Fin (n + 1) => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last (n + 1))).toSubSystem := (Fin.snoc_init_self _).symm`.

Rewrite using `[hsplit, (hR k Ω N x).2.2.2.1 (n + 1) pp (fun i => L (Fin.castSucc i)) (L (Fin.last (n + 1))) s hW hs hsI]`. Use `finsum_nonneg fun qq => ?_` and prove the remaining obligations. Use `split_ifs with h`. Use `mul_nonneg (Nat.cast_nonneg _) (ih qq (fun i => L (Fin.castSucc i)) h.2 hnef fun i hi => ?_)` and prove the remaining obligations. Conclude with `hL _ fun h0 => hi (Fin.castSucc_injective _ (by rw [h0]; rfl))`.

Conclude with `le_rfl`.
-/
theorem interNum_nonneg_nef_veryAmple : ∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin (n + 1) → LineBundle k x),
    IsSubvar x pp (n + 1) → Nef (L 0).toSubSystem → (∀ i, i ≠ 0 → IsVeryAmple (L i).toSubSystem) →
      0 ≤ interNum pp (fun i => (L i).toSubSystem) := by
  intro n
  induction n with
  | zero =>
    intro pp L hW hnef _
    have h1 : (fun i => (L i).toSubSystem) = ![(L 0).toSubSystem] := by
      funext i; fin_cases i; rfl
    rw [h1]
    exact hnef pp bot_le hW
  | succ n ih =>
    intro pp L hW hnef hL
    have hlast : Fin.last (n + 1) ≠ 0 := fun h => by simpa using congrArg Fin.val h
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last (n + 1))) (hL _ hlast) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin (n + 1) => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last (n + 1))).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 (n + 1) pp (fun i => L (Fin.castSucc i)) (L (Fin.last (n + 1))) s hW hs
      hsI]
    refine finsum_nonneg fun qq => ?_
    split_ifs with h
    · refine mul_nonneg (Nat.cast_nonneg _) (ih qq (fun i => L (Fin.castSucc i)) h.2 hnef fun i hi => ?_)
      exact hL _ fun h0 => hi (Fin.castSucc_injective _ (by rw [h0]; rfl))
    · exact le_rfl

end Numbers

/- English proof (translation)
Introduce `k _ Ω _ _ N x d M Nb q m b hZ hM hNb hva hb`. Set `L : Fin (d + 1) → LineBundle k x` to `fun _ => Nb`. Establish `hV : ((M.tpow q).tensor (twistBundle k x m)).toSubSystem = Nb.toSubSystem`. Rewrite using `[hNb, LineBundle.tensor_toSubSystem, LineBundle.tpow_toSubSystem]`. Both sides reduce to the same expression.

Establish `hm0 : 0 ≤ m`. Establish `: (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * b` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨mn, hmn⟩` from `Int.eq_ofNat_of_zero_le hm0`. Establish `h1 : interNum (primeOf (S` using `k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) = q * bundleNum (primeOf (S := k) x) (Function.update L 0 M) + m * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by`.

Establish `e1 : interNum (primeOf (S` using `k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) = bundleNum (primeOf (S := k) x) (Function.update L 0 ((M.tpow q).tensor (twistBundle k x m))) := by`. Unfold `bundleNum`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = 0`.

Substitute `hj` using the available equality. Simplify using `only [Function.update_self, hV]`. Simplify using `only [Function.update_of_ne hj, L]`. Rewrite using `[e1, bundleNum_tensor hR hZ, bundleNum_tpow hR hZ, hmn, bundleNum_twist hR hZ]`. Establish `h2 : interNum (primeOf (S` using `k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ)) (fun _ : Fin d => Nb.toSubSystem)) = b * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by`.

Rewrite using `[← bundleNum_twist hR hZ]`. Unfold `bundleNum`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations.

Simplify using `only [Fin.cons_zero, Function.update_self, twistBundle_toSubSystem]`. Simplify using `only [Fin.cons_succ, Function.update_of_ne (Fin.succ_ne_zero i), L]`. Establish `hX : 0 ≤ bundleNum (primeOf (S` using `k) x) (Function.update L 0 M) := by`. Use `interNum_nonneg_nef_veryAmple hR d _ _ hZ (by simpa only [Function.update_self] using hM) fun i hi => ?_` and prove the remaining obligations. Simplify using `only [Function.update_of_ne hi, L]`.

Conclude with `hva`. Establish `hY : 0 < bundleNum (primeOf (S` using `k) x) (Function.update L 0 (twistBundle k x 1)) := by`. Use `hPos k Ω N x (d + 1) _ _ hZ fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality.

Simplify `(isVeryAmple_twistSys_one (S := k) (x := x))` using `only [Function.update_self, twistBundle_toSubSystem]`. Simplify using `only [Function.update_of_ne hi, L]`. Conclude with `hva`. Rewrite using `[h1, h2]`. Establish `hc` using `mul_pos (sub_pos.mpr hb) hY`.

Establish `hq` using `mul_nonneg (Int.natCast_nonneg q) hX`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem LeadingCoeffPos.proof_of_cut (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) : LeadingCoeffPos.Statement.{u, w} := by
  intro k _ Ω _ _ N x d M Nb q m b hZ hM hNb hva hb
  let L : Fin (d + 1) → LineBundle k x := fun _ => Nb
  have hV : ((M.tpow q).tensor (twistBundle k x m)).toSubSystem = Nb.toSubSystem := by
    rw [hNb, LineBundle.tensor_toSubSystem, LineBundle.tpow_toSubSystem]
    rfl
  have hm0 : 0 ≤ m := by
    have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * b := by positivity
    linarith
  obtain ⟨mn, hmn⟩ := Int.eq_ofNat_of_zero_le hm0

  have h1 : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
      q * bundleNum (primeOf (S := k) x) (Function.update L 0 M) +
        m * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by
    have e1 : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
        bundleNum (primeOf (S := k) x) (Function.update L 0 ((M.tpow q).tensor (twistBundle k x m))) := by
      unfold bundleNum
      congr 1
      funext j
      by_cases hj : j = 0
      · subst hj
        simp only [Function.update_self, hV]
      · simp only [Function.update_of_ne hj, L]
    rw [e1, bundleNum_tensor hR hZ, bundleNum_tpow hR hZ, hmn, bundleNum_twist hR hZ]

  have h2 : interNum (primeOf (S := k) x)
      (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) =
      b * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by
    rw [← bundleNum_twist hR hZ]
    unfold bundleNum
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero, Function.update_self, twistBundle_toSubSystem]
    · simp only [Fin.cons_succ, Function.update_of_ne (Fin.succ_ne_zero i), L]

  have hX : 0 ≤ bundleNum (primeOf (S := k) x) (Function.update L 0 M) := by
    refine interNum_nonneg_nef_veryAmple hR d _ _ hZ (by simpa only [Function.update_self] using hM)
      fun i hi => ?_
    simp only [Function.update_of_ne hi, L]
    exact hva

  have hY : 0 < bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by
    refine hPos k Ω N x (d + 1) _ _ hZ fun i => ?_
    by_cases hi : i = 0
    · subst hi
      simpa only [Function.update_self, twistBundle_toSubSystem] using
        (isVeryAmple_twistSys_one (S := k) (x := x))
    · simp only [Function.update_of_ne hi, L]
      exact hva
  rw [h1, h2]
  have hc := mul_pos (sub_pos.mpr hb) hY
  have hq := mul_nonneg (Int.natCast_nonneg q) hX
  nlinarith

end GroundTheory.Heights₂.Heights.Kleiman
