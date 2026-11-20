import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LeadingCoeffPosSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleProductPosSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

/- English proof (translation)
Introduce `pp _ hW`. Establish `h` using `interNum_nonneg_of_veryAmple hR 1 pp (fun _ => L) hW (fun _ => hL)`. Establish `he : (fun _ : Fin 1 => L.toSubSystem) = ![L.toSubSystem]`. Use function extensionality and compare the values at `i`. Use `fin_cases i`.

Both sides reduce to the same expression. Rewrite `h` using `[he]`. Then use the resulting hypothesis.
-/
theorem nef_of_isVeryAmple (hR : GenericPointSectionInput.Statement.{u, w}) {k : Type u} [Field k] {Ω : Type w} [Field Ω]
    [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω} (L : LineBundle k x) (hL : IsVeryAmple L.toSubSystem) :
    Nef L.toSubSystem := by
  intro pp _ hW
  have h := interNum_nonneg_of_veryAmple hR 1 pp (fun _ => L) hW (fun _ => hL)
  have he : (fun _ : Fin 1 => L.toSubSystem) = ![L.toSubSystem] := by
    funext i; fin_cases i; rfl
  rwa [he] at h

/- English proof (translation)
Introduce `k _ Ω _ _ N x d M Nb q m b hZ hM hNb hva hb`. Set `L : Fin (d + 1) → LineBundle k x` to `fun _ => Nb`. Establish `hV : ((M.tpow q).tensor (twistBundle k x m)).toSubSystem = Nb.toSubSystem`. Rewrite using `[hNb, LineBundle.tensor_toSubSystem, LineBundle.tpow_toSubSystem]`. Both sides reduce to the same expression.

Establish `hm0 : 0 ≤ m`. Establish `: (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * b` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨mn, hmn⟩` from `Int.eq_ofNat_of_zero_le hm0`. Establish `h1 : interNum (primeOf (S` using `k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) = q * bundleNum (primeOf (S := k) x) (Function.update L 0 M) + m * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by`.

Establish `e1 : interNum (primeOf (S` using `k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) = bundleNum (primeOf (S := k) x) (Function.update L 0 ((M.tpow q).tensor (twistBundle k x m))) := by`. Unfold `bundleNum`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = 0`.

Substitute `hj` using the available equality. Simplify using `only [Function.update_self, hV]`. Simplify using `only [Function.update_of_ne hj, L]`. Rewrite using `[e1, bundleNum_tensor hR hZ, bundleNum_tpow hR hZ, hmn, bundleNum_twist hR hZ]`. Establish `h2 : interNum (primeOf (S` using `k) x) (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ)) (fun _ : Fin d => Nb.toSubSystem)) = b * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by`.

Rewrite using `[← bundleNum_twist hR hZ]`. Unfold `bundleNum`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations.

Simplify using `only [Fin.cons_zero, Function.update_self, twistBundle_toSubSystem]`. Simplify using `only [Fin.cons_succ, Function.update_of_ne (Fin.succ_ne_zero i), L]`. Establish `hX : 0 ≤ bundleNum (primeOf (S` using `k) x) (Function.update L 0 M) := by`. Use `hNef k Ω N x (d + 1) _ _ hZ fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = 0`.

Substitute `hi` using the available equality. Simplify `hM` using `only [Function.update_self]`. Simplify using `only [Function.update_of_ne hi, L]`. Conclude with `nef_of_isVeryAmple hR Nb hva`. Establish `hY : 0 < bundleNum (primeOf (S` using `k) x) (Function.update L 0 (twistBundle k x 1)) := by`.

Use `hPos k Ω N x (d + 1) _ _ hZ fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Simplify `(isVeryAmple_twistSys_one (S := k) (x := x))` using `only [Function.update_self, twistBundle_toSubSystem]`. Simplify using `only [Function.update_of_ne hi, L]`.

Conclude with `hva`. Rewrite using `[h1, h2]`. Establish `hc` using `mul_pos (sub_pos.mpr hb) hY`. Establish `hq` using `mul_nonneg (Int.natCast_nonneg q) hX`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem LeadingCoeffPos.proof (hR : GenericPointSectionInput.Statement.{u, w})
    (hNef : NefProductNonneg.Statement.{u, w}) (hPos : VeryAmpleProductPos.Statement.{u, w}) :
    LeadingCoeffPos.Statement.{u, w} := by
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
    refine hNef k Ω N x (d + 1) _ _ hZ fun i => ?_
    by_cases hi : i = 0
    · subst hi
      simpa only [Function.update_self] using hM
    · simp only [Function.update_of_ne hi, L]
      exact nef_of_isVeryAmple hR Nb hva

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
