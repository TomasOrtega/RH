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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
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
