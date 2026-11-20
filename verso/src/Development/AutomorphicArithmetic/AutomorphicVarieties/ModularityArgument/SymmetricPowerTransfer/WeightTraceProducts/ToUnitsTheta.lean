import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.WtMain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex

noncomputable section

open UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Wt

variable {K I : Type} [Field K] [Fintype I] {Δ : K} (em : I → Lsq K Δ →+* ℂ) (j : ℕ)

def cG : Representation ℂ (U3 Δ) (VG I j) := (WG em j).comp Unitary.toUnits

def cD (n : ℕ) (e : ℤ) : Representation ℂ (DX Δ) (VD I n) := (WD em n e).comp (DX Δ).subtype

def cS : Representation ℂ (SU Δ) (VD I j) := (cD em j 0).comp (SU Δ).subtype

abbrev cK : Representation ℂ (DX Δ) (VD I (2 * j + 1)) := cD em (2 * j + 1) (-((j : ℤ) + 1))

def ch (τ : K) : ℂ := chi em j (algebraMap K _ τ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem toUnits_theta (g : U3 Δ) :
    (Unitary.toUnits (theta Δ g) : GL (Fin 3) (Lsq K Δ)) = invT _ 3 (Unitary.toUnits g) := by
  exact Units.ext (Matrix.ext fun _ _ => rfl)

variable {j}

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cG_int (hj : 1 ≤ j) (γ : U3 Δ) (v : VG I j) : thG I j (cG em j γ v) = cG em j (theta Δ γ) (thG I j v) := by
  have := LinearMap.congr_fun ((wtMain _ I em j hj).th_rep (Unitary.toUnits γ)) v
  rw [← toUnits_theta] at this
  exact this

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cG_tr (hj : 1 ≤ j) (δ : U3 Δ) (τ : K) (h : HasTau δ τ) : LinearMap.trace ℂ _ (cG em j δ ∘ₗ thG I j) = ch em j τ := by
  refine (wtMain _ I em j hj).twine (Unitary.toUnits δ) _ ?_
  rw [← toUnits_theta, ← map_mul]
  exact h

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cS_tr (hj : 1 ≤ j) (γ : SU Δ) (τ : K) (h : HasTr (γ : DX Δ) τ) : LinearMap.trace ℂ _ (cS em j γ) = ch em j τ := by
  have := (wtMain _ I em j hj).stable 0 ((γ : DX Δ) : GL (Fin 2) (Lsq K Δ)) h.1
  rw [h.2] at this
  exact this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cK_tr (hj : 1 ≤ j) (g : DX Δ) (τ : K) (h : (mt g).trace = algebraMap K _ (2 + τ)) (h' : (mt g).det = algebraMap K _ (2 + τ)) :
    LinearMap.trace ℂ _ (cK em j g) = ch em j τ :=
  (wtMain _ I em j hj).kappa g _ (by rw [h, map_add, map_ofNat]) (by rw [h', map_add, map_ofNat])

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem cK_scal (hj : 1 ≤ j) (z : Kˣ) (s : DX Δ) (h : IsScal z s) (v : VD I (2 * j + 1)) :
    cK em j s v = (∏ w, em w (algebraMap K _ (z : K)))⁻¹ • v := by
  have e : (s : GL (Fin 2) (Lsq K Δ)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z) := Units.ext h
  have := LinearMap.congr_fun ((wtMain _ I em j hj).scalD (2 * j + 1) (-((j : ℤ) + 1)) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z)) v
  rw [← e, show ((2 * j + 1 : ℕ) : ℤ) + 2 * -((j : ℤ) + 1) = -1 by push_cast; ring] at this
  rw [← Finset.prod_inv_distrib]
  simp only [zpow_neg_one] at this
  exact this

end UpperTheory.V.Z.Sym.Wt

end
