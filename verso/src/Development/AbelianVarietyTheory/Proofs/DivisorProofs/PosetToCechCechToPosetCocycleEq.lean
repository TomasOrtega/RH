import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

namespace GlobalTheory.CechCmp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem toCech_toPos : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toCech s U hU hinf (toPos s U hU hinf c) = c := by
  intro I _ X R _ s U hU hinf c hc
  funext i j
  rw [toCech_apply, cv_toPos, cv_toPos]
  simp only [unop_op]
  rw [NE.pt_single, NE.pt_single]
  have hk : (NE.pair i j).pt = i ∨ (NE.pair i j).pt = j := by
    have := NE.pt_mem (NE.pair i j)
    rw [NE.set_pair] at this
    simpa using this
  have hi : i ∈ (NE.pair i j).set := by simp [NE.set_pair]
  have hj : j ∈ (NE.pair i j).set := by simp [NE.set_pair]
  have hcap : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge
  rw [GlobalTheory.KS.rsT_rsT (le_inf (cap_le U hi) (cap_le U (NE.pt_mem _))) hcap,
    GlobalTheory.KS.rsT_rsT (le_inf (cap_le U hj) (cap_le U (NE.pt_mem _))) hcap]
  generalize (NE.pair i j).pt = k at hk ⊢
  have hle : U i ⊓ U j ≤ U i ⊓ U j ⊓ U k := by
    refine le_inf le_rfl ?_
    rcases hk with h | h <;> subst h
    exacts [inf_le_left, inf_le_right]
  have h := congrArg (fun t => rsT t (U i ⊓ U j)) (hc i j k)
  simp only [GlobalTheory.KS.rsT_add] at h
  have e₁ : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := inf_le_inf_right _ inf_le_right
  have e₂ : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := inf_le_inf_right _ inf_le_left
  rw [GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_self, GlobalTheory.KS.rsT_rsT e₁ hle, GlobalTheory.KS.rsT_rsT e₂ hle] at h
  rw [← h]
  abel

end GlobalTheory.CechCmp
