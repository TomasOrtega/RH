import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong

noncomputable section

namespace GlobalTheory.Cong.OpPoly

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

def opHom (v : V) : (G →₀ ℂ) →+ V :=
  Finsupp.liftAddHom fun g => (smulAddHom ℂ V).flip (ρ g v)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem opHom_apply (v : V) (F : G →₀ ℂ) : opHom ρ v F = opOf ρ F v := by
  rw [opHom, Finsupp.liftAddHom_apply, opOf]
  exact Finsupp.sum_congr fun g _ => rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem opOf_single (g : G) (c : ℂ) (v : V) : opOf ρ (Finsupp.single g c) v = c • ρ g v := by
  simp [opOf, Finsupp.sum_single_index]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem opOf_add (F F' : G →₀ ℂ) (v : V) : opOf ρ (F + F') v = opOf ρ F v + opOf ρ F' v := by
  simp only [← opHom_apply, map_add]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem opOf_smul (F : G →₀ ℂ) (c : ℂ) (v : V) : opOf ρ F (c • v) = c • opOf ρ F v := by
  simp [opOf, Finsupp.smul_sum, smul_comm c]

def conv (F f : G →₀ ℂ) : G →₀ ℂ :=
  F.sum fun g a => f.sum fun h b => Finsupp.single (g * h) (a * b)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem opOf_conv (F f : G →₀ ℂ) (v : V) : opOf ρ (conv F f) v = opOf ρ F (opOf ρ f v) := by
  rw [← opHom_apply]
  simp only [conv, Finsupp.sum, map_sum, opHom_apply, opOf_single]
  simp only [opOf, Finsupp.sum, map_sum, map_smul, Finset.smul_sum, mul_smul, map_mul, Module.End.mul_apply]

end GlobalTheory.Cong.OpPoly
