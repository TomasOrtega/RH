import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.HeckeAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

def avg (ρ : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) (v : V) : V :=
  ∑ᶠ κ : K ⧸ H, ρ ((κ.out : K) : G) v

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem mem_conj {g : G} {t : K} :
    t ∈ (K.map (MulAut.conj g).toMonoidHom).subgroupOf K ↔ g⁻¹ * (t : G) * g ∈ K := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, e⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    rw [← e]; simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem fix_eq {H : Subgroup K} {v : V} (hv : ∀ h ∈ H, ρ ((h : K) : G) v = v) {a b : K} (hab : (a : K ⧸ H) = b) :
    ρ (a : G) v = ρ (b : G) v := by
  have hm := QuotientGroup.eq.1 hab
  have : (b : G) = a * ((a⁻¹ * b : K) : G) := by simp
  rw [this, map_mul, Module.End.mul_apply, hv _ hm]

end GlobalTheory.HeckeAvg
