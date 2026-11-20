import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Closed

/- English proof (translation)
Establish `hcot : ∀ n, Subsingleton (Cot O (G.A n))` using `fun n => ⟨fun a b => by`. Establish `h` using `hp.pow n`. Establish `key : ∀ c : Cot O (G.A n), c = 0` using `fun c => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, h.val_inv_mul, one_smul]`.

Use `_ = 0 := by rw [G.pow_smul_cot n c, smul_zero]`. Rewrite using `[key a, key b]⟩`. Use `⟨⟨fun a b => Subtype.ext (funext fun n => (hcot n).elim _ _)⟩, fun n => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `y`. Conclude with `⟨0, (hcot n).elim _ _⟩`.

Introduce `w`. Establish `h` using `hp.pow n`. Use `⟨fun _ => ⟨((h.unit⁻¹ : Oˣ) : O) • w, ?_⟩, fun _ => by simp⟩` and prove the remaining obligations. Rewrite using `[smul_smul, h.mul_val_inv, one_smul]`. Introduce `x w a _`.

Establish `hs : Subsingleton (O ⧸ Ideal.span {(p : O) ^ n})` using `Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 (hp.pow n))`. Conclude with `hs.elim _ _`.
-/
theorem isOmega_zero_of_isUnit {O : Type} [CommRing O] {p : ℕ} [Fact p.Prime] {A : Over (Sp O)} [GrpObj A]
    {G : PDivGroup p O} (θ : TorsionMap A G) (hp : IsUnit (p : O)) : Subsingleton G.omega ∧ θ.IsOmega 0 := by
  have hcot : ∀ n, Subsingleton (Cot O (G.A n)) := fun n => ⟨fun a b => by
    have h := hp.pow n
    have key : ∀ c : Cot O (G.A n), c = 0 := fun c => by
      calc c = ((h.unit⁻¹ : Oˣ) : O) • (((p : O) ^ n) • c) := by
            rw [smul_smul, h.val_inv_mul, one_smul]
        _ = 0 := by rw [G.pow_smul_cot n c, smul_zero]
    rw [key a, key b]⟩
  refine ⟨⟨fun a b => Subtype.ext (funext fun n => (hcot n).elim _ _)⟩, fun n => ⟨?_, ?_, ?_⟩⟩
  · intro y
    exact ⟨0, (hcot n).elim _ _⟩
  · intro w
    have h := hp.pow n
    refine ⟨fun _ => ⟨((h.unit⁻¹ : Oˣ) : O) • w, ?_⟩, fun _ => by simp⟩
    rw [smul_smul, h.mul_val_inv, one_smul]
  · intro x w a _
    have hs : Subsingleton (O ⧸ Ideal.span {(p : O) ^ n}) :=
      Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 (hp.pow n))
    exact hs.elim _ _

end GlobalTheory.GroupBplus.Closed
