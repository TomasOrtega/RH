import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

noncomputable section

namespace GlobalTheory.UPel.HeckeImage

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {S : Scheme.{0}}

/- English proof (translation)
Establish `h` using `o.eta_add 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)`.
-/
theorem eta_zero {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

/- English proof (translation)
Apply `eq_inv_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← o.eta_add, add_neg_cancel, eta_zero]`.
-/
theorem eta_neg {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (x : D.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, eta_zero]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [eta_zero]`. Consider the case `succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]`.
-/
theorem eta_nsmul {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (m : ℕ) (x : D.La) :
    o.eta (m • x) = o.eta x ^ m := by
  induction m with
  | zero => simp [eta_zero]
  | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

def sub {D : Datum F} {p N' : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s) (g : IntSim D p) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ a, h = o.eta ((N' / g.k) • g.g N' a)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add, smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨a, rfl⟩`.
-/
theorem mem_sub {D : Datum F} {p N' : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s) (g : IntSim D p) (a : D.La) :
    o.eta ((N' / g.k) • g.g N' a) ∈ sub o g := ⟨a, rfl⟩

end GlobalTheory.UPel.HeckeImage
