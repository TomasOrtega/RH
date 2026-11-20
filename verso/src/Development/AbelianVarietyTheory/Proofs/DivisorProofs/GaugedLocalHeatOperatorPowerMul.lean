import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatGaugeCoverOpenLeHeatOperatorOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresBasicOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

open GlobalTheory.KS (rsT_mul rsT_one rsT_sum rsT_sub rsT_add rsT_constFn rsT_rsT)
open GlobalTheory.HeatGlue (IsDer isDer_of_isField field_rsT ringOp_conj)

/- English proof (translation)
Introduce `R _ G _ _ n X m m₁ L dd D h₁ e hdd c hc p k O hO f`. Establish `hW1 : W m h₁ p ≤ h₁.W p.1` using `heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p`. Establish `hdF : IsField (h₁.W p.1) (h₁.d p.1)` using `(h₁.lift p.1).1`. Establish `hd : IsDer (h₁.d p.1 O)` using `isDer_of_isField hdF (hO.trans hW1)`. Establish `hddO : ∀ a, IsDer (dd a O)` using `fun a => isDer_of_isField (hdd a) le_top`.

Establish `hg : rsT (gU m h₁ e p).val O * rsT (gU m h₁ e p)⁻¹.val O = 1`. Rewrite using `[← rsT_mul, Units.mul_inv, rsT_one hO]`. Use `set g := rsT (gU m h₁ e p).val O with hgdef`. Use `set gi := rsT (gU m h₁ e p)⁻¹.val O with hgidef`. Establish `eL : ∀ a, rsT (gL m h₁ e a p) O = dd a O g * gi` using `fun a => by`.

Rewrite using `[gL, rsT_mul, field_rsT (hdd a) le_top hO]`. Establish `eE : rsT (gE m h₁ e p) O = h₁.d p.1 O g * gi`. Rewrite using `[gE, rsT_mul, field_rsT hdF hW1 hO]`. Establish `eY : ∀ a, rsT (gY m h₁ e a p) O = ∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi)` using `fun a => by`. Simplify using `only [gY, rsT_sum, rsT_mul, rsT_constFn G.hom hO, eL]`.

Establish `eP : rsT (gP m h₁ e c p) O = rsT (h₁.p p.1) O - h₁.d p.1 O g * gi - constFn G.hom O c * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi)`. Simplify using `only [gP, rsT_sub, rsT_mul, rsT_sum, rsT_constFn G.hom hO, eL, eE, rsT_rsT hW1 hO]`. Establish `eDL : ∀ a b, rsT (dd a (W m h₁ p) (gL m h₁ e b p)) O = dd a O (dd b O g * gi)` using `fun a b => by`. Rewrite using `[← field_rsT (hdd a) le_top hO, eL]`. Establish `eP' : rsT (gP' m h₁ e c p) O = rsT (h₁.p' p.1) O + constFn G.hom O c * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * dd a O (dd b O g * gi) - ∑ a, constFn G.hom O (h₁.u a) * (dd a O g * gi)`.

Simplify using `only [gP', rsT_sub, rsT_add, rsT_mul, rsT_sum, rsT_constFn G.hom hO, eL, eDL, rsT_rsT hW1 hO]`. Establish `hcO : 2 * constFn G.hom O c = 1`. Use `congrArg (constFn G.hom O) (show c + c = 1 by linear_combination hc)` as an intermediate fact. Simplify using `only [constFn, map_add, map_one] at this ⊢`. Take the linear combination `this`.

Establish `hs : ∀ a b, (h₁.Θ.map (constFn G.hom O)) a b = (h₁.Θ.map (constFn G.hom O)) b a` using `fun a b => by`. Simplify using `only [Matrix.map_apply]`. Rewrite using `[show h₁.Θ a b = h₁.Θᵀ b a from rfl, h₁.symm]`. Establish `key` using `ringOp_conj hd hddO hs (fun a => constFn G.hom O (h₁.u a)) (rsT (h₁.p p.1) O) (rsT (h₁.p' p.1) O) hg k f`. Simplify using `only [ringOp, Matrix.map_apply] at key`.

Establish `S1 : ∑ a, (∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi)) * dd a O (g ^ k * f) = g ^ k * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi) * dd a O f + (k : Γ(G.left, O)) * g ^ k * f * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi)`. Simplify using `only [(hddO _).pow_mul hg, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [op, gD, eY, eP, eP']`.

Take the linear combination `key + 2 * (k : Γ(G.left, O)) * S1 - (k : Γ(G.left, O)) * g ^ k * f * ((k : Γ(G.left, O)) * (∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi)) - ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * dd a O (dd b O g * gi)) * hcO`.
-/
theorem op_gauged : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), (∀ a, IsField ⊤ (dd a)) → ∀ (c : R), 2 * c = 1 → ∀ (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p → ∀ (f : Γ(G.left, O)), op G dd h₁.Θ h₁.u (GlobalTheory.Heat.Gauge.gD m h₁ e p) (GlobalTheory.Heat.Gauge.gP m h₁ e c p) (GlobalTheory.Heat.Gauge.gP' m h₁ e c p) k O (rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * f) = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hdd c hc p k O hO f
  have hW1 : W m h₁ p ≤ h₁.W p.1 := heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p
  have hdF : IsField (h₁.W p.1) (h₁.d p.1) := (h₁.lift p.1).1
  have hd : IsDer (h₁.d p.1 O) := isDer_of_isField hdF (hO.trans hW1)
  have hddO : ∀ a, IsDer (dd a O) := fun a => isDer_of_isField (hdd a) le_top
  have hg : rsT (gU m h₁ e p).val O * rsT (gU m h₁ e p)⁻¹.val O = 1 := by
    rw [← rsT_mul, Units.mul_inv, rsT_one hO]
  set g := rsT (gU m h₁ e p).val O with hgdef
  set gi := rsT (gU m h₁ e p)⁻¹.val O with hgidef
  have eL : ∀ a, rsT (gL m h₁ e a p) O = dd a O g * gi := fun a => by
    rw [gL, rsT_mul, field_rsT (hdd a) le_top hO]
  have eE : rsT (gE m h₁ e p) O = h₁.d p.1 O g * gi := by
    rw [gE, rsT_mul, field_rsT hdF hW1 hO]
  have eY : ∀ a, rsT (gY m h₁ e a p) O = ∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi) := fun a => by
    simp only [gY, rsT_sum, rsT_mul, rsT_constFn G.hom hO, eL]
  have eP : rsT (gP m h₁ e c p) O = rsT (h₁.p p.1) O - h₁.d p.1 O g * gi -
      constFn G.hom O c * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi) := by
    simp only [gP, rsT_sub, rsT_mul, rsT_sum, rsT_constFn G.hom hO, eL, eE, rsT_rsT hW1 hO]
  have eDL : ∀ a b, rsT (dd a (W m h₁ p) (gL m h₁ e b p)) O = dd a O (dd b O g * gi) := fun a b => by
    rw [← field_rsT (hdd a) le_top hO, eL]
  have eP' : rsT (gP' m h₁ e c p) O = rsT (h₁.p' p.1) O +
      constFn G.hom O c * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * dd a O (dd b O g * gi) -
      ∑ a, constFn G.hom O (h₁.u a) * (dd a O g * gi) := by
    simp only [gP', rsT_sub, rsT_add, rsT_mul, rsT_sum, rsT_constFn G.hom hO, eL, eDL, rsT_rsT hW1 hO]
  have hcO : 2 * constFn G.hom O c = 1 := by
    have := congrArg (constFn G.hom O) (show c + c = 1 by linear_combination hc)
    simp only [constFn, map_add, map_one] at this ⊢
    linear_combination this
  have hs : ∀ a b, (h₁.Θ.map (constFn G.hom O)) a b = (h₁.Θ.map (constFn G.hom O)) b a := fun a b => by
    simp only [Matrix.map_apply]
    rw [show h₁.Θ a b = h₁.Θᵀ b a from rfl, h₁.symm]
  have key := ringOp_conj hd hddO hs (fun a => constFn G.hom O (h₁.u a)) (rsT (h₁.p p.1) O) (rsT (h₁.p' p.1) O) hg k f
  simp only [ringOp, Matrix.map_apply] at key
  have S1 : ∑ a, (∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi)) * dd a O (g ^ k * f) =
      g ^ k * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi) * dd a O f +
      (k : Γ(G.left, O)) * g ^ k * f * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi) := by
    simp only [(hddO _).pow_mul hg, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [op, gD, eY, eP, eP']
  linear_combination key + 2 * (k : Γ(G.left, O)) * S1 -
    (k : Γ(G.left, O)) * g ^ k * f * ((k : Γ(G.left, O)) *
      (∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi)) -
      ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * dd a O (dd b O g * gi)) * hcO

end GlobalTheory.Heat.Gauge
