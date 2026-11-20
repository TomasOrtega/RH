import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.MultScale

variable {p : ℕ} [Fact p.Prime]

def EFA (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (D.EF.baseChange ℚ).baseChange (AfP p)

/- English proof (translation)
Simplify using `only [EFA, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one]`. Rewrite using `[Algebra.smul_def, zsmul_eq_mul, _root_.mul_one, map_intCast, mul_comm]`.
-/
theorem EFA_tmul (D : Datum p) (a a' : AfP p) (x x' : D.La) :
    EFA D (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) (a' ⊗ₜ ((1 : ℚ) ⊗ₜ x')) = a * a' * ((D.EF x x' : ℤ) : AfP p) := by
  simp only [EFA, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one]
  rw [Algebra.smul_def, zsmul_eq_mul, _root_.mul_one, map_intCast, mul_comm]

/- English proof (translation)
Rewrite using `[inAf, inAf, EFA_tmul, _root_.one_mul, _root_.one_mul]`.
-/
theorem EFA_inAf (D : Datum p) (x y : D.La) : EFA D (inAf D x) (inAf D y) = ((D.EF x y : ℤ) : AfP p) := by
  rw [inAf, inAf, EFA_tmul, _root_.one_mul, _root_.one_mul]

/- English proof (translation)
Introduce `v` and use `by rw [map_intCast]; exact intCast_mem _ z`.
-/
theorem isIntAf_intCast (z : ℤ) : IsIntAf ((z : AfP p)) := fun v => by
  rw [map_intCast]; exact intCast_mem _ z

/- English proof (translation)
Introduce `v` and use `by rw [map_add]; exact add_mem (ha v) (hb v)`.
-/
theorem isIntAf_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

/- English proof (translation)
Introduce `v` and use `by rw [map_neg]; exact neg_mem (ha v)`.
-/
theorem isIntAf_neg {a : AfP p} (ha : IsIntAf a) : IsIntAf (-a) := fun v => by
  rw [map_neg]; exact neg_mem (ha v)

/- English proof (translation)
Introduce `v` and use `by rw [map_mul]; exact mul_mem (ha v) (hb v)`.
-/
theorem isIntAf_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

/- English proof (translation)
Simplify using `using isIntAf_intCast (p := p) 0`.
-/
theorem isIntAf_zero : IsIntAf (0 : AfP p) := by simpa using isIntAf_intCast (p := p) 0

/- English proof (translation)
Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem v hv`. Take `⟨a, x, ha, rfl⟩` from `hv`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`.

Take `⟨a', x', ha', rfl⟩` from `hw`. Rewrite using `[EFA_tmul]`. Conclude with `isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast _)`. Consider the case `zero => simpa using isIntAf_zero`. Consider the case `add u u' _ _ h h' => rw [map_add]`.

Conclude with `isIntAf_add h h'`. Consider the case `neg u _ h => rw [map_neg]`. Conclude with `isIntAf_neg h`. Consider the case `zero => simpa using isIntAf_zero`. Consider the case `add u u' _ _ h h' => rw [map_add, LinearMap.add_apply]`.

Conclude with `isIntAf_add h h'`. Consider the case `neg u _ h => rw [map_neg, LinearMap.neg_apply]`. Conclude with `isIntAf_neg h`.
-/
theorem isIntAf_EFA (D : Datum p) {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    IsIntAf (EFA D v w) := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, x, ha, rfl⟩ := hv
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a', x', ha', rfl⟩ := hw
      rw [EFA_tmul]; exact isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast _)
    | zero => simpa using isIntAf_zero
    | add u u' _ _ h h' => rw [map_add]; exact isIntAf_add h h'
    | neg u _ h => rw [map_neg]; exact isIntAf_neg h
  | zero => simpa using isIntAf_zero
  | add u u' _ _ h h' => rw [map_add, LinearMap.add_apply]; exact isIntAf_add h h'
  | neg u _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

section Sim

variable {D : Datum p} {G : HTGroup p}

/- English proof (translation)
Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add v v' hv hv' => simp only [map_add, LinearMap.add_apply, hv, hv']`. Consider the case `tmul a x`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add w w' hw hw' => simp only [map_add, hw, hw']`. Consider the case `tmul a' y => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]`.
-/
theorem bc_adj {V : Type} [AddCommGroup V] [Module ℚ V] (A : Type) [CommRing A] [Algebra ℚ A]
    (B : LinearMap.BilinForm ℚ V) (f g : Module.End ℚ V) (h : ∀ v w, B (f v) w = B v (g w)) (v w : A ⊗[ℚ] V) :
    B.baseChange A (f.baseChange A v) w = B.baseChange A v (g.baseChange A w) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' hv hv' => simp only [map_add, LinearMap.add_apply, hv, hv']
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul a' y => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Use `first`. Consider the case `exact Algebra.TensorProduct.lift_tmul _ _ _ r c`. Consider the case `(erw [Algebra.TensorProduct.lift_tmul]; rfl)`. Consider the case `rfl`.
-/
theorem actOn_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r : R) (c : C) :
    actOn rep R (r ⊗ₜ c) = r • (rep c).baseChange R := by
  rw [Algebra.smul_def]
  first
  | exact Algebra.TensorProduct.lift_tmul _ _ _ r c
  | (erw [Algebra.TensorProduct.lift_tmul]; rfl)
  | rfl

/- English proof (translation)
Proceed by induction on `X using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add X X' hX hX' => simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, hX, hX']`. Consider the case `tmul r c`. Rewrite using `[starT_tmul, actOn_tmul, actOn_tmul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, map_smul]`.

Use `congr 1`. Conclude with `bc_adj (AfP p) (D.EF.baseChange ℚ) (L.rep c) (L.rep (sh G c)) (fun v w => L.adj c v w) v w`.
-/
theorem EFA_actOn (L : Link D G) (X : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (actOn L.rep (AfP p) X v) w = EFA D v (actOn L.rep (AfP p) (starT G.star (AfP p) X).unop w) := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | add X X' hX hX' => simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, hX, hX']
  | tmul r c =>
    rw [starT_tmul, actOn_tmul, actOn_tmul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      LinearMap.smul_apply, map_smul]
    congr 1
    exact bc_adj (AfP p) (D.EF.baseChange ℚ) (L.rep c) (L.rep (sh G c)) (fun v w => L.adj c v w) v w

/- English proof (translation)
Take `⟨⟨u, c⟩, hmem⟩` from `g`. Establish `h1 : (u : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) u).unop = algebraMap (AfP p) _ (c : AfP p)` using `hmem`. Establish `h2 : (starT G.star (AfP p) u).unop * u = algebraMap (AfP p) _ (c : AfP p)`. Establish `e : (starT G.star (AfP p) u).unop = ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * algebraMap (AfP p) _ (c : AfP p)`. Rewrite using `[← h1, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]`.

Rewrite using `[e, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]`. Establish `hg : ∀ z, L.actG ⟨⟨u, c⟩, hmem⟩ z = actOn L.rep (AfP p) (u : AfP p ⊗[ℚ] G.C) z` using `fun z => rfl`. Rewrite using `[hg, hg, EFA_actOn, ← Module.End.mul_apply, ← map_mul, h2, AlgHom.commutes, Module.algebraMap_end_apply, map_smul, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem EFA_actG (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (L.actG g v) (L.actG g w) = ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) * EFA D v w := by
  obtain ⟨⟨u, c⟩, hmem⟩ := g
  have h1 : (u : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) u).unop = algebraMap (AfP p) _ (c : AfP p) := hmem
  have h2 : (starT G.star (AfP p) u).unop * u = algebraMap (AfP p) _ (c : AfP p) := by
    have e : (starT G.star (AfP p) u).unop = ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        algebraMap (AfP p) _ (c : AfP p) := by
      rw [← h1, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [e, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hg : ∀ z, L.actG ⟨⟨u, c⟩, hmem⟩ z = actOn L.rep (AfP p) (u : AfP p ⊗[ℚ] G.C) z := fun z => rfl
  rw [hg, hg, EFA_actOn, ← Module.End.mul_apply, ← map_mul, h2, AlgHom.commutes, Module.algebraMap_end_apply,
    map_smul, smul_eq_mul]
  rfl

end Sim

/- English proof (translation)
Simplify using `using isIntAf_intCast (p := p) 1`.
-/
theorem isIntAf_one : IsIntAf (1 : AfP p) := by simpa using isIntAf_intCast (p := p) 1

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, z, isIntAf_one, rfl⟩`.
-/
theorem inAf_mem (D : Datum p) (z : D.La) : inAf D z ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, z, isIntAf_one, rfl⟩

end GlobalTheory.LKGeo.MultScale

namespace GlobalTheory.LKGeo

end GlobalTheory.LKGeo
