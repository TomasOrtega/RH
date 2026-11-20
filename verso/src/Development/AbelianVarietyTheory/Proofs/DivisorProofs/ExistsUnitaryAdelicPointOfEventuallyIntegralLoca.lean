import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV

noncomputable section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical RestrictedProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
The claim follows from `Subtype.ext (funext h)`.
-/
theorem finiteAdeleRingAway_ext {x y : AfP p} (h : ∀ v : AwayP p, AfP.eval v x = AfP.eval v y) : x = y :=
  Subtype.ext (funext h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(⟨s, hs⟩ : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]), fun _ => rfl⟩`.
-/
theorem exists_afP (s : ∀ v : AwayP p, Qv v)
    (hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), s v ∈ v.1.adicCompletionIntegers ℚ) :
    ∃ t : AfP p, ∀ v, AfP.eval v t = s v :=
  ⟨(⟨s, hs⟩ : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]), fun _ => rfl⟩

variable (G : HTGroup p)

abbrev basA : Module.Basis (Fin (Module.finrank ℚ G.C)) (AfP p) (AfP p ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)

abbrev mapV (v : AwayP p) : AfP p ⊗[ℚ] G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r y`. Simplify using `[basV, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem repr_mapV (v : AwayP p) (z : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (mapV G v z) i = AfP.eval v ((basA G).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp [basV, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/- English proof (translation)
The claim follows from `(basA G).ext_elem fun i => finiteAdeleRingAway_ext fun v => by rw [← repr_mapV, ← repr_mapV, h v]`.
-/
theorem eq_of_mapV {z z' : AfP p ⊗[ℚ] G.C} (h : ∀ v, mapV G v z = mapV G v z') : z = z' :=
  (basA G).ext_elem fun i => finiteAdeleRingAway_ext fun v => by rw [← repr_mapV, ← repr_mapV, h v]

/- English proof (translation)
Use `choose a ha using fun i : Fin (Module.finrank ℚ G.C) => exists_afP (fun v => (basV G v).repr (y v) i) (hy.mono fun v hv => hv i)`. Use `⟨(basA G).equivFun.symm a, fun v => (basV G v).ext_elem fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[repr_mapV, ← ha i v]`. Use `congr 1`. Conclude with `congrFun ((basA G).equivFun.apply_symm_apply a) i`.
-/
theorem exists_of_local (y : ∀ v : AwayP p, Qv v ⊗[ℚ] G.C)
    (hy : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v (y v)) :
    ∃ z : AfP p ⊗[ℚ] G.C, ∀ v, mapV G v z = y v := by
  choose a ha using fun i : Fin (Module.finrank ℚ G.C) =>
    exists_afP (fun v => (basV G v).repr (y v) i) (hy.mono fun v hv => hv i)
  refine ⟨(basA G).equivFun.symm a, fun v => (basV G v).ext_elem fun i => ?_⟩
  rw [repr_mapV, ← ha i v]
  congr 1
  exact congrFun ((basA G).equivFun.apply_symm_apply a) i

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r y`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, starT_tmul]`. Consider the case `add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]`.
-/
theorem mapV_star (v : AwayP p) (z : AfP p ⊗[ℚ] G.C) :
    (starT G.star (Qv v) (mapV G v z)).unop = mapV G v (starT G.star (AfP p) z).unop := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      starT_tmul]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

/- English proof (translation)
Simplify using `[Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem mapV_algebraMap (v : AwayP p) (s : AfP p) :
    mapV G v (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (AfP.eval v s) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Introduce `p _ G h hint`. Take `⟨X, hX⟩` from `exists_of_local G (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ)) : Qv v ⊗[ℚ] G.C)) (hint.mono fun v hv => hv.1)`. Take `⟨Y, hY⟩` from `exists_of_local G (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C)) (hint.mono fun v hv => hv.2.1)`. Take `⟨s, hs⟩` from `exists_afP (fun v => (((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v)) (hint.mono fun v hv => hv.2.2.1)`. Take `⟨s', hs'⟩` from `exists_afP (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v)) (hint.mono fun v hv => hv.2.2.2)`.

Establish `hXY : X * Y = 1` using `eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.mul_inv]`. Establish `hYX : Y * X = 1` using `eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.inv_mul]`. Establish `hss : s * s' = 1` using `finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.mul_inv]`. Establish `hss' : s' * s = 1` using `finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.inv_mul]`. Set `U : (AfP p ⊗[ℚ] G.C)ˣ` to `⟨X, Y, hXY, hYX⟩`.

Set `c : (AfP p)ˣ` to `⟨s, s', hss, hss'⟩`. Establish `hmem : (U, c) ∈ UPts G.star (AfP p)` using `by show X * (starT G.star (AfP p) X).unop = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s`. Use `eq_of_mapV G fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← mapV_star, hX, mapV_algebraMap, hs]`. Conclude with `(h v).2`.

Use `⟨⟨(U, c), hmem⟩, fun v => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hX v`.

Apply `Units.ext` to reduce the goal to its premises. Conclude with `hs v`.
-/
theorem exists_glue : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (h : ∀ v : AwayP p, Gv G v),
    (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), h v ∈ IntV G v) → ∃ g : G.GAf, ∀ v, piV G v g = h v := by
  intro p _ G h hint
  obtain ⟨X, hX⟩ := exists_of_local G
    (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ)) : Qv v ⊗[ℚ] G.C))
    (hint.mono fun v hv => hv.1)
  obtain ⟨Y, hY⟩ := exists_of_local G
    (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))
    (hint.mono fun v hv => hv.2.1)
  obtain ⟨s, hs⟩ := exists_afP (fun v => (((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v))
    (hint.mono fun v hv => hv.2.2.1)
  obtain ⟨s', hs'⟩ := exists_afP (fun v => ((((h v : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v))
    (hint.mono fun v hv => hv.2.2.2)
  have hXY : X * Y = 1 := eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.mul_inv]
  have hYX : Y * X = 1 := eq_of_mapV G fun v => by rw [map_mul, hX, hY, map_one, Units.inv_mul]
  have hss : s * s' = 1 := finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.mul_inv]
  have hss' : s' * s = 1 := finiteAdeleRingAway_ext fun v => by rw [map_mul, hs, hs', map_one, Units.inv_mul]
  let U : (AfP p ⊗[ℚ] G.C)ˣ := ⟨X, Y, hXY, hYX⟩
  let c : (AfP p)ˣ := ⟨s, s', hss, hss'⟩
  have hmem : (U, c) ∈ UPts G.star (AfP p) := by
    show X * (starT G.star (AfP p) X).unop = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s
    refine eq_of_mapV G fun v => ?_
    rw [map_mul, ← mapV_star, hX, mapV_algebraMap, hs]
    exact (h v).2
  refine ⟨⟨(U, c), hmem⟩, fun v => ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    exact hX v
  · apply Units.ext
    exact hs v

end GlobalTheory.OrbFinAf
