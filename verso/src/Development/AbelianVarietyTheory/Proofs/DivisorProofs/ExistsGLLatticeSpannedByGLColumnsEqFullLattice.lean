import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

/- English proof (translation)
Introduce `E _ _ _ w K e a B b L hL`. Take `⟨hfg, hspan⟩` from `hL`. Use `haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg`. Use `haveI : NoZeroSMulDivisors K.O B.A := ⟨fun {r x} h => by`. Rewrite `h` using `[← algebraMap_smul K.E r x]`.

Break down `smul_eq_zero.mp h with h | h` into its components or cases. Use the proof step `left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)`. Use `right`. Conclude with `h⟩`. Use `haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'`.

Set `y` to `Module.Free.chooseBasis K.O L`. Set `v : Module.Free.ChooseBasisIndex K.O L → B.A` to `fun i => (y i : B.A)`. Establish `hli : LinearIndependent K.O v` using `y.linearIndependent.map' L.subtype (Submodule.ker_subtype L)`. Establish `hliE : LinearIndependent K.E v` using `(LinearIndependent.iff_fractionRing K.O K.E).mp hli`. Establish `hLv : Submodule.span K.O (Set.range v) = L`.

Establish `: Set.range v = L.subtype '' Set.range y`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, y.span_eq, Submodule.map_subtype_top]`. Establish `hspE : Submodule.span K.E (Set.range v) = ⊤`.

Rewrite using `[← Submodule.span_span_of_tower K.O K.E, hLv]`. Conclude with `hspan`. Set `c` to `Module.Basis.mk hliE hspE.ge`. Set `c'` to `c.reindex (c.indexEquiv b)`. Set `U : (Matrix (Fin a) (Fin a) K.E)ˣ` to `⟨b.toMatrix c', c'.toMatrix b, b.toMatrix_mul_toMatrix_flip c', c'.toMatrix_mul_toMatrix_flip b⟩`.

Use `⟨Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U, ?_⟩` and prove the remaining obligations. Rewrite using `[latOf_eq, ← hLv]`. Establish `hcol : ∀ j, (ofCrd e b fun i => (Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U).val i j) = c' j`. Introduce `j`. Rewrite using `[← ofCrd_crd e b (c' j)]`.

Use `congr 1`. Simplify using `only [hcol]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, rfl⟩`. Use `⟨(c.indexEquiv b).symm j, ?_⟩` and prove the remaining obligations. Simplify using `[c', c, v]`. Introduce and unpack `⟨i, rfl⟩`.

Use `⟨c.indexEquiv b i, ?_⟩` and prove the remaining obligations. Simplify using `[c', c, v]`.
-/
theorem exists_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  intro E _ _ _ w K e a B b L hL
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := ⟨fun {r x} h => by
    rw [← algebraMap_smul K.E r x] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h⟩
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  let y := Module.Free.chooseBasis K.O L
  let v : Module.Free.ChooseBasisIndex K.O L → B.A := fun i => (y i : B.A)
  have hli : LinearIndependent K.O v := y.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent K.E v := (LinearIndependent.iff_fractionRing K.O K.E).mp hli
  have hLv : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range y := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, y.span_eq, Submodule.map_subtype_top]
  have hspE : Submodule.span K.E (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower K.O K.E, hLv]; exact hspan
  let c := Module.Basis.mk hliE hspE.ge
  let c' := c.reindex (c.indexEquiv b)
  let U : (Matrix (Fin a) (Fin a) K.E)ˣ :=
    ⟨b.toMatrix c', c'.toMatrix b, b.toMatrix_mul_toMatrix_flip c', c'.toMatrix_mul_toMatrix_flip b⟩
  refine ⟨Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U, ?_⟩
  rw [latOf_eq, ← hLv]
  have hcol : ∀ j, (ofCrd e b fun i =>
      (Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U).val i j) = c' j := by
    intro j
    rw [← ofCrd_crd e b (c' j)]
    congr 1
  simp only [hcol]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨(c.indexEquiv b).symm j, ?_⟩
    simp [c', c, v]
  · rintro ⟨i, rfl⟩
    refine ⟨c.indexEquiv b i, ?_⟩
    simp [c', c, v]

end GlobalTheory.TwOrbLat
