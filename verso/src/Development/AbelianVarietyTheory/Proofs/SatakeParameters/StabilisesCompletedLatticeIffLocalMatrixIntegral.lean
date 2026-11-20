import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.StabLoc

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

/- English proof (translation)
Establish `key : ∀ (A : Matrix n n R), (∀ i j, A i j ∈ O) → ∀ y : n → R, (∀ i, y i ∈ O) → ∀ i, A.mulVec y i ∈ O` using `fun A hA y hy i => O.sum_mem fun j _ => O.mul_mem (hA i j) (hy j)`. Establish `hs : ∀ j i : n, (Pi.single j (1 : R) : n → R) i ∈ O`. Introduce `j i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[O.one_mem]`. Simplify using `[h, O.zero_mem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩ y`. Use `⟨key _ (fun i j => (k.1 i j).2) y, fun h => ?_⟩` and prove the remaining obligations.

Use `key (Formalism.UG.bc (n := n) O.subtype k⁻¹).1 (fun i j => ((k⁻¹).1 i j).2) _ h` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis. Introduce `h`. Establish `h1 : ∀ i j, m.1 i j ∈ O` using `fun i j => by`. Simplify using `using (h (Pi.single j 1)).1 (hs j) i`.

Establish `h2 : ∀ i j, (m⁻¹).1 i j ∈ O` using `fun i j => by`. Use `(h ((m⁻¹).1.mulVec (Pi.single j 1))).2 (by` as an intermediate fact. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Conclude with `hs j) i`. Rewrite `this` using `[Matrix.mulVec_single_one]`. Then use the resulting hypothesis.

Set `A : Matrix n n O` to `Matrix.of fun i j => ⟨m.1 i j, h1 i j⟩`. Set `B : Matrix n n O` to `Matrix.of fun i j => ⟨(m⁻¹).1 i j, h2 i j⟩`. Establish `hA : O.subtype.mapMatrix A = m.1` using `rfl`. Establish `hB : O.subtype.mapMatrix B = (m⁻¹).1` using `rfl`. Establish `hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n R)` using `fun X Y hXY => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hXY i) j)`.

Use `⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext rfl⟩` and prove the remaining obligations. Rewrite using `[map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Rewrite using `[map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]`.
-/
theorem mem_range_iff (m : GL n R) :
    m ∈ (Formalism.UG.bc (n := n) O.subtype).range ↔
      ∀ y : n → R, (∀ i, y i ∈ O) ↔ ∀ i, m.1.mulVec y i ∈ O := by
  have key : ∀ (A : Matrix n n R), (∀ i j, A i j ∈ O) → ∀ y : n → R, (∀ i, y i ∈ O) →
      ∀ i, A.mulVec y i ∈ O := fun A hA y hy i =>
    O.sum_mem fun j _ => O.mul_mem (hA i j) (hy j)
  have hs : ∀ j i : n, (Pi.single j (1 : R) : n → R) i ∈ O := by
    intro j i
    by_cases h : i = j
    · subst h; simp [O.one_mem]
    · simp [h, O.zero_mem]
  constructor
  · rintro ⟨k, rfl⟩ y
    refine ⟨key _ (fun i j => (k.1 i j).2) y, fun h => ?_⟩
    have := key (Formalism.UG.bc (n := n) O.subtype k⁻¹).1 (fun i j => ((k⁻¹).1 i j).2) _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at this
  · intro h
    have h1 : ∀ i j, m.1 i j ∈ O := fun i j => by
      simpa using (h (Pi.single j 1)).1 (hs j) i
    have h2 : ∀ i j, (m⁻¹).1 i j ∈ O := fun i j => by
      have := (h ((m⁻¹).1.mulVec (Pi.single j 1))).2 (by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        exact hs j) i
      rwa [Matrix.mulVec_single_one] at this
    let A : Matrix n n O := Matrix.of fun i j => ⟨m.1 i j, h1 i j⟩
    let B : Matrix n n O := Matrix.of fun i j => ⟨(m⁻¹).1 i j, h2 i j⟩
    have hA : O.subtype.mapMatrix A = m.1 := rfl
    have hB : O.subtype.mapMatrix B = (m⁻¹).1 := rfl
    have hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n R) :=
      fun X Y hXY => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hXY i) j)
    refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]

end Ring

/- English proof (translation)
Establish `hev : ∀ w (y : Fin V.rank → Af F ⊗[F] E), (fun i => evF E w ((finMat hc.sig V.gram g).mulVec y i)) = (locMat hc V w g).1.mulVec fun i => evF E w (y i)` using `fun w y => by`. Use function extensionality and compare the values at `i`. Rewrite using `[locMat_val]`. Conclude with `RingHom.map_mulVec (evF E w) _ y i`. Establish `hloc : Stab hc V g ↔ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F` using `F) V v ↔ (locMat hc V v g).1.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by`.

Prove the components needed by the constructor for the conclusion. Introduce `hs x`. Establish `hx : ∀ w, w ≠ v → (fun i => evF E w (sgT E v (x i))) = 0` using `fun w hw =>`. Use function extensionality and compare the values at `fun i => evF_sgT_ne hw _`. Establish `hxv : (fun i => evF E v (sgT E v (x i))) = x` using `funext fun i => evF_sgT_self v _`.

Use `hs fun i => sgT E v (x i)` as an intermediate fact. Rewrite `this` using `[mem_lamHat_iff, mem_lamHat_iff]`. Simplify using `only [hev] at this`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Establish `h1` using `this.1 (fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[hxv]`. Conclude with `h0`.

Rewrite using `[hx w hw]`. Conclude with `zero_mem _) v`. Rewrite `h1` using `[hxv]`. Then use the resulting hypothesis. Introduce `h0`. Establish `h1` using `this.2 (fun w => by`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[hxv]`. Conclude with `h0`. Rewrite using `[hx w hw, Matrix.mulVec_zero]`.

Conclude with `zero_mem _) v`. Rewrite `h1` using `[hxv]`. Then use the resulting hypothesis. Introduce `hs y`. Rewrite using `[mem_lamHat_iff, mem_lamHat_iff]`. Use `forall_congr' fun w => ?_` and prove the remaining obligations.

Rewrite using `[hev]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Conclude with `hs _`. Rewrite using `[hg w hw, Units.val_one, Matrix.one_mulVec]`.

Rewrite using `[hloc, mem_range_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hs y`. Use `hs (h.1.mulVec y)` as an intermediate fact. Rewrite `this` using `[hh, hh, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.

Rewrite using `[Units.val_mul, Units.val_mul]` and apply the resulting hypothesis. Introduce `hs x`. Use `hs ((h⁻¹).1.mulVec x)` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec]`. Rewrite using `[hh, hh]`.

Conclude with `this`.
-/
theorem stab_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E))
    (hh : IsFrameAt V v h) (g : HA (AF F) hc.sig V.gram) (hg : ∀ w, w ≠ v → locMat hc V w g = 1) :
    Stab hc V g ↔
      h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range := by
  have hev : ∀ w (y : Fin V.rank → Af F ⊗[F] E),
      (fun i => evF E w ((finMat hc.sig V.gram g).mulVec y i)) =
        (locMat hc V w g).1.mulVec fun i => evF E w (y i) := fun w y => by
    funext i
    rw [locMat_val]
    exact RingHom.map_mulVec (evF E w) _ y i
  have hloc : Stab hc V g ↔ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔
      (locMat hc V v g).1.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
    constructor
    · intro hs x
      have hx : ∀ w, w ≠ v → (fun i => evF E w (sgT E v (x i))) = 0 := fun w hw =>
        funext fun i => evF_sgT_ne hw _
      have hxv : (fun i => evF E v (sgT E v (x i))) = x := funext fun i => evF_sgT_self v _
      have := hs fun i => sgT E v (x i)
      rw [mem_lamHat_iff, mem_lamHat_iff] at this
      simp only [hev] at this
      constructor
      · intro h0
        have h1 := this.1 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw]; exact zero_mem _) v
        rwa [hxv] at h1
      · intro h0
        have h1 := this.2 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw, Matrix.mulVec_zero]; exact zero_mem _) v
        rwa [hxv] at h1
    · intro hs y
      rw [mem_lamHat_iff, mem_lamHat_iff]
      refine forall_congr' fun w => ?_
      rw [hev]
      by_cases hw : w = v
      · subst hw; exact hs _
      · rw [hg w hw, Units.val_one, Matrix.one_mulVec]
  rw [hloc, mem_range_iff]
  constructor
  · intro hs y
    have := hs (h.1.mulVec y)
    rw [hh, hh, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rwa [Units.val_mul, Units.val_mul]
  · intro hs x
    have := hs ((h⁻¹).1.mulVec x)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul,
      ← Matrix.mulVec_mulVec] at this
    rw [hh, hh]
    exact this

end GlobalTheory.PlaceComp.StabLoc
