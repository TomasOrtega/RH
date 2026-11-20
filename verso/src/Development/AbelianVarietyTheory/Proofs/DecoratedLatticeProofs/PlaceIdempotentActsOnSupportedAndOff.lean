import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise TensorProduct
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.FinPl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp [map_add, hx, hy]`. Consider the case `tmul a m`. Simplify using `[Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul, Algebra.smul_def]`.
-/
theorem tensorProductBasis_repr_map_firstFactor {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    [CommRing B] [Algebra F B] {ι : Type} (b : Module.Basis ι F E) (f : A →ₐ[F] B) (x : A ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) x) i =
      f ((Algebra.TensorProduct.basis A b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a m =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul, Algebra.smul_def]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis D.host.F D.host.E`. Set `bA` to `Algebra.TensorProduct.basis (AF D.host.F) b`. It suffices to establish `hc : ∀ i, bA.repr a i = 0 by`. Apply `bA.repr.injective` to reduce the goal to its premises. Use extensionality with `i`.

Simplify using `using hc i`. Introduce `i`. Establish `h1 : fstA D.host.F (bA.repr a i) = 0`. Use `tensorProductBasis_repr_map_firstFactor b (fstA D.host.F) a i` as an intermediate fact. Rewrite using `[← this]`.

Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.basis _ b).repr (infPart D a) i = 0`. Rewrite using `[h0]`. Simplify using `only [map_zero, Finsupp.coe_zero, Pi.zero_apply]`. Establish `h2 : ∀ w : Pl D, evalV D.host.F w (sndA D.host.F (bA.repr a i)) = 0`. Introduce `w`.

Establish `e1` using `tensorProductBasis_repr_map_firstFactor b (sndA D.host.F) a i`. Establish `e2` using `tensorProductBasis_repr_map_firstFactor b (evalV D.host.F w) (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) i`. Establish `hw' : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E) (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) = 0` using `hw w`. Rewrite using `[← e1, ← e2, hw', LinearEquiv.map_zero]`. Both sides reduce to the same expression.

Apply `Prod.ext` to reduce the goal to its premises. Conclude with `h1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Conclude with `h2 w`.
-/
theorem CMAdele_eq_zero_of_infinite_and_finite_components_zero (D : D7) (a : AE D) (h0 : infPart D a = 0) (hw : ∀ w : Pl D, compAt D w a = 0) :
    a = 0 := by
  let b := Module.Free.chooseBasis D.host.F D.host.E
  let bA := Algebra.TensorProduct.basis (AF D.host.F) b
  suffices hc : ∀ i, bA.repr a i = 0 by
    apply bA.repr.injective
    ext i
    simpa using hc i
  intro i
  have h1 : fstA D.host.F (bA.repr a i) = 0 := by
    have := tensorProductBasis_repr_map_firstFactor b (fstA D.host.F) a i
    rw [← this]
    change (Algebra.TensorProduct.basis _ b).repr (infPart D a) i = 0
    rw [h0]; simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have h2 : ∀ w : Pl D, evalV D.host.F w (sndA D.host.F (bA.repr a i)) = 0 := by
    intro w
    have e1 := tensorProductBasis_repr_map_firstFactor b (sndA D.host.F) a i
    have e2 := tensorProductBasis_repr_map_firstFactor b (evalV D.host.F w)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) i
    have hw' : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) = 0 := hw w
    rw [← e1, ← e2, hw', LinearEquiv.map_zero]
    rfl
  apply Prod.ext
  · exact h1
  · apply Subtype.ext
    funext w
    exact h2 w

/- English proof (translation)
Simplify using `only [idAt, Submodule.mem_inf, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]`.
-/
theorem mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere (D : D7) (P : Pl D → Prop) (a : AE D) :
    a ∈ idAt D P ↔ infPart D a = 0 ∧ ∀ w : Pl D, ¬ P w → compAt D w a = 0 := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]

/- English proof (translation)
Establish `ha : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E)`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Use `⟨?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[ha]`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = 0`.

Rewrite using `[Algebra.TensorProduct.map_tmul, hε]`. Conclude with `TensorProduct.zero_tmul _ _`. Rewrite using `[ha]`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E) (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E))) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hε]`.

Both sides reduce to the same expression.
-/
theorem placeIdempotent_infinite_and_finite_components (D : D7) (v : Pl D) (ε : AF D.host.F) (α : Af D.host.F)
    (hε : ε = pairA D.host.F 0 α) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) ε) = evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul, hε]
    exact TensorProduct.zero_tmul _ _
  · rw [ha]
    change Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hε]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha`. Rewrite `ha` using `[mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]`. Take `⟨ha0, haw⟩` from `ha`. Rewrite using `[← sub_eq_zero]`.

Apply `CMAdele_eq_zero_of_infinite_and_finite_components_zero` to reduce the goal to its premises. Rewrite using `[RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]`. Introduce `w`. Rewrite using `[RingHom.map_sub, RingHom.map_mul]`. Distinguish the cases in `h : w = v`.

Substitute `h` using the available equality. Rewrite using `[c1, one_mul, sub_self]`. Rewrite using `[haw w h, mul_zero, sub_zero]`. Introduce `ha`. Rewrite using `[mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]`.

Use `⟨?_, fun w hw' => ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, RingHom.map_mul, h0, zero_mul]`. Rewrite using `[← ha, RingHom.map_mul, c0 w hw', zero_mul]`.
-/
theorem mem_supportedAtPlace_iff_placeIdempotent_mul (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0) (c1 : compAt D v e = 1)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) : a ∈ idAt D (· = v) ↔ e * a = a := by
  constructor
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
    obtain ⟨ha0, haw⟩ := ha
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul]
      by_cases h : w = v
      · subst h; rw [c1, one_mul, sub_self]
      · rw [haw w h, mul_zero, sub_zero]
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
    refine ⟨?_, fun w hw' => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, c0 w hw', zero_mul]

/- English proof (translation)
Rewrite `ha` using `[mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]`. Take `⟨ha0, haw⟩` from `ha`. Apply `CMAdele_eq_zero_of_infinite_and_finite_components_zero` to reduce the goal to its premises. Rewrite using `[RingHom.map_mul, h0, zero_mul]`. Introduce `w`.

Rewrite using `[RingHom.map_mul]`. Distinguish the cases in `h : w = v`. Rewrite using `[haw w (fun h' => h' h), mul_zero]`. Rewrite using `[c0 w h, zero_mul]`.
-/
theorem placeIdempotent_mul_supportedOffPlace_eq_zero (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) (ha : a ∈ idAt D (· ≠ v)) : e * a = 0 := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
  obtain ⟨ha0, haw⟩ := ha
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_mul, h0, zero_mul]
  · intro w
    rw [RingHom.map_mul]
    by_cases h : w = v
    · rw [haw w (fun h' => h' h), mul_zero]
    · rw [c0 w h, zero_mul]

/- English proof (translation)
Introduce `D v ε ⟨α, hε, hv, hw⟩`. Take `⟨h0, hc⟩` from `placeIdempotent_infinite_and_finite_components D v ε α hε`. Establish `c1 : compAt D v (algebraMap (AF D.host.F) (AE D) ε) = 1`. Rewrite using `[hc, hv]`. Both sides reduce to the same expression.

Establish `c0 : ∀ w : Pl D, w ≠ v → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0`. Introduce `w h`. Rewrite using `[hc, hw w h, TensorProduct.zero_tmul]`. Conclude with `⟨mem_supportedAtPlace_iff_placeIdempotent_mul D v _ h0 c1 c0, placeIdempotent_mul_supportedOffPlace_eq_zero D v _ h0 c0⟩`.
-/
theorem placeIdem_acts : ∀ (D : D7) (v : Pl D) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ a : AE D, a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) ε * a = a) ∧
    (∀ a : AE D, a ∈ idAt D (· ≠ v) → algebraMap (AF D.host.F) (AE D) ε * a = 0) := by
  intro D v ε ⟨α, hε, hv, hw⟩
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hε
  have c1 : compAt D v (algebraMap (AF D.host.F) (AE D) ε) = 1 := by
    rw [hc, hv]; rfl
  have c0 : ∀ w : Pl D, w ≠ v → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    intro w h; rw [hc, hw w h, TensorProduct.zero_tmul]
  exact ⟨mem_supportedAtPlace_iff_placeIdempotent_mul D v _ h0 c1 c0, placeIdempotent_mul_supportedOffPlace_eq_zero D v _ h0 c0⟩

end GlobalTheory.FinPl
