import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConductorMulMemAdjoinOfSeparableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenMulLeftImageLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusSubmoduleMulLeftImageMemSelfDualStableLattiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexUnitStabilizerIntegralUnitsNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMaximalOrderHullSelfDualStableLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSelfDualIntegralHermitianLatticesModUnitsStatement

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.OrbitFinite

/- English proof (translation)
Introduce `K B hsep x hxu hxσ`. Distinguish the cases in `h0 : ∃ L0, L0 ∈ B.X x`. Use `swap`. Use `push_neg at h0 haveI : IsEmpty (B.X x) := ⟨fun L => h0 L.1 L.2⟩`. Use `⟨?_, fun L hL => absurd hL (h0 L)⟩` and prove the remaining obligations.

Unfold `Orb`. Use `infer_instance`. Take `⟨L0, hL0⟩` from `h0`. Establish `hgi : IsIntegral K.O B.g` using `isIntegral_of_isLat_stable L0 hL0.1 B.g hL0.2.1`. Take `⟨c, hc0, hc⟩` from `GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable K B hsep hgi`.

Establish `hadj : ∀ L ∈ B.X x, ∀ a ∈ Algebra.adjoin K.O ({B.g} : Set B.A), ∀ y ∈ L, a * y ∈ L`. Introduce `L hL a ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a h`. Rewrite `h` using `[Set.mem_singleton_iff]`.

Substitute `h` using the available equality. Conclude with `hL.2.1`. Consider the case `algebraMap r`. Introduce `y hy`. Rewrite using `[← Algebra.smul_def]`.

Conclude with `L.smul_mem r hy`. Consider the case `add a b _ _ ha hb`. Introduce `y hy`. Rewrite using `[add_mul]`. Conclude with `L.add_mem (ha y hy) (hb y hy)`.

Consider the case `mul a b _ _ ha hb`. Introduce `y hy`. Rewrite using `[mul_assoc]`. Conclude with `ha _ (hb y hy)`. Establish `hcL : ∀ L ∈ B.X x, ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L` using `fun L hL u hu y hy => hadj L hL _ (hc u hu) y hy`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨S, hSf, hSl, hS⟩` from `GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits K B hsep x hxu hxσ c hc0 set W : Set (Submodule K.O B.A) := (⋃ J ∈ S, {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) J ≤ M ∧ M ≤ J}) ∩ B.X x with hW`. Establish `hWf : W.Finite` using `(hSf.biUnion fun J hJ => GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B J (hSl J hJ) c hc0).subset Set.inter_subset_left`. Use `haveI : Finite W := hWf.to_subtype`. Set `f : W → Orb K.O B.T (B.X x)` to `fun M => Quot.mk _ ⟨M.1, M.2.2⟩`.

Apply `Finite.of_surjective f` to reduce the goal to its premises. Introduce `o`. Use `set L := (Quot.out o).1 with hLdef`. Establish `hL : L ∈ B.X x` using `(Quot.out o).2`. Take `⟨J, hJl, hJs, hJ1, hJ2, hJc, hLJ⟩` from `GlobalTheory.T.exists_maximalOrder_hull_selfDual_stable_lattice K B x c hc0 L hL (hcL L hL)`.

Take `⟨t, ht, htS⟩` from `hS J hJl hJs hJ1 hJ2`. Establish `hcomm : mulLat K.O (algebraMap K.O B.A c) (mulLat K.O (t : B.A) J) = mulLat K.O (t : B.A) (mulLat K.O (algebraMap K.O B.A c) J)`. Unfold `mulLat`. Rewrite using `[← Submodule.map_comp, ← Submodule.map_comp]`. Use `congr 1`.

Use extensionality with `y`. Simplify using `[mul_left_comm]`. Establish `hmem : mulLat K.O (t : B.A) L ∈ W`. Use `⟨Set.mem_biUnion htS ⟨?_, Submodule.map_mono hLJ⟩, GlobalTheory.T.torus_submoduleMulLeftImage_mem_selfDualStableLattices K B x t ht L hL⟩` and prove the remaining obligations. Rewrite using `[hcomm]`.

Conclude with `Submodule.map_mono hJc`. Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Quot.out_eq o]`. Conclude with `(Quot.sound ⟨t, ht, rfl⟩).symm`. Introduce `L hL`.

Use `⟨?_, GlobalTheory.T.relIndex_unitStabilizer_integralUnits_ne_zero K B L hL.1 c hc0 (hcL L hL)⟩` and prove the remaining obligations. Introduce and unpack `t ⟨hs, -⟩`. Use `⟨isIntegral_of_isLat_stable L hL.1 (t : B.A) fun y hy => (hs y).mp hy, ?_⟩` and prove the remaining obligations. Use `isIntegral_of_isLat_stable L hL.1 _ fun y hy => (hs _).mpr ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, Units.mul_inv, one_mul]`.

Conclude with `hy`.
-/
theorem orbits_finite : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  intro K B hsep x hxu hxσ
  by_cases h0 : ∃ L0, L0 ∈ B.X x
  swap
  · push_neg at h0
    haveI : IsEmpty (B.X x) := ⟨fun L => h0 L.1 L.2⟩
    refine ⟨?_, fun L hL => absurd hL (h0 L)⟩
    unfold Orb
    infer_instance
  obtain ⟨L0, hL0⟩ := h0
  have hgi : IsIntegral K.O B.g := isIntegral_of_isLat_stable L0 hL0.1 B.g hL0.2.1
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable K B hsep hgi

  have hadj : ∀ L ∈ B.X x, ∀ a ∈ Algebra.adjoin K.O ({B.g} : Set B.A), ∀ y ∈ L, a * y ∈ L := by
    intro L hL a ha
    induction ha using Algebra.adjoin_induction with
    | mem a h =>
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hL.2.1
    | algebraMap r =>
      intro y hy
      rw [← Algebra.smul_def]
      exact L.smul_mem r hy
    | add a b _ _ ha hb =>
      intro y hy
      rw [add_mul]
      exact L.add_mem (ha y hy) (hb y hy)
    | mul a b _ _ ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb y hy)
  have hcL : ∀ L ∈ B.X x, ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L :=
    fun L hL u hu y hy => hadj L hL _ (hc u hu) y hy
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hSf, hSl, hS⟩ := GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits K B hsep x hxu hxσ c hc0
    set W : Set (Submodule K.O B.A) :=
      (⋃ J ∈ S, {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) J ≤ M ∧ M ≤ J}) ∩ B.X x with hW
    have hWf : W.Finite :=
      (hSf.biUnion fun J hJ => GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B J (hSl J hJ) c hc0).subset Set.inter_subset_left
    haveI : Finite W := hWf.to_subtype
    let f : W → Orb K.O B.T (B.X x) := fun M => Quot.mk _ ⟨M.1, M.2.2⟩
    apply Finite.of_surjective f
    intro o
    set L := (Quot.out o).1 with hLdef
    have hL : L ∈ B.X x := (Quot.out o).2
    obtain ⟨J, hJl, hJs, hJ1, hJ2, hJc, hLJ⟩ := GlobalTheory.T.exists_maximalOrder_hull_selfDual_stable_lattice K B x c hc0 L hL (hcL L hL)
    obtain ⟨t, ht, htS⟩ := hS J hJl hJs hJ1 hJ2
    have hcomm : mulLat K.O (algebraMap K.O B.A c) (mulLat K.O (t : B.A) J) =
        mulLat K.O (t : B.A) (mulLat K.O (algebraMap K.O B.A c) J) := by
      unfold mulLat
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext y
      simp [mul_left_comm]
    have hmem : mulLat K.O (t : B.A) L ∈ W := by
      refine ⟨Set.mem_biUnion htS ⟨?_, Submodule.map_mono hLJ⟩, GlobalTheory.T.torus_submoduleMulLeftImage_mem_selfDualStableLattices K B x t ht L hL⟩
      rw [hcomm]
      exact Submodule.map_mono hJc
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [← Quot.out_eq o]
    exact (Quot.sound ⟨t, ht, rfl⟩).symm
  · intro L hL
    refine ⟨?_, GlobalTheory.T.relIndex_unitStabilizer_integralUnits_ne_zero K B L hL.1 c hc0 (hcL L hL)⟩
    rintro t ⟨hs, -⟩
    refine ⟨isIntegral_of_isLat_stable L hL.1 (t : B.A) fun y hy => (hs y).mp hy, ?_⟩
    refine isIntegral_of_isLat_stable L hL.1 _ fun y hy => (hs _).mpr ?_
    rw [← mul_assoc, Units.mul_inv, one_mul]
    exact hy

end GlobalTheory.UnitLemma.OrbitFinite
