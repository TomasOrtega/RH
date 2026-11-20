import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZCore

/- English proof (translation)
Establish `hc : Continuous fun p : GL (Fin d) k × (Fin d → k) => ((p.1 : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec p.2` using `Continuous.matrix_mulVec (Units.continuous_val.comp continuous_fst) continuous_snd`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `g hg`. Establish `hK : IsCompact ((lat0 : COSub k d).sub : Set (Fin d → k))` using `lat0.isCompact`. Conclude with `hK.eventually_forall_of_forall_eventually (P := fun (h : GL (Fin d) k) (y : Fin d → k) => (h : Matrix (Fin d) (Fin d) k).mulVec y ∈ (lat0 : COSub k d).sub) fun y hy => hc.continuousAt.eventually_mem (lat0.isOpen.mem_nhds (hg y hy))`.
-/
theorem isOpen_preserve_standard_lattice {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} :
    IsOpen {g : GL (Fin d) k | ∀ y ∈ (lat0 : COSub k d).sub,
      (g : Matrix (Fin d) (Fin d) k).mulVec y ∈ (lat0 : COSub k d).sub} := by
  have hc : Continuous fun p : GL (Fin d) k × (Fin d → k) =>
      ((p.1 : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec p.2 :=
    Continuous.matrix_mulVec (Units.continuous_val.comp continuous_fst) continuous_snd
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hK : IsCompact ((lat0 : COSub k d).sub : Set (Fin d → k)) := lat0.isCompact
  exact hK.eventually_forall_of_forall_eventually
    (P := fun (h : GL (Fin d) k) (y : Fin d → k) =>
      (h : Matrix (Fin d) (Fin d) k).mulVec y ∈ (lat0 : COSub k d).sub)
    fun y hy => hc.continuousAt.eventually_mem (lat0.isOpen.mem_nhds (hg y hy))

/- English proof (translation)
Establish `h1` using `isOpen_preserve_standard_lattice (k := k) (d := d)`. Establish `h2` using `h1.preimage (continuous_inv (G := GL (Fin d) k))`. Use `h1.inter h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Establish `hg' : (lat0 : COSub k d).act g = lat0` using `hg`. Use `⟨fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `(COSub.mulVec_mem_act (L := (lat0 : COSub k d)) g (y := y)).2 hy` as an intermediate fact. Rewrite `this` using `[hg']`. Then use the resulting hypothesis.

Establish `hy' : y ∈ ((lat0 : COSub k d).act g).sub` using `by rwa [hg']`. Conclude with `COSub.mem_act.1 hy'`. Introduce and unpack `⟨ha, hb⟩`. Use `COSub.ext (AddSubgroup.ext fun y => ?_)` and prove the remaining obligations. Rewrite using `[COSub.mem_act]`.

Use `⟨fun hy => ?_, fun hy => hb y hy⟩` and prove the remaining obligations. Use `ha _ hy` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]`. Then use the resulting hypothesis.
-/
theorem isOpen_stabilizer_standard_lattice {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} :
    IsOpen {g : GL (Fin d) k | (lat0 : COSub k d).act g = lat0} := by
  have h1 := isOpen_preserve_standard_lattice (k := k) (d := d)
  have h2 := h1.preimage (continuous_inv (G := GL (Fin d) k))
  convert h1.inter h2 using 1
  ext g
  constructor
  · intro hg
    have hg' : (lat0 : COSub k d).act g = lat0 := hg
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have := (COSub.mulVec_mem_act (L := (lat0 : COSub k d)) g (y := y)).2 hy
      rwa [hg'] at this
    · have hy' : y ∈ ((lat0 : COSub k d).act g).sub := by rwa [hg']
      exact COSub.mem_act.1 hy'
  · rintro ⟨ha, hb⟩
    refine COSub.ext (AddSubgroup.ext fun y => ?_)
    rw [COSub.mem_act]
    refine ⟨fun hy => ?_, fun hy => hb y hy⟩
    have := ha _ hy
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this

end GlobalTheory.CompanionTheory.BZCore
