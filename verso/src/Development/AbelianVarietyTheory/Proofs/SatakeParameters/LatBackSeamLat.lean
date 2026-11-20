import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack

open NumberField

namespace GlobalTheory.LatticeBackSeam

/- English proof (translation)
Introduce `D X s n N`. Use extensionality with `y`. Rewrite using `[GlobalTheory.TwU.mem_latBack]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `key : ∀ v ∈ Formalism.L2.Ker.Seam.lat s N, ∃ x ∈ N, (fun l => s.iE (x l)) = v`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨x, hx, rfl⟩` from `hv`.

Conclude with `⟨x, hx, rfl⟩`. Consider the case `zero => exact ⟨0, N.zero_mem, by funext l; simp⟩`. Consider the case `add v w _ _ hv hw`. Take `⟨x, hx, rfl⟩` from `hv`. Take `⟨x', hx', rfl⟩` from `hw`.

Conclude with `⟨x + x', N.add_mem hx hx', by funext l; simp⟩`. Consider the case `smul r v _ hv`. Take `⟨x, hx, rfl⟩` from `hv`. Use `⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • x, N.smul_mem _ hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`.

Simplify using `[Algebra.smul_def, RingOfIntegers.mapRingEquiv_symm_apply]`. Take `⟨x, hx, hxy⟩` from `key _ hy`. Establish `hxe : x = y` using `funext fun l => s.iE.injective (congrFun hxy l)`. Rewrite using `[← hxe]`. Conclude with `hx`.

Introduce `hy`. Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`.
-/
theorem latBack_seam_lat : ∀ {D : Formalism.BasicNotions.D7} {X : Formalism.L2.Col.Fields} (s : Formalism.L2.Ker.Seam D X) {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers (Formalism.L2.Col.Fields.E X)) (Formalism.L2.Col.Sp (Formalism.L2.Col.Fields.E X) n)),
    GlobalTheory.TwU.latBack s (Formalism.L2.Ker.Seam.lat s N) = N := by
  intro D X s n N
  ext y
  rw [GlobalTheory.TwU.mem_latBack]
  constructor
  · intro hy
    have key : ∀ v ∈ Formalism.L2.Ker.Seam.lat s N, ∃ x ∈ N, (fun l => s.iE (x l)) = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        exact ⟨x, hx, rfl⟩
      | zero => exact ⟨0, N.zero_mem, by funext l; simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨x, hx, rfl⟩ := hv
        obtain ⟨x', hx', rfl⟩ := hw
        exact ⟨x + x', N.add_mem hx hx', by funext l; simp⟩
      | smul r v _ hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • x, N.smul_mem _ hx, ?_⟩
        funext l
        simp [Algebra.smul_def, RingOfIntegers.mapRingEquiv_symm_apply]
    obtain ⟨x, hx, hxy⟩ := key _ hy
    have hxe : x = y := funext fun l => s.iE.injective (congrFun hxy l)
    rw [← hxe]
    exact hx
  · intro hy
    exact Submodule.subset_span ⟨y, hy, rfl⟩

end GlobalTheory.LatticeBackSeam
