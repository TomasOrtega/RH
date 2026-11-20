import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E _ _ w g _ i hi n τ σ hs`. Take `⟨φ, hφ, hφe⟩` from `hs`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by`. Assume the negation of the conclusion as `h`. Conclude with `hφ (LinearMap.ext fun u => not_not.1 fun hne => h ⟨u, hne⟩)`.

Set `e` to `equivRep σ`. Establish `hfix : ∀ m ∈ KOne (w.adicCompletion E) (Fin n), σ.ρ m (φ u) = φ u`. Introduce `m hm`. Take `⟨k, hk, rfl⟩` from `DiscreteGroups.sglob.DzIso.exists_of_mem_KOne i hi hm`. Use `hφe k u` as an intermediate fact.

Rewrite `this` using `[hk, map_one, Module.End.one_apply]`. Conclude with `this.symm`. Introduce `hbot`. Establish `hv : e.toIntertwiningMap (φ u) ∈ fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1))`. Introduce `m`.

Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul]`. Rewrite using `[← e.toIntertwiningMap.isIntertwining, hfix m m.2]`. Rewrite `hv` using `[hbot, Submodule.mem_bot]`. Establish `h2 : e.toLinearEquiv (φ u) = 0` using `hv`. Conclude with `hu (e.toLinearEquiv.injective (h2.trans (map_zero _).symm))`.
-/
theorem lDepth : LDepth := by
  intro E _ _ w g _ i hi n τ σ hs
  obtain ⟨φ, hφ, hφe⟩ := hs
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun u => not_not.1 fun hne => h ⟨u, hne⟩)
  let e := equivRep σ
  have hfix : ∀ m ∈ KOne (w.adicCompletion E) (Fin n), σ.ρ m (φ u) = φ u := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KOne i hi hm
    have := hφe k u
    rw [hk, map_one, Module.End.one_apply] at this
    exact this.symm
  intro hbot
  have hv : e.toIntertwiningMap (φ u) ∈ fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) := by
    intro m
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [← e.toIntertwiningMap.isIntertwining, hfix m m.2]
  rw [hbot, Submodule.mem_bot] at hv
  have h2 : e.toLinearEquiv (φ u) = 0 := hv
  exact hu (e.toLinearEquiv.injective (h2.trans (map_zero _).symm))

end DiscreteGroups.sglob.DzType
