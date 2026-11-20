import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

/- English proof (translation)
Use `haveI := hL`. Use `haveI : Module.Free 𝒪[k] L := Submodule.IsLattice.free k L`. Use `haveI : Module.Finite 𝒪[k] L := Module.Finite.iff_fg.mpr hL.fg`. Establish `hr : Module.finrank 𝒪[k] L = Fintype.card ι` using `Submodule.IsLattice.finrank_of_pi k L`. Set `b : Module.Basis ι 𝒪[k] L` to `(Module.finBasisOfFinrankEq 𝒪[k] L hr).reindex (Fintype.equivFin ι).symm`.

Set `c : Module.Basis ι k (ι → k)` to `b.extendOfIsLattice k`. Establish `hc : ∀ i, c i = (b i : ι → k)` using `fun i => Module.Basis.extendOfIsLattice_apply k b i`. Set `A : Matrix ι ι k` to `Matrix.of fun i j => (b j : ι → k) i`. Establish `hA : IsUnit A`. Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`.

Establish `: A.col = c`. Use function extensionality and compare the values at `j i`. Rewrite using `[hc]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `c.linearIndependent`. Take `⟨g, hg⟩` from `hA`. Establish `key : ∀ a : ι → 𝒪[k], (g : Matrix ι ι k) *ᵥ (fun i => (a i : k)) = ((∑ j, a j • b j : L) : ι → k)`. Introduce `a`. Use function extensionality and compare the values at `i`.

Rewrite using `[hg, Submodule.coe_sum, Finset.sum_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, Submodule.coe_smul, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Both sides reduce to the same expression.

Use `⟨g, ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Rewrite using `[mem_act]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Use `⟨fun i => (b.repr ⟨v, hv⟩ i : k), mem_stdLat.2 fun i => (b.repr ⟨v, hv⟩ i).2, ?_⟩` and prove the remaining obligations. Rewrite using `[key, b.sum_repr]`. Introduce and unpack `⟨w, hw, rfl⟩`. Rewrite `hw` using `[mem_stdLat]`. Use `key fun i => ⟨w i, hw i⟩` as an intermediate fact.

Express the relevant statement in the definitionally equal form `(g : Matrix ι ι k) *ᵥ w = _ at this`. Rewrite using `[this]`. Conclude with `Subtype.property _`.
-/
theorem exists_eq_act_stdLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (L : Submodule 𝒪[k] (ι → k)) (hL : Submodule.IsLattice k L) :
    ∃ g : GL ι k, L = act g (stdLat k ι) := by
  haveI := hL
  haveI : Module.Free 𝒪[k] L := Submodule.IsLattice.free k L
  haveI : Module.Finite 𝒪[k] L := Module.Finite.iff_fg.mpr hL.fg
  have hr : Module.finrank 𝒪[k] L = Fintype.card ι := Submodule.IsLattice.finrank_of_pi k L
  let b : Module.Basis ι 𝒪[k] L :=
    (Module.finBasisOfFinrankEq 𝒪[k] L hr).reindex (Fintype.equivFin ι).symm
  let c : Module.Basis ι k (ι → k) := b.extendOfIsLattice k
  have hc : ∀ i, c i = (b i : ι → k) := fun i => Module.Basis.extendOfIsLattice_apply k b i
  let A : Matrix ι ι k := Matrix.of fun i j => (b j : ι → k) i
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have : A.col = c := by
      funext j i
      rw [hc]; rfl
    rw [this]; exact c.linearIndependent
  obtain ⟨g, hg⟩ := hA
  have key : ∀ a : ι → 𝒪[k], (g : Matrix ι ι k) *ᵥ (fun i => (a i : k))
      = ((∑ j, a j • b j : L) : ι → k) := by
    intro a
    funext i
    rw [hg, Submodule.coe_sum, Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, Submodule.coe_smul, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]; rfl
  refine ⟨g, ?_⟩
  ext v
  rw [mem_act]
  constructor
  · intro hv
    refine ⟨fun i => (b.repr ⟨v, hv⟩ i : k), mem_stdLat.2 fun i => (b.repr ⟨v, hv⟩ i).2, ?_⟩
    rw [key, b.sum_repr]
  · rintro ⟨w, hw, rfl⟩
    rw [mem_stdLat] at hw
    have := key fun i => ⟨w i, hw i⟩
    change (g : Matrix ι ι k) *ᵥ w = _ at this
    rw [this]
    exact Subtype.property _

end GlobalTheory.RootEx.UnfoldShape
