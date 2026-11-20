import Mathlib
import Formalism.UnipotentAdelicQuotients.FinOrdValGen
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
import GroundTheory.GlobalFields.Adele.WeakApproxUnits

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Topology
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.BlockD

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `hF : {z : ℂˣ | z ^ n = 1}.Finite`. Use `((Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.preimage Units.val_injective.injOn).subset ?_` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]`. Rewrite using `[Polynomial.mem_nthRoots hn]`.

Use `congrArg Units.val (show z ^ n = 1 from hz)` as an intermediate fact. Simplify using `using this`. Establish `hC : IsClosed ({z : ℂˣ | z ^ n = 1} \ {1})` using `(hF.subset Set.sdiff_subset).isClosed`. Establish `hpow : ∀ g, χ g ^ n = 1` using `fun g ↦ by`. Use `congrArg (fun f : G →* ℂˣ ↦ f g) h` as an intermediate fact.

Simplify using `using this`. Establish `heq : (χ.ker : Set G) = χ ⁻¹' ({z : ℂˣ | z ^ n = 1} \ {1})ᶜ`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, not_not]`. Conclude with `⟨fun h1 _ ↦ h1, fun h1 ↦ h1 (hpow g)⟩`.

Rewrite using `[heq]`. Conclude with `hC.isOpen_compl.preimage hχ`.
-/
theorem isOpen_ker_of_pow_eq_one {G : Type*} [Group G] [TopologicalSpace G] (χ : G →* ℂˣ)
    (hχ : Continuous χ) {n : ℕ} (hn : 0 < n) (h : χ ^ n = 1) : IsOpen (χ.ker : Set G) := by
  have hF : {z : ℂˣ | z ^ n = 1}.Finite := by
    refine ((Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.preimage
      Units.val_injective.injOn).subset ?_
    intro z hz
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_nthRoots hn]
    have := congrArg Units.val (show z ^ n = 1 from hz)
    simpa using this
  have hC : IsClosed ({z : ℂˣ | z ^ n = 1} \ {1}) := (hF.subset Set.sdiff_subset).isClosed
  have hpow : ∀ g, χ g ^ n = 1 := fun g ↦ by
    have := congrArg (fun f : G →* ℂˣ ↦ f g) h
    simpa using this
  have heq : (χ.ker : Set G) = χ ⁻¹' ({z : ℂˣ | z ^ n = 1} \ {1})ᶜ := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, not_not]
    exact ⟨fun h1 _ ↦ h1, fun h1 ↦ h1 (hpow g)⟩
  rw [heq]
  exact hC.isOpen_compl.preimage hχ

end GroundTheory.BlockD
