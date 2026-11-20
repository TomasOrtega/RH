import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem

noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.HeckeScalar

open GlobalTheory.LFun.SatCompare GlobalTheory.LocGL

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {K : Subgroup G}

/- English proof (translation)
Establish `hm` using `Final.DosetIndMem G K ℂ g`. Establish `hfin` using `Formalism.UG.P.finite_support_cosets hK hm.2`. Establish `hS : ∀ c : G ⧸ K, c ∈ hfin.toFinset ↔ c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K` using `fun c => by`. Simplify using `[dosetInd]`. Use `⟨hfin.toFinset.card, ?_, ?_⟩` and prove the remaining obligations.

Use `Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (hS _).2 ?_⟩)` and prove the remaining obligations. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K g`. Conclude with `DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩`. Rewrite using `[← idem_of_mem hπ.1 hc (heckeVec_mem_fixed hK hm hz), heckeVec, finsum_eq_sum_of_support_subset (s := hfin.toFinset), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]`. Use `Finset.sum_congr rfl fun c hcS => ?_` and prove the remaining obligations.

Establish `h1` using `(hS c).1 hcS`. Take `⟨a, ha, b, hb, e⟩` from `DoubleCoset.mem_doubleCoset.1 h1`. Rewrite using `[dosetInd, Set.indicator_of_mem h1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hz b hb]`. Simplify using `using idem_apply_mem hπ.1 hc ha (π g z)`. Introduce `c hc'`.

Use `Finset.mem_coe.2 ((hS c).2 ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Conclude with `hc' (by simp [dosetInd, h0])`.
-/
theorem heckeVec_dosetInd_eq_idem (hπ : GlobalTheory.LGrp.IsIrrSmooth π) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (g : G) {z : V} (hz : z ∈ fixed π K) :
    ∃ N : ℂ, N ≠ 0 ∧ heckeVec π K (dosetInd ℂ K g) z = N • idem hπ.1 hc (π g z) := by
  classical
  have hm := Final.DosetIndMem G K ℂ g
  have hfin := Formalism.UG.P.finite_support_cosets hK hm.2
  have hS : ∀ c : G ⧸ K, c ∈ hfin.toFinset ↔ c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c => by
    simp [dosetInd]
  refine ⟨hfin.toFinset.card, ?_, ?_⟩
  · refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (hS _).2 ?_⟩)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩
  · rw [← idem_of_mem hπ.1 hc (heckeVec_mem_fixed hK hm hz), heckeVec,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun c hcS => ?_
      have h1 := (hS c).1 hcS
      obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 h1
      rw [dosetInd, Set.indicator_of_mem h1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        GlobalTheory.LGrp.mem_fixed.1 hz b hb]
      simpa using idem_apply_mem hπ.1 hc ha (π g z)
    · intro c hc'
      refine Finset.mem_coe.2 ((hS c).2 ?_)
      by_contra h0
      exact hc' (by simp [dosetInd, h0])

/- English proof (translation)
Introduce `G V _ _ _ _ _ π K hc hK hcomm hπ hfd h hh`. Distinguish the cases in `hb : fixed π K = ⊥`. Use `⟨0, fun x hx => ?_⟩` and prove the remaining obligations. Use `heckeVec_mem_fixed hK hh hx` as an intermediate fact. Rewrite `this` using `[hb]`.

Simplify using `using this`. Use `haveI : Nontrivial (fixed π K) := Submodule.nontrivial_iff_ne_bot.2 hb`. Set `A : Module.End ℂ (fixed π K)` to `(heckeLin hK hh π).restrict fun x hx => heckeVec_mem_fixed hK hh hx`. Take `⟨c, hcA⟩` from `Module.End.exists_eigenvalue A`. Take `⟨⟨x₀, hx₀⟩, hv⟩` from `hcA.exists_hasEigenvector`.

Establish `h0 : x₀ ≠ 0` using `fun e => hv.2 (Subtype.ext e)`. Establish `he : heckeVec π K h x₀ = c • x₀` using `congrArg Subtype.val hv.apply_eq_smul`. Establish `key : ∀ g, heckeLin hK hh π (idem hπ.1 hc (π g x₀)) = c • idem hπ.1 hc (π g x₀)` using `fun g => by`. Take `⟨N, hN, e⟩` from `heckeVec_dosetInd_eq_idem hπ hc hK g hx₀`. Establish `hm` using `Final.DosetIndMem G K ℂ g`.

Use `smul_right_injective V hN ?_` and prove the remaining obligations. Use `show N • _ = N • _`. Rewrite using `[← map_smul, smul_comm N c, ← e, heckeLin_apply, ← heckeVec_conv hK hh hm hx₀, hcomm _ hh _ hm, heckeVec_conv hK hm hh hx₀, he, heckeVec_smul hK hm]`. Use `⟨c, fun x hx => ?_⟩` and prove the remaining obligations. Establish `all : ∀ w : MonoidAlgebra ℂ G, heckeLin hK hh π (idem hπ.1 hc (orbitMap π x₀ w)) = c • idem hπ.1 hc (orbitMap π x₀ w)` using `fun w => by`.

Proceed by induction on `w using MonoidAlgebra.induction_on with`. Consider the case `of g`. Establish `: orbitMap π x₀ (MonoidAlgebra.of ℂ G g) = π g x₀` using `by show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x₀ = _`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `key g`. Consider the case `add a b ha hb`. Establish `: orbitMap π x₀ (a + b) = orbitMap π x₀ a + orbitMap π x₀ b` using `map_add _ _ _`. Rewrite using `[this, map_add, map_add, ha, hb, smul_add]`. Consider the case `smul r a ha`.

Establish `: orbitMap π x₀ (r • a) = r • orbitMap π x₀ a` using `map_smul _ _ _`. Rewrite using `[this, map_smul, map_smul, ha, smul_comm]`. Take `⟨w, rfl⟩` from `orbitMap_surjective hπ.2 h0 x`. Use `all w` as an intermediate fact. Rewrite `this` using `[idem_of_mem hπ.1 hc hx]`. Then use the resulting hypothesis.
-/
theorem exists_scalar : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K →
    (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → GlobalTheory.LGrp.IsIrrSmooth π →
    FiniteDimensional ℂ (fixed π K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  intro G V _ _ _ _ _ π K hc hK hcomm hπ hfd h hh
  by_cases hb : fixed π K = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    have := heckeVec_mem_fixed hK hh hx
    rw [hb] at this
    simpa using this
  haveI : Nontrivial (fixed π K) := Submodule.nontrivial_iff_ne_bot.2 hb
  let A : Module.End ℂ (fixed π K) := (heckeLin hK hh π).restrict fun x hx => heckeVec_mem_fixed hK hh hx
  obtain ⟨c, hcA⟩ := Module.End.exists_eigenvalue A
  obtain ⟨⟨x₀, hx₀⟩, hv⟩ := hcA.exists_hasEigenvector
  have h0 : x₀ ≠ 0 := fun e => hv.2 (Subtype.ext e)
  have he : heckeVec π K h x₀ = c • x₀ := congrArg Subtype.val hv.apply_eq_smul
  have key : ∀ g, heckeLin hK hh π (idem hπ.1 hc (π g x₀)) = c • idem hπ.1 hc (π g x₀) := fun g => by
    obtain ⟨N, hN, e⟩ := heckeVec_dosetInd_eq_idem hπ hc hK g hx₀
    have hm := Final.DosetIndMem G K ℂ g
    refine smul_right_injective V hN ?_
    show N • _ = N • _
    rw [← map_smul, smul_comm N c, ← e, heckeLin_apply, ← heckeVec_conv hK hh hm hx₀, hcomm _ hh _ hm,
      heckeVec_conv hK hm hh hx₀, he, heckeVec_smul hK hm]
  refine ⟨c, fun x hx => ?_⟩
  have all : ∀ w : MonoidAlgebra ℂ G, heckeLin hK hh π (idem hπ.1 hc (orbitMap π x₀ w)) =
      c • idem hπ.1 hc (orbitMap π x₀ w) := fun w => by
    induction w using MonoidAlgebra.induction_on with
    | of g =>
      have : orbitMap π x₀ (MonoidAlgebra.of ℂ G g) = π g x₀ := by
        show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x₀ = _
        simp
      rw [this]; exact key g
    | add a b ha hb =>
      have : orbitMap π x₀ (a + b) = orbitMap π x₀ a + orbitMap π x₀ b := map_add _ _ _
      rw [this, map_add, map_add, ha, hb, smul_add]
    | smul r a ha =>
      have : orbitMap π x₀ (r • a) = r • orbitMap π x₀ a := map_smul _ _ _
      rw [this, map_smul, map_smul, ha, smul_comm]
  obtain ⟨w, rfl⟩ := orbitMap_surjective hπ.2 h0 x
  have := all w
  rwa [idem_of_mem hπ.1 hc hx] at this

end GlobalTheory.LFun.HeckeScalar

end
