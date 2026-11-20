import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorProductAction
open scoped TensorProduct nonZeroDivisors
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hne : h ≠ 0` using `hm.ne_zero`. Establish `hsemi : T.IsSemisimple` using `Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0`. Establish `hgen : ∀ μ, T.maxGenEigenspace μ = T.eigenspace μ` using `fun μ => hsemi.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ`. Establish `hev : ∀ (q : κ[X]) (ν : κ) (v : G), v ∈ T.eigenspace ν → aeval T q v = eval ν q • v`. Introduce `q ν v hv`.

Distinguish the cases in `hv0 : v = 0`. Simplify using `[hv0]`. Conclude with `Module.End.aeval_apply_of_hasEigenvector (Module.End.hasEigenvector_iff.2 ⟨hv, hv0⟩)`. Use `set R : Finset κ := h.roots.toFinset with hR`. Establish `hmemR : ∀ μ, μ ∈ R ↔ h.IsRoot μ` using `fun μ => by`.

Rewrite using `[hR, Multiset.mem_toFinset, mem_roots hne]`. Establish `hfr : ∀ μ ∈ R, Module.finrank κ (T.eigenspace μ) = N`. Introduce `μ hμ`. Establish `hμ' : μ ∈ h.roots` using `Multiset.mem_toFinset.1 hμ`. Rewrite using `[← hgen, LinearMap.finrank_maxGenEigenspace_eq, hc, ← count_roots, roots_pow, Multiset.count_nsmul, Multiset.count_eq_one_of_mem (nodup_roots hs) hμ', mul_one]`.

Establish `hout : ∀ μ, μ ∉ R → ∀ v ∈ T.eigenspace μ, v = 0`. Introduce `μ hμ v hv`. Assume the negation of the conclusion as `hv0`. Apply `hμ` to reduce the goal to its premises. Rewrite using `[hmemR]`.

Establish `h1` using `hev h μ v hv`. Rewrite `h1` using `[h0]`. Establish `h2 : eval μ h • v = 0` using `by simpa using h1.symm`. Conclude with `(smul_eq_zero.1 h2).resolve_right hv0`. Establish `hbasis : ∀ μ ∈ R, ∃ b : Fin N → G, (∀ j, b j ∈ T.eigenspace μ) ∧ ∀ v ∈ T.eigenspace μ, ∃ c : Fin N → κ, v = ∑ j, c j • b j`.

Introduce `μ hμ`. Set `B` to `Module.finBasisOfFinrankEq κ (T.eigenspace μ) (hfr μ hμ)`. Use `⟨fun j => (B j : G), fun j => (B j).2, fun v hv => ⟨B.repr ⟨v, hv⟩, ?_⟩⟩` and prove the remaining obligations. Establish `h2` using `congrArg Subtype.val (B.sum_repr ⟨v, hv⟩)`. Move the coercions through the operations in `at h2`.

Conclude with `h2.symm`. Use `choose! b hbmem hbspan using hbasis`. Use `⟨fun j => ∑ μ ∈ R, b μ j, fun v => ?_⟩` and prove the remaining obligations. Establish `hinj : Set.InjOn (id : κ → κ) R` using `Function.injective_id.injOn`. Establish `hpick : ∀ μ ∈ R, ∀ j, aeval T (Lagrange.basis R id μ) (∑ ν ∈ R, b ν j) = b μ j`.

Introduce `μ hμ j`. Rewrite using `[map_sum, Finset.sum_eq_single μ]`. Rewrite using `[hev _ μ _ (hbmem μ hμ j)]`. Use `Lagrange.eval_basis_self hinj hμ` as an intermediate fact. Simplify using `only [id] at this`.

Rewrite using `[this, one_smul]`. Introduce `ν hν hne'`. Rewrite using `[hev _ ν _ (hbmem ν hν j)]`. Use `Lagrange.eval_basis_of_ne (v := id) hne'.symm hν` as an intermediate fact. Simplify using `only [id] at this`.

Rewrite using `[this, zero_smul]`. Introduce `h'`. Conclude with `absurd hμ h'`. Establish `htop : v ∈ ⨆ μ, T.eigenspace μ`. Establish `: (⨆ μ, T.eigenspace μ) = ⊤`.

Rewrite using `[← Module.End.iSup_maxGenEigenspace_eq_top T]`. Conclude with `iSup_congr fun μ => (hgen μ).symm`. Rewrite using `[this]`. Conclude with `Submodule.mem_top`. Proceed by induction on `htop using Submodule.iSup_induction' with`.

Consider the case `mem μ w hw`. Distinguish the cases in `hμ : μ ∈ R`. Take `⟨c, rfl⟩` from `hbspan μ hμ w hw`. Use `⟨fun j => C (c j) * Lagrange.basis R id μ, ?_⟩` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, aeval_C, Module.End.mul_apply, hpick μ hμ j]`. Simplify using `[Module.algebraMap_end_apply]`. Rewrite using `[hout μ hμ w hw]`. Conclude with `⟨0, by simp⟩`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨p, rfl⟩` from `hy`. Take `⟨q, rfl⟩` from `hz`. Use `⟨p + q, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[map_add, Finset.sum_add_distrib]`.
-/
theorem semisimple_charpoly_pow_generators (κ : Type) [Field κ] [IsAlgClosed κ] (G : Type)
    [AddCommGroup G] [Module κ G] [FiniteDimensional κ G] (T : Module.End κ G) (h : κ[X])
    (hm : h.Monic) (hs : h.Separable) (h0 : aeval T h = 0) (N : ℕ)
    (hc : LinearMap.charpoly T = h ^ N) :
    ∃ x : Fin N → G, ∀ v : G, ∃ p : Fin N → κ[X], v = ∑ j, aeval T (p j) (x j) := by
  classical
  have hne : h ≠ 0 := hm.ne_zero
  have hsemi : T.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0
  have hgen : ∀ μ, T.maxGenEigenspace μ = T.eigenspace μ :=
    fun μ => hsemi.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ

  have hev : ∀ (q : κ[X]) (ν : κ) (v : G), v ∈ T.eigenspace ν → aeval T q v = eval ν q • v := by
    intro q ν v hv
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact Module.End.aeval_apply_of_hasEigenvector (Module.End.hasEigenvector_iff.2 ⟨hv, hv0⟩)
  set R : Finset κ := h.roots.toFinset with hR
  have hmemR : ∀ μ, μ ∈ R ↔ h.IsRoot μ := fun μ => by
    rw [hR, Multiset.mem_toFinset, mem_roots hne]

  have hfr : ∀ μ ∈ R, Module.finrank κ (T.eigenspace μ) = N := by
    intro μ hμ
    have hμ' : μ ∈ h.roots := Multiset.mem_toFinset.1 hμ
    rw [← hgen, LinearMap.finrank_maxGenEigenspace_eq, hc, ← count_roots, roots_pow,
      Multiset.count_nsmul, Multiset.count_eq_one_of_mem (nodup_roots hs) hμ', mul_one]

  have hout : ∀ μ, μ ∉ R → ∀ v ∈ T.eigenspace μ, v = 0 := by
    intro μ hμ v hv
    by_contra hv0
    apply hμ
    rw [hmemR]
    have h1 := hev h μ v hv
    rw [h0] at h1
    have h2 : eval μ h • v = 0 := by simpa using h1.symm
    exact (smul_eq_zero.1 h2).resolve_right hv0
  have hbasis : ∀ μ ∈ R, ∃ b : Fin N → G, (∀ j, b j ∈ T.eigenspace μ) ∧
      ∀ v ∈ T.eigenspace μ, ∃ c : Fin N → κ, v = ∑ j, c j • b j := by
    intro μ hμ
    let B := Module.finBasisOfFinrankEq κ (T.eigenspace μ) (hfr μ hμ)
    refine ⟨fun j => (B j : G), fun j => (B j).2, fun v hv => ⟨B.repr ⟨v, hv⟩, ?_⟩⟩
    have h2 := congrArg Subtype.val (B.sum_repr ⟨v, hv⟩)
    push_cast at h2
    exact h2.symm
  choose! b hbmem hbspan using hbasis
  refine ⟨fun j => ∑ μ ∈ R, b μ j, fun v => ?_⟩
  have hinj : Set.InjOn (id : κ → κ) R := Function.injective_id.injOn

  have hpick : ∀ μ ∈ R, ∀ j, aeval T (Lagrange.basis R id μ) (∑ ν ∈ R, b ν j) = b μ j := by
    intro μ hμ j
    rw [map_sum, Finset.sum_eq_single μ]
    · rw [hev _ μ _ (hbmem μ hμ j)]
      have := Lagrange.eval_basis_self hinj hμ
      simp only [id] at this
      rw [this, one_smul]
    · intro ν hν hne'
      rw [hev _ ν _ (hbmem ν hν j)]
      have := Lagrange.eval_basis_of_ne (v := id) hne'.symm hν
      simp only [id] at this
      rw [this, zero_smul]
    · intro h'
      exact absurd hμ h'
  have htop : v ∈ ⨆ μ, T.eigenspace μ := by
    have : (⨆ μ, T.eigenspace μ) = ⊤ := by
      rw [← Module.End.iSup_maxGenEigenspace_eq_top T]
      exact iSup_congr fun μ => (hgen μ).symm
    rw [this]
    exact Submodule.mem_top
  induction htop using Submodule.iSup_induction' with
  | mem μ w hw =>
    by_cases hμ : μ ∈ R
    · obtain ⟨c, rfl⟩ := hbspan μ hμ w hw
      refine ⟨fun j => C (c j) * Lagrange.basis R id μ, ?_⟩
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, aeval_C, Module.End.mul_apply, hpick μ hμ j]
      simp [Module.algebraMap_end_apply]
    · rw [hout μ hμ w hw]
      exact ⟨0, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := hz
    refine ⟨p + q, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [map_add, Finset.sum_add_distrib]

end GlobalTheory
