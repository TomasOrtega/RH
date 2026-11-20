import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSumSmulSeparatingInertia

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `Γ _ _ B _ _ N _ _ _ hsemi q hq hcard htriv x`. Establish `: Fintype Γ` using `Fintype.ofFinite Γ`. Take `⟨n, c, d, s, hs, hsep⟩` from `exists_sum_smul_separating_inertia Γ B q hq`. Use `⟨(Nat.card (q.inertia Γ) : B) * s, fun h => (hq.mem_or_mem h).elim hcard hs, ?_⟩` and prove the remaining obligations. Establish `hinv : ∀ j, (∑ g : Γ, g • (c j • x)) ∈ {y : N | ∀ g : Γ, g • y = y}`.

Introduce `j h`. Rewrite using `[Finset.smul_sum]`. Simplify using `only [smul_smul]`. Conclude with `Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)`. Take `⟨z, hzdef⟩ : ∃ z : N, z = ∑ j, d j • ∑ g : Γ, g • (c j • x)` from `⟨_, rfl⟩`.

Establish `hz : z ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y}`. Rewrite using `[hzdef]`. Conclude with `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hinv j)))`. Establish `hz' : z = ∑ g : Γ, (∑ j, d j * g • c j) • (g • x)`. Rewrite using `[hzdef]`.

Simplify using `only [Finset.smul_sum, hsemi, smul_smul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Establish `hc : Nat.card (q.inertia Γ) = (Finset.univ.filter (fun g : Γ => g ∈ q.inertia Γ)).card`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `Fintype.card_subtype _`.

Establish `hsumI : ((Nat.card (q.inertia Γ) : B) * s) • x = ∑ g : Γ, if g ∈ q.inertia Γ then s • x else 0`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, hc, ← Nat.cast_smul_eq_nsmul B, smul_smul]`. Establish `hdiff : z - ((Nat.card (q.inertia Γ) : B) * s) • x ∈ q • (⊤ : Submodule B N)`. Rewrite using `[hz', hsumI, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ (fun g _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hg : g ∈ q.inertia Γ`. Rewrite using `[if_pos hg]`. Establish `e : (∑ j, d j * g • c j) • (g • x) - s • x = ((∑ j, d j * g • c j) - s) • (g • x) + s • (g • x - x)`. Rewrite using `[sub_smul, smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem_smul ((hsep g).1 hg) Submodule.mem_top) (Submodule.smul_mem _ s (htriv g hg x))`. Rewrite using `[if_neg hg, sub_zero]`. Conclude with `Submodule.smul_mem_smul ((hsep g).2 hg) Submodule.mem_top`. Establish `key` using `Submodule.sub_mem _ (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hdiff)`.

Rewrite `key` using `[sub_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem exists_smul_mem_span_invariants_sup :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B] (N : Type)
      [AddCommGroup N] [Module B N] [DistribMulAction Γ N],
      (∀ (g : Γ) (b : B) (x : N), g • (b • x) = (g • b) • (g • x)) → ∀ q : Ideal B, q.IsPrime →
      (Nat.card (q.inertia Γ) : B) ∉ q →
      (∀ g ∈ q.inertia Γ, ∀ x : N, g • x - x ∈ q • (⊤ : Submodule B N)) →
      ∀ x : N, ∃ s : B, s ∉ q ∧
        s • x ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} ⊔ q • (⊤ : Submodule B N) := by
  intro Γ _ _ B _ _ N _ _ _ hsemi q hq hcard htriv x
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨n, c, d, s, hs, hsep⟩ := exists_sum_smul_separating_inertia Γ B q hq

  refine ⟨(Nat.card (q.inertia Γ) : B) * s, fun h => (hq.mem_or_mem h).elim hcard hs, ?_⟩

  have hinv : ∀ j, (∑ g : Γ, g • (c j • x)) ∈ {y : N | ∀ g : Γ, g • y = y} := by
    intro j h
    rw [Finset.smul_sum]
    simp only [smul_smul]
    exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)
  obtain ⟨z, hzdef⟩ : ∃ z : N, z = ∑ j, d j • ∑ g : Γ, g • (c j • x) := ⟨_, rfl⟩
  have hz : z ∈ Submodule.span B {y : N | ∀ g : Γ, g • y = y} := by
    rw [hzdef]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hinv j)))
  have hz' : z = ∑ g : Γ, (∑ j, d j * g • c j) • (g • x) := by
    rw [hzdef]
    simp only [Finset.smul_sum, hsemi, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc : Nat.card (q.inertia Γ) = (Finset.univ.filter (fun g : Γ => g ∈ q.inertia Γ)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hsumI : ((Nat.card (q.inertia Γ) : B) * s) • x
      = ∑ g : Γ, if g ∈ q.inertia Γ then s • x else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, hc, ← Nat.cast_smul_eq_nsmul B, smul_smul]

  have hdiff : z - ((Nat.card (q.inertia Γ) : B) * s) • x ∈ q • (⊤ : Submodule B N) := by
    rw [hz', hsumI, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ (fun g _ => ?_)
    by_cases hg : g ∈ q.inertia Γ
    · rw [if_pos hg]
      have e : (∑ j, d j * g • c j) • (g • x) - s • x
          = ((∑ j, d j * g • c j) - s) • (g • x) + s • (g • x - x) := by
        rw [sub_smul, smul_sub]; abel
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul ((hsep g).1 hg) Submodule.mem_top)
        (Submodule.smul_mem _ s (htriv g hg x))
    · rw [if_neg hg, sub_zero]
      exact Submodule.smul_mem_smul ((hsep g).2 hg) Submodule.mem_top
  have key := Submodule.sub_mem _ (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hdiff)
  rwa [sub_sub_cancel] at key

end GlobalTheory
