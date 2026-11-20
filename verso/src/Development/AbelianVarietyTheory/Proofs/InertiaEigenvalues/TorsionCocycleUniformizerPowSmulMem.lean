import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.TorsCoc

/- English proof (translation)
Establish `hv : v ∈ Submodule.span LL (T : Set V)` using `hT ▸ Submodule.mem_top`. Establish `up : ∀ (x : V) (k j : ℕ), k ≤ j → (algebraMap O LL ϖ) ^ k • x ∈ T → (algebraMap O LL ϖ) ^ j • x ∈ T`. Introduce `x k j hkj hx`. Take `⟨i, rfl⟩` from `Nat.exists_eq_add_of_le hkj`. Rewrite using `[pow_add, mul_comm, mul_smul, ← map_pow, algebraMap_smul]`.

Conclude with `T.smul_mem _ hx`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨0, fun j _ => by rw [← map_pow, algebraMap_smul]; exact T.smul_mem _ hx⟩`. Consider the case `zero => exact ⟨0, fun j _ => by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨max a b, fun j hj => by`. Rewrite using `[smul_add]`. Conclude with `T.add_mem (ha j (le_trans (le_max_left _ _) hj)) (hb j (le_trans (le_max_right _ _) hj))⟩`.

Consider the case `smul a x _ hx`. Take `⟨k, hk⟩` from `hx`. Take `⟨b, s, hs, rfl⟩` from `IsFractionRing.div_surjective (A := O) a`. Establish `hs0 : s ≠ 0` using `nonZeroDivisors.ne_zero hs`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ`.

Use `⟨n + k, fun j hj => up _ (n + k) j hj ?_⟩` and prove the remaining obligations. Establish `key : (algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s) = algebraMap O LL (b * ((u⁻¹ : Oˣ) : O))`. Establish `hsne : algebraMap O LL s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs`. Rewrite using `[mul_div_assoc', div_eq_iff hsne, hu]`. Simplify using `only [map_mul, map_pow]`.

Establish `hu1 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * algebraMap O LL (u : O) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Take the linear combination `(-(algebraMap O LL b * algebraMap O LL ϖ ^ n)) * hu1`. Establish `e : (algebraMap O LL ϖ) ^ (n + k) • ((algebraMap O LL b / algebraMap O LL s) • x) = ((algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s)) • ((algebraMap O LL ϖ) ^ k • x)`. Rewrite using `[pow_add, mul_smul, mul_smul, smul_comm (algebraMap O LL b / algebraMap O LL s)]`.

Rewrite using `[e, key, algebraMap_smul]`. Conclude with `T.smul_mem _ (hk k le_rfl)`.
-/
theorem exists_pow_smul_mem {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O LL] [IsFractionRing O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (hT : Submodule.span LL (T : Set V) = ⊤) (ϖ : O) (hϖ : Irreducible ϖ)
    (v : V) : ∃ k : ℕ, ∀ j, k ≤ j → (algebraMap O LL ϖ) ^ j • v ∈ T := by
  have hv : v ∈ Submodule.span LL (T : Set V) := hT ▸ Submodule.mem_top

  have up : ∀ (x : V) (k j : ℕ), k ≤ j → (algebraMap O LL ϖ) ^ k • x ∈ T →
      (algebraMap O LL ϖ) ^ j • x ∈ T := by
    intro x k j hkj hx
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
    rw [pow_add, mul_comm, mul_smul, ← map_pow, algebraMap_smul]
    exact T.smul_mem _ hx
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, fun j _ => by rw [← map_pow, algebraMap_smul]; exact T.smul_mem _ hx⟩
  | zero => exact ⟨0, fun j _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, fun j hj => by
      rw [smul_add]
      exact T.add_mem (ha j (le_trans (le_max_left _ _) hj)) (hb j (le_trans (le_max_right _ _) hj))⟩
  | smul a x _ hx =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨b, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) a
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
    refine ⟨n + k, fun j hj => up _ (n + k) j hj ?_⟩
    have key : (algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s) =
        algebraMap O LL (b * ((u⁻¹ : Oˣ) : O)) := by
      have hsne : algebraMap O LL s ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      rw [mul_div_assoc', div_eq_iff hsne, hu]
      simp only [map_mul, map_pow]
      have hu1 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * algebraMap O LL (u : O) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(algebraMap O LL b * algebraMap O LL ϖ ^ n)) * hu1
    have e : (algebraMap O LL ϖ) ^ (n + k) • ((algebraMap O LL b / algebraMap O LL s) • x) =
        ((algebraMap O LL ϖ) ^ n * (algebraMap O LL b / algebraMap O LL s)) •
          ((algebraMap O LL ϖ) ^ k • x) := by
      rw [pow_add, mul_smul, mul_smul, smul_comm (algebraMap O LL b / algebraMap O LL s)]
    rw [e, key, algebraMap_smul]
    exact T.smul_mem _ (hk k le_rfl)

/- English proof (translation)
Introduce `l _ K LL _ _ _ O _ _ hO A' LA' ϖ hϖ c hc`. Take `⟨⟨hD, hDVR, hFR⟩, -⟩` from `hO`. Use `haveI : CompactSpace ↥(GK K) := by haveI := K.2`. Conclude with `isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact`. Establish `hfin : (Set.range c).Finite` using `hc.1.range_finite`.

Use `choose f hf using fun y : A'.V ⧸ LA'.T => exists_pow_smul_mem LA'.T LA'.span ϖ hϖ (liftD LA' y)`. Use `⟨hfin.toFinset.sup f, fun g => hf (c g) _ ?_⟩` and prove the remaining obligations. Conclude with `Finset.le_sup (f := f) (hfin.mem_toFinset.2 ⟨g, rfl⟩)`.
-/
theorem cocycle_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL],
    GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ)
    (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', ∃ r : ℕ, ∀ g,
    (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T := by
  intro l _ K LL _ _ _ O _ _ hO A' LA' ϖ hϖ c hc
  obtain ⟨⟨hD, hDVR, hFR⟩, -⟩ := hO
  haveI : CompactSpace ↥(GK K) := by
    haveI := K.2
    exact isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact
  have hfin : (Set.range c).Finite := hc.1.range_finite
  choose f hf using fun y : A'.V ⧸ LA'.T =>
    exists_pow_smul_mem LA'.T LA'.span ϖ hϖ (liftD LA' y)
  refine ⟨hfin.toFinset.sup f, fun g => hf (c g) _ ?_⟩
  exact Finset.le_sup (f := f) (hfin.mem_toFinset.2 ⟨g, rfl⟩)

end GlobalTheory.TorsCoc
