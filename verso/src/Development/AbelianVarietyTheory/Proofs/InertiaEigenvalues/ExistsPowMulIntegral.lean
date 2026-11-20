import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK

namespace GlobalTheory.IntegralPowerMultiple

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) c`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ`. Use `⟨n, ((u⁻¹ : Oˣ) : O) * a, ?_⟩` and prove the remaining obligations. Establish `hbK : algebraMap O (FractionRing O) b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`.

Establish `hu' : algebraMap O (FractionRing O) (u : O) * algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Rewrite `hbK` using `[hu, map_mul]`. Rewrite using `[hu, map_mul, map_mul]`. Rewrite using `[mul_div_assoc', div_eq_iff hbK]`.

Take the linear combination `(-(algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) (ϖ ^ n))) * hu'`.
-/
theorem exists_pow_mul_integral {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (c : FractionRing O) :
    ∃ (n : ℕ) (a : O), algebraMap O (FractionRing O) (ϖ ^ n) * c = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb

  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, ((u⁻¹ : Oˣ) : O) * a, ?_⟩
  have hbK : algebraMap O (FractionRing O) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hu' : algebraMap O (FractionRing O) (u : O) * algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [hu, map_mul] at hbK
  rw [hu, map_mul, map_mul]
  rw [mul_div_assoc', div_eq_iff hbK]
  linear_combination (-(algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) (ϖ ^ n))) * hu'

/- English proof (translation)
Introduce `O _ _ _ V _ _ _ _ T hT ϖ hϖ v`. Establish `hv : v ∈ Submodule.span (FractionRing O) (T : Set V)` using `by rw [hT.2]; exact Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨0, by simpa using hx⟩`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨m₁, h₁⟩` from `hx`. Take `⟨m₂, h₂⟩` from `hy`. Use `⟨m₁ + m₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, pow_add]`.

Use `T.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `T.smul_mem _ h₁`. Rewrite using `[mul_smul]`. Conclude with `T.smul_mem _ h₂`.

Consider the case `smul c x _ hx`. Take `⟨m, hm⟩` from `hx`. Take `⟨n, a, ha⟩` from `exists_pow_mul_integral hϖ c`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `key : ϖ ^ (n + m) • (c • x) = a • (ϖ ^ m • x)`.

Rewrite using `[← algebraMap_smul (FractionRing O) (ϖ ^ (n + m)) (c • x), smul_smul, ← algebraMap_smul (FractionRing O) a, ← algebraMap_smul (FractionRing O) (ϖ ^ m) x, smul_smul, ← ha, pow_add, map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `T.smul_mem a hm`.
-/
theorem exists_pow_smul_mem : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O] {V : Type} [inst_3 : AddCommGroup V] [inst_4 : Module O V] [inst_5 : Module (FractionRing O) V] [inst_6 : IsScalarTower O (FractionRing O) V] (T : Submodule O V), Formalism.RepresentationBoundsCohomology.LOC.IsLatticeIn T → ∀ (ϖ : O), Irreducible ϖ → ∀ (v : V), ∃ (m : ℕ), ϖ ^ m • v ∈ T := by
  intro O _ _ _ V _ _ _ _ T hT ϖ hϖ v
  have hv : v ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT.2]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    rw [smul_add, pow_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem _ h₁
    · rw [mul_smul]
      exact T.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx

    obtain ⟨n, a, ha⟩ := exists_pow_mul_integral hϖ c
    refine ⟨n + m, ?_⟩
    have key : ϖ ^ (n + m) • (c • x) = a • (ϖ ^ m • x) := by
      rw [← algebraMap_smul (FractionRing O) (ϖ ^ (n + m)) (c • x), smul_smul,
        ← algebraMap_smul (FractionRing O) a, ← algebraMap_smul (FractionRing O) (ϖ ^ m) x, smul_smul,
        ← ha, pow_add, map_mul]
      congr 1
      ring
    rw [key]
    exact T.smul_mem a hm

end GlobalTheory.IntegralPowerMultiple
