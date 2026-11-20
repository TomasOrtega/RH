import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq

namespace GlobalTheory.NatSmulMemLattice

open NumberField

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨y, hy0, hy⟩` from `halg.exists_integral_multiple`. Establish `h2 : IsIntegral ℤ ((y : E) * (y • c))`. Establish `h3 : IsIntegral ℤ (y : E)`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := E) (x := y))`.

Conclude with `h3.mul hy`. Use `⟨y.natAbs * y.natAbs, ⟨_, h2⟩, ?_, ?_⟩` and prove the remaining obligations. Use `Int.natAbs_pos.2 hy0` as an intermediate fact. Check the signs of the components of the expression. Establish `h4 : ((y.natAbs * y.natAbs : ℕ) : E) = (y : E) * (y : E)`.

Establish `h5 : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y` using `Int.natAbs_mul_self`. Establish `h6` using `congrArg (Int.cast : ℤ → E) h5`. Rewrite `h6` using `[Int.cast_natCast, Int.cast_mul]`. Conclude with `h6`. Rewrite using `[h4]`.

Express the relevant statement in the definitionally equal form `(y : E) * (y • c) = _`. Rewrite using `[zsmul_eq_mul, mul_assoc]`.
-/
theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ (n : ℕ) (a : 𝓞 E), 0 < n ∧ (a : E) = (n : E) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  have h2 : IsIntegral ℤ ((y : E) * (y • c)) := by
    have h3 : IsIntegral ℤ (y : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := y))
    exact h3.mul hy
  refine ⟨y.natAbs * y.natAbs, ⟨_, h2⟩, ?_, ?_⟩
  · have := Int.natAbs_pos.2 hy0
    positivity
  · have h4 : ((y.natAbs * y.natAbs : ℕ) : E) = (y : E) * (y : E) := by
      have h5 : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
      have h6 := congrArg (Int.cast : ℤ → E) h5
      rw [Int.cast_natCast, Int.cast_mul] at h6
      exact h6
    rw [h4]
    change (y : E) * (y • c) = _
    rw [zsmul_eq_mul, mul_assoc]

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (L : Set W)` using `hL ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hx⟩` from `hx`. Take `⟨b, hb, hy⟩` from `hy`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, Nat.cast_mul]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem _ hx`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem _ hy`. Consider the case `smul c x _ hx`.

Take `⟨a, ha, hx⟩` from `hx`. Take `⟨n, e, hn, he⟩` from `exists_nat_mul_integral c`. Use `⟨a * n, Nat.mul_pos ha hn, ?_⟩` and prove the remaining obligations. Establish `key : ((a * n : ℕ) : 𝓞 E) • c • x = e • (a : 𝓞 E) • x`. Rewrite using `[← algebraMap_smul E e, ← algebraMap_smul E (a : 𝓞 E), ← algebraMap_smul E ((a * n : ℕ) : 𝓞 E), smul_smul, smul_smul]`.

Use `congr 1`. Establish `he' : algebraMap (𝓞 E) E e = (n : E) * c` using `he`. Rewrite using `[he', map_natCast, map_natCast, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `L.smul_mem _ hx`.
-/
theorem exists_nat_smul_mem {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (L : Submodule (𝓞 E) W)
    (hL : Submodule.span E (L : Set W) = ⊤) (v : W) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 E) • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set W) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨n, e, hn, he⟩ := exists_nat_mul_integral c
    refine ⟨a * n, Nat.mul_pos ha hn, ?_⟩
    have key : ((a * n : ℕ) : 𝓞 E) • c • x = e • (a : 𝓞 E) • x := by
      rw [← algebraMap_smul E e, ← algebraMap_smul E (a : 𝓞 E),
        ← algebraMap_smul E ((a * n : ℕ) : 𝓞 E), smul_smul, smul_smul]
      congr 1
      have he' : algebraMap (𝓞 E) E e = (n : E) * c := he
      rw [he', map_natCast, map_natCast, Nat.cast_mul]
      ring
    rw [key]
    exact L.smul_mem _ hx

/- English proof (translation)
The claim follows from `exists_nat_smul_mem _ V.standardTuple_isLattice.span_eq_top v`.
-/
theorem exists_nat_smul_mem_lattice {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (v : Formalism.BasicNotions.HSpace.V V) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 (Formalism.BasicNotions.D7.host D).E) • v ∈ Formalism.BasicNotions.HSpace.L0 V :=
  exists_nat_smul_mem _ V.standardTuple_isLattice.span_eq_top v

end GlobalTheory.NatSmulMemLattice
