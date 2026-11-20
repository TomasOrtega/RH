import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

namespace GlobalTheory.LieSmooth

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨d₁, hd₁, h₁⟩` from `hy`.

Take `⟨d₂, hd₂, h₂⟩` from `hz`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Establish `e1 : (d₁ * d₂) • y = d₂ • (d₁ • y)` using `by rw [mul_comm, mul_smul]`. Establish `e2 : (d₁ * d₂) • z = d₁ • (d₂ • z)` using `by rw [mul_smul]`. Rewrite using `[smul_add, e1, e2]`.

Conclude with `E.add_mem (E.smul_mem _ h₁) (E.smul_mem _ h₂)`. Consider the case `smul c y _ hy`. Take `⟨d, hd, h⟩` from `hy`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) c`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`.

Establish `hbK : (algebraMap (𝓞 K) K b) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Use `⟨b * d, mul_ne_zero hb0 hd, ?_⟩` and prove the remaining obligations. Establish `key : (b * d) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • y) = a • (d • y)`. Rewrite using `[← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d, smul_smul, smul_smul]`. Use `congr 1`.

Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `E.smul_mem _ h`.
-/
theorem exists_ne_zero_smul_mem_of_mem_kspan {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (E : Submodule (𝓞 K) V) (x : V)
    (hx : x ∈ Submodule.span K (E : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ E := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e1 : (d₁ * d₂) • y = d₂ • (d₁ • y) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • z = d₁ • (d₂ • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact E.add_mem (E.smul_mem _ h₁) (E.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (algebraMap (𝓞 K) K b) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have key : (b * d) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • y) = a • (d • y) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d,
        smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact E.smul_mem _ h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Take `⟨g, hg⟩` from `LinearMap.exists_extend ((Module.Basis.span hv).coord i)`. Establish `hgv : ∀ k, g (v k) = if k = i then 1 else 0`. Introduce `k`. Establish `h1 : g (v k) = (Module.Basis.span hv).coord i (Module.Basis.span hv k)`.

Rewrite using `[← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]`. Rewrite using `[h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Use `Submodule.FG.of_le (hE.map (g.restrictScalars (𝓞 K))) ?_` and prove the remaining obligations. Introduce and unpack `a ⟨c, rfl, hc, hmem⟩`. Use `⟨_, hmem, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.restrictScalars_apply, map_sum]`. Simplify using `only [map_smul, hgv, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `hvi : v i ∈ Submodule.span K (E : Set V)` using `hspan (Submodule.subset_span ⟨i, rfl⟩)`. Take `⟨d, hd, hdE⟩` from `exists_ne_zero_smul_mem_of_mem_kspan E (v i) hvi`. Introduce `hbot`.

Establish `hmem : algebraMap (𝓞 K) K d ∈ grIdeal E v i`. Use `⟨Pi.single i (algebraMap (𝓞 K) K d), by simp, fun k hk => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Pi.single_apply, (ne_of_lt hk).symm]`. Rewrite using `[Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]`. Simplify `hdE` using `[algebraMap_smul]`.

Rewrite `hmem` using `[hbot, Submodule.mem_bot]`. Conclude with `hd (by simpa using hmem)`.
-/
theorem grIdeal_fg_ne_bot (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (E : Submodule (𝓞 K) V) (r : ℕ) (v : Fin r → V) (i : Fin r)
    (hE : E.FG) (hv : LinearIndependent K v)
    (hspan : Submodule.span K (Set.range v) ≤ Submodule.span K (E : Set V)) :
    (grIdeal E v i).FG ∧ grIdeal E v i ≠ ⊥ := by
  constructor
  · obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord i)
    have hgv : ∀ k, g (v k) = if k = i then 1 else 0 := by
      intro k
      have h1 : g (v k) = (Module.Basis.span hv).coord i (Module.Basis.span hv k) := by
        rw [← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
      rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    refine Submodule.FG.of_le (hE.map (g.restrictScalars (𝓞 K))) ?_
    rintro a ⟨c, rfl, hc, hmem⟩
    refine ⟨_, hmem, ?_⟩
    rw [LinearMap.restrictScalars_apply, map_sum]
    simp only [map_smul, hgv, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hvi : v i ∈ Submodule.span K (E : Set V) := hspan (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨d, hd, hdE⟩ := exists_ne_zero_smul_mem_of_mem_kspan E (v i) hvi
    intro hbot
    have hmem : algebraMap (𝓞 K) K d ∈ grIdeal E v i := by
      refine ⟨Pi.single i (algebraMap (𝓞 K) K d), by simp, fun k hk => ?_, ?_⟩
      · simp [Pi.single_apply, (ne_of_lt hk).symm]
      · rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
        simpa [algebraMap_smul] using hdE
    rw [hbot, Submodule.mem_bot] at hmem
    exact hd (by simpa using hmem)

end GlobalTheory.LieSmooth
