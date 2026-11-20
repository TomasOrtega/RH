import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

/- English proof (translation)
Introduce `Ω _ _ A g hg hg0 e z z' hz hli hsp`. Establish `hAB : A ≤ Mdl.invAdj A g` using `fun x hx => show x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)`. Establish `hginv : g⁻¹ ∈ Mdl.invAdj A g` using `show g⁻¹ ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from Algebra.subset_adjoin (Set.mem_insert _ _)`. Establish `hden : ∀ x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)), ∃ n : ℕ, x * g ^ n ∈ A`. Set `S : Subalgebra ℚ Ω` to `{ carrier := {x | ∃ n : ℕ, x * g ^ n ∈ A} mul_mem' := by`.

Introduce and unpack `x y ⟨n, hn⟩ ⟨m, hm⟩`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Rewrite using `[show x * y * g ^ (n + m) = (x * g ^ n) * (y * g ^ m) by ring]`. Conclude with `A.mul_mem hn hm`. Use the proof step `one_mem' := ⟨0, by simpa using A.one_mem⟩`.

Use the proof step `add_mem' := by`. Introduce and unpack `x y ⟨n, hn⟩ ⟨m, hm⟩`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Rewrite using `[show (x + y) * g ^ (n + m) = (x * g ^ n) * g ^ m + (y * g ^ m) * g ^ n by ring]`. Conclude with `A.add_mem (A.mul_mem hn (A.pow_mem hg m)) (A.mul_mem hm (A.pow_mem hg n))`.

Use the proof step `zero_mem' := ⟨0, by simpa using A.zero_mem⟩`. Use the proof step `algebraMap_mem' := fun r => ⟨0, by simpa using A.algebraMap_mem r⟩ }`. Establish `hle : Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) ≤ S`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce `x hx`.

Break down `hx with rfl | hx` into its components or cases. Conclude with `⟨1, by rw [pow_one, inv_mul_cancel₀ hg0]; exact A.one_mem⟩`. Conclude with `⟨0, by simpa using hx⟩`. Conclude with `fun x hx => hle hx`. Use `letI : Algebra A (Mdl.invAdj A g) := (Subalgebra.inclusion hAB).toRingHom.toAlgebra`.

Establish `hinc : ∀ a : A, ((algebraMap A (Mdl.invAdj A g) a : Mdl.invAdj A g) : Ω) = a` using `fun _ => rfl`. Use `haveI : IsScalarTower ℚ A (Mdl.invAdj A g) := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)`. Set `g' : A` to `⟨g, hg⟩`. Use `haveI : IsLocalization (Submonoid.powers g') (Mdl.invAdj A g) := by`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨y, n, rfl⟩`. Establish `hu : IsUnit (algebraMap A (Mdl.invAdj A g) g')` using `isUnit_iff_exists_inv.mpr ⟨⟨g⁻¹, hginv⟩, Subtype.ext (by show g * g⁻¹ = 1`. Conclude with `mul_inv_cancel₀ hg0)⟩`. Use `show IsUnit (algebraMap A (Mdl.invAdj A g) (g' ^ n))`. Rewrite using `[map_pow]`.

Conclude with `hu.pow n`. Introduce `b`. Take `⟨n, hn⟩` from `hden b b.2`. Use `⟨(⟨(b : Ω) * g ^ n, hn⟩, ⟨g' ^ n, n, rfl⟩), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show (b : Ω) * ((g' ^ n : A) : Ω) = (b : Ω) * g ^ n`. Simplify using `only [SubmonoidClass.coe_pow]`. Both sides reduce to the same expression. Introduce `x y h`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Establish `hxy : x = y` using `Subtype.ext (by simpa [hinc] using congrArg Subtype.val h)`. Rewrite using `[hxy]`. Use `haveI : Algebra.FormallyEtale A (Mdl.invAdj A g) := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g')`. Establish `hzz : ∀ i, algebraMap A (Mdl.invAdj A g) (z i) = z' i` using `fun i => Subtype.ext ((hinc (z i)).trans (hz i).symm)`. Establish `key` using `GlobalTheory.CompanionTheory.Ar.SncRes.coords_of_formallyEtale (S := ↥(Mdl.invAdj A g)) z hli hsp`.

Simplify using `only [hzz] at key`. Conclude with `key`.
-/
theorem differentials_basis_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 → ∀ (e : ℕ) (z : Fin e → A) (z' : Fin e → Mdl.invAdj A g), (∀ i, (z' i : Ω) = z i) → LinearIndependent A (fun i => KaehlerDifferential.D ℚ A (z i)) → Submodule.span A (Set.range fun i => KaehlerDifferential.D ℚ A (z i)) = ⊤ → LinearIndependent (Mdl.invAdj A g) (fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) ∧ Submodule.span (Mdl.invAdj A g) (Set.range fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) = ⊤ := by
  intro Ω _ _ A g hg hg0 e z z' hz hli hsp
  have hAB : A ≤ Mdl.invAdj A g := fun x hx =>
    show x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from
      Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
  have hginv : g⁻¹ ∈ Mdl.invAdj A g :=
    show g⁻¹ ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from
      Algebra.subset_adjoin (Set.mem_insert _ _)
  have hden : ∀ x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)), ∃ n : ℕ, x * g ^ n ∈ A := by
    let S : Subalgebra ℚ Ω :=
      { carrier := {x | ∃ n : ℕ, x * g ^ n ∈ A}
        mul_mem' := by
          rintro x y ⟨n, hn⟩ ⟨m, hm⟩
          refine ⟨n + m, ?_⟩
          rw [show x * y * g ^ (n + m) = (x * g ^ n) * (y * g ^ m) by ring]
          exact A.mul_mem hn hm
        one_mem' := ⟨0, by simpa using A.one_mem⟩
        add_mem' := by
          rintro x y ⟨n, hn⟩ ⟨m, hm⟩
          refine ⟨n + m, ?_⟩
          rw [show (x + y) * g ^ (n + m) = (x * g ^ n) * g ^ m + (y * g ^ m) * g ^ n by ring]
          exact A.add_mem (A.mul_mem hn (A.pow_mem hg m)) (A.mul_mem hm (A.pow_mem hg n))
        zero_mem' := ⟨0, by simpa using A.zero_mem⟩
        algebraMap_mem' := fun r => ⟨0, by simpa using A.algebraMap_mem r⟩ }
    have hle : Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) ≤ S := by
      refine Algebra.adjoin_le ?_
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hg0]; exact A.one_mem⟩
      · exact ⟨0, by simpa using hx⟩
    exact fun x hx => hle hx
  letI : Algebra A (Mdl.invAdj A g) := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  have hinc : ∀ a : A, ((algebraMap A (Mdl.invAdj A g) a : Mdl.invAdj A g) : Ω) = a := fun _ => rfl
  haveI : IsScalarTower ℚ A (Mdl.invAdj A g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let g' : A := ⟨g, hg⟩
  haveI : IsLocalization (Submonoid.powers g') (Mdl.invAdj A g) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      have hu : IsUnit (algebraMap A (Mdl.invAdj A g) g') :=
        isUnit_iff_exists_inv.mpr ⟨⟨g⁻¹, hginv⟩, Subtype.ext (by
          show g * g⁻¹ = 1
          exact mul_inv_cancel₀ hg0)⟩
      show IsUnit (algebraMap A (Mdl.invAdj A g) (g' ^ n))
      rw [map_pow]
      exact hu.pow n
    · intro b
      obtain ⟨n, hn⟩ := hden b b.2
      refine ⟨(⟨(b : Ω) * g ^ n, hn⟩, ⟨g' ^ n, n, rfl⟩), ?_⟩
      apply Subtype.ext
      show (b : Ω) * ((g' ^ n : A) : Ω) = (b : Ω) * g ^ n
      simp only [SubmonoidClass.coe_pow]
      rfl
    · intro x y h
      refine ⟨1, ?_⟩
      have hxy : x = y := Subtype.ext (by simpa [hinc] using congrArg Subtype.val h)
      rw [hxy]
  haveI : Algebra.FormallyEtale A (Mdl.invAdj A g) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g')
  have hzz : ∀ i, algebraMap A (Mdl.invAdj A g) (z i) = z' i := fun i =>
    Subtype.ext ((hinc (z i)).trans (hz i).symm)
  have key := GlobalTheory.CompanionTheory.Ar.SncRes.coords_of_formallyEtale (S := ↥(Mdl.invAdj A g)) z hli hsp
  simp only [hzz] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
