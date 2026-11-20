import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SgDistribution
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

noncomputable section

namespace GlobalTheory.KZDist

/- English proof (translation)
Take `⟨hc1, hc6, hnot⟩` from `hA`. Use `⟨hc1, hc6, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨k, hk⟩, ⟨l, hl⟩⟩`. Establish `hmQ : (m : ℚ) ≠ 0` using `by exact_mod_cast hm.ne'`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk hl`.

Apply `hnot` to reduce the goal to its premises. Use `⟨⟨m * k - c * a, ?_⟩, ⟨m * l - c * b, ?_⟩⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[hk]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Use `push_cast`. Rewrite using `[hl]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma isAdmissibleSmoothingFactor_divided_indices (c m : ℕ) (x : Fin 2 → ℚ) (a b : ℕ) (hA : admitted c x) (hm : 0 < m) :
    admitted c ![(x 0 + a) / m, (x 1 + b) / m] := by
  obtain ⟨hc1, hc6, hnot⟩ := hA
  refine ⟨hc1, hc6, ?_⟩
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk hl
  apply hnot
  refine ⟨⟨m * k - c * a, ?_⟩, ⟨m * l - c * b, ?_⟩⟩
  · push_cast; rw [hk]; field_simp; ring
  · push_cast; rw [hl]; field_simp; ring

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_im`.
-/
lemma isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

/- English proof (translation)
Rewrite using `[← Filter.forall_mem_nonempty_iff_neBot]`. Introduce `s hs`. Establish `hI : Complex.I ∈ Hs` using `by simp [Hs]`. Establish `h1` using `(mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs) _ hI`. Establish `h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ` using `mem_nhdsWithin_of_mem_nhds (isOpen_Hs'.mem_nhds hI)`.

Take `⟨z, hz1, hz2⟩` from `Filter.nonempty_of_mem (Filter.inter_mem h1 h2)`. Break down `hz1 with h | h` into its components or cases. Conclude with `⟨z, h⟩`. Conclude with `absurd hz2 h`.
-/
lemma codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [← Filter.forall_mem_nonempty_iff_neBot]
  intro s hs
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs) _ hI
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs'.mem_nhds hI)
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  rcases hz1 with h | h
  · exact ⟨z, h⟩
  · exact absurd hz2 h

/- English proof (translation)
Introduce `Ω _ _ _ ε T c m x hA hm hcm`. Use `haveI := codiscreteWithin_Hs_neBot`. Apply `T.an.injective` to reduce the goal to its premises. Rewrite using `[map_prod, GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hA]`. Repeatedly rewrite using `[map_prod]`.

Establish `h1 : ∀ a ∈ Finset.range m, ∏ b ∈ Finset.range m, T.an (siegel T c ![(x 0 + a) / m, (x 1 + b) / m]) = Filter.Germ.coeRingHom _ (∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m])`. Introduce `a _`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c _ (isAdmissibleSmoothingFactor_divided_indices c m x a b hA hm)]`.

Both sides reduce to the same expression. Rewrite using `[Finset.prod_congr rfl h1, ← map_prod]`. Use `show ((∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m] : ℂ → ℂ) : Mero) = _`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Simplify using `only [Finset.prod_apply]`. Conclude with `GlobalTheory.SiegDist.sg_distribution c m x _ hA hm hcm`.
-/
theorem siegel_distribution : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (m : ℕ) (x : Fin 2 → ℚ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, siegel T c ![(x 0 + a) / m, (x 1 + b) / m] = siegel T c x := by
  intro Ω _ _ _ ε T c m x hA hm hcm
  haveI := codiscreteWithin_Hs_neBot
  apply T.an.injective
  rw [map_prod, GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hA]
  simp_rw [map_prod]
  have h1 : ∀ a ∈ Finset.range m, ∏ b ∈ Finset.range m, T.an (siegel T c ![(x 0 + a) / m, (x 1 + b) / m])
      = Filter.Germ.coeRingHom _ (∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m]) := by
    intro a _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c _ (isAdmissibleSmoothingFactor_divided_indices c m x a b hA hm)]
    rfl
  rw [Finset.prod_congr rfl h1, ← map_prod]
  show ((∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m] : ℂ → ℂ) : Mero) = _
  congr 1
  funext z
  simp only [Finset.prod_apply]
  exact GlobalTheory.SiegDist.sg_distribution c m x _ hA hm hcm

end GlobalTheory.KZDist
