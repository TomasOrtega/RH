import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightIntegralEstimates
import ReciprocityTheory.SemistableReduction.AlgAll

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.AlgT

/- English proof (translation)
Use function extensionality and compare the values at `p`. Take `⟨i, j⟩` from `p`. Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using `[ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]`. Simplify using `[ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]`.
-/
theorem genericSection_reindex {F : Type} [Field F] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → F) :
    ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x = sImg (D := D) j₀ x ∘
      (Equiv.prodCongr (Equiv.refl (Fin (D + 1))) (Fin.cycleRange j₀).symm) := by
  funext p
  obtain ⟨i, j⟩ := p
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
  · simp [ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]

/- English proof (translation)
Take `⟨hind, hfin⟩` from `ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS k F D N x hfg htr hJ`. Rewrite `hind`, `hfin` using `[genericSection_reindex j₀ x]`. Rewrite `hfin` using `[(Equiv.surjective _).range_comp]`. Use `⟨(algebraicIndependent_equiv _).1 hind, hfin, ?_⟩` and prove the remaining obligations. Establish `: FiniteDimensional (IntermediateField.adjoin k (Set.range (sImg (D` using `D) j₀ x))) (OmS F D N) := hfin`.

Establish `: CharZero (IntermediateField.adjoin k (Set.range (sImg (D` using `D) j₀ x))) := charZero_of_injective_algebraMap (algebraMap k _).injective`. Use `infer_instance`.
-/
theorem genericSection_field {k F : Type} [Field k] [CharZero k] [Field F] [Algebra k F] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → F) (hfg : (⊤ : IntermediateField k F).FG)
    (htr : Algebra.trdeg k F = D)
    (hJ : ∃ J : Fin D → Fin N, LinearIndependent F fun a => KaehlerDifferential.D k F (x (J a))) :
    AlgebraicIndependent k (sImg (D := D) j₀ x) ∧
      FiniteDimensional (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x))) (OmS F D N) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x)))
        (OmS F D N) := by
  obtain ⟨hind, hfin⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS k F D N x hfg htr hJ
  rw [genericSection_reindex j₀ x] at hind hfin
  rw [(Equiv.surjective _).range_comp] at hfin
  refine ⟨(algebraicIndependent_equiv _).1 hind, hfin, ?_⟩
  have : FiniteDimensional (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x)))
    (OmS F D N) := hfin
  have : CharZero (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x))) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  infer_instance

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

end GlobalTheory
