import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `g hg`. Establish `hg' : g * k = k * g` using `mem_cent.1 hg`. Establish `h1 : ujMat ε g * ujMat ε k = ujMat ε k * ujMat ε g`. Rewrite using `[← map_mul, ← map_mul, hg']`. Establish `h2 : Jm ε * ujMat ε k = ujMat ε k * Jm ε` using `hk.2.symm`.

Establish `hJ : ujMat ε g * Jm ε = Jm ε * ujMat ε g` using `hr.commute h1 h2`. Establish `hU : (ujMat ε g)ᴴ * Jm ε * ujMat ε g = Jm ε` using `g.2`. Establish `hJJ` using `Formalism.REAL.Jm_mul_self ε`. Use `⟨?_, hJ⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`.

Express the relevant statement in the definitionally equal form `(ujMat ε g)ᴴ * ujMat ε g = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc (ujMat ε g)ᴴ (Jm ε * Jm ε), Matrix.mul_assoc (Jm ε), ← hJ]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hU, hJJ]`.
-/
theorem cent_subset_KG_of_regSS {n : ℕ} {ε : Fin n → Bool} {k : UJ ε} (hk : k ∈ KG ε)
    (hr : IsRegSS (ujMat ε k)) : (cent k : Set (UJ ε)) ⊆ (KG ε : Set (UJ ε)) := by
  intro g hg
  have hg' : g * k = k * g := mem_cent.1 hg
  have h1 : ujMat ε g * ujMat ε k = ujMat ε k * ujMat ε g := by
    rw [← map_mul, ← map_mul, hg']
  have h2 : Jm ε * ujMat ε k = ujMat ε k * Jm ε := hk.2.symm
  have hJ : ujMat ε g * Jm ε = Jm ε * ujMat ε g := hr.commute h1 h2
  have hU : (ujMat ε g)ᴴ * Jm ε * ujMat ε g = Jm ε := g.2
  have hJJ := Formalism.REAL.Jm_mul_self ε
  refine ⟨?_, hJ⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (ujMat ε g)ᴴ * ujMat ε g = 1
  calc (ujMat ε g)ᴴ * ujMat ε g = (ujMat ε g)ᴴ * (Jm ε * Jm ε) * ujMat ε g := by rw [hJJ, Matrix.mul_one]
    _ = ((ujMat ε g)ᴴ * Jm ε * ujMat ε g) * Jm ε := by
        rw [Matrix.mul_assoc (ujMat ε g)ᴴ (Jm ε * Jm ε), Matrix.mul_assoc (Jm ε), ← hJ]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU, hJJ]

/- English proof (translation)
Introduce `n ε k hk hr`. Establish `hK : IsCompact (KG ε : Set (UJ ε))`. Simplify `(isCompact_univ (X := KG ε)).image continuous_subtype_val` using `[Subtype.range_coe]`. Conclude with `hK.of_isClosed_subset (isClosed_cent k) (cent_subset_KG_of_regSS hk hr)`.
-/
theorem isCompact_cent_of_mem_KG : ∀ (n : ℕ) (ε : Fin n → Bool) (k : UJ ε), k ∈ KG ε → IsRegSS (ujMat ε k) →
    IsCompact (cent k : Set (UJ ε)) := by
  intro n ε k hk hr
  have hK : IsCompact (KG ε : Set (UJ ε)) := by
    simpa [Subtype.range_coe] using (isCompact_univ (X := KG ε)).image continuous_subtype_val
  exact hK.of_isClosed_subset (isClosed_cent k) (cent_subset_KG_of_regSS hk hr)

end GlobalTheory
