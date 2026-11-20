import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.IterInj

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `S' hS' h a ha`. Establish `: S' = S` using `by simpa using hS'`. Substitute `this` using the available equality.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite `ha` using `[hid]`. Simplify using `using ha`. Consider the case `insert j T' hj ih`. Introduce `S' hS' h a ha`.

Establish `hS'' : S' = insert j (S ∪ T')`. Rewrite using `[hS', Finset.union_insert]`. Substitute `hS''` using the available equality. Establish `hsub : S ⊆ S ∪ T'` using `Finset.subset_union_left`. Establish `hb : res (S ∪ T') (insert j (S ∪ T')) (Finset.subset_insert j _) (res S (S ∪ T') hsub a) = 0`.

Rewrite using `[hcomp]`. Conclude with `ha`. Take `⟨k, hk⟩` from `hloc (S ∪ T') j _ (hS.mono hsub) hb`. Establish `h2 : res S (S ∪ T') hsub ((MvPolynomial.X j : MvPolynomial ι A) ^ k • a) = 0`. Rewrite using `[map_smul]`.

Conclude with `hk`. Take `⟨l, hl⟩` from `ih (S ∪ T') rfl hsub _ h2`. Use `⟨k + l, ?_⟩` and prove the remaining obligations. Establish `hx : xProd A (insert j T') = MvPolynomial.X j * xProd A T'`. Simplify using `[xProd, Finset.prod_insert hj]`.

Establish `: (xProd A (insert j T')) ^ (k + l) = ((MvPolynomial.X j : MvPolynomial ι A) ^ l * xProd A T' ^ k) * (xProd A T' ^ l * (MvPolynomial.X j : MvPolynomial ι A) ^ k)`. Rewrite using `[hx, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, mul_smul _ (xProd A T' ^ l * _), mul_smul (xProd A T' ^ l), hl, smul_zero]`.
-/
theorem restriction_compatible_iterated_injective (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type)
    [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)]
    (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')
    (hid : ∀ S (h : S ⊆ S) a, res S S h a = a)
    (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    (hloc : ∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty →
      res S (insert j S) (Finset.subset_insert j S) a = 0 →
      ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0)
    (S : Finset ι) (hS : S.Nonempty) (T : Finset ι) :
    ∀ (S' : Finset ι) (_ : S' = S ∪ T) (h : S ⊆ S') (a : P S), res S S' h a = 0 →
      ∃ l : ℕ, xProd A T ^ l • a = 0 := by
  induction T using Finset.induction_on with
  | empty =>
    intro S' hS' h a ha
    have : S' = S := by simpa using hS'
    subst this
    refine ⟨0, ?_⟩
    rw [hid] at ha
    simpa using ha
  | insert j T' hj ih =>
    intro S' hS' h a ha
    have hS'' : S' = insert j (S ∪ T') := by
      rw [hS', Finset.union_insert]
    subst hS''
    have hsub : S ⊆ S ∪ T' := Finset.subset_union_left
    have hb : res (S ∪ T') (insert j (S ∪ T')) (Finset.subset_insert j _) (res S (S ∪ T') hsub a) = 0 := by
      rw [hcomp]; exact ha
    obtain ⟨k, hk⟩ := hloc (S ∪ T') j _ (hS.mono hsub) hb
    have h2 : res S (S ∪ T') hsub ((MvPolynomial.X j : MvPolynomial ι A) ^ k • a) = 0 := by
      rw [map_smul]; exact hk
    obtain ⟨l, hl⟩ := ih (S ∪ T') rfl hsub _ h2
    refine ⟨k + l, ?_⟩
    have hx : xProd A (insert j T') = MvPolynomial.X j * xProd A T' := by
      simp [xProd, Finset.prod_insert hj]
    have : (xProd A (insert j T')) ^ (k + l) =
        ((MvPolynomial.X j : MvPolynomial ι A) ^ l * xProd A T' ^ k) *
          (xProd A T' ^ l * (MvPolynomial.X j : MvPolynomial ι A) ^ k) := by
      rw [hx, mul_pow]; ring
    rw [this, mul_smul _ (xProd A T' ^ l * _), mul_smul (xProd A T' ^ l), hl, smul_zero]

/- English proof (translation)
Introduce `ι _ A _ P _ _ res hid hcomp hloc T S a hS ha`. Conclude with `restriction_compatible_iterated_injective ι A P res hid hcomp hloc S hS T (S ∪ T) rfl Finset.subset_union_left a ha`.
-/
theorem iter_localisation_injective : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (T S : Finset ι) (a : P S), S.Nonempty → res S (S ∪ T) Finset.subset_union_left a = 0 → ∃ l : ℕ, xProd A T ^ l • a = 0) := by
  intro ι _ A _ P _ _ res hid hcomp hloc T S a hS ha
  exact restriction_compatible_iterated_injective ι A P res hid hcomp hloc S hS T (S ∪ T) rfl Finset.subset_union_left a ha

end GlobalTheory.CompanionTheory.FormalAlg.IterInj
