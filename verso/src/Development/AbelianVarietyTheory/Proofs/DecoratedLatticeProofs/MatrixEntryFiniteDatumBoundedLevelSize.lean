import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSixth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BadPrimesSharp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedEntryTypePrimeSupportPeriodSizeStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.EntryDatumS

open GlobalTheory.ColNorms.EntryDatum

/- English proof (translation)
Take `⟨C, hC⟩` from `GlobalTheory.T.unfoldedEntry_typePrime_support_period_size`. Use `⟨C, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p' => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3, h4, -⟩` from `GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H`. Establish `hg : ∀ i, Pr.g i = N.g i` using `H.1.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hfr : ∀ {j : ℕ} (p : ChPt (R` using `N.R) sel mu u j) (P : rowSG Pr sel mu) x, frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by`.

Introduce `j p P x`. Establish `hP` using `h1 P.1 P.2`. Unfold `frsF`. Rewrite using `[dif_pos hP]`. Conclude with `(GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ p.deco ⟨P.1, hP⟩).1 x`.

Establish `key` using `smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 p'.deco.1 p'.deco.2 (frsF sel mu p) (frsF sel mu p') (hfr p) (hfr p') (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1)) (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) ( …`. Take `⟨j, -, hj, -⟩` from `h2 P.1 (h1 P.1 P.2)`. Rewrite using `[hj]`. Use `Dvd.dvd.mul_left ?_ _` and prove the remaining obligations. Use `fin_cases j`.

Conclude with `Dvd.intro _ rfl`. Conclude with `Dvd.intro_left _ rfl)`. Use the proof step `(fun P => XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) _`. Use the proof step `(hC CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be)`. Establish `e : ∏ P : rowSG Pr sel mu, (Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2) = ((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)`.

Rewrite using `[Finset.prod_pow, ← Nat.cast_prod, h4, hg 0, hg 1]`. Use `push_cast`. Rewrite using `[← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `key` using `[e]`. Conclude with `key`.
-/
theorem smallDatum_xiEntry_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.unfoldedEntry_typePrime_support_period_size
  refine ⟨C, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p' => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hg : ∀ i, Pr.g i = N.g i := H.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (p : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j p P x
    have hP := h1 P.1 P.2
    unfold frsF
    rw [dif_pos hP]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ p.deco ⟨P.1, hP⟩).1 x
  have key := smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 p'.deco.1 p'.deco.2 (frsF sel mu p) (frsF sel mu p')
    (hfr p) (hfr p') (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P => XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) _
    (hC CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be)
  have e : ∏ P : rowSG Pr sel mu, (Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2) =
      ((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    rw [Finset.prod_pow, ← Nat.cast_prod, h4, hg 0, hg 1]
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [e] at key
  exact key

end GlobalTheory.Core.Ht2.EntryDatumS
