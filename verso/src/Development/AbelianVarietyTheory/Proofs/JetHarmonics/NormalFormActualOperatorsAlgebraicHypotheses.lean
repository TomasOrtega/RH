import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

/- English proof (translation)
Introduce `y hy`. Simplify using `only [TL.siteOps, Set.mem_union, Set.mem_range] at hy`. Break down `hy with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩` into its components or cases. Conclude with `(L.p_GGi l).symm`. Conclude with `(L.pb_GGi l).symm`.

Apply the tactic sequence `all_goals exact L.fns_comm _ (Or.inr (by simp)) _ (by simp)`.
-/
theorem ggi_commute_siteOps {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r) :
    ∀ y ∈ TL.siteOps L, Commute L.GGi y := by
  intro y hy
  simp only [TL.siteOps, Set.mem_union, Set.mem_range] at hy
  rcases hy with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
  · exact (L.p_GGi l).symm
  · exact (L.pb_GGi l).symm
  all_goals exact L.fns_comm _ (Or.inr (by simp)) _ (by simp)

/- English proof (translation)
Take `⟨Y₀, hY₀⟩` from `P5.Kfp.sep_real hP`. Establish `hp : ∀ ρ, (Lagrange.interpolate Finset.univ (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) f).eval (M.xC P ρ (Y₀ : ℂ)) = f ρ` using `fun ρ => Lagrange.eval_interpolate_at_node (v := fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) f hY₀.injOn (Finset.mem_univ ρ)`. Rewrite using `[P5.Kfp.kappa_aeval d (Y₀ : ℂ) _ f hp]`. Establish `e : d.x (Y₀ : ℂ) = d.L.GGi * d.QQ (Y₀ : ℂ) 1 1`. Establish `h : d.QQ (Y₀ : ℂ) 1 1 = d.L.GG * d.x (Y₀ : ℂ)` using `rfl`.

Rewrite using `[h, ← mul_assoc, d.L.GGi_GG, one_mul]`. Establish `hx : Commute (d.x (Y₀ : ℂ)) g`. Rewrite using `[e]`. Conclude with `(ggi_commute_siteOps d.L g hg).mul_left (hq _)`. Generalize the expression as in `Lagrange.interpolate Finset.univ (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) f = p`.

Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add_left hq`. Consider the case `monomial n a`. Rewrite using `[Polynomial.aeval_monomial]`.

Conclude with `(Algebra.commute_algebraMap_left a g).mul_left (hx.pow_left n)`.
-/
theorem kappa_commute_of_qq {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {P : M.Par} (hP : P.OK)
    (d : Q.NFData P A) {g : A} (hg : g ∈ TL.siteOps d.L) (hq : ∀ Y, Commute (d.QQ Y 1 1) g)
    (f : M.Ty P → ℂ) : Commute (d.κ f) g := by
  classical
  obtain ⟨Y₀, hY₀⟩ := P5.Kfp.sep_real hP
  have hp : ∀ ρ, (Lagrange.interpolate Finset.univ (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) f).eval
      (M.xC P ρ (Y₀ : ℂ)) = f ρ := fun ρ =>
    Lagrange.eval_interpolate_at_node (v := fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) f hY₀.injOn (Finset.mem_univ ρ)
  rw [P5.Kfp.kappa_aeval d (Y₀ : ℂ) _ f hp]
  have e : d.x (Y₀ : ℂ) = d.L.GGi * d.QQ (Y₀ : ℂ) 1 1 := by
    have h : d.QQ (Y₀ : ℂ) 1 1 = d.L.GG * d.x (Y₀ : ℂ) := rfl
    rw [h, ← mul_assoc, d.L.GGi_GG, one_mul]
  have hx : Commute (d.x (Y₀ : ℂ)) g := by
    rw [e]
    exact (ggi_commute_siteOps d.L g hg).mul_left (hq _)
  generalize Lagrange.interpolate Finset.univ (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) f = p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_left a g).mul_left (hx.pow_left n)

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN`. Establish `hA : TL.AHyp L st` using `(Formalism.FourierDecayAlt.P.actual_algebra_facts Wp Wq P _ _ _ _ X μ L st l0 hD).1`. Take `⟨hpl, -, hL, hQQ, -, hinv, -, -⟩` from `hD`. Take `⟨hL', hS, hR, hQ⟩` from `hN`. Take `⟨sp, sc, sci⟩` from `P5.HerA.star_site_ops hL'`.

Establish `hsame : SameFns L d.L`. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩` from `hL`. Take `⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩` from `hL'`. Conclude with `⟨funext fun l => (a1 l).trans (b1 l).symm, funext fun l => (a2 l).trans (b2 l).symm,`. Use function extensionality and compare the values at `fun l => (a3 l).trans (b3 l).symm, funext fun l => (a4 l).trans (b4 l).symm,`.

Use function extensionality and compare the values at `fun l => (a5 l).trans (b5 l).symm, funext fun l => (a6 l).trans (b6 l).symm,`. Use the proof step `a7.trans b7.symm, a8.trans b8.symm, a9.trans b9.symm, a10.trans b10.symm, a11.trans b11.symm,`. Use the proof step `a12.trans b12.symm, a13.trans b13.symm⟩`. Establish `hs : M.sgn P l0 = 1 ∨ M.sgn P l0 = -1` using `neg_one_pow_eq_or ℂ _`. Establish `hst : ∀ Y, st.QQ Y = M.sgn P l0 • d.QQ Y` using `fun Y => by rw [hQQ Y, hQ Y]`.

Establish `hsite : TL.siteOps L = TL.siteOps d.L`. Take `⟨e1, e2, e3, e4, e5, e6, -⟩` from `hsame`. Unfold `TL.siteOps`. Rewrite using `[e1, e2, e3, e4, e5, e6]`. Use `⟨⟨hpl.1, hS, hR, sp, sc, sci, fun f g hg => ?_⟩, hA, hsame, hs, hst, hinv⟩` and prove the remaining obligations.

Use `kappa_commute_of_qq hpl.1 d hg (fun Y => ?_) f` and prove the remaining obligations. Establish `h` using `hA.qq_site Y 1 1 g (hsite ▸ hg)`. Rewrite `h` using `[hst Y, Matrix.smul_apply]`. Break down `hs with hs | hs` into its components or cases. Rewrite `h` using `[hs, one_smul]`. Then use the resulting hypothesis.

Rewrite `h` using `[hs, neg_smul, one_smul]`. Conclude with `Commute.neg_left_iff.1 h`.
-/
theorem hatHyp_and_tie_of_isNF :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
      [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
      (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r)
      (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)),
      P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → HatHyp d ∧ Comparison₂ d L st (M.sgn P l0) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN
  have hA : TL.AHyp L st := (Formalism.FourierDecayAlt.P.actual_algebra_facts Wp Wq P _ _ _ _ X μ L st l0 hD).1
  obtain ⟨hpl, -, hL, hQQ, -, hinv, -, -⟩ := hD
  obtain ⟨hL', hS, hR, hQ⟩ := hN
  obtain ⟨sp, sc, sci⟩ := P5.HerA.star_site_ops hL'
  have hsame : SameFns L d.L := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hL
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := hL'
    exact ⟨funext fun l => (a1 l).trans (b1 l).symm, funext fun l => (a2 l).trans (b2 l).symm,
      funext fun l => (a3 l).trans (b3 l).symm, funext fun l => (a4 l).trans (b4 l).symm,
      funext fun l => (a5 l).trans (b5 l).symm, funext fun l => (a6 l).trans (b6 l).symm,
      a7.trans b7.symm, a8.trans b8.symm, a9.trans b9.symm, a10.trans b10.symm, a11.trans b11.symm,
      a12.trans b12.symm, a13.trans b13.symm⟩
  have hs : M.sgn P l0 = 1 ∨ M.sgn P l0 = -1 := neg_one_pow_eq_or ℂ _
  have hst : ∀ Y, st.QQ Y = M.sgn P l0 • d.QQ Y := fun Y => by rw [hQQ Y, hQ Y]
  have hsite : TL.siteOps L = TL.siteOps d.L := by
    obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := hsame
    unfold TL.siteOps
    rw [e1, e2, e3, e4, e5, e6]
  refine ⟨⟨hpl.1, hS, hR, sp, sc, sci, fun f g hg => ?_⟩, hA, hsame, hs, hst, hinv⟩
  refine kappa_commute_of_qq hpl.1 d hg (fun Y => ?_) f
  have h := hA.qq_site Y 1 1 g (hsite ▸ hg)
  rw [hst Y, Matrix.smul_apply] at h
  rcases hs with hs | hs
  · rwa [hs, one_smul] at h
  · rw [hs, neg_smul, one_smul] at h
    exact Commute.neg_left_iff.1 h

end GlobalTheory.HatNF
