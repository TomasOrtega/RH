import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechNerveDiagonalIsoZeroOverBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialSpectralRowExactZeroOfAcyclicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyFiniteKillingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelCohomologySubsingletonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyVanishesPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNervePullbackBijectiveDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDegreeZeroBijective

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace GlobalTheory.EtC.GmStep

/- English proof (translation)
Substitute `hn` using the available equality. Substitute `hi` using the available equality. Both sides reduce to the same expression.
-/
theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

/- English proof (translation)
Simplify using `only [SimplicialObject.δ]`. Rewrite using `[← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, (cechC A A').naturality]`.
-/
theorem cechC_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] {R : Type} [CommRing R] (F : Shv R) (s : ℤ)
    (k : ℕ) (j : Fin (k + 2)) (y : H R (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) F s) :
    pull R (disc.map ((cechC A A').app (op ⦋k + 1⦌))) F s (pull R (disc.map ((cech (baseHom A A')).δ j)) F s y) =
      pull R (disc.map ((cech (laurentHom A A')).δ j)) F s (pull R (disc.map ((cechC A A').app (op ⦋k⦌))) F s y) := by
  simp only [SimplicialObject.δ]
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, (cechC A A').naturality]

/- English proof (translation)
Establish `h` using `(cechAug (laurentHom A A')).naturality (SimplexCategory.δ j).op`. Conclude with `(disc.map_comp _ _).symm.trans (congrArg disc.map (h.trans (Category.comp_id _)))`.
-/
theorem aug_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ) (j : Fin (k + 2)) :
    disc.map ((cech (laurentHom A A')).δ j) ≫ augK A A' k = augK A A' (k + 1) := by
  have h := (cechAug (laurentHom A A')).naturality (SimplexCategory.δ j).op
  exact (disc.map_comp _ _).symm.trans (congrArg disc.map (h.trans (Category.comp_id _)))

/- English proof (translation)
Use `hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom` as an intermediate fact. Simplify using `using this`.
-/
theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

/- English proof (translation)
Establish `hint : (algebraMap A A').IsIntegral` using `fun x => Algebra.IsIntegral.isIntegral x`. Take `⟨hI, hS⟩` from `spec_integral_surj (algebraMap A A') hint hker`. Establish `hB` using `@GlobalTheory.EtC.b4 q _ _ (baseHom A A') hI hS (isUnit_gamma q A hq) j`. Use `GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic (ZMod q) (tw q j) _ (fun k s hs => GlobalTheory.T.cech_cohomology_vanishes_positive q A hA hq A' inferInstance k s j hs) (fun m hm => ?_) p` and prove the remaining obligations. Use `haveI : Subsingleton (H (ZMod q) (sch.obj (Spec (CommRingCat.of A))) (tw q j) m) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) m hm`.

Conclude with `⟨fun a b => by`. Take `⟨a', rfl⟩` from `(hB m).2 a`. Take `⟨b', rfl⟩` from `(hB m).2 b`. Rewrite using `[Subsingleton.elim a' b']⟩`.
-/
theorem rowExact_base (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Finite A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A)
    (j : ℤ) (p : ℕ) : RowExact (ZMod q) (cech (baseHom A A')) (tw q j) 0 p := by
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI, hS⟩ := spec_integral_surj (algebraMap A A') hint hker
  have hB := @GlobalTheory.EtC.b4 q _ _ (baseHom A A') hI hS (isUnit_gamma q A hq) j
  refine GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic (ZMod q) (tw q j) _ (fun k s hs => GlobalTheory.T.cech_cohomology_vanishes_positive q A hA hq A' inferInstance k s j hs) (fun m hm => ?_) p
  haveI : Subsingleton (H (ZMod q) (sch.obj (Spec (CommRingCat.of A))) (tw q j) m) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) m hm
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := (hB m).2 a
    obtain ⟨b', rfl⟩ := (hB m).2 b
    rw [Subsingleton.elim a' b']⟩

/- English proof (translation)
Introduce `q _ n hn IH A _ _ hA hq i`. It suffices to establish `h : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩`. Introduce `x`. Take `⟨A', _, _, hfin, hker, hx⟩` from `GlobalTheory.T.laurent_cohomology_finite_killing q A hA hq n i hn x`. Use `haveI := hfin`.

Establish `hint : (algebraMap A A').IsIntegral` using `fun x => Algebra.IsIntegral.isIntegral x`. Take `⟨hI', hS'⟩` from `spec_integral_surj _ (laurentMap_isIntegral _ hint) (laurentMap_ker _ hker)`. Establish `hqL : IsUnit (q : LaurentPolynomial A)` using `by simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)`. Establish `hB` using `@GlobalTheory.EtC.b4 q _ _ (laurentHom A A') hI' hS' (isUnit_gamma q _ hqL) i`. Take `⟨N, rfl⟩ : ∃ N : ℕ, n = N` from `⟨n.toNat, by omega⟩`.

Apply `(hB N).1` to reduce the goal to its premises. Rewrite using `[map_zero]`. Take `⟨Δ, hΔ0, hΔ⟩` from `GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base (laurentHom A A')`. Use `GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact (ZMod q) (tw q i) (cech (laurentHom A A')) (yoneda.obj _) Δ hΔ0 N _ ?_ ?_` and prove the remaining obligations. Conclude with `(pull_comp (ZMod q) Δ (cechAug (laurentHom A A')) (tw q i) N x).symm.trans ((congrArg (fun g => pull (ZMod q) g (tw q i) N x) hΔ).trans hx)`.

Introduce `p hp`. Break down `(by omega : (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 0 ∨ (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 1 ∨ 2 ≤ (N : ℤ) - ((p + 1 : ℕ) : ℤ)) with h0 | h1 | h2` into its components or cases. Rewrite using `[h0]`. Conclude with `rowExact_transfer (fun k => pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0) (fun k => GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero q A hA hq A' hfin k i) (fun k j y => cechC_face A A' _ _ k j y) p (rowExact_base q A hA hq A' hker i p)`. Rewrite using `[h1]`.

Use `rowExact_transfer (fun k => rowOne A A' q i k) (fun k => GlobalTheory.T.cech_degree_zero_bijective q A hA hq A' hfin k i) (fun k j y => ?_) p (rowExact_base q A hA hq A' hker (i - 1) p)` and prove the remaining obligations. Simplify using `only [rowOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Rewrite using `[pull_cast, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1, cechC_face, ← pull_comp (ZMod q) (disc.map ((cech (laurentHom A A')).δ j)) (augK A A' k), aug_face]`. Introduce `y _ haveI := GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton q N IH A hA hq A' hfin (p + 1) _ i h2 (by omega)`. Conclude with `⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩`.
-/
theorem gm_vanishing_step : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  intro q _ n hn IH A _ _ hA hq i
  suffices h : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨A', _, _, hfin, hker, hx⟩ := GlobalTheory.T.laurent_cohomology_finite_killing q A hA hq n i hn x
  haveI := hfin
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI', hS'⟩ := spec_integral_surj _ (laurentMap_isIntegral _ hint) (laurentMap_ker _ hker)
  have hqL : IsUnit (q : LaurentPolynomial A) := by simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  have hB := @GlobalTheory.EtC.b4 q _ _ (laurentHom A A') hI' hS' (isUnit_gamma q _ hqL) i
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
  apply (hB N).1
  rw [map_zero]
  obtain ⟨Δ, hΔ0, hΔ⟩ := GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base (laurentHom A A')
  refine GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact (ZMod q) (tw q i) (cech (laurentHom A A')) (yoneda.obj _) Δ hΔ0 N _ ?_ ?_
  · exact (pull_comp (ZMod q) Δ (cechAug (laurentHom A A')) (tw q i) N x).symm.trans
      ((congrArg (fun g => pull (ZMod q) g (tw q i) N x) hΔ).trans hx)
  · intro p hp
    rcases (by omega : (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 0 ∨ (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 1 ∨
        2 ≤ (N : ℤ) - ((p + 1 : ℕ) : ℤ)) with h0 | h1 | h2
    · rw [h0]
      exact rowExact_transfer (fun k => pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0)
        (fun k => GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero q A hA hq A' hfin k i) (fun k j y => cechC_face A A' _ _ k j y) p
        (rowExact_base q A hA hq A' hker i p)
    · rw [h1]
      refine rowExact_transfer (fun k => rowOne A A' q i k) (fun k => GlobalTheory.T.cech_degree_zero_bijective q A hA hq A' hfin k i) (fun k j y => ?_) p
        (rowExact_base q A hA hq A' hker (i - 1) p)
      simp only [rowOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [pull_cast, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1, cechC_face,
        ← pull_comp (ZMod q) (disc.map ((cech (laurentHom A A')).δ j)) (augK A A' k), aug_face]
    · intro y _
      haveI := GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton q N IH A hA hq A' hfin (p + 1) _ i h2 (by omega)
      exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩

end GlobalTheory.EtC.GmStep

end
