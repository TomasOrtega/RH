import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecExtendOfNonzeroLocus

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Use `Fintype.ofFinite κ` as an intermediate fact. Use `choose r hr using fun j => AmpleSpan.exists_isRatio (s j) t`. Use `choose σ hσ using fun j => AmpleSpan.exists_isRatio t (s j)`. Establish `top` using `AmpleSpan.ker_sup_span_eq_top f s s hcov (fun j l => if l = j then 1 else 0) (fun j k => by simp [apply_ite]) t (AmpleSpan.isCompact_nonzeroLocus s hcov haff t) r hr`. Use `isAffineOpen_of_isAffineOpen_basicOpen _ (Set.range r) ?_ ?_` and prove the remaining obligations.

Establish `e` using `congrArg (Ideal.map (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t) le_top).hom r)) top`. Rewrite `e` using `[Ideal.map_sup, Ideal.map_top, Ideal.map_span, ← Set.range_comp, (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl, bot_sup_eq]`. Use `e using 3` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using `[apply_ite]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Rewrite using `[(hr j).basicOpen, inf_comm, ← (hσ j).basicOpen]`. Conclude with `(haff j).basicOpen _`.
-/
theorem isAffineOpen_nonzeroLocus_of_universallyClosed {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y]
    [UniversallyClosed f] {H : LB X} {κ : Type} [Finite κ] (s : κ → H.Sec) (hcov : ⨆ j, nonzeroLocus (s j) = ⊤)
    (haff : ∀ j, IsAffineOpen (nonzeroLocus (s j))) (t : H.Sec) : IsAffineOpen (nonzeroLocus t) := by
  classical
  have := Fintype.ofFinite κ
  choose r hr using fun j => AmpleSpan.exists_isRatio (s j) t
  choose σ hσ using fun j => AmpleSpan.exists_isRatio t (s j)
  have top := AmpleSpan.ker_sup_span_eq_top f s s hcov (fun j l => if l = j then 1 else 0)
    (fun j k => by simp [apply_ite]) t (AmpleSpan.isCompact_nonzeroLocus s hcov haff t) r hr
  refine isAffineOpen_of_isAffineOpen_basicOpen _ (Set.range r) ?_ ?_
  · have e := congrArg (Ideal.map (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t) le_top).hom r)) top
    rw [Ideal.map_sup, Ideal.map_top, Ideal.map_span, ← Set.range_comp,
      (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl, bot_sup_eq] at e
    convert e using 3
    funext j
    simp [apply_ite]
  · rintro _ ⟨j, rfl⟩
    rw [(hr j).basicOpen, inf_comm, ← (hσ j).basicOpen]
    exact (haff j).basicOpen _

/- English proof (translation)
Take `⟨N, hN, H⟩` from `h.exists_cover_mul`. Take `⟨M, u, hu, ha⟩` from `H n hn`. Use `isAffineOpen_nonzeroLocus_of_universallyClosed f u hu ha (secCast (Nat.mul_comm n N) (secPow s N))` as an intermediate fact. Rewrite `this` using `[nonzeroLocus_secCast, nonzeroLocus_secPow s hN]`. Then use the resulting hypothesis.
-/
theorem IsAmpleLB.isAffineOpen_nonzeroLocus {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f]
    {L : LB X} (h : IsAmpleLB L) {n : ℕ} (hn : 1 ≤ n) (s : (lbPow L n).Sec) : IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨N, hN, H⟩ := h.exists_cover_mul
  obtain ⟨M, u, hu, ha⟩ := H n hn
  have := isAffineOpen_nonzeroLocus_of_universallyClosed f u hu ha (secCast (Nat.mul_comm n N) (secPow s N))
  rwa [nonzeroLocus_secCast, nonzeroLocus_secPow s hN] at this

/- English proof (translation)
Introduce `R _ X _ L hL hA n hn`. Establish `h` using `isAmpleLB_of_relAmple_of_isAffine X hL hA`. Use `⟨fun s => ?_, ?_⟩` and prove the remaining obligations. Take `⟨s', hs, -⟩ : ∃ s' : (lbPow L n).Sec, nonzeroLocus s' = nonzeroLocus s ∧ _` from `exists_sec_oneTerm L (K' := PUnit) rfl s`. Conclude with `hs ▸ h.isAffineOpen_nonzeroLocus X.hom hn s'`.

Take `⟨N, hN, H⟩` from `h.exists_cover_mul`. Take `⟨M, u, hu, -⟩` from `H n hn`. Use `choose t ht using fun i => exists_sec_oneTerm L (K' := Fin 1) (e' := ((n * N : ℕ) : ℤ)) (by rw [Nat.mul_comm]) (u i)`. Conclude with `⟨N, hN, M + 1, t, (iSup_congr fun i => (ht i).1).trans hu⟩`.
-/
theorem isAffineOpen_nonzeroLocus_of_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ (n : ℕ), 1 ≤ n → (∀ s : H0 L n, IsAffineOpen (nonzeroLocus s)) ∧ ∃ (m : ℕ) (_ : 1 ≤ m) (M : ℕ) (t : Fin M → H0 L (n * m)), ⨆ i, nonzeroLocus (t i) = ⊤ := by
  intro R _ X _ L hL hA n hn
  have h := isAmpleLB_of_relAmple_of_isAffine X hL hA
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨s', hs, -⟩ : ∃ s' : (lbPow L n).Sec, nonzeroLocus s' = nonzeroLocus s ∧ _ :=
      exists_sec_oneTerm L (K' := PUnit) rfl s
    exact hs ▸ h.isAffineOpen_nonzeroLocus X.hom hn s'
  · obtain ⟨N, hN, H⟩ := h.exists_cover_mul
    obtain ⟨M, u, hu, -⟩ := H n hn
    choose t ht using fun i => exists_sec_oneTerm L (K' := Fin 1) (e' := ((n * N : ℕ) : ℤ))
      (by rw [Nat.mul_comm]) (u i)
    exact ⟨N, hN, M + 1, t, (iSup_congr fun i => (ht i).1).trans hu⟩

end GlobalTheory
