import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifferenceStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleChainStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUniqueStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ScalarQuotientStatementStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.Constants

/- English proof (translation)
Unfold `cycEval`. Establish `hfin : (Function.support fun W => divCycle P c W * F W).Finite` using `(ScalarQuotient.divCycle_support_finite P c).subset fun W hW => by`. Rewrite `hW`, the goal using `[Function.mem_support]`. Conclude with `fun h0 => hW (by rw [h0, zero_mul])`. Rewrite using `[mul_finsum' _ _ hfin]`.

Conclude with `finsum_congr fun W => by ring`.
-/
theorem cycEval_natCast_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (F : Ideal (MRing ι O) → ℤ) (P : Ideal (MRing ι O)) (c : MRing ι O) (n : ℕ) :
    cycEval F (fun W => (n : ℤ) * divCycle P c W) = (n : ℤ) * cycEval F (divCycle P c) := by
  unfold cycEval
  have hfin : (Function.support fun W => divCycle P c W * F W).Finite :=
    (ScalarQuotient.divCycle_support_finite P c).subset fun W hW => by
      rw [Function.mem_support] at hW ⊢
      exact fun h0 => hW (by rw [h0, zero_mul])
  rw [mul_finsum' _ _ hfin]
  exact finsum_congr fun W => by ring

/- English proof (translation)
Establish `h` using `hQ (MvPolynomial.mem_support_iff.mp hμ)`. Establish `h2 : Finsupp.degree μ = e`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `h`. Rewrite using `[classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]`.

Simplify `h2` using `[Finsupp.sum, Finsupp.degree_apply]`.
-/
theorem length_classList {K : Type} {q : ℕ} (cls : Fin q → K → ℤ) {Q : MvPolynomial (Fin q) ℤ} {e : ℕ}
    (hQ : Q.IsHomogeneous e) {μ : Fin q →₀ ℕ} (hμ : μ ∈ Q.support) :
    (classList cls μ).length = e := by
  have h := hQ (MvPolynomial.mem_support_iff.mp hμ)
  have h2 : Finsupp.degree μ = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact h
  rw [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  simpa [Finsupp.sum, Finsupp.degree_apply] using h2

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' g hg hmod hlat k hk1 hk2 q L Q hQ`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg hϖ`. Establish `hsame : SameGeneric O x E E'` using `fun s hs => ⟨fun v hv => ⟨_, hg, (hlat s hs _).2 ⟨v, hv, rfl⟩⟩, fun v hv => by`. Take `⟨e, he, rfl⟩` from `(hlat s hs v).1 hv`.

Conclude with `⟨_, hg, E.stable s _ (Subalgebra.algebraMap_mem _ _) _ (E.stable s _ (Subalgebra.algebraMap_mem _ _) _ he)⟩⟩`. Take `⟨K', _, _, ι', _, z, EB, w, b, hJ, hbir, hall⟩` from `GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hmod N 1 V ![E, E'] (by`. Introduce `j`. Use `fin_cases j`. Conclude with `fun s hs => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩`.

Conclude with `hsame)`. Establish `p0 : IsPull O x z E (EB 0)` using `(hall 0).1`. Establish `p1 : IsPull O x z E' (EB 1)` using `(hall 1).1`. Establish `hpull` using `GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) p0 p1`. Establish `hsameJ` using `hpull.2.1 hsame`.

Establish `hscJ` using `hpull.2.2 _ hlat`. Establish `hmodJ : IsModelOver (pointIdeal O (joinCoord x z)) d` using `((BundleExamples.isModelOver_iff O _ d).1 hJ).2`. Take `⟨-, f, f', hpair⟩` from `GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hmodJ N V (EB 0) (EB 1) hsameJ w w (b 0) (b 1) (hall 0).2 (hall 1).2 (fun i j hij => by`. Simplify using `[Module.Basis.repr_self, hij.ne])`. Establish `hnum` using `GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hmod N V E E' hsame K' ι' z hJ hbir (EB 0) (EB 1) p0 p1 w w (b 0) (b 1) f f' hpair`.

Establish `hQ' : Q.IsHomogeneous (d - (k - 1))`. Establish `: d - (k - 1) = d + 1 - k` using `by omega`. Rewrite using `[this]` and apply the resulting hypothesis. Establish `hroot` using `hnum.2 (k - 1) (psum (Fin N) ℤ (k - 1)) (psum_isSymmetric _ _ _) (isHomogeneous_psum N (k - 1)) (by omega) q L Q hQ'`. Establish `hP : (pointIdeal O (joinCoord x z)).IsPrime` using `hmodJ.multiProj.isPrime`.

Establish `hC : ∀ a : O, a ≠ 0 → (C a : MRing (Sum.elim ι ι') O) ∉ pointIdeal O (joinCoord x z)`. Introduce `a ha hmem`. Establish `h1 : a ∈ (pointIdeal O (joinCoord x z)).comap (C : O →+* MRing (Sum.elim ι ι') O)` using `hmem`. Rewrite `h1` using `[hmodJ.noTorsion]`. Conclude with `ha (Ideal.mem_bot.mp h1)`.

Establish `hdiv : ∀ (v : Oˣ) (m : ℕ), rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ((v : O) * ϖ ^ m) = (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ`. Introduce `v m`. Rewrite using `[hroot _ (mul_ne_zero v.ne_zero (pow_ne_zero _ hϖ.ne_zero)), hroot _ hϖ.ne_zero, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[ScalarQuotient.divCycle_const _ hC hϖ.ne_zero v m, cycEval_natCast_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hnum.1 k hk1 hk2 q L Q hQ, hdiv, hroot _ hϖ.ne_zero, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.scalar_quotient_statement O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) d hmodJ N V (EB 0) (EB 1) n u hscJ w w (b 0) (b 1) f f' hpair k (psumExpansion N k) (isPairExpansion_psum N k) _ (by rw [length_classList _ hQ hμ]; omega)]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `m n' h w' hw' hm hEq`. Take `⟨W, rfl⟩` from `hw'`. Distinguish the cases in `h0 : h = 0`. Substitute `h0` using the available equality.

Establish `hn' : n' = 0`. Assume the negation of the conclusion as `hne`. Rewrite `hEq` using `[zero_pow hne, mul_zero]`. Conclude with `pow_ne_zero m hg hEq`. Substitute `hn'` using the available equality.

Establish `hnm : n * m = 0`. Use `IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) W _ _ ?_` and prove the remaining obligations. Rewrite `hEq`, the goal using `[pow_zero, mul_one]`. Rewrite using `[Units.val_pow_eq_pow_val, pow_mul, ← mul_pow, hEq]`. Establish `hn0 : n = 0`.

Break down `Nat.mul_eq_zero.mp hnm with h | h` into its components or cases. Conclude with `h`. Use linear arithmetic over natural numbers and integers. Substitute `hn0` using the available equality. Rewrite using `[hdiv u 0]`.

Simplify using the standard rewrite rules. Take `⟨a, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ`. Establish `hnm : n * m = a * n'`. Use `IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) (W * v ^ n') _ _ ?_` and prove the remaining obligations. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val]`.

Rewrite using `[pow_mul, pow_mul, ← mul_pow, hEq, mul_pow, mul_assoc]`. Establish `hnm' : (n : ℤ) * m = a * n'` using `by exact_mod_cast hnm`. Rewrite using `[hdiv u n, hdiv v a]`. Take the linear combination `rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ * hnm'`.
-/
theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Bd.Statement.{0,0,0} O Ω ι := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' g hg hmod hlat k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg hϖ
  have hsame : SameGeneric O x E E' := fun s hs =>
    ⟨fun v hv => ⟨_, hg, (hlat s hs _).2 ⟨v, hv, rfl⟩⟩, fun v hv => by
      obtain ⟨e, he, rfl⟩ := (hlat s hs v).1 hv
      exact ⟨_, hg, E.stable s _ (Subalgebra.algebraMap_mem _ _) _
        (E.stable s _ (Subalgebra.algebraMap_mem _ _) _ he)⟩⟩
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hJ, hbir, hall⟩ :=
    GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hmod N 1 V ![E, E'] (by
      intro j
      fin_cases j
      · exact fun s hs => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
          fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
      · exact hsame)
  have p0 : IsPull O x z E (EB 0) := (hall 0).1
  have p1 : IsPull O x z E' (EB 1) := (hall 1).1
  have hpull := GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) p0 p1
  have hsameJ := hpull.2.1 hsame
  have hscJ := hpull.2.2 _ hlat
  have hmodJ : IsModelOver (pointIdeal O (joinCoord x z)) d :=
    ((BundleExamples.isModelOver_iff O _ d).1 hJ).2
  obtain ⟨-, f, f', hpair⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hmodJ N V
    (EB 0) (EB 1) hsameJ w w (b 0) (b 1) (hall 0).2 (hall 1).2 (fun i j hij => by
      simp [Module.Basis.repr_self, hij.ne])
  have hnum := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hmod N V E E' hsame K' ι' z hJ hbir (EB 0) (EB 1) p0 p1
    w w (b 0) (b 1) f f' hpair
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have : d - (k - 1) = d + 1 - k := by omega
    rwa [this]
  have hroot := hnum.2 (k - 1) (psum (Fin N) ℤ (k - 1)) (psum_isSymmetric _ _ _)
    (isHomogeneous_psum N (k - 1)) (by omega) q L Q hQ'
  have hP : (pointIdeal O (joinCoord x z)).IsPrime := hmodJ.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing (Sum.elim ι ι') O) ∉ pointIdeal O (joinCoord x z) := by
    intro a ha hmem
    have h1 : a ∈ (pointIdeal O (joinCoord x z)).comap (C : O →+* MRing (Sum.elim ι ι') O) := hmem
    rw [hmodJ.noTorsion] at h1
    exact ha (Ideal.mem_bot.mp h1)
  have hdiv : ∀ (v : Oˣ) (m : ℕ),
      rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ((v : O) * ϖ ^ m) =
        (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ := by
    intro v m
    rw [hroot _ (mul_ne_zero v.ne_zero (pow_ne_zero _ hϖ.ne_zero)), hroot _ hϖ.ne_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [ScalarQuotient.divCycle_const _ hC hϖ.ne_zero v m, cycEval_natCast_mul]
    ring
  refine ⟨?_, ?_⟩
  · rw [hnum.1 k hk1 hk2 q L Q hQ, hdiv, hroot _ hϖ.ne_zero, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [GlobalTheory.T.scalar_quotient_statement O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) d hmodJ N V (EB 0) (EB 1) n u
      hscJ w w (b 0) (b 1) f f' hpair k (psumExpansion N k) (isPairExpansion_psum N k) _
      (by rw [length_classList _ hQ hμ]; omega)]
    ring
  · intro m n' h w' hw' hm hEq
    obtain ⟨W, rfl⟩ := hw'
    by_cases h0 : h = 0
    · subst h0
      have hn' : n' = 0 := by
        by_contra hne
        rw [zero_pow hne, mul_zero] at hEq
        exact pow_ne_zero m hg hEq
      subst hn'
      have hnm : n * m = 0 := by
        refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) W _ _ ?_
        rw [pow_zero, mul_one] at hEq ⊢
        rw [Units.val_pow_eq_pow_val, pow_mul, ← mul_pow, hEq]
      have hn0 : n = 0 := by
        rcases Nat.mul_eq_zero.mp hnm with h | h
        · exact h
        · omega
      subst hn0
      rw [hdiv u 0]
      simp
    · obtain ⟨a, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
      have hnm : n * m = a * n' := by
        refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) (W * v ^ n') _ _ ?_
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        rw [pow_mul, pow_mul, ← mul_pow, hEq, mul_pow, mul_assoc]
      have hnm' : (n : ℤ) * m = a * n' := by exact_mod_cast hnm
      rw [hdiv u n, hdiv v a]
      linear_combination rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ * hnm'

end GlobalTheory.CompanionTheory.Ar.Num.Constants
