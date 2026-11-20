import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section

namespace LateralTheory.CohomologicalPurity.ChartCut

open RingHom in

/- English proof (translation)
Set `B` to `Localization.Away (algebraMap S (Localization.Away u) v)`. Establish `h2 : ((algebraMap (Localization.Away u) B).comp ((algebraMap S (Localization.Away u)).comp ψ)).IsStandardSmoothOfRelativeDimension n` using `zero_add n ▸ (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway (algebraMap S (Localization.Away u) v)).comp h`. Establish `hB : IsLocalization.Away (u * v) B` using `inferInstance`. Set `eT : B ≃ₐ[S] T` to `IsLocalization.algEquiv (Submonoid.powers (u * v)) B T`. Establish `h3 : ((algebraMap S B).comp ψ).IsStandardSmoothOfRelativeDimension n`.

Rewrite using `[IsScalarTower.algebraMap_eq S (Localization.Away u) B, RingHom.comp_assoc]`. Conclude with `h2`. Establish `h4` using `(isStandardSmoothOfRelativeDimension_respectsIso (n := n)).left _ eT.toRingEquiv h3`. Establish `hT : algebraMap S T = (eT.toRingEquiv.toRingHom).comp (algebraMap S B)`. Use extensionality with `x`.

Conclude with `(eT.commutes x).symm`. Rewrite using `[hT, RingHom.comp_assoc]`. Conclude with `h4`.
-/
theorem shrink_away {n : ℕ} {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (u v : S)
    (T : Type) [CommRing T] [Algebra S T] [IsLocalization.Away (u * v) T]
    (h : ((algebraMap S (Localization.Away u)).comp ψ).IsStandardSmoothOfRelativeDimension n) :
    ((algebraMap S T).comp ψ).IsStandardSmoothOfRelativeDimension n := by
  let B := Localization.Away (algebraMap S (Localization.Away u) v)
  have h2 : ((algebraMap (Localization.Away u) B).comp
      ((algebraMap S (Localization.Away u)).comp ψ)).IsStandardSmoothOfRelativeDimension n :=
    zero_add n ▸ (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
      (algebraMap S (Localization.Away u) v)).comp h
  have hB : IsLocalization.Away (u * v) B := inferInstance
  let eT : B ≃ₐ[S] T := IsLocalization.algEquiv (Submonoid.powers (u * v)) B T
  have h3 : ((algebraMap S B).comp ψ).IsStandardSmoothOfRelativeDimension n := by
    rw [IsScalarTower.algebraMap_eq S (Localization.Away u) B, RingHom.comp_assoc]; exact h2
  have h4 := (isStandardSmoothOfRelativeDimension_respectsIso (n := n)).left _ eT.toRingEquiv h3
  have hT : algebraMap S T = (eT.toRingEquiv.toRingHom).comp (algebraMap S B) := by
    ext x; exact (eT.commutes x).symm
  rw [hT, RingHom.comp_assoc]; exact h4

/- English proof (translation)
Introduce `e d R A _ _ φ I p hp hIp ⟨h1, h2⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha1, hap⟩ : ∃ a : A, ((algebraMap A (Localization.Away a)).comp φ).IsStandardSmoothOfRelativeDimension (e + d) ∧ a ∉ p := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hp.ne_top` to reduce the goal to its premises.

Rewrite using `[eq_top_iff, ← h1.span_eq_top, Ideal.span_le]`. Introduce `g hg`. Conclude with `hcon g hg`. Establish `hq : (p.map (Ideal.Quotient.mk I)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc1, hcq⟩ : ∃ c : A ⧸ I, ((algebraMap (A ⧸ I) (Localization.Away c)).comp ((Ideal.Quotient.mk I).comp φ)).IsStandardSmoothOfRelativeDimension e ∧ c ∉ p.map (Ideal.Quotient.mk I) := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hq.ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← h2.span_eq_top, Ideal.span_le]`. Introduce `g hg`.

Conclude with `hcon g hg`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `hbp : b ∉ p` using `fun hb => hcq (Ideal.mem_map_of_mem _ hb)`. Use `⟨a * b, fun h => (hp.mem_or_mem h).elim hap hbp, ?_⟩` and prove the remaining obligations. Introduce `A' _ _ _`.

Use `⟨shrink_away φ a b A' ha1, ?_⟩` and prove the remaining obligations. Establish `hloc : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b))) (A' ⧸ I.map (algebraMap A A'))` using `inferInstance`. Establish `key : Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b)) = Submonoid.powers (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a)`. Rewrite using `[Algebra.algebraMapSubmonoid, Submonoid.map_powers, mul_comm a b, map_mul]`. Both sides reduce to the same expression.

Establish `: IsLocalization.Away (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a) (A' ⧸ I.map (algebraMap A A'))`. Unfold `IsLocalization.Away`. Rewrite using `[← key]`. Conclude with `hloc`. Establish `hcomp : (Ideal.Quotient.mk (I.map (algebraMap A A'))).comp ((algebraMap A A').comp φ) = (algebraMap (A ⧸ I) (A' ⧸ I.map (algebraMap A A'))).comp ((Ideal.Quotient.mk I).comp φ)`.

Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[hcomp]`. Conclude with `shrink_away _ _ (Ideal.Quotient.mk I a) _ hc1`.
-/
theorem LeafShrink_of : LeafShrink := by
  intro e d R A _ _ φ I p hp hIp ⟨h1, h2⟩
  obtain ⟨a, ha1, hap⟩ : ∃ a : A, ((algebraMap A (Localization.Away a)).comp φ).IsStandardSmoothOfRelativeDimension (e + d) ∧ a ∉ p := by
    by_contra hcon
    push Not at hcon
    apply hp.ne_top
    rw [eq_top_iff, ← h1.span_eq_top, Ideal.span_le]
    intro g hg; exact hcon g hg
  have hq : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  obtain ⟨c, hc1, hcq⟩ : ∃ c : A ⧸ I, ((algebraMap (A ⧸ I) (Localization.Away c)).comp ((Ideal.Quotient.mk I).comp φ)).IsStandardSmoothOfRelativeDimension e ∧ c ∉ p.map (Ideal.Quotient.mk I) := by
    by_contra hcon
    push Not at hcon
    apply hq.ne_top
    rw [eq_top_iff, ← h2.span_eq_top, Ideal.span_le]
    intro g hg; exact hcon g hg
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hbp : b ∉ p := fun hb => hcq (Ideal.mem_map_of_mem _ hb)
  refine ⟨a * b, fun h => (hp.mem_or_mem h).elim hap hbp, ?_⟩
  intro A' _ _ _
  refine ⟨shrink_away φ a b A' ha1, ?_⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b)))
      (A' ⧸ I.map (algebraMap A A')) := inferInstance
  have key : Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b)) =
      Submonoid.powers (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, mul_comm a b, map_mul]; rfl
  have : IsLocalization.Away (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a)
      (A' ⧸ I.map (algebraMap A A')) := by
    unfold IsLocalization.Away; rw [← key]; exact hloc
  have hcomp : (Ideal.Quotient.mk (I.map (algebraMap A A'))).comp ((algebraMap A A').comp φ) =
      (algebraMap (A ⧸ I) (A' ⧸ I.map (algebraMap A A'))).comp ((Ideal.Quotient.mk I).comp φ) := by
    ext x; rfl
  rw [hcomp]
  exact shrink_away _ _ (Ideal.Quotient.mk I a) _ hc1

end LateralTheory.CohomologicalPurity.ChartCut
