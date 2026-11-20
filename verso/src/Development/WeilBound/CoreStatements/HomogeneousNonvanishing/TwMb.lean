import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem fix_rt_lemma {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) : g.s H.rt = H.rt := by
  apply RingOfIntegers.ext
  rw [HostAut.s, RingOfIntegers.mapRingEquiv_apply]
  exact g.fix

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem fix_gen_lemma_2 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) : g.s H.w0 = H.w0 ∧ g.s (H.bar H.w0) = H.bar H.w0 := by
  have hr := fix_rt_lemma g
  have hbr : g.s (H.bar H.rt) = H.bar H.rt := by
    have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by
      rw [← map_pow, H.rt_sq, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · rw [h, hr]
    · rw [h, map_neg, hr]
  have two_ne : (2 : 𝓞 E) ≠ 0 := two_ne_zero
  constructor
  · apply mul_left_cancel₀ two_ne
    have h := congrArg g.s H.two_weight_eq_one_add_root
    rw [map_mul, map_ofNat, map_add, map_one, hr] at h
    rw [h, H.two_weight_eq_one_add_root]
  · apply mul_left_cancel₀ two_ne
    have h := congrArg (fun x => g.s (H.bar x)) H.two_weight_eq_one_add_root
    simp only [map_mul, map_ofNat, map_add, map_one] at h
    rw [h, hbr]
    have h2 := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_ofNat, map_add, map_one] at h2
    exact h2.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Treat this case separately. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
private theorem fix_adj_lemma_3 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) (a : 𝓞 E) (ha : a ∈ Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))) : g.s a = a ∧ g.s (H.bar a) = H.bar a := by
  obtain ⟨h1, h2⟩ := fix_gen_lemma_2 g
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨h1, h2⟩
  | algebraMap r =>
    simp
  | add x y _ _ hx hy =>
    simp only [map_add, hx.1, hy.1, hx.2, hy.2]
    exact ⟨trivial, trivial⟩
  | mul x y _ _ hx hy =>
    simp only [map_mul, hx.1, hy.1, hx.2, hy.2]
    exact ⟨trivial, trivial⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem tw_mb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (g : HostAut H), l.Mb.map (g.s : 𝓞 E →+* 𝓞 E) = l.Mb ∧ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)).map (g.s : 𝓞 E →+* 𝓞 E) = l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  intro E _ _ _ H l g
  set S : Set (𝓞 E) := {a : 𝓞 E | a ∈ l.Mb ∧ a ∈ Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))} with hSdef
  have hS : l.Mb = Ideal.span S := l.fromK
  constructor
  · rw [hS, Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [RingEquiv.coe_toRingHom]
      rw [(fix_adj_lemma_3 g y hy.2).1]
      exact hy
    · intro hx
      exact ⟨x, hx, by simp only [RingEquiv.coe_toRingHom]; exact (fix_adj_lemma_3 g x hx.2).1⟩
  · rw [hS, Ideal.map_span, Ideal.map_span, Set.image_image]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp only [RingEquiv.coe_toRingHom]
      exact ((fix_adj_lemma_3 g y hy.2).2).symm
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp only [RingEquiv.coe_toRingHom]
      exact (fix_adj_lemma_3 g y hy.2).2

end PositivityTheory.UnitarySelfGeneration
