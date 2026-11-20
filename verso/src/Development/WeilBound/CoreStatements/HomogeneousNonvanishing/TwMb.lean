import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[HostAut.s, RingOfIntegers.mapRingEquiv_apply]`. Conclude with `g.fix`.
-/
private theorem fix_rt_lemma {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) : g.s H.rt = H.rt := by
  apply RingOfIntegers.ext
  rw [HostAut.s, RingOfIntegers.mapRingEquiv_apply]
  exact g.fix

/- English proof (translation)
Establish `hr` using `fix_rt_lemma g`. Establish `hbr : g.s (H.bar H.rt) = H.bar H.rt`. Establish `hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2`. Rewrite using `[← map_pow, H.rt_sq, map_neg, map_natCast]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h` into its components or cases.

Rewrite using `[h, hr]`. Rewrite using `[h, map_neg, hr]`. Establish `two_ne : (2 : 𝓞 E) ≠ 0` using `two_ne_zero`. Prove the components needed by the constructor for the conclusion. Apply `mul_left_cancel₀ two_ne` to reduce the goal to its premises.

Establish `h` using `congrArg g.s H.two_weight_eq_one_add_root`. Rewrite `h` using `[map_mul, map_ofNat, map_add, map_one, hr]`. Rewrite using `[h, H.two_weight_eq_one_add_root]`. Apply `mul_left_cancel₀ two_ne` to reduce the goal to its premises. Establish `h` using `congrArg (fun x => g.s (H.bar x)) H.two_weight_eq_one_add_root`.

Simplify using `only [map_mul, map_ofNat, map_add, map_one] at h`. Rewrite using `[h, hbr]`. Establish `h2` using `congrArg H.bar H.two_weight_eq_one_add_root`. Rewrite `h2` using `[map_mul, map_ofNat, map_add, map_one]`. Conclude with `h2.symm`.
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
Take `⟨h1, h2⟩` from `fix_gen_lemma_2 g`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite using `[Set.mem_singleton_iff.mp hx]`. Conclude with `⟨h1, h2⟩`.

Consider the case `algebraMap r`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Simplify using `only [map_add, hx.1, hy.1, hx.2, hy.2]`. Conclude with `⟨trivial, trivial⟩`.

Consider the case `mul x y _ _ hx hy`. Simplify using `only [map_mul, hx.1, hy.1, hx.2, hy.2]`. Conclude with `⟨trivial, trivial⟩`.
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
Introduce `E _ _ _ H l g`. Use `set S : Set (𝓞 E) := {a : 𝓞 E | a ∈ l.Mb ∧ a ∈ Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))} with hSdef`. Establish `hS : l.Mb = Ideal.span S` using `l.fromK`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hS, Ideal.map_span]`.

Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `only [RingEquiv.coe_toRingHom]`.

Rewrite using `[(fix_adj_lemma_3 g y hy.2).1]`. Conclude with `hy`. Introduce `hx`. Conclude with `⟨x, hx, by simp only [RingEquiv.coe_toRingHom]; exact (fix_adj_lemma_3 g x hx.2).1⟩`. Rewrite using `[hS, Ideal.map_span, Ideal.map_span, Set.image_image]`.

Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations.

Simplify using `only [RingEquiv.coe_toRingHom]`. Conclude with `((fix_adj_lemma_3 g y hy.2).2).symm`. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Simplify using `only [RingEquiv.coe_toRingHom]`.

Conclude with `(fix_adj_lemma_3 g y hy.2).2`.
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
