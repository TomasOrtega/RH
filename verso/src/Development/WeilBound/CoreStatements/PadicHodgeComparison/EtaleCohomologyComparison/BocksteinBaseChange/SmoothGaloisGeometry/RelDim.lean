import Mathlib

open AlgebraicGeometry CategoryTheory

namespace CrystallineSemistableComparison

namespace RelDim

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

def Chart (n : ℕ) (x : X) : Prop :=
  ∃ (U : (Spec (CommRingCat.of K)).Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
    (e : V ≤ f ⁻¹ᵁ U), RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom

/- English proof (translation)
Establish `: Subsingleton (Spec (CommRingCat.of K))`. Use `⟨fun a b => PrimeSpectrum.ext ?_⟩` and prove the remaining obligations. Use `a.isPrime` as an intermediate fact. Use `b.isPrime` as an intermediate fact. Rewrite using `[Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal]`.

Establish `hy : f x ∈ U` using `e hx`. Use `eq_top_iff.mpr fun z _ => ?_` and prove the remaining obligations. Rewrite using `[Subsingleton.elim z (f x)]` and apply the resulting hypothesis.
-/
theorem eq_top {U : (Spec (CommRingCat.of K)).Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) {x : X} (hx : x ∈ V) :
    U = ⊤ := by
  have : Subsingleton (Spec (CommRingCat.of K)) := by
    refine ⟨fun a b => PrimeSpectrum.ext ?_⟩
    have := a.isPrime
    have := b.isPrime
    rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal]
  have hy : f x ∈ U := e hx
  refine eq_top_iff.mpr fun z _ => ?_
  rwa [Subsingleton.elim z (f x)]

/- English proof (translation)
Substitute `hW` using the available equality. Use `hV.isLocalization_basicOpen a` as an intermediate fact. Establish `h2` using `(RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2 Γ(X, X.basicOpen a) a (f.appLE U V e).hom h`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← Scheme.Hom.appLE_map f e (homOfLE (X.basicOpen_le a)).op]`.

Both sides reduce to the same expression.
-/
theorem basicOpen {n : ℕ} {U : (Spec (CommRingCat.of K)).Opens} {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) (a : Γ(X, V))
    (W : X.Opens) (hW : X.basicOpen a = W) (e' : W ≤ f ⁻¹ᵁ U) :
    RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U W e').hom := by
  subst hW
  have := hV.isLocalization_basicOpen a
  have h2 := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
    Γ(X, X.basicOpen a) a (f.appLE U V e).hom h
  convert h2 using 1
  rw [← Scheme.Hom.appLE_map f e (homOfLE (X.basicOpen_le a)).op]
  rfl

/- English proof (translation)
Set `` to `(f.appLE U W e).hom.toAlgebra`. Establish `h1` using `@Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ n hn`. Establish `h2` using `@Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ m hm`. Conclude with `h1.symm.trans h2` after adjusting the coercions.
-/
theorem uniq {n m : ℕ} {U : (Spec (CommRingCat.of K)).Opens} (W : X.Opens) [Nonempty W] (e : W ≤ f ⁻¹ᵁ U)
    (hn : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U W e).hom)
    (hm : RingHom.IsStandardSmoothOfRelativeDimension m (f.appLE U W e).hom) : n = m := by
  let := (f.appLE U W e).hom.toAlgebra
  have h1 := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ n hn
  have h2 := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ m hm
  exact_mod_cast h1.symm.trans h2

/- English proof (translation)
Take `⟨U, hU, V, hV, hx, e, h⟩` from `hn`. Take `⟨U', hU', V', hV', hx', e', h'⟩` from `hm`. Establish `h1` using `eq_top f e hx`. Establish `h2` using `eq_top f e' hx'`. Substitute `h1 h2` using the available equality.

Take `⟨a, b, hab, hxa⟩` from `exists_basicOpen_le_affine_inter hV hV' x ⟨hx, hx'⟩`. Establish `ea : X.basicOpen a ≤ f ⁻¹ᵁ ⊤` using `(X.basicOpen_le a).trans e`. Establish `ha` using `basicOpen f hV e h a _ rfl ea`. Establish `hb` using `basicOpen f hV' e' h' b _ hab.symm ea`. Establish `: Nonempty (X.basicOpen a)` using `⟨⟨x, hxa⟩⟩`.

Conclude with `uniq f _ ea ha hb`.
-/
theorem chart_uniq {n m : ℕ} {x : X} (hn : Chart f n x) (hm : Chart f m x) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hn
  obtain ⟨U', hU', V', hV', hx', e', h'⟩ := hm
  have h1 := eq_top f e hx
  have h2 := eq_top f e' hx'
  subst h1 h2
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter hV hV' x ⟨hx, hx'⟩
  have ea : X.basicOpen a ≤ f ⁻¹ᵁ ⊤ := (X.basicOpen_le a).trans e
  have ha := basicOpen f hV e h a _ rfl ea
  have hb := basicOpen f hV' e' h' b _ hab.symm ea
  have : Nonempty (X.basicOpen a) := ⟨⟨x, hxa⟩⟩
  exact uniq f _ ea ha hb

/- English proof (translation)
Take `⟨U, hU, V, hV, hx, e, h⟩` from `Smooth.exists_isStandardSmooth f x`. Set `` to `(f.appLE U V e).hom.toAlgebra`. Take `⟨ι, σ, _, _, ⟨P⟩⟩` from `h.out`. Conclude with `⟨P.dimension, U, hU, V, hV, hx, e, P.isStandardSmoothOfRelativeDimension rfl⟩`.
-/
theorem exists_chart [Smooth f] (x : X) : ∃ n, Chart f n x := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h.out
  exact ⟨P.dimension, U, hU, V, hV, hx, e, P.isStandardSmoothOfRelativeDimension rfl⟩

/- English proof (translation)
Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce and unpack `x ⟨U, hU, V, hV, hx, e, h⟩`. Conclude with `⟨V, fun y hy => ⟨U, hU, V, hV, hy, e, h⟩, V.isOpen, hx⟩`.
-/
theorem isOpen_chart (n : ℕ) : IsOpen {x | Chart f n x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, hU, V, hV, hx, e, h⟩
  exact ⟨V, fun y hy => ⟨U, hU, V, hV, hy, e, h⟩, V.isOpen, hx⟩

end RelDim

open RelDim in

/- English proof (translation)
Take `⟨x0⟩` from `(inferInstance : Nonempty X)`. Take `⟨n, hn⟩` from `exists_chart f x0`. Establish `hclopen : IsClopen {x | Chart f n x}`. Use `⟨?_, isOpen_chart f n⟩` and prove the remaining obligations. Rewrite using `[← isOpen_compl_iff]`.

Establish `: {x | Chart f n x}ᶜ = ⋃ m ∈ {m | m ≠ n}, {x | Chart f m x}`. Use extensionality with `x`. Simplify using `only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨m, hm⟩` from `exists_chart f x`. Conclude with `⟨m, fun h => hx (h ▸ hm), hm⟩`. Introduce and unpack `⟨m, hmn, hm⟩ hx`. Conclude with `hmn (chart_uniq f hm hx)`. Rewrite using `[this]`.

Conclude with `isOpen_biUnion fun m _ => isOpen_chart f m`. Establish `huniv` using `(isClopen_iff.mp hclopen).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨x0, hn⟩)`. Use `⟨n, ⟨fun x => ?_⟩⟩` and prove the remaining obligations. Establish `hx : x ∈ {x | Chart f n x}` using `huniv ▸ Set.mem_univ x`. Conclude with `hx`.
-/
theorem exists_smoothOfRelativeDimension {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
    [Smooth f] [ConnectedSpace X] : ∃ d, SmoothOfRelativeDimension d f := by
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨n, hn⟩ := exists_chart f x0
  have hclopen : IsClopen {x | Chart f n x} := by
    refine ⟨?_, isOpen_chart f n⟩
    rw [← isOpen_compl_iff]
    have : {x | Chart f n x}ᶜ = ⋃ m ∈ {m | m ≠ n}, {x | Chart f m x} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := exists_chart f x
        exact ⟨m, fun h => hx (h ▸ hm), hm⟩
      · rintro ⟨m, hmn, hm⟩ hx
        exact hmn (chart_uniq f hm hx)
    rw [this]
    exact isOpen_biUnion fun m _ => isOpen_chart f m
  have huniv := (isClopen_iff.mp hclopen).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨x0, hn⟩)
  refine ⟨n, ⟨fun x => ?_⟩⟩
  have hx : x ∈ {x | Chart f n x} := huniv ▸ Set.mem_univ x
  exact hx

end CrystallineSemistableComparison
