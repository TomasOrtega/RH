import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

namespace GlobalTheory.HolomorphicArc

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `hf 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`.

Conclude with `mul_eq_left.1 h.symm`. Consider the case `succ n ih => rw [succ_nsmul, hf, ih, pow_succ]`.
-/
theorem map_nsmul_eq_pow {L G : Type} [AddCommGroup L] [Group G] (f : L → G) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.1 h.symm
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

/- English proof (translation)
Establish `h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[l.prod]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `h' : (l.M : 𝓞 E) ∈ l.Mb` using `Ideal.mul_le_left h`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`.

Conclude with `Submodule.smul_mem_smul h' Submodule.mem_top`.
-/
theorem nsmul_mem (v : D.La) : l.M • v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  have h' : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left h
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul h' Submodule.mem_top

/- English proof (translation)
Take `⟨φ, hφ⟩` from `Spec.map_surjective (y ≫ s)`. Establish `h₁ : y ≫ s = spMap φ.hom` using `hφ.symm`. Rewrite `h`, the goal using `[Category.assoc, h₁, ← spMap_comp]`. Establish `h₂` using `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`. Use `congr 1`.

Use extensionality with `x`. Establish `h₃ : φ.hom x = algebraMap ℂ R (σ x)` using `Subtype.ext (DFunLike.congr_fun h₂ x)`. Conclude with `(congrArg ev h₃).trans (ev.commutes _)`.
-/
theorem over_of_generic {S : Scheme.{0}} {k : Type} [CommRing k] (s : S ⟶ Sp k) (σ : k →+* ℂ)
    (R : Subalgebra ℂ ℂ⸨X⸩) (y : Sp R ⟶ S) (ev : R →ₐ[ℂ] ℂ)
    (h : (spMap R.val.toRingHom ≫ y) ≫ s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ)) :
    (spMap ev.toRingHom ≫ y) ≫ s = spMap σ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ s)
  have h₁ : y ≫ s = spMap φ.hom := hφ.symm
  rw [Category.assoc, h₁, ← spMap_comp] at h ⊢
  have h₂ := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  congr 1
  ext x
  have h₃ : φ.hom x = algebraMap ℂ R (σ x) := Subtype.ext (DFunLike.congr_fun h₂ x)
  exact (congrArg ev h₃).trans (ev.commutes _)

/- English proof (translation)
Introduce `U f`. Establish `e : {b | b ∈ {w : ℂ | T' < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} = {w : ℂ | T' < w.im} ∩ {b | b ∈ {w : ℂ | T < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U}` using `Set.ext fun b => ⟨fun hb => ⟨hb.1, h.trans_lt hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩`. Rewrite using `[e]`. Conclude with `⟨(isOpen_lt continuous_const Complex.continuous_im).inter (hol U f).1, (hol U f).2.mono Set.inter_subset_right⟩`.
-/
theorem isHolTo_halfPlane_mono {X : Scheme.{0}} {y : ℂ → (Sp ℂ ⟶ X)} {T T' : ℝ} (h : T ≤ T')
    (hol : IsHolTo {w : ℂ | T < w.im} y) : IsHolTo {w : ℂ | T' < w.im} y := by
  intro U f
  have e : {b | b ∈ {w : ℂ | T' < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} =
      {w : ℂ | T' < w.im} ∩ {b | b ∈ {w : ℂ | T < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun b => ⟨fun hb => ⟨hb.1, h.trans_lt hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
  rw [e]
  exact ⟨(isOpen_lt continuous_const Complex.continuous_im).inter (hol U f).1,
    (hol U f).2.mono Set.inter_subset_right⟩

end GlobalTheory.HolomorphicArc
