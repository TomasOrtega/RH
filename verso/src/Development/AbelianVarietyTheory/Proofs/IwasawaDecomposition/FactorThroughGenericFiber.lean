import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `O K _ _ _ _ _ T g hg`. Set `φ : O →+* Γ(T, ⊤)` to `((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ g.appTop).hom`. Establish `hgφ : g = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)`. Establish `h` using `Scheme.toSpecΓ_naturality g`. Establish `e : g = g ≫ (Sp O).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv` using `by simp`.

Rewrite using `[e, ← Category.assoc, h, Category.assoc, ← Spec.map_comp]`. Simplify using `[φ]`. Establish `hunit : ∀ b : nonZeroDivisors O, IsUnit (φ b)`. Introduce and unpack `⟨b, hb⟩`. Use `T.toRingedSpace.isUnit_of_isUnit_germ ⊤ (φ b) fun x hx => ?_` and prove the remaining obligations.

Establish `hmem : x ∈ T.basicOpen (φ b)`. Establish `e : T.basicOpen (φ b) = g ⁻¹ᵁ (Sp O).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv b)`. Rewrite using `[Scheme.preimage_basicOpen_top]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `show g x ∈ (Sp O).basicOpen _`. Rewrite using `[basicOpen_eq_of_affine (R := CommRingCat.of O) b]`. Take `⟨y, hy⟩` from `hg ⟨x, rfl⟩`. Use `show b ∉ (g x).asIdeal`. Rewrite using `[← hy]`.

Introduce `hbm`. Establish `hbm' : algebraMap O K b ∈ y.asIdeal` using `hbm`. Establish `hu : IsUnit (algebraMap O K b)` using `(IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb).isUnit`. Conclude with `y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hbm' hu)`. Conclude with `(T.mem_basicOpen (φ b) x hx).1 hmem`.

Set `ψ : K →+* Γ(T, ⊤)` to `IsLocalization.lift (M := nonZeroDivisors O) hunit`. Use `⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩` and prove the remaining obligations. Rewrite using `[hgφ, Category.assoc, ← Spec.map_comp]`. Use `congr 2`. Use extensionality with `b`.

Simplify using `[ψ]`.
-/
theorem factor_through_fractionField_of_range :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (T : Scheme.{0})
      (g : T ⟶ Sp O), Set.range g ⊆ Set.range (spMap (algebraMap O K)) →
        ∃ f : T ⟶ Sp K, f ≫ spMap (algebraMap O K) = g := by
  intro O K _ _ _ _ _ T g hg
  let φ : O →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ g.appTop).hom
  have hgφ : g = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
    have h := Scheme.toSpecΓ_naturality g
    have e : g = g ≫ (Sp O).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv := by simp
    rw [e, ← Category.assoc, h, Category.assoc, ← Spec.map_comp]
    simp [φ]
  have hunit : ∀ b : nonZeroDivisors O, IsUnit (φ b) := by
    rintro ⟨b, hb⟩
    refine T.toRingedSpace.isUnit_of_isUnit_germ ⊤ (φ b) fun x hx => ?_
    have hmem : x ∈ T.basicOpen (φ b) := by
      have e : T.basicOpen (φ b) = g ⁻¹ᵁ (Sp O).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv b) := by
        rw [Scheme.preimage_basicOpen_top]; rfl
      rw [e]
      show g x ∈ (Sp O).basicOpen _
      rw [basicOpen_eq_of_affine (R := CommRingCat.of O) b]
      obtain ⟨y, hy⟩ := hg ⟨x, rfl⟩
      show b ∉ (g x).asIdeal
      rw [← hy]
      intro hbm
      have hbm' : algebraMap O K b ∈ y.asIdeal := hbm
      have hu : IsUnit (algebraMap O K b) :=
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb).isUnit
      exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hbm' hu)
    exact (T.mem_basicOpen (φ b) x hx).1 hmem
  let ψ : K →+* Γ(T, ⊤) := IsLocalization.lift (M := nonZeroDivisors O) hunit
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
  rw [hgφ, Category.assoc, ← Spec.map_comp]
  congr 2
  ext b
  simp [ψ]

end GlobalTheory
