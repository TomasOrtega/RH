import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

/- English proof (translation)
Establish `hf : f y ∈ U` using `e hy`. Establish `key` using `Y.presheaf.germ_res_apply (homOfLE e) y hy ((f.app U).hom a)`. Unfold `gs`. Rewrite using `[dif_pos hf]`. Use `split_ifs with h1`.

Conclude with `key`. Conclude with `absurd hy h1`.
-/
theorem gs_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (y : Y) (hy : y ∈ V)
    (a : Γ(X, U)) : gs (𝟙 Y) y V ((f.appLE U V e).hom a) = gs f y U a := by
  have hf : f y ∈ U := e hy
  have key := Y.presheaf.germ_res_apply (homOfLE e) y hy ((f.app U).hom a)
  unfold gs
  rw [dif_pos hf]
  split_ifs with h1
  · exact key
  · exact absurd hy h1

/- English proof (translation)
Establish `key` using `congrArg (fun g => (CommRingCat.Hom.hom g) (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key`. Unfold `gm`. Rewrite using `[dif_pos (show (spMap f) z ∈ (⊤ : (Sp A).Opens) from trivial)]`. Rewrite using `[dif_pos (show (𝟙 (Sp B)) z ∈ (⊤ : (Sp B).Opens) from trivial)]`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [MonoidHom.comp_apply, Units.coe_map, pullU, unitΓ, toΓ, MonoidHom.coe_coe, Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]`. Use `erw [key]`. Both sides reduce to the same expression.
-/
theorem gm_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (z : Sp B) :
    gm (spMap f) z ⊤ (unitΓ u) = gm (𝟙 _) z ⊤ (unitΓ (Units.map (f : A →* B) u)) := by
  have key := congrArg (fun g => (CommRingCat.Hom.hom g) (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  unfold gm
  rw [dif_pos (show (spMap f) z ∈ (⊤ : (Sp A).Opens) from trivial)]
  rw [dif_pos (show (𝟙 (Sp B)) z ∈ (⊤ : (Sp B).Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, pullU, unitΓ, toΓ, MonoidHom.coe_coe, Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]
  erw [key]
  rfl

/- English proof (translation)
Establish `hz : r z ∈ t.PP.L.wchart φ (fun k => J (r ≫ φ k))` using `by show r z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k)))`. Use `Set.mem_iInter.2 fun k => ?_` and prove the remaining obligations. Use `hJ (r ≫ φ k)` as an intermediate fact. Simplify `this` using `[Scheme.Hom.comp_apply]`. Unfold `val scaleGenG`.

Use `erw [map_mul, gm_res r z _ hz]`.
-/
theorem val_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u c) r z J = gm r z ⊤ u * val c r z J := by
  have hz : r z ∈ t.PP.L.wchart φ (fun k => J (r ≫ φ k)) := by
    show r z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k)))
    refine Set.mem_iInter.2 fun k => ?_
    have := hJ (r ≫ φ k)
    simpa [Scheme.Hom.comp_apply] using this
  unfold val scaleGenG
  erw [map_mul, gm_res r z _ hz]

/- English proof (translation)
The claim follows from `map_pow _ _ _`.
-/
theorem val_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (genPowG t φ ε c n) r z J = val c r z J ^ n :=
  map_pow _ _ _

/- English proof (translation)
Establish `hsurj : Function.Surjective (jetAug : Jet k κ n →ₐ[k] k).toRingHom` using `fun c => ⟨algebraMap k _ c, (jetAug : Jet k κ n →ₐ[k] k).commutes c⟩`. Establish `hnil : ∀ a : Jet k κ n, jetAug a = 0 → IsNilpotent a`. Introduce `a ha`. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `h0 : MvPolynomial.constantCoeff P = 0`.

Establish `: jetAug (Ideal.Quotient.mk _ P : Jet k κ n) = MvPolynomial.aeval (fun _ : κ => (0 : k)) P` using `rfl`. Rewrite `ha` using `[this]`. Simplify `ha` using `[MvPolynomial.aeval_zero']`. Establish `hP : P ∈ orig k κ`. Establish `: P ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set κ))`.

Rewrite using `[MvPolynomial.mem_ideal_span_X_image]`. Introduce `m hm`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hm0 : m = 0` using `by ext i; exact hc i (Set.mem_univ i)`.

Substitute `hm0` using the available equality. Rewrite `hm` using `[MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq]`. Conclude with `hm h0`. Simplify `this` using `[orig, Set.image_univ]`. Use `⟨n + 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.pow_mem_pow hP _`. Establish `hrange` using `range_comap_of_surjective _ _ hsurj`. Establish `huniv : PrimeSpectrum.zeroLocus (RingHom.ker (jetAug : Jet k κ n →ₐ[k] k).toRingHom : Set (Jet k κ n)) = Set.univ`. Rewrite using `[PrimeSpectrum.zeroLocus_eq_univ_iff]`.

Introduce `a ha`. Conclude with `mem_nilradical.2 (hnil a (RingHom.mem_ker.1 ha))`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : q ∈ Set.range (PrimeSpectrum.comap (jetAug : Jet k κ n →ₐ[k] k).toRingHom) := by`. Rewrite using `[hrange, huniv]`. Discharge the goal by the elementary cases of `trivial`.

Establish `hl` using `congrArg (fun g => Over.Hom.left g) h`. Simplify using `only [Over.comp_left] at hl`. Establish `hq : ψ.left q = (1 : overAt x k ⟶ t.G).left p`. Rewrite using `[← hl, ← hp]`. Both sides reduce to the same expression.

Rewrite using `[hq]`. Conclude with `hj₀ (show p ∈ (⊤ : (Sp k).Opens) from trivial)`.
-/
theorem jet_left_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {k : Type} [Field k] (x : Sp k ⟶ X0) {κ : Type} {n : ℕ} (j₀ : t.PP.L.ι)
    (hj₀ : ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀) (ψ : overAt x (Jet k κ n) ⟶ t.G)
    (h : homAt x (jetAug : Jet k κ n →ₐ[k] k) ≫ ψ = 1) (q : Sp (Jet k κ n)) : ψ.left q ∈ t.PP.L.U j₀ := by
  have hsurj : Function.Surjective (jetAug : Jet k κ n →ₐ[k] k).toRingHom :=
    fun c => ⟨algebraMap k _ c, (jetAug : Jet k κ n →ₐ[k] k).commutes c⟩
  have hnil : ∀ a : Jet k κ n, jetAug a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff P = 0 := by
      have : jetAug (Ideal.Quotient.mk _ P : Jet k κ n) = MvPolynomial.aeval (fun _ : κ => (0 : k)) P := rfl
      rw [this] at ha
      simpa [MvPolynomial.aeval_zero'] using ha
    have hP : P ∈ orig k κ := by
      have : P ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set κ)) := by
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        by_contra hc
        push_neg at hc
        have hm0 : m = 0 := by ext i; exact hc i (Set.mem_univ i)
        subst hm0
        rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq] at hm
        exact hm h0
      simpa [orig, Set.image_univ] using this
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hP _
  have hrange := range_comap_of_surjective _ _ hsurj
  have huniv : PrimeSpectrum.zeroLocus (RingHom.ker (jetAug : Jet k κ n →ₐ[k] k).toRingHom : Set (Jet k κ n)) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro a ha
    exact mem_nilradical.2 (hnil a (RingHom.mem_ker.1 ha))
  obtain ⟨p, hp⟩ : q ∈ Set.range (PrimeSpectrum.comap (jetAug : Jet k κ n →ₐ[k] k).toRingHom) := by
    rw [hrange, huniv]; trivial
  have hl := congrArg (fun g => Over.Hom.left g) h
  simp only [Over.comp_left] at hl
  have hq : ψ.left q = (1 : overAt x k ⟶ t.G).left p := by
    rw [← hl, ← hp]
    rfl
  rw [hq]
  exact hj₀ (show p ∈ (⊤ : (Sp k).Opens) from trivial)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
