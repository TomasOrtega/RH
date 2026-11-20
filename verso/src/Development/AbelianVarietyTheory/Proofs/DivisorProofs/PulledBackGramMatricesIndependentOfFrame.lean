import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

section Pull

variable {F : Type} [Field F] {σ : F →+* ℂ} {X Y : Var F}

/- English proof (translation)
Take `⟨U, hy, a, e⟩` from `(mem_O_ratOf.1 hx).exists_fnOf`. Rewrite using `[← e, ratVal_fnOf (mem_ptsIn.2 hy), ← valF_fromSpecStalk]`. Use `(GlobalTheory.ZH.RatModel.val_valF (M := ratOf X) ?_ a).symm` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Subsingleton.elim (α := PrimeSpectrum ℂ) w (IsLocalRing.closedPoint ℂ)]` and apply the resulting hypothesis.
-/
theorem ratVal_eq_val_ratOf (y : CxPts X.str σ) {x : X.Fn} (hx : x ∈ (ratOf X).O (under y)) :
    ratVal x y = (ratOf X).val y.1 x := by
  obtain ⟨U, hy, a, e⟩ := (mem_O_ratOf.1 hx).exists_fnOf
  rw [← e, ratVal_fnOf (mem_ptsIn.2 hy), ← valF_fromSpecStalk]
  refine (GlobalTheory.ZH.RatModel.val_valF (M := ratOf X) ?_ a).symm
  rintro _ ⟨w, rfl⟩
  rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) w (IsLocalRing.closedPoint ℂ)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem under_ptMap (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (z : CxPts Y.str σ) :
    under (ptMap σ f hf z) = f (under z) := rfl

/- English proof (translation)
Rewrite using `[ratVal_eq_val_ratOf z (hφ.map_mem_O hg), ratVal_eq_val_ratOf (ptMap σ f hf z) hg]`. Conclude with `(hφ.val_comp z.1 _ hg).symm`.
-/
theorem ratVal_pull {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hφ : (ratOf X).IsHom (ratOf Y) φ f)
    (hf : f ≫ X.str = Y.str) (z : CxPts Y.str σ) {g : X.Fn} (hg : g ∈ (ratOf X).O (f (under z))) :
    ratVal (φ g) z = ratVal g (ptMap σ f hf z) := by
  rw [ratVal_eq_val_ratOf z (hφ.map_mem_O hg), ratVal_eq_val_ratOf (ptMap σ f hf z) hg]
  exact (hφ.val_comp z.1 _ hg).symm

end Pull

/- English proof (translation)
Introduce `F _ σ X Y ι m E E' φ f hf hR H hH z`. Use `⟨under_ptMap f hf z, ?_⟩` and prove the remaining obligations. Introduce `A hA B hB τ`. Establish `hA' : A ∈ E.S (under (ptMap σ f hf z))` using `hA`. Establish `hA₀ : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (f (under z))` using `(E.nonempty (under (ptMap σ f hf z))).choose_spec`.

Establish `hA₀' : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (under (ptMap σ f hf z))` using `(E.nonempty (under (ptMap σ f hf z))).choose_spec`. Establish `htr` using `hH.trans (ptMap σ f hf z) mem_ptsIn_top A hA' _ hA₀' τ`. Unfold `pullGram`. Rewrite using `[htr]`. Generalize the expression as in `(E.nonempty (under (ptMap σ f hf z))).choose = A₀ at hA₀ hA₀'`.

Establish `hg : Par 0 ((ratOf Y).O (under z)).toSubring (B * (A₀.map φ)⁻¹)` using `hR.sub (under z) B hB A₀ hA₀`. Establish `hc : Par 0 ((ratOf X).O (f (under z))).toSubring (A₀ * A⁻¹)` using `(Fr.mem_iff hA).1 hA₀`. Establish `hh : Par 0 ((ratOf Y).O (under z)).toSubring ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn))` using `hc.map (φ : X.Fn →+* Y.Fn) fun x hx => hR.hom.map_mem_O hx`. Establish `hprod : B * (A₀.map φ)⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map φ)⁻¹`. Express the relevant statement in the definitionally equal form `B * (A₀.map (φ : X.Fn →+* Y.Fn))⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map (φ : X.Fn →+* Y.Fn))⁻¹`.

Rewrite using `[Mat.map_mul, ← Mat.map_inv, mul_assoc, ← mul_assoc (A₀⁻¹.map _), ← Mat.map_mul, Mat.inv_mul (Fr.det_ne hA₀), Mat.map_one, one_mul, Mat.map_inv]`. Take `⟨ψ, hψ⟩` from `exists_ratVal_hom (X := Y) (σ := σ) z`. Establish `hmul` using `hg.map_mul_of hh (ratVal · z) ψ hψ`. Rewrite `hmul` using `[hprod]`. Establish `hval : ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn)).map (ratVal · z) = (A₀ * A⁻¹).map (ratVal · (ptMap σ f hf z))`.

Use function extensionality and compare the values at `τ'`. Use extensionality with `i j`. Conclude with `ratVal_pull hR.hom hf z ((hc τ').1 i j)`. Rewrite `hmul` using `[hval]`. Rewrite using `[hmul, Pi.mul_apply, Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`.
-/
theorem pullGram_eq_of_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (z : CxPts Y.str σ), under (ptMap σ f hf z) = f (under z) ∧ ∀ A ∈ E.S (f (under z)), ∀ B ∈ E'.S (under z), ∀ τ, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ * H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
  intro F _ σ X Y ι m E E' φ f hf hR H hH z
  refine ⟨under_ptMap f hf z, ?_⟩
  intro A hA B hB τ
  have hA' : A ∈ E.S (under (ptMap σ f hf z)) := hA
  have hA₀ : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (f (under z)) :=
    (E.nonempty (under (ptMap σ f hf z))).choose_spec
  have hA₀' : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (under (ptMap σ f hf z)) :=
    (E.nonempty (under (ptMap σ f hf z))).choose_spec
  have htr := hH.trans (ptMap σ f hf z) mem_ptsIn_top A hA' _ hA₀' τ
  unfold pullGram
  rw [htr]
  generalize (E.nonempty (under (ptMap σ f hf z))).choose = A₀ at hA₀ hA₀'

  have hg : Par 0 ((ratOf Y).O (under z)).toSubring (B * (A₀.map φ)⁻¹) := hR.sub (under z) B hB A₀ hA₀
  have hc : Par 0 ((ratOf X).O (f (under z))).toSubring (A₀ * A⁻¹) := (Fr.mem_iff hA).1 hA₀
  have hh : Par 0 ((ratOf Y).O (under z)).toSubring ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn)) :=
    hc.map (φ : X.Fn →+* Y.Fn) fun x hx => hR.hom.map_mem_O hx
  have hprod : B * (A₀.map φ)⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map φ)⁻¹ := by
    change B * (A₀.map (φ : X.Fn →+* Y.Fn))⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map (φ : X.Fn →+* Y.Fn))⁻¹
    rw [Mat.map_mul, ← Mat.map_inv, mul_assoc, ← mul_assoc (A₀⁻¹.map _), ← Mat.map_mul,
      Mat.inv_mul (Fr.det_ne hA₀), Mat.map_one, one_mul, Mat.map_inv]
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) z
  have hmul := hg.map_mul_of hh (ratVal · z) ψ hψ
  rw [hprod] at hmul
  have hval : ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn)).map (ratVal · z) = (A₀ * A⁻¹).map (ratVal · (ptMap σ f hf z)) := by
    funext τ'
    ext i j
    exact ratVal_pull hR.hom hf z ((hc τ').1 i j)
  rw [hval] at hmul
  rw [hmul, Pi.mul_apply, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end GlobalTheory.ChernCalc
