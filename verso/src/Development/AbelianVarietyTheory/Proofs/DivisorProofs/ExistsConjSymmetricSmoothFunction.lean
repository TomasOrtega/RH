import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ContDiff

namespace GlobalTheory.Mean4O.ConjSmooth

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Conclude with `congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by simp))`.
-/
theorem spMap_conj_conj : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by simp))

/- English proof (translation)
Use `(contDiff_piLp 2).2 fun a => ?_` and prove the remaining obligations. Conclude with `Complex.conjCLE.contDiff.comp ((contDiff_piLp 2).1 contDiff_id a)`.
-/
theorem contDiff_conjCoord (d : ℕ) : ContDiff ℝ ∞ (GlobalTheory.ConjChart.conjCoord d) := by
  refine (contDiff_piLp 2).2 fun a => ?_
  exact Complex.conjCLE.contDiff.comp ((contDiff_piLp 2).1 contDiff_id a)

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)

/- English proof (translation)
Set `R : AnRead Y.str (I.ε b) e` to `{ ι := Fin (M.A b).n chart := fun j => (I.alg b j).choose cover := fun y => by`. Take `⟨j, hj⟩` from `(M.A b).cover ((I.pt b).symm y)`. Use `⟨j, ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[(I.alg b j).choose_spec]`. Simplify using `using hj }`.

Use `AnRead.SmoothOn.chart (R := R) (fun j => ?_) isOpen_univ c` and prove the remaining obligations. Establish `h1` using `hg j`. Rewrite `h1` using `[(I.alg b j).choose_spec]`. Use `(AlgChart.contDiffOn_finChart_iff _ _ _ _).1 ?_` and prove the remaining obligations. Simplify `h1` using `[Function.comp_def]`.
-/
theorem contDiffOn_chart {b : Fin (M.n + 1)} {g : M.X b → ℝ} (hg : (M.A b).Smooth g) (c : AlgChart Y.str (I.ε b) e) :
    ContDiffOn ℝ ∞ ((g ∘ (I.pt b).symm) ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' Set.univ) := by
  let R : AnRead Y.str (I.ε b) e :=
    { ι := Fin (M.A b).n
      chart := fun j => (I.alg b j).choose
      cover := fun y => by
        obtain ⟨j, hj⟩ := (M.A b).cover ((I.pt b).symm y)
        refine ⟨j, ?_⟩
        rw [(I.alg b j).choose_spec] at hj
        simpa using hj }
  refine AnRead.SmoothOn.chart (R := R) (fun j => ?_) isOpen_univ c
  have h1 := hg j
  rw [(I.alg b j).choose_spec] at h1
  refine (AlgChart.contDiffOn_finChart_iff _ _ _ _).1 ?_
  simpa [Function.comp_def] using h1

def conjVal (f : M.Fun) (a' b : Fin (M.n + 1)) (h : I.ε b = (starRingEnd ℂ).comp (I.ε a')) (x' : M.X a') : ℝ :=
  f b ((I.pt b).symm (GlobalTheory.ConjChart.conjPts Y.str h (I.pt a' x')))

/- English proof (translation)
Introduce `j`. Take `⟨c', hc'⟩` from `I.alg a' j`. Establish `key` using `contDiffOn_chart I (hf b) (GlobalTheory.ConjChart.conjChart h c')`. Establish `hcc : ContDiffOn ℝ ∞ ((f b ∘ (I.pt b).symm ∘ GlobalTheory.ConjChart.conjPts Y.str h) ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' Set.univ)`. Use `key.comp (contDiff_conjCoord e).contDiffOn (s := c'.e.target ∩ c'.e.symm ⁻¹' Set.univ) (fun v hv => ⟨by show (GlobalTheory.ConjChart.conjCoord e).symm (GlobalTheory.ConjChart.conjCoord e v) ∈ c'.e.target` as an intermediate fact.

Rewrite using `[Homeomorph.symm_apply_apply]`. Conclude with `hv.1, trivial⟩)`. Use `this.congr fun v _ => ?_` and prove the remaining obligations. Use `show f b ((I.pt b).symm (GlobalTheory.ConjChart.conjPts Y.str h (c'.e.symm v))) = f b ((I.pt b).symm ((GlobalTheory.ConjChart.conjPts Y.str h).symm.symm (c'.e.symm ((GlobalTheory.ConjChart.conjCoord e).symm (GlobalTheory.ConjChart.conjCoord e v)))))`. Rewrite using `[Homeomorph.symm_apply_apply, Homeomorph.symm_symm]`.

Rewrite using `[hc']`. Use `(AlgChart.contDiffOn_finChart_iff c' ∞ Set.univ (f b ∘ (I.pt b).symm ∘ GlobalTheory.ConjChart.conjPts Y.str h)).2 hcc` as an intermediate fact. Simplify `this` using `[conjVal, Function.comp_def]`.
-/
theorem smooth_conjVal (f : M.Fun) (hf : M.Smooth f) (a' b : Fin (M.n + 1))
    (h : I.ε b = (starRingEnd ℂ).comp (I.ε a')) : (M.A a').Smooth (conjVal I f a' b h) := by
  intro j
  obtain ⟨c', hc'⟩ := I.alg a' j
  have key := contDiffOn_chart I (hf b) (GlobalTheory.ConjChart.conjChart h c')
  have hcc : ContDiffOn ℝ ∞ ((f b ∘ (I.pt b).symm ∘ GlobalTheory.ConjChart.conjPts Y.str h) ∘ c'.e.symm)
      (c'.e.target ∩ c'.e.symm ⁻¹' Set.univ) := by
    have := key.comp (contDiff_conjCoord e).contDiffOn (s := c'.e.target ∩ c'.e.symm ⁻¹' Set.univ)
      (fun v hv => ⟨by
        show (GlobalTheory.ConjChart.conjCoord e).symm (GlobalTheory.ConjChart.conjCoord e v) ∈ c'.e.target
        rw [Homeomorph.symm_apply_apply]
        exact hv.1, trivial⟩)
    refine this.congr fun v _ => ?_
    show f b ((I.pt b).symm (GlobalTheory.ConjChart.conjPts Y.str h (c'.e.symm v))) =
      f b ((I.pt b).symm ((GlobalTheory.ConjChart.conjPts Y.str h).symm.symm
        (c'.e.symm ((GlobalTheory.ConjChart.conjCoord e).symm (GlobalTheory.ConjChart.conjCoord e v)))))
    rw [Homeomorph.symm_apply_apply, Homeomorph.symm_symm]
  rw [hc']
  have := (AlgChart.contDiffOn_finChart_iff c' ∞ Set.univ (f b ∘ (I.pt b).symm ∘ GlobalTheory.ConjChart.conjPts Y.str h)).2 hcc
  simpa [conjVal, Function.comp_def] using this

/- English proof (translation)
Establish `h1` using `(I.pt a' x').2`. Establish `h2` using `(I.pt a x).2`. Express the relevant statement in the definitionally equal form `(I.pt a' x').1 ≫ Y.str = spMap (I.ε a') at h1`. Express the relevant statement in the definitionally equal form `(I.pt a x).1 ≫ Y.str = spMap (I.ε a) at h2`. Rewrite `h1` using `[hx, Category.assoc, h2, spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Establish `h4 : (starRingEnd ℂ).comp (I.ε a) = I.ε a'`. Use `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)` as an intermediate fact. Simplify using `using this`. Establish `hε : I.ε b = I.ε a`. Rewrite using `[h, ← h4]`.

Conclude with `RingHom.ext fun z => by simp`. Take `rfl : b = a` from `I.ε.injective hε`. Unfold `conjVal`. Use `congr 1`. Rewrite using `[Homeomorph.symm_apply_eq]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show spMap (starRingEnd ℂ) ≫ (I.pt a' x').1 = (I.pt b x).1`. Rewrite using `[hx, ← Category.assoc, spMap_conj_conj, Category.id_comp]`.
-/
theorem conjVal_eq (f : M.Fun) {a a' : Fin (M.n + 1)} {x : M.X a} {x' : M.X a'}
    (hx : (I.pt a' x').1 = spMap (starRingEnd ℂ) ≫ (I.pt a x).1) (b : Fin (M.n + 1))
    (h : I.ε b = (starRingEnd ℂ).comp (I.ε a')) : conjVal I f a' b h x' = f a x := by
  have h1 := (I.pt a' x').2
  have h2 := (I.pt a x).2
  change (I.pt a' x').1 ≫ Y.str = spMap (I.ε a') at h1
  change (I.pt a x).1 ≫ Y.str = spMap (I.ε a) at h2
  rw [hx, Category.assoc, h2, spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
  have h4 : (starRingEnd ℂ).comp (I.ε a) = I.ε a' := by
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    simpa using this
  have hε : I.ε b = I.ε a := by
    rw [h, ← h4]
    exact RingHom.ext fun z => by simp
  obtain rfl : b = a := I.ε.injective hε
  unfold conjVal
  congr 1
  rw [Homeomorph.symm_apply_eq]
  apply Subtype.ext
  show spMap (starRingEnd ℂ) ≫ (I.pt a' x').1 = (I.pt b x).1
  rw [hx, ← Category.assoc, spMap_conj_conj, Category.id_comp]

/- English proof (translation)
Introduce `F _ _ Y e M I f hf`. Establish `hb (a' : Fin (M.n + 1)) : I.ε (I.ε.symm ((starRingEnd ℂ).comp (I.ε a'))) = (starRingEnd ℂ).comp (I.ε a')` using `I.ε.apply_symm_apply _`. Conclude with `⟨fun a' => conjVal I f a' _ (hb a'), fun a' => smooth_conjVal I f hf a' _ _, fun a a' x x' hx => conjVal_eq I f hx _ _⟩`.
-/
theorem exists_smooth_conj : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y)
    (f : M.Fun), M.Smooth f → ∃ f' : M.Fun, M.Smooth f' ∧
      ∀ a a' x x', (I.pt a' x').1 = spMap (starRingEnd ℂ) ≫ (I.pt a x).1 → f' a' x' = f a x := by
  intro F _ _ Y e M I f hf
  have hb (a' : Fin (M.n + 1)) : I.ε (I.ε.symm ((starRingEnd ℂ).comp (I.ε a'))) = (starRingEnd ℂ).comp (I.ε a') :=
    I.ε.apply_symm_apply _
  exact ⟨fun a' => conjVal I f a' _ (hb a'), fun a' => smooth_conjVal I f hf a' _ _,
    fun a a' x x' hx => conjVal_eq I f hx _ _⟩

end GlobalTheory.Mean4O.ConjSmooth
