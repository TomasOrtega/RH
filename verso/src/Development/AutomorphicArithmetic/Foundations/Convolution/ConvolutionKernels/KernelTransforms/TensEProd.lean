import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Establish `hG : ∀ b, ∏ᶠ a : {a : A // p a b}, f a.1 = ∏ a ∈ hf.toFinset with π a = b, f a`. Introduce `b`. Rewrite using `[finprod_subtype_eq_finprod_cond]`. Use `finprod_cond_eq_prod_of_cond_iff _ fun {x} hx => ?_` and prove the remaining obligations. Simplify using `[hp, Function.mem_mulSupport, hx]`.

Repeatedly rewrite using `[hG]`. Rewrite using `[finprod_eq_prod_of_mulSupport_toFinset_subset f hf subset_rfl]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := hf.toFinset.image π)]`. Conclude with `Finset.prod_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) f`. Introduce `b hb`.

Assume the negation of the conclusion as `hb'`. Use `hb ?_` and prove the remaining obligations. Use `Finset.prod_eq_one fun x hx => ?_` and prove the remaining obligations. It suffices to derive a contradiction. Rewrite `hx` using `[Finset.mem_filter]`.

Conclude with `hb' (by simpa using ⟨x, by simpa using hx.1, hx.2⟩)`.
-/
private theorem finprod_fib {A B M : Type*} [CommMonoid M] (π : A → B) (p : A → B → Prop)
    (hp : ∀ a b, p a b ↔ π a = b) (f : A → M) (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ b : B, ∏ᶠ a : {a : A // p a b}, f a.1 = ∏ᶠ a : A, f a := by
  classical
  have hG : ∀ b, ∏ᶠ a : {a : A // p a b}, f a.1 = ∏ a ∈ hf.toFinset with π a = b, f a := by
    intro b
    rw [finprod_subtype_eq_finprod_cond]
    refine finprod_cond_eq_prod_of_cond_iff _ fun {x} hx => ?_
    simp [hp, Function.mem_mulSupport, hx]
  simp_rw [hG]
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf subset_rfl]
  rw [finprod_eq_prod_of_mulSupport_subset (s := hf.toFinset.image π)]
  · exact Finset.prod_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) f
  · intro b hb
    by_contra hb'
    refine hb ?_
    refine Finset.prod_eq_one fun x hx => ?_
    exfalso
    rw [Finset.mem_filter] at hx
    exact hb' (by simpa using ⟨x, by simpa using hx.1, hx.2⟩)

/- English proof (translation)
Introduce `F E _ _ _ _ _ n h hh g`. Establish `hS : (Function.mulSupport fun w : Pl E => h w (finAt w g)).Finite`. Establish `hev : ∀ᶠ w : Pl E in Filter.cofinite, h w (finAt w g) = 1` using `by filter_upwards [hh, AdelicGLn.eventually_mem_integralGL E n g] with w h1 h2`. Rewrite using `[h1, Set.indicator_of_mem (by exact h2)]`. Both sides reduce to the same expression.

Conclude with `Filter.eventually_cofinite.1 hev`. Establish `e : ∀ v : Pl F, GM.prodFn (v` using `v) (fun w => h w.1) (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g) = ∏ᶠ w : {w : Pl E // w.asIdeal.LiesOver v.asIdeal}, h w.1 (finAt w.1 g) := by`. Introduce `v`. Use `finprod_congr fun w => ?_` and prove the remaining obligations. Establish `: GM.cmp w (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g) = finAt w.1 g`.

Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[this]`. Repeatedly rewrite using `[e]`. Use `finprod_fib (fun w : Pl E => w.under (𝓞 F)) (fun w v => w.asIdeal.LiesOver v.asIdeal) ?_ _ hS` and prove the remaining obligations.

Introduce `w v`. Prove the components needed by the constructor for the conclusion. Introduce `hl ext1`. Conclude with `(hl.over).symm`. Introduce and unpack `rfl`.

Conclude with `⟨rfl⟩`.
-/
theorem UpperTheory.ConvolutionTheory.Tf.tensEProd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ),
      (∀ᶠ w : Pl E in Filter.cofinite, h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))).indicator 1) →
      ∀ g : AdelicGLn.AdelicGL E n,
        ∏ᶠ v : Pl F, GM.prodFn (v := v) (fun w => h w.1) (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g) = ∏ᶠ w : Pl E, h w (finAt w g) := by
  intro F E _ _ _ _ _ n h hh g
  have hS : (Function.mulSupport fun w : Pl E => h w (finAt w g)).Finite := by
    have hev : ∀ᶠ w : Pl E in Filter.cofinite, h w (finAt w g) = 1 := by
      filter_upwards [hh, AdelicGLn.eventually_mem_integralGL E n g] with w h1 h2
      rw [h1, Set.indicator_of_mem (by exact h2)]
      rfl
    exact Filter.eventually_cofinite.1 hev
  have e : ∀ v : Pl F, GM.prodFn (v := v) (fun w => h w.1) (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g)
      = ∏ᶠ w : {w : Pl E // w.asIdeal.LiesOver v.asIdeal}, h w.1 (finAt w.1 g) := by
    intro v
    refine finprod_congr fun w => ?_
    have : GM.cmp w (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g) = finAt w.1 g := by
      ext i j
      rfl
    rw [this]
  simp_rw [e]
  refine finprod_fib (fun w : Pl E => w.under (𝓞 F)) (fun w v => w.asIdeal.LiesOver v.asIdeal) ?_ _ hS
  intro w v
  constructor
  · intro hl
    ext1
    exact (hl.over).symm
  · rintro rfl
    exact ⟨rfl⟩
