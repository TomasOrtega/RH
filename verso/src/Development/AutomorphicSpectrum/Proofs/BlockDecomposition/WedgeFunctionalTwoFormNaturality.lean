import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeTwoForm

section Generic

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}

/- English proof (translation)
Establish `h1 : ∀ i, ∑ j, g i j = ∑ j ∈ Finset.Ioi i, g i j + ∑ j ∈ Finset.Iio i, g i j`. Introduce `i`. Establish `e : (Finset.univ : Finset (Fin n)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i)`. Use extensionality with `j`. Simplify using `only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton, Finset.mem_Iio, true_iff]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, Finset.sum_union, Finset.sum_union]`. Simplify using `[hd]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.disjoint_left]`.

Introduce `j`. Simplify using `only [Finset.mem_Ioi, Finset.mem_union, Finset.mem_singleton, Finset.mem_Iio]`. Use linear arithmetic over natural numbers and integers. Repeatedly rewrite using `[h1, Finset.sum_add_distrib]`. Use `congr 1`.

Conclude with `Finset.sum_comm' (by simp)`.
-/
theorem sum_pairs {N : Type} [AddCommMonoid N] (g : Fin n → Fin n → N) (hd : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j ∈ Finset.Ioi i, (g i j + g j i) := by
  have h1 : ∀ i, ∑ j, g i j = ∑ j ∈ Finset.Ioi i, g i j + ∑ j ∈ Finset.Iio i, g i j := by
    intro i
    have e : (Finset.univ : Finset (Fin n)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton,
        Finset.mem_Iio, true_iff]; omega
    rw [e, Finset.sum_union, Finset.sum_union]
    · simp [hd]
    · simp
    · rw [Finset.disjoint_left]; intro j; simp only [Finset.mem_Ioi, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_Iio]; omega
  simp_rw [h1, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm' (by simp)

def L2 (L : Fin n → Module.Dual A M) (i j : Fin n) : ⋀[A]^2 M →ₗ[A] A :=
  exteriorPower.pairingDual A M 2 (exteriorPower.ιMulti A 2 ![L i, L j])

/- English proof (translation)
Rewrite using `[L2, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]`. Simplify using the standard rewrite rules.
-/
theorem wedge_functional_iota_multi (L : Fin n → Module.Dual A M) (i j : Fin n) (a b : M) :
    L2 L i j (exteriorPower.ιMulti A 2 ![a, b]) = L i a * L j b - L j a * L i b := by
  rw [L2, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp

def wb : M →ₗ[A] M →ₗ[A] ⋀[A]^2 M :=
  LinearMap.mk₂ A (fun a b ↦ exteriorPower.ιMulti A 2 ![a, b])
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, add_mul]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, mul_add]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wb_apply (a b : M) : wb (A := A) a b = exteriorPower.ιMulti A 2 ![a, b] := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (by simp [wb_apply, ExteriorAlgebra.ιMulti_apply])`.
-/
theorem wb_self (a : M) : wb (A := A) a a = 0 :=
  Subtype.ext (by simp [wb_apply, ExteriorAlgebra.ιMulti_apply])

/- English proof (translation)
The claim follows from `Subtype.ext (by simpa [wb_apply, ExteriorAlgebra.ιMulti_apply] using eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := A) b a))`.
-/
theorem wb_swap (a b : M) : wb (A := A) b a = -wb a b :=
  Subtype.ext (by
    simpa [wb_apply, ExteriorAlgebra.ιMulti_apply] using
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := A) b a))

/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> rfl`.
-/
theorem eq_two (v : Fin 2 → M) : v = ![v 0, v 1] := by
  ext i; fin_cases i <;> rfl

/- English proof (translation)
Establish `h1 : wb (A` using `A) a b = ∑ i, ∑ j, (L i a * L j b) • wb (A := A) (e i) (e j) := by conv_lhs => rw [h a, h b]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_smul, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Rewrite using `[h1, sum_pairs _ (fun i ↦ by rw [wb_self, smul_zero])]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[wb_swap (e i) (e j), sub_smul, smul_neg, sub_eq_add_neg]`.
-/
theorem wb_expand (e : Fin n → M) (L : Fin n → Module.Dual A M) (h : ∀ x, x = ∑ i, L i x • e i)
    (a b : M) :
    wb (A := A) a b = ∑ i, ∑ j ∈ Finset.Ioi i, (L i a * L j b - L j a * L i b) • wb (A := A) (e i) (e j) := by
  have h1 : wb (A := A) a b = ∑ i, ∑ j, (L i a * L j b) • wb (A := A) (e i) (e j) := by
    conv_lhs => rw [h a, h b]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_smul,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_comm]
  rw [h1, sum_pairs _ (fun i ↦ by rw [wb_self, smul_zero])]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [wb_swap (e i) (e j), sub_smul, smul_neg, sub_eq_add_neg]

/- English proof (translation)
Establish `hz : z ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2 (M` using `M))) := by`. Rewrite using `[exteriorPower.ιMulti_span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨v, rfl⟩` from `hx`. Establish `e1 : exteriorPower.ιMulti A 2 v = wb (A` using `A) (v 0) (v 1) := by rw [wb_apply, ← eq_two]`. Rewrite using `[e1]`. Use `conv_lhs => rw [wb_expand e L h]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[wb_apply (v 0), wedge_functional_iota_multi]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => conv_lhs => rw [hx, hy]`. Simplify using `only [map_add, add_smul, Finset.sum_add_distrib]`. Consider the case `smul c x _ hx => conv_lhs => rw [hx]`.

Simplify using `only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]`.
-/
theorem expand (e : Fin n → M) (L : Fin n → Module.Dual A M) (h : ∀ x, x = ∑ i, L i x • e i)
    (z : ⋀[A]^2 M) :
    z = ∑ i, ∑ j ∈ Finset.Ioi i, L2 L i j z • wb (A := A) (e i) (e j) := by
  have hz : z ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have e1 : exteriorPower.ιMulti A 2 v = wb (A := A) (v 0) (v 1) := by rw [wb_apply, ← eq_two]
    rw [e1]
    conv_lhs => rw [wb_expand e L h]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [wb_apply (v 0), wedge_functional_iota_multi]
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    simp only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]

end Generic

section Forms

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def wedgeAt (T : C) : Glob1 F [⋀^Fin 2]→ₗ[R] Om R (F.obj T) 2 where
  toMultilinearMap := ((exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R])).toMultilinearMap.restrictScalars
    R).compLinearMap fun _ ↦ evForm F T
  map_eq_zero_of_eq' v i j hv hij :=
    (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R])).map_eq_zero_of_eq _
      (congrArg (evForm F T) hv) hij

def nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2 :=
  LinearMap.pi fun T ↦ exteriorPower.alternatingMapLinearEquiv (wedgeAt F T)

/- English proof (translation)
Rewrite using `[wedge_eq_ιMulti]`. Express the relevant statement in the definitionally equal form `exteriorPower.alternatingMapLinearEquiv (wedgeAt F T) _ = _`. Rewrite using `[exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]`. Express the relevant statement in the definitionally equal form `exteriorPower.ιMulti (F.obj T) 2 (fun i ↦ evForm F T (![a, b] i)) = _`. Use `congr 1`.

Apply the tactic sequence `ext i; fin_cases i <;> rfl`.
-/
theorem nu_ιMulti (a b : Glob1 F) (T : C) :
    nu F (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T) := by
  rw [wedge_eq_ιMulti]
  change exteriorPower.alternatingMapLinearEquiv (wedgeAt F T) _ = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change exteriorPower.ιMulti (F.obj T) 2 (fun i ↦ evForm F T (![a, b] i)) = _
  congr 1
  ext i; fin_cases i <;> rfl

variable {F}

def Lf (hP : Par F) (l : Module.Dual R (Glob1 F)) (T : C) : Module.Dual (F.obj T) Ω[F.obj T⁄R] :=
  (hP T).lift (Algebra.linearMap R (F.obj T) ∘ₗ l)

/- English proof (translation)
The claim follows from `(hP T).lift_eq _ x`.
-/
theorem Lf_ev (hP : Par F) (l : Module.Dual R (Glob1 F)) (T : C) (x : Glob1 F) :
    Lf hP l T (evForm F T x) = algebraMap R (F.obj T) (l x) :=
  (hP T).lift_eq _ x

/- English proof (translation)
The claim follows from `(x.2 φ).symm`.
-/
theorem form_pullback_evaluation {T T' : C} (φ : T ⟶ T') (x : Glob1 F) : p1 F φ (evForm F T x) = evForm F T' x :=
  (x.2 φ).symm

/- English proof (translation)
Use `(hP T).inductionOn α _ (by simp) (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)` and prove the remaining obligations. Rewrite using `[form_pullback_evaluation, Lf_ev, Lf_ev, AlgHom.commutes]`. Rewrite using `[oneFormsMapOfFunctorMorphism_smul, map_smul, hy, map_smul, smul_eq_mul, smul_eq_mul, map_mul]`. Simplify using `only [map_add, hy, hz]`.
-/
theorem linear_form_extension_naturality (hP : Par F) (l : Module.Dual R (Glob1 F)) {T T' : C} (φ : T ⟶ T')
    (α : Ω[F.obj T⁄R]) : Lf hP l T' (p1 F φ α) = mp F φ (Lf hP l T α) := by
  refine (hP T).inductionOn α _ (by simp) (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [form_pullback_evaluation, Lf_ev, Lf_ev, AlgHom.commutes]
  · rw [oneFormsMapOfFunctorMorphism_smul, map_smul, hy, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  · simp only [map_add, hy, hz]

/- English proof (translation)
Use `(hP T).inductionOn α _ (by simp) (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)` and prove the remaining obligations. Use `conv_lhs => rw [h x]`. Simplify using `only [map_sum, map_smul, Lf_ev, algebraMap_smul]`. Use `conv_lhs => rw [hy]`. Simplify using `only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]`.

Use `conv_lhs => rw [hy, hz]`. Simplify using `only [map_add, add_smul, Finset.sum_add_distrib]`.
-/
theorem Lf_expand (hP : Par F) {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Module.Dual R (Glob1 F))
    (h : ∀ x, x = ∑ i, l i x • w i) (T : C) (α : Ω[F.obj T⁄R]) :
    α = ∑ i, Lf hP (l i) T α • evForm F T (w i) := by
  refine (hP T).inductionOn α _ (by simp) (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)
  · conv_lhs => rw [h x]
    simp only [map_sum, map_smul, Lf_ev, algebraMap_smul]
  · conv_lhs => rw [hy]
    simp only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]
  · conv_lhs => rw [hy, hz]
    simp only [map_add, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Establish `hz : z ∈ Submodule.span (F.obj T) (Set.range (exteriorPower.ιMulti (F.obj T) 2 (M` using `Ω[F.obj T⁄R]))) := by`. Rewrite using `[exteriorPower.ιMulti_span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨v, rfl⟩` from `hx`. Rewrite using `[eq_two v, ← wedge_eq_ιMulti, pOm_wedge, wedge_eq_ιMulti, wedge_eq_ιMulti, wedge_functional_iota_multi, wedge_functional_iota_multi]`. Simplify using `only [linear_form_extension_naturality, map_sub, map_mul]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [map_add, hx, hy]`.

Consider the case `smul c x _ hx => simp only [pOm_smul, map_smul, hx, smul_eq_mul, map_mul]`.
-/
theorem wedge_functional_two_form_naturality (hP : Par F) {n : ℕ} (l : Fin n → Module.Dual R (Glob1 F)) (i j : Fin n) {T T' : C}
    (φ : T ⟶ T') (z : Om R (F.obj T) 2) :
    L2 (fun i ↦ Lf hP (l i) T') i j (pOm F 2 φ z) = mp F φ (L2 (fun i ↦ Lf hP (l i) T) i j z) := by
  have hz : z ∈ Submodule.span (F.obj T) (Set.range (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [eq_two v, ← wedge_eq_ιMulti, pOm_wedge, wedge_eq_ιMulti, wedge_eq_ιMulti, wedge_functional_iota_multi, wedge_functional_iota_multi]
    simp only [linear_form_extension_naturality, map_sub, map_mul]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => simp only [pOm_smul, map_smul, hx, smul_eq_mul, map_mul]

/- English proof (translation)
Establish `ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M` using `Glob1 F))) := by`. Rewrite using `[exteriorPower.ιMulti_span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨v, rfl⟩` from `hx`. Rewrite using `[eq_two v, nu_ιMulti, wedge_eq_ιMulti, wedge_functional_iota_multi, wedge_functional_iota_multi]`. Express the relevant statement in the definitionally equal form `Lf hP (l i) T (evForm F T _) * Lf hP (l j) T (evForm F T _) - Lf hP (l j) T (evForm F T _) * Lf hP (l i) T (evForm F T _) = _`. Simplify using `only [Lf_ev, map_sub, map_mul]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy`. Simplify using `only [map_add, Pi.add_apply, hx, hy]`. Consider the case `smul c x _ hx`. Simplify using `only [map_smul, Pi.smul_apply, hx, smul_eq_mul, map_mul]`. Rewrite using `[← algebraMap_smul (F.obj T) c, map_smul, hx, smul_eq_mul]`.
-/
theorem wedge_functional_constant_on_image (hP : Par F) {n : ℕ} (l : Fin n → Module.Dual R (Glob1 F)) (i j : Fin n) (T : C)
    (t : ⋀[R]^2 (Glob1 F)) :
    L2 (fun i ↦ Lf hP (l i) T) i j (nu F t T) = algebraMap R (F.obj T) (L2 l i j t) := by
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := Glob1 F))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [eq_two v, nu_ιMulti, wedge_eq_ιMulti, wedge_functional_iota_multi, wedge_functional_iota_multi]
    change Lf hP (l i) T (evForm F T _) * Lf hP (l j) T (evForm F T _) -
      Lf hP (l j) T (evForm F T _) * Lf hP (l i) T (evForm F T _) = _
    simp only [Lf_ev, map_sub, map_mul]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]
  | smul c x _ hx =>
    simp only [map_smul, Pi.smul_apply, hx, smul_eq_mul, map_mul]
    rw [← algebraMap_smul (F.obj T) c, map_smul, hx, smul_eq_mul]

end Forms

/- English proof (translation)
Introduce `R _ C _ F ⟨hS, hP, hF, hPr⟩`. Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' R (Glob1 F)`. Take `⟨s, hs⟩` from `Module.projective_lifting_property f LinearMap.id hf`. Set `w : Fin n → Glob1 F` to `fun i ↦ f (Pi.single i 1)`. Set `l : Fin n → Module.Dual R (Glob1 F)` to `fun i ↦ LinearMap.proj i ∘ₗ s`.

Establish `hdual : ∀ x, x = ∑ i, l i x • w i`. Introduce `x`. Establish `h1 : f (s x) = x` using `LinearMap.congr_fun hs x`. Use `conv_lhs => rw [← h1, pi_eq_sum_univ' (s x)]`. Simplify using `[w, l, map_sum, map_smul]`.

Establish `hexp : ∀ (T : C) (z : Om R (F.obj T) 2), z = ∑ i, ∑ j ∈ Finset.Ioi i, L2 (fun i ↦ Lf hP (l i) T) i j z • wedge R _ (evForm F T (w i)) (evForm F T (w j))`. Introduce `T z`. Use `conv_lhs => rw [expand (fun i ↦ evForm F T (w i)) (fun i ↦ Lf hP (l i) T) (Lf_expand hP w l hdual T) z]`. Simplify using `only [wb_apply, wedge_eq_ιMulti]`. Use `⟨nu F, nu_ιMulti F, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`. Establish `h0 : ∀ i j, L2 l i j t = 0`. Introduce `i j`. Apply `hS.2` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use function extensionality and compare the values at `T`. Use `wedge_functional_constant_on_image hP l i j T t` as an intermediate fact. Rewrite `this` using `[ht]`. Simplify using `using this.symm`.

Rewrite using `[expand w l hdual t]`. Simplify using `[h0]`. Introduce `u hu`. Establish `hc : ∀ i j, ∃ r : R, ∀ T, algebraMap R (F.obj T) r = L2 (fun i ↦ Lf hP (l i) T) i j (u T)`. Introduce `i j`.

Establish `hz : d0 F (fun T ↦ L2 (fun i ↦ Lf hP (l i) T) i j (u T)) = 0`. Use function extensionality and compare the values at `T T' φ`. Rewrite using `[amitsur_d0_apply, hu T T' φ, wedge_functional_two_form_naturality, sub_self]`. Both sides reduce to the same expression. Take `⟨r, hr⟩` from `(hS.1 _).1 hz`.

Conclude with `⟨r, fun T ↦ congrFun hr T⟩`. Use `choose r hr using hc`. Use `⟨∑ i, ∑ j ∈ Finset.Ioi i, r i j • wb (A := R) (w i) (w j), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T`. Use `conv_rhs => rw [hexp T (u T)]`.

Simplify using `only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, wb_apply, nu_ιMulti]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← hr, algebraMap_smul]`. Both sides reduce to the same expression.
-/
theorem twoFormCohSt : TwoFormCohSt := by
  intro R _ C _ F ⟨hS, hP, hF, hPr⟩
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (Glob1 F)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let w : Fin n → Glob1 F := fun i ↦ f (Pi.single i 1)
  let l : Fin n → Module.Dual R (Glob1 F) := fun i ↦ LinearMap.proj i ∘ₗ s
  have hdual : ∀ x, x = ∑ i, l i x • w i := by
    intro x
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    conv_lhs => rw [← h1, pi_eq_sum_univ' (s x)]
    simp [w, l, map_sum, map_smul]
  have hexp : ∀ (T : C) (z : Om R (F.obj T) 2), z = ∑ i, ∑ j ∈ Finset.Ioi i,
      L2 (fun i ↦ Lf hP (l i) T) i j z • wedge R _ (evForm F T (w i)) (evForm F T (w j)) := by
    intro T z
    conv_lhs => rw [expand (fun i ↦ evForm F T (w i)) (fun i ↦ Lf hP (l i) T)
      (Lf_expand hP w l hdual T) z]
    simp only [wb_apply, wedge_eq_ιMulti]
  refine ⟨nu F, nu_ιMulti F, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro t ht
    have h0 : ∀ i j, L2 l i j t = 0 := by
      intro i j
      apply hS.2
      rw [map_zero]
      funext T
      have := wedge_functional_constant_on_image hP l i j T t
      rw [ht] at this
      simpa using this.symm
    rw [expand w l hdual t]
    simp [h0]
  · intro u hu
    have hc : ∀ i j, ∃ r : R, ∀ T, algebraMap R (F.obj T) r = L2 (fun i ↦ Lf hP (l i) T) i j (u T) := by
      intro i j
      have hz : d0 F (fun T ↦ L2 (fun i ↦ Lf hP (l i) T) i j (u T)) = 0 := by
        funext T T' φ
        rw [amitsur_d0_apply, hu T T' φ, wedge_functional_two_form_naturality, sub_self]
        rfl
      obtain ⟨r, hr⟩ := (hS.1 _).1 hz
      exact ⟨r, fun T ↦ congrFun hr T⟩
    choose r hr using hc
    refine ⟨∑ i, ∑ j ∈ Finset.Ioi i, r i j • wb (A := R) (w i) (w j), ?_⟩
    funext T
    conv_rhs => rw [hexp T (u T)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, wb_apply, nu_ιMulti]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hr, algebraMap_smul]
    rfl

end GlobalTheory.CompanionTheory.HodgeTwoForm
