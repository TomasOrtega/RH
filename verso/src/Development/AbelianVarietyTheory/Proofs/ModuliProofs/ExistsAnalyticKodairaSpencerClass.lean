import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicPeriodicCocycleCoboundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationAlongFibreOfSmoothStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocDerRegularCoeff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Exist

/- English proof (translation)
Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

/- English proof (translation)
The claim follows from `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)`.
-/
theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

/- English proof (translation)
Unfold `constFn`. Rewrite using `[map_zero, map_zero]`.
-/
theorem const_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

/- English proof (translation)
Rewrite using `[h.add W hW, h'.add W hW]; ring mul W hW f f' := by rw [h.mul W hW, h'.mul W hW]; ring res W W' e hW f := by rw [h.res W W' e hW, h'.res W W' e hW]`.
-/
theorem ptDer_add {X : Scheme.{0}} {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f + δ' W f) where
  add W hW f f' := by rw [h.add W hW, h'.add W hW]; ring
  mul W hW f f' := by rw [h.mul W hW, h'.mul W hW]; ring
  res W W' e hW f := by rw [h.res W W' e hW, h'.res W W' e hW]

/- English proof (translation)
Rewrite using `[h.add W (hW.trans inf_le_left), h'.add W (hW.trans inf_le_right)]; ring mul W hW f f' := by rw [h.mul W (hW.trans inf_le_left), h'.mul W (hW.trans inf_le_right)]; ring res W W' e hW f := by rw [h.res W W' e (hW.trans inf_le_left), h'.res W W' e (hW.trans inf_le_right), map_sub] …`.
-/
theorem locDer_sub {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → ℂ}
    {W₀ W₁ : X.Opens} {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D W₀ d)
    (h' : LocDer q p m D W₁ d') : LocDer q p m (fun _ => 0) (W₀ ⊓ W₁) (fun W f => d W f - d' W f) where
  add W hW f f' := by rw [h.add W (hW.trans inf_le_left), h'.add W (hW.trans inf_le_right)]; ring
  mul W hW f f' := by rw [h.mul W (hW.trans inf_le_left), h'.mul W (hW.trans inf_le_right)]; ring
  res W W' e hW f := by rw [h.res W W' e (hW.trans inf_le_left), h'.res W W' e (hW.trans inf_le_right), map_sub]
  base W hW r := by rw [h.base W (hW.trans inf_le_left), h'.base W (hW.trans inf_le_right), sub_self, const_zero]

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
  (m : A₀.left ⟶ X)

/- English proof (translation)
The claim follows from `Over.w (u.ex z)`.
-/
theorem ex_hom (z : Fin g → ℂ) : (u.ex z).left ≫ A₀.hom = 𝟙 _ := Over.w (u.ex z)

/- English proof (translation)
Rewrite using `[u.ex_add, (u.ker l).2 l.2, _root_.mul_one]`.
-/
theorem ex_per (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

/- English proof (translation)
The claim follows from `(u.hol (m ⁻¹ᵁ W) 0).1`.
-/
theorem dom_open (W : X.Opens) : IsOpen (dom u m W) := (u.hol (m ⁻¹ᵁ W) 0).1

/- English proof (translation)
The claim follows from `top_le_preimage_inf _ _ _`.
-/
theorem dom_inf {W W' : X.Opens} {z : Fin g → ℂ} : z ∈ dom u m (W ⊓ W') ↔ z ∈ dom u m W ∧ z ∈ dom u m W' :=
  top_le_preimage_inf _ _ _

/- English proof (translation)
Simplify using `only [dom, Set.mem_setOf_eq, ex_per]`.
-/
theorem dom_per (l : u.Λ) (W : X.Opens) (z : Fin g → ℂ) : z + l ∈ dom u m W ↔ z ∈ dom u m W := by
  simp only [dom, Set.mem_setOf_eq, ex_per]

/- English proof (translation)
The claim follows from `(u.hol (m ⁻¹ᵁ W) c).2`.
-/
theorem val_hol (W : X.Opens) (c : Γ(A₀.left, m ⁻¹ᵁ W)) :
    DifferentiableOn ℂ (fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) c) (dom u m W) := (u.hol (m ⁻¹ᵁ W) c).2

/- English proof (translation)
Establish `: fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f)`. Use function extensionality and compare the values at `fun z => (valAt'_comp _ _ _ _).symm`. Rewrite using `[this]`. Conclude with `val_hol u m W _`.
-/
theorem fn_hol (W : X.Opens) (f : Γ(X, W)) : DifferentiableOn ℂ (fn u m W f) (dom u m W) := by
  have : fn u m W f = fun z => valAt' (u.ex z).left (m ⁻¹ᵁ W) ((m.app W).hom f) :=
    funext fun z => (valAt'_comp _ _ _ _).symm
  rw [this]
  exact val_hol u m W _

/- English proof (translation)
The claim follows from `(fn_hol u m W f).differentiableAt ((dom_open u m W).mem_nhds hz)`.
-/
theorem fn_diffAt {W : X.Opens} (f : Γ(X, W)) {z : Fin g → ℂ} (hz : z ∈ dom u m W) :
    DifferentiableAt ℂ (fn u m W f) z :=
  (fn_hol u m W f).differentiableAt ((dom_open u m W).mem_nhds hz)

/- English proof (translation)
Use `Filter.EventuallyEq.fderiv_eq ?_` and prove the remaining obligations. Use `filter_upwards [(dom_open u m W').mem_nhds hz] with y hy`. Conclude with `valAt'_res _ h f hy`.
-/
theorem fderiv_res {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {z : Fin g → ℂ}
    (hz : z ∈ dom u m W') : fderiv ℂ (fn u m W' (resG X h f)) z = fderiv ℂ (fn u m W f) z := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [(dom_open u m W').mem_nhds hz] with y hy
  exact valAt'_res _ h f hy

/- English proof (translation)
Rewrite using `[← fderiv_comp_add_right]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [fn, ex_per]`.
-/
theorem fderiv_per (l : u.Λ) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) :
    fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  simp only [fn, ex_per]

/- English proof (translation)
Establish `: fn u m W (f + f') = fn u m W f + fn u m W f'` using `funext fun y => valAt'_add _ _ _ _`. Rewrite using `[this, fderiv_add (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]`. Both sides reduce to the same expression. Use `mul W hW f f' := by`. Establish `: fn u m W (f * f') = fn u m W f * fn u m W f'` using `funext fun y => valAt'_mul _ _ _ _`.

Rewrite using `[this, fderiv_mul (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]`. Both sides reduce to the same expression. Use `res W W' h hW f := by rw [fderiv_res u m h f hW]`.
-/
theorem ptDer_fderiv (z w : Fin g → ℂ) :
    PtDer ((u.ex z).left ≫ m) (fun W f => fderiv ℂ (fn u m W f) z w) where
  add W hW f f' := by
    have : fn u m W (f + f') = fn u m W f + fn u m W f' := funext fun y => valAt'_add _ _ _ _
    rw [this, fderiv_add (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]; rfl
  mul W hW f f' := by
    have : fn u m W (f * f') = fn u m W f * fn u m W f' := funext fun y => valAt'_mul _ _ _ _
    rw [this, fderiv_mul (fn_diffAt u m f hW) (fn_diffAt u m f' hW)]; rfl
  res W W' h hW f := by rw [fderiv_res u m h f hW]

/- English proof (translation)
Establish `: fn u m ⊤ (constFn p ⊤ r) = fun _ => valAt' (spMap x₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)`. Use function extensionality and compare the values at `y`. Use `(valAt'_appLE _ p ⊤ ⊤ le_top _ le_top).trans ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hm, ← Category.assoc, ex_hom]`. Conclude with `congrArg (fun x => valAt' x ⊤ _) (Category.id_comp _)`.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem fderiv_const_eq {R : Type} [CommRing R] {x₀ : R →+* ℂ} {p : X ⟶ Sp R} (hm : m ≫ p = A₀.hom ≫ spMap x₀)
    (r : R) (z w : Fin g → ℂ) : fderiv ℂ (fn u m ⊤ (constFn p ⊤ r)) z w = 0 := by
  have : fn u m ⊤ (constFn p ⊤ r) =
      fun _ => valAt' (spMap x₀) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    funext y
    refine (valAt'_appLE _ p ⊤ ⊤ le_top _ le_top).trans ?_
    rw [Category.assoc, hm, ← Category.assoc, ex_hom]
    exact congrArg (fun x => valAt' x ⊤ _) (Category.id_comp _)
  rw [this]
  simp

def ev (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (z : Fin g → ℂ) (W : X.Opens)
    (f : Γ(X, W)) : ℂ :=
  valAt' (u.ex z).left (m ⁻¹ᵁ (W ⊓ W₀)) (d (W ⊓ W₀) (resG X inf_le_left f))

variable {R : Type} [CommRing R] {p : X ⟶ Sp R} {D : R → ℂ} {W₀ : X.Opens}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)}

/- English proof (translation)
Rewrite using `[ev, ← res_res (inf_le_left : W ⊓ W₀ ≤ W) (le_inf h h₀), hd.res _ _ _ inf_le_right]`. Conclude with `(valAt'_res (u.ex z).left (V := m ⁻¹ᵁ W') _ _ hz).symm`.
-/
theorem ev_eq (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} {W W' : X.Opens} (h : W' ≤ W) (h₀ : W' ≤ W₀)
    (hz : z ∈ dom u m W') (f : Γ(X, W)) :
    ev u m W₀ d z W f = valAt' (u.ex z).left (m ⁻¹ᵁ W') (d W' (resG X h f)) := by
  rw [ev, ← res_res (inf_le_left : W ⊓ W₀ ≤ W) (le_inf h h₀), hd.res _ _ _ inf_le_right]
  exact (valAt'_res (u.ex z).left (V := m ⁻¹ᵁ W') _ _ hz).symm

/- English proof (translation)
Simplify using `only [ev, map_add, hd.add _ inf_le_right, valAt'_add]`. Use `mul W hW f f' := by`. Establish `h : z ∈ dom u m (W ⊓ W₀)` using `(dom_inf u m).2 ⟨hW, hz⟩`. Simplify using `only [ev, map_mul, hd.mul _ inf_le_right, valAt'_add, valAt'_mul, valAt'_comp]`. Rewrite using `[valAt'_res _ _ f h, valAt'_res _ _ f' h]`.

Use `res W W' e hW f := by`. Establish `h : z ∈ dom u m (W' ⊓ W₀)` using `(dom_inf u m).2 ⟨hW, hz⟩`. Rewrite using `[ev_eq u m hd (inf_le_left.trans e) inf_le_right h f, ev, res_res]`.
-/
theorem ptDer_ev (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} (hz : z ∈ dom u m W₀) :
    PtDer ((u.ex z).left ≫ m) (ev u m W₀ d z) where
  add W hW f f' := by
    simp only [ev, map_add, hd.add _ inf_le_right, valAt'_add]
  mul W hW f f' := by
    have h : z ∈ dom u m (W ⊓ W₀) := (dom_inf u m).2 ⟨hW, hz⟩
    simp only [ev, map_mul, hd.mul _ inf_le_right, valAt'_add, valAt'_mul, valAt'_comp]
    rw [valAt'_res _ _ f h, valAt'_res _ _ f' h]
  res W W' e hW f := by
    have h : z ∈ dom u m (W' ⊓ W₀) := (dom_inf u m).2 ⟨hW, hz⟩
    rw [ev_eq u m hd (inf_le_left.trans e) inf_le_right h f, ev, res_res]

/- English proof (translation)
Rewrite using `[ev_eq u m hd le_top le_rfl hz, res_const, hd.base _ le_rfl]`. Conclude with `valAt'_constFn _ _ (ex_hom u z) _ _ hz`.
-/
theorem ev_base (hd : LocDer A₀.hom p m D W₀ d) {z : Fin g → ℂ} (hz : z ∈ dom u m W₀) (r : R) :
    ev u m W₀ d z ⊤ (constFn p ⊤ r) = D r := by
  rw [ev_eq u m hd le_top le_rfl hz, res_const, hd.base _ le_rfl]
  exact valAt'_constFn _ _ (ex_hom u z) _ _ hz

/- English proof (translation)
The claim follows from `val_hol u m _ _`.
-/
theorem ev_hol (W : X.Opens) (f : Γ(X, W)) :
    DifferentiableOn ℂ (fun z => ev u m W₀ d z W f) (dom u m (W ⊓ W₀)) := val_hol u m _ _

/- English proof (translation)
Use function extensionality and compare the values at `W f`. Simplify using `only [ev, ex_per]`.
-/
theorem ev_per (l : u.Λ) (z : Fin g → ℂ) : ev u m W₀ d (z + l) = ev u m W₀ d z := by
  funext W f
  simp only [ev, ex_per]

/- English proof (translation)
Establish `e : (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) = fun z => ∑ a, h a z * fderiv ℂ (fn u m W f) z (Pi.single a 1)`. Use function extensionality and compare the values at `z`. Use `conv_lhs => rw [show (fun a => h a z) = ∑ a, h a z • (Pi.single a 1 : Fin g → ℂ) from (pi_eq_sum_univ' _)]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Rewrite using `[e]`.

Use `DifferentiableOn.fun_sum fun a _ => (hh a).mul ?_` and prove the remaining obligations. Conclude with `(((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ _ (dom_open u m W)).2 (fn_hol u m W f)).2 _).mono hS`.
-/
theorem fderiv_field_hol (W : X.Opens) (f : Γ(X, W)) {S : Set (Fin g → ℂ)} (hS : S ⊆ dom u m W)
    (h : Fin g → (Fin g → ℂ) → ℂ) (hh : ∀ a, DifferentiableOn ℂ (h a) S) :
    DifferentiableOn ℂ (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) S := by
  have e : (fun z => fderiv ℂ (fn u m W f) z (fun a => h a z)) =
      fun z => ∑ a, h a z * fderiv ℂ (fn u m W f) z (Pi.single a 1) := by
    funext z
    conv_lhs => rw [show (fun a => h a z) = ∑ a, h a z • (Pi.single a 1 : Fin g → ℂ) from
      (pi_eq_sum_univ' _)]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [e]
  refine DifferentiableOn.fun_sum fun a _ => (hh a).mul ?_
  exact (((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ _ (dom_open u m W)).2 (fn_hol u m W f)).2 _).mono hS

/- English proof (translation)
Take `⟨W, hW, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (x := ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ)) (U := ⊤) trivial`. Conclude with `⟨⟨W, hW⟩, (top_le_preimage_iff_mem _ _).2 hx⟩`.
-/
theorem exists_affine_dom (z : Fin g → ℂ) : ∃ i : X.affineOpens, z ∈ dom u m i.1 := by
  obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  exact ⟨⟨W, hW⟩, (top_le_preimage_iff_mem _ _).2 hx⟩

/- English proof (translation)
Introduce `P₀ u Hm χ hu R _ x₀ X p m hp hm D hD`. Use `choose d hd using fun i : X.affineOpens => GlobalTheory.T.exists_localDerivationAlongFibre_of_smooth R x₀ _ X P₀.A.hom p m D i.1 hp hm.w hD i.2`. Use `choose c hc using fun i j : X.affineOpens => GlobalTheory.KS.locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hd i) (hd j))`. Set `C : X.affineOpens → X.affineOpens → (Fin P₀.g → ℂ) → Fin P₀.g → ℂ` to `fun i j z a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (c i j a)`. Establish `hC : ∀ i j z W f, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m W → ev u m i.1 (d i) z W f - ev u m j.1 (d j) z W f = fderiv ℂ (fn u m W f) z (C i j z)`.

Introduce `i j z W f hi hj hW`. Establish `h : z ∈ dom u m (W ⊓ (i.1 ⊓ j.1))` using `(dom_inf u m).2 ⟨hW, (dom_inf u m).2 ⟨hi, hj⟩⟩`. Rewrite using `[ev_eq u m (hd i) inf_le_left (inf_le_right.trans inf_le_left) h, ev_eq u m (hd j) inf_le_left (inf_le_right.trans inf_le_right) h, ← valAt'_sub, hc i j _ inf_le_right _ z h, fderiv_res u m _ _ h]`. Establish `hco : ∀ i j k z, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m k.1 → C i j z + C j k z = C i k z`. Introduce `i j k z hi hj hk`.

Use `(GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hu R x₀ X p m hp hm z _ (ptDer_fderiv u m z (C i k z)) (fun r => fderiv_const_eq u m hm.w r z _)).unique (fun W f hW => ?_) (fun _ _ _ => rfl)` and prove the remaining obligations. Rewrite using `[map_add, ← hC i j z W f hi hj hW, ← hC j k z W f hj hk hW, ← hC i k z W f hi hk hW]`. Expand and normalize the polynomial expressions, which then agree. Use `choose t h hh hch using fun a : Fin P₀.g => GlobalTheory.holomorphic_periodic_cocycle_coboundary P₀.g u.Λ u.discrete u.full X.affineOpens (fun i => dom u m i.1) (fun i j z => C i j z a) (fun i => dom_open u m _) (fun i l z hz => (dom_per u m l _ z).2 hz) (exists_affine_dom u m) ( …`. Use `choose κ hκ using exists_affine_dom u m`.

Set `s : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ` to `fun z W f => ev u m (κ z).1 (d (κ z)) z W f + fderiv ℂ (fn u m W f) z (fun a => h a (κ z) z)`. Establish `hs : ∀ j z W f, z ∈ dom u m j.1 → z ∈ dom u m W → s z W f = ev u m j.1 (d j) z W f + fderiv ℂ (fn u m W f) z (fun a => h a j z)`. Introduce `j z W f hj hW`. Establish `e₁` using `hC (κ z) j z W f (hκ z) hj hW`. Establish `e₂ : C (κ z) j z = (fun a => h a j z) - fun a => h a (κ z) z`.

Use function extensionality and compare the values at `fun a => hch a (κ z) j z ⟨hκ z, hj⟩`. Rewrite `e₁` using `[e₂, map_sub]`. Simplify using `only [s]`. Take the linear combination `e₁`. Use `⟨Matrix.of t, s, fun z => ptDer_add (ptDer_ev u m (hd _) (hκ z)) (ptDer_fderiv u m z _), fun z r => ?_, fun W f z hz => ?_, fun l W f z hz => ?_⟩` and prove the remaining obligations.

Simplify using `only [s]`. Rewrite using `[ev_base u m (hd _) (hκ z), fderiv_const_eq u m hm.w, add_zero]`. Establish `hz' : z ∈ dom u m (W ⊓ (κ z).1)` using `(dom_inf u m).2 ⟨hz, hκ z⟩`. Establish `hn` using `(dom_open u m _).mem_nhds hz'`. Establish `h₁` using `(ev_hol u m (W₀ := (κ z).1) (d := d (κ z)) W f).add (fderiv_field_hol u m W f (S := dom u m (W ⊓ (κ z).1)) (fun y hy => ((dom_inf u m).1 hy).1) (fun a => h a (κ z)) fun a => (hh a (κ z)).1.mono fun y hy => ((dom_inf u m).1 hy).2)`.

Use `((h₁.congr fun y hy => ?_).differentiableAt hn).differentiableWithinAt` and prove the remaining obligations. Conclude with `hs (κ z) y W f ((dom_inf u m).1 hy).2 ((dom_inf u m).1 hy).1`. Rewrite using `[hs (κ z) (z + l) W f ((dom_per u m l _ z).2 (hκ z)) ((dom_per u m l _ z).2 hz), ev_per, fderiv_per]`. Establish `e : (fun a => h a (κ z) (z + l)) = (fun a => h a (κ z) z) + (Matrix.of t).mulVec (star (l : Fin P₀.g → ℂ))`. Use function extensionality and compare the values at `fun a => (hh a (κ z)).2 l z (hκ z)`.

Rewrite using `[e, map_add]`. Simplify using `only [s]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_ksRel : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D, IsDer x₀ D → ∃ Θ s, KSRel u p m D Θ s := by
  intro P₀ u Hm χ hu R _ x₀ X p m hp hm D hD
  choose d hd using fun i : X.affineOpens => GlobalTheory.T.exists_localDerivationAlongFibre_of_smooth R x₀ _ X P₀.A.hom p m D i.1 hp hm.w hD i.2
  choose c hc using fun i j : X.affineOpens =>
    GlobalTheory.KS.locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hd i) (hd j))
  let C : X.affineOpens → X.affineOpens → (Fin P₀.g → ℂ) → Fin P₀.g → ℂ :=
    fun i j z a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (c i j a)
  have hC : ∀ i j z W f, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m W →
      ev u m i.1 (d i) z W f - ev u m j.1 (d j) z W f = fderiv ℂ (fn u m W f) z (C i j z) := by
    intro i j z W f hi hj hW
    have h : z ∈ dom u m (W ⊓ (i.1 ⊓ j.1)) := (dom_inf u m).2 ⟨hW, (dom_inf u m).2 ⟨hi, hj⟩⟩
    rw [ev_eq u m (hd i) inf_le_left (inf_le_right.trans inf_le_left) h,
      ev_eq u m (hd j) inf_le_left (inf_le_right.trans inf_le_right) h, ← valAt'_sub,
      hc i j _ inf_le_right _ z h, fderiv_res u m _ _ h]
  have hco : ∀ i j k z, z ∈ dom u m i.1 → z ∈ dom u m j.1 → z ∈ dom u m k.1 → C i j z + C j k z = C i k z := by
    intro i j k z hi hj hk
    refine (GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hu R x₀ X p m hp hm z _ (ptDer_fderiv u m z (C i k z))
      (fun r => fderiv_const_eq u m hm.w r z _)).unique (fun W f hW => ?_) (fun _ _ _ => rfl)
    rw [map_add, ← hC i j z W f hi hj hW, ← hC j k z W f hj hk hW, ← hC i k z W f hi hk hW]
    ring
  choose t h hh hch using fun a : Fin P₀.g =>
    GlobalTheory.holomorphic_periodic_cocycle_coboundary P₀.g u.Λ u.discrete u.full X.affineOpens (fun i => dom u m i.1)
      (fun i j z => C i j z a) (fun i => dom_open u m _) (fun i l z hz => (dom_per u m l _ z).2 hz)
      (exists_affine_dom u m)
      (fun i j => (val_hol u m _ (c i j a)).mono fun z hz => (dom_inf u m).2 hz)
      (fun i j l z _ => by simp only [C, ex_per])
      (fun i j k z hz => congrFun (hco i j k z hz.1.1 hz.1.2 hz.2) a)
  choose κ hκ using exists_affine_dom u m
  let s : (Fin P₀.g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ := fun z W f =>
    ev u m (κ z).1 (d (κ z)) z W f + fderiv ℂ (fn u m W f) z (fun a => h a (κ z) z)
  have hs : ∀ j z W f, z ∈ dom u m j.1 → z ∈ dom u m W →
      s z W f = ev u m j.1 (d j) z W f + fderiv ℂ (fn u m W f) z (fun a => h a j z) := by
    intro j z W f hj hW
    have e₁ := hC (κ z) j z W f (hκ z) hj hW
    have e₂ : C (κ z) j z = (fun a => h a j z) - fun a => h a (κ z) z :=
      funext fun a => hch a (κ z) j z ⟨hκ z, hj⟩
    rw [e₂, map_sub] at e₁
    simp only [s]
    linear_combination e₁
  refine ⟨Matrix.of t, s, fun z => ptDer_add (ptDer_ev u m (hd _) (hκ z)) (ptDer_fderiv u m z _), fun z r => ?_,
    fun W f z hz => ?_, fun l W f z hz => ?_⟩
  · simp only [s]
    rw [ev_base u m (hd _) (hκ z), fderiv_const_eq u m hm.w, add_zero]
  · have hz' : z ∈ dom u m (W ⊓ (κ z).1) := (dom_inf u m).2 ⟨hz, hκ z⟩
    have hn := (dom_open u m _).mem_nhds hz'
    have h₁ := (ev_hol u m (W₀ := (κ z).1) (d := d (κ z)) W f).add
      (fderiv_field_hol u m W f (S := dom u m (W ⊓ (κ z).1)) (fun y hy => ((dom_inf u m).1 hy).1)
        (fun a => h a (κ z)) fun a => (hh a (κ z)).1.mono fun y hy => ((dom_inf u m).1 hy).2)
    refine ((h₁.congr fun y hy => ?_).differentiableAt hn).differentiableWithinAt
    exact hs (κ z) y W f ((dom_inf u m).1 hy).2 ((dom_inf u m).1 hy).1
  · rw [hs (κ z) (z + l) W f ((dom_per u m l _ z).2 (hκ z)) ((dom_per u m l _ z).2 hz), ev_per, fderiv_per]
    have e : (fun a => h a (κ z) (z + l)) = (fun a => h a (κ z) z) + (Matrix.of t).mulVec (star (l : Fin P₀.g → ℂ)) :=
      funext fun a => (hh a (κ z)).2 l z (hκ z)
    rw [e, map_add]
    simp only [s]
    ring

end GlobalTheory.KS.Exist
end
