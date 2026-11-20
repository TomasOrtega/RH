import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLocalDerivationAlongFibreFieldOfAffi
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Heat.DerComm
open GlobalTheory.KS GlobalTheory.LocDerExt

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem appLE_congr {X Y : Scheme.{0}} {g g' : Y ⟶ X} (e : g = g') (U : X.Opens) (V : Y.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (h' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V h = g'.appLE U V h' := by
  subst e; rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun W hW' => h.add W (hW'.trans hW), fun W hW' => h.mul W (hW'.trans hW), fun W W' h' hW' => h.res W W' h' (hW'.trans hW), fun W hW' => h.base W (hW'.trans hW)⟩`.
-/
theorem locDerK_mono {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₀ W₁ : X.Opens}
    {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D W₀ d) (hW : W₁ ≤ W₀) :
    LocDerK q p m D W₁ d :=
  ⟨fun W hW' => h.add W (hW'.trans hW), fun W hW' => h.mul W (hW'.trans hW),
   fun W W' h' hW' => h.res W W' h' (hW'.trans hW), fun W hW' => h.base W (hW'.trans hW)⟩

/- English proof (translation)
Use function extensionality and compare the values at `f`. Take `⟨P, rfl⟩` from `hs f`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[MvPolynomial.eval₂Hom_C]`.

Establish `e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) = a`. Simplify using the standard rewrite rules. Establish `: (p.appLE ⊤ V (fun _ _ => trivial)).hom a = constFn p V ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)`. Unfold `constFn`. Rewrite using `[e]`.

Rewrite using `[this, h.base V le_rfl, h'.base V le_rfl]`. Consider the case `add P Q hP hQ => rw [map_add, h.add V le_rfl, h'.add V le_rfl, hP, hQ]`. Consider the case `mul_X P n hP => rw [map_mul, MvPolynomial.eval₂Hom_X', h.mul V le_rfl, h'.mul V le_rfl, hP, he]`.
-/
theorem eq_of_gen {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {V : X.Opens}
    {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D V d)
    (h' : LocDerK q p m D V d') {M : Type} (r : M → Γ(X, V))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ V (fun _ _ => trivial)).hom r))
    (he : ∀ j, d V (r j) = d' V (r j)) : d V = d' V := by
  funext f
  obtain ⟨P, rfl⟩ := hs f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) = a := by
      simp
    have : (p.appLE ⊤ V (fun _ _ => trivial)).hom a =
        constFn p V ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
      unfold constFn; rw [e]
    rw [this, h.base V le_rfl, h'.base V le_rfl]
  | add P Q hP hQ => rw [map_add, h.add V le_rfl, h'.add V le_rfl, hP, hQ]
  | mul_X P n hP => rw [map_mul, MvPolynomial.eval₂Hom_X', h.mul V le_rfl, h'.mul V le_rfl, hP, he]

/- English proof (translation)
Introduce `R K _ _ X Y q p m D dl hdl T T₀ hm hq hp Ix U M r hU hA hs hg`. Establish `pe : ∀ V : X.Opens, (m ≫ T) ⁻¹ᵁ V ≤ T₀ ⁻¹ᵁ (m ⁻¹ᵁ V)` using `fun V => by`. Rewrite using `[← hm]`. Conclude with `le_rfl`. Establish `app1 : ∀ (V : X.Opens) (g : Γ(X, V)), (m.app (T ⁻¹ᵁ V)).hom ((T.app V).hom g) = ((m ≫ T).app V).hom g`.

Introduce `V g`. Rewrite using `[Scheme.Hom.comp_app]`. Both sides reduce to the same expression. Establish `app2 : ∀ (V : X.Opens) (g : Γ(X, V)), pbT T₀ ((m.app V).hom g) ((m ≫ T) ⁻¹ᵁ V) = ((m ≫ T).app V).hom g`. Introduce `V g`.

Rewrite using `[pbT_of_le T₀ (pe V), Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]`. Use `congrArg (fun φ => φ.hom g) (Scheme.Hom.appLE_comp_appLE T₀ m V (m ⁻¹ᵁ V) ((m ≫ T) ⁻¹ᵁ V) le_rfl (pe V))` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun φ : Γ(X, V) ⟶ Γ(Y, (m ≫ T) ⁻¹ᵁ V) => φ.hom g) (appLE_congr hm V _ _ _)`. Set `d1 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V)` to `fun V g => dl (T ⁻¹ᵁ V) ((T.app V).hom g)`.

Set `d2 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V)` to `fun V g => pbT T₀ (dl V g) ((m ≫ T) ⁻¹ᵁ V)`. Establish `h1 : LocDerK q p (m ≫ T) D ⊤ d1`. Use `⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩` and prove the remaining obligations. Simplify using `only [d1, map_add]`. Conclude with `hdl.add _ le_top _ _`.

Simplify using `only [d1, map_mul]`. Rewrite using `[hdl.mul _ le_top, app1, app1]`. Conclude with `rfl`. Simplify using `only [d1]`. Rewrite using `[app_res T h, hdl.res _ _ _ le_top]`.

Both sides reduce to the same expression. Simplify using `only [d1]`. Rewrite using `[Scheme.Hom.app_eq_appLE, ← pbT_of_le T le_rfl, pbT_constFn p T le_rfl, hp]`. Conclude with `hdl.base _ le_top a`. Establish `h2 : LocDerK q p (m ≫ T) D ⊤ d2`.

Use `⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩` and prove the remaining obligations. Simplify using `only [d2]`. Rewrite using `[hdl.add _ le_top, pbT_add]`. Simplify using `only [d2]`. Rewrite using `[hdl.mul _ le_top, pbT_add, pbT_mul, pbT_mul, app2, app2]`.

Simplify using `only [d2]`. Rewrite using `[hdl.res _ _ h le_top, pbT_rsT T₀ (pre_le m h) (pe V'), rsT_pbT T₀ (pe V) (pre_le (m ≫ T) h)]`. Simplify using `only [d2]`. Rewrite using `[hdl.base _ le_top, pbT_constFn q T₀ (pe V), hq]`. Establish `key : ∀ i, ∀ V, V ≤ U i → d1 V = d2 V` using `fun i V hV => GlobalTheory.LocDerExtK.locDerK_unique (hA i) d1 d2 (locDerK_mono h1 le_top) (locDerK_mono h2 le_top) (eq_of_gen (locDerK_mono h1 le_top) (locDerK_mono h2 le_top) (r i) (hs i) (fun j => hg i j)) V hV`.

Introduce `W f`. Use `show d1 W f = d2 W f`. Use `eq_of_rsT_eq (fun k => (m ≫ T) ⁻¹ᵁ (W ⊓ U k)) (fun k => pre_le _ inf_le_left) ?_ _ _ ?_` and prove the remaining obligations. Introduce `y hy`. Establish `: (m ≫ T).base y ∈ ⨆ i, U i` using `by rw [hU]; trivial`.

Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩`. Introduce `k`. Rewrite using `[← h1.res W _ inf_le_left le_top, ← h2.res W _ inf_le_left le_top, key k _ inf_le_right]`.
-/
theorem comm_of_gen : ∀ {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (dl : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK q p m D ⊤ dl → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y), T₀ ≫ m = m ≫ T → T₀ ≫ q = q → T ≫ p = p → ∀ (Ix : Type) (U : Ix → X.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(X, U i)), (⨆ i, U i = ⊤) → (∀ i, IsAffineOpen (U i)) → (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) → (∀ i j, dl (T ⁻¹ᵁ U i) ((T.app (U i)).hom (r i j)) = pbT T₀ (dl (U i) (r i j)) (m ⁻¹ᵁ (T ⁻¹ᵁ U i))) → ∀ (W : X.Opens) (f : Γ(X, W)), dl (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (dl W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W)) := by
  intro R K _ _ X Y q p m D dl hdl T T₀ hm hq hp Ix U M r hU hA hs hg
  have pe : ∀ V : X.Opens, (m ≫ T) ⁻¹ᵁ V ≤ T₀ ⁻¹ᵁ (m ⁻¹ᵁ V) := fun V => by
    rw [← hm]; exact le_rfl
  have app1 : ∀ (V : X.Opens) (g : Γ(X, V)),
      (m.app (T ⁻¹ᵁ V)).hom ((T.app V).hom g) = ((m ≫ T).app V).hom g := by
    intro V g; rw [Scheme.Hom.comp_app]; rfl
  have app2 : ∀ (V : X.Opens) (g : Γ(X, V)),
      pbT T₀ ((m.app V).hom g) ((m ≫ T) ⁻¹ᵁ V) = ((m ≫ T).app V).hom g := by
    intro V g
    rw [pbT_of_le T₀ (pe V), Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
    have := congrArg (fun φ => φ.hom g) (Scheme.Hom.appLE_comp_appLE T₀ m V (m ⁻¹ᵁ V) ((m ≫ T) ⁻¹ᵁ V) le_rfl (pe V))
    refine this.trans ?_
    exact congrArg (fun φ : Γ(X, V) ⟶ Γ(Y, (m ≫ T) ⁻¹ᵁ V) => φ.hom g) (appLE_congr hm V _ _ _)
  let d1 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => dl (T ⁻¹ᵁ V) ((T.app V).hom g)
  let d2 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => pbT T₀ (dl V g) ((m ≫ T) ⁻¹ᵁ V)
  have h1 : LocDerK q p (m ≫ T) D ⊤ d1 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d1, map_add]; exact hdl.add _ le_top _ _
    · simp only [d1, map_mul]; rw [hdl.mul _ le_top, app1, app1]; exact rfl
    · simp only [d1]; rw [app_res T h, hdl.res _ _ _ le_top]; rfl
    · simp only [d1]
      rw [Scheme.Hom.app_eq_appLE, ← pbT_of_le T le_rfl, pbT_constFn p T le_rfl, hp]
      exact hdl.base _ le_top a
  have h2 : LocDerK q p (m ≫ T) D ⊤ d2 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d2]; rw [hdl.add _ le_top, pbT_add]
    · simp only [d2]; rw [hdl.mul _ le_top, pbT_add, pbT_mul, pbT_mul, app2, app2]
    · simp only [d2]
      rw [hdl.res _ _ h le_top, pbT_rsT T₀ (pre_le m h) (pe V'), rsT_pbT T₀ (pe V) (pre_le (m ≫ T) h)]
    · simp only [d2]; rw [hdl.base _ le_top, pbT_constFn q T₀ (pe V), hq]
  have key : ∀ i, ∀ V, V ≤ U i → d1 V = d2 V := fun i V hV =>
    GlobalTheory.LocDerExtK.locDerK_unique (hA i) d1 d2 (locDerK_mono h1 le_top) (locDerK_mono h2 le_top)
      (eq_of_gen (locDerK_mono h1 le_top) (locDerK_mono h2 le_top) (r i) (hs i) (fun j => hg i j)) V hV
  intro W f
  show d1 W f = d2 W f
  refine eq_of_rsT_eq (fun k => (m ≫ T) ⁻¹ᵁ (W ⊓ U k)) (fun k => pre_le _ inf_le_left) ?_ _ _ ?_
  · intro y hy
    have : (m ≫ T).base y ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩
  · intro k
    rw [← h1.res W _ inf_le_left le_top, ← h2.res W _ inf_le_left le_top, key k _ inf_le_right]

end GlobalTheory.Heat.DerComm
