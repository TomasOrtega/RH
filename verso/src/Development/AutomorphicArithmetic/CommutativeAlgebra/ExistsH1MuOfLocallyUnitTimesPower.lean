import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsH1MuGlueOfCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.PicGlue

variable {X : Scheme.{0}}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem top_le (V : X.Opens) : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp

/- English proof (translation)
Introduce `_ _` and use `trivial`.
-/
private theorem top_pre {A B : Scheme.{0}} (f : A ⟶ B) : (⊤ : A.Opens) ≤ f ⁻¹ᵁ (⊤ : B.Opens) :=
  fun _ _ => trivial

/- English proof (translation)
The claim follows from `Scheme.Hom.app_eq_appLE f`.
-/
private theorem appTop_eq {A B : Scheme.{0}} (f : A ⟶ B) : f.appTop = f.appLE ⊤ ⊤ (top_pre f) :=
  Scheme.Hom.app_eq_appLE f

private noncomputable def rho (V : X.Opens) : Γ(X, V) →+* Γ(V.toScheme, ⊤) :=
  (V.ι.appLE V ⊤ (top_le V)).hom

/- English proof (translation)
Substitute `hg` using the available equality. Both sides reduce to the same expression.
-/
private theorem appLE_congr' {A B : Scheme.{0}} {g g' : A ⟶ B} (hg : g = g') (V : B.Opens) (W : A.Opens)
    (h : W ≤ g ⁻¹ᵁ V) (h' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W h = g'.appLE V W h' := by
  subst hg; rfl

/- English proof (translation)
Establish `h1 : U.ι.appLE U ⊤ (top_le U) ≫ (X.homOfLE e).appTop = X.presheaf.map (homOfLE e).op ≫ V.ι.appLE V ⊤ (top_le V)`. Rewrite using `[Scheme.Hom.map_appLE, appTop_eq, Scheme.Hom.appLE_comp_appLE]`. Conclude with `appLE_congr' (X.homOfLE_ι e) _ _ _ _`. Conclude with `congr($(h1).hom s)`.
-/
private theorem rho_res {U V : X.Opens} (e : V ≤ U) (s : Γ(X, U)) :
    (X.homOfLE e).appTop.hom (rho U s) = rho V ((X.presheaf.map (homOfLE e).op).hom s) := by
  have h1 : U.ι.appLE U ⊤ (top_le U) ≫ (X.homOfLE e).appTop =
      X.presheaf.map (homOfLE e).op ≫ V.ι.appLE V ⊤ (top_le V) := by
    rw [Scheme.Hom.map_appLE, appTop_eq, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr' (X.homOfLE_ι e) _ _ _ _
  exact congr($(h1).hom s)

/- English proof (translation)
Establish `hp : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U`. Introduce `z _`. Establish `hz : X.fromSpecStalk x z ⤳ x`. Establish `: X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x)` using `⟨z, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis.

Conclude with `hz.mem_open U.2 hx`. Establish `h1 : U.ι.appLE U ⊤ (top_le U) ≫ (U.fromSpecStalkOfMem x hx).appTop = X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv`. Rewrite using `[appTop_eq, Scheme.Hom.appLE_comp_appLE, appLE_congr' (Scheme.Opens.fromSpecStalkOfMem_ι U x hx) U ⊤ _ hp, Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]`. Simplify using `only [Category.assoc, ← Functor.map_comp]`. Establish `e : ((homOfLE le_top).op ≫ (homOfLE hp).op : Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _` using `rfl`.

Rewrite using `[e, CategoryTheory.Functor.map_id, Category.comp_id]`. Conclude with `congr($(h1).hom s)`.
-/
private theorem rho_generic (U : X.Opens) (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    (U.fromSpecStalkOfMem x hx).appTop.hom (rho U s) =
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s) := by
  have hp : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
    intro z _
    have hz : X.fromSpecStalk x z ⤳ x := by
      have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact hz.mem_open U.2 hx
  have h1 : U.ι.appLE U ⊤ (top_le U) ≫ (U.fromSpecStalkOfMem x hx).appTop =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
    rw [appTop_eq, Scheme.Hom.appLE_comp_appLE,
      appLE_congr' (Scheme.Opens.fromSpecStalkOfMem_ι U x hx) U ⊤ _ hp,
      Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    have e : ((homOfLE le_top).op ≫ (homOfLE hp).op :
        Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
    rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
  exact congr($(h1).hom s)

/- English proof (translation)
Establish `hloc : ∀ x : V, ∃ (W : X.Opens) (hxW : x.1 ∈ W), W ≤ V ∧ ∃ s : Γ(X, W), X.germToFunctionField W (h` using `⟨⟨x.1, hxW⟩⟩) s = f := by`. Introduce `x`. Take `⟨w, hw⟩` from `h x.1 x.2`. Take `⟨W, hxW, g, hg⟩` from `X.presheaf.exists_germ_eq w`. Use `⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op g, ?_⟩` and prove the remaining obligations.

Establish `: Nonempty W` using `⟨⟨x.1, hxW⟩⟩`. Rewrite using `[← hw, ← hg, Scheme.algebraMap_germ_eq_germToFunctionField]`. Simplify using the standard rewrite rules. Use `choose W hxW hWV s hs using hloc`. Establish `hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W s`.

Introduce `i j`. Take `⟨y, hy⟩ : ((W i : Set X) ∩ W j).Nonempty` from `nonempty_preirreducible_inter (W i).isOpen (W j).isOpen ⟨_, hxW i⟩ ⟨_, hxW j⟩`. Establish `: Nonempty (W i ⊓ W j : X.Opens)` using `⟨⟨y, hy⟩⟩`. Establish `: Nonempty (W i)` using `⟨⟨_, hxW i⟩⟩`. Establish `: Nonempty (W j)` using `⟨⟨_, hxW j⟩⟩`.

Apply `Scheme.germToFunctionField_injective X (W i ⊓ W j)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_left).op (s i)) = X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_right).op (s j))`. Simplify using `[hs]`. Take `⟨t, ht, -⟩` from `X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hWV i)) (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) s hcompat`. Use `⟨t, ?_⟩` and prove the remaining obligations.

Take `⟨i⟩` from `‹Nonempty V›`. Establish `: Nonempty (W i)` using `⟨⟨_, hxW i⟩⟩`. Rewrite using `[← hs i, ← ht i]`. Express the relevant statement in the definitionally equal form `_ = X.germToFunctionField (W i) (X.presheaf.map (homOfLE (hWV i)).op t)`. Conclude with `(TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm`.
-/
private theorem sec [IsIntegral X] (V : X.Opens) [Nonempty V] (f : X.functionField)
    (h : ∀ x ∈ V, ∃ w : X.presheaf.stalk x, algebraMap _ X.functionField w = f) :
    ∃ s : Γ(X, V), X.germToFunctionField V s = f := by
  have hloc : ∀ x : V, ∃ (W : X.Opens) (hxW : x.1 ∈ W), W ≤ V ∧
      ∃ s : Γ(X, W), X.germToFunctionField W (h := ⟨⟨x.1, hxW⟩⟩) s = f := by
    intro x
    obtain ⟨w, hw⟩ := h x.1 x.2
    obtain ⟨W, hxW, g, hg⟩ := X.presheaf.exists_germ_eq w
    refine ⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op g, ?_⟩
    have : Nonempty W := ⟨⟨x.1, hxW⟩⟩
    rw [← hw, ← hg, Scheme.algebraMap_germ_eq_germToFunctionField]
    simp
  choose W hxW hWV s hs using hloc
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W s := by
    intro i j
    obtain ⟨y, hy⟩ : ((W i : Set X) ∩ W j).Nonempty :=
      nonempty_preirreducible_inter (W i).isOpen (W j).isOpen ⟨_, hxW i⟩ ⟨_, hxW j⟩
    have : Nonempty (W i ⊓ W j : X.Opens) := ⟨⟨y, hy⟩⟩
    have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
    have : Nonempty (W j) := ⟨⟨_, hxW j⟩⟩
    apply Scheme.germToFunctionField_injective X (W i ⊓ W j)
    change X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_left).op (s i)) =
      X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_right).op (s j))
    simp [hs]
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hWV i))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) s hcompat
  refine ⟨t, ?_⟩
  obtain ⟨i⟩ := ‹Nonempty V›
  have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
  rw [← hs i, ← ht i]
  change _ = X.germToFunctionField (W i) (X.presheaf.map (homOfLE (hWV i)).op t)
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

/- English proof (translation)
Establish `key : ∀ (f : X.functionField) (d : Γ(X, W)), X.germToFunctionField W d = f ^ q → ∃ s : Γ(X, W), X.germToFunctionField W s = f`. Introduce `f d hd`. Use `sec W f fun x hx => ?_` and prove the remaining obligations. Use `hn x` as an intermediate fact. Establish `h1 : IsIntegral (X.presheaf.stalk x) (f ^ q)`.

Rewrite using `[← hd, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx]`. Conclude with `isIntegral_algebraMap`. Conclude with `(IsIntegrallyClosed.isIntegral_iff (K := X.functionField)).1 (h1.of_pow (Nat.pos_of_ne_zero hq))`. Take `⟨s, hs⟩` from `key g c hc`. Take `⟨s', hs'⟩` from `key (g⁻¹ : (X.functionField)ˣ) ((c⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) (by`.

Establish `h2 : X.germToFunctionField W ((c⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * X.germToFunctionField W (c : Γ(X, W)) = 1`. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[hc]`. Rewrite using `[eq_comm, ← mul_right_inj' (pow_ne_zero q g.ne_zero)]`.

Rewrite using `[← mul_pow]`. Simplify `h2.symm)` using `[mul_comm]`. Establish `h3 : s * s' = 1` using `Scheme.germToFunctionField_injective X W (by`. Rewrite using `[map_mul, hs, hs', map_one]`. Use the proof step `simp)`.

Establish `h4 : s' * s = 1` using `by rw [mul_comm]; exact h3`. Conclude with `⟨⟨s, s', h3, h4⟩, hs⟩`.
-/
private theorem sec_unit [IsIntegral X] (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (q : ℕ) (hq : q ≠ 0)
    (W : X.Opens) [Nonempty W] (g : (X.functionField)ˣ) (c : (Γ(X, W))ˣ)
    (hc : X.germToFunctionField W (c : Γ(X, W)) = (g : X.functionField) ^ q) :
    ∃ w : (Γ(X, W))ˣ, X.germToFunctionField W (w : Γ(X, W)) = g := by
  have key : ∀ (f : X.functionField) (d : Γ(X, W)), X.germToFunctionField W d = f ^ q →
      ∃ s : Γ(X, W), X.germToFunctionField W s = f := by
    intro f d hd
    refine sec W f fun x hx => ?_
    have := hn x
    have h1 : IsIntegral (X.presheaf.stalk x) (f ^ q) := by
      rw [← hd, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
      exact isIntegral_algebraMap
    exact (IsIntegrallyClosed.isIntegral_iff (K := X.functionField)).1 (h1.of_pow (Nat.pos_of_ne_zero hq))
  obtain ⟨s, hs⟩ := key g c hc
  obtain ⟨s', hs'⟩ := key (g⁻¹ : (X.functionField)ˣ) ((c⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) (by
    have h2 : X.germToFunctionField W ((c⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * X.germToFunctionField W (c : Γ(X, W)) = 1 := by
      rw [← map_mul]; simp
    rw [hc] at h2
    rw [eq_comm, ← mul_right_inj' (pow_ne_zero q g.ne_zero)]
    rw [← mul_pow]
    simpa [mul_comm] using h2.symm)
  have h3 : s * s' = 1 := Scheme.germToFunctionField_injective X W (by
    rw [map_mul, hs, hs', map_one]; simp)
  have h4 : s' * s = 1 := by rw [mul_comm]; exact h3
  exact ⟨⟨s, s', h3, h4⟩, hs⟩

/- English proof (translation)
Take `⟨W, hW, s, hs⟩` from `X.presheaf.exists_germ_eq (u : X.presheaf.stalk y)`. Establish `hb : y ∈ X.basicOpen s` using `(X.mem_basicOpen s y hW).2 (by rw [hs]; exact u.isUnit)`. Use `⟨X.basicOpen s, hb, (X.toRingedSpace.isUnit_res_basicOpen s).unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, ← hs]`. Conclude with `X.presheaf.germ_res_apply _ _ _ _`.
-/
private theorem spread (y : X) (u : (X.presheaf.stalk y)ˣ) :
    ∃ (W : X.Opens) (hy : y ∈ W) (v : (Γ(X, W))ˣ), (X.presheaf.germ W y hy).hom (v : Γ(X, W)) = u := by
  obtain ⟨W, hW, s, hs⟩ := X.presheaf.exists_germ_eq (u : X.presheaf.stalk y)
  have hb : y ∈ X.basicOpen s := (X.mem_basicOpen s y hW).2 (by rw [hs]; exact u.isUnit)
  refine ⟨X.basicOpen s, hb, (X.toRingedSpace.isUnit_res_basicOpen s).unit, ?_⟩
  rw [IsUnit.unit_spec, ← hs]
  exact X.presheaf.germ_res_apply _ _ _ _

end UpperTheory.PicGlue

namespace UpperTheory.PicGlue

variable {X : Scheme.{0}}

/- English proof (translation)
Simplify using `using hq.map V.ι.appTop.hom`.
-/
private theorem qU (q : ℕ) (hq : IsUnit (q : Γ(X, ⊤))) (V : X.Opens) : IsUnit (q : Γ(V.toScheme, ⊤)) := by
  simpa using hq.map V.ι.appTop.hom

private noncomputable def tr (V : X.Opens) (v : (Γ(X, V))ˣ) : (Γ(V.toScheme, ⊤))ˣ :=
  Units.map (rho V).toMonoidHom v

private noncomputable def resU {U V : X.Opens} (e : V ≤ U) (v : (Γ(X, U))ˣ) : (Γ(X, V))ˣ :=
  Units.map (X.presheaf.map (homOfLE e).op).hom.toMonoidHom v

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 (X.homOfLE e) (tr U v) (qU q hq U)`. Establish `h2 : Units.map (X.homOfLE e).appTop.hom.toMonoidHom (tr U v) = tr V (resU e v)`. Use `ext`. Conclude with `rho_res e _`. Conclude with `h.trans (congrArg _ h2)`.
-/
private theorem nat_tr (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(X, ⊤))) {U V : X.Opens} (e : V ≤ U) (v : (Γ(X, U))ˣ) :
    pl q 1 (X.homOfLE e) 1 (kum q (tr U v)) = kum q (tr V (resU e v)) := by
  have h := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 (X.homOfLE e) (tr U v) (qU q hq U)
  have h2 : Units.map (X.homOfLE e).appTop.hom.toMonoidHom (tr U v) = tr V (resU e v) := by
    ext
    exact rho_res e _
  exact h.trans (congrArg _ h2)

/- English proof (translation)
The claim follows from `TopCat.Presheaf.germ_res_apply _ _ _ _ _`.
-/
private theorem gtf_res [IsIntegral X] {U V : X.Opens} [Nonempty U] [Nonempty V] (e : V ≤ U) (s : Γ(X, U)) :
    X.germToFunctionField V ((X.presheaf.map (homOfLE e).op).hom s) = X.germToFunctionField U s :=
  TopCat.Presheaf.germ_res_apply _ _ _ _ _

/- English proof (translation)
Rewrite using `[nat_tr q hq, nat_tr q hq]`. Establish `hA : X.germToFunctionField W (resU eU v : Γ(X, W)) = X.germToFunctionField U (v : Γ(X, U))` using `gtf_res eU _`. Establish `hB : X.germToFunctionField W (resU eV v' : Γ(X, W)) = X.germToFunctionField V (v' : Γ(X, V))` using `gtf_res eV _`. Establish `hb : X.germToFunctionField V (v' : Γ(X, V)) ≠ 0` using `(v'.isUnit.map (X.germToFunctionField V).hom).ne_zero`. Establish `hc1 : X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * X.germToFunctionField V (v' : Γ(X, V)) = X.germToFunctionField U (v : Γ(X, U))`.

Rewrite using `[← hA, ← hB, ← map_mul]`. Simplify using the standard rewrite rules. Establish `hh : (h : X.functionField) ^ q ≠ 0` using `pow_ne_zero q h.ne_zero`. Establish `hc : X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) = (((h' / h : (X.functionField)ˣ)) : X.functionField) ^ q`. Rewrite using `[Units.val_div_eq_div_val, div_pow, eq_div_iff hh]`.

Establish `h3 : X.germToFunctionField V (v' : Γ(X, V)) * (X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * (h : X.functionField) ^ q) = X.germToFunctionField V (v' : Γ(X, V)) * (h' : X.functionField) ^ q`. Rewrite using `[← hF', hF, ← hc1]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ hb h3`. Take `⟨w, hw⟩` from `sec_unit hn q (NeZero.ne q) W (h' / h) _ hc`.

Establish `hrel : resU eU v = resU eV v' * w ^ q`. Establish `h4 : resU eU v * (resU eV v')⁻¹ = w ^ q`. Use `ext`. Apply `Scheme.germToFunctionField_injective X W` to reduce the goal to its premises. Rewrite using `[hc, Units.val_pow_eq_pow_val, map_pow, hw]`.

Rewrite using `[← h4]`. Simplify using the standard rewrite rules. Establish `hm : tr W (resU eV v' * w ^ q) = tr W (resU eV v') * (tr W w) ^ q`. Simplify using `[tr]`. Rewrite using `[hrel, hm, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (tr W (resU eV v')) ((tr W w) ^ q) (qU q hq W)).1, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (tr W w) (tr W w) (qU q hq W)).2, add_zero]`.
-/
private theorem agree [IsIntegral X] (q : ℕ) [NeZero q] (hq : IsUnit (q : Γ(X, ⊤)))
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (F : X.functionField) {U V W : X.Opens}
    [Nonempty U] [Nonempty V] [Nonempty W] (eU : W ≤ U) (eV : W ≤ V) (v : (Γ(X, U))ˣ) (v' : (Γ(X, V))ˣ)
    (h h' : (X.functionField)ˣ) (hF : F = X.germToFunctionField U (v : Γ(X, U)) * (h : X.functionField) ^ q)
    (hF' : F = X.germToFunctionField V (v' : Γ(X, V)) * (h' : X.functionField) ^ q) :
    pl q 1 (X.homOfLE eU) 1 (kum q (tr U v)) = pl q 1 (X.homOfLE eV) 1 (kum q (tr V v')) := by
  rw [nat_tr q hq, nat_tr q hq]
  have hA : X.germToFunctionField W (resU eU v : Γ(X, W)) = X.germToFunctionField U (v : Γ(X, U)) := gtf_res eU _
  have hB : X.germToFunctionField W (resU eV v' : Γ(X, W)) = X.germToFunctionField V (v' : Γ(X, V)) := gtf_res eV _
  have hb : X.germToFunctionField V (v' : Γ(X, V)) ≠ 0 := (v'.isUnit.map (X.germToFunctionField V).hom).ne_zero
  have hc1 : X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) *
      X.germToFunctionField V (v' : Γ(X, V)) = X.germToFunctionField U (v : Γ(X, U)) := by
    rw [← hA, ← hB, ← map_mul]
    simp
  have hh : (h : X.functionField) ^ q ≠ 0 := pow_ne_zero q h.ne_zero
  have hc : X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) =
      (((h' / h : (X.functionField)ˣ)) : X.functionField) ^ q := by
    rw [Units.val_div_eq_div_val, div_pow, eq_div_iff hh]
    have h3 : X.germToFunctionField V (v' : Γ(X, V)) *
        (X.germToFunctionField W ((resU eU v * (resU eV v')⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * (h : X.functionField) ^ q) =
        X.germToFunctionField V (v' : Γ(X, V)) * (h' : X.functionField) ^ q := by
      rw [← hF', hF, ← hc1]
      ring
    exact mul_left_cancel₀ hb h3
  obtain ⟨w, hw⟩ := sec_unit hn q (NeZero.ne q) W (h' / h) _ hc
  have hrel : resU eU v = resU eV v' * w ^ q := by
    have h4 : resU eU v * (resU eV v')⁻¹ = w ^ q := by
      ext
      apply Scheme.germToFunctionField_injective X W
      rw [hc, Units.val_pow_eq_pow_val, map_pow, hw]
    rw [← h4]
    simp
  have hm : tr W (resU eV v' * w ^ q) = tr W (resU eV v') * (tr W w) ^ q := by
    simp [tr]
  rw [hrel, hm, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (tr W (resU eV v')) ((tr W w) ^ q) (qU q hq W)).1,
    ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (tr W w) (tr W w) (qU q hq W)).2, add_zero]

/- English proof (translation)
Substitute `hT` using the available equality. Conclude with `(inferInstance : IsIso (Scheme.topIso X).hom)`.
-/
private theorem isIso_ι (T : X.Opens) (hT : T = ⊤) : IsIso T.ι := by
  subst hT
  exact (inferInstance : IsIso (Scheme.topIso X).hom)

/- English proof (translation)
Establish `hW : ∀ i j, Nonempty (U i ⊓ U j : X.Opens)` using `fun i j => by`. Take `⟨⟨a, ha⟩⟩` from `‹∀ i, Nonempty (U i)› i`. Take `⟨⟨b, hb⟩⟩` from `‹∀ i, Nonempty (U i)› j`. Take `⟨y, hy⟩ : ((U i : Set X) ∩ U j).Nonempty` from `nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨a, ha⟩ ⟨b, hb⟩`. Conclude with `⟨⟨y, hy⟩⟩`.

Take `⟨y, hy⟩` from `UpperTheory.exists_h1Mu_glue_of_compatible q X hP hq n U (fun i => kum q (tr (U i) (v i))) (fun i j => by`. Use `hW i j` as an intermediate fact. Conclude with `agree q hq hn F inf_le_left inf_le_right (v i) (v j) (h i) (h j) (hF i) (hF j))`. Establish `hξ : genericPoint X ∈ (⨆ i, U i : X.Opens)`. Rewrite using `[hU]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hξ`. Use `isIso_ι (⨆ i, U i) hU` as an intermediate fact. Establish `hcomp : X.fromSpecStalk (genericPoint X) ≫ inv (⨆ i, U i : X.Opens).ι = (U i).fromSpecStalkOfMem _ hi ≫ X.homOfLE (le_iSup U i)`. Rewrite using `[← cancel_mono (⨆ i, U i : X.Opens).ι, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]`.

Use `⟨pl q 1 (inv (⨆ i, U i : X.Opens).ι) 1 y, ?_⟩` and prove the remaining obligations. Rewrite using `[← pl_comp, hcomp, pl_comp, hy i]`. Establish `hqS : IsUnit (q : Γ(Spec X.functionField, ⊤))`. Simplify using `using hq.map (X.fromSpecStalk (genericPoint X)).appTop.hom`. Establish `h1` using `(GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 ((U i).fromSpecStalkOfMem _ hi) (tr (U i) (v i)) (qU q hq _)`.

Establish `h2 : Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F = Units.map ((U i).fromSpecStalkOfMem _ hi).appTop.hom.toMonoidHom (tr (U i) (v i)) * (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i)) ^ q`. Use `ext`. Establish `h3` using `rho_generic (U i) _ hi (v i : Γ(X, U i))`. Establish `h4` using `congrArg (Scheme.ΓSpecIso X.functionField).inv.hom (hF i)`. Rewrite `h4` using `[map_mul, map_pow]`.

Conclude with `h4.trans (congrArg (· * _) h3.symm)`. Use `h1.trans ?_` and prove the remaining obligations. Establish `hb` using `((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i)) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i)) hqS).2`. Rewrite using `[h2, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 _ _ hqS).1, hb, add_zero]`.
-/
private theorem core (q : ℕ) [NeZero q] [IsIntegral X] (hP : Nonempty (Prim q Γ(X, ⊤))) (hq : IsUnit (q : Γ(X, ⊤)))
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (F : (X.functionField)ˣ) (n : ℕ) (U : Fin n → X.Opens)
    [∀ i, Nonempty (U i)] (hU : ⨆ i, U i = ⊤) (v : ∀ i, (Γ(X, U i))ˣ) (h : Fin n → (X.functionField)ˣ)
    (hF : ∀ i, (F : X.functionField) = X.germToFunctionField (U i) (v i : Γ(X, U i)) * (h i : X.functionField) ^ q) :
    ∃ x : Ht q (sch.obj X) 1 1, pl q 1 (X.fromSpecStalk (genericPoint X)) 1 x =
      kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) := by
  have hW : ∀ i j, Nonempty (U i ⊓ U j : X.Opens) := fun i j => by
    obtain ⟨⟨a, ha⟩⟩ := ‹∀ i, Nonempty (U i)› i
    obtain ⟨⟨b, hb⟩⟩ := ‹∀ i, Nonempty (U i)› j
    obtain ⟨y, hy⟩ : ((U i : Set X) ∩ U j).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨⟨y, hy⟩⟩
  obtain ⟨y, hy⟩ := UpperTheory.exists_h1Mu_glue_of_compatible q X hP hq n U (fun i => kum q (tr (U i) (v i))) (fun i j => by
    have := hW i j
    exact agree q hq hn F inf_le_left inf_le_right (v i) (v j) (h i) (h j) (hF i) (hF j))
  have hξ : genericPoint X ∈ (⨆ i, U i : X.Opens) := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hξ
  have := isIso_ι (⨆ i, U i) hU
  have hcomp : X.fromSpecStalk (genericPoint X) ≫ inv (⨆ i, U i : X.Opens).ι =
      (U i).fromSpecStalkOfMem _ hi ≫ X.homOfLE (le_iSup U i) := by
    rw [← cancel_mono (⨆ i, U i : X.Opens).ι, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  refine ⟨pl q 1 (inv (⨆ i, U i : X.Opens).ι) 1 y, ?_⟩
  rw [← pl_comp, hcomp, pl_comp, hy i]
  have hqS : IsUnit (q : Γ(Spec X.functionField, ⊤)) := by
    simpa using hq.map (X.fromSpecStalk (genericPoint X)).appTop.hom
  have h1 := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 ((U i).fromSpecStalkOfMem _ hi) (tr (U i) (v i)) (qU q hq _)
  have h2 : Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F =
      Units.map ((U i).fromSpecStalkOfMem _ hi).appTop.hom.toMonoidHom (tr (U i) (v i)) *
        (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i)) ^ q := by
    ext
    have h3 := rho_generic (U i) _ hi (v i : Γ(X, U i))
    have h4 := congrArg (Scheme.ΓSpecIso X.functionField).inv.hom (hF i)
    rw [map_mul, map_pow] at h4
    exact h4.trans (congrArg (· * _) h3.symm)
  refine h1.trans ?_
  have hb := ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i))
    (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom (h i)) hqS).2
  rw [h2, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 _ _ hqS).1, hb, add_zero]

end UpperTheory.PicGlue

/- English proof (translation)
Introduce `q _ X _ hP hq hc hn F hF`. Use `choose u h hu using hF`. Use `choose W hy v hv using fun y => UpperTheory.PicGlue.spread y (u y)`. Take `⟨t, -, ht⟩` from `isCompact_univ.elim_nhds_subcover (fun y => (W y : Set X)) (fun y _ => (W y).isOpen.mem_nhds (hy y))`. Set `idx : Fin t.card → X` to `fun i => (t.equivFin.symm i).1`.

Establish `: ∀ i, Nonempty (W (idx i))` using `fun i => ⟨⟨_, hy _⟩⟩`. Use `UpperTheory.PicGlue.core q hP hq hn F t.card (fun i => W (idx i)) ?_ (fun i => v (idx i)) (fun i => h (idx i)) (fun i => ?_)` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨z, hz, hyz⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ y))`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨z, hz⟩, by simpa [idx] using hyz⟩`. Rewrite using `[hu (idx i), ← hv (idx i), Scheme.algebraMap_germ_eq_germToFunctionField X (hy (idx i))]`.
-/
theorem UpperTheory.exists_h1Mu_of_locally_unit_times_power :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → CompactSpace X → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ x : Ht q (sch.obj X) 1 1, pl q 1 (X.fromSpecStalk (genericPoint X)) 1 x = kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) := by
  intro q _ X _ hP hq hc hn F hF
  choose u h hu using hF
  choose W hy v hv using fun y => UpperTheory.PicGlue.spread y (u y)
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun y => (W y : Set X))
    (fun y _ => (W y).isOpen.mem_nhds (hy y))
  let idx : Fin t.card → X := fun i => (t.equivFin.symm i).1
  have : ∀ i, Nonempty (W (idx i)) := fun i => ⟨⟨_, hy _⟩⟩
  refine UpperTheory.PicGlue.core q hP hq hn F t.card (fun i => W (idx i)) ?_ (fun i => v (idx i)) (fun i => h (idx i)) (fun i => ?_)
  · rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨z, hz⟩, by simpa [idx] using hyz⟩
  · rw [hu (idx i), ← hv (idx i), Scheme.algebraMap_germ_eq_germToFunctionField X (hy (idx i))]
