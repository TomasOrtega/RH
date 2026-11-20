import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.EpsCocycle

noncomputable section

/- English proof (translation)
Use `ext`. Simplify using `only [res, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
lemma res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Use `congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k)) (hL.cocycle i j k)` as an intermediate fact. Simplify `this` using `only [map_mul, res_res]`.
-/
lemma cocycle_on {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  simpa only [map_mul, res_res] using this

def regauge {X : Scheme.{0}} (L : LB X) (u : ∀ i, Γ(X, L.U i)ˣ) : LB X :=
  ⟨L.ι, L.U, fun i i' => (res inf_le_left (u i))⁻¹ * L.g i i' * res inf_le_right (u i')⟩

/- English proof (translation)
The claim follows from `hL.cover g_self := fun i => by have := hL.g_self i change res (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) ((res inf_le_left (u i))⁻¹ * L.g i i * res inf_le_right (u i)) = 1 simp only [map_mul, map_inv, res_res, this, _root_.mul_one, inv_mul_cancel] cocycle := fun i j k => by h …`.
-/
lemma regauge_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    (regauge L u).IsLB where
  cover := hL.cover
  g_self := fun i => by
    have := hL.g_self i
    change res (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i)
      ((res inf_le_left (u i))⁻¹ * L.g i i * res inf_le_right (u i)) = 1
    simp only [map_mul, map_inv, res_res, this, _root_.mul_one, inv_mul_cancel]
  cocycle := fun i j k => by
    have := hL.cocycle i j k
    change res (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j)
        ((res inf_le_left (u i))⁻¹ * L.g i j * res inf_le_right (u j)) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k)
        ((res inf_le_left (u j))⁻¹ * L.g j k * res inf_le_right (u k)) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k)
        ((res inf_le_left (u i))⁻¹ * L.g i k * res inf_le_right (u k))
    simp only [map_mul, map_inv, res_res, ← this]
    group

/- English proof (translation)
Use `⟨⟨fun p : L.ι × L.ι => ((res inf_le_left (u p.1))⁻¹ * L.g p.1 p.2 : Γ(X, L.U p.1 ⊓ L.U p.2)ˣ)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a, b⟩ ⟨a', b'⟩`. Set `W : X.Opens` to `L.U a ⊓ L.U b ⊓ (L.U a' ⊓ L.U b')`. Establish `ha : W ≤ L.U a` using `inf_le_left.trans inf_le_left`. Establish `hb : W ≤ L.U b` using `inf_le_left.trans inf_le_right`.

Establish `ha' : W ≤ L.U a'` using `inf_le_right.trans inf_le_left`. Establish `hb' : W ≤ L.U b'` using `inf_le_right.trans inf_le_right`. Express the relevant statement in the definitionally equal form `res (le_inf ha hb) ((res inf_le_left (u a))⁻¹ * L.g a b) = (res (le_inf ha ha') ((res inf_le_left (u a))⁻¹ * L.g a a' * res inf_le_right (u a')) * (res (le_inf hb hb') (L.g b b'))⁻¹) * res (le_inf ha' hb') ((res inf_le_left (u a'))⁻¹ * L.g a' b')`. Establish `e₁` using `cocycle_on hL a a' b' (le_inf ha ha') (le_inf ha' hb') (le_inf ha hb')`. Establish `e₂` using `cocycle_on hL a b b' (le_inf ha hb) (le_inf hb hb') (le_inf ha hb')`.

Establish `e₃ : res (le_inf ha hb) (L.g a b) = res (le_inf ha ha') (L.g a a') * res (le_inf ha' hb') (L.g a' b') * (res (le_inf hb hb') (L.g b b'))⁻¹`. Rewrite using `[e₁, ← e₂, mul_inv_cancel_right]`. Simplify using `only [map_mul, map_inv, res_res, e₃]`. Generalize the expression as in `res ha (u a) = x`. Generalize the expression as in `res ha' (u a') = y`.

Generalize the expression as in `res (le_inf ha ha') (L.g a a') = z`. Generalize the expression as in `res (le_inf ha' hb') (L.g a' b') = w`. Generalize the expression as in `res (le_inf hb hb') (L.g b b') = v`. Rewrite using `[mul_mul_mul_comm _ v⁻¹, mul_inv_cancel_right]`. The two sides agree by associativity and commutativity.
-/
lemma regauge_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    LBIso L (regauge L u) := by
  refine ⟨⟨fun p : L.ι × L.ι => ((res inf_le_left (u p.1))⁻¹ * L.g p.1 p.2 :
    Γ(X, L.U p.1 ⊓ L.U p.2)ˣ)⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨a', b'⟩
  let W : X.Opens := L.U a ⊓ L.U b ⊓ (L.U a' ⊓ L.U b')
  have ha : W ≤ L.U a := inf_le_left.trans inf_le_left
  have hb : W ≤ L.U b := inf_le_left.trans inf_le_right
  have ha' : W ≤ L.U a' := inf_le_right.trans inf_le_left
  have hb' : W ≤ L.U b' := inf_le_right.trans inf_le_right
  change res (le_inf ha hb) ((res inf_le_left (u a))⁻¹ * L.g a b) =
    (res (le_inf ha ha') ((res inf_le_left (u a))⁻¹ * L.g a a' * res inf_le_right (u a')) *
      (res (le_inf hb hb') (L.g b b'))⁻¹) *
      res (le_inf ha' hb') ((res inf_le_left (u a'))⁻¹ * L.g a' b')
  have e₁ := cocycle_on hL a a' b' (le_inf ha ha') (le_inf ha' hb') (le_inf ha hb')
  have e₂ := cocycle_on hL a b b' (le_inf ha hb) (le_inf hb hb') (le_inf ha hb')
  have e₃ : res (le_inf ha hb) (L.g a b) = res (le_inf ha ha') (L.g a a') *
      res (le_inf ha' hb') (L.g a' b') * (res (le_inf hb hb') (L.g b b'))⁻¹ := by
    rw [e₁, ← e₂, mul_inv_cancel_right]
  simp only [map_mul, map_inv, res_res, e₃]
  generalize res ha (u a) = x
  generalize res ha' (u a') = y
  generalize res (le_inf ha ha') (L.g a a') = z
  generalize res (le_inf ha' hb') (L.g a' b') = w
  generalize res (le_inf hb hb') (L.g b b') = v
  rw [mul_mul_mul_comm _ v⁻¹, mul_inv_cancel_right]
  ac_rfl

/- English proof (translation)
Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]`. Establish `key : ∀ (f : Y ⟶ Y) (_ : f = 𝟙 Y) (e : O₂ ≤ f ⁻¹ᵁ O), (f.appLE O O₂ e).hom a = resG Y h'' a`. Introduce `f hf e`. Substitute `hf` using the available equality. Simplify using `[Scheme.Hom.appLE]`.

Both sides reduce to the same expression. Conclude with `key _ hj _`.
-/
lemma appLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)) :
    (j.appLE O' O₂ h').hom ((ρ.appLE O O' h).hom a) = resG Y h'' a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Y) (_ : f = 𝟙 Y) (e : O₂ ≤ f ⁻¹ᵁ O), (f.appLE O O₂ e).hom a = resG Y h'' a := by
    intro f hf e
    subst hf
    simp [Scheme.Hom.appLE]
    rfl
  exact key _ hj _

/- English proof (translation)
Establish `h0 : O' ≤ π ⁻¹ᵁ ⊤` using `fun _ _ => trivial`. Express the relevant statement in the definitionally equal form `(j.appLE O' O h).hom ((π.appLE ⊤ O' h0).hom ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps)) = 0`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]`. Establish `key : ∀ (f : Y ⟶ Sp (DualNumber ℂ)) (_ : f = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (e : O ≤ f ⁻¹ᵁ ⊤), (f.appLE ⊤ O e).hom ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = 0`. Introduce `f hf e`.

Substitute `hf` using the available equality. Rewrite using `[Scheme.Hom.comp_appLE, CommRingCat.comp_apply]`. Use `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)` as an intermediate fact. Establish `e2` using `congrArg (fun φ => φ.hom DualNumber.eps) this`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e2`.

Establish `e3 : (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom DualNumber.eps = 0`. Simplify using the standard rewrite rules. Rewrite `e2` using `[e3, map_zero]`. Conclude with `(congrArg _ e2.symm).trans (map_zero _)`. Conclude with `key _ hq _`.
-/
lemma appLE_constFn_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)}
    {j : Y ⟶ Y'} (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    {O : Y.Opens} {O' : Y'.Opens} (h : O ≤ j ⁻¹ᵁ O') :
    (j.appLE O' O h).hom (constFn π O' DualNumber.eps) = 0 := by
  have h0 : O' ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  change (j.appLE O' O h).hom ((π.appLE ⊤ O' h0).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps)) = 0
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Sp (DualNumber ℂ))
      (_ : f = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (e : O ≤ f ⁻¹ᵁ ⊤),
      (f.appLE ⊤ O e).hom ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = 0 := by
    intro f hf e
    subst hf
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have e2 := congrArg (fun φ => φ.hom DualNumber.eps) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    have e3 : (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom DualNumber.eps = 0 := by
      simp
    rw [e3, map_zero] at e2
    exact (congrArg _ e2.symm).trans (map_zero _)
  exact key _ hq _

/- English proof (translation)
Take `⟨h₁, -, h₃⟩` from `GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq`. Establish `key : ∀ (O : Y.Opens) (O' : Y'.Opens) (_ : ρ ⁻¹ᵁ O = O') (F : Γ(Y', O')), ∃ a b : Γ(Y, O), ∀ h : O' ≤ ρ ⁻¹ᵁ O, F = (ρ.appLE _ _ h).hom a + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom b`. Introduce `O O' e F`. Substitute `e` using the available equality. Take `⟨ab, hab, -⟩` from `h₃ O F`.

Use `⟨ab.1, ab.2, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.appLE_eq_app]`. Conclude with `hab`. Take `⟨a, b, hab⟩` from `key _ O' (h₁ O') F`. Use `⟨b, fun h => ?_⟩` and prove the remaining obligations.

Establish `ha : a = 1`. Rewrite `hF` using `[hab h, map_add, map_mul, appLE_constFn_eps hq, zero_mul, add_zero, appLE_section hj h le_rfl le_rfl]`. Establish `e : resG Y (le_refl (j ⁻¹ᵁ O')) a = a`. Express the relevant statement in the definitionally equal form `(Y.presheaf.map (𝟙 _)).hom a = a`. Rewrite using `[Y.presheaf.map_id]`.

Both sides reduce to the same expression. Conclude with `e.symm.trans hF`. Rewrite using `[hab h, ha, map_one]`.
-/
lemma eq_one_add_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)} {ρ : Y' ⟶ Y}
    {j : Y ⟶ Y'} (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (O' : Y'.Opens)
    (F : Γ(Y', O')) (hF : (j.appLE O' _ le_rfl).hom F = 1) :
    ∃ k : Γ(Y, j ⁻¹ᵁ O'), ∀ h : O' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ O'),
      F = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom k := by
  obtain ⟨h₁, -, h₃⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have key : ∀ (O : Y.Opens) (O' : Y'.Opens) (_ : ρ ⁻¹ᵁ O = O') (F : Γ(Y', O')), ∃ a b : Γ(Y, O),
      ∀ h : O' ≤ ρ ⁻¹ᵁ O,
        F = (ρ.appLE _ _ h).hom a + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom b := by
    intro O O' e F
    subst e
    obtain ⟨ab, hab, -⟩ := h₃ O F
    refine ⟨ab.1, ab.2, fun h => ?_⟩
    rw [Scheme.Hom.appLE_eq_app]
    exact hab
  obtain ⟨a, b, hab⟩ := key _ O' (h₁ O') F
  refine ⟨b, fun h => ?_⟩
  have ha : a = 1 := by
    rw [hab h, map_add, map_mul, appLE_constFn_eps hq, zero_mul, add_zero,
      appLE_section hj h le_rfl le_rfl] at hF
    have e : resG Y (le_refl (j ⁻¹ᵁ O')) a = a := by
      change (Y.presheaf.map (𝟙 _)).hom a = a
      rw [Y.presheaf.map_id]
      rfl
    exact e.symm.trans hF
  rw [hab h, ha, map_one]

def pullLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, V)ˣ := Units.map (f.appLE U V h).hom

/- English proof (translation)
Use `ext`. Both sides reduce to the same expression.
-/
lemma pullLE_eq {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (x : Γ(X, U)ˣ) : pullLE f h x = res h (pullU f U x) := by
  ext
  rfl

/- English proof (translation)
Use `ext`. Simplify using `only [pullLE, res, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.map_appLE]`.
-/
lemma pullLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U')
    (h' : U' ≤ U) (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pullLE f h (res h' x) = pullLE f h'' x := by
  ext
  simp only [pullLE, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/- English proof (translation)
Use `ext`. Conclude with `appLE_section hj h h' h'' a.val`.
-/
lemma pullLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)ˣ) : pullLE j h' (pullLE ρ h a) = res h'' a := by
  ext
  exact appLE_section hj h h' h'' a.val

/- English proof (translation)
Introduce `Y Y' q π ρ j hp hj hq Q hQ ⟨t, ht⟩`. Take `⟨h₁, -, -⟩` from `GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq`. Establish `hw : ∀ i : Q.ι, j ⁻¹ᵁ Q.U i ≤ (Q.pull j).U (fun _ => i)` using `fun i _ hy => Set.mem_iInter.2 fun _ => hy`. Set `s : ∀ i : Q.ι, Γ(Y, j ⁻¹ᵁ Q.U i)ˣ` to `fun i => res (hw i) (t.s fun _ => i)`. Set `u : ∀ i, Γ(Y', Q.U i)ˣ` to `fun i => pullLE ρ (h₁ (Q.U i)).ge (s i)`.

Establish `main : ∀ i i' : Q.ι, (j.appLE (Q.U i ⊓ Q.U i') _ le_rfl).hom ((regauge Q u).g i i').val = 1`. Introduce `i i'`. Establish `hl : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i` using `fun _ hy => hy.1`. Establish `hr : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i'` using `fun _ hy => hy.2`. Establish `e` using `congrArg (res (le_inf (hl.trans (hw i)) (hr.trans (hw i')))) (ht (fun _ => i) (fun _ => i'))`.

Establish `eg : res (le_inf (hl.trans (hw i)) (hr.trans (hw i'))) ((Q.pull j).g (fun _ => i) (fun _ => i')) = pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (Q.g i i')`. Rewrite using `[pullLE_eq]`. Express the relevant statement in the definitionally equal form `res _ (∏ _k : PUnit.{1}, (res _ (pullU j _ (Q.g i i'))) ^ (1 : ℤ)) = _`. Rewrite using `[Fintype.prod_unique, zpow_one]`. Conclude with `res_res _ _ _`.

Rewrite `e` using `[map_mul, res_res, res_res, eg]`. Establish `: pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) ((res inf_le_left (u i))⁻¹ * Q.g i i' * res inf_le_right (u i')) = 1`. Rewrite using `[map_mul, map_mul, map_inv, pullLE_res j _ _ hl, pullLE_res j _ _ hr, pullLE_section hj _ _ hl, pullLE_section hj _ _ hr, res_res, res_res, _root_.mul_assoc, ← e, inv_mul_cancel]`. Conclude with `congrArg Units.val this`. Use `choose k hk using fun i i' : Q.ι => eq_one_add_eps hp hj hq _ _ (main i i')`.

Conclude with `⟨regauge Q u, k, regauge_isLB hQ u, regauge_iso hQ u, hk⟩`.
-/
theorem exists_cocycle_one_add_eps : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ Q : LB Y', Q.IsLB → (∃ t : (Q.pull j).Gen, t.IsGen) → ∃ (Q' : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), Q'.IsLB ∧ LBIso Q Q' ∧ (∀ i i' (h : Q'.U i ⊓ Q'.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), (Q'.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) := by
  intro Y Y' q π ρ j hp hj hq Q hQ ⟨t, ht⟩
  obtain ⟨h₁, -, -⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have hw : ∀ i : Q.ι, j ⁻¹ᵁ Q.U i ≤ (Q.pull j).U (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  let s : ∀ i : Q.ι, Γ(Y, j ⁻¹ᵁ Q.U i)ˣ := fun i => res (hw i) (t.s fun _ => i)
  let u : ∀ i, Γ(Y', Q.U i)ˣ := fun i => pullLE ρ (h₁ (Q.U i)).ge (s i)
  have main : ∀ i i' : Q.ι, (j.appLE (Q.U i ⊓ Q.U i') _ le_rfl).hom ((regauge Q u).g i i').val = 1 := by
    intro i i'
    have hl : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have hr : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have e := congrArg (res (le_inf (hl.trans (hw i)) (hr.trans (hw i'))))
      (ht (fun _ => i) (fun _ => i'))
    have eg : res (le_inf (hl.trans (hw i)) (hr.trans (hw i')))
        ((Q.pull j).g (fun _ => i) (fun _ => i')) =
        pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (Q.g i i') := by
      rw [pullLE_eq]
      change res _ (∏ _k : PUnit.{1}, (res _ (pullU j _ (Q.g i i'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact res_res _ _ _
    rw [map_mul, res_res, res_res, eg] at e
    have : pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i')))
        ((res inf_le_left (u i))⁻¹ * Q.g i i' * res inf_le_right (u i')) = 1 := by
      rw [map_mul, map_mul, map_inv, pullLE_res j _ _ hl, pullLE_res j _ _ hr,
        pullLE_section hj _ _ hl, pullLE_section hj _ _ hr, res_res, res_res, _root_.mul_assoc, ← e,
        inv_mul_cancel]
    exact congrArg Units.val this
  choose k hk using fun i i' : Q.ι => eq_one_add_eps hp hj hq _ _ (main i i')
  exact ⟨regauge Q u, k, regauge_isLB hQ u, regauge_iso hQ u, hk⟩

end

end GlobalTheory.EpsCocycle
