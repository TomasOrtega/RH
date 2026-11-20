import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.LocDerExt

/- English proof (translation)
Take `⟨⟨a, t⟩, e⟩` from `IsLocalization.surj (Submonoid.powers f) s`. Establish `hu : IsUnit (φ (algebraMap A B t))` using `(IsLocalization.map_units B t).map φ`. Establish `e₁` using `h₁ s (algebraMap A B t)`. Establish `e₂` using `h₂ s (algebraMap A B t)`. Simplify using `only at e`.

Rewrite `e₁`, `e₂` using `[e]`. Rewrite `e₁` using `[h, e₂, h]`. Conclude with `(hu.mul_left_cancel (add_left_cancel e₁)).symm`.
-/
theorem der_unique {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (δ₁ δ₂ : B → C)
    (h₁ : ∀ a b, δ₁ (a * b) = φ a * δ₁ b + φ b * δ₁ a)
    (h₂ : ∀ a b, δ₂ (a * b) = φ a * δ₂ b + φ b * δ₂ a)
    (h : ∀ a, δ₁ (algebraMap A B a) = δ₂ (algebraMap A B a)) (s : B) : δ₁ s = δ₂ s := by
  obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) s
  have hu : IsUnit (φ (algebraMap A B t)) := (IsLocalization.map_units B t).map φ
  have e₁ := h₁ s (algebraMap A B t)
  have e₂ := h₂ s (algebraMap A B t)
  dsimp only at e
  rw [e] at e₁ e₂
  rw [h, e₂, h] at e₁
  exact (hu.mul_left_cancel (add_left_cancel e₁)).symm

/- English proof (translation)
Establish `h0 : d 0 = 0`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.mp this`. Establish `h1 : d 1 = 0`.

Use `hmul 1 1` as an intermediate fact. Simplify using `only [_root_.mul_one, map_one, _root_.one_mul] at this`. Conclude with `left_eq_add.mp this`. Apply the tactic sequence `obtain ⟨ψ, hψ1, hψ2⟩ : ∃ ψ : A →+* DualNumber C, (∀ a, (ψ a).fst = φ (algebraMap A B a)) ∧ ∀ a, (ψ a).snd = d a := ⟨{ toFun := fun a => TrivSqZeroExt.inl (φ (algebraMap A B a)) + TrivSqZeroExt.inr (d a) map_one' := by ext <;> simp [h1] map_zero' := by ext <;> simp [h0] map_add' : …`. Establish `hu : IsUnit (ψ f)`.

Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ1]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit f).map φ`. Take `⟨Ψ, hΨ⟩ : ∃ Ψ : B →+* DualNumber C, ∀ a, Ψ (algebraMap A B a) = ψ a` from `⟨IsLocalization.Away.lift f hu, fun a => IsLocalization.Away.lift_eq f hu a⟩`. Take `⟨π, hπ⟩ : ∃ π : DualNumber C →+* C, ∀ x, π x = x.fst` from `⟨(TrivSqZeroExt.fstHom C C C).toRingHom, fun _ => rfl⟩`. Establish `hf : π.comp Ψ = φ`.

Apply `IsLocalization.ringHom_ext (Submonoid.powers f)` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, hΨ, hπ, hψ1]`. Establish `hf' : ∀ b, (Ψ b).fst = φ b` using `fun b => by rw [← hf, RingHom.comp_apply, hπ]`. Use `⟨fun b => (Ψ b).snd, fun a b => by simp only [map_add, TrivSqZeroExt.snd_add], fun a b => ?_, fun a => by simp only [hΨ, hψ2]⟩` and prove the remaining obligations.

Simplify using `only [map_mul, DualNumber.snd_mul, hf']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem der_exists {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (d : A → C)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = φ (algebraMap A B a) * d b + φ (algebraMap A B b) * d a) :
    ∃ δ : B → C, (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = φ a * δ b + φ b * δ a) ∧
      ∀ a, δ (algebraMap A B a) = d a := by
  have h0 : d 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have h1 : d 1 = 0 := by
    have := hmul 1 1
    simp only [_root_.mul_one, map_one, _root_.one_mul] at this
    exact left_eq_add.mp this
  obtain ⟨ψ, hψ1, hψ2⟩ : ∃ ψ : A →+* DualNumber C, (∀ a, (ψ a).fst = φ (algebraMap A B a)) ∧
      ∀ a, (ψ a).snd = d a :=
    ⟨{ toFun := fun a => TrivSqZeroExt.inl (φ (algebraMap A B a)) + TrivSqZeroExt.inr (d a)
       map_one' := by ext <;> simp [h1]
       map_zero' := by ext <;> simp [h0]
       map_add' := fun a b => by ext <;> simp [hadd]
       map_mul' := fun a b => by ext <;> simp [hmul, mul_comm] }, fun a => by simp, fun a => by simp⟩
  have hu : IsUnit (ψ f) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ1]
    exact (IsLocalization.Away.algebraMap_isUnit f).map φ
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : B →+* DualNumber C, ∀ a, Ψ (algebraMap A B a) = ψ a :=
    ⟨IsLocalization.Away.lift f hu, fun a => IsLocalization.Away.lift_eq f hu a⟩
  obtain ⟨π, hπ⟩ : ∃ π : DualNumber C →+* C, ∀ x, π x = x.fst :=
    ⟨(TrivSqZeroExt.fstHom C C C).toRingHom, fun _ => rfl⟩
  have hf : π.comp Ψ = φ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply, hΨ, hπ, hψ1]
  have hf' : ∀ b, (Ψ b).fst = φ b := fun b => by rw [← hf, RingHom.comp_apply, hπ]
  refine ⟨fun b => (Ψ b).snd, fun a b => by simp only [map_add, TrivSqZeroExt.snd_add],
    fun a b => ?_, fun a => by simp only [hΨ, hψ2]⟩
  simp only [map_mul, DualNumber.snd_mul, hf']
  ring

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(X.presheaf.map _ ≫ X.presheaf.map _).hom s = _`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res (X : Scheme.{0}) {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (s : Γ(X, U)) :
    resG X k (resG X h s) = resG X (k.trans h) s := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom s = _
  rw [← Functor.map_comp]
  rfl

/- English proof (translation)
The claim follows from `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)`.
-/
theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

/- English proof (translation)
Introduce `_ hy` and use `h hy`.
-/
theorem pre_le {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U :=
  fun _ hy => h hy

/- English proof (translation)
The claim follows from `congrArg (fun φ => φ.hom s) (Scheme.Hom.naturality m (homOfLE h).op)`.
-/
theorem app_res {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    (m.app V).hom (resG X h s) = resG Y (pre_le m h) ((m.app U).hom s) :=
  congrArg (fun φ => φ.hom s) (Scheme.Hom.naturality m (homOfLE h).op)

/- English proof (translation)
Introduce `y hy`. Take `⟨f, hf, hx⟩` from `hW.exists_basicOpen_le (V := W) ⟨m y, hy⟩ (h hy)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩`.
-/
theorem cover {Y X : Scheme.{0}} (m : Y ⟶ X) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens}
    (h : W ≤ W₀) :
    m ⁻¹ᵁ W ≤ ⨆ i : {f : Γ(X, W₀) // X.basicOpen f ≤ W}, m ⁻¹ᵁ X.basicOpen i.1 := by
  intro y hy
  obtain ⟨f, hf, hx⟩ := hW.exists_basicOpen_le (V := W) ⟨m y, hy⟩ (h hy)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩

/- English proof (translation)
The claim follows from `Y.sheaf.eq_of_locally_eq' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1) (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h) s t (fun i => e i.1 i.2)`.
-/
theorem sep {Y X : Scheme.{0}} (m : Y ⟶ X) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens}
    (h : W ≤ W₀) (s t : Γ(Y, m ⁻¹ᵁ W))
    (e : ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) s = resG Y (pre_le m k) t) :
    s = t :=
  Y.sheaf.eq_of_locally_eq' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1)
    (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h) s t (fun i => e i.1 i.2)

/- English proof (translation)
Introduce `R _ Y X q p m D W₀ hW d₀ hadd hmul hbase`. Establish `H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(Y, m ⁻¹ᵁ X.basicOpen f), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = (m.app _).hom a * δ b + (m.app _).hom b * δ a) ∧ ∀ a, δ (resG X (X.basicOpen_le f) a) = resG Y (pre_le m (X.basicOpen_le f)) (d₀ a)`. Introduce `f`. Use `haveI := hW.isLocalization_basicOpen f`. Use `der_exists f (m.app (X.basicOpen f)).hom (fun a => resG Y (pre_le m (X.basicOpen_le f)) (d₀ a)) (fun a b => by simp only [hadd, map_add]) (fun a b => ?_)` and prove the remaining obligations.

Establish `e : ∀ a, (m.app (X.basicOpen f)).hom (algebraMap Γ(X, W₀) Γ(X, X.basicOpen f) a) = resG Y (pre_le m (X.basicOpen_le f)) ((m.app W₀).hom a)` using `fun a => app_res m (X.basicOpen_le f) a`. Rewrite using `[e, e]`. Simplify using `only [hmul, map_add, map_mul]`. Use `choose δ δadd δmul δres using H`. Establish `compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)), resG Y (pre_le m k) (δ f s) = δ g (resG X k s)`.

Introduce `f g k s`. Use `haveI := hW.isLocalization_basicOpen f`. Use `der_unique f ((m.app (X.basicOpen g)).hom.comp (resG X k)) (fun s => resG Y (pre_le m k) (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_) (fun a b => ?_) (fun a => ?_) s` and prove the remaining obligations. Simplify using `only [δmul, map_add, map_mul, RingHom.comp_apply, app_res m k]`. Simplify using `only [δmul, map_mul, RingHom.comp_apply]`.

Express the relevant statement in the definitionally equal form `resG Y (pre_le m k) (δ f (resG X (X.basicOpen_le f) a)) = δ g (resG X k (resG X (X.basicOpen_le f) a))`. Rewrite using `[res_res X, δres, δres, res_res Y]`. Establish `G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(Y, m ⁻¹ᵁ W), ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) t = δ f (resG X k s)`. Introduce `W h s`. Take `⟨t, ht, -⟩` from `Y.sheaf.existsUnique_gluing' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1) (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h) (fun i => δ i.1 (resG X i.2 s)) (fun i j => by`.

Establish `e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1` using `X.basicOpen_mul _ _`. Establish `ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1` using `e.le.trans inf_le_left`. Establish `kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1` using `e.le.trans inf_le_right`. Establish `k : m ⁻¹ᵁ X.basicOpen i.1 ⊓ m ⁻¹ᵁ X.basicOpen j.1 ≤ m ⁻¹ᵁ X.basicOpen (i.1 * j.1)` using `fun y hy => e.ge hy`. Establish `e' : resG Y (pre_le m ki) (δ i.1 (resG X i.2 s)) = resG Y (pre_le m kj) (δ j.1 (resG X j.2 s))`.

Rewrite using `[compat _ _ ki, compat _ _ kj, res_res X, res_res X]`. Establish `e''` using `congrArg (resG Y k) e'`. Rewrite `e''` using `[res_res Y, res_res Y]`. Conclude with `e'')`. Conclude with `⟨t, fun f k => ht ⟨f, k⟩⟩`.

Use `choose t ht using G`. Use `⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `W h a b`. Simplify using `only [dif_pos h]`. Use `sep m hW h _ _ (fun f k => ?_)` and prove the remaining obligations.

Rewrite using `[map_add, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add, δadd]`. Introduce `W h a b`. Simplify using `only [dif_pos h]`. Use `sep m hW h _ _ (fun f k => ?_)` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul, app_res m k, app_res m k]`.

Introduce `W W' h' h a`. Simplify using `only [dif_pos h, dif_pos (h'.trans h)]`. Use `sep m hW (h'.trans h) _ _ (fun f k => ?_)` and prove the remaining obligations. Use `Eq.trans ?_ (res_res Y (pre_le m h') (pre_le m k) _).symm` and prove the remaining obligations. Rewrite using `[ht W' _ _ f k, ht W h a f (k.trans h'), res_res X]`.

Introduce `W h r`. Simplify using `only [dif_pos h]`. Use `sep m hW h _ _ (fun f k => ?_)` and prove the remaining obligations. Rewrite using `[ht W h _ f k, res_const, res_const, ← res_const p (X.basicOpen_le f), δres, hbase, res_const]`. Use function extensionality and compare the values at `a`.

Simplify using `only [dif_pos (le_refl W₀)]`. Use `sep m hW le_rfl _ _ (fun f k => ?_)` and prove the remaining obligations. Rewrite using `[ht W₀ _ _ f k, δres]`.
-/
theorem exists_locDer : ∀ (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ) (W₀ : X.Opens), IsAffineOpen W₀ → ∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDer q p m D W₀ d ∧ d W₀ = d₀ := by
  intro R _ Y X q p m D W₀ hW d₀ hadd hmul hbase
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(Y, m ⁻¹ᵁ X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧
      (∀ a b, δ (a * b) = (m.app _).hom a * δ b + (m.app _).hom b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG Y (pre_le m (X.basicOpen_le f)) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    refine der_exists f (m.app (X.basicOpen f)).hom
      (fun a => resG Y (pre_le m (X.basicOpen_le f)) (d₀ a)) (fun a b => by simp only [hadd, map_add])
      (fun a b => ?_)
    have e : ∀ a, (m.app (X.basicOpen f)).hom (algebraMap Γ(X, W₀) Γ(X, X.basicOpen f) a) =
        resG Y (pre_le m (X.basicOpen_le f)) ((m.app W₀).hom a) :=
      fun a => app_res m (X.basicOpen_le f) a
    rw [e, e]
    simp only [hmul, map_add, map_mul]
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG Y (pre_le m k) (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine der_unique f ((m.app (X.basicOpen g)).hom.comp (resG X k))
      (fun s => resG Y (pre_le m k) (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add, map_mul, RingHom.comp_apply, app_res m k]
    · simp only [δmul, map_mul, RingHom.comp_apply]
    · change resG Y (pre_le m k) (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [res_res X, δres, δres, res_res Y]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(Y, m ⁻¹ᵁ W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1)
      (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : m ⁻¹ᵁ X.basicOpen i.1 ⊓ m ⁻¹ᵁ X.basicOpen j.1 ≤ m ⁻¹ᵁ X.basicOpen (i.1 * j.1) :=
          fun y hy => e.ge hy
        have e' : resG Y (pre_le m ki) (δ i.1 (resG X i.2 s)) =
            resG Y (pre_le m kj) (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, res_res X, res_res X]
        have e'' := congrArg (resG Y k) e'
        rw [res_res Y, res_res Y] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add, δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add, map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul, app_res m k, app_res m k]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep m hW (h'.trans h) _ _ (fun f k => ?_)
    refine Eq.trans ?_ (res_res Y (pre_le m h') (pre_le m k) _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), res_res X]
  · intro W h r
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [ht W h _ f k, res_const, res_const, ← res_const p (X.basicOpen_le f), δres, hbase, res_const]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep m hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

end GlobalTheory.LocDerExt
