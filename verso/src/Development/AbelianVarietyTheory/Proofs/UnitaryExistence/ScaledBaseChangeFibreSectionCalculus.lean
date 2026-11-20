import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.SecCalc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_id, Spec.map_id]`.
-/
theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

/- English proof (translation)
Use `show ((Gx x).presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a * b))) = _`. Rewrite using `[map_mul, map_mul, map_mul]`. Both sides reduce to the same expression.
-/
theorem scal_mul' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a * b))) = _
  rw [map_mul, map_mul, map_mul]
  rfl

/- English proof (translation)
Use `show ((Gx x).presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a + b))) = _`. Rewrite using `[map_add, map_add, map_add]`. Both sides reduce to the same expression.
-/
theorem scal_add' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a + b) i = scal x a i + scal x b i := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a + b))) = _
  rw [map_add, map_add, map_add]
  rfl

/- English proof (translation)
Use `show ((Gx x).presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S 1)) = _`. Rewrite using `[map_one, map_one, map_one]`.
-/
theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x 1 i = 1 := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S 1)) = _
  rw [map_one, map_one, map_one]

/- English proof (translation)
Introduce `p hp`. Establish `hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)` using `Set.mem_iInter.1 hp`. Establish `e` using `congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs`. Use `show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)`. Use `Set.mem_iInter.2 fun k => ?_` and prove the remaining obligations.

Use `show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)`. Rewrite using `[e]`. Conclude with `hp' k`.
-/
theorem ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

/- English proof (translation)
Establish `key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ → ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤, q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top)`. Introduce and unpack `q rfl e`. Conclude with `Scheme.Hom.comp_appLE _ _ _ _ _`. Establish `M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op`. Rewrite using `[Scheme.Hom.map_appLE]`.

Establish `e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop = (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top` using `(Scheme.Hom.appLE_eq_app _).symm`. Rewrite using `[e1]`. Conclude with `(Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)`. Establish `M'` using `congrArg (fun f => f.hom (toΓ S a)) M`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at M'`.

Establish `N` using `congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N`. Use `show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) = ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))`. Rewrite using `[M']`. Use `congr 2`.

Conclude with `N.symm`.
-/
theorem scal_pull' {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm

/- English proof (translation)
The claim follows from `pullback.hom_ext (f := (Over.mk x).hom) (g := Xo.univ.t.G.hom) hf hs`.
-/
theorem pm_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Y : Scheme.{0}} (p q : Y ⟶ Gx x)
    (hs : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left) : p = q :=
  pullback.hom_ext (f := (Over.mk x).hom) (g := Xo.univ.t.G.hom) hf hs

/- English proof (translation)
Assemble the required witnesses or components as `⟨pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ) (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom) (by show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ ≫ x = pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom rw [← hx] exact pullback …`.
-/
theorem pm_exists {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) : ∃ pm : Gx x' ⟶ Gx x,
      pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ :=
  ⟨pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ)
      (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ ≫ x =
          pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition), pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, qs, qf, ha⟩ i`. Take `rfl : q = pm` from `pm_ext _ _ (qs.trans hs.symm) (qf.trans hf.symm)`. Rewrite using `[← ha i (ppx_le q hs i), map_mul, scal_pull' φ q hf]`. Introduce `h`.

Use `⟨pm, hs, hf, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[h i, map_mul, scal_pull' φ pm hf]`.
-/
theorem secBC_iff {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) :
    SecBC φ a x x' s s' ↔ ∀ i : Fin 1 → Xo.univ.t.PP.L.ι,
      s'.f i = scal x' (φ a) i * (pm.appLE _ _ (ppx_le pm hs i)).hom (s.f i) := by
  constructor
  · rintro ⟨q, qs, qf, ha⟩ i
    obtain rfl : q = pm := pm_ext _ _ (qs.trans hs.symm) (qf.trans hf.symm)
    rw [← ha i (ppx_le q hs i), map_mul, scal_pull' φ q hf]
  · intro h
    refine ⟨pm, hs, hf, fun i hi => ?_⟩
    rw [h i, map_mul, scal_pull' φ pm hf]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo S T U _ _ _ φ ψ x x' x'' hx hx'`. Take `⟨p, ps, pf⟩` from `pm_exists φ hx`. Take `⟨q, qs, qf⟩` from `pm_exists ψ hx'`. Use `⟨fun a s s' s'' h => ?_, fun a s t => ?_, fun a s s' t' h => ?_, fun a b i => ⟨scal_mul' x a b i, scal_add' x a b i, scal_one' x i⟩⟩` and prove the remaining obligations. Establish `rs : (q ≫ p) ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x'') Xo.univ.t.G).left`.

Rewrite using `[Category.assoc, ps, qs]`. Establish `rf : (q ≫ p) ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x'') Xo.univ.t.G).left ≫ spMap (ψ.comp φ)`. Rewrite using `[Category.assoc, pf, ← Category.assoc, qf, Category.assoc, spMap_comp']`. Rewrite `h` using `[secBC_iff φ a p ps pf]`. Rewrite using `[secBC_iff ψ 1 q qs qf, secBC_iff (ψ.comp φ) a (q ≫ p) rs rf]`.

Use `forall_congr' fun i => ?_` and prove the remaining obligations. Establish `e : (q ≫ p).appLE _ _ (ppx_le (q ≫ p) rs i) = p.appLE _ _ (ppx_le p ps i) ≫ q.appLE _ _ (ppx_le q qs i)` using `(Scheme.Hom.appLE_comp_appLE q p _ _ _ _ _).symm`. Rewrite using `[e, CommRingCat.hom_comp, RingHom.comp_apply, h i, map_one, scal_one' x'' i, _root_.one_mul, map_mul, scal_pull' ψ q qf]`. Both sides reduce to the same expression. Rewrite using `[secBC_iff (RingHom.id S) a (𝟙 (Gx x)) (Category.id_comp _) (by rw [spMap_id']; exact (Category.id_comp _).trans (Category.comp_id _).symm)]`.

Use `forall_congr' fun i => ?_` and prove the remaining obligations. Establish `e : ∀ hh : (PPx x).U i ≤ (𝟙 (Gx x) : Gx x ⟶ Gx x) ⁻¹ᵁ (PPx x).U i, (𝟙 (Gx x) : Gx x ⟶ Gx x).appLE _ _ hh = 𝟙 _`. Introduce `hh`. Conclude with `(Scheme.Hom.appLE_eq_app (𝟙 (Gx x) : Gx x ⟶ Gx x)).trans (Scheme.Hom.id_app _)`. Rewrite using `[e]`.

Both sides reduce to the same expression. Rewrite `h` using `[secBC_iff φ 1 p ps pf]`. Rewrite using `[secBC_iff φ a p ps pf]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[h i, map_one, scal_one' x' i, _root_.one_mul]`.
-/
theorem sec_calc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T U : Type) [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (x'' : Sp U ⟶ Xo.X), x' = spMap φ ≫ x → x'' = spMap ψ ≫ x' → (∀ (a : S) s s' s'', SecBC φ a x x' s s' → (SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'')) ∧ (∀ (a : S) (s t : LB.Sec (PPx x)), SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i) ∧ (∀ (a : S) s (s' t' : LB.Sec (PPx x')), SecBC φ 1 x x' s s' → (SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i)) ∧ (∀ (a b : S) i, scal x (a * b) i = scal x a i * scal x b i ∧ scal x (a + b) i = scal x a i + scal x b i ∧ scal x 1 i = 1) := by
  intro E _ _ _ H Dw l Xo S T U _ _ _ φ ψ x x' x'' hx hx'
  obtain ⟨p, ps, pf⟩ := pm_exists φ hx
  obtain ⟨q, qs, qf⟩ := pm_exists ψ hx'
  refine ⟨fun a s s' s'' h => ?_, fun a s t => ?_, fun a s s' t' h => ?_,
    fun a b i => ⟨scal_mul' x a b i, scal_add' x a b i, scal_one' x i⟩⟩
  · have rs : (q ≫ p) ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x'') Xo.univ.t.G).left := by
      rw [Category.assoc, ps, qs]
    have rf : (q ≫ p) ≫ (fst (Over.mk x) Xo.univ.t.G).left =
        (fst (Over.mk x'') Xo.univ.t.G).left ≫ spMap (ψ.comp φ) := by
      rw [Category.assoc, pf, ← Category.assoc, qf, Category.assoc, spMap_comp']
    rw [secBC_iff φ a p ps pf] at h
    rw [secBC_iff ψ 1 q qs qf, secBC_iff (ψ.comp φ) a (q ≫ p) rs rf]
    refine forall_congr' fun i => ?_
    have e : (q ≫ p).appLE _ _ (ppx_le (q ≫ p) rs i) = p.appLE _ _ (ppx_le p ps i) ≫ q.appLE _ _ (ppx_le q qs i) :=
      (Scheme.Hom.appLE_comp_appLE q p _ _ _ _ _).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, h i, map_one, scal_one' x'' i, _root_.one_mul, map_mul,
      scal_pull' ψ q qf]
    rfl
  · rw [secBC_iff (RingHom.id S) a (𝟙 (Gx x)) (Category.id_comp _)
      (by rw [spMap_id']; exact (Category.id_comp _).trans (Category.comp_id _).symm)]
    refine forall_congr' fun i => ?_
    have e : ∀ hh : (PPx x).U i ≤ (𝟙 (Gx x) : Gx x ⟶ Gx x) ⁻¹ᵁ (PPx x).U i,
        (𝟙 (Gx x) : Gx x ⟶ Gx x).appLE _ _ hh = 𝟙 _ := by
      intro hh
      exact (Scheme.Hom.appLE_eq_app (𝟙 (Gx x) : Gx x ⟶ Gx x)).trans (Scheme.Hom.id_app _)
    rw [e]
    rfl
  · rw [secBC_iff φ 1 p ps pf] at h
    rw [secBC_iff φ a p ps pf]
    refine forall_congr' fun i => ?_
    rw [h i, map_one, scal_one' x' i, _root_.one_mul]

end GlobalTheory.Frames.SecCalc
