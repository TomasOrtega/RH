import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelBaseChangeOverringStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models.Domination

noncomputable def toRing {T : Scheme.{0}} {R : Type} [CommRing R] (u : T ⟶ Sp R) : R →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ u.appTop).hom

/- English proof (translation)
Apply `ext_of_isAffine` to reduce the goal to its premises. Conclude with `(cancel_epi _).1 (CommRingCat.hom_ext h)`.
-/
theorem toRing_inj {T : Scheme.{0}} {R : Type} [CommRing R] {u v : T ⟶ Sp R} (h : toRing u = toRing v) : u = v := by
  apply ext_of_isAffine
  exact (cancel_epi _).1 (CommRingCat.hom_ext h)

/- English proof (translation)
Unfold `toRing`. Rewrite using `[Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem toRing_comp {T : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (u : T ⟶ Sp R') (b : R →+* R') :
    toRing (u ≫ spMap b) = (toRing u).comp b := by
  unfold toRing
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

/- English proof (translation)
Take `⟨⟨_, -⟩, -, hf⟩` from `hβ`. Take `⟨-, -, hf'⟩` from `hβ'`. Apply `toRing_inj` to reduce the goal to its premises. Establish `h'` using `congrArg toRing h`. Rewrite `h'` using `[toRing_comp, toRing_comp]`.

Rewrite using `[toRing_comp]`. Use extensionality with `x`. Use `letI := β.toAlgebra`. Establish `hinj : Function.Injective β'`. Use `letI := β'.toAlgebra`.

Conclude with `IsFractionRing.injective O' F`. Take `⟨p, q, hq, e⟩` from `IsFractionRing.div_surjective (A := O) (β' x)`. Establish `hq0 : β q ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq`. Establish `e' : β' x * β q = β p`. Rewrite using `[← e]`.

Conclude with `div_mul_cancel₀ _ hq0`. Establish `e₂ : x * b q = b p`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul]`. Use `RingHom.congr_fun hb` as an intermediate fact.

Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[this, this, e']`. Establish `hu : IsUnit (toRing w (β q))` using `(IsUnit.mk0 _ hq0).map _`. Establish `k₁ : ∀ y, toRing u (b y) = toRing w (β y)` using `RingHom.congr_fun h'`. Apply `hu.mul_right_cancel` to reduce the goal to its premises.

Rewrite using `[RingHom.comp_apply, ← map_mul, e', ← k₁, ← k₁, ← map_mul, e₂]`.
-/
theorem eq_of_overring {T : Scheme.{0}} {O O' F : Type} [CommRing O] [CommRing O'] [Field F] {β : O →+* F}
    {β' : O' →+* F} {b : O →+* O'} (hβ : IsDedFrac β) (hβ' : IsDedFrac β') (hb : β'.comp b = β) (u : T ⟶ Sp O')
    (w : T ⟶ Sp F) (h : u ≫ spMap b = w ≫ spMap β) : u = w ≫ spMap β' := by
  obtain ⟨⟨_, -⟩, -, hf⟩ := hβ
  obtain ⟨-, -, hf'⟩ := hβ'
  apply toRing_inj
  have h' := congrArg toRing h
  rw [toRing_comp, toRing_comp] at h'
  rw [toRing_comp]
  ext x
  letI := β.toAlgebra
  have hinj : Function.Injective β' := by
    letI := β'.toAlgebra
    exact IsFractionRing.injective O' F
  obtain ⟨p, q, hq, e⟩ := IsFractionRing.div_surjective (A := O) (β' x)
  have hq0 : β q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have e' : β' x * β q = β p := by
    rw [← e]; exact div_mul_cancel₀ _ hq0
  have e₂ : x * b q = b p := by
    apply hinj
    rw [map_mul]
    have := RingHom.congr_fun hb
    simp only [RingHom.comp_apply] at this
    rw [this, this, e']
  have hu : IsUnit (toRing w (β q)) := (IsUnit.mk0 _ hq0).map _
  have k₁ : ∀ y, toRing u (b y) = toRing w (β y) := RingHom.congr_fun h'
  apply hu.mul_right_cancel
  rw [RingHom.comp_apply, ← map_mul, e', ← k₁, ← k₁, ← map_mul, e₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Apply `toRing_inj` to reduce the goal to its premises. Establish `h'` using `congrArg toRing h`. Rewrite `h'` using `[toRing_comp, toRing_comp]`. Establish `k₁ : ∀ y, toRing u (β y) = toRing v (β y)` using `RingHom.congr_fun h'`. Establish `k₂ : ∀ (x : ℂ) (hx : x ∈ KA l), x ∈ RZ H S A → toRing u ⟨x, hx⟩ = toRing v ⟨x, hx⟩` using `fun x hx hx' => by`.

Establish `: β ⟨x, hx'⟩ = ⟨x, hx⟩` using `Subtype.ext (hβ _)`. Rewrite using `[← this, k₁]`. Set `K : Subfield ℂ` to `((toRing u).eqLocusField (toRing v)).map (KA l).val.toRingHom`. Establish `hK : (KA l).toSubfield ≤ K`. Establish `: KA l ≤ K.toIntermediateField (fun x => by simp)`.

Unfold `KA`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `x (rfl | rfl)`. Establish `m₁ : (1 + H.rt0) / 2 ∈ RZ H S A` using `Subring.subset_closure (by simp)`. Establish `m₂ : H.rt0 ∈ RZ H S A`.

Establish `: H.rt0 = (1 + H.rt0) / 2 + (1 + H.rt0) / 2 - 1` using `by ring`. Rewrite using `[this]`. Conclude with `sub_mem (add_mem m₁ m₁) (one_mem _)`. Conclude with `⟨(baseKA l).ρ, k₂ _ _ m₂, rfl⟩`. Conclude with `⟨(baseKA l).ζ, k₂ _ _ (Subring.subset_closure (by simp [hA])), rfl⟩`.

Conclude with `this`. Use extensionality with `x`. Take `⟨y, hy, e⟩` from `hK x.2`. Establish `: y = x` using `Subtype.ext e`. Conclude with `this ▸ hy`.
-/
theorem eq_of_RZ {T : Scheme.{0}} {l : Level H} {S A : ℕ} (hA : l.A = A) {β : RZ H S A →+* KA l}
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) (u v : T ⟶ Sp (KA l))
    (h : u ≫ spMap β = v ≫ spMap β) : u = v := by
  apply toRing_inj
  have h' := congrArg toRing h
  rw [toRing_comp, toRing_comp] at h'
  have k₁ : ∀ y, toRing u (β y) = toRing v (β y) := RingHom.congr_fun h'
  have k₂ : ∀ (x : ℂ) (hx : x ∈ KA l), x ∈ RZ H S A → toRing u ⟨x, hx⟩ = toRing v ⟨x, hx⟩ := fun x hx hx' => by
    have : β ⟨x, hx'⟩ = ⟨x, hx⟩ := Subtype.ext (hβ _)
    rw [← this, k₁]
  let K : Subfield ℂ := ((toRing u).eqLocusField (toRing v)).map (KA l).val.toRingHom
  have hK : (KA l).toSubfield ≤ K := by
    have : KA l ≤ K.toIntermediateField (fun x => by simp) := by
      unfold KA
      rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · have m₁ : (1 + H.rt0) / 2 ∈ RZ H S A := Subring.subset_closure (by simp)
        have m₂ : H.rt0 ∈ RZ H S A := by
          have : H.rt0 = (1 + H.rt0) / 2 + (1 + H.rt0) / 2 - 1 := by ring
          rw [this]
          exact sub_mem (add_mem m₁ m₁) (one_mem _)
        exact ⟨(baseKA l).ρ, k₂ _ _ m₂, rfl⟩
      · exact ⟨(baseKA l).ζ, k₂ _ _ (Subring.subset_closure (by simp [hA])), rfl⟩
    exact this
  ext x
  obtain ⟨y, hy, e⟩ := hK x.2
  have : y = x := Subtype.ext e
  exact this ▸ hy

/- English proof (translation)
Introduce `L₁ L₂ L₃ E _ _ _ H D Xo n N T l₀ l B c O O' _ _ β β' Y Y' b f t m₁ m₂ r ν k hβ hβ' hb hR hν hk hr hf hφ`. Take `⟨b₀, r₀, ν₀, hb₀, hν₀, ⟨a₀⟩⟩` from `hR`. Take `⟨ν', hν'⟩` from `LevelCover.sab_cancel Y'.m0.toSABMap Y.m0.toSABMap (𝟙 _) (Category.id_comp _)`. Establish `η₁ : ∀ x, (Y.oF.eta x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.eta x).left` using `fun x => LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by`. Rewrite using `[hν', Category.id_comp]`.

Conclude with `(Y.m0.eta x).trans (Y'.m0.eta x).symm)`. Establish `η₂ : ∀ x, (Y.oF.etaA x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.etaA x).left` using `fun x => LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by`. Rewrite using `[hν', Category.id_comp]`. Conclude with `(Y.m0.etaA x).trans (Y'.m0.etaA x).symm)`. Take `⟨ν₁, hν₁⟩` from `LevelCover.sab_comp ν' ν₀ (Category.id_comp r₀)`.

Establish `hl₁ : LevComp Y.oF (Xo l₀).univ r₀ ν₁`. Use `⟨fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₁ x), Category.id_comp, hν₀.1]`. Rewrite using `[hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₂ x), Category.id_comp, hν₀.2]`. Establish `hkb : k.comp B.β = β'.comp b₀` using `RingHom.ext fun x => Subtype.ext ((hk (B.β x)).trans ((B.β_inc x).trans (hb₀ x).symm))`.

Establish `hrB : r ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap (β'.comp b₀)`. Rewrite using `[Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc, hr, Category.assoc, ← spMap_comp, hkb]`. Establish `hrr : r ≫ (Xo l₀).s = r₀ ≫ (Xo l₀).s`. Apply `eq_of_RZ B.A_one B.β_inc` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, ← Cpt.openImmersion_comp_structure_eq_generic B.C, hrB, ← Category.assoc, ← a₀.j_comm, Category.assoc, a₀.π_over, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]`.

Establish `hred : IsReduced ((Xo l).XF c)`. Use `(Xo l).smooth` as an intermediate fact. Establish `: Smooth (Xo l).s` using `SmoothOfRelativeDimension.smooth D.dim _`. Conclude with `(GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ (pullback.snd _ _) inferInstance).1`. Take `⟨rfl, hνν⟩` from `GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r r₀ ν ν₁ hred hrr hν hl₁`.

Take `⟨ido, hid⟩` from `ObjMaps.exists_sab_id Y.oF.t`. Take `⟨C, a, hiso⟩` from `GlobalTheory.T.exists_model_baseChange_overring E H _ c.F O _ Y.oF.t β O' β' b (ofModel Y) ido hid hβ hβ' hb`. Take `⟨e, π, mu, _, e₁, e₂, hj, hm⟩ : ∃ (e : C.X ⟶ pullback Y.s (spMap b)) (π : C.X ⟶ Y.X) (mu : SABMap C.t Y.t π), IsIso e ∧ e ≫ pullback.fst _ _ = π ∧ e ≫ pullback.snd _ _ = C.s ∧ C.j ≫ π = Y.j ∧ C.m.φ ≫ mu.φ = Y.m.φ` from `⟨pullback.lift a.π C.s a.π_over, a.π, a.mu, hiso, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, a.j_comm.trans (Category.id_comp _), a.φ_comm.trans (by rw [hid]; exact Category.id_comp _)⟩`. Establish `hje : ∀ (S : Scheme.{0}) (u : S ⟶ pullback Y.s (spMap b)) (x : S ⟶ (Xo l).XF c), u ≫ pullback.fst _ _ = x ≫ Y.j → u = x ≫ C.j ≫ e` using `fun S u x h => by`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[h, Category.assoc, Category.assoc, e₁, hj]`. Rewrite using `[Category.assoc, Category.assoc, e₂, Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc]`. Apply `eq_of_overring hβ hβ' hb` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← pullback.condition, ← Category.assoc, h, Category.assoc, Category.assoc]`. Conclude with `congrArg (x ≫ ·) (Cpt.openImmersion_comp_structure_eq_generic (ofModel Y))`.

Establish `hjf : C.j ≫ e ≫ f = r ≫ B.C.j`. Rewrite using `[← Category.assoc]`. Conclude with `hf _ (by rw [Category.assoc, e₁, hj])`. Take `⟨κ, hκ⟩` from `LevelCover.sab_cancel m₁ mu e e₁`. Take `⟨κ₂, hκ₂⟩` from `LevelCover.sab_comp κ m₂ rfl`.

Establish `hm₁ : (C.m.φ ≫ κ.φ) ≫ m₁.φ = Y.m.φ`. Rewrite using `[Category.assoc, hκ, hm]`. Establish `hover : (e ≫ f) ≫ B.C.s = C.s ≫ spMap ((RingHom.id O').comp b₀)`. Take `⟨⟨_, _⟩, -, hfr⟩` from `hβ'`. Use `letI := β'.toAlgebra`.

Take `⟨-, -, -, -, -, h3, -⟩` from `GlobalTheory.genericPart_dense_proOpen O' c.F C.X _ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense`. Establish `: IsDominant C.j` using `h3`. Establish `: IsReduced C.X`. Establish `: ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x)` using `fun x => by`. Use `(C.normal x).1` as an intermediate fact.

Use `infer_instance`. Conclude with `isReduced_of_isReduced_stalk _`. Apply `ext_of_isDominant C.j` to reduce the goal to its premises. Rewrite using `[← Category.assoc, hjf, Category.assoc, hrB, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]`. Take `⟨h₀, κ₀, hh₀, -, -, hjh₀, hmh₀, -⟩` from `Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C (ofModel Y') C b₀ (RingHom.id O') (RingHom.id c.F) r ν₀ a₀ (𝟙 _) ν' (e ≫ f) κ₂ hover hβ' rfl (by rw [LevelCover.spMap_id', Category.id_comp, Category.comp_id]) (by rw [hjf, Category.id_comp]) (by rw [hκ₂, ← Categor …`.

Take `⟨h, κ', hh, hjh, hmh⟩ : ∃ (h : C.X ⟶ Y'.X) (κ' : SABMap C.t Y'.t h), h ≫ Y'.s = C.s ∧ C.j ≫ h = Y'.j ∧ C.m.φ ≫ κ'.φ = ν'.φ ≫ Y'.m.φ` from `⟨h₀, κ₀, hh₀.trans (by rw [LevelCover.spMap_id', Category.comp_id]), hjh₀.trans (Category.id_comp _), hmh₀⟩`. Take `⟨idt, hid'⟩` from `ObjMaps.exists_sab_id t`. Take `⟨κi, hκi⟩` from `LevelCover.sab_cancel κ idt (inv e) (IsIso.inv_hom_id e)`. Take `⟨m₃, hm₃⟩` from `LevelCover.sab_comp κi κ' rfl`. Establish `hκκ : κ.φ ≫ κi.φ = 𝟙 _`.

Apply `κ.cart.1.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(κ.φ ≫ κi.φ) ≫ κ.φ = 𝟙 _ ≫ κ.φ`. Rewrite using `[Category.assoc, hκi, hid', Category.comp_id, Category.id_comp]`. Establish `w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e` using `κ.cart.1.w`. Establish `w₂ : κi.φ ≫ C.t.G.hom = t.G.hom ≫ inv e` using `κi.cart.1.w`.

Rewrite using `[Category.assoc, w₂, ← Category.assoc, w₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]`. Use `⟨inv e ≫ h, t, m₁, m₃, ?_, fun u hu => ?_, fun S g g₁ g₂ q₁ q₂ q₃ => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hh, ← e₂, IsIso.inv_hom_id_assoc]`. Rewrite using `[hje _ u (𝟙 _) (by rw [hu, Category.id_comp]), Category.id_comp, Category.assoc, IsIso.hom_inv_id_assoc, hjh]`. Establish `w₀ : ν'.φ ≫ Y'.oF.t.G.hom = Y.oF.t.G.hom` using `ν'.cart.1.w.trans (Category.comp_id _)`.

Establish `s₂ : g₂ = g₁ ≫ ν'.φ`. Apply `Y'.m0.toSABMap.cart.1.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `g₂ ≫ Y'.m0.toSABMap.φ = (g₁ ≫ ν'.φ) ≫ Y'.m0.toSABMap.φ`. Rewrite using `[Category.assoc, hν', q₂]`. Rewrite using `[Category.assoc, w₀, q₃]`.

Establish `s₁ : g = g₁ ≫ C.m.φ ≫ κ.φ`. Apply `m₁.cart.1.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `g ≫ m₁.φ = (g₁ ≫ C.m.φ ≫ κ.φ) ≫ m₁.φ`. Rewrite using `[Category.assoc, hm₁, q₁]`. Establish `w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e` using `κ.cart.1.w`.

Establish `w₂ : C.m.φ ≫ C.t.G.hom = Y.oF.t.G.hom ≫ C.j` using `C.m.cart.1.w`. Establish `w₃ : m₁.φ ≫ Y.t.G.hom = t.G.hom ≫ pullback.fst _ _` using `m₁.cart.1.w`. Establish `w₄ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j` using `Y.m.cart.1.w`. Rewrite using `[hje S (g ≫ t.G.hom) (g₁ ≫ Y.oF.t.G.hom) (by`. Rewrite using `[Category.assoc, ← w₃, ← Category.assoc, q₁, Category.assoc, w₄, Category.assoc])]`.

Simplify using `only [Category.assoc]`. Rewrite using `[w₁, reassoc_of% w₂]`. Rewrite using `[s₁, s₂, hm₃]`. Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hκκ, hmh]`.
-/
theorem dominates_of_map_to_base : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model (Xo l) c β) (Y' : Model (Xo l) c β') (b : O →+* O') (f : pullback Y.s (spMap b) ⟶ B.C.X) (t : SAB H (pullback Y.s (spMap b))) (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t B.C.t f) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r) (k : KA l₀ →+* c.F), IsDedFrac β → IsDedFrac β' → β'.comp b = β → Raises B Y' → LevComp Y.oF (Xo l₀).univ r ν → IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k → r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k → (∀ g : (Xo l).XF c ⟶ pullback Y.s (spMap b), g ≫ pullback.fst _ _ = Y.j → g ≫ f = r ≫ B.C.j) → (∀ y : Y.oF.t.G.left ⟶ t.G.left, y ≫ m₁.φ = Y.m.φ → y ≫ m₂.φ = ν.φ ≫ B.C.m.φ) → Dominates Y Y' b := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N T l₀ l B c O O' _ _ β β' Y Y' b f t m₁ m₂ r ν k hβ hβ' hb hR hν hk hr hf hφ
  obtain ⟨b₀, r₀, ν₀, hb₀, hν₀, ⟨a₀⟩⟩ := hR

  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y'.m0.toSABMap Y.m0.toSABMap (𝟙 _) (Category.id_comp _)
  have η₁ : ∀ x, (Y.oF.eta x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.eta x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.eta x).trans (Y'.m0.eta x).symm)
  have η₂ : ∀ x, (Y.oF.etaA x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.etaA x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.etaA x).trans (Y'.m0.etaA x).symm)
  obtain ⟨ν₁, hν₁⟩ := LevelCover.sab_comp ν' ν₀ (Category.id_comp r₀)
  have hl₁ : LevComp Y.oF (Xo l₀).univ r₀ ν₁ := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₁ x), Category.id_comp, hν₀.1]
    · rw [hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₂ x), Category.id_comp, hν₀.2]
  have hkb : k.comp B.β = β'.comp b₀ := RingHom.ext fun x => Subtype.ext
    ((hk (B.β x)).trans ((B.β_inc x).trans (hb₀ x).symm))
  have hrB : r ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap (β'.comp b₀) := by
    rw [Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc, hr, Category.assoc, ← spMap_comp, hkb]
  have hrr : r ≫ (Xo l₀).s = r₀ ≫ (Xo l₀).s := by
    apply eq_of_RZ B.A_one B.β_inc
    rw [Category.assoc, Category.assoc, ← Cpt.openImmersion_comp_structure_eq_generic B.C, hrB, ← Category.assoc, ← a₀.j_comm, Category.assoc,
      a₀.π_over, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]
  have hred : IsReduced ((Xo l).XF c) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ (pullback.snd _ _)
      inferInstance).1
  obtain ⟨rfl, hνν⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r r₀ ν ν₁ hred hrr hν hl₁

  obtain ⟨ido, hid⟩ := ObjMaps.exists_sab_id Y.oF.t
  obtain ⟨C, a, hiso⟩ := GlobalTheory.T.exists_model_baseChange_overring E H _ c.F O _ Y.oF.t β O' β' b (ofModel Y) ido hid hβ hβ' hb
  obtain ⟨e, π, mu, _, e₁, e₂, hj, hm⟩ : ∃ (e : C.X ⟶ pullback Y.s (spMap b)) (π : C.X ⟶ Y.X) (mu : SABMap C.t Y.t π),
      IsIso e ∧ e ≫ pullback.fst _ _ = π ∧ e ≫ pullback.snd _ _ = C.s ∧ C.j ≫ π = Y.j ∧ C.m.φ ≫ mu.φ = Y.m.φ :=
    ⟨pullback.lift a.π C.s a.π_over, a.π, a.mu, hiso, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      a.j_comm.trans (Category.id_comp _), a.φ_comm.trans (by rw [hid]; exact Category.id_comp _)⟩
  have hje : ∀ (S : Scheme.{0}) (u : S ⟶ pullback Y.s (spMap b)) (x : S ⟶ (Xo l).XF c),
      u ≫ pullback.fst _ _ = x ≫ Y.j → u = x ≫ C.j ≫ e := fun S u x h => by
    apply pullback.hom_ext
    · rw [h, Category.assoc, Category.assoc, e₁, hj]
    · rw [Category.assoc, Category.assoc, e₂, Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc]
      apply eq_of_overring hβ hβ' hb
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, h, Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) (Cpt.openImmersion_comp_structure_eq_generic (ofModel Y))
  have hjf : C.j ≫ e ≫ f = r ≫ B.C.j := by
    rw [← Category.assoc]
    exact hf _ (by rw [Category.assoc, e₁, hj])
  obtain ⟨κ, hκ⟩ := LevelCover.sab_cancel m₁ mu e e₁
  obtain ⟨κ₂, hκ₂⟩ := LevelCover.sab_comp κ m₂ rfl
  have hm₁ : (C.m.φ ≫ κ.φ) ≫ m₁.φ = Y.m.φ := by
    rw [Category.assoc, hκ, hm]
  have hover : (e ≫ f) ≫ B.C.s = C.s ≫ spMap ((RingHom.id O').comp b₀) := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ'
    letI := β'.toAlgebra
    obtain ⟨-, -, -, -, -, h3, -⟩ :=
      GlobalTheory.genericPart_dense_proOpen O' c.F C.X _ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
    have : IsDominant C.j := h3
    have : IsReduced C.X := by
      have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
        have := (C.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk _
    apply ext_of_isDominant C.j
    rw [← Category.assoc, hjf, Category.assoc, hrB, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]
  obtain ⟨h₀, κ₀, hh₀, -, -, hjh₀, hmh₀, -⟩ := Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C
    (ofModel Y') C b₀ (RingHom.id O') (RingHom.id c.F) r ν₀ a₀ (𝟙 _) ν' (e ≫ f) κ₂ hover hβ' rfl
    (by rw [LevelCover.spMap_id', Category.id_comp, Category.comp_id]) (by rw [hjf, Category.id_comp])
    (by rw [hκ₂, ← Category.assoc, hφ _ hm₁, hνν, hν₁, Category.assoc])
  obtain ⟨h, κ', hh, hjh, hmh⟩ : ∃ (h : C.X ⟶ Y'.X) (κ' : SABMap C.t Y'.t h), h ≫ Y'.s = C.s ∧ C.j ≫ h = Y'.j ∧
      C.m.φ ≫ κ'.φ = ν'.φ ≫ Y'.m.φ :=
    ⟨h₀, κ₀, hh₀.trans (by rw [LevelCover.spMap_id', Category.comp_id]), hjh₀.trans (Category.id_comp _), hmh₀⟩
  obtain ⟨idt, hid'⟩ := ObjMaps.exists_sab_id t
  obtain ⟨κi, hκi⟩ := LevelCover.sab_cancel κ idt (inv e) (IsIso.inv_hom_id e)
  obtain ⟨m₃, hm₃⟩ := LevelCover.sab_comp κi κ' rfl
  have hκκ : κ.φ ≫ κi.φ = 𝟙 _ := by
    apply κ.cart.1.hom_ext
    · change (κ.φ ≫ κi.φ) ≫ κ.φ = 𝟙 _ ≫ κ.φ
      rw [Category.assoc, hκi, hid', Category.comp_id, Category.id_comp]
    · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
      have w₂ : κi.φ ≫ C.t.G.hom = t.G.hom ≫ inv e := κi.cart.1.w
      rw [Category.assoc, w₂, ← Category.assoc, w₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        Category.id_comp]
  refine ⟨inv e ≫ h, t, m₁, m₃, ?_, fun u hu => ?_, fun S g g₁ g₂ q₁ q₂ q₃ => ?_⟩
  · rw [Category.assoc, hh, ← e₂, IsIso.inv_hom_id_assoc]
  · rw [hje _ u (𝟙 _) (by rw [hu, Category.id_comp]), Category.id_comp, Category.assoc, IsIso.hom_inv_id_assoc, hjh]
  · have w₀ : ν'.φ ≫ Y'.oF.t.G.hom = Y.oF.t.G.hom := ν'.cart.1.w.trans (Category.comp_id _)
    have s₂ : g₂ = g₁ ≫ ν'.φ := by
      apply Y'.m0.toSABMap.cart.1.hom_ext
      · change g₂ ≫ Y'.m0.toSABMap.φ = (g₁ ≫ ν'.φ) ≫ Y'.m0.toSABMap.φ
        rw [Category.assoc, hν', q₂]
      · rw [Category.assoc, w₀, q₃]
    have s₁ : g = g₁ ≫ C.m.φ ≫ κ.φ := by
      apply m₁.cart.1.hom_ext
      · change g ≫ m₁.φ = (g₁ ≫ C.m.φ ≫ κ.φ) ≫ m₁.φ
        rw [Category.assoc, hm₁, q₁]
      · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
        have w₂ : C.m.φ ≫ C.t.G.hom = Y.oF.t.G.hom ≫ C.j := C.m.cart.1.w
        have w₃ : m₁.φ ≫ Y.t.G.hom = t.G.hom ≫ pullback.fst _ _ := m₁.cart.1.w
        have w₄ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
        rw [hje S (g ≫ t.G.hom) (g₁ ≫ Y.oF.t.G.hom) (by
          rw [Category.assoc, ← w₃, ← Category.assoc, q₁, Category.assoc, w₄, Category.assoc])]
        simp only [Category.assoc]
        rw [w₁, reassoc_of% w₂]
    rw [s₁, s₂, hm₃]
    simp only [Category.assoc]
    rw [reassoc_of% hκκ, hmh]

end GlobalTheory.Models.Domination
