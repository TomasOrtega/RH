import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevQuot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

/- English proof (translation)
Establish `hr : IsIntegral ℚ H.rt0`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[H.sqrt_neg_disc_sq]`. Establish `: IsIntegral ℚ (algebraMap ℚ ℂ (-(H.d : ℚ)))` using `isIntegral_algebraMap`. Simplify using `using this`.

Establish `hz : IsIntegral ℚ (zeta l.A)` using `((Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').isIntegral l.A_pos).tower_top`. Use `show FiniteDimensional ℚ (IntermediateField.adjoin ℚ {H.rt0, zeta l.A})`. Use `IntermediateField.finiteDimensional_adjoin ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`. Conclude with `hr`.

Conclude with `hz`.
-/
theorem finiteDimensional_field (l : Level H) : FiniteDimensional ℚ (KA l) := by
  have hr : IsIntegral ℚ H.rt0 := by
    refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    have : IsIntegral ℚ (algebraMap ℚ ℂ (-(H.d : ℚ))) := isIntegral_algebraMap
    simpa using this
  have hz : IsIntegral ℚ (zeta l.A) :=
    ((Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').isIntegral l.A_pos).tower_top
  show FiniteDimensional ℚ (IntermediateField.adjoin ℚ {H.rt0, zeta l.A})
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x (rfl | rfl)
  · exact hr
  · exact hz

/- English proof (translation)
Establish `: CharZero k` using `(RingHom.charZero_iff β.injective).1 inferInstance`. Establish `key : β.toRatAlgHom = β'.toRatAlgHom`. Use `IntermediateField.adjoin_algHom_ext ℚ (s := {H.rt0, zeta l.A}) ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`. Conclude with `h₁`.

Conclude with `h₂`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Conclude with `DFunLike.congr_fun key x`.
-/
theorem field_hom_ext (l : Level H) {k : Type} [Field k] (β β' : KA l →+* k)
    (h₁ : β (baseKA l).ρ = β' (baseKA l).ρ) (h₂ : β (baseKA l).ζ = β' (baseKA l).ζ) : β = β' := by
  have : CharZero k := (RingHom.charZero_iff β.injective).1 inferInstance
  have key : β.toRatAlgHom = β'.toRatAlgHom := by
    refine IntermediateField.adjoin_algHom_ext ℚ (s := {H.rt0, zeta l.A}) ?_
    rintro x (rfl | rfl)
    · exact h₁
    · exact h₂
  refine RingHom.ext fun x => ?_
  exact DFunLike.congr_fun key x

/- English proof (translation)
Use `finiteDimensional_field l` as an intermediate fact. Use `Finite.of_injective (fun σ : KA l ≃+* KA l => (σ : KA l →+* KA l).toRatAlgHom) ?_` and prove the remaining obligations. Introduce `a b hab`. Use `RingEquiv.ext fun x => ?_` and prove the remaining obligations. Conclude with `DFunLike.congr_fun hab x`.
-/
theorem finite_fieldAut (l : Level H) : Finite (KA l ≃+* KA l) := by
  have := finiteDimensional_field l
  refine Finite.of_injective (fun σ : KA l ≃+* KA l => (σ : KA l →+* KA l).toRatAlgHom) ?_
  intro a b hab
  refine RingEquiv.ext fun x => ?_
  exact DFunLike.congr_fun hab x

/- English proof (translation)
Use `finiteDimensional_field l` as an intermediate fact. Establish `: CharZero k` using `(RingHom.charZero_iff β.injective).1 inferInstance`. Establish `: NeZero l.A` using `⟨l.A_pos.ne'⟩`. Establish `hp : IsPrimitiveRoot (β (baseKA l).ζ) l.A` using `(baseKA l).ζ_prim.map_of_injective β.injective`. Establish `hA : β' (baseKA l).ζ ^ l.A = 1` using `by rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one]`.

Take `⟨i, -, hi⟩` from `hp.eq_pow_of_pow_eq_one hA`. Set `βQ` to `β.toRatAlgHom`. Set `β'Q` to `β'.toRatAlgHom`. Establish `hle : IntermediateField.adjoin ℚ ({H.rt0, zeta l.A} : Set ℂ) ≤ (βQ.fieldRange.comap β'Q).map (KA l).val`. Rewrite using `[IntermediateField.adjoin_le_iff]`.

Introduce and unpack `y (rfl | rfl)`. Conclude with `⟨(baseKA l).ρ, ⟨(baseKA l).ρ, h₁⟩, rfl⟩`. Conclude with `⟨(baseKA l).ζ, ⟨(baseKA l).ζ ^ i, by simpa [βQ, β'Q] using hi⟩, rfl⟩`. Establish `hmem : ∀ x, β'Q x ∈ βQ.fieldRange`. Introduce `x`.

Take `⟨z, hz, hzx⟩` from `hle x.2`. Take `rfl : z = x` from `Subtype.ext hzx`. Conclude with `hz`. Set `e` to `AlgEquiv.ofInjectiveField βQ`. Set `τ : KA l →ₐ[ℚ] βQ.fieldRange` to `β'Q.codRestrict βQ.fieldRange.toSubalgebra hmem`.

Set `σQ : KA l →ₐ[ℚ] KA l` to `e.symm.toAlgHom.comp τ`. Establish `hσ : ∀ x, β (σQ x) = β' x`. Introduce `x`. Use `congrArg Subtype.val (e.apply_symm_apply (τ x))` as an intermediate fact. Conclude with `this`.

Set `σ` to `(AlgEquiv.ofBijective σQ (AlgHom.bijective σQ)).toRingEquiv`. Use `⟨σ, ?_, ?_⟩` and prove the remaining obligations. Apply `β.injective` to reduce the goal to its premises. Conclude with `(hσ _).trans h₁.symm`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations.

Conclude with `hσ x`.
-/
theorem exists_fieldAut (l : Level H) {k : Type} [Field k] (β β' : KA l →+* k)
    (h₁ : β (baseKA l).ρ = β' (baseKA l).ρ) :
    ∃ σ : KA l ≃+* KA l, σ (baseKA l).ρ = (baseKA l).ρ ∧ β.comp σ.toRingHom = β' := by
  have := finiteDimensional_field l
  have : CharZero k := (RingHom.charZero_iff β.injective).1 inferInstance
  have : NeZero l.A := ⟨l.A_pos.ne'⟩
  have hp : IsPrimitiveRoot (β (baseKA l).ζ) l.A := (baseKA l).ζ_prim.map_of_injective β.injective
  have hA : β' (baseKA l).ζ ^ l.A = 1 := by rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one hA
  let βQ := β.toRatAlgHom
  let β'Q := β'.toRatAlgHom
  have hle : IntermediateField.adjoin ℚ ({H.rt0, zeta l.A} : Set ℂ) ≤
      (βQ.fieldRange.comap β'Q).map (KA l).val := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl)
    · exact ⟨(baseKA l).ρ, ⟨(baseKA l).ρ, h₁⟩, rfl⟩
    · exact ⟨(baseKA l).ζ, ⟨(baseKA l).ζ ^ i, by simpa [βQ, β'Q] using hi⟩, rfl⟩
  have hmem : ∀ x, β'Q x ∈ βQ.fieldRange := by
    intro x
    obtain ⟨z, hz, hzx⟩ := hle x.2
    obtain rfl : z = x := Subtype.ext hzx
    exact hz
  let e := AlgEquiv.ofInjectiveField βQ
  let τ : KA l →ₐ[ℚ] βQ.fieldRange := β'Q.codRestrict βQ.fieldRange.toSubalgebra hmem
  let σQ : KA l →ₐ[ℚ] KA l := e.symm.toAlgHom.comp τ
  have hσ : ∀ x, β (σQ x) = β' x := by
    intro x
    have := congrArg Subtype.val (e.apply_symm_apply (τ x))
    exact this
  let σ := (AlgEquiv.ofBijective σQ (AlgHom.bijective σQ)).toRingEquiv
  refine ⟨σ, ?_, ?_⟩
  · apply β.injective
    exact (hσ _).trans h₁.symm
  · refine RingHom.ext fun x => ?_
    exact hσ x

variable {l : Level H}

/- English proof (translation)
Establish `: SmoothOfRelativeDimension D.dim Xo.s` using `Xo.smooth`. Conclude with `(GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field (KA l) Xo.X Xo.s (SmoothOfRelativeDimension.smooth D.dim Xo.s)).1`.
-/
theorem isReduced_moduli (Xo : Moduli D l) : IsReduced Xo.X := by
  have : SmoothOfRelativeDimension D.dim Xo.s := Xo.smooth
  exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field (KA l) Xo.X Xo.s
    (SmoothOfRelativeDimension.smooth D.dim Xo.s)).1

def SemiTwist (Xo : Moduli D l) (f : Xo.X ⟶ Xo.X) (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) (g : D.La → D.La)
    (σ : KA l →+* KA l) : Prop :=
  f ≫ Xo.s = Xo.s ≫ spMap σ ∧ (∀ a, (Xo.univ.eta a).left ≫ φ = f ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo.univ.etaA (g a)).left ≫ φ = f ≫ (Xo.univ.etaA a).left

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Take `⟨h1', h2', h3'⟩` from `h'`. Use `⟨?_, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h1', ← Category.assoc, h1, Category.assoc, GlobalTheory.LevCover.spMap_comp'']`. Rewrite using `[← Category.assoc, h2, Category.assoc, h2', Category.assoc]`.

Rewrite using `[Function.comp_apply, ← Category.assoc, h3, Category.assoc, h3', Category.assoc]`.
-/
theorem SemiTwist.comp {Xo : Moduli D l} {f f' φ φ' g g' σ σ'} (h : SemiTwist Xo f φ g σ)
    (h' : SemiTwist Xo f' φ' g' σ') : SemiTwist Xo (f ≫ f') (φ ≫ φ') (g ∘ g') (σ.comp σ') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, fun a => ?_, fun a => ?_⟩
  · rw [Category.assoc, h1', ← Category.assoc, h1, Category.assoc, GlobalTheory.LevCover.spMap_comp'']
  · rw [← Category.assoc, h2, Category.assoc, h2', Category.assoc]
  · rw [Function.comp_apply, ← Category.assoc, h3, Category.assoc, h3', Category.assoc]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Substitute `hσ` using the available equality. Establish `hs : f ≫ Xo.s = Xo.s` using `by rw [h1, GlobalTheory.LevelCover.spMap_id', Category.comp_id]`. Take `⟨u, -, hu⟩` from `Xo.rep Xo.X Xo.s (isReduced_moduli Xo) Xo.univ`. Establish `hid : (GlobalTheory.LevelTwist.sabMapId Xo.univ.t).φ = 𝟙 _` using `GlobalTheory.LevelTwist.sabMapId_φ _`.

Establish `e1` using `hu f ⟨hs, ⟨⟨m, fun a => h2 a, fun a => by`. Use `h3 a` as an intermediate fact. Rewrite using `[hg a] at this⟩⟩⟩` and apply the resulting hypothesis. Establish `e2` using `hu (𝟙 _) ⟨Category.id_comp _, ⟨⟨GlobalTheory.LevelTwist.sabMapId Xo.univ.t, fun a => by`. Express the relevant statement in the definitionally equal form `_ ≫ (GlobalTheory.LevelTwist.sabMapId Xo.univ.t).φ = _`.

Rewrite using `[hid, Category.comp_id, Category.id_comp], fun a => by`. Express the relevant statement in the definitionally equal form `_ ≫ (GlobalTheory.LevelTwist.sabMapId Xo.univ.t).φ = _`. Rewrite using `[hid, Category.comp_id, Category.id_comp]⟩⟩⟩`. Conclude with `e1.trans e2.symm`.
-/
theorem SemiTwist.eq_id {Xo : Moduli D l} {f g σ} (m : SABMap Xo.univ.t Xo.univ.t f) (h : SemiTwist Xo f m.φ g σ)
    (hσ : σ = RingHom.id _) (hg : ∀ a, Xo.univ.etaA (g a) = Xo.univ.etaA a) : f = 𝟙 _ := by
  obtain ⟨h1, h2, h3⟩ := h
  subst hσ
  have hs : f ≫ Xo.s = Xo.s := by rw [h1, GlobalTheory.LevelCover.spMap_id', Category.comp_id]
  obtain ⟨u, -, hu⟩ := Xo.rep Xo.X Xo.s (isReduced_moduli Xo) Xo.univ
  have hid : (GlobalTheory.LevelTwist.sabMapId Xo.univ.t).φ = 𝟙 _ := GlobalTheory.LevelTwist.sabMapId_φ _
  have e1 := hu f ⟨hs, ⟨⟨m, fun a => h2 a, fun a => by
    have := h3 a
    rwa [hg a] at this⟩⟩⟩
  have e2 := hu (𝟙 _) ⟨Category.id_comp _, ⟨⟨GlobalTheory.LevelTwist.sabMapId Xo.univ.t, fun a => by
      change _ ≫ (GlobalTheory.LevelTwist.sabMapId Xo.univ.t).φ = _
      rw [hid, Category.comp_id, Category.id_comp], fun a => by
      change _ ≫ (GlobalTheory.LevelTwist.sabMapId Xo.univ.t).φ = _
      rw [hid, Category.comp_id, Category.id_comp]⟩⟩⟩
  exact e1.trans e2.symm

/- English proof (translation)
Take `⟨a₀, b₀, hab⟩` from `GlobalTheory.SimAlg.exists_form_eq_one hpq`. Establish `hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)`. Introduce `n m hn hm`. Use `⟨GlobalTheory.SimAlg.dvd_mult_tower g hn hm hab, ?_⟩` and prove the remaining obligations. Take `⟨h, hh⟩` from `g.inv n hn`.

Take `⟨c, hc⟩` from `GlobalTheory.SimAlg.dvd_mult_inv g hn hab h (fun x => (hh x).2)`. Conclude with `⟨D.EF (h a₀) (h b₀), -c, by linear_combination hc⟩`. Set `b' : Base l (KA l)` to `{ unit := (baseKA l).unit ρ := (baseKA l).ρ ρ_sq := (baseKA l).ρ_sq ζ := σ (baseKA l).ζ ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }`. Set `o' : Obj D l b' Xo.s` to `{ t := Xo.univ.t proper := Xo.univ.proper ample := Xo.univ.ample ktriv := Xo.univ.ktriv eta := fun a => Xo.univ.eta (g.f l.M a) eta_add := fun a c => by simp only [map_add, Xo.univ.eta_add] eta_ker := fun a ha => Xo.univ.eta_ker _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha) …`. Take `⟨hdet, I, hI1, hI2, hI3⟩` from `Xo.univ.geom k x β hx`.

Use `⟨hdet, GlobalTheory.LevelTwist.twist I g hν, ?_, fun a => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LevelTwist.twist_ζ, Units.val_zpow_eq_zpow_val, hI1, ← map_zpow₀]`. Conclude with `congrArg β hζ.symm`. Rewrite using `[GlobalTheory.LevelTwist.twist_ev]`. Conclude with `hI2 _`.

Rewrite using `[GlobalTheory.LevelTwist.twist_ev]`. Conclude with `hI3 _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha) }`. Set `o` to `GlobalTheory.objRestrictBase σ o' hρ rfl`. Take `⟨f, ⟨hf, ⟨p⟩⟩, -⟩` from `Xo.rep Xo.X (Xo.s ≫ spMap σ) (isReduced_moduli Xo) o`. Use `⟨f, p.toSABMap, hf, fun a => ?_, fun a => p.etaA a⟩` and prove the remaining obligations.

Establish `e` using `GlobalTheory.Moduli.LevelAction.eta_congr Xo.univ (hg a)`. Use `p.eta a` as an intermediate fact. Express the relevant statement in the definitionally equal form `(Xo.univ.eta (g.f l.M a)).left ≫ _ = _ at this`. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem exists_semiTwist (hpq : 1 ≤ D.p + D.q) (Xo : Moduli D l) (σ : KA l →+* KA l) (g : Sim D)
    (hρ : σ (baseKA l).ρ = (baseKA l).ρ) (hζ : σ (baseKA l).ζ = (baseKA l).ζ ^ g.ν l.A)
    (hg : ∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ (f : Xo.X ⟶ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t f), SemiTwist Xo f m.φ (g.f l.A) σ := by
  obtain ⟨a₀, b₀, hab⟩ := GlobalTheory.SimAlg.exists_form_eq_one hpq
  have hν : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ) := by
    intro n m hn hm
    refine ⟨GlobalTheory.SimAlg.dvd_mult_tower g hn hm hab, ?_⟩
    obtain ⟨h, hh⟩ := g.inv n hn
    obtain ⟨c, hc⟩ := GlobalTheory.SimAlg.dvd_mult_inv g hn hab h (fun x => (hh x).2)
    exact ⟨D.EF (h a₀) (h b₀), -c, by linear_combination hc⟩
  let b' : Base l (KA l) :=
    { unit := (baseKA l).unit
      ρ := (baseKA l).ρ
      ρ_sq := (baseKA l).ρ_sq
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  let o' : Obj D l b' Xo.s :=
    { t := Xo.univ.t
      proper := Xo.univ.proper
      ample := Xo.univ.ample
      ktriv := Xo.univ.ktriv
      eta := fun a => Xo.univ.eta (g.f l.M a)
      eta_add := fun a c => by simp only [map_add, Xo.univ.eta_add]
      eta_ker := fun a ha => Xo.univ.eta_ker _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha)
      etaA := fun a => Xo.univ.etaA (g.f l.A a)
      etaA_add := fun a c => by simp only [map_add, Xo.univ.etaA_add]
      etaA_ker := fun a => by simp only [map_nsmul, Xo.univ.etaA_ker]
      geom := fun k _ _ x β hx => by
        obtain ⟨hdet, I, hI1, hI2, hI3⟩ := Xo.univ.geom k x β hx
        refine ⟨hdet, GlobalTheory.LevelTwist.twist I g hν, ?_, fun a => ?_, fun a ha => ?_⟩
        · rw [GlobalTheory.LevelTwist.twist_ζ, Units.val_zpow_eq_zpow_val, hI1, ← map_zpow₀]
          exact congrArg β hζ.symm
        · rw [GlobalTheory.LevelTwist.twist_ev]
          exact hI2 _
        · rw [GlobalTheory.LevelTwist.twist_ev]
          exact hI3 _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha) }
  let o := GlobalTheory.objRestrictBase σ o' hρ rfl
  obtain ⟨f, ⟨hf, ⟨p⟩⟩, -⟩ := Xo.rep Xo.X (Xo.s ≫ spMap σ) (isReduced_moduli Xo) o
  refine ⟨f, p.toSABMap, hf, fun a => ?_, fun a => p.etaA a⟩
  have e := GlobalTheory.Moduli.LevelAction.eta_congr Xo.univ (hg a)
  have := p.eta a
  change (Xo.univ.eta (g.f l.M a)).left ≫ _ = _ at this
  rw [e] at this
  exact this

/- English proof (translation)
Take `⟨a₀, b₀, hab⟩` from `GlobalTheory.SimAlg.exists_form_eq_one hpq`. Establish `hA0 : NeZero l.A` using `⟨l.A_pos.ne'⟩`. Establish `hprim` using `(baseKA l).ζ_prim`. Establish `hz : (baseKA l).ζ ≠ 0` using `hprim.ne_zero l.A_pos.ne'`. Establish `hcong : ∀ a b : ℤ, (l.A : ℤ) ∣ a - b → (baseKA l).ζ ^ a = (baseKA l).ζ ^ b`.

Introduce and unpack `a b ⟨k, hk⟩`. Rewrite using `[show a = b + l.A * k by linarith, zpow_add₀ hz, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow, _root_.mul_one]`. Establish `hσp : IsPrimitiveRoot (σ (baseKA l).ζ) l.A` using `hprim.map_of_injective σ.injective`. Take `⟨i, -, hi⟩` from `hprim.eq_pow_of_pow_eq_one hσp.pow_eq_one`. Establish `hcop : i.Coprime l.A` using `(hprim.pow_iff_coprime l.A_pos i).1 (hi ▸ hσp)`.

Establish `hMpos : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Establish `hN : 0 < l.M * l.A` using `Nat.mul_pos hMpos l.A_pos`. Establish `hN0 : NeZero (l.M * l.A)` using `⟨hN.ne'⟩`. Take `⟨v, hv⟩` from `ZMod.unitsMap_surjective (m := l.M * l.A) (n := l.A) (dvd_mul_left _ _) (ZMod.unitOfCoprime i hcop)`. Take `⟨ν, hνdef⟩ : ∃ ν : ℤ, ν = ((v : ZMod (l.M * l.A)).val : ℤ)` from `⟨_, rfl⟩`.

Establish `hνN : IsCoprime ν ((l.M * l.A : ℕ) : ℤ)`. Rewrite using `[hνdef]`. Conclude with `Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime v)`. Establish `hνi : (l.A : ℤ) ∣ ν - i`. Establish `h2` using `congrArg (fun w : (ZMod l.A)ˣ => (w : ZMod l.A)) hv`.

Simplify using `only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_eq_val] at h2`. Establish `h3 : ((i : ℤ) : ZMod l.A) = ((ν : ℤ) : ZMod l.A)`. Rewrite using `[hνdef]`. Use `push_cast`. Conclude with `h2.symm`.

Conclude with `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h3`. Take `⟨c, hcN, hcM, -⟩` from `GlobalTheory.SimMult.exists_scalar H l₀ (l.M * l.A) hN (by rw [← hM]; exact dvd_mul_right _ _) (by rw [hA]; exact one_dvd _) ν hνN (by rw [hA, Nat.cast_one]; exact one_dvd _)`. Set `fc : D.La →ₗ[𝓞 E] D.La` to `c • LinearMap.id`. Establish `hfc : ∀ a b, ((l.M * l.A : ℕ) : ℤ) ∣ D.EF (fc a) (fc b) - ν * D.EF a b`. Introduce `a b`.

Take `⟨t, ht⟩` from `hcN`. Establish `hc' : H.bar c * c = (ν : 𝓞 E) + ((l.M * l.A : ℕ) : 𝓞 E) * t` using `by linear_combination ht`. Use `⟨D.EF a (t • b), ?_⟩` and prove the remaining obligations. Simplify using `only [fc, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[D.adj, smul_smul, hc', add_smul, mul_smul]`.

Simplify using `only [map_add, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, map_zsmul, map_nsmul, zsmul_eq_mul, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨g, hgl⟩` from `GlobalTheory.exists_sim_lift E H D (l.M * l.A) fc ν hN hνN hfc`. Establish `hgA : (l.A : ℤ) ∣ g.ν l.A - i`.

Establish `t1` using `GlobalTheory.SimAlg.dvd_mult_tower g l.A_pos hMpos hab`. Rewrite `t1` using `[Nat.mul_comm]`. Establish `t2 : (l.A : ℤ) ∣ g.ν (l.M * l.A) - ν` using `(Int.natCast_dvd_natCast.2 (Nat.dvd_mul_left l.A l.M)).trans hgl.2`. Use `dvd_add (dvd_add (dvd_neg.2 t1) t2) hνi` as an intermediate fact. Rewrite using `[show g.ν l.A - (i : ℤ) = -(g.ν (l.M * l.A) - g.ν l.A) + (g.ν (l.M * l.A) - ν) + (ν - i) by ring]`.

Conclude with `this`. Establish `hζ : σ.toRingHom (baseKA l).ζ = (baseKA l).ζ ^ g.ν l.A` using `by show σ (baseKA l).ζ = _`. Rewrite using `[← hi, ← zpow_natCast]`. Conclude with `hcong _ _ (by rw [← neg_sub]; exact dvd_neg.2 hgA)`. Establish `hgM : ∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)`.

Introduce `a`. Establish `t1` using `GlobalTheory.Moduli.LevelAction.mem_of_modN (D := D) l (GlobalTheory.SimAlg.modN_neg (g.tower l.M l.A hMpos l.A_pos a))`. Establish `t2` using `GlobalTheory.Moduli.LevelAction.mem_of_modN (D := D) l (GlobalTheory.SimAlg.modN_of_mul (hgl.1 a))`. Establish `t3 : (c - 1) • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)` using `Submodule.smul_mem_smul (by rw [hMb]; exact hcM) Submodule.mem_top`. Use `add_mem (add_mem t1 t2) t3` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [fc, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Take `⟨f, m, h⟩` from `exists_semiTwist hpq Xo σ.toRingHom g hρ hζ hgM`. Take `⟨g', hg'⟩` from `GlobalTheory.SimAlg.exists_inv g hab`.

Establish `hρ' : σ.symm.toRingHom (baseKA l).ρ = (baseKA l).ρ` using `σ.injective (by rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, hρ])`. Establish `hζ' : σ.symm.toRingHom (baseKA l).ζ = (baseKA l).ζ ^ g'.ν l.A`. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_zpow₀, ← RingEquiv.coe_toRingHom, ← RingEquiv.toRingHom_eq_coe, hζ, ← zpow_mul, ← zpow_one (baseKA l).ζ, ← zpow_mul, _root_.one_mul]`. Conclude with `hcong _ _ (by rw [← neg_sub]; exact dvd_neg.2 (hg' l.A l.A_pos).2)`.

Establish `hg'M : ∀ a, g'.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)`. Introduce `a`. Use `sub_mem (GlobalTheory.Moduli.LevelAction.mem_of_modN (D := D) l ((hg' l.M hMpos).1 a).2) (hgM (g'.f l.M a))` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis. Take `⟨f', m', h'⟩` from `exists_semiTwist hpq Xo σ.symm.toRingHom g' hρ' hζ' hg'M`.

Take `⟨n₁, hn₁⟩` from `GlobalTheory.Moduli.LevelAction.exists_comp_sabMap m m' (rfl : f ≫ f' = f ≫ f')`. Take `⟨n₂, hn₂⟩` from `GlobalTheory.Moduli.LevelAction.exists_comp_sabMap m' m (rfl : f' ≫ f = f' ≫ f)`. Establish `e₁ : f ≫ f' = 𝟙 _`. Use `SemiTwist.eq_id n₁ (by rw [hn₁]; exact SemiTwist.comp h h') ?_ fun a => ?_` and prove the remaining obligations. Conclude with `RingHom.ext fun x => by simp`.

Conclude with `GlobalTheory.Moduli.LevelAction.etaA_congr Xo.univ ((hg' l.A l.A_pos).1 a).2`. Establish `e₂ : f' ≫ f = 𝟙 _`. Use `SemiTwist.eq_id n₂ (by rw [hn₂]; exact SemiTwist.comp h' h) ?_ fun a => ?_` and prove the remaining obligations. Conclude with `RingHom.ext fun x => by simp`. Conclude with `GlobalTheory.Moduli.LevelAction.etaA_congr Xo.univ ((hg' l.A l.A_pos).1 a).1`.

Conclude with `⟨⟨f, f', e₁, e₂⟩, m, g.f l.A, h⟩`.
-/
theorem exists_semiTwist_iso (hpq : 1 ≤ D.p + D.q) (l₀ : Level H) (hA : l₀.A = 1) (hM : l.M = l₀.M)
    (hMb : l.Mb = l₀.Mb) (Xo : Moduli D l) (σ : KA l ≃+* KA l) (hρ : σ (baseKA l).ρ = (baseKA l).ρ) :
    ∃ (ρ : Xo.X ≅ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t ρ.hom) (g : D.La →ₗ[𝓞 E] D.La),
      SemiTwist Xo ρ.hom m.φ g σ.toRingHom := by
  obtain ⟨a₀, b₀, hab⟩ := GlobalTheory.SimAlg.exists_form_eq_one hpq
  have hA0 : NeZero l.A := ⟨l.A_pos.ne'⟩
  have hprim := (baseKA l).ζ_prim
  have hz : (baseKA l).ζ ≠ 0 := hprim.ne_zero l.A_pos.ne'
  have hcong : ∀ a b : ℤ, (l.A : ℤ) ∣ a - b → (baseKA l).ζ ^ a = (baseKA l).ζ ^ b := by
    rintro a b ⟨k, hk⟩
    rw [show a = b + l.A * k by linarith, zpow_add₀ hz, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow,
      _root_.mul_one]
  have hσp : IsPrimitiveRoot (σ (baseKA l).ζ) l.A := hprim.map_of_injective σ.injective
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hσp.pow_eq_one
  have hcop : i.Coprime l.A := (hprim.pow_iff_coprime l.A_pos i).1 (hi ▸ hσp)
  have hMpos : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hN : 0 < l.M * l.A := Nat.mul_pos hMpos l.A_pos
  have hN0 : NeZero (l.M * l.A) := ⟨hN.ne'⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective (m := l.M * l.A) (n := l.A) (dvd_mul_left _ _)
    (ZMod.unitOfCoprime i hcop)
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℤ, ν = ((v : ZMod (l.M * l.A)).val : ℤ) := ⟨_, rfl⟩
  have hνN : IsCoprime ν ((l.M * l.A : ℕ) : ℤ) := by
    rw [hνdef]
    exact Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime v)
  have hνi : (l.A : ℤ) ∣ ν - i := by
    have h2 := congrArg (fun w : (ZMod l.A)ˣ => (w : ZMod l.A)) hv
    simp only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_eq_val] at h2
    have h3 : ((i : ℤ) : ZMod l.A) = ((ν : ℤ) : ZMod l.A) := by
      rw [hνdef]
      push_cast
      exact h2.symm
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h3
  obtain ⟨c, hcN, hcM, -⟩ := GlobalTheory.SimMult.exists_scalar H l₀ (l.M * l.A) hN
    (by rw [← hM]; exact dvd_mul_right _ _) (by rw [hA]; exact one_dvd _) ν hνN
    (by rw [hA, Nat.cast_one]; exact one_dvd _)
  let fc : D.La →ₗ[𝓞 E] D.La := c • LinearMap.id
  have hfc : ∀ a b, ((l.M * l.A : ℕ) : ℤ) ∣ D.EF (fc a) (fc b) - ν * D.EF a b := by
    intro a b
    obtain ⟨t, ht⟩ := hcN
    have hc' : H.bar c * c = (ν : 𝓞 E) + ((l.M * l.A : ℕ) : 𝓞 E) * t := by linear_combination ht
    refine ⟨D.EF a (t • b), ?_⟩
    simp only [fc, LinearMap.smul_apply, LinearMap.id_apply]
    rw [D.adj, smul_smul, hc', add_smul, mul_smul]
    simp only [map_add, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, map_zsmul, map_nsmul, zsmul_eq_mul,
      nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨g, hgl⟩ := GlobalTheory.exists_sim_lift E H D (l.M * l.A) fc ν hN hνN hfc
  have hgA : (l.A : ℤ) ∣ g.ν l.A - i := by
    have t1 := GlobalTheory.SimAlg.dvd_mult_tower g l.A_pos hMpos hab
    rw [Nat.mul_comm] at t1
    have t2 : (l.A : ℤ) ∣ g.ν (l.M * l.A) - ν :=
      (Int.natCast_dvd_natCast.2 (Nat.dvd_mul_left l.A l.M)).trans hgl.2
    have := dvd_add (dvd_add (dvd_neg.2 t1) t2) hνi
    rw [show g.ν l.A - (i : ℤ) = -(g.ν (l.M * l.A) - g.ν l.A) + (g.ν (l.M * l.A) - ν) + (ν - i) by ring]
    exact this
  have hζ : σ.toRingHom (baseKA l).ζ = (baseKA l).ζ ^ g.ν l.A := by
    show σ (baseKA l).ζ = _
    rw [← hi, ← zpow_natCast]
    exact hcong _ _ (by rw [← neg_sub]; exact dvd_neg.2 hgA)
  have hgM : ∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro a
    have t1 := GlobalTheory.Moduli.LevelAction.mem_of_modN (D := D) l
      (GlobalTheory.SimAlg.modN_neg (g.tower l.M l.A hMpos l.A_pos a))
    have t2 := GlobalTheory.Moduli.LevelAction.mem_of_modN (D := D) l (GlobalTheory.SimAlg.modN_of_mul (hgl.1 a))
    have t3 : (c - 1) • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) :=
      Submodule.smul_mem_smul (by rw [hMb]; exact hcM) Submodule.mem_top
    have := add_mem (add_mem t1 t2) t3
    convert this using 1
    simp only [fc, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul]
    abel
  obtain ⟨f, m, h⟩ := exists_semiTwist hpq Xo σ.toRingHom g hρ hζ hgM
  obtain ⟨g', hg'⟩ := GlobalTheory.SimAlg.exists_inv g hab
  have hρ' : σ.symm.toRingHom (baseKA l).ρ = (baseKA l).ρ :=
    σ.injective (by rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, hρ])
  have hζ' : σ.symm.toRingHom (baseKA l).ζ = (baseKA l).ζ ^ g'.ν l.A := by
    apply σ.injective
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_zpow₀,
      ← RingEquiv.coe_toRingHom, ← RingEquiv.toRingHom_eq_coe, hζ, ← zpow_mul, ← zpow_one (baseKA l).ζ,
      ← zpow_mul, _root_.one_mul]
    exact hcong _ _ (by rw [← neg_sub]; exact dvd_neg.2 (hg' l.A l.A_pos).2)
  have hg'M : ∀ a, g'.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro a
    have := sub_mem (GlobalTheory.Moduli.LevelAction.mem_of_modN (D := D) l ((hg' l.M hMpos).1 a).2)
      (hgM (g'.f l.M a))
    rwa [sub_sub_sub_cancel_left] at this
  obtain ⟨f', m', h'⟩ := exists_semiTwist hpq Xo σ.symm.toRingHom g' hρ' hζ' hg'M
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.Moduli.LevelAction.exists_comp_sabMap m m' (rfl : f ≫ f' = f ≫ f')
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.Moduli.LevelAction.exists_comp_sabMap m' m (rfl : f' ≫ f = f' ≫ f)
  have e₁ : f ≫ f' = 𝟙 _ := by
    refine SemiTwist.eq_id n₁ (by rw [hn₁]; exact SemiTwist.comp h h') ?_ fun a => ?_
    · exact RingHom.ext fun x => by simp
    · exact GlobalTheory.Moduli.LevelAction.etaA_congr Xo.univ ((hg' l.A l.A_pos).1 a).2
  have e₂ : f' ≫ f = 𝟙 _ := by
    refine SemiTwist.eq_id n₂ (by rw [hn₂]; exact SemiTwist.comp h' h) ?_ fun a => ?_
    · exact RingHom.ext fun x => by simp
    · exact GlobalTheory.Moduli.LevelAction.etaA_congr Xo.univ ((hg' l.A l.A_pos).1 a).1
  exact ⟨⟨f, f', e₁, e₂⟩, m, g.f l.A, h⟩

end GlobalTheory.LevQuot
