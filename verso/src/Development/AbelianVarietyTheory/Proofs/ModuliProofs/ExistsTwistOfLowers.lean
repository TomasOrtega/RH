import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelGroup

open GlobalTheory.LevelFibre GlobalTheory.Moduli.LevelAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Field

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
Take `⟨x, hx⟩` from `x`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | rfl` into its components or cases. Conclude with `h₁`.

Conclude with `h₂`. Consider the case `algebraMap q`. Establish `: (⟨algebraMap ℚ ℂ q, (IntermediateField.adjoin ℚ {H.rt0, zeta l.A}).algebraMap_mem q⟩ : KA l) = (q : KA l)` using `Subtype.ext (by simp)`. Rewrite using `[this]`. Conclude with `SubfieldClass.ratCast_mem T q`.

Consider the case `add x y hx hy a b => exact T.add_mem a b`. Consider the case `inv x hx a => exact T.inv_mem a`. Consider the case `mul x y hx hy a b => exact T.mul_mem a b`.
-/
theorem mem_of_gens {l : Level H} (T : Subfield (KA l)) (h₁ : (baseKA l).ρ ∈ T) (h₂ : (baseKA l).ζ ∈ T) (x : KA l) :
    x ∈ T := by
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h₁
    · exact h₂
  | algebraMap q =>
    have : (⟨algebraMap ℚ ℂ q, (IntermediateField.adjoin ℚ {H.rt0, zeta l.A}).algebraMap_mem q⟩ : KA l) = (q : KA l) :=
      Subtype.ext (by simp)
    rw [this]
    exact SubfieldClass.ratCast_mem T q
  | add x y hx hy a b => exact T.add_mem a b
  | inv x hx a => exact T.inv_mem a
  | mul x y hx hy a b => exact T.mul_mem a b

/- English proof (translation)
The claim follows from `RingHom.ext fun x => mem_of_gens (β.eqLocusField β') h₁ h₂ x`.
-/
theorem ringHom_ext {l : Level H} {K : Type} [Field K] {β β' : KA l →+* K} (h₁ : β (baseKA l).ρ = β' (baseKA l).ρ)
    (h₂ : β (baseKA l).ζ = β' (baseKA l).ζ) : β = β' :=
  RingHom.ext fun x => mem_of_gens (β.eqLocusField β') h₁ h₂ x

/- English proof (translation)
Establish `h : ∀ x, ∃ y, β y = β' x` using `fun x => mem_of_gens (β.fieldRange.comap β') ⟨_, h₁⟩ ⟨(baseKA l).ζ ^ n, (map_zpow₀ _ _ _).trans h₂⟩ x`. Use `choose σ hσ using h`. Use `⟨{ toFun := σ map_one' := β.injective (by rw [hσ, map_one, map_one]) map_mul' := fun a b => β.injective (by rw [hσ, map_mul, map_mul, hσ, hσ]) map_zero' := β.injective (by rw [hσ, map_zero, map_zero]) map_add' := fun a b => β.injective (by rw [hσ, map_add, map_add, hσ, hσ]) }, Ri …` and prove the remaining obligations.
-/
theorem exists_factor {l : Level H} {K : Type} [Field K] (β β' : KA l →+* K) (h₁ : β (baseKA l).ρ = β' (baseKA l).ρ)
    {n : ℤ} (h₂ : β (baseKA l).ζ ^ n = β' (baseKA l).ζ) : ∃ σ : KA l →+* KA l, β.comp σ = β' := by
  have h : ∀ x, ∃ y, β y = β' x := fun x =>
    mem_of_gens (β.fieldRange.comap β') ⟨_, h₁⟩ ⟨(baseKA l).ζ ^ n, (map_zpow₀ _ _ _).trans h₂⟩ x
  choose σ hσ using h
  refine ⟨{ toFun := σ
            map_one' := β.injective (by rw [hσ, map_one, map_one])
            map_mul' := fun a b => β.injective (by rw [hσ, map_mul, map_mul, hσ, hσ])
            map_zero' := β.injective (by rw [hσ, map_zero, map_zero])
            map_add' := fun a b => β.injective (by rw [hσ, map_add, map_add, hσ, hσ]) }, RingHom.ext hσ⟩

/- English proof (translation)
Establish `h0 : (baseKA l).ζ ≠ 0` using `(baseKA l).ζ_prim.ne_zero l.A_pos.ne'`. Rewrite using `[← sub_add_cancel i j, zpow_add₀ h0, ((baseKA l).ζ_prim.zpow_eq_one_iff_dvd _).2 h, _root_.one_mul]`.
-/
theorem zeta_zpow_congr (l : Level H) {i j : ℤ} (h : (l.A : ℤ) ∣ i - j) : (baseKA l).ζ ^ i = (baseKA l).ζ ^ j := by
  have h0 : (baseKA l).ζ ≠ 0 := (baseKA l).ζ_prim.ne_zero l.A_pos.ne'
  rw [← sub_add_cancel i j, zpow_add₀ h0, ((baseKA l).ζ_prim.zpow_eq_one_iff_dvd _).2 h, _root_.one_mul]

end Field

/- English proof (translation)
Set `N : Submodule (𝓞 E) D.La` to `LinearMap.range (n • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))`. Use `haveI := D.fin`. Use `haveI : Module.Finite ℤ (D.La ⧸ N) := Module.Finite.trans (𝓞 E) _`. Use `haveI : Finite (D.La ⧸ N) := Module.finite_of_fg_torsion (M := D.La ⧸ N) fun x => by`. Take `⟨x, rfl⟩` from `N.mkQ_surjective x`.

Use `⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(n : ℤ) • N.mkQ x = 0`. Rewrite using `[natCast_zsmul, ← map_nsmul]`. Conclude with `(Submodule.Quotient.mk_eq_zero N).2 ⟨x, rfl⟩`. Take `⟨s, hs⟩` from `D.fin.fg_top`.

Use `⟨s → D.La ⧸ N, inferInstance, fun f x => N.mkQ (f x), fun f f' h a => ?_⟩` and prove the remaining obligations. Establish `: N.mkQ ∘ₗ f = N.mkQ ∘ₗ f'` using `LinearMap.ext_on hs fun x hx => congrFun h ⟨x, hx⟩`. Take `⟨c, hc⟩` from `(Submodule.Quotient.eq N).1 (LinearMap.congr_fun this a)`. Conclude with `⟨c, hc.symm⟩`.
-/
theorem exists_finite_mod (D : Datum H) {n : ℕ} (hn : 0 < n) : ∃ (Q : Type) (_ : Finite Q)
    (π : (D.La →ₗ[𝓞 E] D.La) → Q), ∀ f f', π f = π f' → ∀ a, D.ModN n (f a - f' a) := by
  let N : Submodule (𝓞 E) D.La := LinearMap.range (n • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
  haveI := D.fin
  haveI : Module.Finite ℤ (D.La ⧸ N) := Module.Finite.trans (𝓞 E) _
  haveI : Finite (D.La ⧸ N) := Module.finite_of_fg_torsion (M := D.La ⧸ N) fun x => by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    change (n : ℤ) • N.mkQ x = 0
    rw [natCast_zsmul, ← map_nsmul]
    exact (Submodule.Quotient.mk_eq_zero N).2 ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := D.fin.fg_top
  refine ⟨s → D.La ⧸ N, inferInstance, fun f x => N.mkQ (f x), fun f f' h a => ?_⟩
  have : N.mkQ ∘ₗ f = N.mkQ ∘ₗ f' := LinearMap.ext_on hs fun x hx => congrFun h ⟨x, hx⟩
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq N).1 (LinearMap.congr_fun this a)
  exact ⟨c, hc.symm⟩

section Obj

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

/- English proof (translation)
Take `⟨β, hβ⟩` from `exists_spMap (x ≫ s)`. Take `⟨-, I, -, -, hI⟩` from `o.geom k x β hβ`. Set `P : D.La → (Over.mk x ⟶ o.t.G)` to `fun a => toUnit _ ≫ o.eta a`. Establish `hP : ∀ a b, P (a + b) = P a * P b` using `fun a b => by`. Simplify using `only [P]`.

Rewrite using `[o.eta_add, MonObj.comp_mul]`. Use `eta_congr o (mem_of_eq_one l I P hP (fun b hb => ?_) hI (sub_eq_one P hP ?_))` and prove the remaining obligations. Simplify using `only [P]`. Rewrite using `[o.eta_ker b hb, MonObj.comp_one]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Simplify using `only [P]`. Rewrite using `[unit_left, unit_left, h]`.
-/
theorem eta_eq_of_point (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) {a c : D.La}
    (h : x ≫ (o.eta a).left = x ≫ (o.eta c).left) : o.eta a = o.eta c := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x β hβ
  let P : D.La → (Over.mk x ⟶ o.t.G) := fun a => toUnit _ ≫ o.eta a
  have hP : ∀ a b, P (a + b) = P a * P b := fun a b => by
    simp only [P]; rw [o.eta_add, MonObj.comp_mul]
  refine eta_congr o (mem_of_eq_one l I P hP (fun b hb => ?_) hI (sub_eq_one P hP ?_))
  · simp only [P]; rw [o.eta_ker b hb, MonObj.comp_one]
  · apply Over.OverMorphism.ext
    simp only [P]
    rw [unit_left, unit_left, h]

/- English proof (translation)
Take `⟨β, hβ⟩` from `exists_spMap (x ≫ s)`. Take `⟨-, I, -, hI, -⟩` from `o.geom k x β hβ`. Use `etaA_congr o (modN_of_ev_eq I l.A_pos ?_)` and prove the remaining obligations. Rewrite using `[← hI, ← hI]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[unit_left, unit_left, h]`.
-/
theorem etaA_eq_of_point (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) {a c : D.La}
    (h : x ≫ (o.etaA a).left = x ≫ (o.etaA c).left) : o.etaA a = o.etaA c := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
  obtain ⟨-, I, -, hI, -⟩ := o.geom k x β hβ
  refine etaA_congr o (modN_of_ev_eq I l.A_pos ?_)
  rw [← hI, ← hI]
  apply Over.OverMorphism.ext
  rw [unit_left, unit_left, h]

def twistObj {s' : S ⟶ Sp (KA l)} (o : Obj D l (baseKA l) s') (g : Sim D) (hpq : 1 ≤ D.p + D.q) (b' : Base l (KA l))
    (hρ : b'.ρ = (baseKA l).ρ) (hζ : b'.ζ = (baseKA l).ζ ^ g.ν l.A) : Obj D l b' s' where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta a := o.eta (g.f l.M a)
  eta_add a c := by rw [map_add, o.eta_add]
  eta_ker a ha := o.eta_ker _ (LevelTwist.map_mem_smul_top _ _ ha)
  etaA a := o.etaA (g.f l.A a)
  etaA_add a c := by rw [map_add, o.etaA_add]
  etaA_ker a := by rw [map_nsmul, o.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨hd, I, hζ', hA', hM⟩ := o.geom k x β hx
    refine ⟨hρ ▸ hd, LevelTwist.twist I g ((SimAlg.sim_group E H D hpq).1 g), ?_, fun a => hA' _,
      fun a ha => hM _ (LevelTwist.map_mem_smul_top _ _ ha)⟩
    rw [LevelTwist.twist_ζ, hζ, map_zpow₀, ← hζ', Units.val_zpow_eq_zpow_val]

/- English proof (translation)
Take `⟨e, he⟩` from `exists_ptEquiv m.cart (𝟙 S') f (Category.id_comp f)`. Establish `h₁ : e (toUnit _ ≫ σ) = toUnit _ ≫ τ`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[he, unit_left, unit_left, Category.id_comp]`. Conclude with `h`.

Establish `h₂` using `congrArg (fun w => (w ^ d).left) h₁`. Simplify using `only [← map_pow, ← MonObj.comp_pow, he, unit_left, Category.id_comp] at h₂`. Conclude with `h₂`.
-/
theorem pow_left_comp {S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {σ : 𝟙_ (Over S') ⟶ t'.G} {τ : 𝟙_ (Over S) ⟶ t.G} (h : σ.left ≫ m.φ = f ≫ τ.left) (d : ℕ) :
    (σ ^ d).left ≫ m.φ = f ≫ (τ ^ d).left := by
  obtain ⟨e, he⟩ := exists_ptEquiv m.cart (𝟙 S') f (Category.id_comp f)
  have h₁ : e (toUnit _ ≫ σ) = toUnit _ ≫ τ := by
    apply Over.OverMorphism.ext
    rw [he, unit_left, unit_left, Category.id_comp]; exact h
  have h₂ := congrArg (fun w => (w ^ d).left) h₁
  simp only [← map_pow, ← MonObj.comp_pow, he, unit_left, Category.id_comp] at h₂
  exact h₂

end Obj

section Action

variable {l l₂ : Level H} (Xo : Moduli D l₂) (jK : KA l →+* KA l₂)

structure Twist (g : Sim D) (σ : KA l₂ →+* KA l₂) (f : Xo.X ⟶ Xo.X) : Prop where
  fix : σ.comp jK = jK
  root : σ (baseKA l₂).ζ = (baseKA l₂).ζ ^ g.ν l₂.A
  lowM : ∀ a, Xo.univ.eta (g.f l₂.M a) ^ (l₂.M / l.M) = Xo.univ.eta a ^ (l₂.M / l.M)
  lowA : ∀ a, Xo.univ.etaA (g.f l₂.A a) ^ (l₂.A / l.A) = Xo.univ.etaA a ^ (l₂.A / l.A)
  comm : f ≫ Xo.s = Xo.s ≫ spMap σ
  map : ∃ ν : SABMap Xo.univ.t Xo.univ.t f,
    (∀ a, (Xo.univ.eta (g.f l₂.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo.univ.etaA (g.f l₂.A a)).left ≫ ν.φ = f ≫ (Xo.univ.etaA a).left

/- English proof (translation)
Use `haveI := Xo.smooth`. Conclude with `(isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s (SmoothOfRelativeDimension.smooth D.dim _)).1`.
-/
theorem reduced : IsReduced Xo.X := by
  haveI := Xo.smooth
  exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
    (SmoothOfRelativeDimension.smooth D.dim _)).1

variable {Xo jK}

/- English proof (translation)
The claim follows from `lowerBase_rho jK hj`.
-/
theorem jK_rho (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) : jK (baseKA l).ρ = (baseKA l₂).ρ :=
  lowerBase_rho jK hj

/- English proof (translation)
Rewrite using `[← jK_rho hj]`. Conclude with `RingHom.congr_fun h _`.
-/
theorem rho_of_fix (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) {K : Type} [Field K] {β β' : KA l₂ →+* K}
    (h : β.comp jK = β'.comp jK) : β (baseKA l₂).ρ = β' (baseKA l₂).ρ := by
  rw [← jK_rho hj]; exact RingHom.congr_fun h _

def baseVia (σ : KA l₂ →+* KA l₂) : Base l₂ (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := σ (baseKA l₂).ζ
  ζ_prim := (baseKA l₂).ζ_prim.map_of_injective σ.injective

/- English proof (translation)
Take `⟨f, ⟨h₁, ⟨m⟩⟩, hu⟩` from `moduli_rep_of_base ObjMaps.id_comp_cancel E H D l₂ Xo _ (baseVia σ) σ _ Xo.s (twistObj Xo.univ g hpq (baseVia σ) rfl root) (reduced Xo) (rho_of_fix hj (β' := RingHom.id _) fix) rfl`. Conclude with `⟨f, ⟨h₁, m.toSABMap, m.eta, m.etaA⟩, fun f' ⟨a, ν, b, c⟩ => hu f' ⟨a, ⟨⟨ν, b, c⟩⟩⟩⟩`.
-/
theorem existsUnique_twist (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {g : Sim D} {σ : KA l₂ →+* KA l₂} (fix : σ.comp jK = jK) (root : σ (baseKA l₂).ζ = (baseKA l₂).ζ ^ g.ν l₂.A) :
    ∃! f : Xo.X ⟶ Xo.X, f ≫ Xo.s = Xo.s ≫ spMap σ ∧ ∃ ν : SABMap Xo.univ.t Xo.univ.t f,
      (∀ a, (Xo.univ.eta (g.f l₂.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left) ∧
      ∀ a, (Xo.univ.etaA (g.f l₂.A a)).left ≫ ν.φ = f ≫ (Xo.univ.etaA a).left := by
  obtain ⟨f, ⟨h₁, ⟨m⟩⟩, hu⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l₂ Xo _ (baseVia σ) σ _ Xo.s
    (twistObj Xo.univ g hpq (baseVia σ) rfl root) (reduced Xo) (rho_of_fix hj (β' := RingHom.id _) fix) rfl
  exact ⟨f, ⟨h₁, m.toSABMap, m.eta, m.etaA⟩, fun f' ⟨a, ν, b, c⟩ => hu f' ⟨a, ⟨⟨ν, b, c⟩⟩⟩⟩

/- English proof (translation)
Substitute `hσ` using the available equality. Take `⟨ν, a, b⟩` from `h'.map`. Conclude with `(existsUnique_twist hpq hj h.fix h.root).unique ⟨h.comm, h.map⟩ ⟨h'.comm, ν, fun x => by rw [hM]; exact a x, fun x => by rw [hA]; exact b x⟩`.
-/
theorem Twist.unique (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {g g' : Sim D} {σ σ' : KA l₂ →+* KA l₂} {f f' : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f) (h' : Twist Xo jK g' σ' f')
    (hσ : σ = σ') (hM : ∀ a, Xo.univ.eta (g.f l₂.M a) = Xo.univ.eta (g'.f l₂.M a))
    (hA : ∀ a, Xo.univ.etaA (g.f l₂.A a) = Xo.univ.etaA (g'.f l₂.A a)) : f = f' := by
  subst hσ
  obtain ⟨ν, a, b⟩ := h'.map
  exact (existsUnique_twist hpq hj h.fix h.root).unique ⟨h.comm, h.map⟩
    ⟨h'.comm, ν, fun x => by rw [hM]; exact a x, fun x => by rw [hA]; exact b x⟩

/- English proof (translation)
The claim follows from `rfl root := (zpow_one _).symm lowM _ := rfl lowA _ := rfl comm := by rw [spMap_id', Category.id_comp, Category.comp_id] map := ⟨ObjLower.sabId _, fun _ => (Category.comp_id _).trans (Category.id_comp _).symm, fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩`.
-/
theorem Twist.one : Twist Xo jK (SimAlg.one D) (RingHom.id _) (𝟙 _) where
  fix := rfl
  root := (zpow_one _).symm
  lowM _ := rfl
  lowA _ := rfl
  comm := by rw [spMap_id', Category.id_comp, Category.comp_id]
  map := ⟨ObjLower.sabId _, fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩

/- English proof (translation)
Rewrite using `[RingHom.comp_assoc, h'.fix, h.fix] root := by rw [RingHom.comp_apply, h'.root, map_zpow₀, h.root, ← zpow_mul]; rfl lowM a := (h.lowM _).trans (h'.lowM a) lowA a := (h.lowA _).trans (h'.lowA a) comm := by rw [Category.assoc, h'.comm, ← Category.assoc, h.comm, Category.assoc, spMa …`. Take `⟨ν, a, b⟩` from `h.map`. Take `⟨ν', a', b'⟩` from `h'.map`. Take `⟨n, hn⟩` from `exists_comp_sabMap ν ν' rfl`. Use `⟨n, fun x => ?_, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[hn, Category.assoc, ← a', ← Category.assoc, ← Category.assoc, ← a]`. Both sides reduce to the same expression. Rewrite using `[hn, Category.assoc, ← b', ← Category.assoc, ← Category.assoc, ← b]`. Both sides reduce to the same expression.
-/
theorem Twist.mul {g g' : Sim D} {σ σ' : KA l₂ →+* KA l₂} {f f' : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f)
    (h' : Twist Xo jK g' σ' f') : Twist Xo jK (SimAlg.mul g g') (σ.comp σ') (f ≫ f') where
  fix := by rw [RingHom.comp_assoc, h'.fix, h.fix]
  root := by rw [RingHom.comp_apply, h'.root, map_zpow₀, h.root, ← zpow_mul]; rfl
  lowM a := (h.lowM _).trans (h'.lowM a)
  lowA a := (h.lowA _).trans (h'.lowA a)
  comm := by rw [Category.assoc, h'.comm, ← Category.assoc, h.comm, Category.assoc, spMap_comp']
  map := by
    obtain ⟨ν, a, b⟩ := h.map
    obtain ⟨ν', a', b'⟩ := h'.map
    obtain ⟨n, hn⟩ := exists_comp_sabMap ν ν' rfl
    refine ⟨n, fun x => ?_, fun x => ?_⟩
    · rw [hn, Category.assoc, ← a', ← Category.assoc, ← Category.assoc, ← a]; rfl
    · rw [hn, Category.assoc, ← b', ← Category.assoc, ← Category.assoc, ← b]; rfl

/- English proof (translation)
Take `⟨g', hg'⟩` from `(SimAlg.sim_group E H D hpq).2.2.2 g`. Establish `hz : σ (baseKA l₂).ζ ^ g'.ν l₂.A = (baseKA l₂).ζ`. Rewrite using `[h.root, ← zpow_mul, zeta_zpow_congr l₂ (hg' _ l₂.A_pos).2, zpow_one]`. Take `⟨σ', hσ'⟩` from `exists_factor σ (RingHom.id _) (rho_of_fix hj h.fix) hz`. Establish `fix : σ'.comp jK = jK` using `RingHom.ext fun x => σ.injective ((RingHom.congr_fun hσ' (jK x)).trans (RingHom.congr_fun h.fix x).symm)`.

Establish `root : σ' (baseKA l₂).ζ = (baseKA l₂).ζ ^ g'.ν l₂.A` using `σ.injective ((RingHom.congr_fun hσ' _).trans (by rw [map_zpow₀, hz]; rfl))`. Establish `eM : ∀ a, Xo.univ.eta (g.f l₂.M (g'.f l₂.M a)) = Xo.univ.eta a` using `fun a => eta_congr _ (LevelFibre.mem_of_modN l₂ ((hg' _ (level_pos l₂)).1 a).2)`. Establish `eA : ∀ a, Xo.univ.etaA (g.f l₂.A (g'.f l₂.A a)) = Xo.univ.etaA a` using `fun a => etaA_congr _ ((hg' _ l₂.A_pos).1 a).2`. Take `⟨f', ⟨a, b⟩, -⟩` from `existsUnique_twist (Xo := Xo) hpq hj fix root`. Establish `h' : Twist Xo jK g' σ' f'` using `⟨fix, root, fun x => by rw [← h.lowM, eM], fun x => by rw [← h.lowA, eA], a, b⟩`.

Conclude with `⟨g', σ', f', h', (h.mul h').unique hpq hj Twist.one hσ' eM eA⟩`.
-/
theorem Twist.exists_inv (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {g : Sim D} {σ : KA l₂ →+* KA l₂} {f : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f) :
    ∃ g' σ' f', Twist Xo jK g' σ' f' ∧ f ≫ f' = 𝟙 _ := by
  obtain ⟨g', hg'⟩ := (SimAlg.sim_group E H D hpq).2.2.2 g
  have hz : σ (baseKA l₂).ζ ^ g'.ν l₂.A = (baseKA l₂).ζ := by
    rw [h.root, ← zpow_mul, zeta_zpow_congr l₂ (hg' _ l₂.A_pos).2, zpow_one]
  obtain ⟨σ', hσ'⟩ := exists_factor σ (RingHom.id _) (rho_of_fix hj h.fix) hz
  have fix : σ'.comp jK = jK := RingHom.ext fun x => σ.injective
    ((RingHom.congr_fun hσ' (jK x)).trans (RingHom.congr_fun h.fix x).symm)
  have root : σ' (baseKA l₂).ζ = (baseKA l₂).ζ ^ g'.ν l₂.A := σ.injective
    ((RingHom.congr_fun hσ' _).trans (by rw [map_zpow₀, hz]; rfl))
  have eM : ∀ a, Xo.univ.eta (g.f l₂.M (g'.f l₂.M a)) = Xo.univ.eta a := fun a =>
    eta_congr _ (LevelFibre.mem_of_modN l₂ ((hg' _ (level_pos l₂)).1 a).2)
  have eA : ∀ a, Xo.univ.etaA (g.f l₂.A (g'.f l₂.A a)) = Xo.univ.etaA a := fun a =>
    etaA_congr _ ((hg' _ l₂.A_pos).1 a).2
  obtain ⟨f', ⟨a, b⟩, -⟩ := existsUnique_twist (Xo := Xo) hpq hj fix root
  have h' : Twist Xo jK g' σ' f' :=
    ⟨fix, root, fun x => by rw [← h.lowM, eM], fun x => by rw [← h.lowA, eA], a, b⟩
  exact ⟨g', σ', f', h', (h.mul h').unique hpq hj Twist.one hσ' eM eA⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x => by have := pow_left_comp ν (a x) (l₂.M / l.M) rw [h.lowM] at this exact this, fun x => by have := pow_left_comp ν (b x) (l₂.A / l.A) rw [h.lowA] at this exact this⟩`.
-/
theorem Twist.lowers {g : Sim D} {σ : KA l₂ →+* KA l₂} {f : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f)
    (ν : SABMap Xo.univ.t Xo.univ.t f)
    (a : ∀ a, (Xo.univ.eta (g.f l₂.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left)
    (b : ∀ a, (Xo.univ.etaA (g.f l₂.A a)).left ≫ ν.φ = f ≫ (Xo.univ.etaA a).left) :
    Lowers l Xo.univ (fun x => Xo.univ.eta x ^ (l₂.M / l.M)) (fun x => Xo.univ.etaA x ^ (l₂.A / l.A)) f ν.φ :=
  ⟨fun x => by
    have := pow_left_comp ν (a x) (l₂.M / l.M)
    rw [h.lowM] at this
    exact this, fun x => by
    have := pow_left_comp ν (b x) (l₂.A / l.A)
    rw [h.lowA] at this
    exact this⟩

def lowUniv (Xo : Moduli D l₂) (hd : l.Dvd l₂) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) :
    Obj D l (lowerBase jK) Xo.s :=
  ObjLower.lower Xo.univ hd rfl (lowerBase_zeta jK hd.2.2 hj)

/- English proof (translation)
The claim follows from `obj_pull E H D l _ _ b b (RingHom.id _) _ _ s (y ≫ s) y rfl rfl (by rw [spMap_id', Category.comp_id]) o`.
-/
theorem pull_univ {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) (y : S' ⟶ S) : ∃ o' : Obj D l b (y ≫ s), Nonempty (ObjMap o' o y) :=
  obj_pull E H D l _ _ b b (RingHom.id _) _ _ s (y ≫ s) y rfl rfl (by rw [spMap_id', Category.comp_id]) o

/- English proof (translation)
Take `⟨ν, a, b⟩` from `h.map`. Take `⟨o, ⟨p⟩⟩` from `pull_univ (lowUniv Xo hd hj) y`. Take `⟨n, hn⟩` from `exists_comp_sabMap (t' := Xo.univ.t) p.toSABMap ν hy`. Establish `hrig : n.φ = p.toSABMap.φ` using `obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ (lowUniv Xo hd hj) o y (Or.inl inferInstance) n p.toSABMap fun x => ⟨_, by`. Establish `h₁ : (o.eta x).left ≫ p.toSABMap.φ = y ≫ (Xo.univ.eta x ^ (l₂.M / l.M)).left` using `p.eta x`.

Establish `h₂` using `(h.lowers ν a b).1 x`. Use `Eq.trans ?_ h₁.symm` and prove the remaining obligations. Rewrite using `[hn]`. Use `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ν.φ) h₁).trans ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, h₂, ← Category.assoc, hy], rfl⟩`.

Establish `hid : ∀ τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G, y ≫ τ.left ≫ ν.φ = y ≫ τ.left` using `fun τ => by`. Establish `hq : p.toSABMap.cart.1.lift (y ≫ τ.left) (𝟙 _) ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (sec_w τ)).trans ((Category.comp_id _).trans (Category.id_comp _).symm))) ≫ p.toSABMap.φ = y ≫ τ.left` using `p.toSABMap.cart.1.lift_fst _ _ _`. Rewrite using `[← Category.assoc, ← hq]`. Conclude with `(Category.assoc _ _ _).trans (congrArg _ (hn.symm.trans hrig))`. Take `⟨β, hβ⟩` from `exists_spMap (y ≫ Xo.s)`.

Establish `hσ : β.comp σ = β` using `spMap_inj (by`. Rewrite using `[← spMap_comp', ← hβ, Category.assoc, ← h.comm, ← Category.assoc, hy])`. Use `h.unique hpq hj Twist.one (RingHom.ext fun x => β.injective (RingHom.congr_fun hσ x)) (fun x => eta_eq_of_point _ y ?_) (fun x => etaA_eq_of_point _ y ?_)` and prove the remaining obligations. Rewrite using `[← hid, a, ← Category.assoc, hy]`. Both sides reduce to the same expression.

Rewrite using `[← hid, b, ← Category.assoc, hy]`. Both sides reduce to the same expression.
-/
theorem Twist.eq_id_of_fixed (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂)
    (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {g : Sim D} {σ : KA l₂ →+* KA l₂} {f : Xo.X ⟶ Xo.X} (h : Twist Xo jK g σ f)
    {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (hy : y ≫ f = y) : f = 𝟙 _ := by
  obtain ⟨ν, a, b⟩ := h.map
  obtain ⟨o, ⟨p⟩⟩ := pull_univ (lowUniv Xo hd hj) y
  obtain ⟨n, hn⟩ := exists_comp_sabMap (t' := Xo.univ.t) p.toSABMap ν hy
  have hrig : n.φ = p.toSABMap.φ := obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ (lowUniv Xo hd hj) o y
    (Or.inl inferInstance) n p.toSABMap fun x => ⟨_, by
      have h₁ : (o.eta x).left ≫ p.toSABMap.φ = y ≫ (Xo.univ.eta x ^ (l₂.M / l.M)).left := p.eta x
      have h₂ := (h.lowers ν a b).1 x
      refine Eq.trans ?_ h₁.symm
      rw [hn]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ν.φ) h₁).trans ?_)
      rw [Category.assoc, h₂, ← Category.assoc, hy], rfl⟩
  have hid : ∀ τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G, y ≫ τ.left ≫ ν.φ = y ≫ τ.left := fun τ => by
    have hq : p.toSABMap.cart.1.lift (y ≫ τ.left) (𝟙 _) ((Category.assoc _ _ _).trans
        ((congrArg (y ≫ ·) (sec_w τ)).trans ((Category.comp_id _).trans (Category.id_comp _).symm))) ≫ p.toSABMap.φ = y ≫ τ.left :=
      p.toSABMap.cart.1.lift_fst _ _ _
    rw [← Category.assoc, ← hq]
    exact (Category.assoc _ _ _).trans (congrArg _ (hn.symm.trans hrig))
  obtain ⟨β, hβ⟩ := exists_spMap (y ≫ Xo.s)
  have hσ : β.comp σ = β := spMap_inj (by
    rw [← spMap_comp', ← hβ, Category.assoc, ← h.comm, ← Category.assoc, hy])
  refine h.unique hpq hj Twist.one (RingHom.ext fun x => β.injective (RingHom.congr_fun hσ x))
    (fun x => eta_eq_of_point _ y ?_) (fun x => etaA_eq_of_point _ y ?_)
  · rw [← hid, a, ← Category.assoc, hy]; rfl
  · rw [← hid, b, ← Category.assoc, hy]; rfl

/- English proof (translation)
Take `⟨β, hβ⟩` from `exists_spMap (y ≫ Xo.s)`. Take `⟨β', hβ'⟩` from `exists_spMap (y' ≫ Xo.s)`. Establish `hb : β.comp jK = β'.comp jK` using `spMap_inj (by`. Rewrite using `[← spMap_comp', ← spMap_comp', ← hβ, ← hβ', Category.assoc, Category.assoc, hs])`. Take `⟨o, ⟨p⟩⟩` from `pull_univ Xo.univ y'`.

Take `⟨p', hp'⟩` from `sab_cast (Category.id_comp y').symm p.toSABMap`. Take `⟨n', hn'⟩` from `ObjMaps.exists_sab_cancel mu' p'`. Take `⟨n, hn⟩` from `exists_comp_sabMap n' mu (Category.id_comp y)`. Establish `key : ∀ (τ : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (τ₀ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (ε : 𝟙_ (Over (Sp k)) ⟶ t.G) (d : ℕ), τ.left ≫ p.toSABMap.φ = y' ≫ τ₀.left → ε.left ≫ mu'.φ = y' ≫ (τ₀ ^ d).left → (τ ^ d).left ≫ n.φ = ε.left ≫ mu.φ` using `fun τ τ₀ ε d h₁ h₂ => by`. Establish `h₃ : (τ ^ d).left ≫ n'.φ = ε.left`.

Apply `mu'.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc]`. Conclude with `((congrArg _ (hn'.symm.trans hp')).trans (pow_left_comp p.toSABMap h₁ d)).trans h₂.symm`. Rewrite using `[Category.assoc, n'.cart.1.w, ← Category.assoc, sec_w, sec_w]`. Conclude with `Category.id_comp _`.

Rewrite using `[hn, ← Category.assoc, h₃]`. Take `⟨-, J, hJζ, hJA, hJ⟩` from `Xo.univ.geom k y β hβ`. Take `⟨-, I, hIζ, hIA, hI⟩` from `o.geom k (𝟙 _) β' ((Category.id_comp _).trans hβ')`. Take `⟨e, he⟩` from `exists_ptEquiv n.cart (𝟙 _) y (Category.id_comp y)`. Take `⟨J', hJζ', hJ'⟩` from `exists_tate_push n (𝟙 _) y (Category.id_comp y) e he I`.

Take `⟨h₁, h₂, h₃, h₄⟩` from `obj_isAbelianScheme_dim_rigidified_sym E H D l₂ _ (baseKA l₂) _ Xo.s Xo.univ`. Use `Xo.smooth` as an intermediate fact. Establish `: Smooth Xo.s` using `SmoothOfRelativeDimension.smooth D.dim Xo.s`. Establish `: IsLocallyNoetherian Xo.X` using `LocallyOfFiniteType.isLocallyNoetherian Xo.s`. Set `PA : Out.PolAV Xo.X` to `{ A := Xo.univ.t.G, isAb := h₁, g := _, smoothDim := h₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB, rigid := h₃, sym := h₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv }`.

Take `⟨g, hg⟩` from `tateIso_differ_by_similitude E H D k _ _ _ (fun n p q a b _ hp hq ha hb => unitOn_injective (((hL.weil _ PA n (Over.mk y)).1 p q hp hq).unique ha hb)) J J'`. Establish `hel : ∀ τ : 𝟙_ (Over (Sp k)) ⟶ o.t.G, (e (toUnit _ ≫ τ)).left = τ.left ≫ n.φ` using `fun τ => by`. Rewrite using `[he, unit_left, Category.id_comp]`. Establish `hA : ∀ a, e (toUnit _ ≫ o.etaA a) = toUnit _ ≫ Xo.univ.etaA (g.f l₂.A a)` using `fun a => by`. Rewrite using `[hIA, hJA, ← hJ', (hg _ l₂.A_pos).1]`.

Establish `hM : ∀ a, e (toUnit _ ≫ o.eta a) = toUnit _ ≫ Xo.univ.eta (g.f l₂.M a)` using `fun a => by`. Take `⟨u, hu, v, hv, huv⟩` from `level_split l₂`. Establish `hcs : a = u • a + v • a` using `by rw [← add_smul, huv, one_smul]`. Rewrite using `[hcs, o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul hu trivial), map_add, Xo.univ.eta_add, map_smul, map_smul, Xo.univ.eta_ker _ (Submodule.smul_mem_smul hu trivial), _root_.one_mul, _root_.one_mul, hI _ (Submodule.smul_mem_smul hv trivial), hJ _ (Submodule.smul_mem_smul hv tri …`. Establish `hA' : ∀ a, (o.etaA a).left ≫ n.φ = y ≫ (Xo.univ.etaA (g.f l₂.A a)).left` using `fun a => by`.

Rewrite using `[← hel, hA, unit_left]`. Establish `hM' : ∀ a, (o.eta a).left ≫ n.φ = y ≫ (Xo.univ.eta (g.f l₂.M a)).left` using `fun a => by`. Rewrite using `[← hel, hM, unit_left]`. Establish `hz : β (baseKA l₂).ζ ^ g.ν l₂.A = β' (baseKA l₂).ζ`. Rewrite using `[← hJζ, ← hIζ, ← hJζ', (hg _ l₂.A_pos).2, Units.val_zpow_eq_zpow_val]`.

Take `⟨σ, hσ⟩` from `exists_factor β β' (rho_of_fix hj hb) hz`. Establish `fix : σ.comp jK = jK` using `RingHom.ext fun x => β.injective ((RingHom.congr_fun hσ (jK x)).trans (RingHom.congr_fun hb x).symm)`. Establish `root : σ (baseKA l₂).ζ = (baseKA l₂).ζ ^ g.ν l₂.A` using `β.injective ((RingHom.congr_fun hσ _).trans (by rw [map_zpow₀, hz]))`. Take `⟨f, ⟨hf, ν, a, b⟩, -⟩` from `existsUnique_twist (Xo := Xo) hpq hj fix root`. Use `⟨g, σ, f, ⟨fix, root, fun x => eta_eq_of_point (lowUniv Xo hd hj) y ?_, fun x => etaA_eq_of_point (lowUniv Xo hd hj) y ?_, hf, ν, a, b⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(pow_left_comp n (hM' x) _).symm.trans ((key _ _ _ _ (p.eta x) (hl'.1 x)).trans (hl.1 x))`. Conclude with `(pow_left_comp n (hA' x) _).symm.trans ((key _ _ _ _ (p.etaA x) (hl'.2 x)).trans (hl.2 x))`. Take `⟨m, hm⟩` from `exists_comp_sabMap n ν rfl`. Use `(Xo.rep (Sp k) (y' ≫ Xo.s) inferInstance o).unique ⟨?_, ⟨⟨m, fun x => ?_, fun x => ?_⟩⟩⟩ ⟨rfl, ⟨p⟩⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hf, ← Category.assoc, hβ, hβ', spMap_comp', hσ]`.

Use `show _ ≫ m.φ = _`. Rewrite using `[hm, ← Category.assoc, hM', Category.assoc, a, Category.assoc]`. Use `show _ ≫ m.φ = _`. Rewrite using `[hm, ← Category.assoc, hA', Category.assoc, b, Category.assoc]`.
-/
theorem exists_twist_of_lowers (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂)
    (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) {k : Type} [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Xo.X)
    (t : SAB H (Sp k)) (mu : SABMap t Xo.univ.t y) (mu' : SABMap t Xo.univ.t y')
    (eM eA : D.La → (𝟙_ (Over (Sp k)) ⟶ t.G)) (hs : y ≫ Xo.s ≫ spMap jK = y' ≫ Xo.s ≫ spMap jK)
    (hl : Lowers l Xo.univ eM eA y mu.φ) (hl' : Lowers l Xo.univ eM eA y' mu'.φ) :
    ∃ g σ f, Twist Xo jK g σ f ∧ y ≫ f = y' := by
  obtain ⟨β, hβ⟩ := exists_spMap (y ≫ Xo.s)
  obtain ⟨β', hβ'⟩ := exists_spMap (y' ≫ Xo.s)
  have hb : β.comp jK = β'.comp jK := spMap_inj (by
    rw [← spMap_comp', ← spMap_comp', ← hβ, ← hβ', Category.assoc, Category.assoc, hs])
  obtain ⟨o, ⟨p⟩⟩ := pull_univ Xo.univ y'
  obtain ⟨p', hp'⟩ := sab_cast (Category.id_comp y').symm p.toSABMap
  obtain ⟨n', hn'⟩ := ObjMaps.exists_sab_cancel mu' p'
  obtain ⟨n, hn⟩ := exists_comp_sabMap n' mu (Category.id_comp y)
  have key : ∀ (τ : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (τ₀ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (ε : 𝟙_ (Over (Sp k)) ⟶ t.G) (d : ℕ),
      τ.left ≫ p.toSABMap.φ = y' ≫ τ₀.left → ε.left ≫ mu'.φ = y' ≫ (τ₀ ^ d).left →
      (τ ^ d).left ≫ n.φ = ε.left ≫ mu.φ := fun τ τ₀ ε d h₁ h₂ => by
    have h₃ : (τ ^ d).left ≫ n'.φ = ε.left := by
      apply mu'.cart.1.hom_ext
      · rw [Category.assoc]
        exact ((congrArg _ (hn'.symm.trans hp')).trans (pow_left_comp p.toSABMap h₁ d)).trans h₂.symm
      · rw [Category.assoc, n'.cart.1.w, ← Category.assoc, sec_w, sec_w]
        exact Category.id_comp _
    rw [hn, ← Category.assoc, h₃]
  obtain ⟨-, J, hJζ, hJA, hJ⟩ := Xo.univ.geom k y β hβ
  obtain ⟨-, I, hIζ, hIA, hI⟩ := o.geom k (𝟙 _) β' ((Category.id_comp _).trans hβ')
  obtain ⟨e, he⟩ := exists_ptEquiv n.cart (𝟙 _) y (Category.id_comp y)
  obtain ⟨J', hJζ', hJ'⟩ := exists_tate_push n (𝟙 _) y (Category.id_comp y) e he I
  obtain ⟨h₁, h₂, h₃, h₄⟩ := obj_isAbelianScheme_dim_rigidified_sym E H D l₂ _ (baseKA l₂) _ Xo.s Xo.univ
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  let PA : Out.PolAV Xo.X :=
    { A := Xo.univ.t.G, isAb := h₁, g := _, smoothDim := h₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB,
      rigid := h₃, sym := h₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv }
  obtain ⟨g, hg⟩ := tateIso_differ_by_similitude E H D k _ _ _ (fun n p q a b _ hp hq ha hb =>
    unitOn_injective (((hL.weil _ PA n (Over.mk y)).1 p q hp hq).unique ha hb)) J J'
  have hel : ∀ τ : 𝟙_ (Over (Sp k)) ⟶ o.t.G, (e (toUnit _ ≫ τ)).left = τ.left ≫ n.φ := fun τ => by
    rw [he, unit_left, Category.id_comp]
  have hA : ∀ a, e (toUnit _ ≫ o.etaA a) = toUnit _ ≫ Xo.univ.etaA (g.f l₂.A a) := fun a => by
    rw [hIA, hJA, ← hJ', (hg _ l₂.A_pos).1]
  have hM : ∀ a, e (toUnit _ ≫ o.eta a) = toUnit _ ≫ Xo.univ.eta (g.f l₂.M a) := fun a => by
    obtain ⟨u, hu, v, hv, huv⟩ := level_split l₂
    have hcs : a = u • a + v • a := by rw [← add_smul, huv, one_smul]
    rw [hcs, o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul hu trivial), map_add, Xo.univ.eta_add, map_smul, map_smul,
      Xo.univ.eta_ker _ (Submodule.smul_mem_smul hu trivial), _root_.one_mul, _root_.one_mul,
      hI _ (Submodule.smul_mem_smul hv trivial), hJ _ (Submodule.smul_mem_smul hv trivial), ← hJ',
      (hg _ (level_pos l₂)).1, map_smul]
  have hA' : ∀ a, (o.etaA a).left ≫ n.φ = y ≫ (Xo.univ.etaA (g.f l₂.A a)).left := fun a => by
    rw [← hel, hA, unit_left]
  have hM' : ∀ a, (o.eta a).left ≫ n.φ = y ≫ (Xo.univ.eta (g.f l₂.M a)).left := fun a => by
    rw [← hel, hM, unit_left]
  have hz : β (baseKA l₂).ζ ^ g.ν l₂.A = β' (baseKA l₂).ζ := by
    rw [← hJζ, ← hIζ, ← hJζ', (hg _ l₂.A_pos).2, Units.val_zpow_eq_zpow_val]
  obtain ⟨σ, hσ⟩ := exists_factor β β' (rho_of_fix hj hb) hz
  have fix : σ.comp jK = jK := RingHom.ext fun x => β.injective
    ((RingHom.congr_fun hσ (jK x)).trans (RingHom.congr_fun hb x).symm)
  have root : σ (baseKA l₂).ζ = (baseKA l₂).ζ ^ g.ν l₂.A := β.injective
    ((RingHom.congr_fun hσ _).trans (by rw [map_zpow₀, hz]))
  obtain ⟨f, ⟨hf, ν, a, b⟩, -⟩ := existsUnique_twist (Xo := Xo) hpq hj fix root
  refine ⟨g, σ, f, ⟨fix, root, fun x => eta_eq_of_point (lowUniv Xo hd hj) y ?_,
    fun x => etaA_eq_of_point (lowUniv Xo hd hj) y ?_, hf, ν, a, b⟩, ?_⟩
  · exact (pow_left_comp n (hM' x) _).symm.trans ((key _ _ _ _ (p.eta x) (hl'.1 x)).trans (hl.1 x))
  · exact (pow_left_comp n (hA' x) _).symm.trans ((key _ _ _ _ (p.etaA x) (hl'.2 x)).trans (hl.2 x))
  · obtain ⟨m, hm⟩ := exists_comp_sabMap n ν rfl
    refine (Xo.rep (Sp k) (y' ≫ Xo.s) inferInstance o).unique ⟨?_, ⟨⟨m, fun x => ?_, fun x => ?_⟩⟩⟩ ⟨rfl, ⟨p⟩⟩
    · rw [Category.assoc, hf, ← Category.assoc, hβ, hβ', spMap_comp', hσ]
    · show _ ≫ m.φ = _
      rw [hm, ← Category.assoc, hM', Category.assoc, a, Category.assoc]
    · show _ ≫ m.φ = _
      rw [hm, ← Category.assoc, hA', Category.assoc, b, Category.assoc]

variable (Xo jK) in

def Grp : Type := {f : Xo.X ⟶ Xo.X // ∃ g σ, Twist Xo jK g σ f}

instance : One (Grp Xo jK) := ⟨⟨𝟙 _, _, _, Twist.one⟩⟩

instance : Mul (Grp Xo jK) := ⟨fun a c => ⟨a.1 ≫ c.1, by
  obtain ⟨g, σ, h⟩ := a.2
  obtain ⟨g', σ', h'⟩ := c.2
  exact ⟨_, _, h.mul h'⟩⟩⟩

/- English proof (translation)
Take `⟨g, σ, h⟩` from `a.2`. Take `⟨g', σ', f', h', e⟩` from `h.exists_inv hpq hj`. Conclude with `⟨⟨f', g', σ', h'⟩, Subtype.ext e⟩`.
-/
theorem Grp.exists_inv (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) (a : Grp Xo jK) :
    ∃ c : Grp Xo jK, a * c = 1 := by
  obtain ⟨g, σ, h⟩ := a.2
  obtain ⟨g', σ', f', h', e⟩ := h.exists_inv hpq hj
  exact ⟨⟨f', g', σ', h'⟩, Subtype.ext e⟩

@[reducible] def Grp.group (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) :
    Group (Grp Xo jK) :=
  letI : Inv (Grp Xo jK) := ⟨fun a => (Grp.exists_inv hpq hj a).choose⟩
  Group.ofRightAxioms (fun _ _ _ => Subtype.ext (Category.assoc _ _ _)) (fun _ => Subtype.ext (Category.comp_id _))
    fun a => (Grp.exists_inv hpq hj a).choose_spec

/- English proof (translation)
Take `⟨Q, _, π, hπ⟩` from `exists_finite_mod D (level_pos l₂)`. Take `⟨Q', _, π', hπ'⟩` from `exists_finite_mod D l₂.A_pos`. Use `haveI : NeZero l₂.A := ⟨l₂.A_pos.ne'⟩`. Use `choose g σ h using fun a : Grp Xo jK => a.2`. Use `Finite.of_injective (fun a => ((π ((g a).f l₂.M), π' ((g a).f l₂.A), ((g a).ν l₂.A : ZMod l₂.A)) : Q × Q' × ZMod l₂.A)) fun a c hac => Subtype.ext ?_` and prove the remaining obligations.

Simplify using `only [Prod.mk.injEq] at hac`. Use `(h a).unique hpq hj (h c) (ringHom_ext (rho_of_fix hj ((h a).fix.trans (h c).fix.symm)) ?_) (fun x => eta_congr _ (LevelFibre.mem_of_modN l₂ (hπ _ _ hac.1 x))) fun x => etaA_congr _ (hπ' _ _ hac.2.1 x)` and prove the remaining obligations. Rewrite using `[(h a).root, (h c).root]`. Conclude with `zeta_zpow_congr l₂ ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hac.2.2.symm)`.
-/
theorem Grp.finite (hpq : 1 ≤ D.p + D.q) (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) : Finite (Grp Xo jK) := by
  obtain ⟨Q, _, π, hπ⟩ := exists_finite_mod D (level_pos l₂)
  obtain ⟨Q', _, π', hπ'⟩ := exists_finite_mod D l₂.A_pos
  haveI : NeZero l₂.A := ⟨l₂.A_pos.ne'⟩
  choose g σ h using fun a : Grp Xo jK => a.2
  refine Finite.of_injective (fun a => ((π ((g a).f l₂.M), π' ((g a).f l₂.A), ((g a).ν l₂.A : ZMod l₂.A)) :
    Q × Q' × ZMod l₂.A)) fun a c hac => Subtype.ext ?_
  simp only [Prod.mk.injEq] at hac
  refine (h a).unique hpq hj (h c) (ringHom_ext (rho_of_fix hj ((h a).fix.trans (h c).fix.symm)) ?_)
    (fun x => eta_congr _ (LevelFibre.mem_of_modN l₂ (hπ _ _ hac.1 x))) fun x => etaA_congr _ (hπ' _ _ hac.2.1 x)
  rw [(h a).root, (h c).root]
  exact zeta_zpow_congr l₂ ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hac.2.2.symm)

end Action

/- English proof (translation)
Introduce `hL _ E _ _ _ H D l l₂ Xo jK hpq hd hj`. Establish `hν : ∀ a : Grp Xo jK, ∃ ν : SABMap Xo.univ.t Xo.univ.t a.1, Lowers l Xo.univ (fun x => Xo.univ.eta x ^ (l₂.M / l.M)) (fun x => Xo.univ.etaA x ^ (l₂.A / l.A)) a.1 ν.φ` using `fun a => by`. Take `⟨g, σ, h⟩` from `a.2`. Take `⟨ν, b, c⟩` from `h.map`. Conclude with `⟨ν, h.lowers ν b c⟩`.

Use `choose ν hν using hν`. Establish `rig : ∀ (f : Xo.X ⟶ Xo.X) (m m' : SABMap Xo.univ.t Xo.univ.t f), (∀ x, (Xo.univ.eta x ^ (l₂.M / l.M)).left ≫ m.φ = (Xo.univ.eta x ^ (l₂.M / l.M)).left ≫ m'.φ) → m.φ = m'.φ` using `fun f m m' h => obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ (lowUniv Xo hd hj) (lowUniv Xo hd hj) f (Or.inl (reduced Xo)) m m' fun x => ⟨_, h x, rfl⟩`. Use `⟨Grp Xo jK, Grp.group hpq hj, Grp.finite hpq hj, fun a => a.1, ν, rfl, fun _ _ => rfl, ?_, fun a c => ?_, fun a => ?_, hν, fun k _ _ y a hy => ?_, fun K _ _ y y' t mu mu' eM eA hs hl hl' => ?_⟩` and prove the remaining obligations. Conclude with `rig (𝟙 _) (ν 1) (ObjLower.sabId _) fun x => ((hν 1).1 x).trans ((Category.id_comp _).trans (Category.comp_id _).symm)`. Take `⟨n, hn⟩` from `exists_comp_sabMap (ν a) (ν c) rfl`.

Use `(rig (a.1 ≫ c.1) (ν (a * c)) n fun x => ((hν (a * c)).1 x).trans ?_).trans hn` and prove the remaining obligations. Establish `h₁` using `(hν a).1 x`. Establish `h₂` using `(hν c).1 x`. Simplify using `only at h₁ h₂`. Rewrite using `[hn, ← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]`.

Both sides reduce to the same expression. Take `⟨g, σ, h⟩` from `a.2`. Rewrite using `[← Category.assoc, h.comm, Category.assoc, spMap_comp', h.fix]`. Take `⟨g, σ, h⟩` from `a.2`. Conclude with `Subtype.ext (h.eq_id_of_fixed hL hpq hd hj y hy)`.

Take `⟨g, σ, f, h, e⟩` from `exists_twist_of_lowers hL hpq hd hj y y' t mu mu' eM eA hs hl hl'`. Conclude with `⟨⟨f, g, σ, h⟩, e⟩`.
-/
theorem exists_group_action : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (jK : KA l →+* KA l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) → ∃ (Ga : Type) (_ : Group Ga) (_ : Finite Ga) (ρ : Ga → (Xo₂.X ⟶ Xo₂.X)) (ν : ∀ a, SABMap Xo₂.univ.t Xo₂.univ.t (ρ a)), ρ 1 = 𝟙 _ ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ (ν 1).φ = 𝟙 _ ∧ (∀ a c, (ν (a * c)).φ = (ν a).φ ≫ (ν c).φ) ∧ (∀ a, ρ a ≫ Xo₂.s ≫ spMap jK = Xo₂.s ≫ spMap jK) ∧ (∀ a, Lowers l Xo₂.univ (fun x => Xo₂.univ.eta x ^ (l₂.M / l.M)) (fun x => Xo₂.univ.etaA x ^ (l₂.A / l.A)) (ρ a) (ν a).φ) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo₂.X) (a : Ga), y ≫ ρ a = y → a = 1) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ Xo₂.X) (t : SAB H (Sp K)) (mu : SABMap t Xo₂.univ.t y) (mu' : SABMap t Xo₂.univ.t y') (eM eA : D.La → (𝟙_ (Over (Sp K)) ⟶ t.G)), y ≫ Xo₂.s ≫ spMap jK = y' ≫ Xo₂.s ≫ spMap jK → Lowers l Xo₂.univ eM eA y mu.φ → Lowers l Xo₂.univ eM eA y' mu'.φ → ∃ a, y ≫ ρ a = y' := by
  intro hL _ E _ _ _ H D l l₂ Xo jK hpq hd hj
  have hν : ∀ a : Grp Xo jK, ∃ ν : SABMap Xo.univ.t Xo.univ.t a.1,
      Lowers l Xo.univ (fun x => Xo.univ.eta x ^ (l₂.M / l.M)) (fun x => Xo.univ.etaA x ^ (l₂.A / l.A)) a.1 ν.φ :=
    fun a => by
      obtain ⟨g, σ, h⟩ := a.2
      obtain ⟨ν, b, c⟩ := h.map
      exact ⟨ν, h.lowers ν b c⟩
  choose ν hν using hν
  have rig : ∀ (f : Xo.X ⟶ Xo.X) (m m' : SABMap Xo.univ.t Xo.univ.t f),
      (∀ x, (Xo.univ.eta x ^ (l₂.M / l.M)).left ≫ m.φ = (Xo.univ.eta x ^ (l₂.M / l.M)).left ≫ m'.φ) → m.φ = m'.φ :=
    fun f m m' h => obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ (lowUniv Xo hd hj) (lowUniv Xo hd hj) f
      (Or.inl (reduced Xo)) m m' fun x => ⟨_, h x, rfl⟩
  refine ⟨Grp Xo jK, Grp.group hpq hj, Grp.finite hpq hj, fun a => a.1, ν, rfl, fun _ _ => rfl, ?_, fun a c => ?_,
    fun a => ?_, hν, fun k _ _ y a hy => ?_, fun K _ _ y y' t mu mu' eM eA hs hl hl' => ?_⟩
  · exact rig (𝟙 _) (ν 1) (ObjLower.sabId _) fun x =>
      ((hν 1).1 x).trans ((Category.id_comp _).trans (Category.comp_id _).symm)
  · obtain ⟨n, hn⟩ := exists_comp_sabMap (ν a) (ν c) rfl
    refine (rig (a.1 ≫ c.1) (ν (a * c)) n fun x => ((hν (a * c)).1 x).trans ?_).trans hn
    have h₁ := (hν a).1 x
    have h₂ := (hν c).1 x
    simp only at h₁ h₂
    rw [hn, ← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
    rfl
  · obtain ⟨g, σ, h⟩ := a.2
    rw [← Category.assoc, h.comm, Category.assoc, spMap_comp', h.fix]
  · obtain ⟨g, σ, h⟩ := a.2
    exact Subtype.ext (h.eq_id_of_fixed hL hpq hd hj y hy)
  · obtain ⟨g, σ, f, h, e⟩ := exists_twist_of_lowers hL hpq hd hj y y' t mu mu' eM eA hs hl hl'
    exact ⟨⟨f, g, σ, h⟩, e⟩

end GlobalTheory.LevelGroup
