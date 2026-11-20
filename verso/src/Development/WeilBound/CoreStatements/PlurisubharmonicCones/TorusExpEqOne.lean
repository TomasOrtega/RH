import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalNearBoundary
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeSpans
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelian
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.PerSpan GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.CompanionTheory.Ar.QuotLoc.Lat

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `GlobalTheory.AlphaPair.exists_ptEquiv hp (epsAt (𝟙 (Sp ℂ))).hom (epsAt z).hom (by simp)`. Take `⟨ρ₀, hρ₀⟩` from `GlobalTheory.AlphaPair.exists_ptEquiv hp (𝟙 (Sp ℂ)) z (Category.id_comp _).symm`. Establish `h1 : (1 : Over.mk z ⟶ G).left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G').left ≫ φ`. Rewrite using `[← hρ₀, map_one]`. Establish `tan : ∀ v : epsAt (𝟙 (Sp ℂ)) ⟶ G', IsTanAt G z (ρ v) ↔ IsTanAt G' (𝟙 _) v`.

Introduce `v`. Unfold `IsTanAt`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `hp.1.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[← h1, ← h, Category.assoc]`. Conclude with `congrArg _ (hρ v).symm`. Rewrite using `[Category.assoc, Over.w v, Over.w (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G')]`. Conclude with `TorusModel.fst_eps (𝟙 (Sp ℂ))`. Introduce `h`.

Rewrite using `[h1, ← h, Category.assoc]`. Conclude with `congrArg _ (hρ v)`. Use `choose f hf using fun x => Mz.onto _ ((tan _).2 (MV.tan x))`. Establish `hl : ∀ x, (Mz.pt (f x)).left = (MV.pt x).left ≫ φ` using `fun x => by`. Rewrite using `[hf]`.

Conclude with `hρ _`. Set `F : V →ₗ[ℂ] V'` to `{ toFun := f map_add' := fun x y => Mz.inj (by`. Rewrite using `[Mz.add, hf, hf, hf, MV.add]`. Conclude with `map_mul ρ _ _)`. Use the proof step `map_smul' := fun c x => Mz.inj (Over.OverMorphism.ext (by`.

Rewrite using `[RingHom.id_apply, Mz.smul, hl, hl, MV.smul, Category.assoc])) }`. Use `⟨LinearEquiv.ofBijective F ⟨fun x y h => ?_, fun y => ?_⟩, hl⟩` and prove the remaining obligations. Establish `h' : f x = f y` using `h`. Use `MV.inj (ρ.injective ?_)` and prove the remaining obligations. Conclude with `(hf x).symm.trans ((congrArg Mz.pt h').trans (hf y))`.

Take `⟨x, hx⟩` from `MV.onto (ρ.symm (Mz.pt y)) ((tan _).1 (by rw [ρ.apply_symm_apply]; exact Mz.tan y))`. Use `⟨x, Mz.inj ?_⟩` and prove the remaining obligations. Use `show Mz.pt (f x) = _`. Rewrite using `[hf, hx]`. Conclude with `ρ.apply_symm_apply _`.
-/
theorem lie_equiv {S : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over (Sp ℂ)} [GrpObj G'] {z : Sp ℂ ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G z φ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (MV : LieModel G' (𝟙 (Sp ℂ)) V) (Mz : LieModel G z V') :
    ∃ Φ : V ≃ₗ[ℂ] V', ∀ x, (Mz.pt (Φ x)).left = (MV.pt x).left ≫ φ := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hp (epsAt (𝟙 (Sp ℂ))).hom (epsAt z).hom (by simp)
  obtain ⟨ρ₀, hρ₀⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hp (𝟙 (Sp ℂ)) z (Category.id_comp _).symm
  have h1 : (1 : Over.mk z ⟶ G).left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G').left ≫ φ := by
    rw [← hρ₀, map_one]
  have tan : ∀ v : epsAt (𝟙 (Sp ℂ)) ⟶ G', IsTanAt G z (ρ v) ↔ IsTanAt G' (𝟙 _) v := by
    intro v
    unfold IsTanAt
    constructor
    · intro h
      refine hp.1.hom_ext ?_ ?_
      · rw [← h1, ← h, Category.assoc]
        exact congrArg _ (hρ v).symm
      · rw [Category.assoc, Over.w v, Over.w (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G')]
        exact TorusModel.fst_eps (𝟙 (Sp ℂ))
    · intro h
      rw [h1, ← h, Category.assoc]
      exact congrArg _ (hρ v)
  choose f hf using fun x => Mz.onto _ ((tan _).2 (MV.tan x))
  have hl : ∀ x, (Mz.pt (f x)).left = (MV.pt x).left ≫ φ := fun x => by
    rw [hf]
    exact hρ _
  let F : V →ₗ[ℂ] V' :=
    { toFun := f
      map_add' := fun x y => Mz.inj (by
        rw [Mz.add, hf, hf, hf, MV.add]
        exact map_mul ρ _ _)
      map_smul' := fun c x => Mz.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, Mz.smul, hl, hl, MV.smul, Category.assoc])) }
  refine ⟨LinearEquiv.ofBijective F ⟨fun x y h => ?_, fun y => ?_⟩, hl⟩
  · have h' : f x = f y := h
    refine MV.inj (ρ.injective ?_)
    exact (hf x).symm.trans ((congrArg Mz.pt h').trans (hf y))
  · obtain ⟨x, hx⟩ := MV.onto (ρ.symm (Mz.pt y)) ((tan _).1 (by rw [ρ.apply_symm_apply]; exact Mz.tan y))
    refine ⟨x, Mz.inj ?_⟩
    show Mz.pt (f x) = _
    rw [hf, hx]
    exact ρ.apply_symm_apply _

/- English proof (translation)
Take `⟨v, H⟩` from `GlobalTheory.VerticalDeriv.exists_isDerivAt0 (isHolTo_torusExp β) (fun a => δ (β a))`. Establish `hv` using `GlobalTheory.VerticalDeriv.isDerivAt0_vertical (splitTorus (Sp ℂ) X).hom (𝟙 (Sp ℂ)) (e := fun w => (torusExp β w).left) (fun w => Over.w (torusExp β w)) H`. Set `v' : epsAt (𝟙 (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X` to `Over.homMk v hv`. Establish `h0 : torusExp β (0 : Fin d → ℂ) = 1`. Use `torusExp_add β (0 : Fin d → ℂ) 0` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`. Establish `ht : IsTanAt (splitTorus (Sp ℂ) X) (𝟙 _) v'` using `H.1.trans (congrArg (·.left) h0)`. Take `⟨δ', hδ'⟩` from `MT.onto v' ht`. Establish `e : δ' = δ`.

Use extensionality with `χ`. Establish `H2` using `GlobalTheory.FibreDeriv.isDerivAt0_comp H (pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)))`. Establish `h3` using `H2.2 ⊤ le_top ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))`. Establish `h4 : (fun z => valAt' ((torusExp β z).left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ))) ⊤ ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))) = fun z => Complex.exp (pairing β z χ)`. Use function extensionality and compare the values at `fun z => (valAt'_torusFst' _ _).trans (torusExp_hol_char β z χ)`.

Set `Lc : (Fin d → ℂ) →L[ℂ] ℂ` to `∑ a, ((β.repr χ a : ℤ) : ℂ) • ContinuousLinearMap.proj a`. Establish `hLc : ∀ w, Lc w = pairing β w χ` using `fun w => by simp [Lc, pairing]`. Establish `h5 : fderiv ℂ (fun z => Complex.exp (pairing β z χ)) 0 (fun a => δ (β a)) = δ χ`. Establish `: HasFDerivAt (fun z => Complex.exp (Lc z)) (Complex.exp (Lc 0) • Lc) 0` using `Lc.hasFDerivAt.cexp`. Simplify using `only [hLc] at this`.

Rewrite using `[this.fderiv, ContinuousLinearMap.smul_apply, hLc, ← hLc 0, map_zero, Complex.exp_zero, one_smul]`. Use `conv_rhs => rw [← β.sum_repr χ, map_sum]`. Simplify using `only [pairing, map_zsmul, zsmul_eq_mul]`. Establish `h6` using `hMT δ' χ`. Rewrite `h6` using `[hδ']`.

Establish `h7 : (charVal v' χ).snd = δ' χ` using `by rw [h6]; simp`. Rewrite using `[← h7, ← h5, ← h4]`. Use `Eq.trans ?_ h3` and prove the remaining obligations. Use `congr 1`. Unfold `charVal`.

Use `set g : Sp (DualNumber ℂ) ⟶ Spec (torusRing ZU X) := v'.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)) with hg`. Establish `h : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom = Spec.preimage g` using `by conv_lhs => rw [← Spec.map_preimage g]`. Rewrite using `[Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]`. Establish `h8 : g.appTop = g.appLE ⊤ ⊤ le_top`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`.

Both sides reduce to the same expression. Rewrite using `[← h, h8]`. Both sides reduce to the same expression. Rewrite using `[← e, hδ', e]`. Conclude with `H`.
-/
theorem torus_deriv {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X)
    (MT : LieModel (splitTorus (Sp ℂ) X) (𝟙 _) (X →+ ℂ)) (hMT : IsCocharLie MT) (δ : X →+ ℂ) :
    IsDerivAt0 (fun w => (torusExp β w).left) (fun a => δ (β a)) (MT.pt δ).left := by
  obtain ⟨v, H⟩ := GlobalTheory.VerticalDeriv.exists_isDerivAt0 (isHolTo_torusExp β) (fun a => δ (β a))
  have hv := GlobalTheory.VerticalDeriv.isDerivAt0_vertical (splitTorus (Sp ℂ) X).hom (𝟙 (Sp ℂ))
    (e := fun w => (torusExp β w).left) (fun w => Over.w (torusExp β w)) H
  let v' : epsAt (𝟙 (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X := Over.homMk v hv
  have h0 : torusExp β (0 : Fin d → ℂ) = 1 := by
    have := torusExp_add β (0 : Fin d → ℂ) 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have ht : IsTanAt (splitTorus (Sp ℂ) X) (𝟙 _) v' := H.1.trans (congrArg (·.left) h0)
  obtain ⟨δ', hδ'⟩ := MT.onto v' ht
  have e : δ' = δ := by
    ext χ
    have H2 := GlobalTheory.FibreDeriv.isDerivAt0_comp H (pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)))
    have h3 := H2.2 ⊤ le_top ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))
    have h4 : (fun z => valAt' ((torusExp β z).left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ))) ⊤
        ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))) =
        fun z => Complex.exp (pairing β z χ) :=
      funext fun z => (valAt'_torusFst' _ _).trans (torusExp_hol_char β z χ)
    let Lc : (Fin d → ℂ) →L[ℂ] ℂ := ∑ a, ((β.repr χ a : ℤ) : ℂ) • ContinuousLinearMap.proj a
    have hLc : ∀ w, Lc w = pairing β w χ := fun w => by simp [Lc, pairing]
    have h5 : fderiv ℂ (fun z => Complex.exp (pairing β z χ)) 0 (fun a => δ (β a)) = δ χ := by
      have : HasFDerivAt (fun z => Complex.exp (Lc z)) (Complex.exp (Lc 0) • Lc) 0 := Lc.hasFDerivAt.cexp
      simp only [hLc] at this
      rw [this.fderiv, ContinuousLinearMap.smul_apply, hLc, ← hLc 0, map_zero, Complex.exp_zero, one_smul]
      conv_rhs => rw [← β.sum_repr χ, map_sum]
      simp only [pairing, map_zsmul, zsmul_eq_mul]
    have h6 := hMT δ' χ
    rw [hδ'] at h6
    have h7 : (charVal v' χ).snd = δ' χ := by rw [h6]; simp
    rw [← h7, ← h5, ← h4]
    refine Eq.trans ?_ h3
    congr 1
    unfold charVal
    set g : Sp (DualNumber ℂ) ⟶ Spec (torusRing ZU X) :=
      v'.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)) with hg
    have h : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom = Spec.preimage g := by
      conv_lhs => rw [← Spec.map_preimage g]
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    have h8 : g.appTop = g.appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [← h, h8]
    rfl
  rw [← e, hδ', e]
  exact H

/- English proof (translation)
Establish `hT : ∀ χ : X, torusHom β w (Multiplicative.ofAdd χ) = expUnit (pairing β w χ)` using `fun χ => rfl`. Establish `hE : torusExp β w = (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))).symm (torusHom β w)` using `rfl`. Prove the components needed by the constructor for the conclusion. Introduce `h1`. Establish `hH : torusHom β w = 1`.

Establish `h0` using `congrArg (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))) h1`. Rewrite `h0` using `[hE, MulEquiv.apply_symm_apply, map_one]`. Conclude with `h0`. Establish `hexp : ∀ a, Complex.exp (w a) = 1`. Introduce `a`.

Establish `h2` using `congrArg (fun f => f (Multiplicative.ofAdd (β a))) hH`. Simplify using `only [hT, MonoidHom.one_apply, pairing_basis] at h2`. Establish `h3` using `gamma_expUnit (w a)`. Rewrite `h3` using `[h2, Units.val_one, map_one]`. Conclude with `h3.symm`.

Use `choose n hn using fun a => Complex.exp_eq_one_iff.1 (hexp a)`. Use `⟨(β.constr ℤ n).toAddMonoidHom, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Rewrite using `[hn a]`. Simplify using `only [LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨δ, rfl⟩`. Establish `hH : torusHom β (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) = 1`. Apply `monoidHom_ext_basis β` to reduce the goal to its premises. Introduce `a`.

Rewrite using `[hT, pairing_basis, MonoidHom.one_apply]`. Apply `expUnit_eq_one` to reduce the goal to its premises. Use `show Complex.exp (2 * ↑Real.pi * Complex.I * (δ (β a) : ℂ)) = 1`. Rewrite using `[mul_comm]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I (δ (β a))`.

Rewrite using `[hE, hH, map_one]`.
-/
theorem torusExp_eq_one {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X) (w : Fin d → ℂ) :
    torusExp β w = 1 ↔ ∃ δ : X →+ ℤ, w = fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ) := by
  have hT : ∀ χ : X, torusHom β w (Multiplicative.ofAdd χ) = expUnit (pairing β w χ) := fun χ => rfl
  have hE : torusExp β w =
      (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))).symm (torusHom β w) := rfl
  constructor
  · intro h1
    have hH : torusHom β w = 1 := by
      have h0 := congrArg (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))) h1
      rw [hE, MulEquiv.apply_symm_apply, map_one] at h0
      exact h0
    have hexp : ∀ a, Complex.exp (w a) = 1 := by
      intro a
      have h2 := congrArg (fun f => f (Multiplicative.ofAdd (β a))) hH
      simp only [hT, MonoidHom.one_apply, pairing_basis] at h2
      have h3 := gamma_expUnit (w a)
      rw [h2, Units.val_one, map_one] at h3
      exact h3.symm
    choose n hn using fun a => Complex.exp_eq_one_iff.1 (hexp a)
    refine ⟨(β.constr ℤ n).toAddMonoidHom, ?_⟩
    funext a
    rw [hn a]
    simp only [LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis]
    ring
  · rintro ⟨δ, rfl⟩
    have hH : torusHom β (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) = 1 := by
      apply monoidHom_ext_basis β
      intro a
      rw [hT, pairing_basis, MonoidHom.one_apply]
      apply expUnit_eq_one
      show Complex.exp (2 * ↑Real.pi * Complex.I * (δ (β a) : ℂ)) = 1
      rw [mul_comm]
      exact Complex.exp_int_mul_two_pi_mul_I (δ (β a))
    rw [hE, hH, map_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {t : SAB H (Sp R)}
  {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

/- English proof (translation)
Use `letI := P.τ.grpB`. Use `letI := P.τ.addCommGroup`. Use `haveI := P.τ.free`. Use `haveI := P.τ.finite`. Use `haveI := P.τ.q_hom`.

Use `haveI := P.τ.i_hom`. Use `haveI : IsMonHom P.e.hom := P.e_hom`. Set `β` to `Module.finBasis ℤ P.τ.X`. Take `⟨ρ, hρ⟩` from `GlobalTheory.AlphaPair.exists_ptEquiv P.m.cart (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm`. Set `v : (Fin (Module.finrank ℤ P.τ.X) → ℂ) → (Over.mk (spMap (ψ b)) ⟶ t.G)` to `fun z => ρ (torusExp β z ≫ P.τ.i)`.

Establish `vadd : ∀ z w, v (z + w) = v z * v w` using `fun z w => by show ρ (torusExp β (z + w) ≫ P.τ.i) = ρ (torusExp β z ≫ P.τ.i) * ρ (torusExp β w ≫ P.τ.i)`. Rewrite using `[torusExp_add, MonObj.mul_comp]`. Conclude with `map_mul ρ _ _`. Establish `vl : (fun z => (v z).left) = fun z => (torusExp β z).left ≫ P.τ.i.left ≫ P.m.φ` using `funext fun z => by`. Rewrite using `[← Category.assoc]`.

Conclude with `hρ _`. Establish `vhol : IsHolTo Set.univ (fun z => (v z).left)`. Rewrite using `[vl]`. Conclude with `ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (isHolTo_torusExp β) _`. Take `⟨h', -, hh⟩` from `exists_linear_lift_of_additive_family R t.G g 0 M Set.univ (fun _ => ψ b) (famExpAtPoint e hb) _ Set.univ (fun _ z => v z) isOpen_univ subset_rfl (fun _ _ z w => vadd z w) (isHolTo_snd (V := Fin 0 → ℂ) (X := t.G.left) (c := fun z => (v z).left) vhol)`.

Take `⟨hex, -, hder⟩` from `hh 0 trivial`. Establish `hex' : ∀ z, e.ex b (h' 0 z) = v z` using `hex`. Establish `hder' : ∀ z w, IsDerivAt0 (fun z => (v z).left) z w ↔ IsDerivAt0 (fun z => (e.ex b z).left) (h' 0 z) w` using `hder`. Establish `hmono : Mono P.τ.i`. Use `⟨fun a a' haa => P.τ.isKernel.hom_ext haa (toUnit_unique _ _)⟩` and prove the remaining obligations.

Establish `hQ1 : ∀ z : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X, (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = 1`. Introduce `z`. Establish `h1 : P.τ.i ≫ P.τ.q = toUnit _ ≫ η` using `P.τ.isKernel.w`. Establish `h2 : z ≫ P.τ.i ≫ P.τ.q = 1`. Rewrite using `[h1, ← Category.assoc, Hom.one_def]`.

Use `congr 1`. Conclude with `toUnit_unique _ _`. Combine the equalities or inequalities in the displayed calculation. Use `⟨_, β, h' 0, fun MT hMT δ => ?_, fun z => ?_, fun A _ φ g' u ℓ hA hl y => ?_⟩` and prove the remaining obligations. Establish `d1` using `GlobalTheory.FibreDeriv.isDerivAt0_comp (torus_deriv β MT hMT δ) (P.τ.i.left ≫ P.m.φ)`.

Rewrite `d1` using `[← vl]`. Establish `d2` using `(hder' _ _).1 d1`. Rewrite using `[Over.comp_left, Category.assoc]`. Conclude with `GlobalTheory.VerticalDeriv.isDerivAt0_unique (DiffL.isDerivAt0_pt e hb Mz hL _) d2`. Rewrite using `[← torusExp_eq_one] show e.ex b (h' 0 z) = 1 ↔ _`.

Rewrite using `[hex']`. Use `(map_eq_one_iff ρ ρ.injective).trans ⟨fun h1 => ?_, fun h1 => ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono P.τ.i, MonObj.one_comp]`. Conclude with `h1`. Use `show torusExp β z ≫ P.τ.i = 1`.

Rewrite using `[h1, MonObj.one_comp]`. Take `⟨ρ', hρ'⟩` from `GlobalTheory.AlphaPair.exists_ptEquiv hA (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (Category.id_comp _).symm`. Establish `hl' : ∀ y (s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G), ρ s = e.ex b y → ρ' (u.ex (ℓ y)) = s ≫ P.τ.q ≫ P.e.hom` using `fun y s hs => Over.OverMorphism.ext ((hρ' _).trans (hl y s ((hρ s).symm.trans (congrArg (·.left) hs))))`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Take `⟨Γ₀, hΓ, hd, -, -⟩` from `GlobalTheory.T.period_lattice_discrete_free R t.G g n M B ψ e b hb`. Establish `hcount : (e.per b).Countable`. Rewrite using `[← hΓ]`. Use `haveI := hd`. Establish `: Countable Γ₀` using `countable_of_Lindelof_of_discrete`.

Conclude with `Set.countable_coe_iff.1 this`. Establish `h0 : (LinearMap.range (h' 0)).mkQ y = 0`. Use `GlobalTheory.eq_zero_of_forall_smul_mem_countable (hcount.image (LinearMap.range (h' 0)).mkQ) fun c => ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `ρ.surjective (e.ex b (c • y))`. Establish `h1` using `hl' _ s hs`.

Rewrite `h1` using `[map_smul, hy, smul_zero, (u.ker 0).2 u.Λ.zero_mem]`. Establish `h2 : s ≫ P.τ.q ≫ P.e.hom = 1` using `h1.symm.trans (map_one ρ')`. Establish `h3 : s ≫ P.τ.q = 1`. Rewrite using `[← cancel_mono P.e.hom, MonObj.one_comp, Category.assoc]`. Conclude with `h2`.

Set `τ₀ : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X` to `P.τ.isKernel.lift s (toUnit _) (by rw [h3, Hom.one_def]; rfl)`. Establish `hτ : τ₀ ≫ P.τ.i = s` using `P.τ.isKernel.lift_fst _ _ _`. Take `⟨w, hw⟩` from `torusExp_surjective β τ₀`. Establish `h4 : e.ex b (h' 0 w) = e.ex b (c • y)`. Rewrite using `[hex', ← hs, ← hτ, ← hw]`.

Use `⟨c • y - h' 0 w, ?_, ?_⟩` and prove the remaining obligations. Use `show e.ex b _ = 1`. Use `e.add b hb (c • y - h' 0 w) (h' 0 w)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, h4]`. Conclude with `right_eq_mul.1 this`.

Simplify using `only [map_sub, map_smul, Submodule.mkQ_apply]`. Rewrite using `[(Submodule.Quotient.mk_eq_zero (LinearMap.range (h' 0))).2 ⟨w, rfl⟩, sub_zero]`. Establish `: y ∈ LinearMap.range (h' 0)` using `by simpa using h0`. Take `⟨z, hz⟩` from `this`. Conclude with `⟨z, hz.symm⟩`.

Introduce and unpack `⟨z, rfl⟩`. Establish `hcount : (u.Λ : Set (Fin g' → ℂ)).Countable` using `by haveI := u.discrete`. Establish `: Countable u.Λ` using `countable_of_Lindelof_of_discrete`. Conclude with `Set.countable_coe_iff.1 this`. Use `GlobalTheory.eq_zero_of_forall_smul_mem_countable hcount fun c => ?_` and prove the remaining obligations.

Rewrite using `[← map_smul, ← map_smul]`. Use `(u.ker _).1 (ρ'.injective ?_)` and prove the remaining obligations. Conclude with `((hl' _ _ (hex' (c • z)).symm).trans (hQ1 _)).trans (map_one ρ').symm`.
-/
theorem torus_lift (e : FamExp t.G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (P : AbPart t (spMap (ψ b)))
    (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, M.Lifts (ψ b) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1))) :
    letI := P.τ.addCommGroup
    ∃ (d : ℕ) (β : Module.Basis (Fin d) ℤ P.τ.X) (h : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ (MT : LieModel (splitTorus (Sp ℂ) P.τ.X) (𝟙 _) (P.τ.X →+ ℂ)), IsCocharLie MT → ∀ δ : P.τ.X →+ ℂ,
        (Mz.pt (h fun a => δ (β a))).left = (MT.pt δ ≫ P.τ.i).left ≫ P.m.φ) ∧
      (∀ z, h z ∈ e.per b ↔ ∃ δ : P.τ.X →+ ℤ, z = fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) ∧
      ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g')
        (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsGrpPullback A P.tB.G (𝟙 _) φ → IsAbLift e b P φ u ℓ →
        ∀ y, ℓ y = 0 ↔ ∃ z, y = h z := by
  letI := P.τ.grpB
  letI := P.τ.addCommGroup
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  let β := Module.finBasis ℤ P.τ.X
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv P.m.cart (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm
  let v : (Fin (Module.finrank ℤ P.τ.X) → ℂ) → (Over.mk (spMap (ψ b)) ⟶ t.G) := fun z => ρ (torusExp β z ≫ P.τ.i)
  have vadd : ∀ z w, v (z + w) = v z * v w := fun z w => by
    show ρ (torusExp β (z + w) ≫ P.τ.i) = ρ (torusExp β z ≫ P.τ.i) * ρ (torusExp β w ≫ P.τ.i)
    rw [torusExp_add, MonObj.mul_comp]
    exact map_mul ρ _ _
  have vl : (fun z => (v z).left) = fun z => (torusExp β z).left ≫ P.τ.i.left ≫ P.m.φ := funext fun z => by
    rw [← Category.assoc]
    exact hρ _
  have vhol : IsHolTo Set.univ (fun z => (v z).left) := by
    rw [vl]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (isHolTo_torusExp β) _
  obtain ⟨h', -, hh⟩ := exists_linear_lift_of_additive_family R t.G g 0 M Set.univ (fun _ => ψ b)
    (famExpAtPoint e hb) _ Set.univ (fun _ z => v z) isOpen_univ subset_rfl (fun _ _ z w => vadd z w)
    (isHolTo_snd (V := Fin 0 → ℂ) (X := t.G.left) (c := fun z => (v z).left) vhol)
  obtain ⟨hex, -, hder⟩ := hh 0 trivial
  have hex' : ∀ z, e.ex b (h' 0 z) = v z := hex
  have hder' : ∀ z w, IsDerivAt0 (fun z => (v z).left) z w ↔ IsDerivAt0 (fun z => (e.ex b z).left) (h' 0 z) w := hder
  have hmono : Mono P.τ.i := by
    refine ⟨fun a a' haa => P.τ.isKernel.hom_ext haa (toUnit_unique _ _)⟩
  have hQ1 : ∀ z : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X, (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = 1 := by
    intro z
    have h1 : P.τ.i ≫ P.τ.q = toUnit _ ≫ η := P.τ.isKernel.w
    have h2 : z ≫ P.τ.i ≫ P.τ.q = 1 := by
      rw [h1, ← Category.assoc, Hom.one_def]
      congr 1
      exact toUnit_unique _ _
    calc (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = (z ≫ P.τ.i ≫ P.τ.q) ≫ P.e.hom := by simp only [Category.assoc]
      _ = 1 := by rw [h2, MonObj.one_comp]
  refine ⟨_, β, h' 0, fun MT hMT δ => ?_, fun z => ?_, fun A _ φ g' u ℓ hA hl y => ?_⟩
  · have d1 := GlobalTheory.FibreDeriv.isDerivAt0_comp (torus_deriv β MT hMT δ) (P.τ.i.left ≫ P.m.φ)
    rw [← vl] at d1
    have d2 := (hder' _ _).1 d1
    rw [Over.comp_left, Category.assoc]
    exact GlobalTheory.VerticalDeriv.isDerivAt0_unique (DiffL.isDerivAt0_pt e hb Mz hL _) d2
  · rw [← torusExp_eq_one]
    show e.ex b (h' 0 z) = 1 ↔ _
    rw [hex']
    refine (map_eq_one_iff ρ ρ.injective).trans ⟨fun h1 => ?_, fun h1 => ?_⟩
    · rw [← cancel_mono P.τ.i, MonObj.one_comp]
      exact h1
    · show torusExp β z ≫ P.τ.i = 1
      rw [h1, MonObj.one_comp]
  · obtain ⟨ρ', hρ'⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hA (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (Category.id_comp _).symm
    have hl' : ∀ y (s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G), ρ s = e.ex b y → ρ' (u.ex (ℓ y)) = s ≫ P.τ.q ≫ P.e.hom :=
      fun y s hs => Over.OverMorphism.ext ((hρ' _).trans (hl y s ((hρ s).symm.trans (congrArg (·.left) hs))))
    constructor
    · intro hy
      obtain ⟨Γ₀, hΓ, hd, -, -⟩ := GlobalTheory.T.period_lattice_discrete_free R t.G g n M B ψ e b hb
      have hcount : (e.per b).Countable := by
        rw [← hΓ]
        haveI := hd
        have : Countable Γ₀ := countable_of_Lindelof_of_discrete
        exact Set.countable_coe_iff.1 this
      have h0 : (LinearMap.range (h' 0)).mkQ y = 0 := by
        refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (hcount.image (LinearMap.range (h' 0)).mkQ) fun c => ?_
        obtain ⟨s, hs⟩ := ρ.surjective (e.ex b (c • y))
        have h1 := hl' _ s hs
        rw [map_smul, hy, smul_zero, (u.ker 0).2 u.Λ.zero_mem] at h1
        have h2 : s ≫ P.τ.q ≫ P.e.hom = 1 := h1.symm.trans (map_one ρ')
        have h3 : s ≫ P.τ.q = 1 := by
          rw [← cancel_mono P.e.hom, MonObj.one_comp, Category.assoc]
          exact h2
        let τ₀ : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X :=
          P.τ.isKernel.lift s (toUnit _) (by rw [h3, Hom.one_def]; rfl)
        have hτ : τ₀ ≫ P.τ.i = s := P.τ.isKernel.lift_fst _ _ _
        obtain ⟨w, hw⟩ := torusExp_surjective β τ₀
        have h4 : e.ex b (h' 0 w) = e.ex b (c • y) := by
          rw [hex', ← hs, ← hτ, ← hw]
        refine ⟨c • y - h' 0 w, ?_, ?_⟩
        · show e.ex b _ = 1
          have := e.add b hb (c • y - h' 0 w) (h' 0 w)
          rw [sub_add_cancel, h4] at this
          exact right_eq_mul.1 this
        · simp only [map_sub, map_smul, Submodule.mkQ_apply]
          rw [(Submodule.Quotient.mk_eq_zero (LinearMap.range (h' 0))).2 ⟨w, rfl⟩, sub_zero]
      have : y ∈ LinearMap.range (h' 0) := by simpa using h0
      obtain ⟨z, hz⟩ := this
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      have hcount : (u.Λ : Set (Fin g' → ℂ)).Countable := by
        haveI := u.discrete
        have : Countable u.Λ := countable_of_Lindelof_of_discrete
        exact Set.countable_coe_iff.1 this
      refine GlobalTheory.eq_zero_of_forall_smul_mem_countable hcount fun c => ?_
      rw [← map_smul, ← map_smul]
      refine (u.ker _).1 (ρ'.injective ?_)
      exact ((hl' _ _ (hex' (c • z)).symm).trans (hQ1 _)).trans (map_one ρ').symm

end LevelTowerAlt.Val
