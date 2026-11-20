import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRootStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjEqAddKummerTorusTorsionPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaFixesAbelianPartOfTorsionPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaFixedDvdValuationOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.TauFormGen

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues GlobalTheory.TauForm

/- English proof (translation)
Introduce `R _ _ _ hRb G _ _ hG D A U V _ _ _ _ hVb G' _ _ hG' D' A' U' g gK hgK F _ _ _ _ hF k hk ϖ hϖ O φ σ π hφ eφ hσ hπ hζ ρ e hW hGal hT a b x x' hx hx'`. Take `⟨hR, _⟩` from `hRb`. Take `⟨hV, _⟩` from `hVb`. Establish `hk0 : k ≠ 0` using `by rintro rfl; simp at hk`. Establish `hk1 : 1 ≤ k` using `Nat.one_le_iff_ne_zero.2 hk0`.

Establish `hkO : IsUnit (k : O)` using `by simpa using hk.map (φ.comp g)`. Establish `hB` using `D.tau_bimult`. Establish `hB'` using `D'.tau_bimult`. Take `⟨f, ⟨i₁, s₁, -, a₁, w₁⟩, p₁⟩` from `GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1`. Take `⟨f', ⟨i₂, s₂, -, a₂, w₂⟩, p₂⟩` from `GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV D' A' G' hG' U' F k hk1`.

Establish `wt₁ : ∀ (p p' : QkPt D.toPre F k) (τ : Multiplicative D.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g → WeilIs A.A A.L (k : ℤ) (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y)))` using `fun p p' τ hy hτ => (w₁ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)`. Establish `wt₂ : ∀ (p p' : QkPt D'.toPre F k) (τ : Multiplicative D'.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g → WeilIs A'.A A'.L (k : ℤ) (f' p) (f' p') (unitOn (τ (Multiplicative.ofAdd p'.y)))` using `fun p p' τ hy hτ => (w₂ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)`. Establish `c₁ : ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left`. Introduce `σ p p' hpp'`. Take `⟨-, hx, hiff⟩` from `GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D A G hG U F F σ k hk1 p`.

Take `⟨y, hy⟩` from `hx (f p)`. Establish `: y = f p'` using `(i₁ p' y).1 ((hiff p' (f p) y hpp' hy).1 ((i₁ p (f p)).2 rfl))`. Rewrite using `[← this, hy]`. Establish `c₂ : ∀ (σ : F →ₐ[FractionRing V] F) p p', QkExt σ.toRingHom p p' → (f' p').left = spMap σ.toRingHom ≫ (f' p).left`. Introduce `σ p p' hpp'`.

Take `⟨-, hx, hiff⟩` from `GlobalTheory.UT.Cl.galois_holds V (maximalIdeal V) hV D' A' G' hG' U' F F σ k hk1 p`. Take `⟨y, hy⟩` from `hx (f' p)`. Establish `: y = f' p'` using `(i₂ p' y).1 ((hiff p' (f' p) y hpp' hy).1 ((i₂ p (f' p)).2 rfl))`. Rewrite using `[← this, hy]`. Establish `uniq : ∀ (u v : TFK (R` using `R) F ⟶ A.A) (c c' : Fˣ), WeilIs A.A A.L (k : ℤ) u v (unitOn c) → WeilIs A.A A.L (k : ℤ) u v (unitOn c') → c = c' := fun u v c c' h h' => GlobalTheory.weilIs_unique_fieldPoint _ A.A A.L A.isLB F _ k u v c c' h h'`.

Establish `tor : ∀ (τ' : Multiplicative D'.toPre.X →* Fˣ) (q' : QkPt D'.toPre F k), τ' ^ k = 1 → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → ∀ p : QkPt D.toPre F k, WeilIs A.A A.L (k : ℤ) (e (f' q')) (f p) (unitOn (τ' (Multiplicative.ofAdd (ρ p.y))))`. Introduce `τ' q' h₁ h₂ h₃ p`. Take `⟨q, h₄, h₅⟩` from `GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (τ'.comp (AddMonoidHom.toMultiplicative ρ)) (MonoidHom.ext fun χ => DFunLike.congr_fun h₁ _)`. Establish `: f q = e (f' q')` using `hT _ τ' q q' (f q) (f' q') h₁ (fun _ => rfl) h₄ h₅ h₂ h₃ ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)`. Establish `hw` using `wt₁ q p (τ'.comp (AddMonoidHom.toMultiplicative ρ)) h₄ h₅`.

Rewrite `hw` using `[this]`. Conclude with `hw`. Take `⟨p, rfl⟩` from `GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 a`. Take `⟨pb, rfl⟩` from `GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b`. Take `⟨p', hp'⟩` from `s₂ (e.symm (f p)) (by rw [← map_pow, p₁, map_one])`.

Establish `hp : f p = e (f' p')` using `by rw [hp', e.apply_symm_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, p'.y = ρ p.y + k • z := by`. Use `exists_eq_add_nsmul (ζ := (hζ.isUnit hk0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ) fun τ' h₁ => ?_` and prove the remaining obligations. Take `⟨q', h₂, h₃⟩` from `GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB' (k := k) τ' h₁`. Establish `h` using `hW _ _ _ (wt₂ q' p' τ' h₂ h₃)`.

Rewrite `h` using `[← hp]`. Conclude with `uniq _ _ _ _ (tor τ' q' h₁ h₂ h₃ p) h`. Set `σR : F →ₐ[FractionRing R] F` to `{ σ.toRingHom with commutes' := fun y => by rw [hF]; exact σ.commutes _ }`. Establish `eφR : ∀ r, ((φ.comp g) r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)` using `fun r => by`. Rewrite using `[hF, hgK]`.

Conclude with `eφ _`. Take `⟨r, hr, -⟩` from `GlobalTheory.TorusExt.existsUnique_qkExt hB σR.toRingHom (RingHom.ext σR.commutes) p`. Take `⟨r', hr', -⟩` from `GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'`. Take `⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩` from `GlobalTheory.KummerConj.conj_eq_add_tor R _ hB F O (φ.comp g) eφR k σR p r hr (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB F O (φ.comp g) eφR k hkO σR hσ p)`. Take `⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩` from `GlobalTheory.KummerConj.conj_eq_add_tor V _ hB' F O φ eφ k σ p' r' hr' (GlobalTheory.InertiaFix.sigma_fixes_abelianPart V _ hB' F O φ eφ k hkO σ hσ p')`.

Establish `hq : f q₁ = e (f' q₂)`. Establish `h₁ : f r = e (f' r')` using `Over.OverMorphism.ext (by`. Rewrite using `[c₁ σR p r hr, hGal (f' p') (f' r') (c₂ σ p' r' hr'), ← hp])`. Rewrite `h₁` using `[a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, ← hp]`. Conclude with `mul_left_cancel h₁`.

Establish `hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y))`. Establish `h` using `tor τ₂ q₂ k₂ y₂ t₂ pb`. Rewrite `h` using `[← hq]`. Conclude with `uniq _ _ _ _ (wt₁ q₁ pb τ₁ y₁ t₁) h`. Take `⟨x'', hx''⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre p'.y (ρ pb.y)`.

Take `⟨xz, hxz⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre z (ρ pb.y)`. Take `⟨s, s0, sv, sσ⟩` from `v₁ _ x hx`. Take `⟨s', s0', sv', sσ'⟩` from `v₂ _ x'' hx''`. Establish `sσ : σ s = _` using `sσ`. Establish `dv` using `GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord V F ϖ hϖ k O φ σ π hkO hφ eφ hσ hπ hζ (s / s') (Units.map gK.toMonoidHom x / x'') (by rw [map_div₀, sσ, sσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)]) (by rw [map_div₀, div_pow, sv, sv', Units.val_div_eq_div_val, map_div₀, map_ …`.

Take `⟨u, hu⟩` from `GlobalTheory.TauShift.main V _ hB' _ z _ k x' xz x'' hx' hxz (hz ▸ hx'')`. Rewrite `dv` using `[val_div, hu, (ord_vw V).map_mul, (ord_vw V).map_unit, (ord_vw V).map_mul, val_pow, zero_add, nsmul_eq_mul, ← sub_sub]`. Conclude with `(dvd_sub_left (dvd_mul_right _ _)).1 dv`.
-/
theorem dvd_ord_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G')
  (g : R →+* V) (gK : FractionRing R →+* FractionRing V), (∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r)) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ x, algebraMap (FractionRing R) F x = algebraMap (FractionRing V) F (gK x)) →
  ∀ (k : ℕ), IsUnit (k : R) → ∀ (ϖ : V), Irreducible ϖ → ∀ (O : ValuationSubring F) (φ : V →+* O) (σ : F →ₐ[FractionRing V] F) (π : F), IsLocalHom φ →
    (∀ w, (φ w : F) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) → (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    π ^ k = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ) → IsPrimitiveRoot (σ π / π) k →
  ∀ (ρ : D.toPre.X →+ D'.toPre.X) (e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A)),
    (∀ (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) →
    (∀ (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) →
    (∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ) (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a = e a') →
  ∀ (a b : D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D'.toPre (ρ a) (ρ b) x' →
    (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x' := by
  intro R _ _ _ hRb G _ _ hG D A U V _ _ _ _ hVb G' _ _ hG' D' A' U' g gK hgK F _ _ _ _ hF k hk ϖ hϖ O φ σ π hφ eφ hσ
    hπ hζ ρ e hW hGal hT a b x x' hx hx'
  obtain ⟨hR, _⟩ := hRb
  obtain ⟨hV, _⟩ := hVb
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  obtain ⟨f, ⟨i₁, s₁, -, a₁, w₁⟩, p₁⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
  obtain ⟨f', ⟨i₂, s₂, -, a₂, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV D' A' G' hG' U' F k hk1
  have wt₁ : ∀ (p p' : QkPt D.toPre F k) (τ : Multiplicative D.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
      WeilIs A.A A.L (k : ℤ) (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
    (w₁ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
  have wt₂ : ∀ (p p' : QkPt D'.toPre F k) (τ : Multiplicative D'.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
      WeilIs A'.A A'.L (k : ℤ) (f' p) (f' p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
    (w₂ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
  have c₁ : ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' →
      (f p').left = spMap σ.toRingHom ≫ (f p).left := by
    intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D A G hG U F F σ k hk1 p
    obtain ⟨y, hy⟩ := hx (f p)
    have : y = f p' := (i₁ p' y).1 ((hiff p' (f p) y hpp' hy).1 ((i₁ p (f p)).2 rfl))
    rw [← this, hy]
  have c₂ : ∀ (σ : F →ₐ[FractionRing V] F) p p', QkExt σ.toRingHom p p' →
      (f' p').left = spMap σ.toRingHom ≫ (f' p).left := by
    intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds V (maximalIdeal V) hV D' A' G' hG' U' F F σ k hk1 p
    obtain ⟨y, hy⟩ := hx (f' p)
    have : y = f' p' := (i₂ p' y).1 ((hiff p' (f' p) y hpp' hy).1 ((i₂ p (f' p)).2 rfl))
    rw [← this, hy]
  have uniq : ∀ (u v : TFK (R := R) F ⟶ A.A) (c c' : Fˣ), WeilIs A.A A.L (k : ℤ) u v (unitOn c) →
      WeilIs A.A A.L (k : ℤ) u v (unitOn c') → c = c' := fun u v c c' h h' =>
    GlobalTheory.weilIs_unique_fieldPoint _ A.A A.L A.isLB F _ k u v c c' h h'
  have tor : ∀ (τ' : Multiplicative D'.toPre.X →* Fˣ) (q' : QkPt D'.toPre F k), τ' ^ k = 1 → q'.y = 0 →
      GlobalTheory.UT.IsTor τ' q'.g → ∀ p : QkPt D.toPre F k,
      WeilIs A.A A.L (k : ℤ) (e (f' q')) (f p) (unitOn (τ' (Multiplicative.ofAdd (ρ p.y)))) := by
    intro τ' q' h₁ h₂ h₃ p
    obtain ⟨q, h₄, h₅⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (τ'.comp (AddMonoidHom.toMultiplicative ρ))
      (MonoidHom.ext fun χ => DFunLike.congr_fun h₁ _)
    have : f q = e (f' q') :=
      hT _ τ' q q' (f q) (f' q') h₁ (fun _ => rfl) h₄ h₅ h₂ h₃ ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)
    have hw := wt₁ q p (τ'.comp (AddMonoidHom.toMultiplicative ρ)) h₄ h₅
    rw [this] at hw
    exact hw
  obtain ⟨p, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 a
  obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
  obtain ⟨p', hp'⟩ := s₂ (e.symm (f p)) (by rw [← map_pow, p₁, map_one])
  have hp : f p = e (f' p') := by rw [hp', e.apply_symm_apply]
  obtain ⟨z, hz⟩ : ∃ z, p'.y = ρ p.y + k • z := by
    refine exists_eq_add_nsmul (ζ := (hζ.isUnit hk0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ) fun τ' h₁ => ?_
    obtain ⟨q', h₂, h₃⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB' (k := k) τ' h₁
    have h := hW _ _ _ (wt₂ q' p' τ' h₂ h₃)
    rw [← hp] at h
    exact uniq _ _ _ _ (tor τ' q' h₁ h₂ h₃ p) h

  let σR : F →ₐ[FractionRing R] F := { σ.toRingHom with commutes' := fun y => by rw [hF]; exact σ.commutes _ }
  have eφR : ∀ r, ((φ.comp g) r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) := fun r => by
    rw [hF, hgK]; exact eφ _
  obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σR.toRingHom (RingHom.ext σR.commutes) p
  obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
  obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB F O (φ.comp g) eφR k σR p r hr
    (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB F O (φ.comp g) eφR k hkO σR hσ p)
  obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.KummerConj.conj_eq_add_tor V _ hB' F O φ eφ k σ p' r' hr'
    (GlobalTheory.InertiaFix.sigma_fixes_abelianPart V _ hB' F O φ eφ k hkO σ hσ p')
  have hq : f q₁ = e (f' q₂) := by
    have h₁ : f r = e (f' r') := Over.OverMorphism.ext (by
      rw [c₁ σR p r hr, hGal (f' p') (f' r') (c₂ σ p' r' hr'), ← hp])
    rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, ← hp] at h₁
    exact mul_left_cancel h₁
  have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) := by
    have h := tor τ₂ q₂ k₂ y₂ t₂ pb
    rw [← hq] at h
    exact uniq _ _ _ _ (wt₁ q₁ pb τ₁ y₁ t₁) h
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre p'.y (ρ pb.y)
  obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre z (ρ pb.y)
  obtain ⟨s, s0, sv, sσ⟩ := v₁ _ x hx
  obtain ⟨s', s0', sv', sσ'⟩ := v₂ _ x'' hx''
  have sσ : σ s = _ := sσ
  have dv := GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord V F ϖ hϖ k O φ σ π hkO hφ eφ hσ hπ hζ (s / s') (Units.map gK.toMonoidHom x / x'')
    (by rw [map_div₀, sσ, sσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
    (by rw [map_div₀, div_pow, sv, sv', Units.val_div_eq_div_val, map_div₀, map_div₀, hF]; rfl)
  obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main V _ hB' _ z _ k x' xz x'' hx' hxz (hz ▸ hx'')
  rw [val_div, hu, (ord_vw V).map_mul, (ord_vw V).map_unit, (ord_vw V).map_mul, val_pow, zero_add, nsmul_eq_mul,
    ← sub_sub] at dv
  exact (dvd_sub_left (dvd_mul_right _ _)).1 dv

end GlobalTheory.TauFormGen
