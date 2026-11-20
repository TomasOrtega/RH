import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CorrOfValFieldExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.QkClosure

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀]
  [Field F] [Algebra (FractionRing R) F] (f : F₀ →+* F)
  (hf : f.comp (algebraMap (FractionRing R) F₀) = algebraMap (FractionRing R) F)

/- English proof (translation)
The claim follows from `val_corr hJ (GlobalTheory.corr_of_val_field_extension _ _ f _ D.P.L D.P.isLB _ _ _ _ _ _ t t' h) _`.
-/
theorem val_eq_of_ext {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TF (R := R) F₀).left ⟶ D.P.A.left)}
    {ε : K → ℤ} {φ' : K' → ((TF (R := R) F₀).left ⟶ D.P.A.left)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (t' : LB.Gen (LB.LinComb D.P.L φ' ε'))
    (h : ∀ z J, Good D.P.L z J → val t (extMap (R := R) f hf).left z J = val t' (extMap (R := R) f hf).left z J)
    {y J} (hJ : Good D.P.L y J) : val t (𝟙 _) y J = val t' (𝟙 _) y J :=
  val_corr hJ (GlobalTheory.corr_of_val_field_extension _ _ f _ D.P.L D.P.isLB _ _ _ _ _ _ t t' h) _

/- English proof (translation)
Rewrite using `[val_pull hJ, tauVal, ← extMap_jFK f hf]`.
-/
theorem val_tau_ext (x χ : D.X) {z J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀)) (extMap (R := R) f hf).left z J = tauVal D F x χ z J := by
  rw [val_pull hJ, tauVal, ← extMap_jFK f hf]

include f hf in

/- English proof (translation)
Take `⟨b', v'⟩` from `(isIota_iff_val _ _).1 hh'`. Establish `vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R` using `R) F₀)) (𝟙 (TF (R := R) F₀).left) y J = tauVal D F₀ x χ y J := fun χ y J hJ => val_pull hJ _ _ _`. Take `⟨g, hb, hv⟩` from `exists_gt (F := F₀) (cP D _ x) (fun χ => LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀)) (fun χ => pullGen_isGen _ _ _ _ (tau_isGen D x χ) _) (fun χ U _ h => by`. Establish `a : ∀ w : D.X, jFK (R` using `R) F₀ ≫ ptK (D.c w) = (cP D (TF (R := R) F₀) w).left := fun w => (Category.assoc _ _ _).symm`. Establish `a₀ : jFK (R` using `R) F₀ ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F₀ ⟶ D.P.A).left := (Category.assoc _ _ _).symm`.

Rewrite using `[prod_gt, ← cPoint_add, add_comm χ x, ← a, ← a, ← a, ← a₀]`. Simplify using `only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one]`. Rewrite using `[mul_right_comm _ (h _) (h _)]) (fun y J hJ => by`. Use `(val_eq_of_ext f hf _ (LB.oneGen D.P.L) (fun z J' hJ' => ?_) hJ).trans (val_one _)` and prove the remaining obligations. Conclude with `(val_tau_ext f hf x 0 hJ').trans ((v' 0 z J' hJ').symm.trans ((charVal_zero h' hJ').trans (val_one _).symm)))`.

Use the proof step `(fun χ χ' y J hJ => by`. Use `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).symm.trans ((val_eq_of_ext f hf _ _ (fun z J' hJ' => ?_) hJ).trans (val_mul hJ _ _ _))` and prove the remaining obligations. Establish `c` using `val_cub D.cub (extMap (R := R) f hf) hJ' (cP D _ χ) (cP D _ χ') (cP D _ x)`. Rewrite `c` using `[comp_cP, comp_cP, comp_cP]`. Establish `e` using `charVal_add h' hJ' χ χ'`.

Rewrite `e` using `[b', v' _ _ _ hJ', v' _ _ _ hJ', v' _ _ _ hJ']`. Use `(val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)` and prove the remaining obligations. Conclude with `(congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') c).trans (e.trans (congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') (val_tau_ext f hf _ _ hJ')).symm))`. Conclude with `⟨g, (isIota_iff_val _ _).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩⟩`.
-/
theorem exists_isIota_of_ext {x : D.X} {h' : GtPtF D F} (hh' : GtPtF.IsIota x h') : ∃ g : GtPtF D F₀, GtPtF.IsIota x g := by
  obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 hh'
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀))
      (𝟙 (TF (R := R) F₀).left) y J = tauVal D F₀ x χ y J := fun χ y J hJ => val_pull hJ _ _ _
  obtain ⟨g, hb, hv⟩ := exists_gt (F := F₀) (cP D _ x) (fun χ => LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀))
    (fun χ => pullGen_isGen _ _ _ _ (tau_isGen D x χ) _) (fun χ U _ h => by
      have a : ∀ w : D.X, jFK (R := R) F₀ ≫ ptK (D.c w) = (cP D (TF (R := R) F₀) w).left := fun w =>
        (Category.assoc _ _ _).symm
      have a₀ : jFK (R := R) F₀ ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F₀ ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      rw [prod_gt, ← cPoint_add, add_comm χ x, ← a, ← a, ← a, ← a₀]
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one]
      rw [mul_right_comm _ (h _) (h _)]) (fun y J hJ => by
      refine (val_eq_of_ext f hf _ (LB.oneGen D.P.L) (fun z J' hJ' => ?_) hJ).trans (val_one _)
      exact (val_tau_ext f hf x 0 hJ').trans ((v' 0 z J' hJ').symm.trans ((charVal_zero h' hJ').trans (val_one _).symm)))
    (fun χ χ' y J hJ => by
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).symm.trans
        ((val_eq_of_ext f hf _ _ (fun z J' hJ' => ?_) hJ).trans (val_mul hJ _ _ _))
      have c := val_cub D.cub (extMap (R := R) f hf) hJ' (cP D _ χ) (cP D _ χ') (cP D _ x)
      rw [comp_cP, comp_cP, comp_cP] at c
      have e := charVal_add h' hJ' χ χ'
      rw [b', v' _ _ _ hJ', v' _ _ _ hJ', v' _ _ _ hJ'] at e
      refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
      exact (congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') c).trans
        (e.trans (congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') (val_tau_ext f hf _ _ hJ')).symm))
  exact ⟨g, (isIota_iff_val _ _).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩⟩

end GlobalTheory.QkClosure

namespace GlobalTheory.QkClosure

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀]
  [Field F] [Algebra (FractionRing R) F] (f : F₀ →+* F)
  (hf : f.comp (algebraMap (FractionRing R) F₀) = algebraMap (FractionRing R) F) {k : ℕ}

include hf

/- English proof (translation)
Take `⟨b, -⟩` from `(isIota_iff_val _ _).1 hh`. Use `(isIota_iff_val _ _).2 ⟨by rw [gtExt_b, b, comp_cP], fun χ y J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[gtExt_val f hf _ χ hJ, tauVal, ← extMap_jFK f hf]`. Conclude with `(val_corr hJ (hh.2 χ) _).trans (val_pull hJ _ _ _)`.
-/
theorem isIota_gtExt {x : D.X} {h : GtPtF D F₀} (hh : GtPtF.IsIota x h) : GtPtF.IsIota x (gtExt D f hf h) := by
  obtain ⟨b, -⟩ := (isIota_iff_val _ _).1 hh
  refine (isIota_iff_val _ _).2 ⟨by rw [gtExt_b, b, comp_cP], fun χ y J hJ => ?_⟩
  rw [gtExt_val f hf _ χ hJ, tauVal, ← extMap_jFK f hf]
  exact (val_corr hJ (hh.2 χ) _).trans (val_pull hJ _ _ _)

/- English proof (translation)
Take `⟨h, h₁, h₂⟩` from `p.eq`. Take `rfl` from `(isNsmul_iff_eq _ _ _).1 h₁`. Conclude with `⟨⟨p.y, gtExt D f hf p.g, gtExt D f hf (k • p.g), (isNsmul_iff_eq _ _ _).2 (map_nsmul _ _ _), isIota_gtExt f hf h₂⟩, rfl, (eq_gtExt_iff f hf _ _).1 rfl⟩`.
-/
theorem exists_qkExt (p : QkPt D F₀ k) : ∃ p' : QkPt D F k, QkExt f p p' := by
  obtain ⟨h, h₁, h₂⟩ := p.eq
  obtain rfl := (isNsmul_iff_eq _ _ _).1 h₁
  exact ⟨⟨p.y, gtExt D f hf p.g, gtExt D f hf (k • p.g), (isNsmul_iff_eq _ _ _).2 (map_nsmul _ _ _),
    isIota_gtExt f hf h₂⟩, rfl, (eq_gtExt_iff f hf _ _).1 rfl⟩

/- English proof (translation)
The claim follows from `qk_ext (h₁.1.trans h₂.1.symm) (((eq_gtExt_iff f hf _ _).2 h₁.2).trans ((eq_gtExt_iff f hf _ _).2 h₂.2).symm)`.
-/
theorem qkExt_unique {p : QkPt D F₀ k} {p₁ p₂ : QkPt D F k} (h₁ : QkExt f p p₁) (h₂ : QkExt f p p₂) : p₁ = p₂ :=
  qk_ext (h₁.1.trans h₂.1.symm) (((eq_gtExt_iff f hf _ _).2 h₁.2).trans ((eq_gtExt_iff f hf _ _).2 h₂.2).symm)

/- English proof (translation)
The claim follows from `qk_ext (h₁.1.symm.trans h₂.1) (GlobalTheory.ArcExt.gtExt_injective f hf (((eq_gtExt_iff f hf _ _).2 h₁.2).symm.trans ((eq_gtExt_iff f hf _ _).2 h₂.2)))`.
-/
theorem qkExt_inj {p₁ p₂ : QkPt D F₀ k} {p' : QkPt D F k} (h₁ : QkExt f p₁ p') (h₂ : QkExt f p₂ p') : p₁ = p₂ :=
  qk_ext (h₁.1.symm.trans h₂.1)
    (GlobalTheory.ArcExt.gtExt_injective f hf (((eq_gtExt_iff f hf _ _).2 h₁.2).symm.trans ((eq_gtExt_iff f hf _ _).2 h₂.2)))

/- English proof (translation)
Establish `hL : Laws` using `GlobalTheory.allSixLaws.1`. Establish `hk0 : k ≠ 0` using `by rintro rfl; exact hk Nat.cast_zero`. Take `⟨h', h₁', h₂'⟩` from `p'.eq`. Take `rfl` from `(isNsmul_iff_eq _ _ _).1 h₁'`. Take `⟨h₀, hh₀⟩` from `exists_isIota_of_ext f hf h₂'`.

Establish `e₀ : gtExt D f hf h₀ = k • p'.g` using `isIota_unique (isIota_gtExt f hf hh₀) h₂'`. Take `⟨g₀, hg₀⟩` from `exists_nsmul_eq hL.mulN (Or.inr hL.polBaseChange) hk0 h₀`. Establish `ht' : k • (p'.g - gtExt D f hf g₀) = 0`. Rewrite using `[nsmul_sub, ← map_nsmul, hg₀, e₀, sub_self]`. Take `⟨t, ht⟩` from `GlobalTheory.ArcExt.exists_gtExt_of_torsion f hf hL hk _ ht'`.

Establish `ht0 : k • t = 0` using `GlobalTheory.ArcExt.gtExt_injective f hf (by rw [map_nsmul, ht, ht', map_zero])`. Establish `e : p'.g = gtExt D f hf (g₀ + t)` using `by rw [map_add, ht, add_sub_cancel]`. Use `⟨⟨p'.y, g₀ + t, h₀, (isNsmul_iff_eq _ _ _).2 ?_, hh₀⟩, rfl, (eq_gtExt_iff f hf _ _).1 e⟩` and prove the remaining obligations. Rewrite using `[nsmul_add, ht0, add_zero, hg₀]`.
-/
theorem exists_qkExt_descent [IsAlgClosed F₀] [IsAlgClosed F] (hk : (k : F₀) ≠ 0) (p' : QkPt D F k) :
    ∃ p : QkPt D F₀ k, QkExt f p p' := by
  have hL : Laws := GlobalTheory.allSixLaws.1
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  obtain ⟨h', h₁', h₂'⟩ := p'.eq
  obtain rfl := (isNsmul_iff_eq _ _ _).1 h₁'
  obtain ⟨h₀, hh₀⟩ := exists_isIota_of_ext f hf h₂'
  have e₀ : gtExt D f hf h₀ = k • p'.g := isIota_unique (isIota_gtExt f hf hh₀) h₂'
  obtain ⟨g₀, hg₀⟩ := exists_nsmul_eq hL.mulN (Or.inr hL.polBaseChange) hk0 h₀
  have ht' : k • (p'.g - gtExt D f hf g₀) = 0 := by
    rw [nsmul_sub, ← map_nsmul, hg₀, e₀, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.ArcExt.exists_gtExt_of_torsion f hf hL hk _ ht'
  have ht0 : k • t = 0 := GlobalTheory.ArcExt.gtExt_injective f hf (by rw [map_nsmul, ht, ht', map_zero])
  have e : p'.g = gtExt D f hf (g₀ + t) := by rw [map_add, ht, add_sub_cancel]
  refine ⟨⟨p'.y, g₀ + t, h₀, (isNsmul_iff_eq _ _ _).2 ?_, hh₀⟩, rfl, (eq_gtExt_iff f hf _ _).1 e⟩
  rw [nsmul_add, ht0, add_zero, hg₀]

end GlobalTheory.QkClosure

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ D F _ _ _ em N hN`. Establish `hf` using `em.comp_algebraMap`. Establish `: CharZero (Kb R)` using `(RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance`. Establish `hk : (N : Kb R) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Use `⟨fun p => ?_, fun p' => ?_⟩` and prove the remaining obligations.

Take `⟨p', hp'⟩` from `GlobalTheory.QkClosure.exists_qkExt em.toRingHom hf p`. Conclude with `⟨p', hp', fun q hq => GlobalTheory.QkClosure.qkExt_unique em.toRingHom hf hq hp'⟩`. Take `⟨p, hp⟩` from `GlobalTheory.QkClosure.exists_qkExt_descent em.toRingHom hf hk p'`. Conclude with `⟨p, hp, fun q hq => GlobalTheory.QkClosure.qkExt_inj em.toRingHom hf hq hp⟩`.
-/
theorem qkPt_algClosure_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → (∀ p : QkPt D (Kb R) N, ∃! p' : QkPt D F N, QkExt em.toRingHom p p') ∧ ∀ p' : QkPt D F N, ∃! p : QkPt D (Kb R) N, QkExt em.toRingHom p p' := by
  intro R _ _ _ D F _ _ _ em N hN
  have hf := em.comp_algebraMap
  have : CharZero (Kb R) := (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  have hk : (N : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨fun p => ?_, fun p' => ?_⟩
  · obtain ⟨p', hp'⟩ := GlobalTheory.QkClosure.exists_qkExt em.toRingHom hf p
    exact ⟨p', hp', fun q hq => GlobalTheory.QkClosure.qkExt_unique em.toRingHom hf hq hp'⟩
  · obtain ⟨p, hp⟩ := GlobalTheory.QkClosure.exists_qkExt_descent em.toRingHom hf hk p'
    exact ⟨p, hp, fun q hq => GlobalTheory.QkClosure.qkExt_inj em.toRingHom hf hq hp⟩

end GlobalTheory.Mum
