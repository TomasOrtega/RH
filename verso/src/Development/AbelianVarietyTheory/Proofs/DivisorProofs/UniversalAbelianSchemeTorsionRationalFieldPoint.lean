import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFullLevel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.XFTorsion

open GlobalTheory.FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
The claim follows from `(Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm`.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

/- English proof (translation)
Take `⟨m, hm⟩` from `A_dvd_M' l`. Establish `hM` using `M'_pos l`. Establish `hm0 : (m : ℂ) ≠ 0`. Introduce and unpack `h`. Rewrite `h` using `[Nat.cast_eq_zero]`.

Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `hA : (l.A : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 l.A_pos.ne'`. Rewrite using `[hm, Nat.mul_div_cancel_left _ l.A_pos, zeta, zeta, ← Complex.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem zeta_pow (l : Geo.Tor.Level H) : zeta l.M' ^ (l.M' / l.A) = zeta l.A := by
  obtain ⟨m, hm⟩ := A_dvd_M' l
  have hM := M'_pos l
  have hm0 : (m : ℂ) ≠ 0 := by
    rintro h
    rw [Nat.cast_eq_zero] at h
    subst h
    omega
  have hA : (l.A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 l.A_pos.ne'
  rw [hm, Nat.mul_div_cancel_left _ l.A_pos, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/- English proof (translation)
Take `⟨ev, ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩, hu⟩` from `exists_unique_fullLevel o k x β hx z hz hzA`. Establish `hid : spMap (RingHom.id k) = 𝟙 (Sp k)` using `Spec.map_id _`. Establish `e1 : spMap (σ.symm : k →+* k) ≫ spMap (σ : k →+* k) = 𝟙 _`. Rewrite using `[spMap_comp, ← hid]`. Use `congr 1`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Establish `e2 : spMap (σ : k →+* k) ≫ spMap (σ.symm : k →+* k) = 𝟙 _`. Rewrite using `[spMap_comp, ← hid]`. Use `congr 1`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Establish `hσ' : spMap (σ.symm : k →+* k) ≫ x = x` using `by conv_lhs => rw [← hσ, ← Category.assoc, e1, Category.id_comp]`. Set `g : (Over.mk x : Over S) ⟶ Over.mk x` to `Over.homMk (spMap (σ : k →+* k)) hσ`. Set `g' : (Over.mk x : Over S) ⟶ Over.mk x` to `Over.homMk (spMap (σ.symm : k →+* k)) hσ'`.

Establish `gg' : g ≫ g' = 𝟙 _` using `Over.OverMorphism.ext e2`. Establish `g'g : g' ≫ g = 𝟙 _` using `Over.OverMorphism.ext e1`. Establish `key : (fun a => g ≫ ev a) = ev`. Use `(hu _ ⟨⟨fun a c => ?_, fun c a => ?_, fun a => ?_, fun u => ?_, fun a c => ?_⟩, fun a => ?_, fun a ha => ?_⟩).trans (hu ev ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩).symm` and prove the remaining obligations. Use `show g ≫ ev (a + c) = (g ≫ ev a) * (g ≫ ev c)`.

Rewrite using `[h1, MonObj.comp_mul]`. Use `show g ≫ ev (c • a) = (g ≫ ev a) ≫ o.t.act.act c`. Rewrite using `[h2, Category.assoc]`. Use `show g ≫ ev a = 1 ↔ _`. Rewrite using `[← h3]`.

Use `⟨fun h => ?_, fun h => by rw [h, MonObj.comp_one]⟩` and prove the remaining obligations. Rewrite using `[← Category.id_comp (ev a), ← g'g, Category.assoc, h, MonObj.comp_one]`. Use `⟨fun h => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `(h4 (g' ≫ u)).1 (by rw [← MonObj.comp_pow, h, MonObj.comp_one])`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Use `show g ≫ ev a = u`. Rewrite using `[ha, ← Category.assoc, gg', Category.id_comp]`. Introduce and unpack `⟨a, rfl⟩ show (g ≫ ev a) ^ l.M' = 1`. Rewrite using `[← MonObj.comp_pow, (h4 _).2 ⟨a, rfl⟩, MonObj.comp_one]`. Establish `h₁` using `GlobalTheory.CommPairing.weilIs_pull GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme o) o.t.PP.isLB g (h5 a c)`.

Establish `e' : Units.map g.left.appTop.hom.toMonoidHom (unitOn (z ^ D.EF a c)) = unitOn (Units.map (σ : k →+* k).toMonoidHom (z ^ D.EF a c))` using `Units.ext (congrArg (fun q => q.hom (z ^ D.EF a c).val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : k →+* k)))).symm`. Establish `e'' : Units.map (σ : k →+* k).toMonoidHom (z ^ D.EF a c) = z ^ D.EF a c`. Rewrite using `[map_zpow]`. Use `congr 1`. Conclude with `Units.ext hσz`.

Rewrite `e'` using `[e'']`. Conclude with `(congrArg (WeilIs o.t.G o.t.PP.L (l.M' : ℕ) (g ≫ ev a) (g ≫ ev c)) e').mp h₁`. Use `show (g ≫ ev a) ^ (l.M' / l.A) = toUnit _ ≫ o.etaA a`. Rewrite using `[← MonObj.comp_pow, h6, comp_toUnit_assoc]`. Use `show (g ≫ ev a) ^ (l.M' / l.M) = toUnit _ ≫ o.eta a`.

Rewrite using `[← MonObj.comp_pow, h7 a ha, comp_toUnit_assoc]`. Take `⟨a, rfl⟩` from `(h4 w).1 hw`. Conclude with `congrArg CommaMorphism.left (congrFun key a)`.
-/
theorem torsion_fixed {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (z : kˣ) (hz : IsPrimitiveRoot z l.M')
    (hzA : (z : k) ^ (l.M' / l.A) = β b.ζ) (σ : k ≃+* k) (hσ : spMap (σ : k →+* k) ≫ x = x) (hσz : σ z = z)
    (w : Over.mk x ⟶ o.t.G) (hw : w ^ l.M' = 1) : spMap (σ : k →+* k) ≫ w.left = w.left := by
  obtain ⟨ev, ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩, hu⟩ := exists_unique_fullLevel o k x β hx z hz hzA
  have hid : spMap (RingHom.id k) = 𝟙 (Sp k) := Spec.map_id _
  have e1 : spMap (σ.symm : k →+* k) ≫ spMap (σ : k →+* k) = 𝟙 _ := by
    rw [spMap_comp, ← hid]; congr 1; ext a; simp
  have e2 : spMap (σ : k →+* k) ≫ spMap (σ.symm : k →+* k) = 𝟙 _ := by
    rw [spMap_comp, ← hid]; congr 1; ext a; simp
  have hσ' : spMap (σ.symm : k →+* k) ≫ x = x := by
    conv_lhs => rw [← hσ, ← Category.assoc, e1, Category.id_comp]
  let g : (Over.mk x : Over S) ⟶ Over.mk x := Over.homMk (spMap (σ : k →+* k)) hσ
  let g' : (Over.mk x : Over S) ⟶ Over.mk x := Over.homMk (spMap (σ.symm : k →+* k)) hσ'
  have gg' : g ≫ g' = 𝟙 _ := Over.OverMorphism.ext e2
  have g'g : g' ≫ g = 𝟙 _ := Over.OverMorphism.ext e1
  have key : (fun a => g ≫ ev a) = ev := by
    refine (hu _ ⟨⟨fun a c => ?_, fun c a => ?_, fun a => ?_, fun u => ?_, fun a c => ?_⟩, fun a => ?_, fun a ha => ?_⟩).trans
      (hu ev ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩).symm
    · show g ≫ ev (a + c) = (g ≫ ev a) * (g ≫ ev c)
      rw [h1, MonObj.comp_mul]
    · show g ≫ ev (c • a) = (g ≫ ev a) ≫ o.t.act.act c
      rw [h2, Category.assoc]
    · show g ≫ ev a = 1 ↔ _
      rw [← h3]
      refine ⟨fun h => ?_, fun h => by rw [h, MonObj.comp_one]⟩
      rw [← Category.id_comp (ev a), ← g'g, Category.assoc, h, MonObj.comp_one]
    · refine ⟨fun h => ?_, ?_⟩
      · obtain ⟨a, ha⟩ := (h4 (g' ≫ u)).1 (by rw [← MonObj.comp_pow, h, MonObj.comp_one])
        refine ⟨a, ?_⟩
        show g ≫ ev a = u
        rw [ha, ← Category.assoc, gg', Category.id_comp]
      · rintro ⟨a, rfl⟩
        show (g ≫ ev a) ^ l.M' = 1
        rw [← MonObj.comp_pow, (h4 _).2 ⟨a, rfl⟩, MonObj.comp_one]
    · have h₁ := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme o) o.t.PP.isLB g
        (h5 a c)
      have e' : Units.map g.left.appTop.hom.toMonoidHom (unitOn (z ^ D.EF a c)) =
          unitOn (Units.map (σ : k →+* k).toMonoidHom (z ^ D.EF a c)) :=
        Units.ext (congrArg (fun q => q.hom (z ^ D.EF a c).val)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : k →+* k)))).symm
      have e'' : Units.map (σ : k →+* k).toMonoidHom (z ^ D.EF a c) = z ^ D.EF a c := by
        rw [map_zpow]
        congr 1
        exact Units.ext hσz
      rw [e''] at e'
      exact (congrArg (WeilIs o.t.G o.t.PP.L (l.M' : ℕ) (g ≫ ev a) (g ≫ ev c)) e').mp h₁
    · show (g ≫ ev a) ^ (l.M' / l.A) = toUnit _ ≫ o.etaA a
      rw [← MonObj.comp_pow, h6, comp_toUnit_assoc]
    · show (g ≫ ev a) ^ (l.M' / l.M) = toUnit _ ≫ o.eta a
      rw [← MonObj.comp_pow, h7 a ha, comp_toUnit_assoc]
  obtain ⟨a, rfl⟩ := (h4 w).1 hw
  exact congrArg CommaMorphism.left (congrFun key a)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ K K' _ _ _ κ y x hx`. Take `⟨bF, hbF⟩ : ∃ bF : c.F →+* K, y ≫ pullback.snd _ _ = spMap bF` from `⟨(Spec.preimage (y ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩`. Use `haveI : CharZero K := RingHom.charZero_iff bF.injective |>.1 inferInstance`. Use `letI : Algebra K K' := κ.toAlgebra`. Set `inc` to `(IntermediateField.inclusion c.le).toRingHom`.

Establish `hs : (spMap κ ≫ y ≫ pullback.fst _ _) ≫ Xo.s = spMap (κ.comp (bF.comp inc))`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, ← Category.assoc y, hbF, spMap_comp, spMap_comp]`. Set `z₀ : c.F` to `⟨zeta l.M', c.zeta_mem⟩`. Establish `hz₀ : IsPrimitiveRoot z₀ l.M'` using `IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (Complex.isPrimitiveRoot_exp l.M' (M'_pos l).ne') Subtype.val_injective`. Establish `hz₁ : IsPrimitiveRoot (κ (bF z₀)) l.M'` using `(hz₀.map_of_injective bF.injective).map_of_injective κ.injective`.

Set `z : K'ˣ` to `(hz₁.isUnit (M'_pos l).ne').unit`. Establish `hz : IsPrimitiveRoot z l.M'` using `IsPrimitiveRoot.coe_units_iff.1 hz₁`. Establish `hzA : (z : K') ^ (l.M' / l.A) = (κ.comp (bF.comp inc)) (baseKA l).ζ` using `by show κ (bF z₀) ^ _ = κ (bF (inc _))`. Rewrite using `[← map_pow, ← map_pow]`. Use `congr 2`.

Conclude with `Subtype.ext (zeta_pow l)`. Take `⟨p, hp, -⟩` from `GlobalTheory.FixedPoint.existsUnique_factor_of_isAlgClosed (K₀ := K) (L := K') x.left fun σ => torsion_fixed Xo.univ K' _ _ hs z hz hzA σ.toRingEquiv (by`. Rewrite using `[← Category.assoc, spMap_comp]`. Use `congr 2`. Use extensionality with `a`.

Conclude with `σ.commutes a) (σ.commutes (bF z₀)) x hx`. Use `haveI : Epi (spMap κ) := GlobalTheory.FixedPoint.epi_specAlg (K₀ := K) (K₁ := K')`. Establish `hp' : spMap κ ≫ p = x.left` using `hp`. Establish `hpo : p ≫ Xo.univ.t.G.hom = y ≫ pullback.fst _ _`. Rewrite using `[← cancel_epi (spMap κ), ← Category.assoc, hp']`.

Conclude with `Over.w x`. Set `x₀ : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G` to `Over.homMk p hpo`. Set `g : (Over.mk (spMap κ ≫ y ≫ pullback.fst _ _) : Over Xo.X) ⟶ Over.mk (y ≫ pullback.fst _ _)` to `Over.homMk (spMap κ) rfl`. Establish `hg : g ≫ x₀ = x` using `Over.OverMorphism.ext hp'`. Use `⟨x₀, Over.OverMorphism.ext ?_, hp'.symm⟩` and prove the remaining obligations.

Establish `h : g ≫ x₀ ^ l.M' = g ≫ 1` using `by rw [MonObj.comp_pow, hg, hx, MonObj.comp_one]`. Conclude with `(cancel_epi (spMap κ)).1 (congrArg CommaMorphism.left h)`.
-/
theorem torsion_rational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (K K' : Type) [Field K] [Field K'] [IsAlgClosed K'] (κ : K →+* K') (y : Sp K ⟶ Xo.XF c) (x : Over.mk (spMap κ ≫ y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G), x ^ l.M' = 1 → ∃ x₀ : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G, x₀ ^ l.M' = 1 ∧ x.left = spMap κ ≫ x₀.left := by
  intro E _ _ _ H Dw l Xo c _ K K' _ _ _ κ y x hx
  obtain ⟨bF, hbF⟩ : ∃ bF : c.F →+* K, y ≫ pullback.snd _ _ = spMap bF :=
    ⟨(Spec.preimage (y ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  haveI : CharZero K := RingHom.charZero_iff bF.injective |>.1 inferInstance
  letI : Algebra K K' := κ.toAlgebra
  let inc := (IntermediateField.inclusion c.le).toRingHom
  have hs : (spMap κ ≫ y ≫ pullback.fst _ _) ≫ Xo.s = spMap (κ.comp (bF.comp inc)) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc y, hbF, spMap_comp, spMap_comp]
  let z₀ : c.F := ⟨zeta l.M', c.zeta_mem⟩
  have hz₀ : IsPrimitiveRoot z₀ l.M' := IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom)
    (Complex.isPrimitiveRoot_exp l.M' (M'_pos l).ne') Subtype.val_injective
  have hz₁ : IsPrimitiveRoot (κ (bF z₀)) l.M' := (hz₀.map_of_injective bF.injective).map_of_injective κ.injective
  let z : K'ˣ := (hz₁.isUnit (M'_pos l).ne').unit
  have hz : IsPrimitiveRoot z l.M' := IsPrimitiveRoot.coe_units_iff.1 hz₁
  have hzA : (z : K') ^ (l.M' / l.A) = (κ.comp (bF.comp inc)) (baseKA l).ζ := by
    show κ (bF z₀) ^ _ = κ (bF (inc _))
    rw [← map_pow, ← map_pow]
    congr 2
    exact Subtype.ext (zeta_pow l)
  obtain ⟨p, hp, -⟩ := GlobalTheory.FixedPoint.existsUnique_factor_of_isAlgClosed (K₀ := K) (L := K') x.left fun σ =>
    torsion_fixed Xo.univ K' _ _ hs z hz hzA σ.toRingEquiv (by
      rw [← Category.assoc, spMap_comp]
      congr 2
      ext a
      exact σ.commutes a) (σ.commutes (bF z₀)) x hx
  haveI : Epi (spMap κ) := GlobalTheory.FixedPoint.epi_specAlg (K₀ := K) (K₁ := K')
  have hp' : spMap κ ≫ p = x.left := hp
  have hpo : p ≫ Xo.univ.t.G.hom = y ≫ pullback.fst _ _ := by
    rw [← cancel_epi (spMap κ), ← Category.assoc, hp']
    exact Over.w x
  let x₀ : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G := Over.homMk p hpo
  let g : (Over.mk (spMap κ ≫ y ≫ pullback.fst _ _) : Over Xo.X) ⟶ Over.mk (y ≫ pullback.fst _ _) :=
    Over.homMk (spMap κ) rfl
  have hg : g ≫ x₀ = x := Over.OverMorphism.ext hp'
  refine ⟨x₀, Over.OverMorphism.ext ?_, hp'.symm⟩
  have h : g ≫ x₀ ^ l.M' = g ≫ 1 := by rw [MonObj.comp_pow, hg, hx, MonObj.comp_one]
  exact (cancel_epi (spMap κ)).1 (congrArg CommaMorphism.left h)

end GlobalTheory.XFTorsion
