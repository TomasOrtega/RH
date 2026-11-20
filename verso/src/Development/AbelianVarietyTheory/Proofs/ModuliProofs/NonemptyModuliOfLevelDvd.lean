import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleDeeperLevelCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelUp

/- English proof (translation)
Set `π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k` to `CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom`. Establish `hπ : Function.Surjective π` using `fun a => ⟨TrivSqZeroExt.inl a, rfl⟩`. Establish `hn : IsNilpotent (RingHom.ker π.hom)`. Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]`.

Introduce `a ha c hc`. Establish `ha' : a.fst = 0` using `ha`. Establish `hc' : c.fst = 0` using `hc`. Rewrite using `[Ideal.mem_bot]`. Apply the tactic sequence `ext <;> simp [ha', hc']`.

Use `IsClosedImmersion.spec_of_surjective π hπ` as an intermediate fact. Use `FormallyUnramified.hom_ext (Spec.map π) (isNilpotent_ker_specMap π hn) f ?_ (h.trans (by simp only [Geo.Tor.constPt, Category.assoc]))` and prove the remaining obligations. Establish `e : Spec.map π ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`.

Rewrite using `[Geo.Tor.constPt, ← Category.assoc, e, Category.id_comp]`.
-/
theorem eq_constPt_of_formallyUnramified {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    (x : Sp (DualNumber k) ⟶ X) (h : x ≫ f = Geo.Tor.constPt (x ≫ f)) : x = Geo.Tor.constPt x := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha c hc
    have ha' : a.fst = 0 := ha
    have hc' : c.fst = 0 := hc
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hc']
  have := IsClosedImmersion.spec_of_surjective π hπ
  refine FormallyUnramified.hom_ext (Spec.map π) (isNilpotent_ker_specMap π hn) f ?_
    (h.trans (by simp only [Geo.Tor.constPt, Category.assoc]))
  have e : Spec.map π ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [Geo.Tor.constPt, ← Category.assoc, e, Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

/- English proof (translation)
Use `IntermediateField.finiteDimensional_adjoin fun x hx => ?_` and prove the remaining obligations. Break down `hx with rfl | rfl` into its components or cases. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[H.sqrt_neg_disc_sq]`. Conclude with `(isIntegral_algebraMap (x := (H.d : ℚ))).neg`.

Use `IsIntegral.of_pow l.A_pos ?_` and prove the remaining obligations. Rewrite using `[show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]`. Conclude with `isIntegral_one`.
-/
theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

/- English proof (translation)
Rewrite using `[HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]`. Use `finiteDimensional_KA l₂` as an intermediate fact. Establish `: Algebra.FormallyUnramified ℚ (KA l₂)` using `Algebra.FormallyUnramified.of_isSeparable ℚ (KA l₂)`. Set `_ : Algebra (KA l) (KA l₂)` to `j.toAlgebra`. Conclude with `Algebra.FormallyUnramified.of_restrictScalars ℚ (KA l) (KA l₂)`.
-/
theorem formallyUnramified_spMap (j : KA l →+* KA l₂) : FormallyUnramified (spMap j) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := finiteDimensional_KA l₂
  have : Algebra.FormallyUnramified ℚ (KA l₂) := Algebra.FormallyUnramified.of_isSeparable ℚ (KA l₂)
  let _ : Algebra (KA l) (KA l₂) := j.toAlgebra
  exact Algebra.FormallyUnramified.of_restrictScalars ℚ (KA l) (KA l₂)

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨o, ⟨ObjComp.objMapId o⟩⟩`.
-/
theorem exists_obj_of_eq {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s s' : S ⟶ Sp B} (e : s = s')
    (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o (𝟙 S)) := by
  subst e
  exact ⟨o, ⟨ObjComp.objMapId o⟩⟩

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨m⟩`.
-/
theorem nonempty_objMap_of_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {f g : S' ⟶ S}
    (e : f = g) (m : ObjMap o' o f) : Nonempty (ObjMap o' o g) := by
  subst e
  exact ⟨m⟩

/- English proof (translation)
Take `⟨n, hn⟩` from `ObjMaps.exists_sab_comp m u.toSABMap`. Establish `hn' : n.cm.F = u.cm.F ≫ m.cm.F` using `hn`. Use `⟨⟨n, fun a => ?_, fun a => ?_⟩, hn⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _`. Rewrite using `[hn']`.

Use `ObjComp.sec_comp (h₁ a) ?_` and prove the remaining obligations. Rewrite using `[← ObjLower.map_nsmul_of_add _ o'.eta_add, ← ObjLower.map_nsmul_of_add _ o₂.eta_add]`. Conclude with `u.eta _`. Express the relevant statement in the definitionally equal form `(o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _`. Rewrite using `[hn']`.

Use `ObjComp.sec_comp (h₂ a) ?_` and prove the remaining obligations. Rewrite using `[← ObjLower.map_nsmul_of_add _ o'.etaA_add, ← ObjLower.map_nsmul_of_add _ o₂.etaA_add]`. Conclude with `u.etaA _`.
-/
theorem exists_objMap_lower {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj D l b s} {o₂ : Obj D l₂ b₂ s₂} {o' : Obj D l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    ∃ n : ObjMap (ObjLower.lower o' h hρ hζ) o (g ≫ π), n.toSABMap.φ = u.toSABMap.φ ≫ m.φ := by
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩, hn⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₁ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.eta_add, ← ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₂ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.etaA_add, ← ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

end GlobalTheory.LevelUp

namespace GlobalTheory

open LevelUp

/- English proof (translation)
Introduce `hL _ E _ _ _ H D l l₂ hpq hd ⟨Xo⟩`. Establish `hA : l.A ∣ l₂.A` using `hd.2.2`. Set `j` to `levelFieldIncl hA`. Set `b` to `baseOfFinerLevel hA`. Establish `hρ : b.ρ = (baseKA l₂).ρ` using `baseOfFinerLevel_rho hA`.

Establish `hζ : b.ζ = (baseKA l₂).ζ ^ (l₂.A / l.A)` using `baseOfFinerLevel_zeta hA`. Establish `jρ : j (baseKA l).ρ = b.ρ` using `levelFieldIncl_rho hA`. Establish `jζ : j (baseKA l).ζ = b.ζ` using `levelFieldIncl_zeta hA`. Take `⟨o₁, ⟨m₀⟩⟩` from `obj_pull E H D l _ _ (baseKA l) b j _ _ Xo.s (pullback.snd Xo.s (spMap j)) (pullback.fst Xo.s (spMap j)) jρ jζ pullback.condition Xo.univ`. Take `⟨S₂, π, o₂, m, hfin, het, -, ⟨h₁, h₂⟩, huniv⟩` from `GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ b (baseKA l₂) _ _ o₁ hpq hd hρ hζ`.

Establish `hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap j))` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth`. Use `⟨{ X := S₂, s := π ≫ pullback.snd Xo.s (spMap j), qproj := ?_, smooth := ?_, univ := o₂, rep := ?_, unram := ?_ }⟩` and prove the remaining obligations. Conclude with `isQProjOver_comp_of_isFinite_noetherian _ _ _ _ _ hfin ((isQProjOver_baseChange_and_finite_restrict _ _ j _ Xo.s).1 Xo.qproj)`. Establish `: SmoothOfRelativeDimension (0 + D.dim) (π ≫ pullback.snd Xo.s (spMap j))` using `inferInstance`. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.

Introduce `S t hS o`. Take `⟨f₀, ⟨hf₀, ⟨n⟩⟩, hu₀⟩` from `moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo _ b j S t (ObjLower.lower o hd hρ hζ) hS jρ jζ`. Take `⟨f, hf₁, hf₂⟩ : ∃ f : S ⟶ pullback Xo.s (spMap j), f ≫ pullback.fst _ _ = f₀ ∧ f ≫ pullback.snd _ _ = t` from `⟨pullback.lift f₀ t hf₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`. Substitute `hf₁ hf₂` using the available equality. Take `⟨m', -⟩` from `ObjComp.objMap_cancel m₀ n`.

Take `⟨h, ⟨hh, u, -⟩, hu⟩` from `huniv S f o m'.toSABMap ⟨m'.eta, m'.etaA⟩`. Use `⟨h, ⟨by rw [← Category.assoc, hh], ⟨u⟩⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨hg, ⟨v⟩⟩`. Take `⟨w, hw⟩` from `exists_objMap_lower hd hρ hζ m h₁ h₂ v`. Take `⟨w', -⟩` from `ObjComp.objMap_comp m₀ w`.

Establish `e : g ≫ π = f`. Use `pullback.hom_ext (hu₀ _ ⟨?_, ⟨w'⟩⟩) (by rw [Category.assoc, hg])` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← hg]`. Simplify using `only [Category.assoc]`. Substitute `e` using the available equality.

Use `hu g ⟨rfl, v, hw.symm.trans ?_⟩` and prove the remaining obligations. Conclude with `obj_rigid_closed hL E H D l _ _ b b _ _ _ _ o₁ (ObjLower.lower o hd hρ hζ) (g ≫ π) (Or.inl hS) w.toSABMap m'.toSABMap fun a => ⟨_, w.eta a, m'.eta a⟩`. Introduce and unpack `k _ x o ⟨u⟩ ⟨u'⟩`. Establish `hj` using `formallyUnramified_spMap j`. Establish `hp : FormallyUnramified (pullback.fst Xo.s (spMap j))` using `(HasRingHomProperty.isStableUnderBaseChange (P := @FormallyUnramified.{0}) RingHom.FormallyUnramified.isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip hj`.

Establish `hr : FormallyUnramified (π ≫ pullback.fst Xo.s (spMap j))` using `MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hp`. Use `eq_constPt_of_formallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) x ?_` and prove the remaining obligations. Take `⟨w, -⟩` from `exists_objMap_lower hd hρ hζ m h₁ h₂ u`. Take `⟨w', -⟩` from `exists_objMap_lower hd hρ hζ m h₁ h₂ u'`. Establish `e : (x ≫ π ≫ pullback.snd Xo.s (spMap j)) ≫ spMap j = (x ≫ π ≫ pullback.fst Xo.s (spMap j)) ≫ Xo.s`.

Simplify using `only [Category.assoc, pullback.condition]`. Take `⟨o', ⟨i⟩⟩` from `exists_obj_of_eq e (objRestrictBase j (ObjLower.lower o hd hρ hζ) jρ jζ)`. Set `i' : ObjMap o' (ObjLower.lower o hd hρ hζ) (𝟙 _)` to `⟨i.toSABMap, i.eta, i.etaA⟩`. Take `⟨n, -⟩` from `ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w).choose i'`. Take `⟨n', -⟩` from `ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w').choose i'`.

Conclude with `Xo.unram k _ o' (nonempty_objMap_of_eq (by simp only [Category.assoc, Category.id_comp]) n) (nonempty_objMap_of_eq (by simp only [Geo.Tor.constPt, Category.assoc, Category.id_comp]) n')`.
-/
theorem nonempty_moduli_of_dvd : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l) → Nonempty (Moduli D l₂) := by
  intro hL _ E _ _ _ H D l l₂ hpq hd ⟨Xo⟩
  have hA : l.A ∣ l₂.A := hd.2.2
  let j := levelFieldIncl hA
  let b := baseOfFinerLevel hA
  have hρ : b.ρ = (baseKA l₂).ρ := baseOfFinerLevel_rho hA
  have hζ : b.ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := baseOfFinerLevel_zeta hA
  have jρ : j (baseKA l).ρ = b.ρ := levelFieldIncl_rho hA
  have jζ : j (baseKA l).ζ = b.ζ := levelFieldIncl_zeta hA
  obtain ⟨o₁, ⟨m₀⟩⟩ := obj_pull E H D l _ _ (baseKA l) b j _ _ Xo.s (pullback.snd Xo.s (spMap j))
    (pullback.fst Xo.s (spMap j)) jρ jζ pullback.condition Xo.univ
  obtain ⟨S₂, π, o₂, m, hfin, het, -, ⟨h₁, h₂⟩, huniv⟩ :=
    GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ b (baseKA l₂) _ _ o₁ hpq hd hρ hζ
  have hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap j)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  refine ⟨{ X := S₂, s := π ≫ pullback.snd Xo.s (spMap j), qproj := ?_, smooth := ?_, univ := o₂,
            rep := ?_, unram := ?_ }⟩
  · exact isQProjOver_comp_of_isFinite_noetherian _ _ _ _ _ hfin
      ((isQProjOver_baseChange_and_finite_restrict _ _ j _ Xo.s).1 Xo.qproj)
  · have : SmoothOfRelativeDimension (0 + D.dim) (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
    rwa [zero_add] at this
  · intro S t hS o
    obtain ⟨f₀, ⟨hf₀, ⟨n⟩⟩, hu₀⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo _ b j S t
      (ObjLower.lower o hd hρ hζ) hS jρ jζ
    obtain ⟨f, hf₁, hf₂⟩ : ∃ f : S ⟶ pullback Xo.s (spMap j), f ≫ pullback.fst _ _ = f₀ ∧ f ≫ pullback.snd _ _ = t :=
      ⟨pullback.lift f₀ t hf₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    subst hf₁ hf₂
    obtain ⟨m', -⟩ := ObjComp.objMap_cancel m₀ n
    obtain ⟨h, ⟨hh, u, -⟩, hu⟩ := huniv S f o m'.toSABMap ⟨m'.eta, m'.etaA⟩
    refine ⟨h, ⟨by rw [← Category.assoc, hh], ⟨u⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨v⟩⟩
    obtain ⟨w, hw⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ v
    obtain ⟨w', -⟩ := ObjComp.objMap_comp m₀ w
    have e : g ≫ π = f := by
      refine pullback.hom_ext (hu₀ _ ⟨?_, ⟨w'⟩⟩) (by rw [Category.assoc, hg])
      rw [Category.assoc, pullback.condition, ← hg]
      simp only [Category.assoc]
    subst e
    refine hu g ⟨rfl, v, hw.symm.trans ?_⟩
    exact obj_rigid_closed hL E H D l _ _ b b _ _ _ _ o₁ (ObjLower.lower o hd hρ hζ) (g ≫ π) (Or.inl hS)
      w.toSABMap m'.toSABMap fun a => ⟨_, w.eta a, m'.eta a⟩
  · rintro k _ x o ⟨u⟩ ⟨u'⟩
    have hj := formallyUnramified_spMap j
    have hp : FormallyUnramified (pullback.fst Xo.s (spMap j)) :=
      (HasRingHomProperty.isStableUnderBaseChange (P := @FormallyUnramified.{0})
        RingHom.FormallyUnramified.isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip hj
    have hr : FormallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hp
    refine eq_constPt_of_formallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) x ?_
    obtain ⟨w, -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u
    obtain ⟨w', -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u'
    have e : (x ≫ π ≫ pullback.snd Xo.s (spMap j)) ≫ spMap j = (x ≫ π ≫ pullback.fst Xo.s (spMap j)) ≫ Xo.s := by
      simp only [Category.assoc, pullback.condition]
    obtain ⟨o', ⟨i⟩⟩ := exists_obj_of_eq e (objRestrictBase j (ObjLower.lower o hd hρ hζ) jρ jζ)
    let i' : ObjMap o' (ObjLower.lower o hd hρ hζ) (𝟙 _) := ⟨i.toSABMap, i.eta, i.etaA⟩
    obtain ⟨n, -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w).choose i'
    obtain ⟨n', -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w').choose i'
    exact Xo.unram k _ o' (nonempty_objMap_of_eq (by simp only [Category.assoc, Category.id_comp]) n)
      (nonempty_objMap_of_eq (by simp only [Geo.Tor.constPt, Category.assoc, Category.id_comp]) n')

end GlobalTheory
