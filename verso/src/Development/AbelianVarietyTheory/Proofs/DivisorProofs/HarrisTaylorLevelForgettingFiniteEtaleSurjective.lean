import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIsLevelLiftOfPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePointOfLevelLiftHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHigherLevelPointsEqOfSameImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPointsStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Introduce `p _ D R _ _ b N N' hd hc h3 M M' π hπ ⟨om⟩`. Use `haveI := M.smooth`. Use `haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s`. Use `haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s`. Take `⟨Y, ηu, hYf, hYe, HY⟩` from `GlobalTheory.T.exists_finite_etale_level_lift_scheme p D R b N N' hc hd M.X M.s M.univ`.

Set `T0 : Over M.X` to `Over.mk π`. Establish `hw : ∀ a, ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = T0.hom` using `fun a => by`. Establish `w : (om.φ : M'.univ.A.left ⟶ M.univ.A.left) ≫ M.univ.A.hom = M'.univ.A.hom ≫ π` using `om.cart.1.w`. Establish `w2 : (M'.univ.eta a).left ≫ M'.univ.A.hom = 𝟙 M'.X` using `Over.w (M'.univ.eta a)`. Use `show ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = π`.

Use `erw [Category.assoc, w, ← Category.assoc, w2, Category.id_comp]`. Set `lv0 : D.La → (T0 ⟶ M.univ.A)` to `fun a => Over.homMk ((M'.univ.eta a).left ≫ om.φ) (hw a)`. Establish `hl0 : IsLift M.univ N' T0 lv0` using `GlobalTheory.T.harrisTaylor_isLevelLift_of_point p D R b N N' hd hc M.X M'.X M.s M'.s M.univ M'.univ π om T0 (𝟙 M'.X) lv0 (Category.id_comp π) fun a => (Category.id_comp _).symm`. Take `⟨g0, hg0, -⟩` from `(HY T0 lv0).1 hl0`. Establish `hlY : IsLift M.univ N' Y ηu` using `(HY Y ηu).2 ⟨𝟙 Y, fun a => Category.id_comp _⟩`.

Take `⟨h, hh, hha⟩` from `GlobalTheory.T.exists_unique_point_of_level_lift_harrisTaylor p D R b N N' h3 hd hc M M' π hπ om Y ηu hlY`. Establish `e1 : g0.left ≫ h = 𝟙 M'.X`. Use `GlobalTheory.T.harrisTaylor_higherLevel_points_eq_of_same_image p D R b N N' hd hc M.X M.s M.univ M' π hπ om M'.X _ _ ?_ fun a => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hh, Over.w g0, Category.id_comp]`. Both sides reduce to the same expression.

Rewrite using `[Category.id_comp, Category.assoc, ← hha a, ← Over.comp_left, hg0 a]`. Both sides reduce to the same expression. Set `hY : Y ⟶ T0` to `Over.homMk h hh`. Establish `e2 : hY ≫ g0 = 𝟙 Y`. Take `⟨f, -, hf⟩` from `(HY Y ηu).1 hlY`.

Establish `a1` using `hf (hY ≫ g0) fun a => by`. Rewrite using `[Category.assoc, hg0 a]`. Use `ext`. Simplify using `only [Over.comp_left, Over.homMk_left, hY, lv0]`. Rewrite using `[hha a]`.

Establish `a2` using `hf (𝟙 Y) fun a => Category.id_comp _`. Rewrite using `[a1, a2]`. Establish `e2' : h ≫ g0.left = 𝟙 Y.left`. Use `congrArg (fun q => q.left) e2` as an intermediate fact. Simplify `this` using `[hY]`.

Use `haveI : IsIso g0.left := ⟨⟨h, e1, e2'⟩⟩`. Establish `e : π = g0.left ≫ Y.hom` using `(Over.w g0).symm`. Establish `hfe : IsFinite π ∧ Etale π`. Rewrite using `[e]`. Conclude with `⟨inferInstance, inferInstance⟩`.

Use `⟨hfe.1, hfe.2, ⟨fun z => ?_⟩⟩` and prove the remaining obligations. Take `⟨k, _, _, g, hg⟩` from `GlobalTheory.FinEt.exists_algClosed_point M.X z`. Take `⟨β, hβ⟩ : ∃ β : R →+* k, g ≫ M.s = spMap β` from `⟨(Spec.preimage (g ≫ M.s)).hom, by simp [spMap]⟩`. Take `⟨I, hI⟩` from `M.univ.geom k g β hβ`. Establish `hN' : 0 < N'` using `levelPos_of_coprime hc`.

Establish `hN : 0 < N` using `by omega`. Establish `hk : 0 < N' / N` using `Nat.div_pos (Nat.le_of_dvd hN' hd) hN`. Set `T : Over M.X` to `Over.mk g`. Set `lv : D.La → (T ⟶ M.univ.A)` to `fun a => I.ev N' a`. Establish `hadd : ∀ x y, lv (x + y) = lv x * lv y` using `fun x y => I.add N' x y`.

Establish `hker : ∀ x, lv (N' • x) = 1` using `fun x => (I.ker N' hN' hc _).2 ⟨x, rfl⟩`. Establish `hlin : ∀ (c : D.O) x, lv (c • x) = lv x ≫ M.univ.act.act c` using `fun c x => I.lin N' c x`. Use `haveI : IsLocallyNoetherian T.left := by show IsLocallyNoetherian (Spec (CommRingCat.of k)) infer_instance`. Establish `hlv : IsLift M.univ N' T lv`. Use `⟨hadd, hker, hlin, fun x => ?_, fun k' _ _ x' => ?_⟩` and prove the remaining obligations.

Use `show I.ev N' ((N' / N) • x) = toUnit T ≫ M.univ.eta x`. Rewrite using `[hI x, I.ev_nsmul]`. Use `I.tower N (N' / N) hN hk (by rw [Nat.mul_div_cancel' hd]; exact hc) x` as an intermediate fact. Rewrite `this` using `[Nat.mul_div_cancel' hd]`. Then use the resulting hypothesis. Establish `h0 : TateAt M.univ N' g (fun a => lv a)` using `⟨I, fun y => rfl⟩`.

Establish `h1 : TateAt M.univ N' (𝟙 T.left ≫ T.hom) (fun a => (Over.homMk (𝟙 T.left) rfl : Over.mk (𝟙 T.left ≫ T.hom) ⟶ T) ≫ lv a)` using `tateAt_congr M.univ N' (Category.id_comp g).symm _ _ (fun a => by congr 1) h0`. Conclude with `(GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points p D R b N N' hc M.X M.s M.univ T lv hadd hker hlin (𝟙 T.left) x' (x'.base (⊥ : PrimeSpectrum k')) (⊥ : PrimeSpectrum k') (by first`. Consider the case `exact specializes_rfl`. Consider the case `(rw [Scheme.id.base_apply])`. Consider the case `(simp only [Scheme.Hom.id_apply]; exact specializes_rfl)`.

Consider the case `exact (Subsingleton.elim (α := PrimeSpectrum k) _ _) ▸ specializes_rfl)).1 h1`. Take `⟨f, -, -⟩` from `(HY T lv).1 hlv`. Take `⟨u, hu⟩ : z ∈ Set.range g` from `by rw [hg]; rfl`. Use `⟨(f.left ≫ h).base u, ?_⟩` and prove the remaining obligations. Establish `hf : f.left ≫ h ≫ π = g` using `by rw [hh]; exact Over.w f`.

Rewrite using `[← hu, ← hf]`. Both sides reduce to the same expression.
-/
theorem forget_map_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (M : Model b N) (M' : Model b N') (t : M'.X ⟶ M.X), t ≫ M.s = M'.s → Nonempty (ObjMap (M'.univ.forget N hd hc) M.univ t) → IsFinite t ∧ Etale t ∧ Surjective t := by
  intro p _ D R _ _ b N N' hd hc h3 M M' π hπ ⟨om⟩
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, ηu, hYf, hYe, HY⟩ := GlobalTheory.T.exists_finite_etale_level_lift_scheme p D R b N N' hc hd M.X M.s M.univ
  let T0 : Over M.X := Over.mk π
  have hw : ∀ a, ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = T0.hom := fun a => by
    have w : (om.φ : M'.univ.A.left ⟶ M.univ.A.left) ≫ M.univ.A.hom = M'.univ.A.hom ≫ π := om.cart.1.w
    have w2 : (M'.univ.eta a).left ≫ M'.univ.A.hom = 𝟙 M'.X := Over.w (M'.univ.eta a)
    show ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = π
    erw [Category.assoc, w, ← Category.assoc, w2, Category.id_comp]
  let lv0 : D.La → (T0 ⟶ M.univ.A) := fun a => Over.homMk ((M'.univ.eta a).left ≫ om.φ) (hw a)
  have hl0 : IsLift M.univ N' T0 lv0 :=
    GlobalTheory.T.harrisTaylor_isLevelLift_of_point p D R b N N' hd hc M.X M'.X M.s M'.s M.univ M'.univ π om T0 (𝟙 M'.X) lv0
      (Category.id_comp π) fun a => (Category.id_comp _).symm
  obtain ⟨g0, hg0, -⟩ := (HY T0 lv0).1 hl0
  have hlY : IsLift M.univ N' Y ηu := (HY Y ηu).2 ⟨𝟙 Y, fun a => Category.id_comp _⟩
  obtain ⟨h, hh, hha⟩ := GlobalTheory.T.exists_unique_point_of_level_lift_harrisTaylor p D R b N N' h3 hd hc M M' π hπ om Y ηu hlY
  have e1 : g0.left ≫ h = 𝟙 M'.X := by
    refine GlobalTheory.T.harrisTaylor_higherLevel_points_eq_of_same_image p D R b N N' hd hc M.X M.s M.univ M' π hπ om M'.X _ _ ?_ fun a => ?_
    · rw [Category.assoc, hh, Over.w g0, Category.id_comp]
      rfl
    · rw [Category.id_comp, Category.assoc, ← hha a, ← Over.comp_left, hg0 a]
      rfl
  let hY : Y ⟶ T0 := Over.homMk h hh
  have e2 : hY ≫ g0 = 𝟙 Y := by
    obtain ⟨f, -, hf⟩ := (HY Y ηu).1 hlY
    have a1 := hf (hY ≫ g0) fun a => by
      rw [Category.assoc, hg0 a]
      ext
      simp only [Over.comp_left, Over.homMk_left, hY, lv0]
      rw [hha a]
    have a2 := hf (𝟙 Y) fun a => Category.id_comp _
    rw [a1, a2]
  have e2' : h ≫ g0.left = 𝟙 Y.left := by
    have := congrArg (fun q => q.left) e2
    simpa [hY] using this
  haveI : IsIso g0.left := ⟨⟨h, e1, e2'⟩⟩
  have e : π = g0.left ≫ Y.hom := (Over.w g0).symm
  have hfe : IsFinite π ∧ Etale π := by
    rw [e]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨hfe.1, hfe.2, ⟨fun z => ?_⟩⟩

  obtain ⟨k, _, _, g, hg⟩ := GlobalTheory.FinEt.exists_algClosed_point M.X z
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, g ≫ M.s = spMap β :=
    ⟨(Spec.preimage (g ≫ M.s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := M.univ.geom k g β hβ
  have hN' : 0 < N' := levelPos_of_coprime hc
  have hN : 0 < N := by omega
  have hk : 0 < N' / N := Nat.div_pos (Nat.le_of_dvd hN' hd) hN
  let T : Over M.X := Over.mk g
  let lv : D.La → (T ⟶ M.univ.A) := fun a => I.ev N' a
  have hadd : ∀ x y, lv (x + y) = lv x * lv y := fun x y => I.add N' x y
  have hker : ∀ x, lv (N' • x) = 1 := fun x => (I.ker N' hN' hc _).2 ⟨x, rfl⟩
  have hlin : ∀ (c : D.O) x, lv (c • x) = lv x ≫ M.univ.act.act c := fun c x => I.lin N' c x
  haveI : IsLocallyNoetherian T.left := by
    show IsLocallyNoetherian (Spec (CommRingCat.of k))
    infer_instance
  have hlv : IsLift M.univ N' T lv := by
    refine ⟨hadd, hker, hlin, fun x => ?_, fun k' _ _ x' => ?_⟩
    · show I.ev N' ((N' / N) • x) = toUnit T ≫ M.univ.eta x
      rw [hI x, I.ev_nsmul]
      have := I.tower N (N' / N) hN hk (by rw [Nat.mul_div_cancel' hd]; exact hc) x
      rwa [Nat.mul_div_cancel' hd] at this
    · have h0 : TateAt M.univ N' g (fun a => lv a) := ⟨I, fun y => rfl⟩
      have h1 : TateAt M.univ N' (𝟙 T.left ≫ T.hom)
          (fun a => (Over.homMk (𝟙 T.left) rfl : Over.mk (𝟙 T.left ≫ T.hom) ⟶ T) ≫ lv a) :=
        tateAt_congr M.univ N' (Category.id_comp g).symm _ _ (fun a => by congr 1) h0
      exact (GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points p D R b N N' hc M.X M.s M.univ T lv hadd hker hlin (𝟙 T.left) x'
        (x'.base (⊥ : PrimeSpectrum k')) (⊥ : PrimeSpectrum k') (by
          first
          | exact specializes_rfl
          | (rw [Scheme.id.base_apply])
          | (simp only [Scheme.Hom.id_apply]; exact specializes_rfl)
          | exact (Subsingleton.elim (α := PrimeSpectrum k) _ _) ▸ specializes_rfl)).1 h1
  obtain ⟨f, -, -⟩ := (HY T lv).1 hlv
  obtain ⟨u, hu⟩ : z ∈ Set.range g := by rw [hg]; rfl
  refine ⟨(f.left ≫ h).base u, ?_⟩
  have hf : f.left ≫ h ≫ π = g := by rw [hh]; exact Over.w f
  rw [← hu, ← hf]
  rfl

end GlobalTheory.UPel.HT
