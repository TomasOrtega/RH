import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Spec.preimage g).hom, (Spec.map_preimage g).symm⟩`.
-/
theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (g : Sp A ⟶ Sp B) : ∃ β : B →+* A, g = spMap β :=
  ⟨(Spec.preimage g).hom, (Spec.map_preimage g).symm⟩

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_inj' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
The claim follows from `(Spec.map_comp _ _).symm`.
-/
theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

def fnOn {L : Type} [CommRing L] {T : Scheme.{0}} (g : T ⟶ Sp L) : L →+* Γ(T, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show h.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β c)`. Establish `h1 : (h ≫ g).appTop = g.appTop ≫ h.appTop` using `Scheme.Hom.comp_appTop _ _`. Establish `h2` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)`. Establish `h3` using `congrArg (fun φ => φ.hom (c : L)) h2`.

Rewrite `h1` using `[e]`. Establish `h4` using `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) h1`. Conclude with `h4.symm.trans h3.symm`.
-/
theorem map_fnOn {L k : Type} [CommRing L] [CommRing k] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp k ⟶ T)
    (β : L →+* k) (e : h ≫ g = spMap β) (c : Lˣ) :
    Units.map h.appTop.hom.toMonoidHom (Units.map (fnOn g).toMonoidHom c) = unitOn (Units.map β.toMonoidHom c) := by
  apply Units.ext
  show h.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) =
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β c)
  have h1 : (h ≫ g).appTop = g.appTop ≫ h.appTop := Scheme.Hom.comp_appTop _ _
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  have h3 := congrArg (fun φ => φ.hom (c : L)) h2
  rw [e] at h1
  have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) h1
  exact h4.symm.trans h3.symm

abbrev TateAt (D : Datum H) (t : SAB H S) {k : Type} [Field k] (x : Sp k ⟶ S) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
    (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

/- English proof (translation)
Use `D.fin` as an intermediate fact. Use `D.proj` as an intermediate fact. Establish `h : Module.Finite ℤ D.La` using `Module.Finite.trans (𝓞 E) D.La`. Establish `: Module.Flat ℤ D.La` using `Module.Flat.trans ℤ (𝓞 E) D.La`. Conclude with `⟨inferInstance, h⟩`.
-/
theorem datum_free (D : Datum H) : Module.Free ℤ D.La ∧ Module.Finite ℤ D.La := by
  have := D.fin
  have := D.proj
  have h : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  exact ⟨inferInstance, h⟩

/- English proof (translation)
Use `t.act.hom c` as an intermediate fact. Rewrite using `[add_map_nsmul t.act.add, MonObj.comp_pow, MonObj.pow_comp]`.
-/
theorem act_nsmul (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) (c : 𝓞 E) :
    x ≫ t.act.act (n • c) = (x ^ n) ≫ t.act.act c := by
  have := t.act.hom c
  rw [add_map_nsmul t.act.add, MonObj.comp_pow, MonObj.pow_comp]

/- English proof (translation)
Take `⟨hfree, hfin⟩` from `datum_free D`. Establish `hLf : IsFinite (spMap (algebraMap B L))`. Rewrite using `[spMap, IsFinite.SpecMap_iff]`. Conclude with `RingHom.finite_algebraMap.mpr inferInstance`. Establish `hLe : Etale (spMap (algebraMap B L))`.

Rewrite using `[spMap, HasRingHomProperty.Spec_iff (P := @Etale)]`. Establish `: Algebra.FormallyEtale B L` using `Algebra.FormallyEtale.of_isSeparable B L`. Establish `: Algebra.FinitePresentation B L` using `Algebra.FinitePresentation.of_finiteType.1 inferInstance`. Conclude with `RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩`. Set `C : Over S` to `Over.mk (pullback.fst s (spMap (algebraMap B L)))`.

Establish `hC1 : IsFinite C.hom` using `inferInstanceAs (IsFinite (pullback.fst s (spMap (algebraMap B L))))`. Establish `hC2 : Etale C.hom` using `inferInstanceAs (Etale (pullback.fst s (spMap (algebraMap B L))))`. Use `R.1` as an intermediate fact. Use `R.2.1` as an intermediate fact. Take `⟨hY1, hY2⟩` from `finiteEtale_tensor Z C`.

Set `g : (Z ⊗ C).left ⟶ Sp L` to `(snd Z C).left ≫ pullback.snd s (spMap (algebraMap B L))`. Establish `hg : g ≫ spMap (algebraMap B L) = (Z ⊗ C).hom ≫ s`. Rewrite using `[Category.assoc, ← pullback.condition, ← Category.assoc]`. Conclude with `congrArg (· ≫ s) (Over.w (snd Z C))`. Set `y : D.La → (Z ⊗ C ⟶ t.G)` to `fun a => fst Z C ≫ et a`.

Establish `yadd : ∀ a c, y (a + c) = y a * y c` using `fun a c => by simp only [y, R.2.2.1, MonObj.comp_mul]`. Establish `ypow : ∀ a, y a ^ N = 1` using `fun a => by simp only [y]; rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one]`. Establish `ymod : ∀ a c, y (a + N • c) = y a` using `fun a c => by rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]`. Establish `hchar : CharZero L` using `charZero_of_injective_algebraMap (algebraMap B L).injective`. Establish `hu : IsUnit (N : Γ((Z ⊗ C).left, ⊤))`.

Use `(IsUnit.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')).map (fnOn g)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨κ, _, q, hq⟩` from `exists_finite_mod D.La hN`. Take `⟨κ', _, q', hq'⟩` from `exists_finite_mod (𝓞 E) hN`. Establish `c1 : ClopenCond (Z ⊗ C) fun _ h => ∀ (c : 𝓞 E) a, h ≫ y (c • a) = h ≫ y a ≫ t.act.act c`.

Use `ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_` and prove the remaining obligations. Use `t.act.hom c` as an intermediate fact. Use `R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ t.act.act c) (fun a a' => by rw [smul_add, yadd]) (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by` and prove the remaining obligations. Rewrite using `[← MonObj.pow_comp, ypow, MonObj.one_comp]`. Take `⟨d, rfl⟩` from `hq' c c' e`.

Use `t.act.hom d` as an intermediate fact. Rewrite using `[add_smul, smul_assoc, ymod, Hc, t.act.add, MonObj.comp_mul, act_nsmul, ypow, MonObj.one_comp, _root_.mul_one]`. Establish `c2 : ClopenCond (Z ⊗ C) fun _ h => ∀ p : D.La × D.La, Out.WeilIs t.G t.PP.L N (h ≫ y p.1) (h ≫ y p.2) (Units.map (h.left.appTop).hom.toMonoidHom (Units.map (fnOn g).toMonoidHom (ξ ^ D.EF p.1 p.2)))`. Use `ClopenCond.forall_of_finite (Prod.map q q) (fun p => hW _ _ _ _ hu (ypow _) (ypow _) ?_) fun p p' e T' h Hc => ?_` and prove the remaining obligations. Rewrite using `[← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow, map_one]`.

Take `⟨a, b⟩` from `p`. Take `⟨a', b'⟩` from `p'`. Take `⟨c, rfl⟩` from `hq a a' (congrArg Prod.fst e)`. Take `⟨d, rfl⟩` from `hq b b' (congrArg Prod.snd e)`. Establish `: ξ ^ D.EF (a + N • c) (b + N • d) = ξ ^ D.EF a b`.

Establish `: D.EF (a + N • c) (b + N • d) = D.EF a b + N * (D.EF a d + D.EF c (b + N • d))`. Simplify using `only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, zpow_add, zpow_mul, zpow_natCast, hξ, one_zpow, _root_.mul_one]`. Simplify using `only at Hc ⊢`.

Rewrite using `[ymod, ymod, this]` and apply the resulting hypothesis. Take `⟨U, hU, HU⟩` from `c1.and c2`. Take `⟨W, i, hW1, hW2, -, Hi⟩` from `exists_sub U hU`. Use `⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul], fun a => by beta_reduce; rw [← MonObj.comp_pow, ypow, MonObj.comp_one], fun k _ x β hx α' hadd hpow => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨w, hw⟩`.

Take `⟨h1, h2⟩` from `(HU _ (w ≫ i)).2 ((Hi _ _).2 ⟨w, rfl⟩)`. Take `⟨β', hβ'⟩` from `exists_spMap (A := k) ((w ≫ i).left ≫ g)`. Use `⟨β', spMap_inj' ?_, fun c a => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[← spMap_comp'', ← hβ', ← hx, Category.assoc, hg, ← Category.assoc]`. Conclude with `congrArg (· ≫ s) (Over.w (w ≫ i))`.

Rewrite using `[← hw, ← hw, ← Category.assoc, h1]`. Simplify using `only [Category.assoc]`. Use `h2 (a, b)` as an intermediate fact. Rewrite `this` using `[map_fnOn g _ β' hβ', map_zpow, Category.assoc, Category.assoc, hw, hw]`. Conclude with `this`.

Introduce and unpack `⟨β', hβ', h1, h2⟩`. Take `⟨z, hz, -⟩` from `R.2.2.2.2 _ α' hadd hpow`. Set `c : Over.mk x ⟶ C` to `Over.homMk (pullback.lift x (spMap β') (by rw [hx, spMap_comp'', hβ'])) (pullback.lift_fst _ _ _)`. Establish `hy : ∀ a, lift z c ≫ y a = α' a` using `fun a => by simp only [y]; rw [lift_fst_assoc, hz]`. Establish `hg' : (lift z c).left ≫ g = spMap β'`.

Simplify using `only [g]`. Rewrite using `[← Category.assoc, ← Over.comp_left, lift_snd]`. Conclude with `pullback.lift_snd _ _ _`. Take `⟨w, hw⟩` from `(Hi _ (lift z c)).1 ((HU _ _).1 ⟨fun c a => by rw [hy, ← Category.assoc, hy, h1], fun p => by`. Rewrite using `[map_fnOn g _ β' hg', map_zpow, hy, hy]`.

Conclude with `h2 _ _⟩)`. Conclude with `⟨w, fun a => by rw [← Category.assoc, hw, hy]⟩`.
-/
theorem exists_full (t : SAB H S) {B L : Type} [Field B] [CharZero B] [Field L] [Algebra B L] [FiniteDimensional B L]
    (s : S ⟶ Sp B) {N : ℕ} (hN : 0 < N) {ξ : Lˣ} (hξ : ξ ^ N = 1)
    {Z : Over S} {et : D.La → (Z ⟶ t.G)} (R : RepTors t.G N D.La Z et)
    (hW : ∀ (T : Over S) (x y : T ⟶ t.G) (c : Γ(T.left, ⊤)ˣ), IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
      c ^ N = 1 → ClopenCond T fun _ h =>
        Out.WeilIs t.G t.PP.L N (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c)) :
    ∃ (W : Over S) (α : D.La → (W ⟶ t.G)), IsFinite W.hom ∧ Etale W.hom ∧ (∀ a c, α (a + c) = α a * α c) ∧
      (∀ a, α a ^ N = 1) ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
        ∀ α' : D.La → (Over.mk x ⟶ t.G), (∀ a c, α' (a + c) = α' a * α' c) → (∀ a, α' a ^ N = 1) →
          ((∃ w : Over.mk x ⟶ W, ∀ a, w ≫ α a = α' a) ↔ ∃ β' : L →+* k, β'.comp (algebraMap B L) = β ∧
            (∀ (c : 𝓞 E) a, α' (c • a) = α' a ≫ t.act.act c) ∧
            ∀ a b, Out.WeilIs t.G t.PP.L N (α' a) (α' b) (unitOn (Units.map β'.toMonoidHom ξ ^ D.EF a b))) := by
  obtain ⟨hfree, hfin⟩ := datum_free D
  have hLf : IsFinite (spMap (algebraMap B L)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hLe : Etale (spMap (algebraMap B L)) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isSeparable B L
    have : Algebra.FinitePresentation B L := Algebra.FinitePresentation.of_finiteType.1 inferInstance
    exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  let C : Over S := Over.mk (pullback.fst s (spMap (algebraMap B L)))
  have hC1 : IsFinite C.hom := inferInstanceAs (IsFinite (pullback.fst s (spMap (algebraMap B L))))
  have hC2 : Etale C.hom := inferInstanceAs (Etale (pullback.fst s (spMap (algebraMap B L))))
  have := R.1
  have := R.2.1
  obtain ⟨hY1, hY2⟩ := finiteEtale_tensor Z C
  let g : (Z ⊗ C).left ⟶ Sp L := (snd Z C).left ≫ pullback.snd s (spMap (algebraMap B L))
  have hg : g ≫ spMap (algebraMap B L) = (Z ⊗ C).hom ≫ s := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ s) (Over.w (snd Z C))
  let y : D.La → (Z ⊗ C ⟶ t.G) := fun a => fst Z C ≫ et a
  have yadd : ∀ a c, y (a + c) = y a * y c := fun a c => by simp only [y, R.2.2.1, MonObj.comp_mul]
  have ypow : ∀ a, y a ^ N = 1 := fun a => by simp only [y]; rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one]
  have ymod : ∀ a c, y (a + N • c) = y a := fun a c => by rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap B L).injective
  have hu : IsUnit (N : Γ((Z ⊗ C).left, ⊤)) := by
    have := (IsUnit.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')).map (fnOn g)
    rwa [map_natCast] at this
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod D.La hN
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod (𝓞 E) hN
  have c1 : ClopenCond (Z ⊗ C) fun _ h => ∀ (c : 𝓞 E) a, h ≫ y (c • a) = h ≫ y a ≫ t.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := t.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ t.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := t.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, t.act.add, MonObj.comp_mul, act_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond (Z ⊗ C) fun _ h => ∀ p : D.La × D.La, Out.WeilIs t.G t.PP.L N (h ≫ y p.1) (h ≫ y p.2)
      (Units.map (h.left.appTop).hom.toMonoidHom (Units.map (fnOn g).toMonoidHom (ξ ^ D.EF p.1 p.2))) := by
    refine ClopenCond.forall_of_finite (Prod.map q q) (fun p => hW _ _ _ _ hu (ypow _) (ypow _) ?_)
      fun p p' e T' h Hc => ?_
    · rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow, map_one]
    · obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := p'
      obtain ⟨c, rfl⟩ := hq a a' (congrArg Prod.fst e)
      obtain ⟨d, rfl⟩ := hq b b' (congrArg Prod.snd e)
      have : ξ ^ D.EF (a + N • c) (b + N • d) = ξ ^ D.EF a b := by
        have : D.EF (a + N • c) (b + N • d) = D.EF a b + N * (D.EF a d + D.EF c (b + N • d)) := by
          simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
          ring
        rw [this, zpow_add, zpow_mul, zpow_natCast, hξ, one_zpow, _root_.mul_one]
      dsimp only at Hc ⊢
      rwa [ymod, ymod, this]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, -, Hi⟩ := exists_sub U hU
  refine ⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, ypow, MonObj.comp_one], fun k _ x β hx α' hadd hpow => ⟨?_, ?_⟩⟩
  · rintro ⟨w, hw⟩
    obtain ⟨h1, h2⟩ := (HU _ (w ≫ i)).2 ((Hi _ _).2 ⟨w, rfl⟩)
    obtain ⟨β', hβ'⟩ := exists_spMap (A := k) ((w ≫ i).left ≫ g)
    refine ⟨β', spMap_inj' ?_, fun c a => ?_, fun a b => ?_⟩
    · rw [← spMap_comp'', ← hβ', ← hx, Category.assoc, hg, ← Category.assoc]
      exact congrArg (· ≫ s) (Over.w (w ≫ i))
    · rw [← hw, ← hw, ← Category.assoc, h1]
      simp only [Category.assoc]
    · have := h2 (a, b)
      rw [map_fnOn g _ β' hβ', map_zpow, Category.assoc, Category.assoc, hw, hw] at this
      exact this
  · rintro ⟨β', hβ', h1, h2⟩
    obtain ⟨z, hz, -⟩ := R.2.2.2.2 _ α' hadd hpow
    let c : Over.mk x ⟶ C := Over.homMk (pullback.lift x (spMap β') (by rw [hx, spMap_comp'', hβ']))
      (pullback.lift_fst _ _ _)
    have hy : ∀ a, lift z c ≫ y a = α' a := fun a => by simp only [y]; rw [lift_fst_assoc, hz]
    have hg' : (lift z c).left ≫ g = spMap β' := by
      simp only [g]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact pullback.lift_snd _ _ _
    obtain ⟨w, hw⟩ := (Hi _ (lift z c)).1 ((HU _ _).1 ⟨fun c a => by rw [hy, ← Category.assoc, hy, h1], fun p => by
      rw [map_fnOn g _ β' hg', map_zpow, hy, hy]
      exact h2 _ _⟩)
    exact ⟨w, fun a => by rw [← Category.assoc, hw, hy]⟩

end GlobalTheory.LevCover
