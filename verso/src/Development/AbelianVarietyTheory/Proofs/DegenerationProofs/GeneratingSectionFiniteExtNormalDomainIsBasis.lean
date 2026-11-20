import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGenBasis

/- English proof (translation)
Take `rfl : (fun k => p ≫ φ k) = φ'` from `funext e`. Use `p.app_injective _ (fn_ext fun y hy => ?_)` and prove the remaining obligations. Establish `hy' : (𝟙 Y' : _ ⟶ _) y ∈ LB.wchart L (fun k => p ≫ φ k) j` using `Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k`. Conclude with `(gs_res _ y _ hy' _).symm.trans ((congrArg (gs (𝟙 _) y _) (h j)).trans (gs_res _ y _ hy' _))`.
-/
theorem pullTo_injective {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X)} (p : Y' ⟶ Y) (e : ∀ k, p ≫ φ k = φ' k) [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    {s t : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, (VVRank.pullTo s p e).f j = (VVRank.pullTo t p e).f j) (j) :
    s.f j = t.f j := by
  obtain rfl : (fun k => p ≫ φ k) = φ' := funext e
  refine p.app_injective _ (fn_ext fun y hy => ?_)
  have hy' : (𝟙 Y' : _ ⟶ _) y ∈ LB.wchart L (fun k => p ≫ φ k) j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  exact (gs_res _ y _ hy' _).symm.trans ((congrArg (gs (𝟙 _) y _) (h j)).trans (gs_res _ y _ hy' _))

/- English proof (translation)
Establish `hp : IsPullback (h ▷ G).left (fst T' G).left (fst T G).left h.left`. Use `IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_ (IsPullback.of_hasPullback T.hom G.hom).flip` and prove the remaining obligations. Rewrite using `[VVRank.whisker_snd_left, Over.w]`. Conclude with `(IsPullback.of_hasPullback T'.hom G.hom).flip`. Rewrite using `[← Over.comp_left, whiskerRight_fst, Over.comp_left]`.

Establish `: Flat (fst T G).left` using `MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.hom G.hom).flip inferInstance`. Establish `: IsSchemeTheoreticallyDominant (h ▷ G).left` using `.of_isPullback hp.flip`. Establish `: QuasiCompact (h ▷ G).left` using `MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance`. Introduce `s t e`. Conclude with `Subtype.ext (funext (pullTo_injective (s := SecM.toSec G s) (t := SecM.toSec G t) (h ▷ G).left (fun _ => VVRank.whisker_snd_left G h) fun j => congrFun (congrArg Subtype.val e) j))`.
-/
theorem pullM_injective {S : Scheme.{0}} (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left) (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) [IsSchemeTheoreticallyDominant h.left] [QuasiCompact h.left] :
    Function.Injective (VVRank.pullM G L a h) := by
  have hp : IsPullback (h ▷ G).left (fst T' G).left (fst T G).left h.left := by
    refine IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_
      (IsPullback.of_hasPullback T.hom G.hom).flip
    · rw [VVRank.whisker_snd_left, Over.w]
      exact (IsPullback.of_hasPullback T'.hom G.hom).flip
    · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have : Flat (fst T G).left :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.hom G.hom).flip inferInstance
  have : IsSchemeTheoreticallyDominant (h ▷ G).left := .of_isPullback hp.flip
  have : QuasiCompact (h ▷ G).left := MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  intro s t e
  exact Subtype.ext (funext (pullTo_injective (s := SecM.toSec G s) (t := SecM.toSec G t) (h ▷ G).left
    (fun _ => VVRank.whisker_snd_left G h) fun j => congrFun (congrArg Subtype.val e) j))

/- English proof (translation)
Establish `h₁ : i' (b / a) = algebraMap W' _ r`. Rewrite using `[map_div₀, h, mul_div_cancel_right₀ _ ((map_ne_zero i').2 ha)]`. Take `⟨p, hp, h₂⟩` from `hf.to_isIntegral r`. Establish `h₃ : IsIntegral W (b / a)` using `⟨p, hp, i'.injective (by`. Rewrite using `[Polynomial.hom_eval₂, hi, h₁, ← Polynomial.hom_eval₂, h₂, map_zero, map_zero])⟩`.

Take `⟨r₀, hr⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral h₃`. Conclude with `⟨r₀, by rw [hr, div_mul_cancel₀ _ ha]⟩`.
-/
theorem exists_eq_mul {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    (i : W →+* W') (hf : i.Finite) (i' : FractionRing W →+* FractionRing W')
    (hi : i'.comp (algebraMap W _) = (algebraMap W' _).comp i) {a b : FractionRing W} (ha : a ≠ 0) {r : W'}
    (h : i' b = algebraMap W' _ r * i' a) : ∃ r₀ : W, b = algebraMap W _ r₀ * a := by
  have h₁ : i' (b / a) = algebraMap W' _ r := by
    rw [map_div₀, h, mul_div_cancel_right₀ _ ((map_ne_zero i').2 ha)]
  obtain ⟨p, hp, h₂⟩ := hf.to_isIntegral r
  have h₃ : IsIntegral W (b / a) := ⟨p, hp, i'.injective (by
    rw [Polynomial.hom_eval₂, hi, h₁, ← Polynomial.hom_eval₂, h₂, map_zero, map_zero])⟩
  obtain ⟨r₀, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h₃
  exact ⟨r₀, by rw [hr, div_mul_cancel₀ _ ha]⟩

/- English proof (translation)
Establish `hg : Function.Injective ((algebraMap W' (FractionRing W')).comp i)`. Rewrite using `[RingHom.coe_comp]`. Conclude with `(IsFractionRing.injective W' (FractionRing W')).comp hi`. Use `⟨IsFractionRing.lift (K := FractionRing W) hg, RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, IsFractionRing.lift_algebraMap]`.
-/
theorem exists_fractionMap {W W' : Type} [CommRing W] [IsDomain W] [CommRing W'] [IsDomain W'] (i : W →+* W')
    (hi : Function.Injective i) : ∃ i' : FractionRing W →+* FractionRing W',
      i'.comp (algebraMap W _) = (algebraMap W' _).comp i := by
  have hg : Function.Injective ((algebraMap W' (FractionRing W')).comp i) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective W' (FractionRing W')).comp hi
  refine ⟨IsFractionRing.lift (K := FractionRing W) hg, RingHom.ext fun x => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

/- English proof (translation)
The claim follows from `(congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm`.
-/
theorem appTop_inv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f x) :=
  (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

/- English proof (translation)
The claim follows from `ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv`.
-/
theorem inv_bijective (R : Type) [CommRing R] :
    Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

/- English proof (translation)
Take `⟨a, rfl⟩` from `(inv_bijective _).2 a`. Take `⟨b, rfl⟩` from `(inv_bijective _).2 b`. Take `⟨r, rfl⟩` from `(inv_bijective _).2 r`. Rewrite `h` using `[appTop_inv, appTop_inv, appTop_inv, ← map_mul]`. Take `⟨r₀, hr⟩` from `exists_eq_mul i hf i' hi (a := a) (fun e => ha (by rw [e, map_zero])) ((inv_bijective (FractionRing W')).1 h)`.

Conclude with `⟨(Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r₀, by`. Rewrite using `[appTop_inv (algebraMap W (FractionRing W)), ← map_mul, ← hr]⟩`.
-/
theorem exists_eq_mul_fn {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    (i : W →+* W') (hf : i.Finite) (i' : FractionRing W →+* FractionRing W')
    (hi : i'.comp (algebraMap W _) = (algebraMap W' _).comp i) {a b : Γ(Sp (FractionRing W), ⊤)} (ha : a ≠ 0)
    {r : Γ(Sp W', ⊤)} (h : (spMap i').appTop.hom b = (jK W').appTop.hom r * (spMap i').appTop.hom a) :
    ∃ r₀ : Γ(Sp W, ⊤), b = (jK W).appTop.hom r₀ * a := by
  obtain ⟨a, rfl⟩ := (inv_bijective _).2 a
  obtain ⟨b, rfl⟩ := (inv_bijective _).2 b
  obtain ⟨r, rfl⟩ := (inv_bijective _).2 r
  rw [appTop_inv, appTop_inv, appTop_inv, ← map_mul] at h
  obtain ⟨r₀, hr⟩ := exists_eq_mul i hf i' hi (a := a) (fun e => ha (by rw [e, map_zero]))
    ((inv_bijective (FractionRing W')).1 h)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r₀, by
    rw [appTop_inv (algebraMap W (FractionRing W)), ← map_mul, ← hr]⟩

/- English proof (translation)
Take `⟨a, ha, -⟩` from `h₀ (p σ)`. Establish `ha0 : a ≠ 0` using `fun h => hne (ha.trans (by rw [h, zero_smul]))`. Use `⟨Fintype.linearIndependent_iff.2 fun c hc k => ?_, eq_top_iff.2 fun s _ => ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[Fin.sum_univ_one]`. Rewrite using `[Subsingleton.elim k 0]`.

Establish `t` using `congrArg p hc`. Rewrite `t` using `[map_smulₛₗ, ha, smul_smul, map_zero]`. Establish `t'` using `(h₀ 0).unique t.symm (zero_smul _ _).symm`. Conclude with `hf (((mul_eq_zero.1 t').resolve_right ha0).trans (map_zero _).symm)`. Take `⟨b, hb, -⟩` from `h₀ (p s)`.

Take `⟨r, hr⟩` from `hgen s`. Establish `t` using `congrArg p' hr`. Rewrite `t` using `[map_smulₛₗ, ← hsq, ← hsq, ha, hb, map_smulₛₗ, map_smulₛₗ, smul_smul]`. Take `⟨r₀, hr₀⟩` from `hint a b r ha0 ((h₁ _).unique rfl t)`. Establish `: s = r₀ • σ` using `hp (by rw [map_smulₛₗ, ha, hb, smul_smul, hr₀])`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)`.
-/
theorem basis_of_square {A A' K K' M M' N N' : Type} [CommRing A] [CommRing A'] [CommRing K] [CommRing K'] [IsDomain K]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N'] [Module A M] [Module A' M'] [Module K N]
    [Module K' N'] {f : A →+* K} {g : A →+* A'} {f' : A' →+* K'} {g' : K →+* K'} (p : M →ₛₗ[f] N) (q : M →ₛₗ[g] M')
    (p' : M' →ₛₗ[f'] N') (q' : N →ₛₗ[g'] N') (hsq : ∀ x, q' (p x) = p' (q x)) (hp : Function.Injective p)
    (hf : Function.Injective f) (e : N) (h₀ : ∀ s, ∃! c : K, s = c • e) (h₁ : ∀ s, ∃! c : K', s = c • q' e) (σ : M)
    (hne : p σ ≠ 0) (hgen : ∀ s, ∃ r : A', q s = r • q σ)
    (hint : ∀ a b r, a ≠ 0 → g' b = f' r * g' a → ∃ r₀, b = f r₀ * a) :
    LinearIndependent A (fun _ : Fin 1 => σ) ∧ Submodule.span A (Set.range fun _ : Fin 1 => σ) = ⊤ := by
  obtain ⟨a, ha, -⟩ := h₀ (p σ)
  have ha0 : a ≠ 0 := fun h => hne (ha.trans (by rw [h, zero_smul]))
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc k => ?_, eq_top_iff.2 fun s _ => ?_⟩
  · rw [Fin.sum_univ_one] at hc
    rw [Subsingleton.elim k 0]
    have t := congrArg p hc
    rw [map_smulₛₗ, ha, smul_smul, map_zero] at t
    have t' := (h₀ 0).unique t.symm (zero_smul _ _).symm
    exact hf (((mul_eq_zero.1 t').resolve_right ha0).trans (map_zero _).symm)
  · obtain ⟨b, hb, -⟩ := h₀ (p s)
    obtain ⟨r, hr⟩ := hgen s
    have t := congrArg p' hr
    rw [map_smulₛₗ, ← hsq, ← hsq, ha, hb, map_smulₛₗ, map_smulₛₗ, smul_smul] at t
    obtain ⟨r₀, hr₀⟩ := hint a b r ha0 ((h₁ _).unique rfl t)
    have : s = r₀ • σ := hp (by rw [map_smulₛₗ, ha, hb, smul_smul, hr₀])
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

/- English proof (translation)
Introduce `S G _ _ L hL W W' _ _ _ _ _ i hinj hf χ σ hgen ⟨e, he⟩ hne`. Take `⟨i', hi⟩` from `exists_fractionMap i hinj`. Establish `hsq : spMap i' ≫ jK W = jK W' ≫ spMap i`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]`. Set `hK : Over.mk (jK W ≫ χ) ⟶ Over.mk χ` to `Over.homMk (jK W) rfl`.

Set `hI : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ` to `Over.homMk (spMap i) rfl`. Set `hI' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ)` to `Over.homMk (spMap i') rfl`. Set `hK' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (spMap i ≫ χ)` to `Over.homMk (jK W') (by`. Express the relevant statement in the definitionally equal form `jK W' ≫ spMap i ≫ χ = spMap i' ≫ jK W ≫ χ`. Rewrite using `[← Category.assoc, ← hsq, Category.assoc])`.

Establish `hsq' : hI' ≫ hK = hK' ≫ hI` using `Over.OverMorphism.ext hsq`. Establish `: IsSchemeTheoreticallyDominant hK.left` using `(ExtUnique.spec_fractionRing W (FractionRing W)).2`. Establish `: QuasiCompact hK.left` using `(ExtUnique.spec_fractionRing W (FractionRing W)).1`. Establish `hρ` using `pullM_injective G L ((1 : ℕ) : ℤ) hK`. Establish `hid : spMap (RingHom.id (FractionRing W)) = 𝟙 _` using `Spec.map_id _`.

Establish `h₀ : ∀ s : SecM G L ((1 : ℕ) : ℤ) (Over.mk (jK W ≫ χ)), ∃! c : Γ((Over.mk (jK W ≫ χ)).left, ⊤), s = c • SecM.ofSec G e` using `fun s => by`. Establish `q` using `he _ (RingHom.id _) _ (by rw [hid, Category.id_comp]) s`. Rewrite `q` using `[← VVRank.pullM_ofSec, show (Over.homMk (spMap (RingHom.id (FractionRing W))) _ : Over.mk (jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ)) = 𝟙 _ from Over.OverMorphism.ext hid, VVRank.pullM_id G hL]`. Then use the resulting hypothesis. Establish `h₁ : ∀ s, ∃! c : Γ((Over.mk (spMap i' ≫ jK W ≫ χ)).left, ⊤), s = c • VVRank.pullM G L ((1 : ℕ) : ℤ) hI' (SecM.ofSec G e)` using `he _ i' _ rfl`. Establish `hdom : IsDomain Γ((Over.mk (jK W ≫ χ)).left, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of (FractionRing W))).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _`.

Establish `key` using `basis_of_square (VVRank.pullM G L ((1 : ℕ) : ℤ) hK) (VVRank.pullM G L _ hI) (VVRank.pullM G L _ hK') (VVRank.pullM G L _ hI') (fun x => by rw [VVRank.pullM_comp G hL, VVRank.pullM_comp G hL, hsq']) hρ (hK.left.app_injective ⊤) _ h₀ h₁ (SecM.ofSec G σ) hne (fun s => (hgen (SecM.to …`. Rewrite `key` using `[← VVRank.pullM_id G hL _ (SecM.ofSec G σ)]`. Conclude with `(GlobalTheory.LN.PolFrames.basisAlong_iff G L 1 (𝟙 _) hL (b' := fun _ => VVRank.pullS G _ (𝟙 _) σ) fun _ => VVRank.isPullSec_pullS G _ _ σ).2 key`.
-/
theorem basisAlong_of_isGenSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left), L.IsLB → ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (χ : Sp W ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))), IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ) σ) → (∃ e, UnivBasis G L (jK W ≫ χ) e) → SecM.ofSec G (VVRank.pullS G _ (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) σ) ≠ 0 → GlobalTheory.LN.BasisAlong G L 1 (𝟙 (Over.mk χ)) (fun _ : Fin 1 => σ) := by
  intro S G _ _ L hL W W' _ _ _ _ _ i hinj hf χ σ hgen ⟨e, he⟩ hne
  obtain ⟨i', hi⟩ := exists_fractionMap i hinj
  have hsq : spMap i' ≫ jK W = jK W' ≫ spMap i := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  let hK : Over.mk (jK W ≫ χ) ⟶ Over.mk χ := Over.homMk (jK W) rfl
  let hI : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap i) rfl
  let hI' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ) := Over.homMk (spMap i') rfl
  let hK' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (spMap i ≫ χ) := Over.homMk (jK W') (by
    change jK W' ≫ spMap i ≫ χ = spMap i' ≫ jK W ≫ χ
    rw [← Category.assoc, ← hsq, Category.assoc])
  have hsq' : hI' ≫ hK = hK' ≫ hI := Over.OverMorphism.ext hsq
  have : IsSchemeTheoreticallyDominant hK.left := (ExtUnique.spec_fractionRing W (FractionRing W)).2
  have : QuasiCompact hK.left := (ExtUnique.spec_fractionRing W (FractionRing W)).1
  have hρ := pullM_injective G L ((1 : ℕ) : ℤ) hK
  have hid : spMap (RingHom.id (FractionRing W)) = 𝟙 _ := Spec.map_id _
  have h₀ : ∀ s : SecM G L ((1 : ℕ) : ℤ) (Over.mk (jK W ≫ χ)), ∃! c : Γ((Over.mk (jK W ≫ χ)).left, ⊤),
      s = c • SecM.ofSec G e := fun s => by
    have q := he _ (RingHom.id _) _ (by rw [hid, Category.id_comp]) s
    rwa [← VVRank.pullM_ofSec, show (Over.homMk (spMap (RingHom.id (FractionRing W))) _ :
      Over.mk (jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ)) = 𝟙 _ from Over.OverMorphism.ext hid, VVRank.pullM_id G hL] at q
  have h₁ : ∀ s, ∃! c : Γ((Over.mk (spMap i' ≫ jK W ≫ χ)).left, ⊤),
      s = c • VVRank.pullM G L ((1 : ℕ) : ℤ) hI' (SecM.ofSec G e) := he _ i' _ rfl
  have hdom : IsDomain Γ((Over.mk (jK W ≫ χ)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing W))).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have key := basis_of_square (VVRank.pullM G L ((1 : ℕ) : ℤ) hK) (VVRank.pullM G L _ hI) (VVRank.pullM G L _ hK')
    (VVRank.pullM G L _ hI') (fun x => by rw [VVRank.pullM_comp G hL, VVRank.pullM_comp G hL, hsq']) hρ
    (hK.left.app_injective ⊤) _ h₀ h₁ (SecM.ofSec G σ) hne
    (fun s => (hgen (SecM.toSec G (VVRank.pullM G L _ hI s))).imp fun _ hr => Subtype.ext (funext hr))
    fun a b r ha h => exists_eq_mul_fn i hf i' hi ha h
  rw [← VVRank.pullM_id G hL _ (SecM.ofSec G σ)] at key
  exact (GlobalTheory.LN.PolFrames.basisAlong_iff G L 1 (𝟙 _) hL
    (b' := fun _ => VVRank.pullS G _ (𝟙 _) σ) fun _ => VVRank.isPullSec_pullS G _ _ σ).2 key

end GlobalTheory.Ex.OneGenBasis
end
