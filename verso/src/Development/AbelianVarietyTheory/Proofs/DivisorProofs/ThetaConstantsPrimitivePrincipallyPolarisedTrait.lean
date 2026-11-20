import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrSplitExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NzEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitiveAtUniformisedTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

/- English proof (translation)
Use `letI := g.toAlgebra`. Use `letI := j.toAlgebra`. Use `haveI : Algebra.IsIntegral V W := ⟨hg⟩`. Use `haveI : Module.IsTorsionFree V W := Module.isTorsionFree_iff_algebraMap_injective.2 hgi`. Use `haveI : Module.IsTorsionFree V K := Module.isTorsionFree_iff_algebraMap_injective.2 hj`.

Set `f : W →ₐ[V] K` to `IsAlgClosed.lift`. Establish `hc : f.toRingHom.comp (algebraMap V W) = j` using `RingHom.ext fun a => f.commutes a`. Use `⟨f.toRingHom, hc, ?_⟩` and prove the remaining obligations. Establish `hk : (RingHom.ker f.toRingHom).comap (algebraMap V W) = ⊥`. Rewrite using `[RingHom.comap_ker, hc]`.

Conclude with `(RingHom.injective_iff_ker_eq_bot j).1 hj`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).2 (Ideal.eq_bot_of_comap_eq_bot hk)`.
-/
theorem exists_embed_integral {V W K : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] [Field K]
    [IsAlgClosed K] (g : V →+* W) (hg : g.IsIntegral) (hgi : Function.Injective g) (j : V →+* K)
    (hj : Function.Injective j) : ∃ j' : W →+* K, j'.comp g = j ∧ Function.Injective j' := by
  letI := g.toAlgebra
  letI := j.toAlgebra
  haveI : Algebra.IsIntegral V W := ⟨hg⟩
  haveI : Module.IsTorsionFree V W := Module.isTorsionFree_iff_algebraMap_injective.2 hgi
  haveI : Module.IsTorsionFree V K := Module.isTorsionFree_iff_algebraMap_injective.2 hj
  let f : W →ₐ[V] K := IsAlgClosed.lift
  have hc : f.toRingHom.comp (algebraMap V W) = j := RingHom.ext fun a => f.commutes a
  refine ⟨f.toRingHom, hc, ?_⟩
  have hk : (RingHom.ker f.toRingHom).comap (algebraMap V W) = ⊥ := by
    rw [RingHom.comap_ker, hc]
    exact (RingHom.injective_iff_ker_eq_bot j).1 hj
  exact (RingHom.injective_iff_ker_eq_bot _).2 (Ideal.eq_bot_of_comap_eq_bot hk)

/- English proof (translation)
Establish `up : ∀ x : K', i'.IsIntegralElem x → (k.comp i).IsIntegralElem x`. Introduce `x hx`. Use `letI := g.toAlgebra`. Use `letI := i'.toAlgebra`. Use `letI := (k.comp i).toAlgebra`.

Use `haveI : Algebra.IsIntegral V W := ⟨hg⟩`. Use `haveI : IsScalarTower V W K' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun h a).symm`. Conclude with `isIntegral_trans (R := V) (A := W) x hx`. Establish `down : ∀ y : K, (k.comp i).IsIntegralElem (k y) → i.IsIntegralElem y`. Introduce and unpack `y ⟨p, hm, he⟩`.

Use `⟨p, hm, k.injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, Polynomial.hom_eval₂]`. Conclude with `he`. Use `⟨fun a => down _ (up _ (hp.1 a)), ?_⟩` and prove the remaining obligations. Take `⟨a, ha, hinv⟩` from `hp.2`.

Use `⟨a, fun e => ha (by simp [e]), down _ ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv₀]`. Conclude with `up _ hinv`.
-/
theorem prim_descend {V W K K' : Type} [CommRing V] [CommRing W] [Field K] [Field K'] (g : V →+* W)
    (hg : g.IsIntegral) (i : V →+* K) (k : K →+* K') (i' : W →+* K') (h : i'.comp g = k.comp i) {J : Type}
    (c : J → K) (hp : Prim i' (fun a => k (c a))) : Prim i c := by
  have up : ∀ x : K', i'.IsIntegralElem x → (k.comp i).IsIntegralElem x := by
    intro x hx
    letI := g.toAlgebra
    letI := i'.toAlgebra
    letI := (k.comp i).toAlgebra
    haveI : Algebra.IsIntegral V W := ⟨hg⟩
    haveI : IsScalarTower V W K' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun h a).symm
    exact isIntegral_trans (R := V) (A := W) x hx
  have down : ∀ y : K, (k.comp i).IsIntegralElem (k y) → i.IsIntegralElem y := by
    rintro y ⟨p, hm, he⟩
    refine ⟨p, hm, k.injective ?_⟩
    rw [map_zero, Polynomial.hom_eval₂]
    exact he
  refine ⟨fun a => down _ (up _ (hp.1 a)), ?_⟩
  obtain ⟨a, ha, hinv⟩ := hp.2
  refine ⟨a, fun e => ha (by simp [e]), down _ ?_⟩
  rw [map_inv₀]
  exact up _ hinv

/- English proof (translation)
Take `⟨P, α, -, hc, hL⟩` from `h`. Establish `g₁` using `isGrpPullback_pullback t.G x`. Establish `w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x`. Rewrite using `[Category.comp_id]`. Conclude with `pullback.condition`.

Take `⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ P.A.left, ψ ≫ α = pullback.fst t.G.hom x ∧ ψ ≫ P.A.hom = pullback.snd t.G.hom x ≫ 𝟙 _` from `⟨_, hc.1.lift_fst _ _ w, hc.1.lift_snd _ _ w⟩`. Establish `g₂ : IsGrpPullback ((Over.pullback x).obj t.G) P.A (𝟙 _) ψ` using `hc.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂`. Establish `hM` using `pull_isLB t.PP.isLB (pullback.fst t.G.hom x)`. Establish `e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (P.L.pull ψ)` using `(GlobalTheory.LN.GenericPoint.lbIso_pull hL ψ h₁.symm).symm`. Establish `hq` using `amplePt (Sp K) K (𝟙 _) P.A ((Over.pullback x).obj t.G) ψ g₂ P.L (t.PP.L.pull (pullback.fst t.G.hom x)) P.isLB hM e P.ample P.ktriv`.

Conclude with `⟨MorphismProperty.of_isPullback (P := @IsProper) g₂.1 P.isAb.proper, hq.1, hq.2⟩`.
-/
theorem polAt_of_polFib {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (g : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hc, hL⟩ := h
  have g₁ := isGrpPullback_pullback t.G x
  have w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x := by
    rw [Category.comp_id]; exact pullback.condition
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ P.A.left,
      ψ ≫ α = pullback.fst t.G.hom x ∧ ψ ≫ P.A.hom = pullback.snd t.G.hom x ≫ 𝟙 _ :=
    ⟨_, hc.1.lift_fst _ _ w, hc.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) P.A (𝟙 _) ψ :=
    hc.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (P.L.pull ψ) :=
    (GlobalTheory.LN.GenericPoint.lbIso_pull hL ψ h₁.symm).symm
  have hq := amplePt (Sp K) K (𝟙 _) P.A ((Over.pullback x).obj t.G) ψ g₂ P.L
    (t.PP.L.pull (pullback.fst t.G.hom x)) P.isLB hM e P.ample P.ktriv
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g₂.1 P.isAb.proper, hq.1, hq.2⟩

/- English proof (translation)
Substitute `e` using the available equality. Take `rfl : h₁ = h₂` from `Over.OverMorphism.ext hl`. Conclude with `⟨pt, hT⟩`.
-/
theorem thList_move {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ)
    {K : Type} [Field K] {T : Over S} (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂)
    (h₁ : Over.mk x₁ ⟶ T) (h₂ : Over.mk x₂ ⟶ T) (hl : h₁.left = h₂.left) {N : ℕ} (pt : Fin N → (Over.mk x₁ ⟶ G))
    (c : Fin N → K) (hT : ThList G L ρ m x₁ (VVRank.pullS G _ h₁ s) pt c) :
    ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ (VVRank.pullS G _ h₂ s) pt' c := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext hl
  exact ⟨pt, hT⟩

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_eq' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Introduce `E _ _ _ H S t g V _ _ _ hV χ hpf σ hσ m N hm hm3 hmu K _ i pt c hi hT`. Take `⟨hd, hc, h0⟩` from `(GlobalTheory.LN.cDvr_iff V).1 hV`. Use `haveI := hd`. Use `haveI := h0`. Choose the witnesses or unpack the hypotheses as in `⟨t₁, ⟨m₁⟩⟩ : ∃ t₁ : SAB H (Sp V), Nonempty (SABMap t₁ t χ) := by`.

Take `⟨PP₁, cub₁, sym₁, adj₁, prim₁, m', -⟩` from `sabPull Out.CubePf.cubePull χ t`. Conclude with `⟨_, ⟨m'⟩⟩`. Take `⟨W, _, _, _, _, gW, hcW, hgi, hginj, hgl, Ex, hEx⟩` from `GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V hc t₁.G t₁.semi`. Choose the witnesses or unpack the hypotheses as in `⟨t₂, m₂, hS⟩ : ∃ (t₂ : SAB H (Sp W)) (_ : SABMap t₂ t₁ (spMap gW)), ∃ E' : SplitExt (Sp (IsLocalRing.ResidueField W)), E'.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj t₂.G) := by`. Take `⟨PP', cub, sym, adj, prim, m', -⟩` from `sabPull Out.CubePf.cubePull (spMap gW) t₁`.

Conclude with `⟨_, m', Ex, hEx⟩`. Take `⟨n, -⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₂`. Establish `hp0 : GlobalTheory.LN.PolAt t (jK V ≫ χ)` using `polAt_of_polFib t g _ hpf`. Establish `hp1` using `GlobalTheory.DatUniq.polAt_pull m₁ hp0 (jK V) (𝟙 _) (Category.id_comp _)`. Establish `hinj : Function.Injective ((algebraMap W (FractionRing W)).comp gW)` using `(IsFractionRing.injective W (FractionRing W)).comp hginj`.

Set `gam : FractionRing V →+* FractionRing W` to `IsFractionRing.lift hinj`. Establish `hg' : ∀ r, gam (algebraMap _ _ r) = algebraMap W _ (gW r)` using `fun r => IsFractionRing.lift_algebraMap hinj r`. Use `clear_value gam`. Establish `hgam : spMap gam ≫ jK V = jK W ≫ spMap gW`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`.

Conclude with `congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hg'))`. Establish `hp2` using `GlobalTheory.DatUniq.polAt_pull m₂ hp1 (jK W) (spMap gam) hgam`. Establish `hW : GlobalTheory.LN.CDvr W` using `(GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hcW, inferInstance⟩`. Take `⟨U, -⟩` from `GlobalTheory.LN.uDvrSt_holds E H W hW t₂ hp2 hS`. Establish `hσ'` using `nz_pull S t.G t.PP.L t.PP.isLB t.semi V W χ σ gW hσ`.

Establish `hmuW : IsUnit (m : W)` using `by simpa using hmu.map gW`. Set `k : K →+* AlgebraicClosure K` to `algebraMap K (AlgebraicClosure K)`. Take `⟨i', hi'c, hi'⟩` from `exists_embed_integral gW hgi hginj (k.comp i) (k.injective.comp hi)`. Take `⟨pt₁, -, hT₁⟩` from `GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N K (AlgebraicClosure K) k (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c hT`. Set `a₁ : Over.mk (spMap k ≫ spMap i ≫ χ) ⟶ Over.mk (spMap i ≫ χ)` to `Over.homMk (spMap k) rfl`.

Set `a₂ : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ` to `Over.homMk (spMap i) rfl`. Set `b₁ : Over.mk (spMap i' ≫ spMap gW ≫ χ) ⟶ Over.mk (spMap gW ≫ χ)` to `Over.homMk (spMap i') rfl`. Set `b₂ : Over.mk (spMap gW ≫ χ) ⟶ Over.mk χ` to `Over.homMk (spMap gW) rfl`. Establish `e₁ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ i) k = VVRank.pullS t.G _ (a₁ ≫ a₂) σ` using `GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _`. Establish `e₂ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ gW) i' = VVRank.pullS t.G _ (b₁ ≫ b₂) σ` using `GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _`.

Establish `hx : spMap i' ≫ spMap gW = spMap k ≫ spMap i`. Rewrite using `[spMap_comp_eq', spMap_comp_eq', hi'c]`. Rewrite `hT₁` using `[e₁]`. Take `⟨pt₂, hT₂⟩` from `thList_move t.G t.PP.L t.PP.rig m σ (by rw [← Category.assoc, ← hx, Category.assoc]) (a₁ ≫ a₂) (b₁ ≫ b₂) (by simp [a₁, a₂, b₁, b₂, hx]) pt₁ _ hT₁`. Rewrite `hT₂` using `[← e₂]`.

Conclude with `prim_descend gW hgi i k i' hi'c c (GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H S t W hW (spMap gW ≫ χ) t₂ ⟨n⟩ ⟨U⟩ _ hσ' m N hm hm3 hmuW _ i' pt₂ _ hi' hT₂)`.
-/
theorem prim_of_polFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S), PolFib t.G t.PP.L g (jK V ≫ χ) → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  intro E _ _ _ H S t g V _ _ _ hV χ hpf σ hσ m N hm hm3 hmu K _ i pt c hi hT
  obtain ⟨hd, hc, h0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  haveI := hd
  haveI := h0
  obtain ⟨t₁, ⟨m₁⟩⟩ : ∃ t₁ : SAB H (Sp V), Nonempty (SABMap t₁ t χ) := by
    obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, m', -⟩ := sabPull Out.CubePf.cubePull χ t
    exact ⟨_, ⟨m'⟩⟩
  obtain ⟨W, _, _, _, _, gW, hcW, hgi, hginj, hgl, Ex, hEx⟩ :=
    GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V hc t₁.G t₁.semi
  obtain ⟨t₂, m₂, hS⟩ : ∃ (t₂ : SAB H (Sp W)) (_ : SABMap t₂ t₁ (spMap gW)),
      ∃ E' : SplitExt (Sp (IsLocalRing.ResidueField W)),
        E'.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj t₂.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m', -⟩ := sabPull Out.CubePf.cubePull (spMap gW) t₁
    exact ⟨_, m', Ex, hEx⟩
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₂
  have hp0 : GlobalTheory.LN.PolAt t (jK V ≫ χ) := polAt_of_polFib t g _ hpf
  have hp1 := GlobalTheory.DatUniq.polAt_pull m₁ hp0 (jK V) (𝟙 _) (Category.id_comp _)
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp gW) :=
    (IsFractionRing.injective W (FractionRing W)).comp hginj
  let gam : FractionRing V →+* FractionRing W := IsFractionRing.lift hinj
  have hg' : ∀ r, gam (algebraMap _ _ r) = algebraMap W _ (gW r) := fun r => IsFractionRing.lift_algebraMap hinj r
  clear_value gam
  have hgam : spMap gam ≫ jK V = jK W ≫ spMap gW := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hg'))
  have hp2 := GlobalTheory.DatUniq.polAt_pull m₂ hp1 (jK W) (spMap gam) hgam
  have hW : GlobalTheory.LN.CDvr W := (GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hcW, inferInstance⟩
  obtain ⟨U, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW t₂ hp2 hS
  have hσ' := nz_pull S t.G t.PP.L t.PP.isLB t.semi V W χ σ gW hσ
  have hmuW : IsUnit (m : W) := by simpa using hmu.map gW
  let k : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨i', hi'c, hi'⟩ := exists_embed_integral gW hgi hginj (k.comp i) (k.injective.comp hi)
  obtain ⟨pt₁, -, hT₁⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N K (AlgebraicClosure K) k
    (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c hT
  let a₁ : Over.mk (spMap k ≫ spMap i ≫ χ) ⟶ Over.mk (spMap i ≫ χ) := Over.homMk (spMap k) rfl
  let a₂ : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap i) rfl
  let b₁ : Over.mk (spMap i' ≫ spMap gW ≫ χ) ⟶ Over.mk (spMap gW ≫ χ) := Over.homMk (spMap i') rfl
  let b₂ : Over.mk (spMap gW ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap gW) rfl
  have e₁ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ i) k = VVRank.pullS t.G _ (a₁ ≫ a₂) σ :=
    GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _
  have e₂ : SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ gW) i' = VVRank.pullS t.G _ (b₁ ≫ b₂) σ :=
    GlobalTheory.ThetaRuleCompare.pullS_comp _ _ _
  have hx : spMap i' ≫ spMap gW = spMap k ≫ spMap i := by
    rw [spMap_comp_eq', spMap_comp_eq', hi'c]
  rw [e₁] at hT₁
  obtain ⟨pt₂, hT₂⟩ := thList_move t.G t.PP.L t.PP.rig m σ (by rw [← Category.assoc, ← hx, Category.assoc])
    (a₁ ≫ a₂) (b₁ ≫ b₂) (by simp [a₁, a₂, b₁, b₂, hx]) pt₁ _ hT₁
  rw [← e₂] at hT₂
  exact prim_descend gW hgi i k i' hi'c c
    (GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H S t W hW (spMap gW ≫ χ) t₂ ⟨n⟩ ⟨U⟩ _ hσ' m N hm hm3 hmuW _ i' pt₂ _ hi' hT₂)

end GlobalTheory.UMin
