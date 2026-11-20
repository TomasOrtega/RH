import Development.WeilBound.CoreStatements.SesquilinearFractions.SpMapMonoOfFraction
import Development.WeilBound.CoreStatements.SesquilinearFractions.GModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

/- English proof (translation)
Establish `one_left : ∀ (Y : Over S), (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left`. Introduce `Y`. Rewrite using `[Hom.one_def, Over.comp_left]`. Use `congr 1`. Establish `hmul : Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) = Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)`.

Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Apply the tactic sequence `ext <;> simp [CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.

Establish `hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hsec : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _`.

Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id]`. Unfold `IsTanAt`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[Over.comp_left, one_left]`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _`. Rewrite using `[hmul, Category.assoc, h, one_left]`. Simplify using `[epsAt]`. Introduce `h`.

Rewrite using `[one_left]`. Establish `h2` using `congrArg Over.Hom.left h`. Rewrite `h2` using `[Over.comp_left, one_left]`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _ at h2`. Rewrite `h2` using `[hmul, Category.assoc]`.

Establish `h3` using `congrArg (fun q => Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ q) h2`. Simplify using `only [epsAt, Over.mk_hom, ← Category.assoc, hsec, Category.id_comp] at h3`. Rewrite using `[h3]`. Simplify using the standard rewrite rules.
-/
private theorem isTanAt_iff_epsScale_zero_comp_eq_one {R : Type} [CommRing R] {S : Scheme} (x : Sp R ⟶ S) (G : Over S) [GrpObj G]
    (v : epsAt x ⟶ G) : IsTanAt G x v ↔ LieTangent.epsScale x 0 ≫ v = 1 := by
  have one_left : ∀ (Y : Over S), (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hmul : Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    ext <;> simp [CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    apply RingHom.ext
    intro a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hsec : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id]
  unfold IsTanAt
  constructor
  · intro h
    apply Over.OverMorphism.ext
    rw [Over.comp_left, one_left]
    change Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _
    rw [hmul, Category.assoc, h, one_left]
    simp [epsAt]
  · intro h
    rw [one_left]
    have h2 := congrArg Over.Hom.left h
    rw [Over.comp_left, one_left] at h2
    change Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _ at h2
    rw [hmul, Category.assoc] at h2
    have h3 := congrArg (fun q => Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ q) h2
    simp only [epsAt, Over.mk_hom, ← Category.assoc, hsec, Category.id_comp] at h3
    rw [h3]
    simp

open BaseChangeTangents in
/- English proof (translation)
Introduce `E _ _ _ H D l Xo c K _ V _ _ _ y T tK m m' U _ _ M ρ σ I _ n r e uV u v hρ hσ huVt huVb hcorr hv hspan`. Establish `hinj : Function.Injective (algebraMap V K)` using `IsFractionRing.injective V K`. Set `P : (epsAt (𝟙 (Sp V)) ⟶ T.G) → (epsAt (under y) ⟶ Xo.univ.t.G)` to `fun w => BaseChangeTangents.push m.cart (BaseChangeTangents.bcTan (algebraMap V K) m'.cart w)`. Establish `hP1 : P 1 = 1`. Simplify using `only [P, BaseChangeTangents.bcTan_one]`.

Conclude with `map_one (BaseChangeTangents.pushHom m.cart)`. Establish `hPscale : ∀ (a : V) w, P (LieTangent.epsScale (𝟙 (Sp V)) a ≫ w) = LieTangent.epsScale (under y) (algebraMap V K a) ≫ P w`. Introduce `a w`. Simplify using `only [P, BaseChangeTangents.bcTan_scale, BaseChangeTangents.push_scale]`. Establish `hPcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)), P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod = (List.ofFn fun i => LieTangent.epsScale (under y) (algebraMap V K (cc i)) ≫ P (w i)).prod`.

Introduce `N cc w`. Simplify using `only [P, BaseChangeTangents.bcTan_comb, BaseChangeTangents.push_comb]`. Establish `hPact : ∀ (a : 𝓞 E) w, P (w ≫ T.act.act a) = P w ≫ Xo.univ.t.act.act a`. Introduce `a w`. Simplify using `only [P]`.

Rewrite using `[BaseChangeTangents.bcTan_act _ m'.cart (tK.act.act a) (T.act.act a) (m'.act a), BaseChangeTangents.push_act m.cart (tK.act.act a) (Xo.univ.t.act.act a) (m.act a)]`. Establish `tprod : ∀ (L : List (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ w ∈ L, IsTanAt T.G (𝟙 (Sp V)) w) → IsTanAt T.G (𝟙 (Sp V)) L.prod`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`.

Introduce `_`. Simplify using `using LieTangent.isTanAt_one`. Consider the case `cons a L ih`. Introduce `h`. Rewrite using `[List.prod_cons]`.

Conclude with `LieTangent.isTanAt_mul (h a (by simp)) (ih fun w hw => h w (by simp [hw]))`. Establish `tcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ k, IsTanAt T.G (𝟙 (Sp V)) (w k)) → IsTanAt T.G (𝟙 (Sp V)) (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod`. Introduce `N cc w hw`. Apply `tprod` to reduce the goal to its premises. Introduce `z hz`.

Simplify using `only [List.mem_ofFn] at hz`. Take `⟨i, rfl⟩` from `hz`. Conclude with `LieTangent.isTanAt_scale _ (hw i)`. Establish `hPinj : ∀ w w', IsTanAt T.G (𝟙 (Sp V)) w → IsTanAt T.G (𝟙 (Sp V)) w' → P w = P w' → w = w'`. Introduce `w w' hw hw' h`.

Conclude with `BaseChangeTangents.bcTan_inj _ m'.cart hinj hw hw' (BaseChangeTangents.push_inj m.cart h)`. Establish `hM0 : M.pt 0 = 1`. Establish `h` using `M.add 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_eq_left.mp h.symm`.

Establish `hMscale : ∀ (a : K) (z : U), M.pt (a • z) = LieTangent.epsScale (under y) a ≫ M.pt z`. Introduce `a z`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[M.smul, Over.comp_left]`. Both sides reduce to the same expression.

Establish `hPu : ∀ k, P (uV k) = M.pt (u (e k))`. Introduce `k`. Take `⟨s, hs1, hs2⟩` from `hcorr k`. Establish `hs` using `BaseChangeTangents.eq_bcTan_left (algebraMap V K) m'.cart rfl (uV k) s hs2`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Simplify using `only [P]`. Rewrite using `[BaseChangeTangents.push_left, ← hs]`. Conclude with `hs1`. Establish `hPsum : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (z : Fin N → U), (∀ k, P (w k) = M.pt (z k)) → P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod = M.pt (∑ i, algebraMap V K (cc i) • z i)`. Introduce `N cc w z hwz`.

Rewrite using `[hPcomb]`. Simplify using `only [hwz]`. Conclude with `BaseChangeTangents.prod_pt M _ z`. Establish `hsmul : ∀ (a : V) (z : U), a • z = algebraMap V K a • z` using `fun a z => (algebraMap_smul K a z).symm`. Establish `hliV : LinearIndependent V u`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Set `cc : Fin n → V` to `fun k => g (e k)`. Establish `hsum : ∑ k, algebraMap V K (cc k) • u (e k) = 0`. Combine the equalities or inequalities in the displayed calculation.

Establish `hcomb1 : P (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (cc k) ≫ uV k).prod = P 1`. Rewrite using `[hPsum cc uV (fun k => u (e k)) hPu]`. Simplify using `only [hsum, hM0, hP1]`. Establish `heq1` using `hPinj _ _ (tcomb cc uV huVt) LieTangent.isTanAt_one hcomb1`. Take `⟨c0, _, huniq⟩` from `huVb 1 LieTangent.isTanAt_one`.

Establish `hc1 : IsComb cc uV 1`. Rewrite using `[BaseChangeTangents.isComb_iff]`. Conclude with `heq1.symm`. Establish `hc0 : IsComb (fun _ => (0 : V)) uV 1`. Rewrite using `[BaseChangeTangents.isComb_iff]`.

Establish `h0 : ∀ k, LieTangent.epsScale (𝟙 (Sp V)) (0 : V) ≫ uV k = 1` using `fun k => (isTanAt_iff_epsScale_zero_comp_eq_one _ _ _).mp (huVt k)`. Simplify using `only [h0, List.ofFn_const, List.prod_replicate, one_pow]`. Establish `hcc` using `(huniq cc hc1).trans (huniq _ hc0).symm`. Establish `hk` using `congrFun hcc (e.symm i)`. Simplify `hk` using `[cc]`.

Establish `hliK : LinearIndependent K u` using `LinearIndependent.localization K (nonZeroDivisors V) hliV`. Use `⟨hliK, ?_⟩` and prove the remaining obligations. Set `σV : 𝓞 E →+* V` to `(σ.comp (algebraMap (𝓞 E) E)).codRestrict V (fun a => hσ a)`. Establish `hσV : ∀ a, algebraMap V K (σV a) = σ (a : E)` using `fun a => rfl`. Establish `hvmem : ∀ a, v a ∈ Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V`.

Introduce `a`. Rewrite using `[hspan]`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Use `choose d hd using fun a => (Submodule.mem_span_range_iff_exists_fun V).mp (hvmem a).1`. Set `vV : Fin r → (epsAt (𝟙 (Sp V)) ⟶ T.G)` to `fun a => (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (d a (e k)) ≫ uV k).prod`.

Establish `hPv : ∀ a, P (vV a) = M.pt (v a)`. Introduce `a`. Rewrite using `[hPsum (fun k => d a (e k)) uV (fun k => u (e k)) hPu, ← hd a]`. Use `congr 1`. Rewrite using `[← Equiv.sum_comp e (fun i => d a i • u i)]`.

Conclude with `Finset.sum_congr rfl fun k _ => (hsmul _ _).symm`. Establish `hvVt : ∀ a, IsTanAt T.G (𝟙 (Sp V)) (vV a)` using `fun a => tcomb _ uV huVt`. Establish `heig : ∀ w (z : U), IsTanAt T.G (𝟙 (Sp V)) w → P w = M.pt z → (IsEigVec T.act (𝟙 (Sp V)) σV w ↔ z ∈ HT.eigSp ρ σ)`. Introduce `w z hw hwz`. Establish `key : ∀ a : 𝓞 E, (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔ ρ a z = σ (a : E) • z`.

Introduce `a`. Establish `e1 : (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔ w ≫ T.act.act a = LieTangent.epsScale (𝟙 (Sp V)) (σV a) ≫ w`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[h, Over.comp_left]`. Both sides reduce to the same expression. Introduce `h`. Rewrite using `[h, Over.comp_left]`. Both sides reduce to the same expression.

Rewrite using `[e1]`. Use `haveI := T.act.hom a`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `congrArg P h`.

Rewrite `h2` using `[hPact, hPscale, hwz, hσV]`. Apply `M.inj` to reduce the goal to its premises. Rewrite using `[hMscale, ← h2]`. Conclude with `hρ a z`. Introduce `h`.

Apply `hPinj _ _ (TransportLieModel.isTanAt_comp hw _) (LieTangent.isTanAt_scale _ hw)` to reduce the goal to its premises. Rewrite using `[hPact, hPscale, hwz, hσV, ← hMscale, ← h]`. Conclude with `(hρ a z).symm`. Simplify using `only [IsEigVec, hw, true_and, key]`. Simplify using `only [HT.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`.

Use `⟨σV, vV, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.ext fun a => rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Conclude with `(heig (vV a) (v a) (hvVt a) (hPv a)).mpr ((Submodule.restrictScalars_mem _ _ _).mp (hvmem a).2)`.

Introduce `w hw`. Establish `hwt : IsTanAt T.G (𝟙 (Sp V)) w` using `hw.1`. Take `⟨cc, hcc, _⟩` from `huVb w hwt`. Rewrite `hcc` using `[BaseChangeTangents.isComb_iff]`. Establish `hPw : P w = M.pt (∑ k, algebraMap V K (cc k) • u (e k))`.

Rewrite using `[hcc]`. Conclude with `hPsum cc uV (fun k => u (e k)) hPu`. Establish `hzE` using `(heig w _ hwt hPw).mp hw`. Establish `hzU : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range u)`. Apply `Submodule.sum_mem` to reduce the goal to its premises.

Introduce `k _`. Rewrite using `[← hsmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, rfl⟩)`. Establish `hzv : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range v)`. Rewrite using `[← hspan]`.

Conclude with `⟨hzU, hzE⟩`. Take `⟨g, hg⟩` from `(Submodule.mem_span_range_iff_exists_fun V).mp hzv`. Establish `hPg : P (List.ofFn fun a => LieTangent.epsScale (𝟙 (Sp V)) (g a) ≫ vV a).prod = M.pt (∑ k, algebraMap V K (cc k) • u (e k))`. Rewrite using `[hPsum g vV v hPv, ← hg]`. Conclude with `congrArg M.pt (Finset.sum_congr rfl fun a _ => (hsmul _ _).symm)`.

Use `⟨g, ?_, ?_⟩` and prove the remaining obligations. Use `show Fl.IsComb g vV w`. Rewrite using `[BaseChangeTangents.isComb_iff]`. Conclude with `hPinj _ _ hwt (tcomb g vV hvVt) (hPw.trans hPg.symm)`. Introduce `g' hg'`.

Express the relevant statement in the definitionally equal form `Fl.IsComb g' vV w at hg'`. Rewrite `hg'` using `[BaseChangeTangents.isComb_iff]`. Establish `h1 : M.pt (∑ a, algebraMap V K (g' a) • v a) = M.pt (∑ a, algebraMap V K (g a) • v a)`. Rewrite using `[← hPsum g' vV v hPv, ← hg', hPw, ← hg]`. Conclude with `congrArg M.pt (Finset.sum_congr rfl fun a _ => hsmul _ _)`.

Establish `h2` using `M.inj h1`. Use function extensionality and compare the values at `a`. Apply `hinj` to reduce the goal to its premises. Establish `h3` using `Fintype.linearIndependent_iff.mp hv (fun a => algebraMap V K (g' a) - algebraMap V K (g a)) (by simp only [sub_smul, Finset.sum_sub_distrib, h2, sub_self]) a`. Conclude with `sub_eq_zero.mp h3`.

Introduce `a`. Use `⟨(BaseChangeTangents.bcTan (algebraMap V K) m'.cart (vV a)).left, ?_, BaseChangeTangents.bcTan_left _ _ _⟩` and prove the remaining obligations. Conclude with `(BaseChangeTangents.push_left m.cart _).symm.trans (congrArg Over.Hom.left (hPv a))`.
-/
theorem lie_model_extends_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (K : Type) [Field K] (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))) (U : Type) [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I : Type) [Fintype I] (n r : ℕ) (e : Fin n ≃ I) (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (u : I → U) (v : Fin r → U), M.IsActOf Xo.univ.t.act.act ρ → (∀ a : 𝓞 E, σ (a : E) ∈ V) → (∀ k, IsTanAt T.G _ (uV k)) → (∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w) → (∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left, s ≫ m.φ = (M.pt (u (e k))).left ∧ s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) → LinearIndependent K v → Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range v) → LinearIndependent K u ∧ IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (v a)) := by
  intro E _ _ _ H D l Xo c K _ V _ _ _ y T tK m m' U _ _ M ρ σ I _ n r e uV u v hρ hσ huVt huVb hcorr hv hspan
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  let P : (epsAt (𝟙 (Sp V)) ⟶ T.G) → (epsAt (under y) ⟶ Xo.univ.t.G) :=
    fun w => BaseChangeTangents.push m.cart (BaseChangeTangents.bcTan (algebraMap V K) m'.cart w)
  have hP1 : P 1 = 1 := by
    simp only [P, BaseChangeTangents.bcTan_one]
    exact map_one (BaseChangeTangents.pushHom m.cart)
  have hPscale : ∀ (a : V) w, P (LieTangent.epsScale (𝟙 (Sp V)) a ≫ w) =
      LieTangent.epsScale (under y) (algebraMap V K a) ≫ P w := by
    intro a w
    simp only [P, BaseChangeTangents.bcTan_scale, BaseChangeTangents.push_scale]
  have hPcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)),
      P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod =
        (List.ofFn fun i => LieTangent.epsScale (under y) (algebraMap V K (cc i)) ≫ P (w i)).prod := by
    intro N cc w
    simp only [P, BaseChangeTangents.bcTan_comb, BaseChangeTangents.push_comb]
  have hPact : ∀ (a : 𝓞 E) w, P (w ≫ T.act.act a) = P w ≫ Xo.univ.t.act.act a := by
    intro a w
    simp only [P]
    rw [BaseChangeTangents.bcTan_act _ m'.cart (tK.act.act a) (T.act.act a) (m'.act a),
      BaseChangeTangents.push_act m.cart (tK.act.act a) (Xo.univ.t.act.act a) (m.act a)]
  have tprod : ∀ (L : List (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ w ∈ L, IsTanAt T.G (𝟙 (Sp V)) w) →
      IsTanAt T.G (𝟙 (Sp V)) L.prod := by
    intro L
    induction L with
    | nil =>
      intro _
      simpa using LieTangent.isTanAt_one
    | cons a L ih =>
      intro h
      rw [List.prod_cons]
      exact LieTangent.isTanAt_mul (h a (by simp)) (ih fun w hw => h w (by simp [hw]))
  have tcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)),
      (∀ k, IsTanAt T.G (𝟙 (Sp V)) (w k)) →
        IsTanAt T.G (𝟙 (Sp V)) (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod := by
    intro N cc w hw
    apply tprod
    intro z hz
    simp only [List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact LieTangent.isTanAt_scale _ (hw i)
  have hPinj : ∀ w w', IsTanAt T.G (𝟙 (Sp V)) w → IsTanAt T.G (𝟙 (Sp V)) w' → P w = P w' → w = w' := by
    intro w w' hw hw' h
    exact BaseChangeTangents.bcTan_inj _ m'.cart hinj hw hw' (BaseChangeTangents.push_inj m.cart h)
  have hM0 : M.pt 0 = 1 := by
    have h := M.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hMscale : ∀ (a : K) (z : U), M.pt (a • z) = LieTangent.epsScale (under y) a ≫ M.pt z := by
    intro a z
    apply Over.OverMorphism.ext
    rw [M.smul, Over.comp_left]
    rfl
  have hPu : ∀ k, P (uV k) = M.pt (u (e k)) := by
    intro k
    obtain ⟨s, hs1, hs2⟩ := hcorr k
    have hs := BaseChangeTangents.eq_bcTan_left (algebraMap V K) m'.cart rfl (uV k) s hs2
    apply Over.OverMorphism.ext
    simp only [P]
    rw [BaseChangeTangents.push_left, ← hs]
    exact hs1
  have hPsum : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (z : Fin N → U),
      (∀ k, P (w k) = M.pt (z k)) →
        P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod =
          M.pt (∑ i, algebraMap V K (cc i) • z i) := by
    intro N cc w z hwz
    rw [hPcomb]
    simp only [hwz]
    exact BaseChangeTangents.prod_pt M _ z
  have hsmul : ∀ (a : V) (z : U), a • z = algebraMap V K a • z := fun a z => (algebraMap_smul K a z).symm
  have hliV : LinearIndependent V u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let cc : Fin n → V := fun k => g (e k)
    have hsum : ∑ k, algebraMap V K (cc k) • u (e k) = 0 := by
      calc ∑ k, algebraMap V K (cc k) • u (e k) = ∑ k, g (e k) • u (e k) :=
            Finset.sum_congr rfl fun k _ => (hsmul _ _).symm
        _ = ∑ i, g i • u i := Equiv.sum_comp e (fun i => g i • u i)
        _ = 0 := hg
    have hcomb1 : P (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (cc k) ≫ uV k).prod = P 1 := by
      rw [hPsum cc uV (fun k => u (e k)) hPu]
      simp only [hsum, hM0, hP1]
    have heq1 := hPinj _ _ (tcomb cc uV huVt) LieTangent.isTanAt_one hcomb1
    obtain ⟨c0, _, huniq⟩ := huVb 1 LieTangent.isTanAt_one
    have hc1 : IsComb cc uV 1 := by
      rw [BaseChangeTangents.isComb_iff]
      exact heq1.symm
    have hc0 : IsComb (fun _ => (0 : V)) uV 1 := by
      rw [BaseChangeTangents.isComb_iff]
      have h0 : ∀ k, LieTangent.epsScale (𝟙 (Sp V)) (0 : V) ≫ uV k = 1 :=
        fun k => (isTanAt_iff_epsScale_zero_comp_eq_one _ _ _).mp (huVt k)
      simp only [h0, List.ofFn_const, List.prod_replicate, one_pow]
    have hcc := (huniq cc hc1).trans (huniq _ hc0).symm
    have hk := congrFun hcc (e.symm i)
    simpa [cc] using hk
  have hliK : LinearIndependent K u := LinearIndependent.localization K (nonZeroDivisors V) hliV
  refine ⟨hliK, ?_⟩
  let σV : 𝓞 E →+* V := (σ.comp (algebraMap (𝓞 E) E)).codRestrict V (fun a => hσ a)
  have hσV : ∀ a, algebraMap V K (σV a) = σ (a : E) := fun a => rfl
  have hvmem : ∀ a, v a ∈ Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V := by
    intro a
    rw [hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  choose d hd using fun a => (Submodule.mem_span_range_iff_exists_fun V).mp (hvmem a).1
  let vV : Fin r → (epsAt (𝟙 (Sp V)) ⟶ T.G) :=
    fun a => (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (d a (e k)) ≫ uV k).prod
  have hPv : ∀ a, P (vV a) = M.pt (v a) := by
    intro a
    rw [hPsum (fun k => d a (e k)) uV (fun k => u (e k)) hPu, ← hd a]
    congr 1
    rw [← Equiv.sum_comp e (fun i => d a i • u i)]
    exact Finset.sum_congr rfl fun k _ => (hsmul _ _).symm
  have hvVt : ∀ a, IsTanAt T.G (𝟙 (Sp V)) (vV a) := fun a => tcomb _ uV huVt
  have heig : ∀ w (z : U), IsTanAt T.G (𝟙 (Sp V)) w → P w = M.pt z →
      (IsEigVec T.act (𝟙 (Sp V)) σV w ↔ z ∈ HT.eigSp ρ σ) := by
    intro w z hw hwz
    have key : ∀ a : 𝓞 E, (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔
        ρ a z = σ (a : E) • z := by
      intro a
      have e1 : (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔
          w ≫ T.act.act a = LieTangent.epsScale (𝟙 (Sp V)) (σV a) ≫ w := by
        constructor
        · intro h
          apply Over.OverMorphism.ext
          rw [h, Over.comp_left]
          rfl
        · intro h
          rw [h, Over.comp_left]
          rfl
      rw [e1]
      haveI := T.act.hom a
      constructor
      · intro h
        have h2 := congrArg P h
        rw [hPact, hPscale, hwz, hσV] at h2
        apply M.inj
        rw [hMscale, ← h2]
        exact hρ a z
      · intro h
        apply hPinj _ _ (TransportLieModel.isTanAt_comp hw _) (LieTangent.isTanAt_scale _ hw)
        rw [hPact, hPscale, hwz, hσV, ← hMscale, ← h]
        exact (hρ a z).symm
    simp only [IsEigVec, hw, true_and, key]
    simp only [HT.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  refine ⟨σV, vV, ?_, ?_, ?_⟩
  · exact RingHom.ext fun a => rfl
  · refine ⟨?_, ?_⟩
    · intro a
      exact (heig (vV a) (v a) (hvVt a) (hPv a)).mpr ((Submodule.restrictScalars_mem _ _ _).mp (hvmem a).2)
    · intro w hw
      have hwt : IsTanAt T.G (𝟙 (Sp V)) w := hw.1
      obtain ⟨cc, hcc, _⟩ := huVb w hwt
      rw [BaseChangeTangents.isComb_iff] at hcc
      have hPw : P w = M.pt (∑ k, algebraMap V K (cc k) • u (e k)) := by
        rw [hcc]
        exact hPsum cc uV (fun k => u (e k)) hPu
      have hzE := (heig w _ hwt hPw).mp hw
      have hzU : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range u) := by
        apply Submodule.sum_mem
        intro k _
        rw [← hsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, rfl⟩)
      have hzv : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range v) := by
        rw [← hspan]
        exact ⟨hzU, hzE⟩
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun V).mp hzv
      have hPg : P (List.ofFn fun a => LieTangent.epsScale (𝟙 (Sp V)) (g a) ≫ vV a).prod =
          M.pt (∑ k, algebraMap V K (cc k) • u (e k)) := by
        rw [hPsum g vV v hPv, ← hg]
        exact congrArg M.pt (Finset.sum_congr rfl fun a _ => (hsmul _ _).symm)
      refine ⟨g, ?_, ?_⟩
      · show Fl.IsComb g vV w
        rw [BaseChangeTangents.isComb_iff]
        exact hPinj _ _ hwt (tcomb g vV hvVt) (hPw.trans hPg.symm)
      · intro g' hg'
        change Fl.IsComb g' vV w at hg'
        rw [BaseChangeTangents.isComb_iff] at hg'
        have h1 : M.pt (∑ a, algebraMap V K (g' a) • v a) = M.pt (∑ a, algebraMap V K (g a) • v a) := by
          rw [← hPsum g' vV v hPv, ← hg', hPw, ← hg]
          exact congrArg M.pt (Finset.sum_congr rfl fun a _ => hsmul _ _)
        have h2 := M.inj h1
        funext a
        apply hinj
        have h3 := Fintype.linearIndependent_iff.mp hv (fun a => algebraMap V K (g' a) - algebraMap V K (g a))
          (by simp only [sub_smul, Finset.sum_sub_distrib, h2, sub_self]) a
        exact sub_eq_zero.mp h3
  · intro a
    refine ⟨(BaseChangeTangents.bcTan (algebraMap V K) m'.cart (vV a)).left, ?_, BaseChangeTangents.bcTan_left _ _ _⟩
    exact (BaseChangeTangents.push_left m.cart _).symm.trans (congrArg Over.Hom.left (hPv a))

end PositivityTheory.Xgf
