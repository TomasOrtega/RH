import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.WeilBound.CoreStatements.HodgeTatePoints.LieMultComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Qac

section Pull

open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.KeyUnitModels GlobalTheory.KeyCancel IsLocalRing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Take `⟨φ'', he'', w'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩` from `hx`. Take `⟨w, hw, hr, -⟩` from `m.lin`. Establish `g` using `(isGen_iff w).1 hw`. Establish `g''` using `(isGen_iff w'').1 hw''`. Take `⟨θ', hs⟩` from `sec_pull_down g t.PP.isLB t'.PP.isLB θ`.

Take `⟨v', hv', hvv⟩` from `GlobalTheory.exists_isLieBasis_baseChange _ _ f t.G t'.G m.φ m.cart t.semi.smooth n v hv`. Establish `he : eSec t'.G ≫ m.φ = spMap f ≫ eSec t.G` using `m.cm.e_comm.trans (congrArg (· ≫ eSec t.G) m.base)`. Establish `hrig : m.cm.rigPull t.PP.L t.PP.rig = rigPullOf m.φ (spMap f) he t.PP.L t.PP.rig`. Establish `key : ∀ (a b : Sp R' ⟶ Sp R) (_ : a = b) ha hb, rigPullOf (G'` using `t'.G) m.φ a ha t.PP.L t.PP.rig = rigPullOf m.φ b hb t.PP.L t.PP.rig := by`. Introduce and unpack `a b rfl _ _`.

Both sides reduce to the same expression. Conclude with `key _ _ m.base _ _`. Rewrite `hr` using `[hrig]`. Use `⟨θ', v', ?_, hv', ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hz'⟩` from `hθ (spMap f (closedPoint R'))`.

Take `⟨y, rfl, hy⟩` from `Scheme.exists_preimage_of_isPullback m.cart.1 z (closedPoint R') hz`. Take `⟨k, hb⟩` from `TopologicalSpace.Opens.mem_iSup.1 hz'`. Establish `hk : m.φ y ∈ t.PP.L.U k` using `t.G.left.basicOpen_le _ hb`. Take `⟨l, hl⟩` from `exists_chart t'.PP.isLB y`. Establish `u : IsUnit (gs (𝟙 _) (m.φ y) _ (θ.f k))`.

Rewrite using `[gs_eq (𝟙 _) (m.φ y) _ hk]`. Conclude with `(t.G.left.mem_basicOpen _ _ hk).1 hb`. Establish `u₁ : IsUnit (gs m.φ y _ (θ.f k))` using `by rw [gs_stalkMap m.φ y _ hk]; exact u.map _`. Establish `e` using `hs _ (𝟙 _) y k l hk hl`. Rewrite `e` using `[Category.id_comp]`.

Establish `u₂` using `isUnit_of_mul_isUnit_right (e ▸ u₁)`. Rewrite `u₂` using `[gs_eq (𝟙 _) y _ hl]`. Conclude with `⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (t'.G.left.mem_basicOpen _ _ hl).2 u₂⟩⟩`. Establish `hsp : spMap (f'.comp f) = spMap f' ≫ spMap f` using `spMap_comp _ _`. Establish `hc` using `m.cart`.

Establish `hp` using `hc.1`. Take `⟨φ', hφ, hw0⟩ : ∃ φ' : x.P.A.left ⟶ t'.G.left, φ' ≫ m.φ = φ'' ∧ φ' ≫ t'.G.hom = x.P.A.hom ≫ spMap f'` from `⟨hp.lift φ'' (x.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩`. Substitute `hφ` using the available equality. Establish `he' : eSec x.P.A ≫ φ' = spMap f' ≫ eSec t'.G`. Apply `hp.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]`. Establish `a₁ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _` using `Over.w η[x.P.A]`. Establish `a₂ : eSec t'.G ≫ t'.G.hom = 𝟙 _` using `Over.w η[t'.G]`. Rewrite using `[Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]`. Simplify using the standard rewrite rules.

Take `⟨w', T⟩` from `exists_cancel t.PP.isLB w w'' g g'' t'.PP.isLB x.P.isLB`. Establish `r` using `(maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig (spMap f) _ (rigPull_le m.φ (spMap f) he t.PP.L) (fun _ => rfl)).1 hr`. Establish `r''` using `(maps_iff w'' _ (fun _ => eSec t.G) _ x.rig t.PP.rig (spMap (f'.comp f)) _ (rigPull_le (φ' ≫ m.φ) (spMap (f'.comp f)) he'' t.PP.L) (fun _ => rfl)).1 hr''`. Rewrite `r''` using `[hsp]`. Establish `hFF : (Chart.dualMapR f').comp (Chart.dualMapR f) = F''` using `dualNumber_ringHom_ext (fun a => by`.

Rewrite using `[RingHom.comp_apply, hF'']`. Apply the tactic sequence `ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])`. Use the proof step `(by`. Rewrite using `[RingHom.comp_apply, hFe'']`. Apply the tactic sequence `ext <;> simp [Chart.dualMapR])`.

Use `⟨φ', he', w', hg'', Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0, (isGen_iff w').2 (T.pgen_cancel t.PP.isLB g g''), (maps_iff w' _ (fun _ => eSec t'.G) _ x.rig t'.PP.rig (spMap f') _ (rigPull_le φ' (spMap f') he' t'.PP.L) (fun _ => rfl)).2 (T.pmaps_cancel t.PP.isLB (fun …` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart t.PP.isLB (m.φ (φ' (q z)))`. Establish `a` using `hs Z (q ≫ φ') z j i hj hi`. Establish `b` using `(appLE_eq_iff_stalk w'' θ x.th).1 hs'' Z q z j k hj hk`. Rewrite `b` using `[T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc]`.

Conclude with `(Units.mul_right_inj _).1 b`. Apply the tactic sequence `ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`. Apply the tactic sequence `ext <;> simp [Chart.dualMapR]`. Apply `hp.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hv'', Category.assoc, hvv, ← hFF, ← Category.assoc, spMap_comp]`.

Rewrite using `[Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w] show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply the tactic sequence `ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem exists_isFibreOf_pull_local {R R' R'' : Type} [CommRing R] [CommRing R'] [IsLocalRing R'] [CommRing R'']
    {f : R →+* R'} {f' : R' →+* R''} {t : SAB H (Sp R)} {t' : SAB H (Sp R')} (m : SABMap t' t (spMap f))
    {θ : t.PP.L.Sec} {n : ℕ} {v : Fin n → (epsR R ⟶ t.G)}
    (hθ : ∀ b : Sp R, ∃ y : t.G.left, t.G.hom y = b ∧ y ∈ Out.nonzeroLocus θ) (hv : IsLieBasis v)
    {x : KeyIn R''} (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ v (f'.comp f)) :
    ∃ (θ' : t'.PP.L.Sec) (v' : Fin n → (epsR R' ⟶ t'.G)), NonzeroClosed (X := t'.G) θ' ∧ IsLieBasis v' ∧
      IsFibreOf x t'.G t'.PP.L t'.PP.rig θ' v' f' := by
  obtain ⟨φ'', he'', w'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := hx
  obtain ⟨w, hw, hr, -⟩ := m.lin
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨θ', hs⟩ := sec_pull_down g t.PP.isLB t'.PP.isLB θ
  obtain ⟨v', hv', hvv⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ f t.G t'.G m.φ m.cart t.semi.smooth n v hv
  have he : eSec t'.G ≫ m.φ = spMap f ≫ eSec t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec t.G) m.base)
  have hrig : m.cm.rigPull t.PP.L t.PP.rig = rigPullOf m.φ (spMap f) he t.PP.L t.PP.rig := by
    have key : ∀ (a b : Sp R' ⟶ Sp R) (_ : a = b) ha hb,
        rigPullOf (G' := t'.G) m.φ a ha t.PP.L t.PP.rig = rigPullOf m.φ b hb t.PP.L t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  rw [hrig] at hr
  refine ⟨θ', v', ?_, hv', ?_⟩
  · obtain ⟨z, hz, hz'⟩ := hθ (spMap f (closedPoint R'))
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 z (closedPoint R') hz
    obtain ⟨k, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
    have hk : m.φ y ∈ t.PP.L.U k := t.G.left.basicOpen_le _ hb
    obtain ⟨l, hl⟩ := exists_chart t'.PP.isLB y
    have u : IsUnit (gs (𝟙 _) (m.φ y) _ (θ.f k)) := by
      rw [gs_eq (𝟙 _) (m.φ y) _ hk]; exact (t.G.left.mem_basicOpen _ _ hk).1 hb
    have u₁ : IsUnit (gs m.φ y _ (θ.f k)) := by rw [gs_stalkMap m.φ y _ hk]; exact u.map _
    have e := hs _ (𝟙 _) y k l hk hl
    rw [Category.id_comp] at e
    have u₂ := isUnit_of_mul_isUnit_right (e ▸ u₁)
    rw [gs_eq (𝟙 _) y _ hl] at u₂
    exact ⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (t'.G.left.mem_basicOpen _ _ hl).2 u₂⟩⟩
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp _ _
  have hc := m.cart
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x.P.A.left ⟶ t'.G.left, φ' ≫ m.φ = φ'' ∧ φ' ≫ t'.G.hom = x.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x.P.A ≫ φ' = spMap f' ≫ eSec t'.G := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := Over.w η[x.P.A]
      have a₂ : eSec t'.G ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  obtain ⟨w', T⟩ := exists_cancel t.PP.isLB w w'' g g'' t'.PP.isLB x.P.isLB
  have r := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig (spMap f) _ (rigPull_le m.φ (spMap f) he t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec t.G) _ x.rig t.PP.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ m.φ) (spMap (f'.comp f)) he'' t.PP.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp (Chart.dualMapR f) = F'' := dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', he', w', hg'', Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec t'.G) _ x.rig t'.PP.rig (spMap f') _ (rigPull_le φ' (spMap f') he' t'.PP.L)
      (fun _ => rfl)).2 (T.pmaps_cancel t.PP.isLB (fun _ => he') r r''),
    (appLE_eq_iff_stalk w' θ' x.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (φ' (q z)))
    have a := hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w'' θ x.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hvv, ← hFF, ← Category.assoc, spMap_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Take `⟨t', ⟨m⟩⟩` from `Kftwo.exists_pull (spMap f) t`. Take `⟨θ', w', h₁, h₂, h₃⟩` from `exists_isFibreOf_pull_local m hθ hw hx`. Conclude with `Kftwo.key_isUnit hκ hpow t' θ' w' x h₃ h₂ h₁`.
-/
theorem key_mem_of_dvr {κ : KeyRule} (hκ : IsKeyRule κ) (hpow : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K) (j : ℕ),
      GlobalTheory.KeyPow.IsKeyPow y x j → κ K y = κ K x ^ j)
    {A V K : Type} [CommRing A] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] (f : A →+* V) (t : SAB H (Sp A)) (θ : t.PP.L.Sec) {n : ℕ} (w : Fin n → (epsR A ⟶ t.G))
    (x : KeyIn K) (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ w ((algebraMap V K).comp f)) (hw : IsLieBasis w)
    (hθ : ∀ b : Sp A, ∃ y : t.G.left, t.G.hom y = b ∧ y ∈ Out.nonzeroLocus θ) :
    ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := by
  obtain ⟨t', ⟨m⟩⟩ := Kftwo.exists_pull (spMap f) t
  obtain ⟨θ', w', h₁, h₂, h₃⟩ := exists_isFibreOf_pull_local m hθ hw hx
  exact Kftwo.key_isUnit hκ hpow t' θ' w' x h₃ h₂ h₁

end Pull

/- English proof (translation)
Establish `hb : a ∈ (⊥ : Subalgebra (𝓞 L) L)`. Rewrite using `[← IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot (𝓞 L) L, Algebra.mem_iInf]`. Conclude with `h`. Take `⟨b, rfl⟩` from `Algebra.mem_bot.1 hb`. Conclude with `b.isIntegral_coe`.
-/
theorem isIntegral_of_forall_mem {L : Type} [Field L] [NumberField L] (a : L)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      a ∈ Localization.subalgebra.ofField L _ v.asIdeal.primeCompl_le_nonZeroDivisors) : IsIntegral ℤ a := by
  have hb : a ∈ (⊥ : Subalgebra (𝓞 L) L) := by
    rw [← IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot (𝓞 L) L, Algebra.mem_iInf]
    exact h
  obtain ⟨b, rfl⟩ := Algebra.mem_bot.1 hb
  exact b.isIntegral_coe

section Main

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights TensorProduct GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

/- English proof (translation)
Introduce `κ k₁ k₂ k₃ k₄ k₅ E _ _ _ H L _ _ t th x v ⟨φ, he, w, h1, h2, h3, h4, h5⟩ hv hθ`. Establish `hκ : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ`. Use `⟨?_, k₂, k₃, k₄, ?_⟩` and prove the remaining obligations. Simplify `k₁` using `only [GlobalTheory.KeyCl.Homog, _root_.mul_one]`. Simplify `k₅` using `only [GlobalTheory.KeyCl.ArchNorm, _root_.mul_one]`.

Apply the tactic sequence `have hx : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsFibreOf x t.G t.PP.L t.PP.rig th v (algebraMap (𝓞 L) L) := ⟨φ, he, w, rfl, dualMap (algebraMap (𝓞 L) L), h1, h2, h3, h4, fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl], by ext <;> simp [d …`. Use `isIntegral_of_forall_mem _ fun p => ?_` and prove the remaining obligations. Take `⟨V, hV⟩ : ∃ V : Subalgebra (𝓞 L) L, V = Localization.subalgebra.ofField L _ p.asIdeal.primeCompl_le_nonZeroDivisors` from `⟨_, rfl⟩`. Establish `hl : IsLocalization.AtPrime V p.asIdeal`. Rewrite using `[hV]`.

Conclude with `Localization.subalgebra.isLocalization_ofField L _ _`. Establish `hd : IsDiscreteValuationRing V` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) p.ne_bot V`. Rewrite `hx` using `[IsScalarTower.algebraMap_eq (𝓞 L) V L]`. Take `⟨u, hu⟩` from `key_mem_of_dvr hκ (GlobalTheory.KeyCl.rule_pow κ k₁ k₂ k₄) (algebraMap (𝓞 L) V) t th v x hx hv hθ`. Rewrite using `[← hV, hu]`.

Conclude with `(u : V).2`.
-/
theorem key_isIntegral : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ → GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (th : t.PP.L.Sec) (x : KeyIn L) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ t.G)), KeyOver (algebraMap (𝓞 L) L) t th x v → IsLieBasis v → KeyDeg.NonVan t.G.hom th → IsIntegral ℤ (κ L x : L) := by
  intro κ k₁ k₂ k₃ k₄ k₅ E _ _ _ H L _ _ t th x v ⟨φ, he, w, h1, h2, h3, h4, h5⟩ hv hθ
  have hκ : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, _root_.mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, _root_.mul_one] using k₅
  have hx : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsFibreOf x t.G t.PP.L t.PP.rig th v (algebraMap (𝓞 L) L) :=
    ⟨φ, he, w, rfl, dualMap (algebraMap (𝓞 L) L), h1, h2, h3, h4,
      fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl], by ext <;> simp [dualMap], h5⟩
  refine isIntegral_of_forall_mem _ fun p => ?_
  obtain ⟨V, hV⟩ : ∃ V : Subalgebra (𝓞 L) L,
      V = Localization.subalgebra.ofField L _ p.asIdeal.primeCompl_le_nonZeroDivisors := ⟨_, rfl⟩
  have hl : IsLocalization.AtPrime V p.asIdeal := by
    rw [hV]; exact Localization.subalgebra.isLocalization_ofField L _ _
  have hd : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) p.ne_bot V
  rw [IsScalarTower.algebraMap_eq (𝓞 L) V L] at hx
  obtain ⟨u, hu⟩ := key_mem_of_dvr hκ (GlobalTheory.KeyCl.rule_pow κ k₁ k₂ k₄) (algebraMap (𝓞 L) V) t th v x hx hv hθ
  rw [← hV, hu]
  exact (u : V).2

/- English proof (translation)
Introduce `_` and use `key_isIntegral`.
-/
theorem keydeg_integral : KeyBadSt → ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ → GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (th : t.PP.L.Sec) (x : KeyIn L) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ t.G)), KeyOver (algebraMap (𝓞 L) L) t th x v → IsLieBasis v → KeyDeg.NonVan t.G.hom th → IsIntegral ℤ (κ L x : L) :=
  fun _ => key_isIntegral

end Main

end PositivityTheory.HtPt.Qac
