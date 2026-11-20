import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RepJetAugCompTrunc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniversalThickeningStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

/- English proof (translation)
Establish `hs : Function.Surjective (toJetHom R κ m)` using `fun q => by`. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Conclude with `⟨P, toJet_coe m P⟩`. Take `⟨h, hh, e⟩` from `(Ideal.mem_map_iff_of_surjective _ hs).1 hg`. Establish `h2 : g - h ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1)`.

Rewrite using `[← germIdeal_eq_span, mem_germIdeal_pow_iff]`. Introduce `d hd`. Rewrite using `[map_sub, (toJet_eq_iff m h g).1 e d hd, sub_self]`. Establish `: g = h + (g - h)` using `by ring`. Rewrite using `[this]`.

Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left hh) (Ideal.mem_sup_right h2)`.
-/
theorem mem_sup_pow_of_toJet_mem_map {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ)
    (I : Ideal (MvPowerSeries κ R)) (g : MvPowerSeries κ R) (hg : toJet m g ∈ I.map (toJetHom R κ m)) :
    g ∈ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1) := by
  have hs : Function.Surjective (toJetHom R κ m) := fun q => by
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨P, toJet_coe m P⟩
  obtain ⟨h, hh, e⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 hg
  have h2 : g - h ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1) := by
    rw [← germIdeal_eq_span, mem_germIdeal_pow_iff]
    intro d hd
    rw [map_sub, (toJet_eq_iff m h g).1 e d hd, sub_self]
  have : g = h + (g - h) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left hh) (Ideal.mem_sup_right h2)

/- English proof (translation)
Establish `h1 : LocallyOfFiniteType (f.left ≫ G.hom)` using `by rw [Over.w f]; infer_instance`. Establish `h2 : LocallyOfFiniteType f.left` using `locallyOfFiniteType_of_comp f.left G.hom`. Establish `h3` using `(IsPullback.of_hasPullback f η[G]).map (Over.forget S)`. Establish `h4 : LocallyOfFiniteType (pullback.snd f η[G]).left` using `MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h3 h2`. Establish `h5 : (pullback f η[G]).hom = (pullback.snd f η[G]).left`.

Rewrite using `[← Over.w (pullback.snd f η[G])]`. Conclude with `Category.comp_id _`. Rewrite using `[h5]`. Conclude with `h4`.
-/
theorem locallyOfFiniteType_pullback_unit {S : Scheme.{0}} (G : Over S) [GrpObj G] [LocallyOfFiniteType G.hom]
    (f : G ⟶ G) : LocallyOfFiniteType (pullback f η[G]).hom := by
  have h1 : LocallyOfFiniteType (f.left ≫ G.hom) := by rw [Over.w f]; infer_instance
  have h2 : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left G.hom
  have h3 := (IsPullback.of_hasPullback f η[G]).map (Over.forget S)
  have h4 : LocallyOfFiniteType (pullback.snd f η[G]).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h3 h2
  have h5 : (pullback f η[G]).hom = (pullback.snd f η[G]).left := by
    rw [← Over.w (pullback.snd f η[G])]
    exact Category.comp_id _
  rw [h5]
  exact h4

/- English proof (translation)
Introduce `k _ G _ _ f hf hfin d x hx φ hφ`. Use `haveI := locallyOfFiniteType_pullback_unit G f`. Establish `hext : ∀ {T : Over (Spec (CommRingCat.of k))} (u v : T ⟶ pullback f η[G]), u ≫ pullback.fst f η[G] = v ≫ pullback.fst f η[G] → u = v` using `fun u v h => pullback.hom_ext h (toUnit_unique _ _)`. Establish `hfinK : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite (Over.mk t ⟶ pullback f η[G])`. Introduce `Ω _ _ t`.

Use `haveI := hfin Ω t`. Use `Finite.of_injective (β := {x : Over.mk t ⟶ G // x ≫ f = 1}) (fun u => ⟨u ≫ pullback.fst f η[G], ?_⟩) (fun u v h => hext u v (congrArg Subtype.val h))` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]`. Use `congr 1`. Conclude with `toUnit_unique _ _`.

Establish `h1f : (1 : Chart.sp (R₀` using `k) k ⟶ G) ≫ f = toUnit _ ≫ η[G] := by`. Rewrite using `[Hom.one_def, Category.assoc, hf]`. Take `⟨A, _, _, aug, M, io, hM, hio, hU⟩` from `GlobalTheory.T.exists_universal_thickening_of_finite_points k (pullback f η[G]) hfinK (pullback.lift 1 (toUnit _) h1f)`. Use `⟨M + 1, ?_⟩` and prove the remaining obligations. Take `⟨hex, -, hfp, -, -⟩` from `repSt_of_jetAlgSt jetAlg k G d x hx (Fin 1 × Fin d)`.

Take `⟨y, hy, -⟩` from `hex (pt k (n := 1) d 0) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0)`. Establish `hy'` using `hφ.2 1 _ y hy`. Rewrite `hy'` using `[ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_comp1_pt_right]`. Take `⟨ψ₀, hψ₀, hy₀⟩` from `hy.2 (M + 1)`. Take `⟨ψ₁, hψ₁, hy₁⟩` from `hy'.2 (M + 1)`.

Establish `hya` using `(hfp _ y hy).2 (M + 1)`. Establish `hxa` using `(isFPt_of_isUnivChart hx).2 (M + 1)`. Use `set I : Ideal (Chart.JetR k (Fin 1 × Fin d) (M + 1)) := (Ideal.span (Set.range φ)).map (toJetHom k (Fin 1 × Fin d) (M + 1)) with hI`. Establish `hIle : I ≤ RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1))`. Rewrite using `[hI, Ideal.map_le_iff_le_comap, Ideal.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `(jetAug_toJet (M + 1) (φ j)).trans (hφ.1 j)`. Set `π` to `Ideal.Quotient.mkₐ k I`. Set `augQ : (Chart.JetR k (Fin 1 × Fin d) (M + 1) ⧸ I) →ₐ[k] k` to `Ideal.Quotient.liftₐ I (Chart.jetAug k (Fin 1 × Fin d) (M + 1)) (fun a ha => hIle ha)`. Establish `haπ : augQ.comp π = Chart.jetAug k (Fin 1 × Fin d) (M + 1)` using `AlgHom.ext fun _ => rfl`.

Establish `hkQ : RingHom.ker augQ ^ (M + 1 + 1) = ⊥`. Establish `hle : RingHom.ker augQ ≤ (RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1))).map π`. Introduce `q hq`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Conclude with `Ideal.mem_map_of_mem π hq`.

Rewrite using `[← le_bot_iff]`. Use `(Ideal.pow_right_mono hle _).trans ?_` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow, Chart.ker_jetAug_pow, Ideal.map_bot]`. Establish `hz : (Chart.spMap π ≫ y (M + 1)) ≫ f = toUnit _ ≫ η[G]`. Establish `e : π.comp ψ₁ = (Algebra.ofId k _).comp (Chart.jetAug k (Fin d) (M + 1))`.

Use `Chart.jet_ext fun j => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero, hψ₁]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem (toJetHom k (Fin 1 × Fin d) (M + 1)) (Ideal.subset_span ⟨j, rfl⟩))`. Establish `hy₁' : y (M + 1) ≫ f = Chart.spMap ψ₁ ≫ x (M + 1)` using `hy₁`. Rewrite using `[Category.assoc, hy₁', ← Category.assoc, Chart.spMap_comp, e, ← Chart.spMap_comp, Category.assoc, hxa, ← Hom.one_def]`.

Conclude with `MonObj.comp_one _`. Establish `hzone : Chart.spMap augQ ≫ Chart.spMap π ≫ y (M + 1) = 1`. Rewrite using `[← Category.assoc, Chart.spMap_comp, haπ, hya]`. Take `⟨a, ha, hza⟩` from `hU _ augQ (M + 1) hkQ (pullback.lift _ (toUnit _) hz) (hext _ _ (by`. Rewrite using `[Category.assoc, pullback.lift_fst, pullback.lift_fst, hzone]))`.

Establish `hM' : RingHom.ker aug ^ (M + 1 + 1) = ⊥`. Rewrite using `[pow_succ (RingHom.ker aug) (M + 1), hM, Ideal.bot_mul]`. Take `⟨ψ, ⟨hψa, hψ⟩, -⟩` from `hx.2.2 A aug (M + 1) hM' (io ≫ pullback.fst f η[G]) (by`. Rewrite using `[← Category.assoc, hio, pullback.lift_fst])`. Establish `hz0 : ∀ j, ψ₀ (Chart.zR (M + 1) j) = Chart.zR (M + 1) (0, j)` using `fun j => (hψ₀ j).trans (toJet_X (M + 1) _)`.

Establish `heq : a.comp ψ = π.comp ψ₀`. Use `(hx.2.2 _ augQ (M + 1) hkQ (Chart.spMap π ≫ y (M + 1)) hzone).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, ha, hψa]`. Rewrite using `[← Chart.spMap_comp, Category.assoc, ← hψ, ← Category.assoc, ← hza, pullback.lift_fst]`. Rewrite using `[← AlgHom.comp_assoc, haπ]`.

Use `Chart.jet_ext fun j => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, hz0, Chart.jetAug_zR, Chart.jetAug_zR]`. Rewrite using `[hy₀, ← Category.assoc, Chart.spMap_comp]`. Set `Θ` to `π.comp (toJetHom k (Fin 1 × Fin d) (M + 1))`. Establish `hΘ : Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ≤ ((RingHom.ker aug).map a).comap Θ`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨⟨i, j⟩, rfl⟩`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Establish `e1 : Θ (MvPowerSeries.X (0, j)) = a (ψ (Chart.zR (M + 1) j))`. Use `AlgHom.congr_fun heq (Chart.zR (M + 1) j)` as an intermediate fact.

Rewrite `this` using `[AlgHom.comp_apply, AlgHom.comp_apply, hψ₀]`. Conclude with `this.symm`. Use `show Θ (MvPowerSeries.X (0, j)) ∈ (RingHom.ker aug).map a`. Rewrite using `[e1]`. Conclude with `Ideal.mem_map_of_mem a ((AlgHom.congr_fun hψa _).trans (Chart.jetAug_zR (M + 1) j))`.

Introduce `g hg`. Establish `h2` using `Ideal.le_comap_pow _ (M + 1) (Ideal.pow_right_mono hΘ (M + 1) hg)`. Rewrite `h2` using `[← Ideal.map_pow, hM, Ideal.map_bot]`. Conclude with `mem_sup_pow_of_toJet_mem_map (M + 1) _ g (Ideal.Quotient.eq_zero_iff_mem.1 h2)`.
-/
theorem exists_pow_le_span_sup_pow_succ : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] (f : G ⟶ G), η[G] ≫ f = η[G] → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite {x : Over.mk t ⟶ G // x ≫ f = 1}) → ∀ (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ φ : Pt k 1 d, GlobalTheory.JetSer.IsMapOf x x f φ → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ M ≤ Ideal.span (Set.range φ) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ (M + 1) := by
  intro k _ G _ _ f hf hfin d x hx φ hφ
  haveI := locallyOfFiniteType_pullback_unit G f
  have hext : ∀ {T : Over (Spec (CommRingCat.of k))} (u v : T ⟶ pullback f η[G]),
      u ≫ pullback.fst f η[G] = v ≫ pullback.fst f η[G] → u = v := fun u v h =>
    pullback.hom_ext h (toUnit_unique _ _)
  have hfinK : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)),
      Finite (Over.mk t ⟶ pullback f η[G]) := by
    intro Ω _ _ t
    haveI := hfin Ω t
    refine Finite.of_injective (β := {x : Over.mk t ⟶ G // x ≫ f = 1})
      (fun u => ⟨u ≫ pullback.fst f η[G], ?_⟩) (fun u v h => hext u v (congrArg Subtype.val h))
    rw [Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h1f : (1 : Chart.sp (R₀ := k) k ⟶ G) ≫ f = toUnit _ ≫ η[G] := by
    rw [Hom.one_def, Category.assoc, hf]
  obtain ⟨A, _, _, aug, M, io, hM, hio, hU⟩ :=
    GlobalTheory.T.exists_universal_thickening_of_finite_points k (pullback f η[G]) hfinK (pullback.lift 1 (toUnit _) h1f)
  refine ⟨M + 1, ?_⟩
  obtain ⟨hex, -, hfp, -, -⟩ := repSt_of_jetAlgSt jetAlg k G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := hex (pt k (n := 1) d 0) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0)
  have hy' := hφ.2 1 _ y hy
  rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_comp1_pt_right] at hy'
  obtain ⟨ψ₀, hψ₀, hy₀⟩ := hy.2 (M + 1)
  obtain ⟨ψ₁, hψ₁, hy₁⟩ := hy'.2 (M + 1)
  have hya := (hfp _ y hy).2 (M + 1)
  have hxa := (isFPt_of_isUnivChart hx).2 (M + 1)
  set I : Ideal (Chart.JetR k (Fin 1 × Fin d) (M + 1)) :=
    (Ideal.span (Set.range φ)).map (toJetHom k (Fin 1 × Fin d) (M + 1)) with hI
  have hIle : I ≤ RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1)) := by
    rw [hI, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact (jetAug_toJet (M + 1) (φ j)).trans (hφ.1 j)
  let π := Ideal.Quotient.mkₐ k I
  let augQ : (Chart.JetR k (Fin 1 × Fin d) (M + 1) ⧸ I) →ₐ[k] k :=
    Ideal.Quotient.liftₐ I (Chart.jetAug k (Fin 1 × Fin d) (M + 1)) (fun a ha => hIle ha)
  have haπ : augQ.comp π = Chart.jetAug k (Fin 1 × Fin d) (M + 1) := AlgHom.ext fun _ => rfl
  have hkQ : RingHom.ker augQ ^ (M + 1 + 1) = ⊥ := by
    have hle : RingHom.ker augQ ≤ (RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1))).map π := by
      intro q hq
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact Ideal.mem_map_of_mem π hq
    rw [← le_bot_iff]
    refine (Ideal.pow_right_mono hle _).trans ?_
    rw [← Ideal.map_pow, Chart.ker_jetAug_pow, Ideal.map_bot]
  have hz : (Chart.spMap π ≫ y (M + 1)) ≫ f = toUnit _ ≫ η[G] := by
    have e : π.comp ψ₁ = (Algebra.ofId k _).comp (Chart.jetAug k (Fin d) (M + 1)) := by
      refine Chart.jet_ext fun j => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero, hψ₁]
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_map_of_mem (toJetHom k (Fin 1 × Fin d) (M + 1)) (Ideal.subset_span ⟨j, rfl⟩))
    have hy₁' : y (M + 1) ≫ f = Chart.spMap ψ₁ ≫ x (M + 1) := hy₁
    rw [Category.assoc, hy₁', ← Category.assoc, Chart.spMap_comp, e, ← Chart.spMap_comp, Category.assoc, hxa,
      ← Hom.one_def]
    exact MonObj.comp_one _
  have hzone : Chart.spMap augQ ≫ Chart.spMap π ≫ y (M + 1) = 1 := by
    rw [← Category.assoc, Chart.spMap_comp, haπ, hya]
  obtain ⟨a, ha, hza⟩ := hU _ augQ (M + 1) hkQ (pullback.lift _ (toUnit _) hz) (hext _ _ (by
    rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hzone]))
  have hM' : RingHom.ker aug ^ (M + 1 + 1) = ⊥ := by
    rw [pow_succ (RingHom.ker aug) (M + 1), hM, Ideal.bot_mul]
  obtain ⟨ψ, ⟨hψa, hψ⟩, -⟩ := hx.2.2 A aug (M + 1) hM' (io ≫ pullback.fst f η[G]) (by
    rw [← Category.assoc, hio, pullback.lift_fst])
  have hz0 : ∀ j, ψ₀ (Chart.zR (M + 1) j) = Chart.zR (M + 1) (0, j) := fun j =>
    (hψ₀ j).trans (toJet_X (M + 1) _)
  have heq : a.comp ψ = π.comp ψ₀ := by
    refine (hx.2.2 _ augQ (M + 1) hkQ (Chart.spMap π ≫ y (M + 1)) hzone).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [← AlgHom.comp_assoc, ha, hψa]
    · rw [← Chart.spMap_comp, Category.assoc, ← hψ, ← Category.assoc, ← hza, pullback.lift_fst]
    · rw [← AlgHom.comp_assoc, haπ]
      refine Chart.jet_ext fun j => ?_
      rw [AlgHom.comp_apply, hz0, Chart.jetAug_zR, Chart.jetAug_zR]
    · rw [hy₀, ← Category.assoc, Chart.spMap_comp]
  let Θ := π.comp (toJetHom k (Fin 1 × Fin d) (M + 1))
  have hΘ : Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ≤
      ((RingHom.ker aug).map a).comap Θ := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have e1 : Θ (MvPowerSeries.X (0, j)) = a (ψ (Chart.zR (M + 1) j)) := by
      have := AlgHom.congr_fun heq (Chart.zR (M + 1) j)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hψ₀] at this
      exact this.symm
    show Θ (MvPowerSeries.X (0, j)) ∈ (RingHom.ker aug).map a
    rw [e1]
    exact Ideal.mem_map_of_mem a ((AlgHom.congr_fun hψa _).trans (Chart.jetAug_zR (M + 1) j))
  intro g hg
  have h2 := Ideal.le_comap_pow _ (M + 1) (Ideal.pow_right_mono hΘ (M + 1) hg)
  rw [← Ideal.map_pow, hM, Ideal.map_bot] at h2
  exact mem_sup_pow_of_toJet_mem_map (M + 1) _ g (Ideal.Quotient.eq_zero_iff_mem.1 h2)

end GlobalTheory.JetSer
