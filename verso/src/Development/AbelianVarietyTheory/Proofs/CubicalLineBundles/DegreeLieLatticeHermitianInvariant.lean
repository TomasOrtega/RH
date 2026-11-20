import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelationStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FibIndep

section Lattice

variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

open scoped ComplexOrder in
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] in

/- English proof (translation)
Take `⟨s⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `c hc`. Assume the negation of the conclusion as `hne`. Establish `hli : LinearIndependent K ![c]` using `(linearIndependent_unique_iff (v := ![c])).2 (by simpa using hne)`.

Establish `hpos` using `(h.posDef s 1 ![c] hli).diag_pos (i := 0)`. Establish `hzero : h'.form s 0 0 = 0` using `by simpa using h'.smul_right s 0 0 0`. Establish `hcc : h.form s c c = 0` using `by rw [← hM, hc, hzero]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val_fin_one] at hpos`. Rewrite `hpos` using `[hcc]`.

Conclude with `lt_irrefl _ hpos`.
-/
theorem injective_of_isometry (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s c c', h'.form s (M c) (M c') = h.form s c c') : Function.Injective M := by
  obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  by_contra hne
  have hli : LinearIndependent K ![c] := (linearIndependent_unique_iff (v := ![c])).2 (by simpa using hne)
  have hpos := (h.posDef s 1 ![c] hli).diag_pos (i := 0)
  have hzero : h'.form s 0 0 = 0 := by simpa using h'.smul_right s 0 0 0
  have hcc : h.form s c c = 0 := by rw [← hM, hc, hzero]
  simp only [Matrix.of_apply, Matrix.cons_val_fin_one] at hpos
  rw [hcc] at hpos
  exact lt_irrefl _ hpos

/- English proof (translation)
Apply the tactic sequence `have hinj := injective_of_isometry h h' M hM`. Take `⟨v, hv⟩` from `exists_isFrame E hE`. Take `⟨hvE, hvli, hvsp⟩` from `hv`. Establish `hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v)`. Use `⟨fun i => Submodule.mem_map_of_mem (hvE i), hvli.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx'` using `hvsp hx`. Rewrite using `[Set.range_comp, Submodule.span_image]`. Conclude with `Submodule.mem_map_of_mem hx'`. Rewrite using `[arakelovDegree_eq_degreeOfFamily h hE ⟨hvE, hvli, hvsp⟩, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']`.

Establish `hgram : ∀ σ, h'.gram σ (M ∘ v) = h.gram σ v` using `fun σ => by`. Use extensionality with `i j`. Simplify using `[HermFam.gram, hM]`. Establish `hspan : Submodule.span (𝓞 K) (Set.range (M ∘ v)) = (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K))`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression. Establish `hidx : (Submodule.span (𝓞 K) (Set.range (M ∘ v))).toAddSubgroup.relIndex (E.map (M.restrictScalars (𝓞 K))).toAddSubgroup = (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup`. Rewrite using `[hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]`. Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ hinj`. Unfold `degreeOfFamily`.

Rewrite using `[hidx]`. Simplify using `only [hgram]`.
-/
theorem deg_map_of_isometry (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s c c', h'.form s (M c) (M c') = h.form s c c') {E : Submodule (𝓞 K) V} (hE : E.FG) :
    deg h E = deg h' (E.map (M.restrictScalars (𝓞 K))) := by
  have hinj := injective_of_isometry h h' M hM
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  obtain ⟨hvE, hvli, hvsp⟩ := hv
  have hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v) := by
    refine ⟨fun i => Submodule.mem_map_of_mem (hvE i), hvli.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hvsp hx
    rw [Set.range_comp, Submodule.span_image]
    exact Submodule.mem_map_of_mem hx'
  rw [arakelovDegree_eq_degreeOfFamily h hE ⟨hvE, hvli, hvsp⟩, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']
  have hgram : ∀ σ, h'.gram σ (M ∘ v) = h.gram σ v := fun σ => by
    ext i j
    simp [HermFam.gram, hM]
  have hspan : Submodule.span (𝓞 K) (Set.range (M ∘ v)) =
      (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range (M ∘ v))).toAddSubgroup.relIndex
      (E.map (M.restrictScalars (𝓞 K))).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup := by
    rw [hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  unfold degreeOfFamily
  rw [hidx]
  simp only [hgram]

end Lattice

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))}

/- English proof (translation)
Establish `hb` using `F.basis`. Unfold `IsLieBasis at hb`. Establish `hf` using `F.fib`. Unfold `IsPolFibre at hf`. Take `⟨-, hpb, -⟩` from `hf`.

Take `⟨w, hw, hwu⟩` from `existsUnique_isVecOver hpb.1 u`. Take `⟨c, hc, hcu⟩` from `hb.2 w (hw.isTangent hpb hu)`. Use `⟨c, ⟨hu, w, hw, hc⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `c' ⟨-, w', hw', hc'⟩`. Take `rfl` from `hwu w' hw'`.

Conclude with `hcu c' hc'`.
-/
theorem existsUnique_coord (F : GenFib P) {u : epsR (𝓞 K) ⟶ P.A} (hu : IsTangent u) : ∃! c, F.IsCoord u c := by
  have hb := F.basis
  unfold IsLieBasis at hb
  have hf := F.fib
  unfold IsPolFibre at hf
  obtain ⟨-, hpb, -⟩ := hf
  obtain ⟨w, hw, hwu⟩ := existsUnique_isVecOver hpb.1 u
  obtain ⟨c, hc, hcu⟩ := hb.2 w (hw.isTangent hpb hu)
  refine ⟨c, ⟨hu, w, hw, hc⟩, ?_⟩
  rintro c' ⟨-, w', hw', hc'⟩
  obtain rfl := hwu w' hw'
  exact hcu c' hc'

/- English proof (translation)
Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `c`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hp⟩`.

Take `⟨ht, -⟩` from `id hu`. Take `⟨c₀, hc₀, -⟩` from `existsUnique_coord F ht`. Use `⟨c₀, ⟨u, hc₀, hp⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `hM u c₀ hc₀`. Rewrite `h1` using `[Category.comp_id]`.

Conclude with `(existsUnique_coord F' ht).unique h1 hu`. Introduce and unpack `⟨c₀, ⟨u, hu, hp⟩, rfl⟩`. Establish `h1` using `hM u c₀ hu`. Rewrite `h1` using `[Category.comp_id]`. Conclude with `⟨u, h1, hp⟩`.
-/
theorem image_coord (F F' : GenFib P) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)} (hM : F.IsDiffOf F' (𝟙 P.A) M)
    (p : (epsR (𝓞 K) ⟶ P.A) → Prop) :
    Submodule.span (𝓞 K) {c | ∃ u, F'.IsCoord u c ∧ p u} =
      (Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c ∧ p u}).map (M.restrictScalars (𝓞 K)) := by
  rw [Submodule.map_span]
  congr 1
  ext c
  constructor
  · rintro ⟨u, hu, hp⟩
    obtain ⟨ht, -⟩ := id hu
    obtain ⟨c₀, hc₀, -⟩ := existsUnique_coord F ht
    refine ⟨c₀, ⟨u, hc₀, hp⟩, ?_⟩
    have h1 := hM u c₀ hc₀
    rw [Category.comp_id] at h1
    exact (existsUnique_coord F' ht).unique h1 hu
  · rintro ⟨c₀, ⟨u, hu, hp⟩, rfl⟩
    have h1 := hM u c₀ hu
    rw [Category.comp_id] at h1
    exact ⟨u, h1, hp⟩

/- English proof (translation)
Introduce `hU hL K _ _ P F F' h h' hh hh'`. Take `⟨⟨M, hM, -⟩, -⟩` from `GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F' (𝟙 P.A) inferInstance`. Establish `hN : F.IsDiffOf F (𝟙 P.A) LinearMap.id` using `fun u c hc => by`. Rewrite using `[Category.comp_id]`. Conclude with `hc`.

Establish `hlam : LamEq P.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A)` using `GlobalTheory.PolBaseChange.lbIso_refl (GlobalTheory.LamCalc.cubeLB_isLB P.isLB _)`. Establish `hiso : ∀ s c c', h'.form s (M c) (M c') = h.form s c c'` using `fun s c c' => by`. Simplify using `using GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hU hL K P F P F' h h' (𝟙 P.A) (𝟙 P.A) M LinearMap.id hh hh' inferInstance inferInstance hlam hM hN s c c'`. Establish `hFG` using `(GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1`. Use `⟨?_, fun O _ act τ => ?_⟩` and prove the remaining obligations.

Establish `e` using `image_coord F F' hM (fun _ => True)`. Simplify using `only [and_true] at e`. Establish `e' : F'.lieLat = F.lieLat.map (M.restrictScalars (𝓞 K))` using `e`. Rewrite using `[e']`. Apply the tactic sequence `exact deg_map_of_isometry h h' M hiso hFG`.

Establish `e` using `image_coord F F' hM (fun u => ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a))`. Establish `hle : F.eigLat act τ ≤ F.lieLat` using `Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩`. Establish `hFG' : (F.eigLat act τ).FG` using `hFG.of_le hle`. Establish `e' : F'.eigLat act τ = (F.eigLat act τ).map (M.restrictScalars (𝓞 K))` using `e`. Rewrite using `[e']`.

Apply the tactic sequence `exact deg_map_of_isometry h h' M hiso hFG'`.
-/
theorem deg_lieLat_eq : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → deg h F.lieLat = deg h' F'.lieLat ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K), deg h (F.eigLat act τ) = deg h' (F'.eigLat act τ) := by
  intro hU hL K _ _ P F F' h h' hh hh'
  obtain ⟨⟨M, hM, -⟩, -⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F' (𝟙 P.A) inferInstance
  have hN : F.IsDiffOf F (𝟙 P.A) LinearMap.id := fun u c hc => by
    rw [Category.comp_id]
    exact hc
  have hlam : LamEq P.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) :=
    GlobalTheory.PolBaseChange.lbIso_refl (GlobalTheory.LamCalc.cubeLB_isLB P.isLB _)
  have hiso : ∀ s c c', h'.form s (M c) (M c') = h.form s c c' := fun s c c' => by
    simpa using GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hU hL K P F P F' h h' (𝟙 P.A) (𝟙 P.A) M LinearMap.id hh hh'
      inferInstance inferInstance hlam hM hN s c c'
  have hFG := (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1
  refine ⟨?_, fun O _ act τ => ?_⟩
  · have e := image_coord F F' hM (fun _ => True)
    simp only [and_true] at e
    have e' : F'.lieLat = F.lieLat.map (M.restrictScalars (𝓞 K)) := e
    rw [e']
    exact deg_map_of_isometry h h' M hiso hFG
  · have e := image_coord F F' hM (fun u => ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a))
    have hle : F.eigLat act τ ≤ F.lieLat :=
      Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩
    have hFG' : (F.eigLat act τ).FG := hFG.of_le hle
    have e' : F'.eigLat act τ = (F.eigLat act τ).map (M.restrictScalars (𝓞 K)) := e
    rw [e']
    exact deg_map_of_isometry h h' M hiso hFG'

end GlobalTheory.FibIndep
end
