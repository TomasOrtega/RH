import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfIsogeny
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGrpObjOfFlatClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

namespace TorsionKernelModel

/- English proof (translation)
Establish `hk : IsPullback (pullback.fst f η[H]) (toUnit _) f η[H]`. Use `IsPullback.of_hasPullback f η[H]` as an intermediate fact. Rewrite `this` using `[toUnit_unique (pullback.snd f η[H]) (toUnit _)]`. Then use the resulting hypothesis. Generalize the expression as in `pullback.fst f η[H] = i at hk`. Generalize the expression as in `pullback f η[H] = Z at i hk`.

Establish `h₁ : IsClosedImmersion (η[H].left ≫ H.hom)`. Rewrite using `[Over.w]`. Conclude with `inferInstanceAs (IsClosedImmersion (𝟙 S))`. Establish `h₂ : IsClosedImmersion η[H].left` using `IsClosedImmersion.of_comp _ H.hom`. Establish `h₃ : IsClosedImmersion i.left` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂`.

Establish `hm : Mono i` using `(Over.forget S).mono_of_mono_map (inferInstanceAs (Mono i.left))`. Establish `hi : i ≫ f = 1` using `hk.w`. Take `⟨_, hG⟩` from `exists_grpObj_of_mono i (hk.lift η[G] (toUnit _) (by simp)) (hk.lift ((fst Z Z ≫ i) * (snd Z Z ≫ i)) (toUnit _) (by`. Rewrite using `[MonObj.mul_comp, Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one, _root_.mul_one, Hom.one_def]))`. Use the proof step `(hk.lift i⁻¹ (toUnit _) (by rw [GrpObj.inv_comp, hi, inv_one, Hom.one_def]))`.

Use the proof step `(hk.lift_fst _ _ _) ((hk.lift_fst _ _ _).trans (by rw [Hom.mul_def, lift_fst_comp_snd_comp]))`. Use the proof step `((hk.lift_fst _ _ _).trans (Hom.inv_def _))`. Conclude with `⟨Z, _, i, hG, h₃, hk⟩`.
-/
theorem exists_kernel {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] [IsSeparated H.hom] (f : G ⟶ H)
    [IsMonHom f] :
    ∃ (Z : Over S) (_ : GrpObj Z) (i : Z ⟶ G), IsMonHom i ∧ IsClosedImmersion i.left ∧
      IsPullback i (toUnit Z) f η[H] := by
  have hk : IsPullback (pullback.fst f η[H]) (toUnit _) f η[H] := by
    have := IsPullback.of_hasPullback f η[H]
    rwa [toUnit_unique (pullback.snd f η[H]) (toUnit _)] at this
  generalize pullback.fst f η[H] = i at hk
  generalize pullback f η[H] = Z at i hk
  have h₁ : IsClosedImmersion (η[H].left ≫ H.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[H].left := IsClosedImmersion.of_comp _ H.hom
  have h₃ : IsClosedImmersion i.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂
  have hm : Mono i := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have hi : i ≫ f = 1 := hk.w
  obtain ⟨_, hG⟩ := exists_grpObj_of_mono i
    (hk.lift η[G] (toUnit _) (by simp))
    (hk.lift ((fst Z Z ≫ i) * (snd Z Z ≫ i)) (toUnit _) (by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one, _root_.mul_one,
        Hom.one_def]))
    (hk.lift i⁻¹ (toUnit _) (by rw [GrpObj.inv_comp, hi, inv_one, Hom.one_def]))
    (hk.lift_fst _ _ _) ((hk.lift_fst _ _ _).trans (by rw [Hom.mul_def, lift_fst_comp_snd_comp]))
    ((hk.lift_fst _ _ _).trans (Hom.inv_def _))
  exact ⟨Z, _, i, hG, h₃, hk⟩

/- English proof (translation)
Use `(h.map (Over.pullback j)).of_iso (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback j)).symm (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) ?_` and prove the remaining obligations. Simplify using `[Functor.obj.η_def]`.
-/
theorem isPullback_kernel_baseChange {S S' : Scheme.{0}} (j : S' ⟶ S) {Z G H : Over S} [GrpObj H]
    {i : Z ⟶ G} {f : G ⟶ H} (h : IsPullback i (toUnit Z) f η[H]) :
    IsPullback ((Over.pullback j).map i) (toUnit _) ((Over.pullback j).map f) η[(Over.pullback j).obj H] := by
  refine (h.map (Over.pullback j)).of_iso (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback j)).symm
    (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) ?_
  simp [Functor.obj.η_def]

/- English proof (translation)
Establish `h₁ : IsClosedImmersion (η[G].left ≫ G.hom)`. Rewrite using `[Over.w]`. Conclude with `inferInstanceAs (IsClosedImmersion (𝟙 S))`. Establish `h₂ : IsClosedImmersion η[G].left` using `IsClosedImmersion.of_comp _ G.hom`. Establish `e₁ : i ≫ (𝟙 G ^ n) = toUnit Z ≫ η[G]`.

Rewrite using `[MonObj.comp_pow, Category.comp_id, h, Hom.one_def]`. Establish `e₂ : i.left ≫ (𝟙 G ^ n).left = Z.hom ≫ η[G].left`. Rewrite using `[← Over.comp_left, e₁]`. Simplify using the standard rewrite rules. Set `l : Z.left ⟶ pullback (𝟙 G ^ n).left η[G].left` to `pullback.lift i.left Z.hom e₂`.

Establish `h₃ : IsClosedImmersion (l ≫ pullback.fst _ _)`. Rewrite using `[pullback.lift_fst]`. Use `infer_instance`. Establish `h₄ : IsClosedImmersion l` using `IsClosedImmersion.of_comp l (pullback.fst _ _)`. Establish `e₃ : l ≫ pullback.snd _ _ = Z.hom` using `pullback.lift_snd _ _ _`.

Rewrite using `[← e₃]`. Use `infer_instance`.
-/
theorem isFinite_of_pow_eq_one {S : Scheme.{0}} {Z G : Over S} [GrpObj G] [IsSeparated G.hom] (i : Z ⟶ G)
    [IsClosedImmersion i.left] (n : ℕ) [hn : IsFinite (𝟙 G ^ n).left] (h : i ^ n = 1) : IsFinite Z.hom := by
  have h₁ : IsClosedImmersion (η[G].left ≫ G.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  have e₁ : i ≫ (𝟙 G ^ n) = toUnit Z ≫ η[G] := by
    rw [MonObj.comp_pow, Category.comp_id, h, Hom.one_def]
  have e₂ : i.left ≫ (𝟙 G ^ n).left = Z.hom ≫ η[G].left := by
    rw [← Over.comp_left, e₁]; simp
  let l : Z.left ⟶ pullback (𝟙 G ^ n).left η[G].left := pullback.lift i.left Z.hom e₂
  have h₃ : IsClosedImmersion (l ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]; infer_instance
  have h₄ : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.fst _ _)
  have e₃ : l ≫ pullback.snd _ _ = Z.hom := pullback.lift_snd _ _ _
  rw [← e₃]
  infer_instance

end TorsionKernelModel

open TorsionKernelModel in

/- English proof (translation)
Introduce `hL R K _ _ _ _ _ P A₀ B₀ _ _ φ ψ n hφ hB _ _ _ _ hn hker`. Take `⟨_, _⟩` from `ExtUnique.spec_fractionRing R K`. Use `P.isAb.proper` as an intermediate fact. Use `hB.proper` as an intermediate fact. Take `⟨a, ha, ha'⟩` from `grpPullback_iso (isGrpPullback_pullback P.A _) hφ`.

Establish `: IsIso a.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map a.hom))`. Take `⟨Z, _, i, _, hi, hZ⟩` from `exists_kernel (a.hom ≫ ψ)`. Take `⟨Ga, io, e, _, _, he⟩` from `IsogenyModel.exists_flat_closure R K P.A Z i hi`. Take `⟨_, _, -⟩` from `exists_grpObj_of_flat_closed _ P.A Ga io Z i e he`. Establish `hkill : (Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom ≫ ψ = toUnit _ ≫ η[B₀]`.

Rewrite using `[← he, Category.assoc, hZ.w, comp_toUnit_assoc]`. Establish `hpow : io ^ n = 1`. Apply `ExtUnique.pullback_map_injective (spMap (algebraMap R K))` to reduce the goal to its premises. Establish `h₁` using `hker _ ((Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom) (by`. Rewrite using `[Category.assoc, hkill, Hom.one_def])`.

Rewrite `h₁` using `[← MonObj.pow_comp, ← MonObj.one_comp a.hom, cancel_mono]`. Conclude with `(map_pow (Over.pullback (spMap (algebraMap R K))).homMonoidHom io n).trans (h₁.trans (map_one (Over.pullback (spMap (algebraMap R K))).homMonoidHom).symm)`. Use `(hL.mulN _ P n hn).1` as an intermediate fact. Establish `hfin : IsFinite Ga.hom` using `isFinite_of_pow_eq_one io n hpow`. Establish `hm : Mono io` using `(Over.forget _).mono_of_mono_map (inferInstanceAs (Mono io.left))`.

Take `⟨B, _, hab, q, _, hq₁, hq₂, hq₃, hq⟩` from `hL.quotient R P Ga io ‹_› hm hfin ‹_›`. Establish `hq'` using `isPullback_kernel_baseChange (spMap (algebraMap R K)) hq`. Establish `hqc : QuasiCompact q.left` using `inferInstance`. Take `⟨β, _, hβ⟩` from `flatQuotient_iso_of_same_kernel _ _ _ _ _ _ ((Over.pullback (spMap (algebraMap R K))).map q) ((Over.pullback (spMap (algebraMap R K))).map io) (a.hom ≫ ψ) i inferInstance inferInstance (MorphismProperty.overPullbackMap (P := @Flat) _ q hq₂) (MorphismProperty.overPullbackMap (P := …`. Use `⟨B, _, β.hom.left ≫ pullback.fst B.hom (spMap (algebraMap R K)), q, hab, ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback B _)).congr (Category.id_comp _) rfl, ‹_›, hq₁, hq₂, hq₃, ?_⟩` and prove the remaining obligations.

Rewrite using `[← cancel_epi a.hom.left, ← Category.assoc a.hom.left φ, ha', ← ExtUnique.pullback_map_left_fst, ← hβ]`. Simplify using `only [Over.comp_left, Category.assoc]`.
-/
theorem exists_abelianScheme_model_of_isogeny_dedekind :
    Out.Laws → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (A₀ B₀ : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] (φ : A₀.left ⟶ P.A.left) (ψ : A₀ ⟶ B₀) (n : ℕ), IsGrpPullback A₀ P.A (spMap (algebraMap R K)) φ → IsAbelianScheme B₀ → IsMonHom ψ → IsFinite ψ.left → Flat ψ.left → Surjective ψ.left → 1 ≤ n → (∀ (T : Over (Sp K)) (x : T ⟶ A₀), x ≫ ψ = 1 → x ^ n = 1) →
  ∃ (B : Over (Sp R)) (_ : GrpObj B) (φB : B₀.left ⟶ B.left) (Ψ : P.A ⟶ B), IsAbelianScheme B ∧ IsGrpPullback B₀ B (spMap (algebraMap R K)) φB ∧ IsMonHom Ψ ∧ IsFinite Ψ.left ∧ Flat Ψ.left ∧ Surjective Ψ.left ∧ ψ.left ≫ φB = φ ≫ Ψ.left := by
  intro hL R K _ _ _ _ _ P A₀ B₀ _ _ φ ψ n hφ hB _ _ _ _ hn hker
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := P.isAb.proper
  have := hB.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback P.A _) hφ
  have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
  obtain ⟨Z, _, i, _, hi, hZ⟩ := exists_kernel (a.hom ≫ ψ)
  obtain ⟨Ga, io, e, _, _, he⟩ := IsogenyModel.exists_flat_closure R K P.A Z i hi
  obtain ⟨_, _, -⟩ := exists_grpObj_of_flat_closed _ P.A Ga io Z i e he
  have hkill : (Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom ≫ ψ = toUnit _ ≫ η[B₀] := by
    rw [← he, Category.assoc, hZ.w, comp_toUnit_assoc]
  have hpow : io ^ n = 1 := by
    apply ExtUnique.pullback_map_injective (spMap (algebraMap R K))
    have h₁ := hker _ ((Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom) (by
      rw [Category.assoc, hkill, Hom.one_def])
    rw [← MonObj.pow_comp, ← MonObj.one_comp a.hom, cancel_mono] at h₁
    exact (map_pow (Over.pullback (spMap (algebraMap R K))).homMonoidHom io n).trans
      (h₁.trans (map_one (Over.pullback (spMap (algebraMap R K))).homMonoidHom).symm)
  have := (hL.mulN _ P n hn).1
  have hfin : IsFinite Ga.hom := isFinite_of_pow_eq_one io n hpow
  have hm : Mono io := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono io.left))
  obtain ⟨B, _, hab, q, _, hq₁, hq₂, hq₃, hq⟩ := hL.quotient R P Ga io ‹_› hm hfin ‹_›
  have hq' := isPullback_kernel_baseChange (spMap (algebraMap R K)) hq
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨β, _, hβ⟩ := flatQuotient_iso_of_same_kernel _ _ _ _ _ _
    ((Over.pullback (spMap (algebraMap R K))).map q) ((Over.pullback (spMap (algebraMap R K))).map io) (a.hom ≫ ψ) i
    inferInstance inferInstance
    (MorphismProperty.overPullbackMap (P := @Flat) _ q hq₂)
    (MorphismProperty.overPullbackMap (P := @Surjective) _ q hq₃)
    (MorphismProperty.overPullbackMap (P := @QuasiCompact) _ q hqc) hq' inferInstance inferInstance
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hZ
    (by rw [← e.inv_hom_id_assoc i, he, Category.assoc, hq'.w, comp_toUnit_assoc]) hkill
  refine ⟨B, _, β.hom.left ≫ pullback.fst B.hom (spMap (algebraMap R K)), q, hab,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback B _)).congr (Category.id_comp _) rfl,
    ‹_›, hq₁, hq₂, hq₃, ?_⟩
  rw [← cancel_epi a.hom.left, ← Category.assoc a.hom.left φ, ha', ← ExtUnique.pullback_map_left_fst, ← hβ]
  simp only [Over.comp_left, Category.assoc]

end GlobalTheory
