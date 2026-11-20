import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.CongTop

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fmt_eq (V : HSp D) (g : GA D V) : fmt V g = (finHom V g).1 := rfl

/- English proof (translation)
Rewrite using `[fmt_eq, map_one, Units.val_one]`.
-/
theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by rw [fmt_eq, map_one, Units.val_one]

/- English proof (translation)
Rewrite using `[fmt_eq, map_mul, Units.val_mul, fmt_eq, fmt_eq]`.
-/
theorem fmt_mul (V : HSp D) (g h : GA D V) : fmt V (g * h) = fmt V g * fmt V h := by
  rw [fmt_eq, map_mul, Units.val_mul, fmt_eq, fmt_eq]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun u hu => (h _).2 ⟨u, hu, rfl⟩, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨u₀, h0, rfl⟩` from `(h u).1 hu`. Rewrite using `[Matrix.mulVec_mulVec, ← fmt_mul, inv_mul_cancel, fmt_one, Matrix.one_mulVec]` and apply the resulting hypothesis.

Introduce and unpack `⟨h1, h2⟩ u`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Use `⟨_, h2 u hu, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, ← fmt_mul, mul_inv_cancel, fmt_one, Matrix.one_mulVec]`.

Introduce and unpack `⟨u₀, h0, rfl⟩`. Conclude with `h1 _ h0`.
-/
theorem isMov_iff (V : HSp D) (L : Lt D.host.E V.rank) (k : GA D V) :
    IsMov (fmt V k) L L ↔ (∀ u ∈ hatV L, fmt V k *ᵥ u ∈ hatV L) ∧ ∀ u ∈ hatV L, fmt V k⁻¹ *ᵥ u ∈ hatV L := by
  constructor
  · intro h
    refine ⟨fun u hu => (h _).2 ⟨u, hu, rfl⟩, fun u hu => ?_⟩
    obtain ⟨u₀, h0, rfl⟩ := (h u).1 hu
    rwa [Matrix.mulVec_mulVec, ← fmt_mul, inv_mul_cancel, fmt_one, Matrix.one_mulVec]
  · rintro ⟨h1, h2⟩ u
    constructor
    · intro hu
      refine ⟨_, h2 u hu, ?_⟩
      rw [Matrix.mulVec_mulVec, ← fmt_mul, mul_inv_cancel, fmt_one, Matrix.one_mulVec]
    · rintro ⟨u₀, h0, rfl⟩
      exact h1 _ h0

noncomputable def congSub (V : HSp D) (L : Lt D.host.E V.rank) (M : ℕ) : Subgroup (GA D V) where
  carrier := {k | CongK V L M k}
  one_mem' := by
    refine ⟨(isMov_iff V L 1).2 ⟨fun u hu => ?_, fun u hu => ?_⟩, fun u _ => ⟨0, zero_mem _, ?_⟩⟩
    · rwa [fmt_one, Matrix.one_mulVec]
    · rwa [inv_one, fmt_one, Matrix.one_mulVec]
    · rw [fmt_one, Matrix.one_mulVec, sub_self, nsmul_zero]
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    rw [isMov_iff] at ha hb
    refine ⟨(isMov_iff V L _).2 ⟨fun u hu => ?_, fun u hu => ?_⟩, fun u hu => ?_⟩
    · rw [fmt_mul, ← Matrix.mulVec_mulVec]
      exact ha.1 _ (hb.1 _ hu)
    · rw [_root_.mul_inv_rev, fmt_mul, ← Matrix.mulVec_mulVec]
      exact hb.2 _ (ha.2 _ hu)
    · obtain ⟨x, hx, ex⟩ := ha' _ (hb.1 _ hu)
      obtain ⟨y, hy, ey⟩ := hb' _ hu
      refine ⟨x + y, add_mem hx hy, ?_⟩
      rw [fmt_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← ex, ← ey, sub_add_sub_cancel]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    rw [isMov_iff] at ha
    refine ⟨(isMov_iff V L _).2 ⟨ha.2, by rw [inv_inv]; exact ha.1⟩, fun u hu => ?_⟩
    obtain ⟨x, hx, ex⟩ := ha' _ (ha.2 _ hu)
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.mulVec_mulVec, ← fmt_mul, mul_inv_cancel, fmt_one, Matrix.one_mulVec] at ex
    rw [neg_nsmul, ← ex, neg_sub]

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram` as an intermediate fact. Establish `hn : {m : Matrix (Fin V.rank) (Fin V.rank) (AfE D) | ∀ z ∈ hatV L, ∃ y ∈ hatV L, m *ᵥ z - z = M • y} ∈ nhds (1 : Matrix (Fin V.rank) (Fin V.rank) (AfE D))` using `GlobalTheory.LevelOpen.congr_mem_nhds D.host.F D.host.E V.rank _ hfg hsp M hM`. Establish `hc : Continuous (fmt V)` using `GlobalTheory.Member.continuous_finHom_val D V`. Establish `h1` using `hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [fmt_one]; exact hn)`. Establish `h2` using `(hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds (by rw [Function.comp_apply, inv_one, fmt_one]; exact hn)`.

Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Use `Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_` and prove the remaining obligations. Introduce and unpack `k ⟨hk1, hk2⟩`. Use `⟨(isMov_iff V L k).2 ⟨fun y hy => ?_, fun y hy => ?_⟩, hk1⟩` and prove the remaining obligations. Take `⟨w, hw, h⟩` from `hk1 y hy`.

Rewrite using `[eq_add_of_sub_eq h]`. Conclude with `add_mem (nsmul_mem hw M) hy`. Take `⟨w, hw, h⟩` from `hk2 y hy`. Rewrite `h` using `[Function.comp_apply]`. Rewrite using `[eq_add_of_sub_eq h]`.

Conclude with `add_mem (nsmul_mem hw M) hy`.
-/
theorem isOpen_congSub (V : HSp D) (L : Lt D.host.E V.rank) (M : ℕ) (hfg : L.FG)
    (hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) (hM : 0 < M) :
    IsOpen (congSub V L M : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hn : {m : Matrix (Fin V.rank) (Fin V.rank) (AfE D) | ∀ z ∈ hatV L, ∃ y ∈ hatV L, m *ᵥ z - z = M • y} ∈
      nhds (1 : Matrix (Fin V.rank) (Fin V.rank) (AfE D)) :=
    GlobalTheory.LevelOpen.congr_mem_nhds D.host.F D.host.E V.rank _ hfg hsp M hM
  have hc : Continuous (fmt V) := GlobalTheory.Member.continuous_finHom_val D V
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [fmt_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, fmt_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro k ⟨hk1, hk2⟩
  refine ⟨(isMov_iff V L k).2 ⟨fun y hy => ?_, fun y hy => ?_⟩, hk1⟩
  · obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw M) hy
  · obtain ⟨w, hw, h⟩ := hk2 y hy
    rw [Function.comp_apply] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw M) hy

/- English proof (translation)
Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)`. Use `haveI : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space`. Establish `h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1}`.

Use extensionality with `g`. Conclude with `Units.ext_iff`. Rewrite using `[h]`. Conclude with `isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const`.
-/
theorem isClosed_GinfC (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

/- English proof (translation)
Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field D.host.F`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Ainf D.host.F)`. Use `haveI : T2Space (Ainf D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space`. Establish `h : (GfC V : Set (GA D V)) = {g | (infHom V g).1 = 1}`.

Use extensionality with `g`. Conclude with `Units.ext_iff`. Rewrite using `[h]`. Establish `hm : Continuous (fun k : GA D V => (matHom V k).1)` using `Units.continuous_val.comp continuous_subtype_val`. Conclude with `isClosed_eq (hm.matrix_map (GlobalTheory.Member.continuous_infPart D)) continuous_const`.
-/
theorem isClosed_GfC (V : HSp D) : IsClosed (GfC V : Set (GA D V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Ainf D.host.F)
  haveI : T2Space (Ainf D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GfC V : Set (GA D V)) = {g | (infHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  have hm : Continuous (fun k : GA D V => (matHom V k).1) :=
    Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq (hm.matrix_map (GlobalTheory.Member.continuous_infPart D)) continuous_const

/- English proof (translation)
Take `⟨θ₀, hθ₀⟩` from `(GlobalTheory.Member.infiniteAdele_bijective D).1`. Set `θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)` to `fun ρ => θ₀ (tauE D ρ)`. Establish `hθ : IsInfFam θ` using `fun ρ => hθ₀ _`. Establish `hsp'` using `(GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1`. Establish `hu : ∀ ρ h, (infMat D.sp.cm.sig V.gram (θ ρ) h)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) h = gramAt D V ρ` using `fun ρ h => (GlobalTheory.Member.Arch.unit_iff _ _ _).1 ((hsp' (tauE D ρ)).2.2.2.2 h)`.

Take `⟨C, hC, hCe⟩` from `GlobalTheory.StabCompact.exists_compact_entries D.host.F D.host.E L hfg hsp`. Take `⟨C', hC', hCe'⟩` from `GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C hC`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Take `⟨K, hK, hKe⟩` from `GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'`.

Use `⟨K, hK, fun k h1 h2 => hKe k fun i j => hCe' _ (hCe (fmt V k) ((isMov_iff V L k).1 h1).1 i j) fun ρ => ?_⟩` and prove the remaining obligations. Establish `hU : infMat D.sp.cm.sig V.gram (θ ρ) k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ`. Break down `h2 with h2 | h2` into its components or cases. Establish `h3 : (infHom V k).1 = 1` using `congrArg Units.val (show infHom V k = 1 from h2)`. Establish `h4 : infMat D.sp.cm.sig V.gram (θ ρ) k = ((infHom V k).1).map (θ ρ)` using `rfl`.

Rewrite using `[h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `one_mem _`. Establish `h3 : gramAt D V ρ = 1`. Unfold `gramAt`. Rewrite using `[h2, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `h4` using `hu ρ k`. Rewrite `h4` using `[h3, Matrix.mul_one]`. Conclude with `Matrix.mem_unitaryGroup_iff'.2 h4`. Conclude with `entry_norm_bound_of_unitary hU i j`.
-/
theorem exists_compact (V : HSp D) (L : Lt D.host.E V.rank) (hfg : L.FG)
    (hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k : GA D V, IsMov (fmt V k) L L → (k ∈ GfC V ∨ V.gram = 1) → k ∈ C := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun ρ => θ₀ (tauE D ρ)
  have hθ : IsInfFam θ := fun ρ => hθ₀ _
  have hsp' := (GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1
  have hu : ∀ ρ h, (infMat D.sp.cm.sig V.gram (θ ρ) h)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) h =
      gramAt D V ρ := fun ρ h => (GlobalTheory.Member.Arch.unit_iff _ _ _).1 ((hsp' (tauE D ρ)).2.2.2.2 h)
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.StabCompact.exists_compact_entries D.host.F D.host.E L hfg hsp
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C hC
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k h1 h2 => hKe k fun i j =>
    hCe' _ (hCe (fmt V k) ((isMov_iff V L k).1 h1).1 i j) fun ρ => ?_⟩
  have hU : infMat D.sp.cm.sig V.gram (θ ρ) k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
    rcases h2 with h2 | h2
    · have h3 : (infHom V k).1 = 1 := congrArg Units.val (show infHom V k = 1 from h2)
      have h4 : infMat D.sp.cm.sig V.gram (θ ρ) k = ((infHom V k).1).map (θ ρ) := rfl
      rw [h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]
      exact one_mem _
    · have h3 : gramAt D V ρ = 1 := by
        unfold gramAt
        rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]
      have h4 := hu ρ k
      rw [h3, Matrix.mul_one] at h4
      exact Matrix.mem_unitaryGroup_iff'.2 h4
  exact entry_norm_bound_of_unitary hU i j

/- English proof (translation)
Introduce `D V`. Take `⟨i1, i2, i3⟩` from `GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram`. Establish `i0` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram`. Use `⟨i0, i1, i2, i3, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram, isClosed_GinfC V, ?_⟩` and prove the remaining obligations. Introduce and unpack `L M ⟨hfg, hsp⟩ hM`.

Establish `ho` using `isOpen_congSub V L M hfg hsp hM`. Establish `hcl : IsClosed (congSub V L M : Set (GA D V))` using `Subgroup.isClosed_of_isOpen _ ho`. Take `⟨C, hC, hCm⟩` from `exists_compact V L hfg hsp`. Use `⟨congSub V L M, fun _ => Iff.rfl, ho, ?_, fun hg => ?_⟩` and prove the remaining obligations. Conclude with `hC.of_isClosed_subset (hcl.inter (isClosed_GfC V)) fun k hk => hCm k hk.1.1 (Or.inl hk.2)`.

Conclude with `hC.of_isClosed_subset hcl fun k hk => hCm k hk.1 (Or.inr hg)`.
-/
theorem adelicUnitary_top_cong : ∀ (D : D7) (V : HSp D), IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ IsClosed (GinfC V : Set (GA D V)) ∧ ∀ (L : Lt D.host.E V.rank) (M : ℕ), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) → 0 < M → ∃ K : Subgroup (GA D V), (∀ k, k ∈ K ↔ CongK V L M k) ∧ IsOpen (K : Set (GA D V)) ∧ IsCompact ((K : Set (GA D V)) ∩ GfC V) ∧ (V.gram = 1 → IsCompact (K : Set (GA D V))) := by
  intro D V
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine ⟨i0, i1, i2, i3, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram, isClosed_GinfC V, ?_⟩
  rintro L M ⟨hfg, hsp⟩ hM
  have ho := isOpen_congSub V L M hfg hsp hM
  have hcl : IsClosed (congSub V L M : Set (GA D V)) := Subgroup.isClosed_of_isOpen _ ho
  obtain ⟨C, hC, hCm⟩ := exists_compact V L hfg hsp
  refine ⟨congSub V L M, fun _ => Iff.rfl, ho, ?_, fun hg => ?_⟩
  · exact hC.of_isClosed_subset (hcl.inter (isClosed_GfC V)) fun k hk => hCm k hk.1.1 (Or.inl hk.2)
  · exact hC.of_isClosed_subset hcl fun k hk => hCm k hk.1 (Or.inr hg)

end GlobalTheory.Ker.CongTop
