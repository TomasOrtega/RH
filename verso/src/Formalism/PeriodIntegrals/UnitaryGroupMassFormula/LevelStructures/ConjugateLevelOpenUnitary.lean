import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uLeKfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.HaarIdx

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

variable {D : D7}

def levelSubgroupOfCharacter (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' := fun ha hb => hK.2.1 _ ha _ hb
  inv_mem' := fun ha => hK.2.2.1 _ ha

def conjugateLevelSubgroup (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) :
    Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  ((levelSubgroupOfCharacter X hK).map (PI.MassDataKppVolLemmas.tfHom X.B.I hb)).map
    (MulAut.conj (finHA X hb (X.xu w))).toMonoidHom

/- English proof (translation)
Rewrite using `[conjugateLevelSubgroup, Subgroup.coe_map, Subgroup.coe_map]`. Both sides reduce to the same expression.
-/
theorem coe_K2uSub (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) :
    (conjugateLevelSubgroup X hb hK w : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) = K2u X hb w := by
  rw [conjugateLevelSubgroup, Subgroup.coe_map, Subgroup.coe_map]
  rfl

def conjugateLevelLocal (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word)
    (v : HeightOneSpectrum (𝓞 X.B.I.F)) : Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :=
  (conjugateLevelSubgroup X hb hK w).map (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v))

/- English proof (translation)
Rewrite using `[conjugateLevelLocal, Subgroup.coe_map, coe_K2uSub]`. Both sides reduce to the same expression.
-/
theorem coe_K2vSub (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word)
    (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    (conjugateLevelLocal X hb hK w v : Set (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J)) =
      compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) v := by
  rw [conjugateLevelLocal, Subgroup.coe_map, coe_K2uSub]
  rfl

def KvSub (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :=
  (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).comap
    (HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J).subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_KvSub (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    (KvSub X v : Set (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J)) =
      Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v := rfl

/- English proof (translation)
Introduce and unpack `_ ⟨h, hh, rfl⟩`. Establish `h1 : h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))` using `k2uLeKf_holds X hb hK hL w (by rw [← coe_K2uSub X hb hK w]; exact hh)`. Rewrite `h1` using `[Kf, Subgroup.mem_iInf]`. Conclude with `h1 v`.
-/
theorem local_level_le_maximal (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (w : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) : conjugateLevelLocal X hb hK w v ≤ KvSub X v := by
  rintro _ ⟨h, hh, rfl⟩
  have h1 : h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    k2uLeKf_holds X hb hK hL w (by rw [← coe_K2uSub X hb hK w]; exact hh)
  rw [Kf, Subgroup.mem_iInf] at h1
  exact h1 v

def ConjugateLevelOpenUnitary : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, IsOpen (Subtype.val ⁻¹' K2u X hb w :
      Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)))

def ParabolicLevelOpenLocal : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), IsOpen (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))

/- English proof (translation)
Establish `hc : Continuous fun q : S × S => ((q.1 : G) * (q.2 : G))` using `(continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)`. Conclude with `⟨hc.subtype_mk (fun q => S.mul_mem q.1.2 q.2.2)⟩`.
-/
theorem contMul_sub {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (S : Subgroup G) :
    ContinuousMul S := by
  have hc : Continuous fun q : S × S => ((q.1 : G) * (q.2 : G)) :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  exact ⟨hc.subtype_mk (fun q => S.mul_mem q.1.2 q.2.2)⟩

/- English proof (translation)
Establish `: FiniteDimensional X.B.I.F X.B.I.E` using `Module.Finite.of_restrictScalars_finite ℚ _ _`. Establish `: IsModuleTopology (Af X.B.I.F) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)` using `⟨rfl⟩`. Use `IsModuleTopology.isTopologicalRing (Af X.B.I.F) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)` as an intermediate fact. Conclude with `inferInstanceAs (ContinuousMul (HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))`.
-/
theorem contMul_HAf {D : D7} (X : HidaSetting D) : ContinuousMul (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsModuleTopology (Af X.B.I.F) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E) := ⟨rfl⟩
  have := IsModuleTopology.isTopologicalRing (Af X.B.I.F) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)
  exact inferInstanceAs (ContinuousMul (HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))

/- English proof (translation)
Establish `: FiniteDimensional X.B.I.F X.B.I.E` using `Module.Finite.of_restrictScalars_finite ℚ _ _`. Establish `: IsModuleTopology (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)` using `⟨rfl⟩`. Use `IsModuleTopology.isTopologicalRing (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)` as an intermediate fact. Conclude with `inferInstanceAs (ContinuousMul (HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J))`.
-/
theorem contMul_HAv {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    ContinuousMul (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsModuleTopology (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := ⟨rfl⟩
  have := IsModuleTopology.isTopologicalRing (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
  exact inferInstanceAs (ContinuousMul (HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J))

/- English proof (translation)
Introduce `D X hb hK hT hL w`. Establish `hH : ((X.measW w).μHf).IsHaarMeasure` using `(X.measW_norm w).2.2.1`. Use `contMul_HAf X` as an intermediate fact. Use `contMul_sub (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))` as an intermediate fact. Use `haveI : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩`.

Establish `eA : (Subtype.val ⁻¹' K2u X hb w : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) = (((conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _)`. Use extensionality with `x`. Use `show (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb w ↔ (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ conjugateLevelSubgroup X hb hK w`. Rewrite using `[← coe_K2uSub X hb hK w]`. Both sides reduce to the same expression.

Establish `eB : (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) = (((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf (Hsu …` using `rfl`. Establish `hle : (conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) ≤ (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))`. Introduce `x hx`. Rewrite `hx`, the goal using `[Subgroup.mem_subgroupOf]`. Conclude with `k2uLeKf_holds X hb hK hL w (by rw [← coe_K2uSub X hb hK w]; exact hx)`.

Establish `hop` using `hO X hb hK hT hL w`. Rewrite `hop` using `[eA]`. Establish `hBor : BorelSpace (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))` using `Subtype.borelSpace ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) : Subgroup _) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))`. Establish `key` using `toReal_eq_relIndex_mul_of_haar (G := Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) (contMul_sub _) hBor (X.measW w).μHf hH _ _ hle hop`. Establish `eA' : Subgroup.closure (Subtype.val ⁻¹' K2u X hb w : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) = (conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))`.

Rewrite using `[eA, Subgroup.closure_eq]`. Establish `eB' : Subgroup.closure (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) = (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) …`. Rewrite using `[eB, Subgroup.closure_eq]`. Unfold `muHf muHfpp idxH`. Use `erw [eA', eB', eA, eB]`.

Apply the tactic sequence `all_goals exact key`.
-/
theorem haarIdxGlob_of (hO : ConjugateLevelOpenUnitary) : HaarIdxGlob := by
  intro D X hb hK hT hL w
  have hH : ((X.measW w).μHf).IsHaarMeasure := (X.measW_norm w).2.2.1
  have := contMul_HAf X
  have := contMul_sub (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
  haveI : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have eA : (Subtype.val ⁻¹' K2u X hb w : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := by
    ext x
    show (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb w ↔ (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ conjugateLevelSubgroup X hb hK w
    rw [← coe_K2uSub X hb hK w]
    rfl
  have eB : (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := rfl
  have hle : (conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) ≤
      (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact k2uLeKf_holds X hb hK hL w (by rw [← coe_K2uSub X hb hK w]; exact hx)
  have hop := hO X hb hK hT hL w
  rw [eA] at hop
  have hBor : BorelSpace (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) :=
    Subtype.borelSpace ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) : Subgroup _) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))
  have key := toReal_eq_relIndex_mul_of_haar (G := Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
    (contMul_sub _) hBor
    (X.measW w).μHf hH _ _ hle hop
  have eA' : Subgroup.closure (Subtype.val ⁻¹' K2u X hb w :
      Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eA, Subgroup.closure_eq]
  have eB' : Subgroup.closure (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eB, Subgroup.closure_eq]
  unfold muHf muHfpp idxH
  erw [eA', eB', eA, eB]
  all_goals exact key

/- English proof (translation)
Introduce `D X hb hK hT hL w p`. Establish `hH : ((X.measW w).μSv p.1).IsHaarMeasure` using `(X.measW_norm w).2.2.2.2.2.2.2.1 p.1`. Use `contMul_HAv X p.1` as an intermediate fact. Use `contMul_sub (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))` as an intermediate fact. Use `haveI : BorelSpace (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩`.

Establish `eA : (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 : Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) = (((conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _)`. Use extensionality with `x`. Use `show (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 ↔ (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ conjugateLevelLocal X hb hK w p.1`. Rewrite using `[← coe_K2vSub X hb hK w p.1]`. Both sides reduce to the same expression.

Establish `eB : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) = (((KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _)` using `rfl`. Establish `hle : (conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) ≤ (KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))`. Introduce `x hx`. Rewrite `hx`, the goal using `[Subgroup.mem_subgroupOf]`. Conclude with `local_level_le_maximal X hb hK hL w p.1 hx`.

Establish `hop` using `hO X hb hK hT hL w p`. Rewrite `hop` using `[eA]`. Establish `hBor : BorelSpace (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))` using `Subtype.borelSpace ((Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) : Subgroup _) : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J))`. Establish `key` using `toReal_eq_relIndex_mul_of_haar (G := Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) (contMul_sub _) hBor ((X.measW w).μSv p.1) hH _ _ hle hop`. Establish `eA' : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 : Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) = (conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))`.

Rewrite using `[eA, Subgroup.closure_eq]`. Establish `eB' : Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 : Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) = (KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))`. Rewrite using `[eB, Subgroup.closure_eq]`. Unfold `muSv muSvpp idxS`. Use `erw [eA', eB', eA, eB]`.

Apply the tactic sequence `all_goals exact key`.
-/
theorem haarIdxLoc_of (hO : ParabolicLevelOpenLocal) : HaarIdxLoc := by
  intro D X hb hK hT hL w p
  have hH : ((X.measW w).μSv p.1).IsHaarMeasure := (X.measW_norm w).2.2.2.2.2.2.2.1 p.1
  have := contMul_HAv X p.1
  have := contMul_sub (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))
  haveI : BorelSpace (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have eA : (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := by
    ext x
    show (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 ↔
      (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ conjugateLevelLocal X hb hK w p.1
    rw [← coe_K2vSub X hb hK w p.1]
    rfl
  have eB : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := rfl
  have hle : (conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) ≤
      (KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact local_level_le_maximal X hb hK hL w p.1 hx
  have hop := hO X hb hK hT hL w p
  rw [eA] at hop
  have hBor : BorelSpace (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) :=
    Subtype.borelSpace ((Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) : Subgroup _) :
      Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J))
  have key := toReal_eq_relIndex_mul_of_haar (G := Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))
    (contMul_sub _) hBor
    ((X.measW w).μSv p.1) hH _ _ hle hop
  have eA' : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eA, Subgroup.closure_eq]
  have eB' : Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eB, Subgroup.closure_eq]
  unfold muSv muSvpp idxS
  erw [eA', eB', eA, eB]
  all_goals exact key

end MassDataLevelSSteps
