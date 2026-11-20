import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.HoweType
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.AtDown
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SbInv
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ValuationNatCastLeOne

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.Loc GlobalTheory.SplitWeil
open Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped ComplexConjugate

/- English proof (translation)
Use `(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ U`. Use `filter_upwards [hU.isOpen.mem_nhds hx, hh.eventually_eq x] with y hy e`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx, e]`. Use `filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy`.

Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`.
-/
private theorem lc_ind {G : Type} [TopologicalSpace G] {U : Set G} (hU : IsClopen U) {h : G → ℂ}
    (hh : IsLocallyConstant h) : IsLocallyConstant (U.indicator h) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx, hh.eventually_eq x] with y hy e
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, e]
  · filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

/- English proof (translation)
Use `haveI : TotallyDisconnectedSpace k := inferInstance`. Use `haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))`. Conclude with `⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩`.
-/
private theorem td_gl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    TotallyDisconnectedSpace (GL (Fin n) k) := by
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/- English proof (translation)
Use `letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩`. Set `r : CompletionsOver E v ≃+* w.1.adicCompletion E` to `RingEquiv.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)`. Establish `hr : Continuous r` using `continuous_apply _`. Establish `hs : Continuous r.symm` using `(Homeomorph.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)).symm.continuous`. Use `⟨{ toEquiv := (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin n) r).toMulEquiv).toEquiv continuous_toFun := ?_ continuous_invFun := ?_ }, fun g => ?_⟩` and prove the remaining obligations.

Conclude with `Continuous.units_map _ (continuous_id.matrix_map hr)`. Conclude with `Continuous.units_map _ (continuous_id.matrix_map hs)`. Conclude with `Units.ext (Matrix.ext fun i j => rfl)`.
-/
private theorem cmp_homeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) {v : HeightOneSpectrum (𝓞 F)}
    (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) :
    ∃ e : GL (Fin n) (CompletionsOver E v) ≃ₜ GL (Fin n) (w.1.adicCompletion E), ∀ g, e g = UpperTheory.ConvolutionTheory.GM.cmp w g := by
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let r : CompletionsOver E v ≃+* w.1.adicCompletion E :=
    RingEquiv.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)
  have hr : Continuous r := continuous_apply _
  have hs : Continuous r.symm :=
    (Homeomorph.piUnique (fun u : PlacesOver E v => u.1.adicCompletion E)).symm.continuous
  refine ⟨{ toEquiv := (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin n) r).toMulEquiv).toEquiv
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun g => ?_⟩
  · exact Continuous.units_map _ (continuous_id.matrix_map hr)
  · exact Continuous.units_map _ (continuous_id.matrix_map hs)
  · exact Units.ext (Matrix.ext fun i j => rfl)

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hns`. Take `⟨-, -, hne, huniq, -, -⟩` from `UpperTheory.ConvolutionTheory.T.places F E hp`. Take `⟨w⟩` from `hne v`. Establish `hw : ∀ w' : PlacesOver E v, w' = w` using `huniq v hns w`. Use `letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩`.

Take `⟨ρ, hρ, hdown⟩` from `UpperTheory.ConvolutionTheory.Loc.atDown F E σ hσ v w hw n`. Establish `hN : ball n ρ ∈ nhds (1 : Gw n w.1)` using `(UpperTheory.ConvolutionTheory.Loc.BallG.isOpen_ball hρ.ne').mem_nhds (fun i j => by simp)`. Take `⟨J, χ, hCO, hchr, hJN, hrank, hne0, hst⟩` from `UpperTheory.ConvolutionTheory.T.howeType F E σ hσ hp n hn μ V hV v w hw _ hN`. Use `haveI : T2Space (Gw n w.1) := (UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n).2.2.1`. Use `haveI : T2Space (Gw n v) := (UpperTheory.V.Z.Tf.Orb.gLTop (v.adicCompletion F) n).2.2.1`.

Establish `hJc : IsClopen (J : Set (Gw n w.1))` using `⟨hCO.1.isClosed, hCO.2⟩`. Set `φ : Gw n w.1 → ℂ` to `(J : Set (Gw n w.1)).indicator fun x => conj (χ x)`. Establish `hφl : IsLocallyConstant φ` using `lc_ind hJc (hchr.1.comp fun z => conj z)`. Establish `hφc : HasCompactSupport φ` using `HasCompactSupport.intro hCO.1 fun x hx => Set.indicator_of_notMem hx _`. Establish `hφS : φ ∈ SB (GL (Fin n) (w.1.adicCompletion E))` using `⟨hφl, hφc⟩`.

Establish `hsupp : Function.support φ ⊆ ball n ρ` using `fun x hx => hJN (Set.mem_of_indicator_ne_zero hx)`. Take `⟨f, hfS, hmatch⟩` from `hdown φ hφS hsupp`. Take `⟨e, he⟩` from `cmp_homeo (F := F) n w hw`. Establish `hec : (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) = φ ∘ e` using `funext fun g => by simp [he]`. Establish `hTE : Test (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g))`.

Rewrite using `[hec]`. Conclude with `⟨hφl.comp_continuous e.continuous, hφc.comp_homeomorph e⟩`. Establish `hTF : Test f` using `hfS`. Take `⟨U₁, hU₁o, hU₁K, hU₁⟩` from `UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n w.1) φ hφS (GLnLocal.integralGL (w.1.adicCompletion E) n) (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)`. Take `⟨U₂, hU₂o, hU₂K, hU₂⟩` from `UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n v) f hfS (GLnLocal.integralGL (v.adicCompletion F) n) (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)`.

Set `J' : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)` to `fun u => (hw u).symm ▸ J`. Set `χ' : ∀ u : PlacesOver E v, Gw n u.1 → ℂ` to `fun u => (hw u).symm ▸ χ`. Establish `all : ∀ P : PlacesOver E v → Prop, P w → ∀ u, P u` using `fun P h u => (hw u).symm ▸ h`. Establish `hprod : (UpperTheory.ConvolutionTheory.GM.prodFn fun u : PlacesOver E v => (J' u : Set (Gw n u.1)).indicator fun x => conj (χ' u x)) = fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)` using `funext fun g => by`. Unfold `UpperTheory.ConvolutionTheory.GM.prodFn`.

Conclude with `finprod_unique (fun u : PlacesOver E v => (J' u : Set (Gw n u.1)).indicator (fun x => conj (χ' u x)) (UpperTheory.ConvolutionTheory.GM.cmp u g))`. Use `⟨J', χ', f, U₁.comap (UpperTheory.ConvolutionTheory.GM.cmp w), U₂, ?_, ?_, by rw [hprod]; exact hmatch, by rw [hprod]; exact hTE, hTF, ?_, ?_, hU₂o, hU₂K, ?_, ?_⟩` and prove the remaining obligations. Conclude with `all _ ⟨hCO, hchr, hrank, hne0⟩`. Introduce `x hx`. Establish `hxw : UpperTheory.ConvolutionTheory.GM.cmp w x ∈ J` using `hx w`.

Take `⟨h1, h2⟩` from `hst x hxw`. Use `⟨all _ h1, ?_⟩` and prove the remaining obligations. Rewrite using `[finprod_unique, finprod_unique]`. Conclude with `h2`. Establish `: (UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) = e` using `funext fun g => (he g).symm`.

Express the relevant statement in the definitionally equal form `IsOpen ((UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) ⁻¹' (U₁ : Set (Gw n w.1)))`. Rewrite using `[this]`. Conclude with `hU₁o.preimage e.continuous`. Introduce `g hg u`. Establish `hu` using `hw u`.

Substitute `hu` using the available equality. Conclude with `hU₁K hg`. Introduce `y hy g`. Rewrite using `[hprod]`. Express the relevant statement in the definitionally equal form `φ (UpperTheory.ConvolutionTheory.GM.cmp w (y * g)) = φ (UpperTheory.ConvolutionTheory.GM.cmp w g)`.

Rewrite using `[map_mul]`. Conclude with `(hU₁ _ hy _).1`. Introduce `y hy g`. Conclude with `(hU₂ y hy g).1`.
-/
theorem UpperTheory.ConvolutionTheory.T.inertData :
    UpperTheory.ConvolutionTheory.T.InertData := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hns
  obtain ⟨-, -, hne, huniq, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨w⟩ := hne v
  have hw : ∀ w' : PlacesOver E v, w' = w := huniq v hns w
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  obtain ⟨ρ, hρ, hdown⟩ := UpperTheory.ConvolutionTheory.Loc.atDown F E σ hσ v w hw n
  have hN : ball n ρ ∈ nhds (1 : Gw n w.1) :=
    (UpperTheory.ConvolutionTheory.Loc.BallG.isOpen_ball hρ.ne').mem_nhds (fun i j => by simp)
  obtain ⟨J, χ, hCO, hchr, hJN, hrank, hne0, hst⟩ := UpperTheory.ConvolutionTheory.T.howeType F E σ hσ hp n hn μ V hV v w hw _ hN
  haveI : T2Space (Gw n w.1) := (UpperTheory.V.Z.Tf.Orb.gLTop (w.1.adicCompletion E) n).2.2.1
  haveI : T2Space (Gw n v) := (UpperTheory.V.Z.Tf.Orb.gLTop (v.adicCompletion F) n).2.2.1
  have hJc : IsClopen (J : Set (Gw n w.1)) := ⟨hCO.1.isClosed, hCO.2⟩
  let φ : Gw n w.1 → ℂ := (J : Set (Gw n w.1)).indicator fun x => conj (χ x)
  have hφl : IsLocallyConstant φ := lc_ind hJc (hchr.1.comp fun z => conj z)
  have hφc : HasCompactSupport φ := HasCompactSupport.intro hCO.1 fun x hx => Set.indicator_of_notMem hx _
  have hφS : φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)) := ⟨hφl, hφc⟩
  have hsupp : Function.support φ ⊆ ball n ρ := fun x hx => hJN (Set.mem_of_indicator_ne_zero hx)
  obtain ⟨f, hfS, hmatch⟩ := hdown φ hφS hsupp
  obtain ⟨e, he⟩ := cmp_homeo (F := F) n w hw
  have hec : (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) = φ ∘ e := funext fun g => by simp [he]
  have hTE : Test (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) := by
    rw [hec]
    exact ⟨hφl.comp_continuous e.continuous, hφc.comp_homeomorph e⟩
  have hTF : Test f := hfS
  obtain ⟨U₁, hU₁o, hU₁K, hU₁⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n w.1) φ hφS (GLnLocal.integralGL (w.1.adicCompletion E) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  obtain ⟨U₂, hU₂o, hU₂K, hU₂⟩ := UpperTheory.ConvolutionTheory.Loc.sbInv (Gw n v) f hfS (GLnLocal.integralGL (v.adicCompletion F) n)
    (GLnLocal.isOpen_integralGL _ _) (GLnLocal.isCompact_integralGL _ _) (td_gl _ n)
  let J' : ∀ u : PlacesOver E v, Subgroup (Gw n u.1) := fun u => (hw u).symm ▸ J
  let χ' : ∀ u : PlacesOver E v, Gw n u.1 → ℂ := fun u => (hw u).symm ▸ χ
  have all : ∀ P : PlacesOver E v → Prop, P w → ∀ u, P u := fun P h u => (hw u).symm ▸ h
  have hprod : (UpperTheory.ConvolutionTheory.GM.prodFn fun u : PlacesOver E v => (J' u : Set (Gw n u.1)).indicator fun x => conj (χ' u x)) =
      fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g) := funext fun g => by
    unfold UpperTheory.ConvolutionTheory.GM.prodFn
    exact finprod_unique (fun u : PlacesOver E v =>
      (J' u : Set (Gw n u.1)).indicator (fun x => conj (χ' u x)) (UpperTheory.ConvolutionTheory.GM.cmp u g))
  refine ⟨J', χ', f, U₁.comap (UpperTheory.ConvolutionTheory.GM.cmp w), U₂, ?_, ?_, by rw [hprod]; exact hmatch, by rw [hprod]; exact hTE, hTF, ?_, ?_, hU₂o, hU₂K, ?_, ?_⟩
  · exact all _ ⟨hCO, hchr, hrank, hne0⟩
  · intro x hx
    have hxw : UpperTheory.ConvolutionTheory.GM.cmp w x ∈ J := hx w
    obtain ⟨h1, h2⟩ := hst x hxw
    refine ⟨all _ h1, ?_⟩
    rw [finprod_unique, finprod_unique]
    exact h2
  · have : (UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) = e := funext fun g => (he g).symm
    change IsOpen ((UpperTheory.ConvolutionTheory.GM.cmp w : GL (Fin n) (CompletionsOver E v) → Gw n w.1) ⁻¹' (U₁ : Set (Gw n w.1)))
    rw [this]
    exact hU₁o.preimage e.continuous
  · intro g hg u
    have hu := hw u
    subst hu
    exact hU₁K hg
  · intro y hy g
    rw [hprod]
    change φ (UpperTheory.ConvolutionTheory.GM.cmp w (y * g)) = φ (UpperTheory.ConvolutionTheory.GM.cmp w g)
    rw [map_mul]
    exact (hU₁ _ hy _).1
  · intro y hy g
    exact (hU₂ y hy g).1
