import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

def CharSupp : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
      (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (T : SmIrr (GL (Fin n) (u.adicCompletion L))), π.IsLocComp v τ → P.IsLocComp u T →
      ∀ (ξ : Fin n → ((v.adicCompletion K)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport τ.ρ (GlobalTheory.RoadU.chars ξ hξ) →
        HasSupport T.ρ (GlobalTheory.RoadU.chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u))
          fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j))

def CharLiftPrime : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ a : ℕ, 1 ≤ a → ∀ (π : CuspSub K a) (P : CuspSub L a),
    GlobalTheory.GalCut.IsLift π P → GlobalTheory.RoadU.CharLift π P

def UnlThru : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) s s', SuppAt π v s → SuppAt P w.1 s' → GlobalTheory.RoadU.Unlinked s →
      ∀ ζ hζ, IrrGL.ofChar ζ hζ ∈ s' → Thru w ζ → ∀ y ∈ s', IrrGL.ofChar ζ hζ ≠ y.nu 1 ∧ y ≠ (IrrGL.ofChar ζ hζ).nu 1

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `e : ∃ ζ : kˣ →* ℂˣ, ∃ hζ, IrrGL.ofChar ξ h = IrrGL.ofChar ζ hζ` using `⟨ξ, h, rfl⟩`. Use `Multiset.filterMap_cons_some _ _ _ ?_` and prove the remaining obligations. Rewrite using `[dif_pos e]`. Take `⟨_, h2⟩` from `e.choose_spec`. Conclude with `congrArg some (IrrGL.ofChar_inj.1 h2).symm`.
-/
theorem chs_cons (ξ : kˣ →* ℂˣ) (h : IsSmoothChar ξ) (s : Multiset (IrrGL k)) : chs (IrrGL.ofChar ξ h ::ₘ s) = ξ ::ₘ chs s := by
  have e : ∃ ζ : kˣ →* ℂˣ, ∃ hζ, IrrGL.ofChar ξ h = IrrGL.ofChar ζ hζ := ⟨ξ, h, rfl⟩
  refine Multiset.filterMap_cons_some _ _ _ ?_
  rw [dif_pos e]
  obtain ⟨_, h2⟩ := e.choose_spec
  exact congrArg some (IrrGL.ofChar_inj.1 h2).symm

/- English proof (translation)
The claim follows from `Multiset.filterMap_cons_none _ _ (dif_neg h)`.
-/
theorem chs_cons_of_not {y : IrrGL k} (h : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) (s : Multiset (IrrGL k)) :
    chs (y ::ₘ s) = chs s := Multiset.filterMap_cons_none _ _ (dif_neg h)

/- English proof (translation)
Proceed by induction on `t using Multiset.induction with`. Consider the case `empty => rfl`. Consider the case `cons a t ih => rw [Multiset.map_cons, chs_cons, ih, Multiset.map_cons]`.
-/
theorem chs_map {ι : Type} (t : Multiset ι) (ξ : ι → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) :
    chs (t.map fun j => IrrGL.ofChar (ξ j) (hξ j)) = t.map ξ := by
  induction t using Multiset.induction with
  | empty => rfl
  | cons a t ih => rw [Multiset.map_cons, chs_cons, ih, Multiset.map_cons]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction with`. Consider the case `empty => exact ⟨le_rfl, fun _ y hy => absurd hy (Multiset.notMem_zero _)⟩`. Consider the case `cons a s ih`. Take `⟨h1, h2⟩` from `ih fun y hy => h y (Multiset.mem_cons_of_mem hy)`. Establish `ha` using `h a (Multiset.mem_cons_self _ _)`.

Rewrite using `[Multiset.map_cons, Multiset.sum_cons]`. Distinguish the cases in `c : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, a = IrrGL.ofChar ξ hξ`. Take `⟨ξ, hξ, rfl⟩` from `c`. Establish `e : (IrrGL.ofChar ξ hξ).1 = 1` using `rfl`. Rewrite using `[chs_cons, Multiset.card_cons, e]`.

Use `⟨by omega, fun H y hy => ?_⟩` and prove the remaining obligations. Break down `Multiset.mem_cons.1 hy with rfl | hy` into its components or cases. Conclude with `⟨ξ, hξ, rfl⟩`. Conclude with `h2 (by omega) y hy`. Rewrite using `[chs_cons_of_not c]`.

Conclude with `⟨by omega, fun H => by omega⟩`.
-/
theorem card_chs_le (s : Multiset (IrrGL k)) (h : ∀ y ∈ s, 0 < y.1) :
    Multiset.card (chs s) ≤ (s.map Sigma.fst).sum ∧
      (Multiset.card (chs s) = (s.map Sigma.fst).sum → ∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) := by
  induction s using Multiset.induction with
  | empty => exact ⟨le_rfl, fun _ y hy => absurd hy (Multiset.notMem_zero _)⟩
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    have ha := h a (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.sum_cons]
    by_cases c : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, a = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := c
      have e : (IrrGL.ofChar ξ hξ).1 = 1 := rfl
      rw [chs_cons, Multiset.card_cons, e]
      refine ⟨by omega, fun H y hy => ?_⟩
      rcases Multiset.mem_cons.1 hy with rfl | hy
      · exact ⟨ξ, hξ, rfl⟩
      · exact h2 (by omega) y hy
    · rw [chs_cons_of_not c]
      exact ⟨by omega, fun H => by omega⟩

/- English proof (translation)
Establish `key : ∀ s : Multiset (IrrGL k), (∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) → s = (chs s).map fun ξ => if h : IsSmoothChar ξ then IrrGL.ofChar ξ h else IrrGL.ofChar 1 isSmoothChar_one`. Introduce `s`. Proceed by induction on `s using Multiset.induction with`. Consider the case `empty => intro _`. Both sides reduce to the same expression.

Consider the case `cons a s ih`. Introduce `H`. Take `⟨ξ, hξ, rfl⟩` from `H a (Multiset.mem_cons_self _ _)`. Rewrite using `[chs_cons, Multiset.map_cons, dif_pos hξ, ← ih fun y hy => H y (Multiset.mem_cons_of_mem hy)]`. Rewrite using `[key s hs, key t ht, h]`.
-/
theorem eq_of_chs {s t : Multiset (IrrGL k)} (hs : ∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (ht : ∀ y ∈ t, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) (h : chs s = chs t) : s = t := by
  have key : ∀ s : Multiset (IrrGL k), (∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) →
      s = (chs s).map fun ξ => if h : IsSmoothChar ξ then IrrGL.ofChar ξ h else IrrGL.ofChar 1 isSmoothChar_one := by
    intro s
    induction s using Multiset.induction with
    | empty => intro _; rfl
    | cons a s ih =>
      intro H
      obtain ⟨ξ, hξ, rfl⟩ := H a (Multiset.mem_cons_self _ _)
      rw [chs_cons, Multiset.map_cons, dif_pos hξ, ← ih fun y hy => H y (Multiset.mem_cons_of_mem hy)]
  rw [key s hs, key t ht, h]

end

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ _ _ hp n hn π P hW v u hu τ T hτ hT ξ hξ hs`. Take `⟨⟨s', hs'⟩, huniq, hdeg, -⟩` from `h3 L n hn P u`. Establish `H` using `h1 K L hp n hn π P hW v ⟨u, hu⟩ _ s' ⟨τ, hτ, hs⟩ hs'`. Take `⟨-, hsum, hpos⟩` from `hdeg s' hs'`. Take `⟨c1, c2⟩` from `card_chs_le s' hpos`.

Rewrite `H` using `[up, GlobalTheory.RoadU.chars, chs_map, h2 K L v ⟨u, hu⟩, Multiset.map_map]`. Establish `hc : Multiset.card ((chs s').filter (Thru (v` using `v) ⟨u, hu⟩)) = n := by rw [H]; simp`. Establish `hle` using `Multiset.filter_le (Thru (v := v) ⟨u, hu⟩) (chs s')`. Establish `hc'` using `Multiset.card_le_card hle`. Establish `e` using `Multiset.eq_of_le_of_card_le hle (by omega)`.

Establish `es : s' = GlobalTheory.RoadU.chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j)`. Use `eq_of_chs (c2 (by omega)) (fun y hy => ?_) ?_` and prove the remaining obligations. Take `⟨j, -, rfl⟩` from `Multiset.mem_map.1 hy`. Conclude with `⟨_, _, rfl⟩`. Rewrite using `[← e, H, GlobalTheory.RoadU.chars, chs_map]`.

Both sides reduce to the same expression. Take `⟨T', hT', hs''⟩` from `hs'`. Establish `h1 : (CG.mk P).IsLoc u (Quotient.mk _ T)` using `hT`. Establish `h2 : (CG.mk P).IsLoc u (Quotient.mk _ T')` using `hT'`. Take `⟨φ⟩` from `Quotient.exact (CG.IsLoc.unique L n _ u _ _ h2 h1)`.

Conclude with `es ▸ hs''.of_equiv φ`.
-/
theorem charSupp_of (h1 : GamMixed) (h2 : NmEq) (h3 : SuppFacts) : CharSupp := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hW v u hu τ T hτ hT ξ hξ hs
  obtain ⟨⟨s', hs'⟩, huniq, hdeg, -⟩ := h3 L n hn P u
  have H := h1 K L hp n hn π P hW v ⟨u, hu⟩ _ s' ⟨τ, hτ, hs⟩ hs'
  obtain ⟨-, hsum, hpos⟩ := hdeg s' hs'
  obtain ⟨c1, c2⟩ := card_chs_le s' hpos
  rw [up, GlobalTheory.RoadU.chars, chs_map, h2 K L v ⟨u, hu⟩, Multiset.map_map] at H
  have hc : Multiset.card ((chs s').filter (Thru (v := v) ⟨u, hu⟩)) = n := by rw [H]; simp
  have hle := Multiset.filter_le (Thru (v := v) ⟨u, hu⟩) (chs s')
  have hc' := Multiset.card_le_card hle
  have e := Multiset.eq_of_le_of_card_le hle (by omega)
  have es : s' = GlobalTheory.RoadU.chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u))
      fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j) := by
    refine eq_of_chs (c2 (by omega)) (fun y hy => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
      exact ⟨_, _, rfl⟩
    · rw [← e, H, GlobalTheory.RoadU.chars, chs_map]; rfl
  obtain ⟨T', hT', hs''⟩ := hs'
  have h1 : (CG.mk P).IsLoc u (Quotient.mk _ T) := hT
  have h2 : (CG.mk P).IsLoc u (Quotient.mk _ T') := hT'
  obtain ⟨φ⟩ := Quotient.exact (CG.IsLoc.unique L n _ u _ _ h2 h1)
  exact es ▸ hs''.of_equiv φ

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ _ _ hp a ha π P hL`. Use `⟨hL, fun v u _ => h K L hp a ha π P ?_ v u⟩` and prove the remaining obligations. Unfold `WeakBC`. Use `filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL K a π)] with w hw`. Take `⟨B, hB⟩` from `hw`.

Conclude with `fun f hf => ⟨B, hB, hL.sat w f B hf hB⟩`.
-/
theorem charLiftPrime_of (h : CharSupp) : CharLiftPrime := by
  intro K L _ _ _ _ _ _ _ _ hp a ha π P hL
  refine ⟨hL, fun v u _ => h K L hp a ha π P ?_ v u⟩
  unfold WeakBC
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually
    (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL K a π)] with w hw
  obtain ⟨B, hB⟩ := hw
  exact fun f hf => ⟨B, hB, hL.sat w f B hf hB⟩

def UnlThruOf : Prop := GamMixed → Spread → ChsFacts → NormVal → PolFacts → UnlThru

end UpperTheory.Gal.GamX
