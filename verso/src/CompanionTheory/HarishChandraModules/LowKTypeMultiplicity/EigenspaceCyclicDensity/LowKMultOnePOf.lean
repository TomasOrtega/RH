import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.LK

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight CasK Cas)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsDS rhoC)
open CompanionTheory.D.DSIC (KRel KUnit KStab LowSpan HWMap)

variable {n : ℕ}

section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Simplify using `only [CompanionTheory.D.LK.evK, CompanionTheory.D.LK.ev, CompanionTheory.D.LK.allT, if_true]`.
-/
theorem evK_allT (E : Fin n → Fin n → Module.End ℂ V) : evK (allT n) E = ev E := by
  simp only [CompanionTheory.D.LK.evK, CompanionTheory.D.LK.ev, CompanionTheory.D.LK.allT, if_true]

/- English proof (translation)
Use `FreeAlgebra.induction ℂ (Fin n) (fun r => ?_) (fun c => ?_) (fun a b ha hb => ?_) (fun a b ha hb => ?_) b` and prove the remaining obligations. Simplify using `only [AlgHom.commutes, Module.algebraMap_end_apply]`. Both sides reduce to the same expression. Simplify using `only [CompanionTheory.D.LK.evd, FreeAlgebra.lift_ι_apply, h]`. Rewrite using `[map_mul, Module.End.mul_apply, hb, map_smul, ha, map_mul, smul_smul, mul_comm]`.

Rewrite using `[map_add, LinearMap.add_apply, ha, hb, map_add, add_smul]`.
-/
theorem evd_eig (F : Fin n → Module.End ℂ V) (τ : Fin n → ℂ) (x : V) (h : ∀ c, F c x = τ c • x)
    (b : FreeAlgebra ℂ (Fin n)) : evd F b x = FreeAlgebra.lift ℂ τ b • x := by
  refine FreeAlgebra.induction ℂ (Fin n) (fun r => ?_) (fun c => ?_) (fun a b ha hb => ?_) (fun a b ha hb => ?_) b
  · simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rfl
  · simp only [CompanionTheory.D.LK.evd, FreeAlgebra.lift_ι_apply, h]
  · rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, map_mul, smul_smul, mul_comm]
  · rw [map_add, LinearMap.add_apply, ha, hb, map_add, add_smul]

/- English proof (translation)
Unfold `CompanionTheory.D.LK.Cyc`. Rewrite using `[LinearMap.mem_range]`. Conclude with `Iff.rfl`.
-/
theorem mem_cyc {E : Fin n → Fin n → Module.End ℂ V} {v w : V} : w ∈ Cyc E v ↔ ∃ a, ev E a v = w := by
  unfold CompanionTheory.D.LK.Cyc
  rw [LinearMap.mem_range]
  exact Iff.rfl

/- English proof (translation)
Take `⟨a, rfl⟩` from `mem_cyc.1 h`. Use `mem_cyc.2 ⟨FreeAlgebra.ι ℂ (c, d) * a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply]`. Simplify using `only [CompanionTheory.D.LK.ev, FreeAlgebra.lift_ι_apply]`.
-/
theorem cyc_stab {E : Fin n → Fin n → Module.End ℂ V} {v w : V} (c d : Fin n) (h : w ∈ Cyc E v) :
    E c d w ∈ Cyc E v := by
  obtain ⟨a, rfl⟩ := mem_cyc.1 h
  refine mem_cyc.2 ⟨FreeAlgebra.ι ℂ (c, d) * a, ?_⟩
  rw [map_mul, Module.End.mul_apply]
  simp only [CompanionTheory.D.LK.ev, FreeAlgebra.lift_ι_apply]

end

/- English proof (translation)
Introduce `n ε lam V _ _ E hlam hGl hU hLF hIM v w hv0 hv hw hwc`. Establish `hKE : CompanionTheory.D.DSIC.KRel ε E` using `fun a b c d _ _ => hGl a b c d`. Take `⟨S, hSfd, hSst, hvS⟩` from `hLF v`. Take `⟨L, hLS, hvL, hLst, hLirr, -, hLuniq⟩` from `hL n ε V E (lowK ε lam) v S hKE hU hv0 hv hSfd hSst hvS`. Establish `hLfd : FiniteDimensional ℂ L` using `Submodule.finiteDimensional_of_le hLS`.

Set `ET : Fin n → Fin n → Module.End ℂ L` to `fun a b => if h : ε a = ε b then (E a b).restrict (fun x hx => hLst a b h x hx) else 0`. Establish `hET : ∀ a b (h : ε a = ε b) (x : L), ((ET a b x : L) : V) = E a b x`. Introduce `a b h x`. Simplify using `only [ET, dif_pos h, LinearMap.coe_restrict_apply]`. Establish `kET : CompanionTheory.D.DSIC.KRel ε ET`.

Introduce `a b c d hab hcd`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `key` using `LinearMap.congr_fun (hGl a b c d) (x : V)`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub] at key ⊢`. Rewrite using `[hET a b hab, hET c d hcd x, hET c d hcd, hET a b hab x]`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a`. Establish `e1 : ε a = ε d` using `by rw [h1] at hab; exact hab.trans hcd`. Establish `e2 : ε c = ε b` using `by rw [h2] at hcd; exact hcd.trans hab`.

Rewrite `key`, the goal using `[if_pos h1, if_pos h2]`. Rewrite using `[hET a d e1, hET c b e2]`. Conclude with `key`. Establish `e1 : ε a = ε d` using `by rw [h1] at hab; exact hab.trans hcd`. Rewrite `key`, the goal using `[if_pos h1, if_neg h2]`.

Rewrite using `[hET a d e1]`. Simplify using `only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at key ⊢`. Conclude with `key`. Establish `e2 : ε c = ε b` using `by rw [h2] at hcd; exact hcd.trans hab`. Rewrite `key`, the goal using `[if_neg h1, if_pos h2]`.

Rewrite using `[hET c b e2]`. Simplify using `only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at key ⊢`. Conclude with `key`. Rewrite `key`, the goal using `[if_neg h1, if_neg h2]`. Simplify using `only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at key ⊢`.

Conclude with `key`. Establish `uET : CompanionTheory.D.DSIC.KUnit ε ET`. Introduce `a b h x y`. Rewrite using `[Submodule.coe_inner, Submodule.coe_inner, hET a b h, hET b a h.symm]`. Conclude with `hU a b h x y`.

Set `v' : L` to `⟨v, hvL⟩`. Establish `hv'0 : v' ≠ 0` using `fun h0 => hv0 (congrArg Subtype.val h0)`. Establish `hv' : KHighest ε ET (lowK ε lam) v'`. Use `⟨fun a => ?_, fun a b hab h => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hET a a rfl, Submodule.coe_smul]`. Conclude with `hv.1 a`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hET a b h, ZeroMemClass.coe_zero]`. Conclude with `hv.2 a b hab h`.

Take `⟨S2, hS2fd, hS2st, hwS2⟩` from `hLF w`. Take `⟨φ, hφv, hφ⟩` from `hH n ε L V ET E (lowK ε lam) v' w S2 kET uET hKE hU hv'0 hv' hw hS2fd hS2st hwS2`. Establish `hφc : ∀ s : L, φ s ∈ Cyc E v`. Set `L' : Submodule ℂ V` to `Submodule.map L.subtype ((Cyc E v).comap φ)`. Establish `hL'L : L' ≤ L`.

Introduce and unpack `_ ⟨s, -, rfl⟩`. Conclude with `s.2`. Establish `hL'st : CompanionTheory.D.DSIC.KStab ε E L'`. Introduce and unpack `a b h _ ⟨s, hs, rfl⟩`. Use `⟨ET a b s, ?_, hET a b h s⟩` and prove the remaining obligations.

Use `show φ (ET a b s) ∈ Cyc E v`. Rewrite using `[hφ a b h s]`. Conclude with `cyc_stab a b (show φ s ∈ Cyc E v from hs)`. Establish `hvL' : v ∈ L'` using `⟨v', show φ v' ∈ Cyc E v by rw [hφv]; exact hwc, rfl⟩`. Break down `hLirr L' hL'L hL'st with h0 | h0` into its components or cases.

It suffices to derive a contradiction. Establish `hb0 : v ∈ (⊥ : Submodule ℂ V)` using `h0 ▸ hvL'`. Conclude with `hv0 ((Submodule.mem_bot ℂ).1 hb0)`. Introduce `s`. Establish `hs : (s : V) ∈ L'` using `by rw [h0]; exact s.2`.

Take `⟨s', hs', hss'⟩` from `hs`. Establish `: s' = s` using `Subtype.ext hss'`. Rewrite using `[← this]`. Conclude with `hs'`. Take `⟨-, hDφ⟩` from `hD n ε V E (lowK ε lam) v L hKE hU hv0 hvL hv.1 hLfd hLst hLirr hLuniq`.

Take `⟨a, ha⟩` from `hDφ φ hφc`. Establish `hcomm : ∀ c d, ε c = ε d → ∀ s ∈ L, E c d (ev E a s) = ev E a (E c d s)`. Introduce `c d h s hs`. Establish `e1 : ev E a s = φ ⟨s, hs⟩` using `ha ⟨s, hs⟩`. Establish `e2 : ev E a (E c d s) = φ (ET c d ⟨s, hs⟩)`.

Rewrite using `[← ha (ET c d ⟨s, hs⟩), hET c d h]`. Rewrite using `[e1, e2, hφ c d h]`. Take `⟨a', ha'inv, ha'⟩` from `hI n ε V E L a hGl hLst hcomm`. Establish `hwa : ev E a' v = w`. Rewrite using `[ha' v hvL]`.

Conclude with `(ha v').trans hφv`. Take `⟨b, hb⟩` from `hC n a' (fun V' _ _ E' hGl' c => ha'inv V' E' hGl' c c rfl)`. Take `⟨-, hTop⟩` from `hT n ε V E (lowK ε lam) v`. Take `⟨hbd0, hWt⟩` from `hTop hv`. Establish `hfilt : ∀ A : Finset (CompanionTheory.D.LK.Pos n), Pi.single (M` using `fun _ => V) (CompanionTheory.D.LK.om ε) v A ≠ 0 → A = CompanionTheory.D.LK.om ε := by`.

Introduce `A hA`. Assume the negation of the conclusion as `hne`. Apply `hA` to reduce the goal to its premises. Rewrite using `[Pi.single_apply, if_neg hne]`. Establish `hSup : CompanionTheory.D.LK.Sup (CompanionTheory.D.LK.allT n) ∅ (CompanionTheory.D.LK.om ε).card (Pi.single (CompanionTheory.D.LK.om ε) v)`.

Introduce `A hA`. Rewrite using `[hfilt A hA]`. Use `⟨Finset.filter_false_of_mem (fun i _ hi => hi rfl), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.filter_true_of_mem (fun i _ => rfl)]`. Establish `hRef : CompanionTheory.D.LK.Ref (CompanionTheory.D.LK.allT n) ε (Pi.single (CompanionTheory.D.LK.om ε) v)`.

Introduce `A hA i hi _`. Rewrite `hi` using `[hfilt A hA]`. Conclude with `(Finset.mem_filter.1 hi).2`. Take `⟨y, hySup, hy⟩` from `hG n (CompanionTheory.D.LK.allT n) ε a' b (fun _ _ _ => rfl) (fun V' _ _ E' hK' => by`. Establish `hGl' : GlRel E'` using `fun a b c d => hK' a b c d rfl rfl`.

Rewrite using `[evK_allT]`. Conclude with `⟨fun i hi => ha'inv V' E' hGl' _ _ hi, fun x => hb V' E' hGl' x⟩)`. Use `V E (fun a b c d _ _ => hGl a b c d) ∅ _ _ hSup hRef hbd0`. Rewrite `hy` using `[evK_allT]`. Establish `hev : CompanionTheory.D.LK.evd (CompanionTheory.D.LK.Ft (CompanionTheory.D.LK.allT n) E) b (Pi.single (CompanionTheory.D.LK.om ε) v) = FreeAlgebra.lift ℂ (fun c => (((lowK ε lam + (2 : ℝ) • rhoC ε) c : ℝ) : ℂ)) b • Pi.single (CompanionTheory.D.LK.om ε) v` using `evd_eig _ _ _ (fun c => hWt c) b`.

Establish `hlift : CompanionTheory.D.LK.lift n (ev E a') (Pi.single (CompanionTheory.D.LK.om ε) v) = Pi.single (CompanionTheory.D.LK.om ε) w`. Use function extensionality and compare the values at `A`. Rewrite using `[CompanionTheory.D.LK.lift_apply]`. Distinguish the cases in `hA : A = CompanionTheory.D.LK.om ε`. Substitute `hA` using the available equality.

Rewrite using `[Pi.single_eq_same, Pi.single_eq_same, hwa]`. Rewrite using `[Pi.single_eq_of_ne hA, Pi.single_eq_of_ne hA, map_zero]`. Use `set β := FreeAlgebra.lift ℂ (fun c => (((lowK ε lam + (2 : ℝ) • rhoC ε) c : ℝ) : ℂ)) b`. Rewrite `hy` using `[hlift, hev]`. Establish `hu : w - β • v = 0`.

Use `hJ n ε lam V E hlam hGl hU hLF hIM (w - β • v) y (fun a => ?_) hySup ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, hw.1 a, hv.1 a, smul_sub, smul_comm]`. Rewrite using `[← hy, Pi.single_sub, Pi.single_smul']`. Conclude with `⟨β, sub_eq_zero.1 hu⟩`.
-/
theorem multAlg_of (hL : LowSpan) (hH : HWMap) (hD : Dens) (hI : InvLift) (hC : HCdec) (hG : GenCO) (hT : TopCycle)
    (hJ : Inj) : MultAlg := by
  intro n ε lam V _ _ E hlam hGl hU hLF hIM v w hv0 hv hw hwc
  have hKE : CompanionTheory.D.DSIC.KRel ε E := fun a b c d _ _ => hGl a b c d
  obtain ⟨S, hSfd, hSst, hvS⟩ := hLF v
  obtain ⟨L, hLS, hvL, hLst, hLirr, -, hLuniq⟩ := hL n ε V E (lowK ε lam) v S hKE hU hv0 hv hSfd hSst hvS
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLS
  let ET : Fin n → Fin n → Module.End ℂ L := fun a b =>
    if h : ε a = ε b then (E a b).restrict (fun x hx => hLst a b h x hx) else 0
  have hET : ∀ a b (h : ε a = ε b) (x : L), ((ET a b x : L) : V) = E a b x := by
    intro a b h x
    simp only [ET, dif_pos h, LinearMap.coe_restrict_apply]
  have kET : CompanionTheory.D.DSIC.KRel ε ET := by
    intro a b c d hab hcd
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have key := LinearMap.congr_fun (hGl a b c d) (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub] at key ⊢
    rw [hET a b hab, hET c d hcd x, hET c d hcd, hET a b hab x]
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · have e1 : ε a = ε d := by rw [h1] at hab; exact hab.trans hcd
      have e2 : ε c = ε b := by rw [h2] at hcd; exact hcd.trans hab
      rw [if_pos h1, if_pos h2] at key ⊢
      rw [hET a d e1, hET c b e2]
      exact key
    · have e1 : ε a = ε d := by rw [h1] at hab; exact hab.trans hcd
      rw [if_pos h1, if_neg h2] at key ⊢
      rw [hET a d e1]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at key ⊢
      exact key
    · have e2 : ε c = ε b := by rw [h2] at hcd; exact hcd.trans hab
      rw [if_neg h1, if_pos h2] at key ⊢
      rw [hET c b e2]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at key ⊢
      exact key
    · rw [if_neg h1, if_neg h2] at key ⊢
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at key ⊢
      exact key
  have uET : CompanionTheory.D.DSIC.KUnit ε ET := by
    intro a b h x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hET a b h, hET b a h.symm]
    exact hU a b h x y
  let v' : L := ⟨v, hvL⟩
  have hv'0 : v' ≠ 0 := fun h0 => hv0 (congrArg Subtype.val h0)
  have hv' : KHighest ε ET (lowK ε lam) v' := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · apply Subtype.ext
      rw [hET a a rfl, Submodule.coe_smul]
      exact hv.1 a
    · apply Subtype.ext
      rw [hET a b h, ZeroMemClass.coe_zero]
      exact hv.2 a b hab h
  obtain ⟨S2, hS2fd, hS2st, hwS2⟩ := hLF w
  obtain ⟨φ, hφv, hφ⟩ := hH n ε L V ET E (lowK ε lam) v' w S2 kET uET hKE hU hv'0 hv' hw hS2fd hS2st hwS2
  have hφc : ∀ s : L, φ s ∈ Cyc E v := by
    let L' : Submodule ℂ V := Submodule.map L.subtype ((Cyc E v).comap φ)
    have hL'L : L' ≤ L := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2
    have hL'st : CompanionTheory.D.DSIC.KStab ε E L' := by
      rintro a b h _ ⟨s, hs, rfl⟩
      refine ⟨ET a b s, ?_, hET a b h s⟩
      show φ (ET a b s) ∈ Cyc E v
      rw [hφ a b h s]
      exact cyc_stab a b (show φ s ∈ Cyc E v from hs)
    have hvL' : v ∈ L' := ⟨v', show φ v' ∈ Cyc E v by rw [hφv]; exact hwc, rfl⟩
    rcases hLirr L' hL'L hL'st with h0 | h0
    · exfalso
      have hb0 : v ∈ (⊥ : Submodule ℂ V) := h0 ▸ hvL'
      exact hv0 ((Submodule.mem_bot ℂ).1 hb0)
    · intro s
      have hs : (s : V) ∈ L' := by rw [h0]; exact s.2
      obtain ⟨s', hs', hss'⟩ := hs
      have : s' = s := Subtype.ext hss'
      rw [← this]
      exact hs'
  obtain ⟨-, hDφ⟩ := hD n ε V E (lowK ε lam) v L hKE hU hv0 hvL hv.1 hLfd hLst hLirr hLuniq
  obtain ⟨a, ha⟩ := hDφ φ hφc
  have hcomm : ∀ c d, ε c = ε d → ∀ s ∈ L, E c d (ev E a s) = ev E a (E c d s) := by
    intro c d h s hs
    have e1 : ev E a s = φ ⟨s, hs⟩ := ha ⟨s, hs⟩
    have e2 : ev E a (E c d s) = φ (ET c d ⟨s, hs⟩) := by
      rw [← ha (ET c d ⟨s, hs⟩), hET c d h]
    rw [e1, e2, hφ c d h]
  obtain ⟨a', ha'inv, ha'⟩ := hI n ε V E L a hGl hLst hcomm
  have hwa : ev E a' v = w := by
    rw [ha' v hvL]
    exact (ha v').trans hφv
  obtain ⟨b, hb⟩ := hC n a' (fun V' _ _ E' hGl' c => ha'inv V' E' hGl' c c rfl)
  obtain ⟨-, hTop⟩ := hT n ε V E (lowK ε lam) v
  obtain ⟨hbd0, hWt⟩ := hTop hv
  have hfilt : ∀ A : Finset (CompanionTheory.D.LK.Pos n), Pi.single (M := fun _ => V) (CompanionTheory.D.LK.om ε) v A ≠ 0 → A = CompanionTheory.D.LK.om ε := by
    intro A hA
    by_contra hne
    apply hA
    rw [Pi.single_apply, if_neg hne]
  have hSup : CompanionTheory.D.LK.Sup (CompanionTheory.D.LK.allT n) ∅ (CompanionTheory.D.LK.om ε).card (Pi.single (CompanionTheory.D.LK.om ε) v) := by
    intro A hA
    rw [hfilt A hA]
    refine ⟨Finset.filter_false_of_mem (fun i _ hi => hi rfl), ?_⟩
    rw [Finset.filter_true_of_mem (fun i _ => rfl)]
  have hRef : CompanionTheory.D.LK.Ref (CompanionTheory.D.LK.allT n) ε (Pi.single (CompanionTheory.D.LK.om ε) v) := by
    intro A hA i hi _
    rw [hfilt A hA] at hi
    exact (Finset.mem_filter.1 hi).2
  obtain ⟨y, hySup, hy⟩ := hG n (CompanionTheory.D.LK.allT n) ε a' b (fun _ _ _ => rfl)
    (fun V' _ _ E' hK' => by
      have hGl' : GlRel E' := fun a b c d => hK' a b c d rfl rfl
      rw [evK_allT]
      exact ⟨fun i hi => ha'inv V' E' hGl' _ _ hi, fun x => hb V' E' hGl' x⟩)
    V E (fun a b c d _ _ => hGl a b c d) ∅ _ _ hSup hRef hbd0
  rw [evK_allT] at hy
  have hev : CompanionTheory.D.LK.evd (CompanionTheory.D.LK.Ft (CompanionTheory.D.LK.allT n) E) b (Pi.single (CompanionTheory.D.LK.om ε) v)
      = FreeAlgebra.lift ℂ (fun c => (((lowK ε lam + (2 : ℝ) • rhoC ε) c : ℝ) : ℂ)) b • Pi.single (CompanionTheory.D.LK.om ε) v :=
    evd_eig _ _ _ (fun c => hWt c) b
  have hlift : CompanionTheory.D.LK.lift n (ev E a') (Pi.single (CompanionTheory.D.LK.om ε) v) = Pi.single (CompanionTheory.D.LK.om ε) w := by
    funext A
    rw [CompanionTheory.D.LK.lift_apply]
    by_cases hA : A = CompanionTheory.D.LK.om ε
    · subst hA
      rw [Pi.single_eq_same, Pi.single_eq_same, hwa]
    · rw [Pi.single_eq_of_ne hA, Pi.single_eq_of_ne hA, map_zero]
  set β := FreeAlgebra.lift ℂ (fun c => (((lowK ε lam + (2 : ℝ) • rhoC ε) c : ℝ) : ℂ)) b
  rw [hlift, hev] at hy
  have hu : w - β • v = 0 := by
    refine hJ n ε lam V E hlam hGl hU hLF hIM (w - β • v) y (fun a => ?_) hySup ?_
    · rw [map_sub, map_smul, hw.1 a, hv.1 a, smul_sub, smul_comm]
    · rw [← hy, Pi.single_sub, Pi.single_smul']
  exact ⟨β, sub_eq_zero.1 hu⟩

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Establish `hsplit : E c d * Cas E - Cas E * E c d = (∑ a, ∑ b, (if d = a then E c b else 0) * E b a) - (∑ a, ∑ b, (if b = c then E a d else 0) * E b a) + ((∑ a, ∑ b, E a b * (if d = b then E c a else 0)) - (∑ a, ∑ b, E a b * (if a = c then E b d else 0)))`. Simplify using `only [Formalism.REAL.Cas, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Rewrite using `[← sub_mul, ← mul_sub, ← hE c d a b, ← hE c d b a]`.

Use `noncomm_ring`. Establish `T1 : (∑ a, ∑ b, (if d = a then E c b else 0) * E b a) = ∑ b, E c b * E b d`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Establish `T2 : (∑ a, ∑ b, (if b = c then E a d else 0) * E b a) = ∑ a, E a d * E c a`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Simplify using `only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `T3 : (∑ a, ∑ b, E a b * (if d = b then E c a else 0)) = ∑ a, E a d * E c a`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations.

Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `T4 : (∑ a, ∑ b, E a b * (if a = c then E b d else 0)) = ∑ b, E c b * E b d`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[hsplit, T1, T2, T3, T4]`. Normalize the expressions using the abelian group laws.
-/
private lemma commute_E_cas_of_glRel {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (c d : Fin n) :
    E c d * Cas E = Cas E * E c d := by
  rw [← sub_eq_zero]
  have hsplit : E c d * Cas E - Cas E * E c d =
      (∑ a, ∑ b, (if d = a then E c b else 0) * E b a) - (∑ a, ∑ b, (if b = c then E a d else 0) * E b a)
      + ((∑ a, ∑ b, E a b * (if d = b then E c a else 0)) - (∑ a, ∑ b, E a b * (if a = c then E b d else 0))) := by
    simp only [Formalism.REAL.Cas, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [← sub_mul, ← mul_sub, ← hE c d a b, ← hE c d b a]
    noncomm_ring
  have T1 : (∑ a, ∑ b, (if d = a then E c b else 0) * E b a) = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have T2 : (∑ a, ∑ b, (if b = c then E a d else 0) * E b a) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have T3 : (∑ a, ∑ b, E a b * (if d = b then E c a else 0)) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have T4 : (∑ a, ∑ b, E a b * (if a = c then E b d else 0)) = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsplit, T1, T2, T3, T4]
  abel

/- English proof (translation)
Introduce `N ε lam H _ _ σ hHC hDS S S' hS hS'`. Take `⟨hcomp, -, hUR, hIR, -, -, hmin⟩` from `hDS`. Use `haveI := hcomp`. Take `⟨D, E, hK⟩` from `hE N ε H σ hUR hIR`. Establish `hGl : GlRel E` using `hK.gl`.

Establish `hU : CompanionTheory.D.DSIC.KUnit ε E`. Introduce `a b h x y`. Rewrite using `[hK.unit a b x y]`. Simplify using `only [Formalism.REAL.sgn, if_pos h, Complex.ofReal_one, one_mul]`. Establish `hLF : CompanionTheory.D.LK.LocFin ε E` using `hK.locFin`.

Establish `hIM : CompanionTheory.D.LK.IsMin ε E lam`. Introduce `μ x hx hxh`. Take `⟨T, hT⟩` from `hK.ty μ x hx hxh`. Conclude with `hmin μ T hT`. Take `⟨v, hv0, hvS, hv⟩` from `hK.hw _ S hS`.

Take `⟨v', hv'0, hv'S, hv'⟩` from `hK.hw _ S' hS'`. Establish `hmult : ∀ w, KHighest ε E (lowK ε lam) w → w ∈ Cyc E v → ∃ c : ℂ, w = c • v` using `fun w hw hwc => hM N ε lam D E hHC.1 hGl hU hLF hIM v w hv0 hv hw hwc`. Establish `hcv : KHighest ε E (lowK ε lam) (Cas E v)`. Use `⟨fun a => ?_, fun a b hab h => ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, commute_E_cas_of_glRel E hGl a a, Module.End.mul_apply, hv.1 a, map_smul]`.

Rewrite using `[← Module.End.mul_apply, commute_E_cas_of_glRel E hGl a b, Module.End.mul_apply, hv.2 a b hab h, map_zero]`. Establish `hcc : Cas E v ∈ Cyc E v`. Use `mem_cyc.2 ⟨∑ a, ∑ b, FreeAlgebra.ι ℂ (a, b) * FreeAlgebra.ι ℂ (b, a), ?_⟩` and prove the remaining obligations. Simplify using `only [CompanionTheory.D.LK.ev, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Formalism.REAL.Cas]`. Take `⟨c, hc⟩` from `hmult _ hcv hcc`.

Establish `hdense` using `hD N ε H σ D E hUR hIR hK v c hv0 hc`. Use `set u : D := inner ℂ v v • v' - inner ℂ v v' • v with hu_def`. Establish `hu : KHighest ε E (lowK ε lam) u`. Use `⟨fun a => ?_, fun a b hab h => ?_⟩` and prove the remaining obligations. Rewrite using `[hu_def, map_sub, map_smul, map_smul, hv'.1 a, hv.1 a, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm (inner ℂ v v), mul_comm (inner ℂ v v')]`.

Rewrite using `[hu_def, map_sub, map_smul, map_smul, hv'.2 a b hab h, hv.2 a b hab h, smul_zero, smul_zero, sub_zero]`. Establish `horth0 : inner ℂ v u = 0`. Rewrite using `[hu_def, inner_sub_right, inner_smul_right, inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree. Establish `horth` using `hO N ε D E (lowK ε lam) v u hGl hU hLF (fun w hwc hw => hmult w hw hwc) hu horth0`.

Establish `hsub : Submodule.map D.subtype (Cyc E v) ≤ (ℂ ∙ (u : H))ᗮ`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Rewrite using `[Submodule.mem_orthogonal_singleton_iff_inner_left]`. Conclude with `(Submodule.coe_inner D m u).symm.trans (horth m hm)`. Establish `hcl` using `Submodule.topologicalClosure_minimal _ hsub (Submodule.isClosed_orthogonal _)`.

Rewrite `hcl` using `[hdense]`. Establish `hum : (u : H) ∈ (ℂ ∙ (u : H))ᗮ` using `hcl Submodule.mem_top`. Rewrite `hum` using `[Submodule.mem_orthogonal_singleton_iff_inner_left, inner_self_eq_zero]`. Establish `hu0 : u = 0` using `Subtype.ext hum`. Establish `hvv : inner ℂ v v ≠ 0` using `inner_self_ne_zero.2 hv0`.

Establish `heq : inner ℂ v v • v' = inner ℂ v v' • v` using `sub_eq_zero.1 (hu_def ▸ hu0)`. Establish `hv'S2 : (v' : H) ∈ S`. Establish `e : v' = ((inner ℂ v v)⁻¹ * inner ℂ v v') • v`. Rewrite using `[mul_smul, ← heq, smul_smul, inv_mul_cancel₀ hvv, one_smul]`. Rewrite using `[e, Submodule.coe_smul]`.

Conclude with `S.smul_mem _ hvS`. Establish `hinf : PI.UpqRep.IsKStableOn ε σ (S ⊓ S')` using `fun g hg x hx => ⟨hS.2.1 g hg x hx.1, hS'.2.1 g hg x hx.2⟩`. Establish `hvne : (v : H) ≠ 0` using `fun h0 => hv0 (Subtype.ext h0)`. Establish `hv'ne : (v' : H) ≠ 0` using `fun h0 => hv'0 (Subtype.ext h0)`. Break down `hS.2.2.1 (S ⊓ S') inf_le_left hinf with h | h` into its components or cases.

It suffices to derive a contradiction. Establish `hm : (v' : H) ∈ S ⊓ S'` using `⟨hv'S2, hv'S⟩`. Rewrite `hm` using `[h]`. Conclude with `hv'ne ((Submodule.mem_bot ℂ).1 hm)`. Establish `hle : S ≤ S'` using `h ▸ inf_le_right`.

Break down `hS'.2.2.1 S hle hS.2.1 with h2 | h2` into its components or cases. It suffices to derive a contradiction. Establish `hm : (v : H) ∈ S` using `hvS`. Rewrite `hm` using `[h2]`. Conclude with `hvne ((Submodule.mem_bot ℂ).1 hm)`.

Conclude with `h2`.
-/
theorem lowKMultOneP_of (hM : MultAlg) (hE : KModExists) (hD : CycDense) (hO : OrthCyc) : LowKMultOneP := by
  intro N ε lam H _ _ σ hHC hDS S S' hS hS'
  obtain ⟨hcomp, -, hUR, hIR, -, -, hmin⟩ := hDS
  haveI := hcomp
  obtain ⟨D, E, hK⟩ := hE N ε H σ hUR hIR
  have hGl : GlRel E := hK.gl
  have hU : CompanionTheory.D.DSIC.KUnit ε E := by
    intro a b h x y
    rw [hK.unit a b x y]
    simp only [Formalism.REAL.sgn, if_pos h, Complex.ofReal_one, one_mul]
  have hLF : CompanionTheory.D.LK.LocFin ε E := hK.locFin
  have hIM : CompanionTheory.D.LK.IsMin ε E lam := by
    intro μ x hx hxh
    obtain ⟨T, hT⟩ := hK.ty μ x hx hxh
    exact hmin μ T hT
  obtain ⟨v, hv0, hvS, hv⟩ := hK.hw _ S hS
  obtain ⟨v', hv'0, hv'S, hv'⟩ := hK.hw _ S' hS'
  have hmult : ∀ w, KHighest ε E (lowK ε lam) w → w ∈ Cyc E v → ∃ c : ℂ, w = c • v :=
    fun w hw hwc => hM N ε lam D E hHC.1 hGl hU hLF hIM v w hv0 hv hw hwc
  have hcv : KHighest ε E (lowK ε lam) (Cas E v) := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · rw [← Module.End.mul_apply, commute_E_cas_of_glRel E hGl a a, Module.End.mul_apply, hv.1 a, map_smul]
    · rw [← Module.End.mul_apply, commute_E_cas_of_glRel E hGl a b, Module.End.mul_apply, hv.2 a b hab h, map_zero]
  have hcc : Cas E v ∈ Cyc E v := by
    refine mem_cyc.2 ⟨∑ a, ∑ b, FreeAlgebra.ι ℂ (a, b) * FreeAlgebra.ι ℂ (b, a), ?_⟩
    simp only [CompanionTheory.D.LK.ev, map_sum, map_mul, FreeAlgebra.lift_ι_apply, Formalism.REAL.Cas]
  obtain ⟨c, hc⟩ := hmult _ hcv hcc
  have hdense := hD N ε H σ D E hUR hIR hK v c hv0 hc
  set u : D := inner ℂ v v • v' - inner ℂ v v' • v with hu_def
  have hu : KHighest ε E (lowK ε lam) u := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · rw [hu_def, map_sub, map_smul, map_smul, hv'.1 a, hv.1 a, smul_sub, smul_smul, smul_smul,
        smul_smul, smul_smul, mul_comm (inner ℂ v v), mul_comm (inner ℂ v v')]
    · rw [hu_def, map_sub, map_smul, map_smul, hv'.2 a b hab h, hv.2 a b hab h, smul_zero, smul_zero, sub_zero]
  have horth0 : inner ℂ v u = 0 := by
    rw [hu_def, inner_sub_right, inner_smul_right, inner_smul_right]
    ring
  have horth := hO N ε D E (lowK ε lam) v u hGl hU hLF (fun w hwc hw => hmult w hw hwc) hu horth0
  have hsub : Submodule.map D.subtype (Cyc E v) ≤ (ℂ ∙ (u : H))ᗮ := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact (Submodule.coe_inner D m u).symm.trans (horth m hm)
  have hcl := Submodule.topologicalClosure_minimal _ hsub (Submodule.isClosed_orthogonal _)
  rw [hdense] at hcl
  have hum : (u : H) ∈ (ℂ ∙ (u : H))ᗮ := hcl Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_self_eq_zero] at hum
  have hu0 : u = 0 := Subtype.ext hum
  have hvv : inner ℂ v v ≠ 0 := inner_self_ne_zero.2 hv0
  have heq : inner ℂ v v • v' = inner ℂ v v' • v := sub_eq_zero.1 (hu_def ▸ hu0)
  have hv'S2 : (v' : H) ∈ S := by
    have e : v' = ((inner ℂ v v)⁻¹ * inner ℂ v v') • v := by
      rw [mul_smul, ← heq, smul_smul, inv_mul_cancel₀ hvv, one_smul]
    rw [e, Submodule.coe_smul]
    exact S.smul_mem _ hvS
  have hinf : PI.UpqRep.IsKStableOn ε σ (S ⊓ S') :=
    fun g hg x hx => ⟨hS.2.1 g hg x hx.1, hS'.2.1 g hg x hx.2⟩
  have hvne : (v : H) ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have hv'ne : (v' : H) ≠ 0 := fun h0 => hv'0 (Subtype.ext h0)
  rcases hS.2.2.1 (S ⊓ S') inf_le_left hinf with h | h
  · exfalso
    have hm : (v' : H) ∈ S ⊓ S' := ⟨hv'S2, hv'S⟩
    rw [h] at hm
    exact hv'ne ((Submodule.mem_bot ℂ).1 hm)
  · have hle : S ≤ S' := h ▸ inf_le_right
    rcases hS'.2.2.1 S hle hS.2.1 with h2 | h2
    · exfalso
      have hm : (v : H) ∈ S := hvS
      rw [h2] at hm
      exact hvne ((Submodule.mem_bot ℂ).1 hm)
    · exact h2

end CompanionTheory.D.LK
