import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

/- English proof (translation)
Introduce `hE E _ _ _ n U U' C sU sU' sC h0 hne hle hs`. Establish `sup : ∀ T : Module.End ℂ (cuspForms E n), (∀ φ ∈ U, T φ ∈ U) → (∀ φ ∈ U', T φ ∈ U') → ∀ φ ∈ U ⊔ U', T φ ∈ U ⊔ U'` using `fun T h h' φ hφ => by`. Take `⟨u, hu, x, hx, rfl⟩` from `Submodule.mem_sup.1 hφ`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (h u hu) (h' x hx)`.

Use `⟨C ⊓ (U ⊔ U'), inf_le_left, fun e => hne (eq_bot_iff.2 fun x hx => ?_), ⟨fun X φ h => ⟨sC.ρ X φ h.1, sup _ (sU.ρ X) (sU'.ρ X) φ h.2⟩, fun X φ h => ⟨sC.σ X φ h.1, sup _ (sU.σ X) (sU'.σ X) φ h.2⟩, fun X φ h => ⟨sC.τ X φ h.1, sup _ (sU.τ X) (sU'.τ X) φ h.2⟩⟩, hs.mono fun w ⟨B, h1, h …` and prove the remaining obligations. Take `⟨u, hu, c, hc, e'⟩` from `Submodule.mem_sup.1 (hle hx)`. Establish `h1 : c ∈ C ⊓ (U ⊔ U')` using `⟨hc, by`. Rewrite using `[show c = -u + x by rw [← e']; abel]`. Conclude with `Submodule.add_mem_sup (U.neg_mem hu) hx⟩`.

Rewrite `h1` using `[e, Submodule.mem_bot]`. Rewrite `e'` using `[h1, add_zero]`. Rewrite using `[← h0]`. Conclude with `⟨e' ▸ hu, hx⟩`. Take `⟨u, hu, x, hx, rfl⟩` from `Submodule.mem_sup.1 hc.2`.

Establish `ev : ∀ (φ : cuspForms E n) k g, (finRepCusp E n k φ).1 g = φ.1 (g * finGL E n k)` using `fun φ k g => by`. Rewrite using `[← Fb.finEmb_eq]`. Both sides reduce to the same expression. Establish `key : ∀ k ∈ GlobalTheory.LFun.KGL w n, finRepCusp E n (locGL E n w k) u = u ∧ finRepCusp E n (locGL E n w k) x = x`. Introduce `k hk`.

Establish `e : finRepCusp E n (locGL E n w k) (u + x) = u + x` using `Subtype.ext (funext fun g => (ev _ _ g).trans (hK g k hk))`. Rewrite `e` using `[map_add]`. Establish `e2 : finRepCusp E n (locGL E n w k) u - u = x - finRepCusp E n (locGL E n w k) x`. Rewrite using `[sub_eq_sub_iff_add_eq_add, e, add_comm]`. Establish `m : finRepCusp E n (locGL E n w k) u - u ∈ U ⊓ U'` using `⟨U.sub_mem (sU.τ _ u hu) hu, e2 ▸ U'.sub_mem hx (sU'.τ _ x hx)⟩`.

Rewrite `m` using `[h0, Submodule.mem_bot]`. Conclude with `⟨sub_eq_zero.1 m, (sub_eq_zero.1 (e2.symm.trans m)).symm⟩`. Establish `a` using `h1 (-u) (U.neg_mem hu) fun g k hk => by`. Rewrite using `[← ev, map_neg, (key k hk).1]`. Establish `b` using `h2 x hx fun g k hk => by rw [← ev, (key k hk).2]`.

Establish `e : (u + x).1 = x.1 - (-u).1`. Rewrite using `[← Submodule.coe_sub, sub_neg_eq_add, add_comm]`. Rewrite using `[e]`. Conclude with `(hE E n w B _ b).2.2 _ a`.
-/
theorem UpperTheory.V.Af.StrongMultiplicityOne.proj :
    UpperTheory.V.Af.StrongMultiplicityOne.EigMap → UpperTheory.V.Af.StrongMultiplicityOne.Proj := by
  intro hE E _ _ _ n U U' C sU sU' sC h0 hne hle hs
  have sup : ∀ T : Module.End ℂ (cuspForms E n), (∀ φ ∈ U, T φ ∈ U) → (∀ φ ∈ U', T φ ∈ U') →
      ∀ φ ∈ U ⊔ U', T φ ∈ U ⊔ U' := fun T h h' φ hφ => by
    obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.1 hφ
    rw [map_add]
    exact Submodule.add_mem_sup (h u hu) (h' x hx)
  refine ⟨C ⊓ (U ⊔ U'), inf_le_left, fun e => hne (eq_bot_iff.2 fun x hx => ?_),
    ⟨fun X φ h => ⟨sC.ρ X φ h.1, sup _ (sU.ρ X) (sU'.ρ X) φ h.2⟩,
      fun X φ h => ⟨sC.σ X φ h.1, sup _ (sU.σ X) (sU'.σ X) φ h.2⟩,
      fun X φ h => ⟨sC.τ X φ h.1, sup _ (sU.τ X) (sU'.τ X) φ h.2⟩⟩,
    hs.mono fun w ⟨B, h1, h2⟩ => ⟨B, h1, fun c hc hK => ?_⟩⟩
  · obtain ⟨u, hu, c, hc, e'⟩ := Submodule.mem_sup.1 (hle hx)
    have h1 : c ∈ C ⊓ (U ⊔ U') := ⟨hc, by
      rw [show c = -u + x by rw [← e']; abel]
      exact Submodule.add_mem_sup (U.neg_mem hu) hx⟩
    rw [e, Submodule.mem_bot] at h1
    rw [h1, add_zero] at e'
    rw [← h0]
    exact ⟨e' ▸ hu, hx⟩
  · obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.1 hc.2
    have ev : ∀ (φ : cuspForms E n) k g, (finRepCusp E n k φ).1 g = φ.1 (g * finGL E n k) := fun φ k g => by
      rw [← Fb.finEmb_eq]
      rfl
    have key : ∀ k ∈ GlobalTheory.LFun.KGL w n, finRepCusp E n (locGL E n w k) u = u ∧ finRepCusp E n (locGL E n w k) x = x := by
      intro k hk
      have e : finRepCusp E n (locGL E n w k) (u + x) = u + x :=
        Subtype.ext (funext fun g => (ev _ _ g).trans (hK g k hk))
      rw [map_add] at e
      have e2 : finRepCusp E n (locGL E n w k) u - u = x - finRepCusp E n (locGL E n w k) x := by
        rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
      have m : finRepCusp E n (locGL E n w k) u - u ∈ U ⊓ U' :=
        ⟨U.sub_mem (sU.τ _ u hu) hu, e2 ▸ U'.sub_mem hx (sU'.τ _ x hx)⟩
      rw [h0, Submodule.mem_bot] at m
      exact ⟨sub_eq_zero.1 m, (sub_eq_zero.1 (e2.symm.trans m)).symm⟩
    have a := h1 (-u) (U.neg_mem hu) fun g k hk => by
      rw [← ev, map_neg, (key k hk).1]
    have b := h2 x hx fun g k hk => by rw [← ev, (key k hk).2]
    have e : (u + x).1 = x.1 - (-u).1 := by
      rw [← Submodule.coe_sub, sub_neg_eq_add, add_comm]
    rw [e]
    exact (hE E n w B _ b).2.2 _ a
