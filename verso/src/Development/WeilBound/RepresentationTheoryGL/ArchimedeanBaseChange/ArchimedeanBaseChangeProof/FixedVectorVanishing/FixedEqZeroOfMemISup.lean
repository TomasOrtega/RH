import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.Loc

section Finite

variable {G X V : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hle : (⨆ i ∈ s, LinearMap.range (f i)) ≤ (⨆ i ∈ s, LinearMap.range (f i)).comap (ρ g)`. Use `iSup₂_le fun i hi => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Submodule.mem_comap, ← hf]`. Conclude with `Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨σ g x, rfl⟩)`.

Conclude with `fun y hy => hle hy`.
-/
theorem partial_stable (ρ : Representation ℂ G V) (σ : Representation ℂ G X) {ι : Type}
    (f : ι → X →ₗ[ℂ] V) (hf : ∀ i g x, f i (σ g x) = ρ g (f i x)) (s : Finset ι) (g : G) :
    ∀ y ∈ ⨆ i ∈ s, LinearMap.range (f i), ρ g y ∈ ⨆ i ∈ s, LinearMap.range (f i) := by
  have hle : (⨆ i ∈ s, LinearMap.range (f i)) ≤ (⨆ i ∈ s, LinearMap.range (f i)).comap (ρ g) := by
    refine iSup₂_le fun i hi => ?_
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_comap, ← hf]
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨σ g x, rfl⟩)
  exact fun y hy => hle hy

/- English proof (translation)
Establish `hirr` using `((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `φ hφ _`. Simplify using `using hφ`.

Consider the case `insert a s ha ih`. Introduce `φ hφ hfix`. Rewrite `hφ` using `[Finset.iSup_insert]`. Take `⟨_, ⟨x, rfl⟩, z, hz, rfl⟩` from `Submodule.mem_sup.1 hφ`. Establish `hstab` using `partial_stable ρ σ f hf s`.

Distinguish the cases in `hA : ∃ x', f a x' ∈ ⨆ i ∈ s, LinearMap.range (f i) ∧ f a x' ≠ 0`. Take `⟨x', hx'Y, hx'0⟩` from `hA`. Establish `hZ : (⨆ i ∈ s, LinearMap.range (f i)).comap (f a) = ⊤`. Break down `hirr ((⨆ i ∈ s, LinearMap.range (f i)).comap (f a)) (fun g v hv => by` into its components or cases. Rewrite `hv`, the goal using `[Submodule.mem_comap]`.

Rewrite using `[hf]`. Conclude with `hstab g _ hv) with h | h`. Establish `: x' ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f a)` using `hx'Y`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `absurd (by rw [this, map_zero]) hx'0`.

Conclude with `h`. Establish `hxY : x ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f a)` using `hZ ▸ Submodule.mem_top`. Conclude with `ih _ (add_mem hxY hz) hfix`. Use `push Not at hA`. Establish `hd : ∀ g ∈ S, f a (σ g x - x) = 0`.

Introduce `g hg`. Apply `hA` to reduce the goal to its premises. Establish `h1` using `hfix g hg`. Rewrite `h1` using `[map_add]`. Establish `h2 : ρ g (f a x) - f a x = z - ρ g z`.

Rewrite using `[sub_eq_sub_iff_add_eq_add, h1, add_comm]`. Rewrite using `[map_sub, hf, h2]`. Conclude with `sub_mem hz (hstab g z hz)`. Establish `hzfix : ∀ g ∈ S, ρ g z = z`. Introduce `g hg`.

Establish `h1` using `hfix g hg`. Establish `h2` using `hd g hg`. Rewrite `h2` using `[map_sub, sub_eq_zero, hf]`. Rewrite `h1` using `[map_add, h2]`. Conclude with `add_left_cancel h1`.

Establish `hz0 : z = 0` using `ih z hz hzfix`. Substitute `hz0` using the available equality. Break down `hirr (LinearMap.ker (f a)) (fun g v hv => by` into its components or cases. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hf, hv, map_zero]) with h | h`.

Establish `hx : x = 0` using `hX x fun g hg => by`. Establish `h3` using `hd g hg`. Rewrite `h3` using `[← LinearMap.mem_ker, h, Submodule.mem_bot, sub_eq_zero]`. Conclude with `h3`. Simplify using `[hx]`.

Establish `: x ∈ LinearMap.ker (f a)` using `h ▸ Submodule.mem_top`. Rewrite `this` using `[LinearMap.mem_ker]`. Simplify using `[this]`.
-/
theorem sum_fixed_eq_zero (ρ : Representation ℂ G V) (σ : Representation ℂ G X)
    (hσ : σ.IsIrreducible) {ι : Type} (f : ι → X →ₗ[ℂ] V)
    (hf : ∀ i g x, f i (σ g x) = ρ g (f i x)) (S : Set G)
    (hX : ∀ x, (∀ g ∈ S, σ g x = x) → x = 0) (s : Finset ι) :
    ∀ φ ∈ ⨆ i ∈ s, LinearMap.range (f i), (∀ g ∈ S, ρ g φ = φ) → φ = 0 := by
  classical
  have hirr := ((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2
  induction s using Finset.induction_on with
  | empty =>
    intro φ hφ _
    simpa using hφ
  | insert a s ha ih =>
    intro φ hφ hfix
    rw [Finset.iSup_insert] at hφ
    obtain ⟨_, ⟨x, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hφ
    have hstab := partial_stable ρ σ f hf s
    by_cases hA : ∃ x', f a x' ∈ ⨆ i ∈ s, LinearMap.range (f i) ∧ f a x' ≠ 0
    · obtain ⟨x', hx'Y, hx'0⟩ := hA
      have hZ : (⨆ i ∈ s, LinearMap.range (f i)).comap (f a) = ⊤ := by
        rcases hirr ((⨆ i ∈ s, LinearMap.range (f i)).comap (f a)) (fun g v hv => by
          rw [Submodule.mem_comap] at hv ⊢
          rw [hf]
          exact hstab g _ hv) with h | h
        · have : x' ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f a) := hx'Y
          rw [h, Submodule.mem_bot] at this
          exact absurd (by rw [this, map_zero]) hx'0
        · exact h
      have hxY : x ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f a) := hZ ▸ Submodule.mem_top
      exact ih _ (add_mem hxY hz) hfix
    · push Not at hA
      have hd : ∀ g ∈ S, f a (σ g x - x) = 0 := by
        intro g hg
        apply hA
        have h1 := hfix g hg
        rw [map_add] at h1
        have h2 : ρ g (f a x) - f a x = z - ρ g z := by
          rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
        rw [map_sub, hf, h2]
        exact sub_mem hz (hstab g z hz)
      have hzfix : ∀ g ∈ S, ρ g z = z := by
        intro g hg
        have h1 := hfix g hg
        have h2 := hd g hg
        rw [map_sub, sub_eq_zero, hf] at h2
        rw [map_add, h2] at h1
        exact add_left_cancel h1
      have hz0 : z = 0 := ih z hz hzfix
      subst hz0
      rcases hirr (LinearMap.ker (f a)) (fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hf, hv, map_zero]) with h | h
      · have hx : x = 0 := hX x fun g hg => by
          have h3 := hd g hg
          rw [← LinearMap.mem_ker, h, Submodule.mem_bot, sub_eq_zero] at h3
          exact h3
        simp [hx]
      · have : x ∈ LinearMap.ker (f a) := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker] at this
        simp [this]

/- English proof (translation)
Take `⟨s, hs⟩` from `Submodule.exists_finset_of_mem_iSup _ hφ`. Conclude with `sum_fixed_eq_zero ρ σ hσ f hf S hX s φ hs hfix`.
-/
theorem fixed_eq_zero_of_mem_iSup (ρ : Representation ℂ G V) (σ : Representation ℂ G X)
    (hσ : σ.IsIrreducible) {ι : Type} (f : ι → X →ₗ[ℂ] V)
    (hf : ∀ i g x, f i (σ g x) = ρ g (f i x)) (S : Set G)
    (hX : ∀ x, (∀ g ∈ S, σ g x = x) → x = 0) (φ : V)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) (hfix : ∀ g ∈ S, ρ g φ = φ) : φ = 0 := by
  obtain ⟨s, hs⟩ := Submodule.exists_finset_of_mem_iSup _ hφ
  exact sum_fixed_eq_zero ρ σ hσ f hf S hX s φ hs hfix

end Finite

/- English proof (translation)
Set `p : locU n w →* GL (Fin n) (w.adicCompletion E)` to `(cLoc w).comp (locU n w).subtype`. Take `⟨e, he⟩` from `GlobalTheory.locU_equiv_GL E n w hw`. Establish `hp : Function.Surjective p` using `fun g => ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩`. Take `⟨φ, hφ, hφ0, hφK⟩` from `hu`. Take `⟨hσirr, f, hf0, hfm, hf⟩` from `hc`.

Assume the negation of the conclusion as `hns`. Establish `hfix : ∀ v, (∀ k ∈ GlobalTheory.LFun.KGL w n, P.ρ k v = v) → v = 0` using `fun v hv => by`. Assume the negation of the conclusion as `hv0`. Conclude with `hns ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩)`. Set `Ψ : GlobalTheory.DefU.AutSub E n` to `⟨π, hπ⟩`.

Set `τ : Representation ℂ (locU n w) P.V` to `P.ρ.comp p`. Establish `hirr : τ.IsIrreducible`. Take `⟨h0, h1⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr`. Use `(GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hp g`.

Conclude with `hY x v hv`. Set `F : τ.IntertwiningMap (Ψ.rep.comp (locU n w).subtype)` to `⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩`. Establish `hF0 : F ≠ 0` using `fun h => hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))`. Take `⟨r, -, -, hr⟩` from `GlobalTheory.DefU.LocRet.exists_ret E n w`. Establish `htop : (⨆ i : τ.IntertwiningMap (Ψ.rep.comp (locU n w).subtype), LinearMap.range i.toLinearMap) = ⊤` using `(GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V P.V P.V Ψ.rep (locU n w).subtype τ τ Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1`.

Establish `key` using `fixed_eq_zero_of_mem_iSup (Ψ.rep.comp (locU n w).subtype) τ hirr (fun i : τ.IntertwiningMap (Ψ.rep.comp (locU n w).subtype) => i.toLinearMap) (fun i g x => Representation.IntertwiningMap.isIntertwining _ _ i g x) (((GlobalTheory.LFun.KGL w n).comap p : Subgroup (locU n w)) : Set …`. Take `⟨x, rfl⟩` from `hp k`. Conclude with `hv x hk)`. Use the proof step `⟨φ, hφ⟩ (htop ▸ Submodule.mem_top) (fun k hk => Subtype.ext (hφK k.1 k.2 hk))`. Conclude with `hφ0 (congrArg Subtype.val key)`.
-/
theorem split_spherical2 {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    (P : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E)))
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ) (hu : IsUnramU π w) :
    GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w n) := by
  let p : locU n w →* GL (Fin n) (w.adicCompletion E) := (cLoc w).comp (locU n w).subtype
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  have hp : Function.Surjective p := fun g => ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hc
  by_contra hns

  have hfix : ∀ v, (∀ k ∈ GlobalTheory.LFun.KGL w n, P.ρ k v = v) → v = 0 := fun v hv => by
    by_contra hv0
    exact hns ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩)
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  let τ : Representation ℂ (locU n w) P.V := P.ρ.comp p

  have hirr : τ.IsIrreducible := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : τ.IntertwiningMap (Ψ.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop : (⨆ i : τ.IntertwiningMap (Ψ.rep.comp (locU n w).subtype), LinearMap.range i.toLinearMap) = ⊤ :=
    (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V P.V P.V Ψ.rep (locU n w).subtype τ τ
      Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  have key := fixed_eq_zero_of_mem_iSup (Ψ.rep.comp (locU n w).subtype) τ hirr
    (fun i : τ.IntertwiningMap (Ψ.rep.comp (locU n w).subtype) => i.toLinearMap)
    (fun i g x => Representation.IntertwiningMap.isIntertwining _ _ i g x)
    (((GlobalTheory.LFun.KGL w n).comap p : Subgroup (locU n w)) : Set (locU n w))
    (fun v hv => hfix v fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk)
    ⟨φ, hφ⟩ (htop ▸ Submodule.mem_top) (fun k hk => Subtype.ext (hφK k.1 k.2 hk))
  exact hφ0 (congrArg Subtype.val key)

end PositivityTheory.Rg.BcB.Loc
