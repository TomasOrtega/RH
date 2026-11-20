import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometryStatement

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.SeenIso

section General

variable {K U V W : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/- English proof (translation)
Take `⟨g, hg⟩` from `(X.mkQ ∘ₗ ι).exists_leftInverse_of_injective (by`. Rewrite using `[eq_bot_iff]`. Introduce `w hw`. Conclude with `hWX w ((Submodule.Quotient.mk_eq_zero X).1 hw))`. Set `p : V →ₗ[K] W` to `g ∘ₗ X.mkQ`.

Establish `hpι : ∀ w, p (ι w) = w` using `fun w => LinearMap.congr_fun hg w`. Establish `hpX : ∀ u ∈ X, p u = 0` using `fun u hu => by`. Establish `: X.mkQ u = 0` using `(Submodule.Quotient.mk_eq_zero X).2 hu`. Simplify using `only [p, LinearMap.comp_apply, this, map_zero]`. Establish `hF : ∀ x : H, (x : V) - ι (p x) ∈ X` using `fun x => by`.

Take `⟨w, hw⟩` from `hsp x x.2`. Use `hpX _ hw` as an intermediate fact. Rewrite `this` using `[map_sub, hpι, sub_eq_zero]`. Rewrite using `[this]` and apply the resulting hypothesis. Use `⟨p ∘ₗ H.subtype, ?_, fun x y => ?_, hF⟩` and prove the remaining obligations.

Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`. Establish `h1 : p x = 0` using `hx`. Establish `h2` using `hF x`. Rewrite `h2` using `[h1, map_zero, sub_zero]`.

Establish `h3 : (x : V) ∈ H ⊓ X` using `⟨x.2, h2⟩`. Rewrite `h3` using `[hHX]`. Conclude with `Subtype.ext h3`. Express the relevant statement in the definitionally equal form `h0 (p x) (p y) = _`. Establish `a` using `hXH _ (hF x) _ y.2`.

Establish `b` using `hXι _ (hF y) (p x)`. Establish `c : h (ι (p x)) ((y : V) - ι (p y)) = 0` using `by rw [← hs.eq, b, map_zero]`. Rewrite `a` using `[map_sub, LinearMap.sub_apply, sub_eq_zero]`. Rewrite `c` using `[map_sub, sub_eq_zero]`. Rewrite using `[a, c, hι]`.
-/
theorem exists_proj [StarRing K] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {h0 : W →ₗ⋆[K] W →ₗ[K] K}
    (ι : W →ₗ[K] V) (hι : ∀ x y, h (ι x) (ι y) = h0 x y) (X H : Submodule K V)
    (hWX : ∀ w, ι w ∈ X → w = 0)
    (hXι : ∀ x ∈ X, ∀ w, h x (ι w) = 0) (hXH : ∀ x ∈ X, ∀ v ∈ H, h x v = 0)
    (hsp : ∀ v ∈ H, ∃ w, v - ι w ∈ X) (hHX : H ⊓ X = ⊥) :
    ∃ π : H →ₗ[K] W, Function.Injective π ∧ (∀ x y, h0 (π x) (π y) = h x y) ∧
      ∀ x : H, (x : V) - ι (π x) ∈ X := by
  obtain ⟨g, hg⟩ := (X.mkQ ∘ₗ ι).exists_leftInverse_of_injective (by
    rw [eq_bot_iff]
    intro w hw
    exact hWX w ((Submodule.Quotient.mk_eq_zero X).1 hw))
  let p : V →ₗ[K] W := g ∘ₗ X.mkQ
  have hpι : ∀ w, p (ι w) = w := fun w => LinearMap.congr_fun hg w
  have hpX : ∀ u ∈ X, p u = 0 := fun u hu => by
    have : X.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero X).2 hu
    simp only [p, LinearMap.comp_apply, this, map_zero]
  have hF : ∀ x : H, (x : V) - ι (p x) ∈ X := fun x => by
    obtain ⟨w, hw⟩ := hsp x x.2
    have := hpX _ hw
    rw [map_sub, hpι, sub_eq_zero] at this
    rwa [this]
  refine ⟨p ∘ₗ H.subtype, ?_, fun x y => ?_, hF⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have h1 : p x = 0 := hx
    have h2 := hF x
    rw [h1, map_zero, sub_zero] at h2
    have h3 : (x : V) ∈ H ⊓ X := ⟨x.2, h2⟩
    rw [hHX] at h3
    exact Subtype.ext h3
  · change h0 (p x) (p y) = _
    have a := hXH _ (hF x) _ y.2
    have b := hXι _ (hF y) (p x)
    have c : h (ι (p x)) ((y : V) - ι (p y)) = 0 := by rw [← hs.eq, b, map_zero]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at a
    rw [map_sub, sub_eq_zero] at c
    rw [a, c, hι]

variable [NumberField K] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `: ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = i '' (N : Set U)` using `rfl`. Rewrite using `[this, ← Submodule.map_span]`. Conclude with `(Submodule.equivMapOfInjective i hi _).finrank_eq.symm`.
-/
theorem finrank_span_map (i : U →ₗ[K] V) (hi : Function.Injective i) (N : Submodule (𝓞 K) U) :
    finrank K (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      finrank K (Submodule.span K (N : Set U)) := by
  have : ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = i '' (N : Set U) := rfl
  rw [this, ← Submodule.map_span]
  exact (Submodule.equivMapOfInjective i hi _).finrank_eq.symm

/- English proof (translation)
Use `AddSubgroup.relIndex_map_map_of_injective (f := i.toAddMonoidHom) B.toAddSubgroup A.toAddSubgroup hi` as an intermediate fact. Conclude with `this`.
-/
theorem card_quot_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    Nat.card (↥(A.map (i.restrictScalars (𝓞 K))) ⧸
      (B.map (i.restrictScalars (𝓞 K))).comap (A.map (i.restrictScalars (𝓞 K))).subtype) =
      Nat.card (A ⧸ B.comap A.subtype) := by
  have := AddSubgroup.relIndex_map_map_of_injective (f := i.toAddMonoidHom) B.toAddSubgroup A.toAddSubgroup hi
  exact this

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D T F H hW hH hHX N N' hN hN'`. Establish `hm : 0 < D.R.m` using `lt_of_lt_of_le (by norm_num) D.R.two_le_m`. Establish `hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y` using `D.sp.iXY_isom 0 hm`. Establish `hXι : ∀ x ∈ Xsp F, ∀ w, (hS D).hT x (D.sp.iXY 0 w) = 0` using `fun x hx w => (Formalism.MainNotions.mem_orth_iff _ _).1 (hW.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)) x (Submodule.mem_sup_left hx)`. Establish `hWX : ∀ w, D.sp.iXY 0 w ∈ Xsp F → w = 0` using `fun w hw => (D.sp.X 0).nondeg.1 w fun y => by rw [← hiso]; exact hXι _ hw y`.

Take `⟨π, hinj, hπ, hF⟩` from `exists_proj (hS D).herm (D.sp.iXY 0) hiso (Xsp F) H hWX hXι (fun x hx v hv => (Formalism.MainNotions.mem_orth_iff _ _).1 (hH hv) x (Submodule.mem_sup_left hx)) (fun v hv => by`. Take `⟨_, ⟨w, rfl⟩, x, hx, rfl⟩` from `Submodule.mem_sup.1 (hW.1.ge (hH hv))`. Conclude with `⟨w, by simpa using hx⟩) hHX`. Establish `key : ∀ M : LatV D, M ≤ toO (hS D) H → ∃ M₀ : Submodule (𝓞 D.host.E) H, M = M₀.map (H.subtype.restrictScalars (𝓞 D.host.E)) ∧ seen D F M = M₀.map (π.restrictScalars (𝓞 D.host.E))`. Introduce `M hM`.

Use `⟨M.comap (H.subtype.restrictScalars (𝓞 D.host.E)), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨⟨x, hM hx⟩, hx, rfl⟩`.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`.

Take `⟨l, hl, x, hx, e⟩` from `Submodule.mem_sup.1 hw`. Use `⟨⟨l, hM hl⟩, hl, ?_⟩` and prove the remaining obligations. Establish `e' : l + x = D.sp.iXY 0 w` using `e`. Establish `h1` using `(Xsp F).add_mem (hF ⟨l, hM hl⟩) hx`. Establish `h2 : w - π ⟨l, hM hl⟩ = 0` using `hWX _ (by`.

Rewrite using `[map_sub, ← e']`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use the proof step `abel)`. Conclude with `(sub_eq_zero.1 h2).symm`. Introduce and unpack `⟨y, hy, rfl⟩`.

Use `Submodule.mem_sup.2 ⟨y, hy, _, (Xsp F).neg_mem (hF y), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = D.sp.iXY 0 (π y)`. Normalize the expressions using the abelian group laws. Take `⟨A, rfl, a⟩` from `key N hN`. Take `⟨B, rfl, b⟩` from `key N' hN'`.

Rewrite using `[a, b]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `exact (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ π hinj hπ A).trans (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ H.subtype H.injective_subtype (fun _ _ => rfl) A).symm`. Conclude with `(finrank_span_map π hinj A).trans (finrank_span_map H.subtype H.injective_subtype A).symm`. Conclude with `(card_quot_map π hinj A B).trans (card_quot_map H.subtype H.injective_subtype A B).symm`.
-/
theorem main : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (H : Submodule D.host.E (hS D).V), WHyp D F (Wsp D) → H ≤ orth (hS D) (Xplus F) → H ⊓ Xsp F = ⊥ → ∀ N N' : LatV D, N ≤ toO (hS D) H → N' ≤ toO (hS D) H → detW D (seen D F N) = latDet (hS D) N ∧ rkW D (seen D F N) = finrank D.host.E (spanE (hS D) N) ∧ idxW D (seen D F N) (seen D F N') = idx (hS D) N N' := by
  intro D T F H hW hH hHX N N' hN hN'
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y := D.sp.iXY_isom 0 hm
  have hXι : ∀ x ∈ Xsp F, ∀ w, (hS D).hT x (D.sp.iXY 0 w) = 0 := fun x hx w =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 (hW.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)) x (Submodule.mem_sup_left hx)
  have hWX : ∀ w, D.sp.iXY 0 w ∈ Xsp F → w = 0 := fun w hw =>
    (D.sp.X 0).nondeg.1 w fun y => by rw [← hiso]; exact hXι _ hw y
  obtain ⟨π, hinj, hπ, hF⟩ := exists_proj (hS D).herm (D.sp.iXY 0) hiso (Xsp F) H hWX hXι
    (fun x hx v hv => (Formalism.MainNotions.mem_orth_iff _ _).1 (hH hv) x (Submodule.mem_sup_left hx))
    (fun v hv => by
      obtain ⟨_, ⟨w, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 (hW.1.ge (hH hv))
      exact ⟨w, by simpa using hx⟩) hHX
  have key : ∀ M : LatV D, M ≤ toO (hS D) H → ∃ M₀ : Submodule (𝓞 D.host.E) H,
      M = M₀.map (H.subtype.restrictScalars (𝓞 D.host.E)) ∧
        seen D F M = M₀.map (π.restrictScalars (𝓞 D.host.E)) := by
    intro M hM
    refine ⟨M.comap (H.subtype.restrictScalars (𝓞 D.host.E)), ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        exact ⟨⟨x, hM hx⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
    · ext w
      constructor
      · intro hw
        obtain ⟨l, hl, x, hx, e⟩ := Submodule.mem_sup.1 hw
        refine ⟨⟨l, hM hl⟩, hl, ?_⟩
        have e' : l + x = D.sp.iXY 0 w := e
        have h1 := (Xsp F).add_mem (hF ⟨l, hM hl⟩) hx
        have h2 : w - π ⟨l, hM hl⟩ = 0 := hWX _ (by
          rw [map_sub, ← e']
          convert h1 using 1
          abel)
        exact (sub_eq_zero.1 h2).symm
      · rintro ⟨y, hy, rfl⟩
        refine Submodule.mem_sup.2 ⟨y, hy, _, (Xsp F).neg_mem (hF y), ?_⟩
        change _ = D.sp.iXY 0 (π y)
        abel
  obtain ⟨A, rfl, a⟩ := key N hN
  obtain ⟨B, rfl, b⟩ := key N' hN'
  rw [a, b]
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ π hinj hπ A).trans
      (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ H.subtype H.injective_subtype (fun _ _ => rfl) A).symm
  · exact (finrank_span_map π hinj A).trans (finrank_span_map H.subtype H.injective_subtype A).symm
  · exact (card_quot_map π hinj A B).trans (card_quot_map H.subtype H.injective_subtype A B).symm

end GlobalTheory.LoopC.SeenIso
