import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearLiftBijectiveLocalization

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.HodgeSubsheaf

open GlobalTheory.Twist

/- English proof (translation)
Set `sec : ∀ U : T.Opens, Submodule Γ(T, U) Γ(H, U)` to `fun U => { carrier := {s | ∀ (V : T.Opens) (hV : IsAffineOpen V) (h : V ≤ U), resM H h s ∈ P V hV} add_mem' := fun ha hb V hV h => by`. Rewrite using `[map_add]`. Conclude with `add_mem (ha V hV h) (hb V hV h)`. Use the proof step `zero_mem' := fun V hV h => by rw [map_zero]; exact zero_mem _`. Use the proof step `smul_mem' := fun r s hs V hV h => by`.

Rewrite using `[resM_smul]`. Conclude with `Submodule.smul_mem _ _ (hs V hV h) }`. Establish `hsec : ∀ (U : T.Opens) (s : Γ(H, U)), s ∈ sec U ↔ ∀ (V : T.Opens) (hV : IsAffineOpen V) (h : V ≤ U), resM H h s ∈ P V hV` using `fun _ _ => Iff.rfl`. Use `⟨⟨sec, fun {V W} h {s} hs => (hsec _ _).2 fun V' hV' h' => ?_, fun {U} {s} hs => (hsec _ _).2 fun V hV h => ?_⟩, fun V hV s => ⟨fun hs => ?_, fun hs => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[resM_resM]`.

Conclude with `(hsec _ _).1 hs V' hV' _`. Set `J : Ideal Γ(T, V)` to `(P V hV).comap (LinearMap.toSpanSingleton Γ(T, V) Γ(H, V) (resM H h s))`. Establish `hJ : ∀ a : Γ(T, V), a ∈ J ↔ a • resM H h s ∈ P V hV` using `fun a => Iff.rfl`. Set `S : Set Γ(T, V)` to `{f | ∃ n : ℕ, f ^ n • resM H h s ∈ P V hV}`. Establish `hS : V ≤ ⨆ f : S, T.basicOpen f.1`.

Introduce `y hy`. Take `⟨W, hWU, hyW, hW⟩` from `hs y (h hy)`. Take `⟨f, hfle, hyf⟩` from `hV.exists_basicOpen_le (V := W) ⟨y, hyW⟩ hy`. Establish `h0` using `(hsec _ _).1 hW _ (hV.basicOpen f) hfle`. Rewrite `h0` using `[resM_resM]`.

Take `⟨n, hn⟩` from `hloc V hV f (resM H h s) (by rw [resM_resM]; exact h0)`. Rewrite using `[TopologicalSpace.Opens.mem_iSup]`. Conclude with `⟨⟨f, n, hn⟩, hyf⟩`. Establish `hspan : Ideal.span S = ⊤` using `(hV.self_le_iSup_basicOpen_iff).mp hS`. Establish `hrad : J.radical = ⊤`.

Rewrite using `[eq_top_iff, ← hspan, Ideal.span_le]`. Introduce and unpack `f ⟨n, hn⟩`. Conclude with `⟨n, (hJ _).mpr hn⟩`. Rewrite `hrad` using `[Ideal.radical_eq_top]`. Establish `h1 : (1 : Γ(T, V)) ∈ J` using `by rw [hrad]; trivial`.

Simplify using `using (hJ 1).mp h1`. Simplify using `using (hsec _ _).1 hs V hV le_rfl`. Conclude with `(hsec _ _).2 fun W hW h => hres V W hV hW h s hs`.
-/
theorem exists_sub_of_affine {T : Scheme.{0}} (H : T.Modules)
    (P : ∀ (V : T.Opens), IsAffineOpen V → Submodule Γ(T, V) Γ(H, V))
    (hres : ∀ (V W : T.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V) (s : Γ(H, V)),
      s ∈ P V hV → resM H h s ∈ P W hW)
    (hloc : ∀ (V : T.Opens) (hV : IsAffineOpen V) (f : Γ(T, V)) (s : Γ(H, V)),
      resM H (T.basicOpen_le f) s ∈ P _ (hV.basicOpen f) → ∃ n : ℕ, f ^ n • s ∈ P V hV) :
    ∃ F : GlobalTheory.VB.Sub H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ s ∈ P V hV := by
  let sec : ∀ U : T.Opens, Submodule Γ(T, U) Γ(H, U) := fun U =>
    { carrier := {s | ∀ (V : T.Opens) (hV : IsAffineOpen V) (h : V ≤ U), resM H h s ∈ P V hV}
      add_mem' := fun ha hb V hV h => by
        rw [map_add]; exact add_mem (ha V hV h) (hb V hV h)
      zero_mem' := fun V hV h => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun r s hs V hV h => by
        rw [resM_smul]; exact Submodule.smul_mem _ _ (hs V hV h) }
  have hsec : ∀ (U : T.Opens) (s : Γ(H, U)), s ∈ sec U ↔
      ∀ (V : T.Opens) (hV : IsAffineOpen V) (h : V ≤ U), resM H h s ∈ P V hV := fun _ _ => Iff.rfl
  refine ⟨⟨sec, fun {V W} h {s} hs => (hsec _ _).2 fun V' hV' h' => ?_,
    fun {U} {s} hs => (hsec _ _).2 fun V hV h => ?_⟩, fun V hV s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rw [resM_resM]; exact (hsec _ _).1 hs V' hV' _
  · let J : Ideal Γ(T, V) :=
      (P V hV).comap (LinearMap.toSpanSingleton Γ(T, V) Γ(H, V) (resM H h s))
    have hJ : ∀ a : Γ(T, V), a ∈ J ↔ a • resM H h s ∈ P V hV := fun a => Iff.rfl
    let S : Set Γ(T, V) := {f | ∃ n : ℕ, f ^ n • resM H h s ∈ P V hV}
    have hS : V ≤ ⨆ f : S, T.basicOpen f.1 := by
      intro y hy
      obtain ⟨W, hWU, hyW, hW⟩ := hs y (h hy)
      obtain ⟨f, hfle, hyf⟩ := hV.exists_basicOpen_le (V := W) ⟨y, hyW⟩ hy
      have h0 := (hsec _ _).1 hW _ (hV.basicOpen f) hfle
      rw [resM_resM] at h0
      obtain ⟨n, hn⟩ := hloc V hV f (resM H h s) (by rw [resM_resM]; exact h0)
      rw [TopologicalSpace.Opens.mem_iSup]
      exact ⟨⟨f, n, hn⟩, hyf⟩
    have hspan : Ideal.span S = ⊤ := (hV.self_le_iSup_basicOpen_iff).mp hS
    have hrad : J.radical = ⊤ := by
      rw [eq_top_iff, ← hspan, Ideal.span_le]
      rintro f ⟨n, hn⟩
      exact ⟨n, (hJ _).mpr hn⟩
    rw [Ideal.radical_eq_top] at hrad
    have h1 : (1 : Γ(T, V)) ∈ J := by rw [hrad]; trivial
    simpa using (hJ 1).mp h1
  · simpa using (hsec _ _).1 hs V hV le_rfl
  · exact (hsec _ _).2 fun W hW h => hres V W hV hW h s hs

/- English proof (translation)
Establish `key : ∀ m' ∈ Submodule.span R' (ρ '' N), ∃ (n : ℕ) (y : M), y ∈ N ∧ algebraMap R R' f ^ n • m' = ρ y`. Introduce `m' hm'`. Proceed by induction on `hm' using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨y, hy, rfl⟩` from `hz`.

Conclude with `⟨0, y, hy, by simp⟩`. Consider the case `zero => exact ⟨0, 0, zero_mem _, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨n, y, hy, e⟩` from `ha`. Take `⟨k, z, hz, e'⟩` from `hb`.

Use `⟨n + k, f ^ k • y + f ^ n • z, add_mem (N.smul_mem _ hy) (N.smul_mem _ hz), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smulₛₗ, map_smulₛₗ, ← e, ← e', smul_add, map_pow, map_pow, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm k n]`. Consider the case `smul c a _ ha`. Take `⟨n, y, hy, e⟩` from `ha`. Take `⟨⟨r, ⟨_, k, rfl⟩⟩, hr⟩` from `IsLocalization.surj (Submonoid.powers f) c`.

Use `⟨n + k, r • y, N.smul_mem _ hy, ?_⟩` and prove the remaining obligations. Simplify using `only [map_pow] at hr`. Rewrite using `[map_smulₛₗ, ← e, ← hr, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨n, y, hy, e⟩` from `key _ hx`. Take `⟨k, hk⟩` from `(GlobalTheory.DeRham.localisation_of_liftSemi_bijective f ρ hρ).2 (f ^ n • x - y) (by rw [map_sub, map_smulₛₗ, map_pow, e, sub_self])`. Use `⟨k + n, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[smul_sub, sub_eq_zero, smul_smul, ← pow_add]`. Rewrite using `[hk]`.

Conclude with `N.smul_mem _ hy`.
-/
theorem exists_pow_smul_mem {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    [IsLocalization.Away f R'] {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R' M'] (ρ : M →ₛₗ[algebraMap R R'] M') (hρ : Function.Bijective (liftSemi ρ))
    (N : Submodule R M) (x : M) (hx : ρ x ∈ Submodule.span R' (ρ '' N)) :
    ∃ n : ℕ, f ^ n • x ∈ N := by
  have key : ∀ m' ∈ Submodule.span R' (ρ '' N), ∃ (n : ℕ) (y : M), y ∈ N ∧
      algebraMap R R' f ^ n • m' = ρ y := by
    intro m' hm'
    induction hm' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨0, y, hy, by simp⟩
    | zero => exact ⟨0, 0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨n, y, hy, e⟩ := ha
      obtain ⟨k, z, hz, e'⟩ := hb
      refine ⟨n + k, f ^ k • y + f ^ n • z, add_mem (N.smul_mem _ hy) (N.smul_mem _ hz), ?_⟩
      rw [map_add, map_smulₛₗ, map_smulₛₗ, ← e, ← e', smul_add, map_pow, map_pow, smul_smul,
        smul_smul, ← pow_add, ← pow_add, add_comm k n]
    | smul c a _ ha =>
      obtain ⟨n, y, hy, e⟩ := ha
      obtain ⟨⟨r, ⟨_, k, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers f) c
      refine ⟨n + k, r • y, N.smul_mem _ hy, ?_⟩
      simp only [map_pow] at hr
      rw [map_smulₛₗ, ← e, ← hr, smul_smul, smul_smul]
      congr 1
      ring
  obtain ⟨n, y, hy, e⟩ := key _ hx
  obtain ⟨k, hk⟩ := (GlobalTheory.DeRham.localisation_of_liftSemi_bijective f ρ hρ).2 (f ^ n • x - y)
    (by rw [map_sub, map_smulₛₗ, map_pow, e, sub_self])
  refine ⟨k + n, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hk
  rw [hk]
  exact N.smul_mem _ hy

/- English proof (translation)
Introduce `hP T A _ g hA hg H e he`. Establish `hBC` using `hP.p5.2.2.1`. Use `exists_sub_of_affine H (fun V hV => (PrimitiveSubmodule (onAff A hV)).comap (e V hV).toLinearMap) ?_ ?_` and prove the remaining obligations. Introduce `V W hV hW h s hs`. Use `letI := resAlg h`.

Take `⟨φ, hφ, hφ'⟩` from `VB.exists_transition A hV hW h`. Express the relevant statement in the definitionally equal form `e W hW _ ∈ PrimitiveSubmodule _`. Rewrite using `[he V W hV hW h φ hφ hφ']`. Conclude with `(GlobalTheory.Published.AbelianDeRham.bcMor hφ).isMor.pullback1_mem_hodgeFiltration hs`. Introduce `V hV f s hs`.

Establish `hD` using `hV.basicOpen f`. Use `letI := resAlg (T.basicOpen_le f)`. Take `⟨φ, hφ, hφ'⟩` from `VB.exists_transition A hV hD (T.basicOpen_le f)`. Take `⟨hbc, hF⟩` from `hBC _ (onAff A hV) g (VB.isAbelianScheme_onAff A hA hV) (VB.smooth_onAff A hg hV) _ (onAff A hD) φ hφ`. Express the relevant statement in the definitionally equal form `e _ hD _ ∈ PrimitiveSubmodule _ at hs`.

Rewrite `hs` using `[he V _ hV hD (T.basicOpen_le f) φ hφ hφ', hF]`. Use `haveI := hV.isLocalization_basicOpen f`. Take `⟨n, hn⟩` from `exists_pow_smul_mem f _ hbc _ _ hs`. Use `⟨n, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e V hV _ ∈ PrimitiveSubmodule _`.

Rewrite using `[map_smul]`. Conclude with `hn`.
-/
theorem exists_hodgeSub : GlobalTheory.CovTop.Hypotheses2 → ∀ {T : Scheme.{0}} (A : Over T) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ F : GlobalTheory.VB.Sub H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV) := by
  intro hP T A _ g hA hg H e he
  have hBC := hP.p5.2.2.1
  refine exists_sub_of_affine H
    (fun V hV => (PrimitiveSubmodule (onAff A hV)).comap (e V hV).toLinearMap) ?_ ?_
  · intro V W hV hW h s hs
    letI := resAlg h
    obtain ⟨φ, hφ, hφ'⟩ := VB.exists_transition A hV hW h
    change e W hW _ ∈ PrimitiveSubmodule _
    rw [he V W hV hW h φ hφ hφ']
    exact (GlobalTheory.Published.AbelianDeRham.bcMor hφ).isMor.pullback1_mem_hodgeFiltration hs
  · intro V hV f s hs
    have hD := hV.basicOpen f
    letI := resAlg (T.basicOpen_le f)
    obtain ⟨φ, hφ, hφ'⟩ := VB.exists_transition A hV hD (T.basicOpen_le f)
    obtain ⟨hbc, hF⟩ := hBC _ (onAff A hV) g (VB.isAbelianScheme_onAff A hA hV)
      (VB.smooth_onAff A hg hV) _ (onAff A hD) φ hφ
    change e _ hD _ ∈ PrimitiveSubmodule _ at hs
    rw [he V _ hV hD (T.basicOpen_le f) φ hφ hφ', hF] at hs
    haveI := hV.isLocalization_basicOpen f
    obtain ⟨n, hn⟩ := exists_pow_smul_mem f _ hbc _ _ hs
    refine ⟨n, ?_⟩
    change e V hV _ ∈ PrimitiveSubmodule _
    rw [map_smul]
    exact hn

end GlobalTheory.HodgeSubsheaf
