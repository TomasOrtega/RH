import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsLiftComplete

/- English proof (translation)
Introduce `V K _ _ _ _ n hc hn π hπ A₀ _ _ A _ _ i hA hpb s₀ hs₀`. Use `haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hc`. Use `haveI : HenselianLocalRing V := GlobalTheory.henselianLocalRing_of_henselianRing V`. Use `haveI : Smooth A.hom := hA.smooth`. Establish `hn' : IsUnit (n : Γ(Sp V, ⊤))`.

Simplify using `using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom`. Use `haveI := GlobalTheory.GrpTangent.etale_id_pow A hn'`. Set `T' : Over (Sp K)` to `𝟙_ (Over (Sp K))`. Set `T : Over (Sp V)` to `Over.mk (T'.hom ≫ spMap π)`. Establish `hwi : i ≫ A.hom = A₀.hom ≫ spMap π` using `hpb.1.w`.

Establish `hpt : ∀ x : T' ⟶ A₀, (x.left ≫ i) ≫ A.hom = T.hom`. Introduce `x`. Rewrite using `[Category.assoc, hwi, ← Category.assoc, Over.w x]`. Both sides reduce to the same expression. Set `pt : (T' ⟶ A₀) → (T ⟶ A)` to `fun x => Over.homMk (x.left ≫ i) (hpt x)`.

Establish `hone : pt 1 = 1`. Establish `h` using `hpb.2 T' 1 1 (pt 1) (pt 1) rfl rfl`. Rewrite `h` using `[_root_.mul_one]`. Establish `h2 : pt 1 * pt 1 = pt 1` using `Over.OverMorphism.ext h`. Conclude with `mul_eq_left.mp h2`.

Establish `hpow : ∀ m : ℕ, (pt s₀) ^ m = pt (s₀ ^ m)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, hone]`. Consider the case `succ m ih`.

Rewrite using `[pow_succ, pow_succ]`. Conclude with `Over.OverMorphism.ext (hpb.2 T' (s₀ ^ m) s₀ ((pt s₀) ^ m) (pt s₀) (by rw [ih]; rfl) rfl)`. Establish `hx : (pt s₀) ^ n = 1` using `by rw [hpow, hs₀, hone]`. Set `f : A.left ⟶ A.left` to `(𝟙 A ^ n).left`. Establish `hf : ∀ {Y : Over (Sp V)} (y : Y ⟶ A), y.left ≫ f = (y ^ n).left`.

Introduce `Y y`. Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id]`. Establish `hone' : ∀ {Y : Over (Sp V)} , ((1 : Y ⟶ A)).left = Y.hom ≫ (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left`. Introduce `Y`. Rewrite using `[Hom.one_def, Over.comp_left]`.

Use `congr 1`. Establish `hw : (s₀.left ≫ i) ≫ f = Spec.map (CommRingCat.ofHom π) ≫ (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left`. Use `hf (pt s₀)` as an intermediate fact. Rewrite `this` using `[hx, hone']`. Simplify `this` using `[pt, T, T']`.

Take `⟨l, ⟨hl1, hl2⟩, huniq⟩` from `GlobalTheory.existsUnique_lift_of_etale_of_henselian f π hπ (s₀.left ≫ i) _ hw`. Establish `hls : l ≫ A.hom = (𝟙_ (Over (Sp V))).hom`. Establish `e : f ≫ A.hom = A.hom` using `Over.w (𝟙 A ^ n)`. Rewrite using `[← e, ← Category.assoc, hl2]`. Conclude with `Over.w (η[A] : 𝟙_ (Over (Sp V)) ⟶ A)`.

Set `s : 𝟙_ (Over (Sp V)) ⟶ A` to `Over.homMk l hls`. Establish `hsn : ∀ s' : 𝟙_ (Over (Sp V)) ⟶ A, s' ^ n = 1 ↔ s'.left ≫ f = (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left`. Introduce `s'`. Establish `e1 : ((1 : 𝟙_ (Over (Sp V)) ⟶ A)).left = (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left`. Rewrite using `[hone']`.

Conclude with `Category.id_comp _`. Rewrite using `[hf]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h, e1]`.

Introduce `h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[h, e1]`. Use `⟨s, ⟨(hsn s).2 hl2, hl1.symm⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `s' ⟨h1, h2⟩`.

Conclude with `Over.OverMorphism.ext (huniq s'.left ⟨h2.symm, (hsn s').1 h1⟩)`.
-/
theorem existsUnique_torsion_lift : ∀ (V K : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [Field K] (n : ℕ), IsAdicComplete (IsLocalRing.maximalIdeal V) V → IsUnit (n : V) → ∀ π : V →+* K, Function.Surjective π → ∀ (A₀ : Over (Sp K)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A₀ A (spMap π) i → ∀ s₀ : 𝟙_ (Over (Sp K)) ⟶ A₀, s₀ ^ n = 1 → ∃! s : 𝟙_ (Over (Sp V)) ⟶ A, s ^ n = 1 ∧ s₀.left ≫ i = spMap π ≫ s.left := by
  intro V K _ _ _ _ n hc hn π hπ A₀ _ _ A _ _ i hA hpb s₀ hs₀
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hc
  haveI : HenselianLocalRing V := GlobalTheory.henselianLocalRing_of_henselianRing V
  haveI : Smooth A.hom := hA.smooth
  have hn' : IsUnit (n : Γ(Sp V, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  haveI := GlobalTheory.GrpTangent.etale_id_pow A hn'
  let T' : Over (Sp K) := 𝟙_ (Over (Sp K))
  let T : Over (Sp V) := Over.mk (T'.hom ≫ spMap π)
  have hwi : i ≫ A.hom = A₀.hom ≫ spMap π := hpb.1.w
  have hpt : ∀ x : T' ⟶ A₀, (x.left ≫ i) ≫ A.hom = T.hom := by
    intro x
    rw [Category.assoc, hwi, ← Category.assoc, Over.w x]
    rfl
  let pt : (T' ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk (x.left ≫ i) (hpt x)
  have hone : pt 1 = 1 := by
    have h := hpb.2 T' 1 1 (pt 1) (pt 1) rfl rfl
    rw [_root_.mul_one] at h
    have h2 : pt 1 * pt 1 = pt 1 := Over.OverMorphism.ext h
    exact mul_eq_left.mp h2
  have hpow : ∀ m : ℕ, (pt s₀) ^ m = pt (s₀ ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact Over.OverMorphism.ext (hpb.2 T' (s₀ ^ m) s₀ ((pt s₀) ^ m) (pt s₀) (by rw [ih]; rfl) rfl)
  have hx : (pt s₀) ^ n = 1 := by rw [hpow, hs₀, hone]
  let f : A.left ⟶ A.left := (𝟙 A ^ n).left
  have hf : ∀ {Y : Over (Sp V)} (y : Y ⟶ A), y.left ≫ f = (y ^ n).left := by
    intro Y y
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone' : ∀ {Y : Over (Sp V)} , ((1 : Y ⟶ A)).left = Y.hom ≫ (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hw : (s₀.left ≫ i) ≫ f = Spec.map (CommRingCat.ofHom π) ≫ (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
    have := hf (pt s₀)
    rw [hx, hone'] at this
    simpa [pt, T, T'] using this
  obtain ⟨l, ⟨hl1, hl2⟩, huniq⟩ :=
    GlobalTheory.existsUnique_lift_of_etale_of_henselian f π hπ (s₀.left ≫ i) _ hw
  have hls : l ≫ A.hom = (𝟙_ (Over (Sp V))).hom := by
    have e : f ≫ A.hom = A.hom := Over.w (𝟙 A ^ n)
    rw [← e, ← Category.assoc, hl2]
    exact Over.w (η[A] : 𝟙_ (Over (Sp V)) ⟶ A)
  let s : 𝟙_ (Over (Sp V)) ⟶ A := Over.homMk l hls
  have hsn : ∀ s' : 𝟙_ (Over (Sp V)) ⟶ A, s' ^ n = 1 ↔ s'.left ≫ f = (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
    intro s'
    have e1 : ((1 : 𝟙_ (Over (Sp V)) ⟶ A)).left = (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
      rw [hone']; exact Category.id_comp _
    rw [hf]
    constructor
    · intro h; rw [h, e1]
    · intro h
      apply Over.OverMorphism.ext
      rw [h, e1]
  refine ⟨s, ⟨(hsn s).2 hl2, hl1.symm⟩, ?_⟩
  rintro s' ⟨h1, h2⟩
  exact Over.OverMorphism.ext (huniq s'.left ⟨h2.symm, (hsn s').1 h1⟩)

end GlobalTheory.TorsLiftComplete
