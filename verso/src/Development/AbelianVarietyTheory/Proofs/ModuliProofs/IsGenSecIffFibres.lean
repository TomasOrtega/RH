import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoordsExistsUnit
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.GenSecFibre

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.VVRank GlobalTheory.EmbPull TopologicalSpace

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

/- English proof (translation)
Establish `e : ∀ j, z ∈ (LPow P.A P.L a T').U j → (IsUnit (gs (𝟙 _) z _ ((pullS P.A a h th).f j)) ↔ IsUnit (gs (𝟙 _) ((h ▷ P.A).left z) _ (th.f j)))` using `fun j hj => by`. Establish `q` using `gs_pullTo (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => a) th (h ▷ P.A).left (fun _ => whisker_snd_left P.A h) (𝟙 _) z j hj`. Rewrite `q` using `[Category.id_comp]`. Establish `q'` using `q.trans (gs_stalkMap (h ▷ P.A).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left P.A h) j hj) _)`. Conclude with `(iff_of_eq (congrArg IsUnit q')).trans (isUnit_map_iff _ _)`.

Rewrite using `[mem_nonzeroLocus, mem_nonzeroLocus]`. Use `exists_congr fun j => ⟨fun ⟨hj, u⟩ => ⟨?_, (e j hj).1 u⟩, fun ⟨hj, u⟩ => ?_⟩` and prove the remaining obligations. Conclude with `wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) j hj`. Establish `hj'` using `mem_wchart_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) z j hj`. Conclude with `⟨hj', (e j hj').2 u⟩`.
-/
theorem mem_nonzeroLocus_pullS (a : ℤ) (h : T' ⟶ T) (th : LB.Sec (LPow P.A P.L a T)) (z : (T' ⊗ P.A).left) :
    z ∈ nonzeroLocus (pullS P.A a h th) ↔ (h ▷ P.A).left z ∈ nonzeroLocus th := by
  have e : ∀ j, z ∈ (LPow P.A P.L a T').U j → (IsUnit (gs (𝟙 _) z _ ((pullS P.A a h th).f j)) ↔
      IsUnit (gs (𝟙 _) ((h ▷ P.A).left z) _ (th.f j))) := fun j hj => by
    have q := gs_pullTo (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => a) th (h ▷ P.A).left
      (fun _ => whisker_snd_left P.A h) (𝟙 _) z j hj
    rw [Category.id_comp] at q
    have q' := q.trans (gs_stalkMap (h ▷ P.A).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left P.A h) j hj) _)
    exact (iff_of_eq (congrArg IsUnit q')).trans (isUnit_map_iff _ _)
  rw [mem_nonzeroLocus, mem_nonzeroLocus]
  refine exists_congr fun j => ⟨fun ⟨hj, u⟩ => ⟨?_, (e j hj).1 u⟩, fun ⟨hj, u⟩ => ?_⟩
  · exact wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) j hj
  · have hj' := mem_wchart_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) z j hj
    exact ⟨hj', (e j hj').2 u⟩

/- English proof (translation)
Set `w : Spec (CommRingCat.of (T.left.residueField p)) ⟶ T.left` to `T.left.fromSpecResidueField p`. Set `h : Over.mk (w ≫ T.hom) ⟶ T` to `Over.homMk w rfl`. Establish `: IsAffine (Over.mk (w ≫ T.hom)).left` using `inferInstanceAs (IsAffine (Spec _))`. Establish `h₀` using `ThetaCoset.ne_zero_of_isGenSec hS P (w ≫ T.hom) (isGenSec_pullS P hS h H)`. Use `P.isAb.smooth` as an intermediate fact.

Establish `: Smooth (fst (Over.mk (w ≫ T.hom)) P.A).left` using `inferInstanceAs (Smooth (pullback.fst (w ≫ T.hom) P.A.hom))`. Establish `: IsReduced (Over.mk (w ≫ T.hom) ⊗ P.A).left` using `isReduced_scheme_of_smooth_of_isIntegrallyClosed (T.left.residueField p) (fst (Over.mk (w ≫ T.hom)) P.A).left`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 h th) := by`. Assume the negation of the conclusion as `hn`. Use `h₀ (Subtype.ext (funext fun j => ?_))` and prove the remaining obligations.

Conclude with `eq_zero_of_basicOpen_eq_bot _ (le_bot_iff.1 fun z hz => hn ⟨z, Opens.mem_iSup.2 ⟨j, hz⟩⟩)`. Use `⟨(h ▷ P.A).left z, ?_, (mem_nonzeroLocus_pullS P 1 h th z).1 hz⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, (isPullback_whisker P.A h).w, Scheme.Hom.comp_apply]`. Conclude with `(T.left.range_fromSpecResidueField p).le ⟨_, rfl⟩`.
-/
theorem exists_mem_nonzeroLocus (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : IsGenSec P.A P.L 1 th) (p : T.left) :
    ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th := by
  let w : Spec (CommRingCat.of (T.left.residueField p)) ⟶ T.left := T.left.fromSpecResidueField p
  let h : Over.mk (w ≫ T.hom) ⟶ T := Over.homMk w rfl
  have : IsAffine (Over.mk (w ≫ T.hom)).left := inferInstanceAs (IsAffine (Spec _))
  have h₀ := ThetaCoset.ne_zero_of_isGenSec hS P (w ≫ T.hom) (isGenSec_pullS P hS h H)
  have := P.isAb.smooth
  have : Smooth (fst (Over.mk (w ≫ T.hom)) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst (w ≫ T.hom) P.A.hom))
  have : IsReduced (Over.mk (w ≫ T.hom) ⊗ P.A).left :=
    isReduced_scheme_of_smooth_of_isIntegrallyClosed (T.left.residueField p) (fst (Over.mk (w ≫ T.hom)) P.A).left
  obtain ⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 h th) := by
    by_contra hn
    refine h₀ (Subtype.ext (funext fun j => ?_))
    exact eq_zero_of_basicOpen_eq_bot _ (le_bot_iff.1 fun z hz => hn ⟨z, Opens.mem_iSup.2 ⟨j, hz⟩⟩)
  refine ⟨(h ▷ P.A).left z, ?_, (mem_nonzeroLocus_pullS P 1 h th z).1 hz⟩
  rw [← Scheme.Hom.comp_apply, (isPullback_whisker P.A h).w, Scheme.Hom.comp_apply]
  exact (T.left.range_fromSpecResidueField p).le ⟨_, rfl⟩

/- English proof (translation)
Rewrite using `[map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_mul, map_mul, ht, hs, hd, he, smul_smul, smul_smul, sub_eq_zero]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_sub_eq_zero' {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M]
    [Module R' M'] (σ : R →+* R') (φ : M →ₛₗ[σ] M') (s t : M) (b : M') (a c d₀ e₀ : R) (d e : R')
    (ht : φ t = d • b) (hs : φ s = e • b) (hd : σ d₀ = σ a * d) (he : σ e₀ = σ c * e) :
    φ ((d₀ * c) • s - (e₀ * a) • t) = 0 := by
  rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_mul, map_mul, ht, hs, hd, he, smul_smul, smul_smul,
    sub_eq_zero]
  congr 1
  ring

/- English proof (translation)
Introduce `s`. Set `I : Ideal Γ(T.left, ⊤)` to `(Submodule.span Γ(T.left, ⊤) {SecM.ofSec P.A th}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))`. Establish `key : ∀ p : T.left, ∃ f ∈ I, p ∈ T.left.basicOpen f` using `fun p => by`. Take `⟨V, hV, b, hb⟩` from `hS S P 1 le_rfl (T.hom p)`. Establish `hq : Unique (Fin (1 ^ P.g))` using `by rw [one_pow]; infer_instance`.

Take `⟨f, hf, hp⟩` from `(isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial`. Set `W` to `T.left.basicOpen f`. Set `l : overRes W ⟶ overRes (T` to `baseOver S) V := Over.homMk (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))`. Establish `hW : IsAffineOpen W` using `(isAffineOpen_top _).basicOpen f`. Establish `: IsAffine (overRes W).left` using `hW`. Take `⟨c, -⟩` from `exists_basis P 1 b hb (overRes W) l`. Establish `rep : ∀ x : SecM P.A P.L 1 (overRes W), ∃ d : Γ((overRes W).left, ⊤), x = d • (c hq.default :)` using `fun x => by`.

Use `c.sum_repr x` as an intermediate fact. Rewrite `this` using `[Fintype.sum_unique]`. Conclude with `⟨_, this.symm⟩`. Take `⟨d, hd⟩` from `rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A th))`. Take `⟨e, he⟩` from `rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A s))`.

Take `⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ = (overResι W).left.appTop.hom (f ^ m) * d` from `exists_pow_mul_extend f d`. Take `⟨n, e₀, he₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ = (overResι W).left.appTop.hom (f ^ m) * e` from `exists_pow_mul_extend f e`. Take `⟨N, hN⟩` from `exists_pow_kill_secM P 1 f ((d₀ * f ^ n) • SecM.ofSec P.A s - (e₀ * f ^ m) • SecM.ofSec P.A th) (map_sub_eq_zero' _ _ _ _ _ _ _ _ _ d e hd he hd₀ he₀)`. Establish `hu : p ∈ T.left.basicOpen d₀`. Take `⟨q, hqp, hq0⟩` from `H p`.

Take `⟨z, hz, hz'⟩` from `Scheme.exists_preimage_of_isPullback (isPullback_whisker P.A (overResι W)) q ⟨p, hp⟩ hqp`. Substitute `hz` using the available equality. Take `⟨j, hj, u⟩` from `(mem_nonzeroLocus _ _).1 ((mem_nonzeroLocus_pullS P 1 (overResι W) th z).2 hq0)`. Establish `k` using `(congrArg (fun x => gs (𝟙 _) z _ (x.1 j)) hd).trans (PushInv.gs_smul P.A P.L _ 1 d _ j z hj)`. Establish `u₁ : IsUnit (gs (fst (overRes W) P.A).left z ⊤ d)` using `isUnit_of_mul_isUnit_left (k ▸ u)`.

Rewrite `u₁` using `[gs_stalkMap _ z ⊤ trivial, isUnit_map_iff, gs_eq _ _ ⊤ trivial]`. Establish `u₂ : (fst (overRes W) P.A).left z ∈ (overRes W).left.basicOpen d` using `(Scheme.mem_basicOpen_top _ _ _).2 u₁`. Establish `u₃ : (⟨p, hp⟩ : (overRes W).left) ∈ (overResι W).left ⁻¹ᵁ T.left.basicOpen d₀`. Rewrite using `[Scheme.preimage_basicOpen_top, hd₀, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top]`. Use `⟨?_, hz' ▸ u₂⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `p ∈ T.left.basicOpen (f ^ m)`. Rewrite `hp`, the goal using `[Scheme.mem_basicOpen_top]`. Rewrite using `[map_pow]`. Conclude with `hp.pow _`. Conclude with `u₃`.

Use `⟨f ^ N * (d₀ * f ^ n), Submodule.mem_span_singleton.2 ⟨f ^ N * (e₀ * f ^ m), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite `hN` using `[smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul]`. Conclude with `hN.symm`. Rewrite `hp`, `hu`, the goal using `[Scheme.mem_basicOpen_top]`. Simplify using `only [map_mul, map_pow]`.

Conclude with `(hp.pow _).mul (hu.mul (hp.pow _))`. Establish `hI : Ideal.span (I : Set Γ(T.left, ⊤)) = ⊤` using `(isAffineOpen_top T.left).self_le_iSup_basicOpen_iff.1 fun p _ => by`. Take `⟨f, hf, hp⟩` from `key p`. Conclude with `Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩`. Rewrite `hI` using `[Ideal.span_eq, Ideal.eq_top_iff_one]`.

Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 hI`. Rewrite `hr` using `[LinearMap.toSpanSingleton_apply, one_smul]`. Conclude with `⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩`.
-/
theorem isGenSec_of_fibres (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : ∀ p : T.left, ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th) :
    IsGenSec P.A P.L 1 th := by
  intro s
  let I : Ideal Γ(T.left, ⊤) := (Submodule.span Γ(T.left, ⊤)
    {SecM.ofSec P.A th}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))
  have key : ∀ p : T.left, ∃ f ∈ I, p ∈ T.left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
    have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
    let W := T.left.basicOpen f
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
    have : IsAffine (overRes W).left := hW
    obtain ⟨c, -⟩ := exists_basis P 1 b hb (overRes W) l
    have rep : ∀ x : SecM P.A P.L 1 (overRes W), ∃ d : Γ((overRes W).left, ⊤), x = d • (c hq.default :) := fun x => by
      have := c.sum_repr x
      rw [Fintype.sum_unique] at this
      exact ⟨_, this.symm⟩
    obtain ⟨d, hd⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A th))
    obtain ⟨e, he⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A s))
    obtain ⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * d := exists_pow_mul_extend f d
    obtain ⟨n, e₀, he₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * e := exists_pow_mul_extend f e
    obtain ⟨N, hN⟩ := exists_pow_kill_secM P 1 f ((d₀ * f ^ n) • SecM.ofSec P.A s - (e₀ * f ^ m) • SecM.ofSec P.A th)
      (map_sub_eq_zero' _ _ _ _ _ _ _ _ _ d e hd he hd₀ he₀)
    have hu : p ∈ T.left.basicOpen d₀ := by
      obtain ⟨q, hqp, hq0⟩ := H p
      obtain ⟨z, hz, hz'⟩ := Scheme.exists_preimage_of_isPullback (isPullback_whisker P.A (overResι W)) q
        ⟨p, hp⟩ hqp
      subst hz
      obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 ((mem_nonzeroLocus_pullS P 1 (overResι W) th z).2 hq0)
      have k := (congrArg (fun x => gs (𝟙 _) z _ (x.1 j)) hd).trans (PushInv.gs_smul P.A P.L _ 1 d _ j z hj)
      have u₁ : IsUnit (gs (fst (overRes W) P.A).left z ⊤ d) := isUnit_of_mul_isUnit_left (k ▸ u)
      rw [gs_stalkMap _ z ⊤ trivial, isUnit_map_iff, gs_eq _ _ ⊤ trivial] at u₁
      have u₂ : (fst (overRes W) P.A).left z ∈ (overRes W).left.basicOpen d := (Scheme.mem_basicOpen_top _ _ _).2 u₁
      have u₃ : (⟨p, hp⟩ : (overRes W).left) ∈ (overResι W).left ⁻¹ᵁ T.left.basicOpen d₀ := by
        rw [Scheme.preimage_basicOpen_top, hd₀, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top]
        refine ⟨?_, hz' ▸ u₂⟩
        change p ∈ T.left.basicOpen (f ^ m)
        rw [Scheme.mem_basicOpen_top] at hp ⊢
        rw [map_pow]
        exact hp.pow _
      exact u₃
    refine ⟨f ^ N * (d₀ * f ^ n), Submodule.mem_span_singleton.2 ⟨f ^ N * (e₀ * f ^ m), ?_⟩, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul] at hN
      exact hN.symm
    · rw [Scheme.mem_basicOpen_top] at hp hu ⊢
      simp only [map_mul, map_pow]
      exact (hp.pow _).mul (hu.mul (hp.pow _))
  have hI : Ideal.span (I : Set Γ(T.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hI
  rw [LinearMap.toSpanSingleton_apply, one_smul] at hr
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

/- English proof (translation)
Introduce `h S P R _ y th`. Establish `: IsAffine (Over.mk y).left` using `inferInstanceAs (IsAffine (Spec _))`. Conclude with `⟨exists_mem_nonzeroLocus P h.secBaseChangeAny, isGenSec_of_fibres P (T := Over.mk y) h.secBaseChangeAny⟩`.
-/
theorem isGenSec_iff_fibres : Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (R : Type) [CommRing R] (y : Sp R ⟶ S) (th : LB.Sec (Out.LPow P.A P.L 1 (Over.mk y))), Out.IsGenSec P.A P.L 1 th ↔ ∀ p : Sp R, ∃ q : (Over.mk y ⊗ P.A).left, (fst (Over.mk y) P.A).left q = p ∧ q ∈ Out.nonzeroLocus th := by
  intro h S P R _ y th
  have : IsAffine (Over.mk y).left := inferInstanceAs (IsAffine (Spec _))
  exact ⟨exists_mem_nonzeroLocus P h.secBaseChangeAny,
    isGenSec_of_fibres P (T := Over.mk y) h.secBaseChangeAny⟩

end GlobalTheory.GenSecFibre
end
