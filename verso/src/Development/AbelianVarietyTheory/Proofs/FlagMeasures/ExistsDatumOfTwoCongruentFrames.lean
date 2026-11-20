import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOntoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeFrameEqStandardTranslateStatement

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.TermOver

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Simplify using `[img, Submodule.mem_map]`.
-/
lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [img, Submodule.mem_map]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_img]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨k y, ⟨y, hy, rfl⟩, rfl⟩`.

Introduce and unpack `⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`.
-/
lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_img]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`.

Introduce `hx`. Conclude with `⟨x, hx, rfl⟩`.
-/
lemma img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hΛ`. Use `⟨h1.map _, ?_, ?_⟩` and prove the remaining obligations. Establish `himg : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V →ₗ[E] V) '' (Λ : Set V)`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, mem_img, Set.mem_image]`.

Both sides reduce to the same expression. Rewrite using `[himg, ← Submodule.map_span, h2, Submodule.map_top]`. Conclude with `LinearMap.range_eq_top.mpr g.surjective`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx y hy`. Take `⟨a, ha, rfl⟩` from `(mem_img g Λ x).1 hx`. Take `⟨b, hb, rfl⟩` from `(mem_img g Λ y).1 hy`. Rewrite using `[hg]`. Conclude with `(h3 a).1 ha b hb`.

Introduce `hx`. Take `⟨a, rfl⟩` from `g.surjective x`. Use `(mem_img g Λ _).2 ⟨a, (h3 a).2 fun y hy => ?_, rfl⟩` and prove the remaining obligations. Use `hx (g y) ((mem_img g Λ _).2 ⟨y, hy, rfl⟩)` as an intermediate fact. Rewrite `this` using `[hg]`. Then use the resulting hypothesis.
-/
lemma img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨h1, h2, h3⟩ := hΛ
  refine ⟨h1.map _, ?_, ?_⟩
  · have himg : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V →ₗ[E] V) '' (Λ : Set V) := by
      ext x
      simp only [SetLike.mem_coe, mem_img, Set.mem_image]
      rfl
    rw [himg, ← Submodule.map_span, h2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr g.surjective
  · intro x
    constructor
    · intro hx y hy
      obtain ⟨a, ha, rfl⟩ := (mem_img g Λ x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_img g Λ y).1 hy
      rw [hg]
      exact (h3 a).1 ha b hb
    · intro hx
      obtain ⟨a, rfl⟩ := g.surjective x
      refine (mem_img g Λ _).2 ⟨a, (h3 a).2 fun y hy => ?_, rfl⟩
      have := hx (g y) ((mem_img g Λ _).2 ⟨y, hy, rfl⟩)
      rwa [hg] at this

/- English proof (translation)
Take `⟨⟨p1, p2, p3⟩, h2, h3, h4, h5⟩` from `hf`. Use `⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, p1 a, rfl⟩, ?_, ?_⟩, ?_, ?_, h4, h5⟩` and prove the remaining obligations. Conclude with `p2.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)`. Introduce `x hx hs`. Take `⟨y, hy, rfl⟩` from `(mem_img g Λ x).1 hx`.

Establish `hrange : Set.range (fun b => g (f b)) = (g : V →ₗ[E] V) '' Set.range f`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite `hs` using `[hrange, ← Submodule.map_span]`. Take `⟨y', hy', hyy⟩` from `hs`.

Establish `hyy' : y' = y` using `g.injective hyy`. Substitute `hyy'` using the available equality. Establish `hO` using `p3 y' hy hy'`. Establish `hmap : ∀ v ∈ Submodule.span M.L.O (Set.range f), g v ∈ Submodule.span M.L.O (Set.range fun b => g (f b))`. Introduce `v hv`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨b, rfl⟩` from `hv`. Conclude with `Submodule.subset_span ⟨b, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha`. Establish `: g (c • a) = c • g a`.

Express the relevant statement in the definitionally equal form `g ((c : E) • a) = (c : E) • g a`. Conclude with `map_smul g (c : E) a`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ c ha`. Conclude with `hmap y' hO`.

Introduce `a b hab`. Rewrite using `[hg]`. Conclude with `h2 a b hab`. Rewrite using `[hg]`. Conclude with `h3`.
-/
lemma img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  obtain ⟨⟨p1, p2, p3⟩, h2, h3, h4, h5⟩ := hf
  refine ⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, p1 a, rfl⟩, ?_, ?_⟩, ?_, ?_, h4, h5⟩
  · exact p2.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)
  · intro x hx hs
    obtain ⟨y, hy, rfl⟩ := (mem_img g Λ x).1 hx
    have hrange : Set.range (fun b => g (f b)) = (g : V →ₗ[E] V) '' Set.range f := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span] at hs
    obtain ⟨y', hy', hyy⟩ := hs
    have hyy' : y' = y := g.injective hyy
    subst hyy'
    have hO := p3 y' hy hy'
    have hmap : ∀ v ∈ Submodule.span M.L.O (Set.range f),
        g v ∈ Submodule.span M.L.O (Set.range fun b => g (f b)) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨b, rfl⟩ := hv
        exact Submodule.subset_span ⟨b, rfl⟩
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : g (c • a) = c • g a := by
          change g ((c : E) • a) = (c : E) • g a
          exact map_smul g (c : E) a
        rw [this]
        exact Submodule.smul_mem _ c ha
    exact hmap y' hO
  · intro a b hab
    rw [hg]
    exact h2 a b hab
  · rw [hg]
    exact h3

/- English proof (translation)
Take `⟨h1, -, h3⟩` from `GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto M hM H r Fr hf.2.2.2.2`. Take `⟨n, hn, hnf⟩` from `h3 f hT`. Establish `hu : IsUnitary H n⁻¹` using `((h1 _).1 (Fr.N.inv_mem hn)).1`. Establish `hfr : H.IsFrame (img n⁻¹ Λ) r Fr.f Fr.T`. Use `img_frame H hu hf` as an intermediate fact.

Establish `he : (fun b => n⁻¹ (f b)) = Fr.f`. Use function extensionality and compare the values at `b`. Rewrite using `[hnf]`. Conclude with `n.symm_apply_apply _`. Rewrite `this` using `[he]`. Then use the resulting hypothesis.

Take `⟨L, hL, -, n0, hn0, hfix, hΛ0⟩` from `GlobalTheory.T.selfDual_lattice_frame_eq_standard_translate M hM H r Fr (img n⁻¹ Λ) (img_selfDual H hu hΛ) hfr`. Use `⟨L, hL, n * n0, Fr.N.mul_mem hn hn0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hnf]`. Use function extensionality and compare the values at `b`. Express the relevant statement in the definitionally equal form `n (Fr.f b) = n (n0 (Fr.f b))`.

Rewrite using `[hfix]`. Rewrite using `[img_mul, ← hΛ0, ← img_mul, mul_inv_cancel, img_one]`.
-/
lemma side (hM : M.OK) (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) {Λ : Submodule M.L.O V}
    {f : Fin (r + 1) → V} (hΛ : H.IsSelfDual Λ) (hf : H.IsFrame Λ r f Fr.T) (hT : Tri E Fr.f f) :
    ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧
      ∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = img n (Fr.LamStd L) := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto M hM H r Fr hf.2.2.2.2
  obtain ⟨n, hn, hnf⟩ := h3 f hT
  have hu : IsUnitary H n⁻¹ := ((h1 _).1 (Fr.N.inv_mem hn)).1
  have hfr : H.IsFrame (img n⁻¹ Λ) r Fr.f Fr.T := by
    have := img_frame H hu hf
    have he : (fun b => n⁻¹ (f b)) = Fr.f := by
      funext b
      rw [hnf]
      exact n.symm_apply_apply _
    rwa [he] at this
  obtain ⟨L, hL, -, n0, hn0, hfix, hΛ0⟩ :=
    GlobalTheory.T.selfDual_lattice_frame_eq_standard_translate M hM H r Fr (img n⁻¹ Λ) (img_selfDual H hu hΛ) hfr
  refine ⟨L, hL, n * n0, Fr.N.mul_mem hn hn0, ?_, ?_⟩
  · rw [hnf]
    funext b
    change n (Fr.f b) = n (n0 (Fr.f b))
    rw [hfix]
  · rw [img_mul, ← hΛ0, ← img_mul, mul_inv_cancel, img_one]

end

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r P t ht hT hT' hf hf'`. Take `⟨hsd, hfr, hfr', -, -, hg⟩` from `ht`. Rewrite `hfr` using `[hT]`. Rewrite `hfr'` using `[hT']`. Take `⟨L, hL, n, hn, hnf, hnΛ⟩` from `side hM H r P.A hsd hfr hf`.

Take `⟨L', hL', n', hn', hnf', hnΛ'⟩` from `side hM H r P.B hsd hfr' hf'`. Set `s : Term V M r` to `⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩`. Use `⟨⟨L, L', hL, hL', {p | ∃ g, M.split = some g ∧ p ∈ H.iotaGraph g s}, ?_⟩, hT, hT', ⟨n, hn, hnf, hnΛ⟩, ⟨n', hn', hnf', hnΛ'⟩, ?_⟩` and prove the remaining obligations. Introduce `h`. Use extensionality with `p`.

Simplify using `[h]`. Introduce `g hgs`. Use `⟨(hg g hgs).2.2, ?_⟩` and prove the remaining obligations. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion.

Introduce `hp`. Conclude with `⟨g, hgs, hp⟩`. Introduce and unpack `⟨g', hg', hp⟩`. Take `rfl : g = g'` from `Option.some.inj (hgs.symm.trans hg')`. Conclude with `hp`.
-/
theorem exists_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (P : FPair H r) (t : Term V M r), H.IsTerm t → t.T = P.A.T → t.T' = P.B.T → Tri E P.A.f t.f → Tri E P.B.f t.f' → ∃ d : Datum P, IsTermOver P d t := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r P t ht hT hT' hf hf'
  obtain ⟨hsd, hfr, hfr', -, -, hg⟩ := ht
  rw [hT] at hfr
  rw [hT'] at hfr'
  obtain ⟨L, hL, n, hn, hnf, hnΛ⟩ := side hM H r P.A hsd hfr hf
  obtain ⟨L', hL', n', hn', hnf', hnΛ'⟩ := side hM H r P.B hsd hfr' hf'
  let s : Term V M r := ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩
  refine ⟨⟨L, L', hL, hL', {p | ∃ g, M.split = some g ∧ p ∈ H.iotaGraph g s}, ?_⟩, hT, hT',
    ⟨n, hn, hnf, hnΛ⟩, ⟨n', hn', hnf', hnΛ'⟩, ?_⟩
  · intro h
    ext p
    simp [h]
  · intro g hgs
    refine ⟨(hg g hgs).2.2, ?_⟩
    ext p
    constructor
    · intro hp
      exact ⟨g, hgs, hp⟩
    · rintro ⟨g', hg', hp⟩
      obtain rfl : g = g' := Option.some.inj (hgs.symm.trans hg')
      exact hp

end GlobalTheory.LocOver.TermOver
