import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Module

namespace GlobalTheory.WeilDeligne

section ProdLin

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
The claim follows from `map_absSpace_le (f := f) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inl ℂ V V') (fun x => Prod.ext rfl (map_zero g).symm) r`.
-/
theorem inl_absSpace_le (f : End ℂ V) (g : End ℂ V') (r : ℝ) :
    (absSpace f r).map (LinearMap.inl ℂ V V') ≤ absSpace (f.prodMap g : End ℂ (V × V')) r :=
  map_absSpace_le (f := f) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inl ℂ V V')
    (fun x => Prod.ext rfl (map_zero g).symm) r

/- English proof (translation)
The claim follows from `map_absSpace_le (f := g) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inr ℂ V V') (fun x => Prod.ext (map_zero f).symm rfl) r`.
-/
theorem inr_absSpace_le (f : End ℂ V) (g : End ℂ V') (r : ℝ) :
    (absSpace g r).map (LinearMap.inr ℂ V V') ≤ absSpace (f.prodMap g : End ℂ (V × V')) r :=
  map_absSpace_le (f := g) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inr ℂ V V')
    (fun x => Prod.ext (map_zero f).symm rfl) r

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `⟨map_absSpace_le (LinearMap.fst ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩, map_absSpace_le (LinearMap.snd ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `e : v = LinearMap.inl ℂ V V' v.1 + LinearMap.inr ℂ V V' v.2` using `by simp`.

Rewrite using `[e]`. Conclude with `add_mem (inl_absSpace_le f g r ⟨_, h1, rfl⟩) (inr_absSpace_le f g r ⟨_, h2, rfl⟩)`.
-/
theorem mem_absSpace_prodMap (f : End ℂ V) (g : End ℂ V') (r : ℝ) (v : V × V') :
    v ∈ absSpace (f.prodMap g : End ℂ (V × V')) r ↔ v.1 ∈ absSpace f r ∧ v.2 ∈ absSpace g r := by
  constructor
  · intro hv
    exact ⟨map_absSpace_le (LinearMap.fst ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩,
      map_absSpace_le (LinearMap.snd ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    have e : v = LinearMap.inl ℂ V V' v.1 + LinearMap.inr ℂ V V' v.2 := by simp
    rw [e]
    exact add_mem (inl_absSpace_le f g r ⟨_, h1, rfl⟩) (inr_absSpace_le f g r ⟨_, h2, rfl⟩)

/- English proof (translation)
Establish `hpow : ∀ i : ℕ, (N.prodMap M : End ℂ (V × V')) ^ i = (N ^ i).prodMap (M ^ i)` using `fun i => (map_pow (LinearMap.prodMapRingHom ℂ V V') (N, M) i).symm`. Use `⟨eq_top_iff.mpr fun v _ => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : v.1 ∈ ⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2))` using `hf.1 ▸ Submodule.mem_top`. Establish `h2 : v.2 ∈ ⨆ i : ℤ, absSpace g (q ^ ((i : ℝ) / 2))` using `hg.1 ▸ Submodule.mem_top`. Establish `hl : (⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2))).map (LinearMap.inl ℂ V V') ≤ ⨆ i : ℤ, absSpace (f.prodMap g : End ℂ (V × V')) (q ^ ((i : ℝ) / 2))`.

Rewrite using `[Submodule.map_iSup]`. Conclude with `iSup_mono fun i => inl_absSpace_le f g _`. Establish `hr : (⨆ i : ℤ, absSpace g (q ^ ((i : ℝ) / 2))).map (LinearMap.inr ℂ V V') ≤ ⨆ i : ℤ, absSpace (f.prodMap g : End ℂ (V × V')) (q ^ ((i : ℝ) / 2))`. Rewrite using `[Submodule.map_iSup]`. Conclude with `iSup_mono fun i => inr_absSpace_le f g _`.

Establish `e : v = LinearMap.inl ℂ V V' v.1 + LinearMap.inr ℂ V V' v.2` using `by simp`. Rewrite using `[e]`. Conclude with `add_mem (hl ⟨_, h1, rfl⟩) (hr ⟨_, h2, rfl⟩)`. Rewrite using `[hpow]`. Use `⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩` and prove the remaining obligations.

Rewrite `hv`, the goal using `[SetLike.mem_coe, mem_absSpace_prodMap]`. Conclude with `⟨(hf.2 i).1 hv.1, (hg.2 i).1 hv.2⟩`. Rewrite `hv`, `hv'` using `[SetLike.mem_coe, mem_absSpace_prodMap]`. Use `Prod.ext_iff.mp hvv` as an intermediate fact. Conclude with `Prod.ext ((hf.2 i).2.1 hv.1 hv'.1 this.1) ((hg.2 i).2.1 hv.2 hv'.2 this.2)`.

Rewrite `hv` using `[SetLike.mem_coe, mem_absSpace_prodMap]`. Take `⟨u, hu, e1⟩` from `(hf.2 i).2.2 hv.1`. Take `⟨u', hu', e2⟩` from `(hg.2 i).2.2 hv.2`. Conclude with `⟨(u, u'), (mem_absSpace_prodMap _ _ _ _).mpr ⟨hu, hu'⟩, Prod.ext e1 e2⟩`.
-/
theorem IsPurePair.prodMap {q : ℝ} {f N : End ℂ V} {g M : End ℂ V'} (hf : IsPurePair q f N)
    (hg : IsPurePair q g M) :
    IsPurePair q (f.prodMap g : End ℂ (V × V')) (N.prodMap M) := by
  have hpow : ∀ i : ℕ, (N.prodMap M : End ℂ (V × V')) ^ i = (N ^ i).prodMap (M ^ i) :=
    fun i => (map_pow (LinearMap.prodMapRingHom ℂ V V') (N, M) i).symm
  refine ⟨eq_top_iff.mpr fun v _ => ?_, fun i => ?_⟩
  · have h1 : v.1 ∈ ⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2)) := hf.1 ▸ Submodule.mem_top
    have h2 : v.2 ∈ ⨆ i : ℤ, absSpace g (q ^ ((i : ℝ) / 2)) := hg.1 ▸ Submodule.mem_top
    have hl : (⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2))).map (LinearMap.inl ℂ V V') ≤
        ⨆ i : ℤ, absSpace (f.prodMap g : End ℂ (V × V')) (q ^ ((i : ℝ) / 2)) := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun i => inl_absSpace_le f g _
    have hr : (⨆ i : ℤ, absSpace g (q ^ ((i : ℝ) / 2))).map (LinearMap.inr ℂ V V') ≤
        ⨆ i : ℤ, absSpace (f.prodMap g : End ℂ (V × V')) (q ^ ((i : ℝ) / 2)) := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun i => inr_absSpace_le f g _
    have e : v = LinearMap.inl ℂ V V' v.1 + LinearMap.inr ℂ V V' v.2 := by simp
    rw [e]
    exact add_mem (hl ⟨_, h1, rfl⟩) (hr ⟨_, h2, rfl⟩)
  · rw [hpow]
    refine ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩
    · rw [SetLike.mem_coe, mem_absSpace_prodMap] at hv ⊢
      exact ⟨(hf.2 i).1 hv.1, (hg.2 i).1 hv.2⟩
    · rw [SetLike.mem_coe, mem_absSpace_prodMap] at hv hv'
      have := Prod.ext_iff.mp hvv
      exact Prod.ext ((hf.2 i).2.1 hv.1 hv'.1 this.1) ((hg.2 i).2.1 hv.2 hv'.2 this.2)
    · rw [SetLike.mem_coe, mem_absSpace_prodMap] at hv
      obtain ⟨u, hu, e1⟩ := (hf.2 i).2.2 hv.1
      obtain ⟨u', hu', e2⟩ := (hg.2 i).2.2 hv.2
      exact ⟨(u, u'), (mem_absSpace_prodMap _ _ _ _).mpr ⟨hu, hu'⟩, Prod.ext e1 e2⟩

end ProdLin

/- English proof (translation)
Introduce `φ hφ` and use `(ha φ hφ).prodMap (hb φ hφ)`.
-/
theorem WDRep.Tempered.sum {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {a : WDRep h V} {b : WDRep h V'}
    (ha : a.Tempered) (hb : b.Tempered) : (a.sum b).Tempered :=
  fun φ hφ => (ha φ hφ).prodMap (hb φ hφ)

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h x y hx hy`. Proceed by induction on `x using WD.ind with`. Consider the case `hP n a`. Proceed by induction on `y using WD.ind with`. Consider the case `hP m b`.

Rewrite `hx`, `hy` using `[WD.tempered_mk]`. Rewrite using `[WD.lpSum_mk, WD.tempered_mk]`. Conclude with `hx.sum hy`.
-/
theorem WD.tempered_lpSum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (x.lpSum y).tempered := by
  intro E Ω _ _ _ _ _ A w h x y hx hy
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.tempered_mk] at hx hy
      rw [WD.lpSum_mk, WD.tempered_mk]
      exact hx.sum hy

end GlobalTheory.WeilDeligne
