import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet

/- English proof (translation)
Take `⟨s, hs⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ k).FG)`. Establish `hroot : ∀ a : k, ∃ S : Set ℂ, S.Finite ∧ ∀ σ : k →+* ℂ, σ a ∈ S`. Introduce `a`. Take `⟨P, hm, hP⟩` from `(Algebra.IsIntegral.isIntegral a : IsIntegral ℤ a)`. Use `⟨{z | (P.map (Int.castRingHom ℂ)).IsRoot z}, ?_, fun σ => ?_⟩` and prove the remaining obligations.

Conclude with `Polynomial.finite_setOf_isRoot (hm.map _).ne_zero`. Establish `h : Polynomial.eval₂ (σ.comp (algebraMap ℤ k)) (σ a) P = 0`. Rewrite using `[← Polynomial.hom_eval₂, hP, map_zero]`. Rewrite `h` using `[Subsingleton.elim (σ.comp (algebraMap ℤ k)) (Int.castRingHom ℂ)]`. Simplify `h` using `[Polynomial.IsRoot, Polynomial.eval_map]`.

Use `choose S hS hm using hroot`. Establish `: ∀ i : s, Finite (S i)` using `fun i => (hS i).to_subtype`. Use `Finite.of_injective (fun (σ : k →+* ℂ) (i : s) => (⟨σ i, hm i σ⟩ : S i)) fun σ₁ σ₂ h => ?_` and prove the remaining obligations. Establish `hs' : ∀ i ∈ s, σ₁ i = σ₂ i` using `fun i hi => congrArg Subtype.val (congrFun h ⟨i, hi⟩)`. Establish `hspan : ∀ x ∈ Submodule.span ℤ (s : Set k), σ₁ x = σ₂ x`.

Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact hs' x h`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [map_add, hx, hy]`.

Consider the case `smul a x _ hx => simp [map_zsmul, hx]`. Conclude with `RingHom.ext fun x => hspan x (hs ▸ Submodule.mem_top)`.
-/
theorem finite_ringHom (k : Type) [CommRing k] [Module.Finite ℤ k] : Finite (k →+* ℂ) := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ k).FG)
  have hroot : ∀ a : k, ∃ S : Set ℂ, S.Finite ∧ ∀ σ : k →+* ℂ, σ a ∈ S := by
    intro a
    obtain ⟨P, hm, hP⟩ := (Algebra.IsIntegral.isIntegral a : IsIntegral ℤ a)
    refine ⟨{z | (P.map (Int.castRingHom ℂ)).IsRoot z}, ?_, fun σ => ?_⟩
    · exact Polynomial.finite_setOf_isRoot (hm.map _).ne_zero
    · have h : Polynomial.eval₂ (σ.comp (algebraMap ℤ k)) (σ a) P = 0 := by
        rw [← Polynomial.hom_eval₂, hP, map_zero]
      rw [Subsingleton.elim (σ.comp (algebraMap ℤ k)) (Int.castRingHom ℂ)] at h
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using h
  choose S hS hm using hroot
  have : ∀ i : s, Finite (S i) := fun i => (hS i).to_subtype
  refine Finite.of_injective (fun (σ : k →+* ℂ) (i : s) => (⟨σ i, hm i σ⟩ : S i)) fun σ₁ σ₂ h => ?_
  have hs' : ∀ i ∈ s, σ₁ i = σ₂ i := fun i hi => congrArg Subtype.val (congrFun h ⟨i, hi⟩)
  have hspan : ∀ x ∈ Submodule.span ℤ (s : Set k), σ₁ x = σ₂ x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => exact hs' x h
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul a x _ hx => simp [map_zsmul, hx]
  exact RingHom.ext fun x => hspan x (hs ▸ Submodule.mem_top)

variable {k : Type} [CommRing k] {X : Scheme.{0}}

/- English proof (translation)
The claim follows from `(ev_algX (y := unsheet p y) mem_ptsIn_top a).symm`.
-/
theorem emb_apply (p : X ⟶ Sp k) {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ} (y : CxPts t τ) (a : k) :
    emb p y a = ev t τ ⊤ (algX p ⊤ a) y :=
  (ev_algX (y := unsheet p y) mem_ptsIn_top a).symm

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Conclude with `emb_sheet t τ z`. Introduce `h`.

Establish `h' : emb p y = σ` using `h`. Substitute `h'` using the available equality. Conclude with `⟨unsheet p y, rfl⟩`.
-/
theorem range_sheet (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact emb_sheet t τ z
  · intro h
    have h' : emb p y = σ := h
    subst h'
    exact ⟨unsheet p y, rfl⟩

/- English proof (translation)
Establish `hc (a : k) : Continuous fun y : CxPts t τ => emb p y a`. Simplify using `only [emb_apply]`. Conclude with `(Points.continuous_valR_top _).comp continuous_subtype_val`. Establish `e : {y : CxPts t τ | emb p y = σ} = ⋂ σ' : {s : k →+* ℂ // s ≠ σ}, ⋃ a : k, {y | emb p y a ≠ σ'.1 a}`. Use extensionality with `y`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl σ'`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `σ'.2 (RingHom.ext fun a => (h a).symm)`. Introduce `h`. Assume the negation of the conclusion as `he`. Take `⟨a, ha⟩` from `h ⟨_, he⟩`. Conclude with `ha rfl`.

Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun σ' => isOpen_iUnion fun a => isOpen_ne_fun (hc a) continuous_const`.
-/
theorem isOpen_emb_eq [Finite (k →+* ℂ)] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    IsOpen {y : CxPts t τ | emb p y = σ} := by
  have hc (a : k) : Continuous fun y : CxPts t τ => emb p y a := by
    simp only [emb_apply]
    exact (Points.continuous_valR_top _).comp continuous_subtype_val
  have e : {y : CxPts t τ | emb p y = σ} =
      ⋂ σ' : {s : k →+* ℂ // s ≠ σ}, ⋃ a : k, {y | emb p y a ≠ σ'.1 a} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · rintro rfl σ'
      by_contra h
      push Not at h
      exact σ'.2 (RingHom.ext fun a => (h a).symm)
    · intro h
      by_contra he
      obtain ⟨a, ha⟩ := h ⟨_, he⟩
      exact ha rfl
  rw [e]
  exact isOpen_iInter_of_finite fun σ' => isOpen_iUnion fun a => isOpen_ne_fun (hc a) continuous_const

/- English proof (translation)
Introduce `k _ _ X p t τ σ`. Use `finite_ringHom k` as an intermediate fact. Establish `hr` using `range_sheet p t τ σ`. Use `⟨⟨IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val IsEmbedding.subtypeVal, ?_⟩, hr⟩` and prove the remaining obligations. Rewrite using `[hr]`.

Conclude with `isOpen_emb_eq p t τ σ`.
-/
theorem isOpenEmbedding_and_range : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ), Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) ∧ Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  intro k _ _ X p t τ σ
  have := finite_ringHom k
  have hr := range_sheet p t τ σ
  refine ⟨⟨IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
    IsEmbedding.subtypeVal, ?_⟩, hr⟩
  rw [hr]
  exact isOpen_emb_eq p t τ σ

end GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet
