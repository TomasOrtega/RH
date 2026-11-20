import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
  (Algebra.lmul ℂ (Fin g → ℂ)).toRingHom.comp (Pi.ringHom fun i => (ty i).comp (algebraMap (𝓞 E) E))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagAct_apply (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (i : Fin g) :
    diagAct ty a x i = ty i (a : E) * x i := rfl

/- English proof (translation)
The claim follows from `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)`.
-/
theorem embedding_eq_of_integers {s t : E →+* ℂ} (h : ∀ a : 𝓞 E, s (a : E) = t (a : E)) : s = t :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

/- English proof (translation)
Establish `key : ∀ (a : 𝓞 E) (i : Fin g), ((diagAct ty a - (s.comp (algebraMap (𝓞 E) E)) a • LinearMap.id : Module.End ℂ (Fin g → ℂ)) x) i = (ty i (a : E) - s (a : E)) * x i`. Introduce `a i`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, diagAct_apply, RingHom.comp_apply]`. Put the polynomial expressions in normal form. Simplify using `only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]`.

Prove the components needed by the constructor for the conclusion. Introduce `h i hi`. Assume the negation of the conclusion as `hx`. Use `hi (embedding_eq_of_integers fun a => ?_)` and prove the remaining obligations. Establish `h1` using `congrFun (h a) i`.

Rewrite `h1` using `[key]`. Simplify `h1` using `[hx, sub_eq_zero]`. Introduce `h a`. Use function extensionality and compare the values at `i`. Rewrite using `[key]`.

Distinguish the cases in `hi : ty i = s`. Simplify using `[hi]`. Simplify using `[h i hi]`.
-/
theorem mem_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) (x : Fin g → ℂ) :
    x ∈ eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ↔ ∀ i, ty i ≠ s → x i = 0 := by
  have key : ∀ (a : 𝓞 E) (i : Fin g),
      ((diagAct ty a - (s.comp (algebraMap (𝓞 E) E)) a • LinearMap.id : Module.End ℂ (Fin g → ℂ)) x) i = (ty i (a : E) - s (a : E)) * x i := by
    intro a i
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      diagAct_apply, RingHom.comp_apply]
    ring_nf
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i hi
    by_contra hx
    refine hi (embedding_eq_of_integers fun a => ?_)
    have h1 := congrFun (h a) i
    rw [key] at h1
    simpa [hx, sub_eq_zero] using h1
  · intro h a
    funext i
    rw [key]
    by_cases hi : ty i = s
    · simp [hi]
    · simp [h i hi]

def eigSpDiagEquiv (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ≃ₗ[ℂ] ({i // ty i = s} → ℂ) where
  toFun x j := x.1 j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun i => open Classical in if h : ty i = s then f ⟨i, h⟩ else 0,
    (mem_eigSp_diagAct ty s _).2 fun i hi => by simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases h : ty i = s
    · simp [h]
    · simp [h, (mem_eigSp_diagAct ty s x.1).1 x.2 i h]
  right_inv f := by
    funext j
    simp [j.2]

/- English proof (translation)
Rewrite using `[(eigSpDiagEquiv ty s).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]`.
-/
theorem finrank_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = Nat.card {i // ty i = s} := by
  classical
  rw [(eigSpDiagEquiv ty s).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Diag

/- English proof (translation)
Set `L : Submodule ℤ (Fin g → ℂ)` to `P.range.toIntSubmodule`. Use `haveI : DiscreteTopology L := hd`. Use `haveI : IsZLattice ℝ L := ⟨by`. Establish `: ((L : Set (Fin g → ℂ))) = Set.range P`. Use extensionality with `x`.

Simplify using `[L]`. Rewrite using `[this, hs]⟩`. Set `e : Λ ≃ₗ[ℤ] L` to `(AddMonoidHom.ofInjective hi).toIntLinearEquiv`. Use `haveI : Module.Free ℤ L := ZLattice.module_free ℝ L`. Use `haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L`.

Use `⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex, mul_comm]`.
-/
theorem free_of_period {Λ : Type} [AddCommGroup Λ] {g : ℕ} (P : Λ →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    have : ((L : Set (Fin g → ℂ))) = Set.range P := by
      ext x; simp [L]
    rw [this, hs]⟩
  let e : Λ ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/- English proof (translation)
Introduce `E _ _ _ H D g ty P hty hP`. Take `⟨hact, hinj, hdisc, hspan, Hm, hherm, hpos, him⟩` from `hP`. Take `⟨hfree, hfin, hrank⟩` from `free_of_period P hinj hdisc hspan`. Use `⟨{ free := hfree, fin := hfin, rank := hrank, form := D.EF, alt := D.alt, unimod := D.unimod adj := ?_, P := P, Hm := Hm, herm := hherm, pos := hpos, im := him, B := diagAct ty, act := ?_ }, rfl, rfl, fun a x i => diagAct_apply ty a x i, fun s => ?_⟩` and prove the remaining obligations. Introduce `a a' h x y`.

Establish `: a' = H.bar a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq a]`. Conclude with `h`. Rewrite using `[this]`.

Conclude with `D.adj a x y`. Introduce `a x`. Use function extensionality and compare the values at `i`. Conclude with `hact a x i`. Use `show Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = _`.

Rewrite using `[finrank_eigSp_diagAct]`. Distinguish the cases in `h : s (H.rt : E) = H.rt0`. Rewrite using `[if_pos h]`. Conclude with `(hty s).1 h`. Rewrite using `[if_neg h]`.

Conclude with `(hty s).2 h`.
-/
theorem riemLat_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P → ∃ R : RiemLat E g D.La, R.P = P ∧ R.form = D.EF ∧ (∀ a x i, R.B a x i = ty i (a : E) * x i) ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q := by
  intro E _ _ _ H D g ty P hty hP
  obtain ⟨hact, hinj, hdisc, hspan, Hm, hherm, hpos, him⟩ := hP
  obtain ⟨hfree, hfin, hrank⟩ := free_of_period P hinj hdisc hspan
  refine ⟨{ free := hfree, fin := hfin, rank := hrank, form := D.EF, alt := D.alt, unimod := D.unimod
            adj := ?_, P := P, Hm := Hm, herm := hherm, pos := hpos, im := him, B := diagAct ty, act := ?_ },
    rfl, rfl, fun a x i => diagAct_apply ty a x i, fun s => ?_⟩
  · intro a a' h x y
    have : a' = H.bar a := by
      apply RingOfIntegers.ext
      rw [H.bar_eq a]
      exact h
    rw [this]
    exact D.adj a x y
  · intro a x
    funext i
    exact hact a x i
  · show Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = _
    rw [finrank_eigSp_diagAct]
    by_cases h : s (H.rt : E) = H.rt0
    · rw [if_pos h]
      exact (hty s).1 h
    · rw [if_neg h]
      exact (hty s).2 h

end GlobalTheory.CompanionTheory.Ar.Cusp
