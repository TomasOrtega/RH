import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrbitRel

open Formalism.MainNotions.S.Loc ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

/- English proof (translation)
Unfold `Formalism.MainNotions.S.LocNG.FPair.UW0 at hg`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩`. Consider the case `mul x y _ _ hx hy`.

Use `⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `show H.h (x (y u)) (x (y v)) = H.h u v`. Rewrite using `[hx.1, hy.1]`. Use `show x (y (P.A.f b)) = P.A.f b`. Rewrite using `[(hy.2 b).1, (hx.2 b).1]`.

Use `show x (y (P.B.f b)) = P.B.f b`. Rewrite using `[(hy.2 b).2, (hx.2 b).2]`. Consider the case `inv x _ hx`. Use `⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `show H.h (x.symm u) (x.symm v) = H.h u v`.

Use `hx.1 (x.symm u) (x.symm v)` as an intermediate fact. Simplify using `using this.symm`. Use `show x.symm (P.A.f b) = P.A.f b conv_lhs => rw [← (hx.2 b).1]`. Simplify using the standard rewrite rules. Use `show x.symm (P.B.f b) = P.B.f b conv_lhs => rw [← (hx.2 b).2]`.

Simplify using the standard rewrite rules.
-/
theorem framePairFixator_unitary_and_fixes_frame (P : Formalism.MainNotions.S.LocNG.FPair H r) {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    Formalism.MainNotions.S.LocNG.IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  unfold Formalism.MainNotions.S.LocNG.FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x (y u)) (x (y v)) = H.h u v
      rw [hx.1, hy.1]
    · show x (y (P.A.f b)) = P.A.f b
      rw [(hy.2 b).1, (hx.2 b).1]
    · show x (y (P.B.f b)) = P.B.f b
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x.symm u) (x.symm v) = H.h u v
      have := hx.1 (x.symm u) (x.symm v)
      simpa using this.symm
    · show x.symm (P.A.f b) = P.A.f b
      conv_lhs => rw [← (hx.2 b).1]
      simp
    · show x.symm (P.B.f b) = P.B.f b
      conv_lhs => rw [← (hx.2 b).2]
      simp

/- English proof (translation)
Introduce `v hv`. Establish `hfix : Set.EqOn (g : V →ₗ[E] V) (LinearMap.id : V →ₗ[E] V) (Set.range fun a : Fin r => f a.castSucc)`. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `using hf a.castSucc`. Establish `hv' : g v = v` using `LinearMap.eqOn_span' hfix hv`.

Use `hu x v` as an intermediate fact. Rewrite `this` using `[hv']`. Rewrite using `[this]`. Conclude with `hx v hv`.
-/
theorem perp_stable {g : V ≃ₗ[E] V} (hu : Formalism.MainNotions.S.LocNG.IsUnitary H g) {f : Fin (r + 1) → V}
    (hf : ∀ b, g (f b) = f b) {x : V} (hx : x ∈ H.perp (H.X f)) : g x ∈ H.perp (H.X f) := by
  intro v hv
  have hfix : Set.EqOn (g : V →ₗ[E] V) (LinearMap.id : V →ₗ[E] V) (Set.range fun a : Fin r => f a.castSucc) := by
    rintro _ ⟨a, rfl⟩
    simpa using hf a.castSucc
  have hv' : g v = v := LinearMap.eqOn_span' hfix hv
  have := hu x v
  rw [hv'] at this
  rw [this]
  exact hx v hv

/- English proof (translation)
Use `⟨fun d => ?_, fun {d d'} h => ?_, fun {d d' d''} h h' => ?_⟩` and prove the remaining obligations. Use `⟨1, P.UW0.one_mem, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Establish `: y = x` using `Subtype.ext (by simpa using hxy)`. Substitute `this` using the available equality.

Conclude with `Iff.rfl`. Introduce `x y hxy`. Establish `: y = x` using `Subtype.ext (by simpa using hxy)`. Substitute `this` using the available equality. Conclude with `Iff.rfl`.

Introduce `x' y' x y hx' hx`. Establish `e1 : y' = x'` using `Subtype.ext (by simpa using hx')`. Establish `e2 : y = x` using `Subtype.ext (by simpa using hx)`. Substitute `e1` using the available equality. Substitute `e2` using the available equality.

Conclude with `Iff.rfl`. Take `⟨g, hg, h1, h2, h3⟩` from `h`. Use `⟨g⁻¹, P.UW0.inv_mem hg, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Establish `: (x : V) = g y` using `by rw [hxy]; show (x : V) = g (g.symm x); simp`.

Conclude with `(h1 y x this).symm`. Introduce `x y hxy`. Establish `: (x : V) = g y` using `by rw [hxy]; show (x : V) = g (g.symm x); simp`. Conclude with `(h2 y x this).symm`. Introduce `x' y' x y hx' hx`.

Establish `a1 : (x' : V) = g y'` using `by rw [hx']; show (x' : V) = g (g.symm x'); simp`. Establish `a2 : (x : V) = g y` using `by rw [hx]; show (x : V) = g (g.symm x); simp`. Conclude with `(h3 y' x' y x a1 a2).symm`. Take `⟨g, hg, h1, h2, h3⟩` from `h`. Take `⟨g', hg', h1', h2', h3'⟩` from `h'`.

Establish `hs` using `framePairFixator_unitary_and_fixes_frame P hg`. Use `⟨g' * g, P.UW0.mul_mem hg' hg, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Set `z : ↥(H.perp (H.X P.A.f))` to `⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩`. Conclude with `(h1 x z rfl).trans (h1' z y hxy)`.

Introduce `x y hxy`. Set `z : ↥(H.perp (H.X P.B.f))` to `⟨g x, perp_stable hs.1 (fun b => (hs.2 b).2) x.2⟩`. Conclude with `(h2 x z rfl).trans (h2' z y hxy)`. Introduce `x' y' x y hx' hx`. Set `z' : ↥(H.perp (H.X P.B.f))` to `⟨g x', perp_stable hs.1 (fun b => (hs.2 b).2) x'.2⟩`.

Set `z : ↥(H.perp (H.X P.A.f))` to `⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩`. Conclude with `(h3 x' z' x z rfl rfl).trans (h3' z' y' z y hx' hx)`.
-/
theorem rel_equivalence (P : Formalism.MainNotions.S.LocNG.FPair H r) :
    Equivalence (Formalism.MainNotions.S.LocNG.Datum.Rel (P := P)) := by
  refine ⟨fun d => ?_, fun {d d'} h => ?_, fun {d d' d''} h h' => ?_⟩
  · refine ⟨1, P.UW0.one_mem, ?_, ?_, ?_⟩
    · intro x y hxy
      have : y = x := Subtype.ext (by simpa using hxy)
      subst this; exact Iff.rfl
    · intro x y hxy
      have : y = x := Subtype.ext (by simpa using hxy)
      subst this; exact Iff.rfl
    · intro x' y' x y hx' hx
      have e1 : y' = x' := Subtype.ext (by simpa using hx')
      have e2 : y = x := Subtype.ext (by simpa using hx)
      subst e1; subst e2; exact Iff.rfl
  · obtain ⟨g, hg, h1, h2, h3⟩ := h
    refine ⟨g⁻¹, P.UW0.inv_mem hg, ?_, ?_, ?_⟩
    · intro x y hxy
      have : (x : V) = g y := by rw [hxy]; show (x : V) = g (g.symm x); simp
      exact (h1 y x this).symm
    · intro x y hxy
      have : (x : V) = g y := by rw [hxy]; show (x : V) = g (g.symm x); simp
      exact (h2 y x this).symm
    · intro x' y' x y hx' hx
      have a1 : (x' : V) = g y' := by rw [hx']; show (x' : V) = g (g.symm x'); simp
      have a2 : (x : V) = g y := by rw [hx]; show (x : V) = g (g.symm x); simp
      exact (h3 y' x' y x a1 a2).symm
  · obtain ⟨g, hg, h1, h2, h3⟩ := h
    obtain ⟨g', hg', h1', h2', h3'⟩ := h'
    have hs := framePairFixator_unitary_and_fixes_frame P hg
    refine ⟨g' * g, P.UW0.mul_mem hg' hg, ?_, ?_, ?_⟩
    · intro x y hxy
      let z : ↥(H.perp (H.X P.A.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩
      exact (h1 x z rfl).trans (h1' z y hxy)
    · intro x y hxy
      let z : ↥(H.perp (H.X P.B.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).2) x.2⟩
      exact (h2 x z rfl).trans (h2' z y hxy)
    · intro x' y' x y hx' hx
      let z' : ↥(H.perp (H.X P.B.f)) :=
        ⟨g x', perp_stable hs.1 (fun b => (hs.2 b).2) x'.2⟩
      let z : ↥(H.perp (H.X P.A.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩
      exact (h3 x' z' x z rfl rfl).trans (h3' z' y' z y hx' hx)

/- English proof (translation)
Introduce `_ _ FP p` and use `rel_equivalence (FP p)`.
-/
theorem relEqv : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS)
    (p : PlF D), Equivalence (Formalism.MainNotions.S.LocNG.Datum.Rel (P := FP p)) :=
  fun _ _ FP p => rel_equivalence (FP p)

end GlobalTheory.OrbitRel
