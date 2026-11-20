import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ P : HeightOneSpectrum (𝓞 E), ι x P = afIso F E x P`. Introduce `P`. Establish `ev : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a + b) P = a P + b P` using `fun _ _ => rfl`. Establish `evm : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a * b) P = a P * b P` using `fun _ _ => rfl`. Establish `evn : ∀ n : ℕ, ((n : FiniteAdeleRing (𝓞 E) E)) P = (n : P.adicCompletion E)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Nat.cast_succ, ev, ih, Nat.cast_succ]`. Both sides reduce to the same expression.

Rewrite using `[← sub_eq_zero]`. Assume the negation of the conclusion as `hne`. Use `set d := ι x P - afIso F E x P with hd`. Establish `hv : Valued.v d ≠ 0` using `(Valuation.ne_zero_iff _).2 hne`. Take `⟨y, N, r, hr, hN, e⟩` from `exists_approx_small (F := F) (E := E) x {P} hv`.

Establish `hNP` using `hN P (Finset.mem_singleton_self P)`. Establish `h1 : ι (Formalism.UG.inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) y) = afIso F E (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) := by show ι (y ⊗ₜ[F] 1) = afIso F E (y ⊗ₜ[F] 1)`. Rewrite using `[hι.1, afIso_tmul_one]`. Establish `hd2 : d = (N : P.adicCompletion E) * (ι r P - afIso F E r P)`. Rewrite using `[hd, e, map_add, map_add, h1, map_mul, map_mul, map_natCast, map_natCast]`.

Rewrite using `[ev, ev, evm, evm, evn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr1 : Valued.v (ι r P) ≤ 1` using `(hι.2 r).1 hr P`. Establish `hr2 : Valued.v (afIso F E r P) ≤ 1` using `(mem_rInt_iff F E r).1 hr P`. Establish `hsub : Valued.v (ι r P - afIso F E r P) ≤ 1` using `(Valuation.map_sub _ _ _).trans (max_le hr1 hr2)`.

Establish `hle : Valued.v d ≤ Valued.v (N : P.adicCompletion E)`. Rewrite using `[hd2, map_mul]`. Conclude with `mul_le_of_le_one_right' hsub`. Conclude with `lt_irrefl _ (hle.trans_lt hNP)`. Conclude with `Subtype.ext (funext key)`.
-/
theorem isAdIso_eq_afIso (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (hι : GlobalTheory.TwU.IsAdIso ι) (x : AfE F E) : ι x = afIso F E x := by
  have key : ∀ P : HeightOneSpectrum (𝓞 E), ι x P = afIso F E x P := by
    intro P
    have ev : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a + b) P = a P + b P := fun _ _ => rfl
    have evm : ∀ a b : FiniteAdeleRing (𝓞 E) E, (a * b) P = a P * b P := fun _ _ => rfl
    have evn : ∀ n : ℕ, ((n : FiniteAdeleRing (𝓞 E) E)) P = (n : P.adicCompletion E) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Nat.cast_succ, ev, ih, Nat.cast_succ]; rfl
    rw [← sub_eq_zero]
    by_contra hne
    set d := ι x P - afIso F E x P with hd
    have hv : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := F) (E := E) x {P} hv
    have hNP := hN P (Finset.mem_singleton_self P)
    have h1 : ι (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) = afIso F E (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) := by
      show ι (y ⊗ₜ[F] 1) = afIso F E (y ⊗ₜ[F] 1)
      rw [hι.1, afIso_tmul_one]
    have hd2 : d = (N : P.adicCompletion E) * (ι r P - afIso F E r P) := by
      rw [hd, e, map_add, map_add, h1, map_mul, map_mul, map_natCast, map_natCast]
      rw [ev, ev, evm, evm, evn]
      ring
    have hr1 : Valued.v (ι r P) ≤ 1 := (hι.2 r).1 hr P
    have hr2 : Valued.v (afIso F E r P) ≤ 1 := (mem_rInt_iff F E r).1 hr P
    have hsub : Valued.v (ι r P - afIso F E r P) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le hr1 hr2)
    have hle : Valued.v d ≤ Valued.v (N : P.adicCompletion E) := by
      rw [hd2, map_mul]
      exact mul_le_of_le_one_right' hsub
    exact lt_irrefl _ (hle.trans_lt hNP)
  exact Subtype.ext (funext key)

end GlobalTheory
