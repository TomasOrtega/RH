import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

/- English proof (translation)
Introduce `E _ _ _ H Dw _ l Xo c C A hA hirr hne`. Take `⟨_, hyA, y, rfl⟩` from `hne`. Establish `hζ : IsGenericPoint hirr.genericPoint A` using `hirr.isGenericPoint_genericPoint hA.isClosed`. Use `set ζ := hirr.genericPoint`. Establish `h1 : ζ ⤳ C.i y` using `hζ.specializes hyA`.

Establish `hcomp : C.z (C.i y) = spMap C.b (pullback.snd C.z (spMap C.b) (C.iF y))`. Use `congrArg (fun f => f.base (C.iF y)) (pullback.condition (f := C.z) (g := spMap C.b))` as an intermediate fact. Simplify using `using this`. Establish `hbot : ∀ q : Sp c.F, (spMap C.b q).asIdeal = ⊥`. Introduce `q`.

Use `haveI := q.isPrime`. Establish `hq : q.asIdeal = ⊥` using `Ideal.eq_bot_of_prime q.asIdeal`. Use `show Ideal.comap C.b q.asIdeal = ⊥`. Rewrite using `[hq]`. Conclude with `Ideal.comap_bot_of_injective C.b C.inj`.

Establish `h2 : C.z ζ = C.z (C.i y)`. Establish `hs : C.z ζ ⤳ C.z (C.i y)` using `h1.map C.z.continuous`. Establish `hle : (C.z ζ).asIdeal ≤ (C.z (C.i y)).asIdeal` using `(PrimeSpectrum.le_iff_specializes _ _).2 hs`. Rewrite `hle` using `[hcomp, hbot]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Rewrite using `[hcomp, hbot]`. Conclude with `le_bot_iff.1 hle`. Take `⟨p', hp', -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := C.z) (g := spMap C.b) ζ (pullback.snd C.z (spMap C.b) (C.iF y)) (h2.trans hcomp)`. Use `haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := by`. Use `letI := C.b.toAlgebra`.

Use `haveI := C.isFractionRing`. Use `haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)`. Use `infer_instance`. Establish `h3 : p' ⤳ C.iF y`. Apply `(IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).specializes_iff.1` to reduce the goal to its premises.

Rewrite using `[hp']`. Conclude with `h1`. Use `haveI := C.iF_open`. Take `⟨η, hη⟩` from `h3.mem_open C.iF.isOpenEmbedding.isOpen_range ⟨y, rfl⟩`. Establish `hCi : C.i η = ζ`.

Rewrite using `[← hp', ← hη]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective C.i` using `(IsPreimmersion.isEmbedding C.i).injective`. Use `⟨η, ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩, by rw [hCi]; exact hζ⟩` and prove the remaining obligations. Establish `hη' : IsGenericPoint hT.closure.genericPoint (closure T)` using `hT.closure.isGenericPoint_genericPoint isClosed_closure`.

Establish `hs : hT.closure.genericPoint ⤳ η` using `hη'.specializes (subset_closure (hle (subset_closure rfl)))`. Establish `hs' : C.i hT.closure.genericPoint ⤳ ζ` using `hCi ▸ hs.map C.i.continuous`. Establish `hmem : C.i hT.closure.genericPoint ∈ A` using `hs'.mem_open hA.isOpen hζ.mem`. Establish `heq : hT.closure.genericPoint = η` using `hinj ((hs'.antisymm (hζ.specializes hmem)).eq.trans hCi.symm)`. Rewrite using `[← heq, hη']`.

Conclude with `subset_closure`.
-/
theorem exists_genericPoint_closure_eq_of_isClopen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∃ η ∈ genericPoints (Xo.XF c), closure {C.i η} = A := by
  intro E _ _ _ H Dw _ l Xo c C A hA hirr hne
  obtain ⟨_, hyA, y, rfl⟩ := hne
  have hζ : IsGenericPoint hirr.genericPoint A := hirr.isGenericPoint_genericPoint hA.isClosed
  set ζ := hirr.genericPoint
  have h1 : ζ ⤳ C.i y := hζ.specializes hyA
  have hcomp : C.z (C.i y) = spMap C.b (pullback.snd C.z (spMap C.b) (C.iF y)) := by
    have := congrArg (fun f => f.base (C.iF y)) (pullback.condition (f := C.z) (g := spMap C.b))
    simpa using this
  have hbot : ∀ q : Sp c.F, (spMap C.b q).asIdeal = ⊥ := by
    intro q
    haveI := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
    show Ideal.comap C.b q.asIdeal = ⊥
    rw [hq]
    exact Ideal.comap_bot_of_injective C.b C.inj
  have h2 : C.z ζ = C.z (C.i y) := by
    have hs : C.z ζ ⤳ C.z (C.i y) := h1.map C.z.continuous
    have hle : (C.z ζ).asIdeal ≤ (C.z (C.i y)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 hs
    rw [hcomp, hbot] at hle
    apply PrimeSpectrum.ext
    rw [hcomp, hbot]
    exact le_bot_iff.1 hle
  obtain ⟨p', hp', -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.z) (g := spMap C.b) ζ
    (pullback.snd C.z (spMap C.b) (C.iF y)) (h2.trans hcomp)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := by
    letI := C.b.toAlgebra
    haveI := C.isFractionRing
    haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
    infer_instance
  have h3 : p' ⤳ C.iF y := by
    apply (IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).specializes_iff.1
    rw [hp']
    exact h1
  haveI := C.iF_open
  obtain ⟨η, hη⟩ := h3.mem_open C.iF.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  have hCi : C.i η = ζ := by
    rw [← hp', ← hη]
    rfl
  have hinj : Function.Injective C.i := (IsPreimmersion.isEmbedding C.i).injective
  refine ⟨η, ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩, by rw [hCi]; exact hζ⟩
  have hη' : IsGenericPoint hT.closure.genericPoint (closure T) :=
    hT.closure.isGenericPoint_genericPoint isClosed_closure
  have hs : hT.closure.genericPoint ⤳ η := hη'.specializes (subset_closure (hle (subset_closure rfl)))
  have hs' : C.i hT.closure.genericPoint ⤳ ζ := hCi ▸ hs.map C.i.continuous
  have hmem : C.i hT.closure.genericPoint ∈ A := hs'.mem_open hA.isOpen hζ.mem
  have heq : hT.closure.genericPoint = η := hinj ((hs'.antisymm (hζ.specializes hmem)).eq.trans hCi.symm)
  rw [← heq, hη']
  exact subset_closure

end GlobalTheory.UPoinc
