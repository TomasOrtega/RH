import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.RootsIn

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.Mem.Col2
open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

def finOr {α : Type} (s : Set α) : Finset α := by
  classical
  exact if h : s.Finite then h.toFinset else ∅

/- English proof (translation)
Unfold `finOr`. Rewrite using `[dif_pos h, Set.Finite.mem_toFinset]`.
-/
theorem mem_finOr {α : Type} {s : Set α} (h : s.Finite) {x : α} : x ∈ finOr s ↔ x ∈ s := by
  unfold finOr
  rw [dif_pos h, Set.Finite.mem_toFinset]

def rootN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Simplify using `only [rootN, Nat.cast_zero, div_zero, Complex.exp_zero]`. Conclude with `isAlgebraic_one`. Establish `h : rootN N ^ N = 1` using `(Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one`. Conclude with `(IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)).isAlgebraic`.
-/
theorem rootN_isAlgebraic (N : ℕ) : IsAlgebraic ℚ (rootN N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [rootN, Nat.cast_zero, div_zero, Complex.exp_zero]
    exact isAlgebraic_one
  · have h : rootN N ^ N = 1 := (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one
    exact (IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)).isAlgebraic

def ramSet {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) : Set (HeightOneSpectrum (𝓞 E)) :=
  {Q | ¬ χ.UnrAt Q}

def overN {E : Type} [Field E] [NumberField E] (n : ℕ) : Set (HeightOneSpectrum (𝓞 E)) :=
  {Q' | ((n : ℕ) : 𝓞 E) ∈ Q'.asIdeal}

def rootsOf {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) : Finset ℂ := by
  classical
  exact (finOr (ramSet χ)).biUnion fun Q =>
    (finOr (overN (E := E) (Ideal.absNorm Q.asIdeal))).image fun Q' => rootN (Nat.card (kP Q'))

def Sv (P : Pre) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Finset ℂ := by
  classical
  exact (finOr Ξ).biUnion rootsOf

/- English proof (translation)
Unfold `Sv at hz`. Take `⟨χ, -, hχ⟩` from `Finset.mem_biUnion.1 hz`. Unfold `rootsOf at hχ`. Take `⟨Q, -, hQ⟩` from `Finset.mem_biUnion.1 hχ`. Take `⟨Q', -, rfl⟩` from `Finset.mem_image.1 hQ`.

Conclude with `rootN_isAlgebraic _`.
-/
theorem isAlgebraic_of_mem_Sv (P : Pre) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) (z : ℂ) (hz : z ∈ Sv P Ξ) : IsAlgebraic ℚ z := by
  unfold Sv at hz
  obtain ⟨χ, -, hχ⟩ := Finset.mem_biUnion.1 hz
  unfold rootsOf at hχ
  obtain ⟨Q, -, hQ⟩ := Finset.mem_biUnion.1 hχ
  obtain ⟨Q', -, rfl⟩ := Finset.mem_image.1 hQ
  exact rootN_isAlgebraic _

/- English proof (translation)
Establish `h` using `GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1`. Rewrite `h` using `[Filter.eventually_cofinite]`. Use `h.subset fun Q hQ => ?_` and prove the remaining obligations. Simplify using `only [ramSet, Set.mem_setOf_eq] at hQ ⊢`. Rewrite using `[GlobalTheory.HeckeSplit.unrAt_iff]` and apply the resulting hypothesis.
-/
theorem ramSet_finite {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) : (ramSet χ).Finite := by
  have h := GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun Q hQ => ?_
  simp only [ramSet, Set.mem_setOf_eq] at hQ ⊢
  rwa [GlobalTheory.HeckeSplit.unrAt_iff]

/- English proof (translation)
Establish `hne : (Ideal.span {((n : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hn` after adjusting the coercions. Use `(Ideal.finite_factors hne).subset fun Q hQ => ?_` and prove the remaining obligations. Simplify using `only [overN, Set.mem_setOf_eq] at hQ ⊢`.

Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hQ`.
-/
theorem overN_finite {E : Type} [Field E] [NumberField E] {n : ℕ} (hn : n ≠ 0) : (overN (E := E) n).Finite := by
  have hne : (Ideal.span {((n : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hne).subset fun Q hQ => ?_
  simp only [overN, Set.mem_setOf_eq] at hQ ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hQ

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Simplify using `only [Qprime, Set.mem_setOf_eq] at hv`. Apply `hv` to reduce the goal to its premises. Introduce `x hx`.

Rewrite using `[MonoidHom.mem_ker]`. Take `⟨a, rfl⟩` from `finAf_surjective F E x`. Simplify using `only [inertAt, Subgroup.mem_inf] at hx`. Take `⟨hx1, hx2⟩` from `hx`. Establish `hcomp : ∀ P : HeightOneSpectrum (𝓞 E), ((GlobalTheory.HeckeSplit.finPart E P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) = afIso F E (finAf F E a : AfE F E) P`.

Introduce `P`. Rewrite using `[afIso_finAf]`. Both sides reduce to the same expression. Establish `key : ξ.1 a = ξ.1 (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a))`. Rewrite using `[GlobalTheory.HeckeSplit.char_eq_prod_local ξ.1 ξ.2.1 a ∅ ?_, Finset.prod_empty, mul_one]`.

Introduce `P _`. Distinguish the cases in `hPv : P.under (𝓞 F) = v`. Apply `(GlobalTheory.HeckeSplit.unrAt_iff E ξ P).2 (hne P hPv)` to reduce the goal to its premises. Rewrite using `[hcomp]`. Simplify using `only [intU, Submonoid.mem_units_iff] at hx1`.

Establish `h1` using `(mem_rInt_iff F E _).1 hx1.1 P`. Establish `h2` using `(mem_rInt_iff F E _).1 hx1.2 P`. Establish `hprod : afIso F E (finAf F E a : AfE F E) P * afIso F E (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1`. Establish `h : afIso F E ((finAf F E a : AfE F E) * (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E)) P = 1`. Rewrite using `[Units.mul_inv, map_one]`.

Both sides reduce to the same expression. Rewrite `h` using `[map_mul]`. Conclude with `h`. Establish `hv' : Valued.v (afIso F E (finAf F E a : AfE F E) P) * Valued.v (afIso F E (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E) P) = 1`. Rewrite using `[← map_mul, hprod, map_one]`.

Use `le_antisymm h1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : GlobalTheory.HeckeSplit.finPart E P a = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hcomp, Units.val_one]`.

Conclude with `(mem_suppAt_iff F E v _).1 hx2 P hPv`. Rewrite using `[h1, map_one, map_one]`. Establish `hb : finAf F E (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a)) = 1`. Apply `Units.ext` to reduce the goal to its premises. Apply `(afIso F E).injective` to reduce the goal to its premises.

Rewrite using `[afIso_finAf, Units.val_one, map_one]`. Both sides reduce to the same expression. Establish `e1` using `h a`. Establish `e2` using `h (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a))`. Rewrite `e2` using `[hb, map_one, Units.val_one, map_one]`.

Rewrite `e1` using `[key, e2]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_one]`. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[map_one]`.

Conclude with `e1.symm`.
-/
theorem exists_ram {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K] {σ : K →+* ℂ}
    {μ : Chr F E K} {ξ : Formalism.L2.Host.HChar E} (h : Reads σ μ ξ) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ Qprime μ) :
    ∃ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v ∧ ¬ ξ.UnrAt Q := by
  by_contra hne
  push_neg at hne
  simp only [Qprime, Set.mem_setOf_eq] at hv
  apply hv
  intro x hx
  rw [MonoidHom.mem_ker]
  obtain ⟨a, rfl⟩ := finAf_surjective F E x
  simp only [inertAt, Subgroup.mem_inf] at hx
  obtain ⟨hx1, hx2⟩ := hx

  have hcomp : ∀ P : HeightOneSpectrum (𝓞 E),
      ((GlobalTheory.HeckeSplit.finPart E P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) =
        afIso F E (finAf F E a : AfE F E) P := by
    intro P
    rw [afIso_finAf]
    rfl

  have key : ξ.1 a = ξ.1 (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a)) := by
    rw [GlobalTheory.HeckeSplit.char_eq_prod_local ξ.1 ξ.2.1 a ∅ ?_, Finset.prod_empty, mul_one]
    intro P _
    by_cases hPv : P.under (𝓞 F) = v
    · apply (GlobalTheory.HeckeSplit.unrAt_iff E ξ P).2 (hne P hPv)
      rw [hcomp]
      simp only [intU, Submonoid.mem_units_iff] at hx1
      have h1 := (mem_rInt_iff F E _).1 hx1.1 P
      have h2 := (mem_rInt_iff F E _).1 hx1.2 P
      have hprod : afIso F E (finAf F E a : AfE F E) P *
          afIso F E (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
        have h : afIso F E ((finAf F E a : AfE F E) * (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E)) P = 1 := by
          rw [Units.mul_inv, map_one]
          rfl
        rw [map_mul] at h
        exact h
      have hv' : Valued.v (afIso F E (finAf F E a : AfE F E) P) *
          Valued.v (afIso F E (((finAf F E a)⁻¹ : (AfE F E)ˣ) : AfE F E) P) = 1 := by
        rw [← map_mul, hprod, map_one]
      refine le_antisymm h1 ?_
      calc (1 : _) = _ := hv'.symm
        _ ≤ Valued.v (afIso F E (finAf F E a : AfE F E) P) * 1 := by gcongr
        _ = _ := mul_one _
    · have h1 : GlobalTheory.HeckeSplit.finPart E P a = 1 := by
        apply Units.ext
        rw [hcomp, Units.val_one]
        exact (mem_suppAt_iff F E v _).1 hx2 P hPv
      rw [h1, map_one, map_one]
  have hb : finAf F E (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a)) = 1 := by
    apply Units.ext
    apply (afIso F E).injective
    rw [afIso_finAf, Units.val_one, map_one]
    rfl
  have e1 := h a
  have e2 := h (GlobalTheory.HeckeSplit.infIdele E (GlobalTheory.HeckeSplit.infPart E a))
  rw [hb, map_one, Units.val_one, map_one] at e2
  rw [key, e2] at e1
  apply Units.ext
  rw [Units.val_one]
  apply σ.injective
  rw [map_one]
  exact e1.symm

end GlobalTheory.Mem.Col2.RootsIn

open GlobalTheory.Mem.Col2.RootsIn in

/- English proof (translation)
Use `⟨GlobalTheory.Mem.Col2.RootsIn.Sv, fun P Ξ z hz => isAlgebraic_of_mem_Sv P Ξ z hz, ?_⟩` and prove the remaining obligations. Introduce `B px I hI hS`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a P _`. Conclude with `⟨_, (hI.xi_reads a _).symm⟩`.

Introduce `a P hP`. Take `⟨v, hv, hsel, -⟩` from `I.exists_of_mem_Q hP`. Take `⟨Q, hQv, hQ⟩` from `exists_ram (hI.xi_reads a) hv`. Establish `hPv : P.asIdeal.under (𝓞 B.fields.F) = v.asIdeal` using `hsel ▸ hI.sel_ok v`. Establish `hQP : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal`.

Establish `h2 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.F) ∈ P.asIdeal.under (𝓞 B.fields.F)`. Rewrite using `[hPv, ← hQv]`. Use `show _ ∈ Ideal.comap (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E)) Q.asIdeal`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.absNorm_mem _`.

Establish `h3 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.F) ∈ Ideal.comap (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E)) P.asIdeal` using `h2`. Rewrite `h3` using `[Ideal.mem_comap, map_natCast]`. Conclude with `h3`. Establish `hQ0 : Ideal.absNorm Q.asIdeal ≠ 0` using `fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Establish `hN : Nat.card (kP P) ≠ 0`.

Establish `hP0 : Ideal.absNorm P.asIdeal ≠ 0` using `fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Rewrite `hP0` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Then use the resulting hypothesis. Establish `hmem : rootN (Nat.card (kP P)) ∈ GlobalTheory.Mem.Col2.RootsIn.Sv B.toPre (Set.range I.xi)`. Unfold `GlobalTheory.Mem.Col2.RootsIn.Sv`. Use `Finset.mem_biUnion.2 ⟨I.xi a, (mem_finOr (Set.finite_range _)).2 ⟨a, rfl⟩, ?_⟩` and prove the remaining obligations.

Unfold `rootsOf`. Use `Finset.mem_biUnion.2 ⟨Q, (mem_finOr (ramSet_finite _)).2 hQ, ?_⟩` and prove the remaining obligations. Conclude with `Finset.mem_image.2 ⟨P, (mem_finOr (overN_finite hQ0)).2 hQP, rfl⟩`. Take `⟨z, hz⟩` from `(B.mem_LLC).1 (hS _ hmem)`. Use `⟨z, IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective⟩` and prove the remaining obligations.

Rewrite using `[hz]`. Conclude with `Complex.isPrimitiveRoot_exp _ hN`.
-/
theorem GlobalTheory.Mem.Col2.exists_roots_valsIn : ∃ Sv : ∀ P : Pre, Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ, (∀ P Ξ, ∀ z ∈ Sv P Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), I.Ok → (∀ z ∈ Sv B.toPre (Set.range I.xi), z ∈ B.LLC) → ValsIn I := by
  refine ⟨GlobalTheory.Mem.Col2.RootsIn.Sv, fun P Ξ z hz => isAlgebraic_of_mem_Sv P Ξ z hz, ?_⟩
  intro B px I hI hS
  refine ⟨?_, ?_⟩
  ·
    intro a P _
    exact ⟨_, (hI.xi_reads a _).symm⟩
  · intro a P hP
    obtain ⟨v, hv, hsel, -⟩ := I.exists_of_mem_Q hP
    obtain ⟨Q, hQv, hQ⟩ := exists_ram (hI.xi_reads a) hv
    have hPv : P.asIdeal.under (𝓞 B.fields.F) = v.asIdeal := hsel ▸ hI.sel_ok v

    have hQP : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
      have h2 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.F) ∈ P.asIdeal.under (𝓞 B.fields.F) := by
        rw [hPv, ← hQv]
        show _ ∈ Ideal.comap (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E)) Q.asIdeal
        rw [Ideal.mem_comap, map_natCast]
        exact Ideal.absNorm_mem _
      have h3 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 B.fields.F) ∈
          Ideal.comap (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E)) P.asIdeal := h2
      rw [Ideal.mem_comap, map_natCast] at h3
      exact h3
    have hQ0 : Ideal.absNorm Q.asIdeal ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have hN : Nat.card (kP P) ≠ 0 := by
      have hP0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hP0
    have hmem : rootN (Nat.card (kP P)) ∈ GlobalTheory.Mem.Col2.RootsIn.Sv B.toPre (Set.range I.xi) := by
      unfold GlobalTheory.Mem.Col2.RootsIn.Sv
      refine Finset.mem_biUnion.2 ⟨I.xi a, (mem_finOr (Set.finite_range _)).2 ⟨a, rfl⟩, ?_⟩
      unfold rootsOf
      refine Finset.mem_biUnion.2 ⟨Q, (mem_finOr (ramSet_finite _)).2 hQ, ?_⟩
      exact Finset.mem_image.2 ⟨P, (mem_finOr (overN_finite hQ0)).2 hQP, rfl⟩
    obtain ⟨z, hz⟩ := (B.mem_LLC).1 (hS _ hmem)
    refine ⟨z, IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective⟩
    rw [hz]
    exact Complex.isPrimitiveRoot_exp _ hN
