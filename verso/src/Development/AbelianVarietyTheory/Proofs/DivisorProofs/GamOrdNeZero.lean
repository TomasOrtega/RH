import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7}

def gfcToGf (V : HSp D) : GfC V →* Bridge.Gf V := (finHom V).rangeRestrict.comp (GfC V).subtype

/- English proof (translation)
Introduce and unpack `⟨_, h, rfl⟩`. Take `⟨k, hk, e⟩` from `GlobalTheory.VolHeckeCompare.exists_finite_part V h`. Conclude with `⟨⟨k, hk⟩, Subtype.ext e⟩`.
-/
theorem gfcToGf_surjective (V : HSp D) : Function.Surjective (gfcToGf V) := by
  rintro ⟨_, h, rfl⟩
  obtain ⟨k, hk, e⟩ := GlobalTheory.VolHeckeCompare.exists_finite_part V h
  exact ⟨⟨k, hk⟩, Subtype.ext e⟩

/- English proof (translation)
Introduce `a b e`. Apply `Units.ext` to reduce the goal to its premises. Establish `h` using `congrArg Units.val e`. Conclude with `Matrix.map_injective (f := Lev.swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h`.
-/
theorem bc_swapAE_injective (n : ℕ) :
    Function.Injective (Formalism.UG.bc (Lev.swapAE D) : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →* _) := by
  intro a b e
  apply Units.ext
  have h := congrArg Units.val e
  exact Matrix.map_injective (f := Lev.swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

/- English proof (translation)
Introduce `a b e`. Establish `e' : finHom V a.1 = finHom V b.1` using `bc_swapAE_injective V.rank e`. Establish `h1 : finHom V (a.1⁻¹ * b.1) = 1` using `by rw [map_mul, map_inv, e', inv_mul_cancel]`. Use `GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (mul_mem (inv_mem a.2) b.2) h1` as an intermediate fact. Conclude with `Subtype.ext (inv_mul_eq_one.1 this)`.
-/
theorem finG_injective (V : HSp D) : Function.Injective (finG V) := by
  intro a b e
  have e' : finHom V a.1 = finHom V b.1 := bc_swapAE_injective V.rank e
  have h1 : finHom V (a.1⁻¹ * b.1) = 1 := by rw [map_mul, map_inv, e', inv_mul_cancel]
  have := GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (mul_mem (inv_mem a.2) b.2) h1
  exact Subtype.ext (inv_mul_eq_one.1 this)

def finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Subgroup (Bridge.Gf V) :=
  (K.comap (Formalism.UG.bc (Lev.swapAE D))).comap (Bridge.Gf V).subtype

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_finLev_iff (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (g : GfC V) :
    gfcToGf V g ∈ finLev V K ↔ g ∈ K.comap (finG V) := Iff.rfl

/- English proof (translation)
Establish `e : (((finLev V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V)) = ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))` using `rfl`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev`. Rewrite using `[e]`. Conclude with `hK.1`.
-/
theorem isOpenLev_finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsCO V K) :
    GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev V (finLev V K) := by
  have e : (((finLev V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V)) =
      ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev
  rw [e]
  exact hK.1

/- English proof (translation)
Take `⟨m, c, hc⟩` from `GlobalTheory.RepsObj.exists_cover V hV (finLev V K) (isOpenLev_finLev V K hK)`. Use `choose x hx using fun a => gfcToGf_surjective V (c a)`. Use `Finite.of_surjective (fun a : Fin m => (DoubleCoset.mk (ratFin V) (K.comap (finG V)) (x a) : FinCl V K)) ?_` and prove the remaining obligations. Introduce `q`. Rewrite using `[← DoubleCoset.out_eq' _ _ q]`.

Use `set y := Quotient.out q`. Take `⟨a, γ, k, e⟩` from `hc (gfcToGf V y)`. Take `⟨z, hz⟩` from `gfcToGf_surjective V (Bridge.ratF V γ)`. Use `⟨a, (DoubleCoset.eq _ _ _ _).2 ⟨z, ?_, (x a)⁻¹ * z⁻¹ * y, ?_, by group⟩⟩` and prove the remaining obligations. Establish `hz' : finHom V z.1 = finHom V γ.1` using `congrArg Subtype.val hz`.

Use `⟨γ.1, γ.2, ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.bc (Lev.swapAE D) (finHom V γ.1) = Formalism.UG.bc (Lev.swapAE D) (finHom V z.1)`. Rewrite using `[hz']`. Use `(mem_finLev_iff V K _).1 ?_` and prove the remaining obligations. Establish `h1 : gfcToGf V ((x a)⁻¹ * z⁻¹ * y) = (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y`.

Simplify using `only [map_mul, map_inv]`. Establish `h2 : (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y = (k : Bridge.Gf V)`. Simplify using `only [hx a, hz, e]`. Use `group`. Conclude with `(congrArg (· ∈ finLev V K) (h1.trans h2)).mpr k.2`.
-/
theorem finite_finCl (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) : Finite (FinCl V K) := by
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover V hV (finLev V K) (isOpenLev_finLev V K hK)
  choose x hx using fun a => gfcToGf_surjective V (c a)
  refine Finite.of_surjective (fun a : Fin m => (DoubleCoset.mk (ratFin V) (K.comap (finG V)) (x a) : FinCl V K)) ?_
  intro q
  rw [← DoubleCoset.out_eq' _ _ q]
  set y := Quotient.out q
  obtain ⟨a, γ, k, e⟩ := hc (gfcToGf V y)
  obtain ⟨z, hz⟩ := gfcToGf_surjective V (Bridge.ratF V γ)
  refine ⟨a, (DoubleCoset.eq _ _ _ _).2 ⟨z, ?_, (x a)⁻¹ * z⁻¹ * y, ?_, by group⟩⟩
  · have hz' : finHom V z.1 = finHom V γ.1 := congrArg Subtype.val hz
    refine ⟨γ.1, γ.2, ?_⟩
    show Formalism.UG.bc (Lev.swapAE D) (finHom V γ.1) = Formalism.UG.bc (Lev.swapAE D) (finHom V z.1)
    rw [hz']
  · refine (mem_finLev_iff V K _).1 ?_
    have h1 : gfcToGf V ((x a)⁻¹ * z⁻¹ * y) = (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y := by
      simp only [map_mul, map_inv]
    have h2 : (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y = (k : Bridge.Gf V) := by
      simp only [hx a, hz, e]; group
    exact (congrArg (· ∈ finLev V K) (h1.trans h2)).mpr k.2

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram` as an intermediate fact. Take `⟨π, hπ, -⟩` from `GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram`. Conclude with `(continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ`.
-/
theorem continuous_finHom (V : HSp D) : Continuous (finHom V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  exact (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ

/- English proof (translation)
Use `set C : Set (Af D.host.F ⊗[D.host.F] D.host.E) := ⋃ p : Fin V.rank × Fin V.rank, (fun g : GA D V => (finHom V g).1 p.1 p.2) '' (Lev.levA V K : Set (GA D V)) with hCdef`. Establish `hC : IsCompact C` using `isCompact_iUnion fun p => hK.2.image ((Units.continuous_val.comp (continuous_finHom V)).matrix_elem p.1 p.2)`. Establish `hCJ : ∀ k ∈ finLev V K, ∀ i j, (k : Bridge.Gf V).1.1 i j ∈ C`. Introduce `k hk i j`. Take `⟨g, rfl⟩` from `gfcToGf_surjective V k`.

Conclude with `Set.mem_iUnion.2 ⟨(i, j), g.1, ⟨g.2, (mem_finLev_iff V K g).1 hk⟩, rfl⟩`. Establish `hs` using `GlobalTheory.RepsObj.finite_stab V hV (finLev V K) hC hCJ (gfcToGf V x)`. Establish `hq : ∀ γ : ratFin V, ∃ q : GQ V, Lev.finE V q.1 = finG V γ.1` using `fun γ => by`. Take `⟨q, hq, e⟩` from `Subgroup.mem_map.1 γ.2`. Conclude with `⟨⟨q, hq⟩, e⟩`.

Use `choose q hq using hq`. Establish `hfin : Finite {γ : ratFin V // finG V (x⁻¹ * γ * x) ∈ K}`. Use `Finite.of_injective (β := Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x)) (fun γ => ⟨q γ.1, ?_⟩) ?_` and prove the remaining obligations. Establish `e0 : Bridge.ratF V (q γ.1) = gfcToGf V γ.1.1` using `Subtype.ext (bc_swapAE_injective V.rank (hq γ.1))`. Establish `e1 : (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) = gfcToGf V (x⁻¹ * γ.1.1 * x)`.

Simplify using `only [e0, map_mul, map_inv, MulAut.conj_inv_apply]`. Use `show (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) ∈ finLev V K`. Conclude with `(congrArg (· ∈ finLev V K) e1).mpr ((mem_finLev_iff V K _).2 γ.2)`. Introduce `γ γ' e`. Establish `e1 : Lev.finE V (q γ.1).1 = Lev.finE V (q γ'.1).1`.

Use `congrArg (fun s : Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x) => Lev.finE V s.1.1) e` as an intermediate fact. Conclude with `this`. Rewrite `e1` using `[hq, hq]`. Conclude with `Subtype.ext (Subtype.ext (finG_injective V e1))`. Use `Nat.card_ne_zero.2 ⟨⟨⟨1, one_mem _⟩, ?_⟩, hfin⟩` and prove the remaining obligations.

Simplify using `only [mul_one, inv_mul_cancel, map_one]`. Conclude with `one_mem K`.
-/
theorem gamOrd_ne_zero (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) (x : GfC V) : gamOrd V K x ≠ 0 := by
  set C : Set (Af D.host.F ⊗[D.host.F] D.host.E) :=
    ⋃ p : Fin V.rank × Fin V.rank, (fun g : GA D V => (finHom V g).1 p.1 p.2) '' (Lev.levA V K : Set (GA D V)) with hCdef
  have hC : IsCompact C := isCompact_iUnion fun p =>
    hK.2.image ((Units.continuous_val.comp (continuous_finHom V)).matrix_elem p.1 p.2)
  have hCJ : ∀ k ∈ finLev V K, ∀ i j, (k : Bridge.Gf V).1.1 i j ∈ C := by
    intro k hk i j
    obtain ⟨g, rfl⟩ := gfcToGf_surjective V k
    exact Set.mem_iUnion.2 ⟨(i, j), g.1, ⟨g.2, (mem_finLev_iff V K g).1 hk⟩, rfl⟩
  have hs := GlobalTheory.RepsObj.finite_stab V hV (finLev V K) hC hCJ (gfcToGf V x)
  have hq : ∀ γ : ratFin V, ∃ q : GQ V, Lev.finE V q.1 = finG V γ.1 := fun γ => by
    obtain ⟨q, hq, e⟩ := Subgroup.mem_map.1 γ.2
    exact ⟨⟨q, hq⟩, e⟩
  choose q hq using hq
  have hfin : Finite {γ : ratFin V // finG V (x⁻¹ * γ * x) ∈ K} := by
    refine Finite.of_injective (β := Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x))
      (fun γ => ⟨q γ.1, ?_⟩) ?_
    · have e0 : Bridge.ratF V (q γ.1) = gfcToGf V γ.1.1 :=
        Subtype.ext (bc_swapAE_injective V.rank (hq γ.1))
      have e1 : (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) = gfcToGf V (x⁻¹ * γ.1.1 * x) := by
        simp only [e0, map_mul, map_inv, MulAut.conj_inv_apply]
      show (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) ∈ finLev V K
      exact (congrArg (· ∈ finLev V K) e1).mpr ((mem_finLev_iff V K _).2 γ.2)
    · intro γ γ' e
      have e1 : Lev.finE V (q γ.1).1 = Lev.finE V (q γ'.1).1 := by
        have := congrArg (fun s : Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x) => Lev.finE V s.1.1) e
        exact this
      rw [hq, hq] at e1
      exact Subtype.ext (Subtype.ext (finG_injective V e1))
  refine Nat.card_ne_zero.2 ⟨⟨⟨1, one_mem _⟩, ?_⟩, hfin⟩
  simp only [mul_one, inv_mul_cancel, map_one]
  exact one_mem K

/- English proof (translation)
Introduce `V K hV hK` and use `⟨finite_finCl V K (fun τ => hV (tauE _ τ)) hK, gamOrd_ne_zero V K (fun τ => hV (tauE _ τ)) hK⟩`.
-/
theorem finite_finCl_and_gamOrd : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))),
    (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) → IsCO V K → Finite (FinCl V K) ∧ ∀ x, gamOrd V K x ≠ 0 :=
  fun V K hV hK => ⟨finite_finCl V K (fun τ => hV (tauE _ τ)) hK, gamOrd_ne_zero V K (fun τ => hV (tauE _ τ)) hK⟩

end GlobalTheory.FunObj
