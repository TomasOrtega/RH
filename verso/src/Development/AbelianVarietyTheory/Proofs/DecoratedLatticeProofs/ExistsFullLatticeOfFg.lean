import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.SpanLattice

open Formalism.L2.GlobalTheoryTheory.HLatOps

/- English proof (translation)
Introduce `K _ _ _ n X hX N hN`. Use `set U : Submodule K (Fin n → K) := Submodule.span K (N : Set (Fin n → K)) with hU`. Set `c` to `Module.finBasis K U`. Set `e : Fin (finrank K U) → Fin n → K` to `fun i => (c i : Fin n → K)`. Set `ψ : (Fin (finrank K U) → K) →ₗ[K] (Fin n → K)` to `U.subtype ∘ₗ c.equivFun.symm.toLinearMap`.

Establish `hψ : ∀ x, ψ x = ∑ i, x i • e i`. Introduce `x`. Simplify using `[ψ, e, Basis.equivFun_symm_apply]`. Establish `hinj : Function.Injective ψ` using `(Submodule.injective_subtype U).comp c.equivFun.symm.injective`. Establish `hrange : ∀ y ∈ U, ∃ x, ψ x = y` using `fun y hy => ⟨c.equivFun ⟨y, hy⟩, by simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply]⟩`.

Establish `hmemU : ∀ x, ψ x ∈ U` using `fun x => (c.equivFun.symm x).2`. Establish `hsingle : ∀ i, ψ (Pi.single i 1) = e i`. Introduce `i`. Rewrite using `[hψ, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Set `L : Submodule (𝓞 K) (Fin (finrank K U) → K)` to `N.comap (ψ.restrictScalars (𝓞 K))`. Establish `hmap : L.map (ψ.restrictScalars (𝓞 K)) = N`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hx`. Introduce `hy`.

Take `⟨x, rfl⟩` from `hrange y (Submodule.subset_span hy)`. Conclude with `⟨x, hy, rfl⟩`. Establish `hfg : L.FG` using `Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hinj (by rw [hmap]; exact hN)`. Establish `hS` using `isSesq_comp (isSesq_maj (Pi.basisFun K (Fin n)) X) ψ`. Establish `hP` using `posAt_comp (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin (finrank K U))) (isSesq_maj (Pi.basisFun K (Fin n)) X) (posAt_maj (Pi.basisFun K (Fin n)) X hX) ψ hinj`.

Take `⟨h1, h2, h3⟩` from `of_form_spec K _ _ (Pi.basisFun K (Fin (finrank K U))) L _ hS hP`. Set `Y : InfinitePlace K → Matrix (Fin (finrank K U)) (Fin (finrank K U)) ℂ` to `fun v => frameOf (gramOf (Pi.basisFun K (Fin (finrank K U))) (fun x y => Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y)))`. Establish `hY : ∀ v, IsUnit (Y v).det` using `h1`. Establish `hm : ∀ v x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (finrank K U))) Y v x y = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y)` using `h2`. Establish `hn : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v (ψ x) = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (finrank K U))) Y v x` using `fun v x => by`.

Rewrite using `[normAt_eq_sqrt (Pi.basisFun K (Fin n)) X v (ψ x)]`. Conclude with `(h3 v x).symm`. Use `⟨finrank K U, e, Y, L, ?_, hY, ⟨hfg, ?_⟩, fun x => ?_, fun v => ?_, ?_⟩` and prove the remaining obligations. Conclude with `c.linearIndependent.map' U.subtype (Submodule.ker_subtype U)`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Establish `hsp : Submodule.span K (N : Set (Fin n → K)) = (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ`. Rewrite using `[Submodule.map_span, ← hmap]`. Both sides reduce to the same expression. Establish `hx : ψ x ∈ (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ`.

Rewrite using `[← hsp]`. Conclude with `hmemU x`. Take `⟨y, hy, hxy⟩` from `hx`. Conclude with `hinj hxy ▸ hy`. Rewrite using `[← hψ]`.

Both sides reduce to the same expression. Use extensionality with `a b`. Simplify using `only [gram, Formalism.HN.gramPl, Matrix.of_apply, hm, hsingle]`. Establish `h` using `(Formalism.HN.rerealize K _ _ _ _ (Pi.basisFun K (Fin (finrank K U))) Y (Pi.basisFun K (Fin n)) X ψ hY hX hinj hn L hfg).1`. Rewrite `h` using `[hmap]`.

Unfold `lcv`. Rewrite using `[h]`.
-/
theorem exists_fullLattice_of_fg :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
      (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
      ∀ N : Submodule (𝓞 K) (Fin n → K), N.FG →
      ∃ (j : ℕ) (e : Fin j → Fin n → K) (Y : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ)
        (L : Submodule (𝓞 K) (Fin j → K)), LinearIndependent K e ∧ (∀ v, IsUnit (Y v).det) ∧
        Submodule.IsLattice K L ∧ (∀ x : Fin j → K, x ∈ L ↔ ∑ i, x i • e i ∈ N) ∧
        (∀ v, gram Y v (fun i => (Pi.single i 1 : Fin j → K)) = gram X v e) ∧
        lcv Y L = lcv X N := by
  intro K _ _ _ n X hX N hN
  set U : Submodule K (Fin n → K) := Submodule.span K (N : Set (Fin n → K)) with hU
  let c := Module.finBasis K U
  let e : Fin (finrank K U) → Fin n → K := fun i => (c i : Fin n → K)
  let ψ : (Fin (finrank K U) → K) →ₗ[K] (Fin n → K) := U.subtype ∘ₗ c.equivFun.symm.toLinearMap
  have hψ : ∀ x, ψ x = ∑ i, x i • e i := by
    intro x
    simp [ψ, e, Basis.equivFun_symm_apply]
  have hinj : Function.Injective ψ :=
    (Submodule.injective_subtype U).comp c.equivFun.symm.injective
  have hrange : ∀ y ∈ U, ∃ x, ψ x = y := fun y hy =>
    ⟨c.equivFun ⟨y, hy⟩, by simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Submodule.subtype_apply]⟩
  have hmemU : ∀ x, ψ x ∈ U := fun x => (c.equivFun.symm x).2
  have hsingle : ∀ i, ψ (Pi.single i 1) = e i := by
    intro i
    rw [hψ, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  let L : Submodule (𝓞 K) (Fin (finrank K U) → K) := N.comap (ψ.restrictScalars (𝓞 K))
  have hmap : L.map (ψ.restrictScalars (𝓞 K)) = N := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hrange y (Submodule.subset_span hy)
      exact ⟨x, hy, rfl⟩
  have hfg : L.FG :=
    Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hinj (by rw [hmap]; exact hN)
  have hS := isSesq_comp (isSesq_maj (Pi.basisFun K (Fin n)) X) ψ
  have hP := posAt_comp (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin (finrank K U)))
    (isSesq_maj (Pi.basisFun K (Fin n)) X) (posAt_maj (Pi.basisFun K (Fin n)) X hX) ψ hinj
  obtain ⟨h1, h2, h3⟩ := of_form_spec K _ _ (Pi.basisFun K (Fin (finrank K U))) L _ hS hP
  let Y : InfinitePlace K → Matrix (Fin (finrank K U)) (Fin (finrank K U)) ℂ := fun v =>
    frameOf (gramOf (Pi.basisFun K (Fin (finrank K U)))
      (fun x y => Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y)))
  have hY : ∀ v, IsUnit (Y v).det := h1
  have hm : ∀ v x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (finrank K U))) Y v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y) := h2
  have hn : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v (ψ x) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (finrank K U))) Y v x := fun v x => by
    rw [normAt_eq_sqrt (Pi.basisFun K (Fin n)) X v (ψ x)]
    exact (h3 v x).symm
  refine ⟨finrank K U, e, Y, L, ?_, hY, ⟨hfg, ?_⟩, fun x => ?_, fun v => ?_, ?_⟩
  · exact c.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · rw [eq_top_iff]
    intro x _
    have hsp : Submodule.span K (N : Set (Fin n → K)) =
        (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ := by
      rw [Submodule.map_span, ← hmap]
      rfl
    have hx : ψ x ∈ (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ := by
      rw [← hsp]
      exact hmemU x
    obtain ⟨y, hy, hxy⟩ := hx
    exact hinj hxy ▸ hy
  · rw [← hψ]
    rfl
  · ext a b
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, hm, hsingle]
  · have h := (Formalism.HN.rerealize K _ _ _ _ (Pi.basisFun K (Fin (finrank K U))) Y
      (Pi.basisFun K (Fin n)) X ψ hY hX hinj hn L hfg).1
    rw [hmap] at h
    unfold lcv
    rw [h]

end GlobalTheory.SpanLattice
