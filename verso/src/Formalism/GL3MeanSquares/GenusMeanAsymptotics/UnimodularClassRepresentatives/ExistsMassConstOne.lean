import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaStdOneNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNeZeroOfIsLattice
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Introduce `x hx`. Establish `hsum` using `trace_eq_sum_embeddings ℂ (K := ℚ) (x := h x x)`. Establish `hre : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re`. Use `congrArg Complex.re hsum` as an intermediate fact. Simplify `this` using `[Complex.re_sum]`.

Establish `hne : Nonempty (K →ₐ[ℚ] ℂ)` using `⟨IsAlgClosed.lift⟩`. Establish `hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re` using `Finset.sum_pos (fun σ _ => hd x hx σ.toRingHom) Finset.univ_nonempty`. Conclude with `hre ▸ hpos` after adjusting the coercions.
-/
theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (x := h x x)
  have hre : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hd x hx σ.toRingHom) Finset.univ_nonempty
  exact_mod_cast hre ▸ hpos

/- English proof (translation)
Set `b` to `Module.finBasisOfFinrankEq K V h1`. Set `φ : V ≃ₗ[K] K` to `b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)`. Set `h' : K →ₗ⋆[K] K →ₗ[K] K` to `(h.comp φ.symm.toLinearMap).compl₂ φ.symm.toLinearMap`. Establish `hh' : ∀ x y, h' (φ x) (φ y) = h x y`. Introduce `x y`.

Simplify using `[h']`. Establish `htr` using `trace_pos hd`. Take `⟨hex, -, -⟩` from `Formalism.HermitianLatticesTheory.massBasic K V h hs htr L hL`. Take `⟨hex', hm⟩` from `mass_mapE φ hh' hex`. Use `⟨h', mapE φ L, ?_, isLattice_mapE φ hL, hex', hm⟩` and prove the remaining obligations.

Establish `h0 : φ.symm 1 ≠ 0` using `by simp`. Introduce `hz`. Use `htr _ h0` as an intermediate fact. Establish `hz' : h (φ.symm 1) (φ.symm 1) = 0` using `by simpa [h'] using hz`. Rewrite `this` using `[hz', map_zero]`.

Conclude with `lt_irrefl _ this`.
-/
theorem exists_model [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (h1 : finrank K V = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) :
    ∃ (h' : K →ₗ⋆[K] K →ₗ[K] K) (A : Submodule (𝓞 K) K), h' 1 1 ≠ 0 ∧ Submodule.IsLattice K A ∧
      (∃ s, IsClassReps h' A s) ∧ mass h' A = mass h L := by
  let b := Module.finBasisOfFinrankEq K V h1
  let φ : V ≃ₗ[K] K := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)
  let h' : K →ₗ⋆[K] K →ₗ[K] K := (h.comp φ.symm.toLinearMap).compl₂ φ.symm.toLinearMap
  have hh' : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    simp [h']
  have htr := trace_pos hd
  obtain ⟨hex, -, -⟩ := Formalism.HermitianLatticesTheory.massBasic K V h hs htr L hL
  obtain ⟨hex', hm⟩ := mass_mapE φ hh' hex
  refine ⟨h', mapE φ L, ?_, isLattice_mapE φ hL, hex', hm⟩
  have h0 : φ.symm 1 ≠ 0 := by simp
  intro hz
  have := htr _ h0
  have hz' : h (φ.symm 1) (φ.symm 1) = 0 := by simpa [h'] using hz
  rw [hz', map_zero] at this
  exact lt_irrefl _ this

end RankOne

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

/- English proof (translation)
Take `⟨h₀, hh⟩ : ∃ h₀ : K →ₗ⋆[K] K →ₗ[K] K, ∀ x y, h₀ x y = star x * y` from `⟨LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y) (fun x y z => by simp [add_mul]) (fun a x y => by simp [smul_eq_mul, mul_assoc, starRingEnd_apply]) (fun x y z => by simp [mul_add]) (fun a x y => by simp [smul_eq_mul, mul_left_comm]), fun _ _ => rfl⟩`. Establish `hs₀ : h₀.IsSymm` using `by first`. Consider the case `(intro x y; simp [hh, starRingEnd_apply, mul_comm])`. Consider the case `(constructor; intro x y; simp [hh, starRingEnd_apply, mul_comm])`. Establish `hd₀ : IsTotPosDef h₀`.

Introduce `x hx φ`. Establish `hx' : φ x ≠ 0` using `(map_ne_zero φ).mpr hx`. Establish `: φ (h₀ x x) = ((Complex.normSq (φ x) : ℝ) : ℂ)`. Rewrite using `[hh, map_mul, hK.2.1 φ x, Complex.normSq_eq_conj_mul_self]`. Rewrite using `[this, Complex.ofReal_re]`.

Conclude with `Complex.normSq_pos.mpr hx'`. Establish `hn₀ : h₀ 1 1 ≠ 0` using `by simp [hh]`. Use `set L₀ : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}`. Establish `hL₀ : Submodule.IsLattice K L₀`. Use `⟨Submodule.fg_span_singleton _, ?_⟩` and prove the remaining obligations.

Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Establish `h1 : (1 : K) ∈ Submodule.span K (L₀ : Set K)` using `Submodule.subset_span (Submodule.subset_span rfl)`. Simplify using `using Submodule.smul_mem _ y h1`. Take `⟨hex₀, -, hpos₀⟩` from `Formalism.HermitianLatticesTheory.massBasic K K h₀ hs₀ (RankOne.trace_pos hd₀) L₀ hL₀`. Use `⟨Formalism.HermitianLatticesTheory.mass h₀ L₀, hpos₀, ?_⟩` and prove the remaining obligations.

Introduce `V _ _ _ _ _ h L hs hd h1 hL hLi`. Take `⟨h', A, hn', hA, -, hm⟩` from `RankOne.exists_model hs hd h1 hL`. Establish `hlam : lamG F h L = 1`. Unfold `lamG`. Conclude with `(tprod_congr fun p => localFactor_rank_one hK hF hs hd hL hLi h1 p.2).trans tprod_one`.

Rewrite using `[hlam, mul_one, ← hm]`. Conclude with `RankOne.mass_eq_of_lattices hn₀ hn' hL₀ hA hex₀`.
-/
theorem exists_massConst_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := by
  obtain ⟨h₀, hh⟩ : ∃ h₀ : K →ₗ⋆[K] K →ₗ[K] K, ∀ x y, h₀ x y = star x * y :=
    ⟨LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
      (fun x y z => by simp [add_mul]) (fun a x y => by simp [smul_eq_mul, mul_assoc, starRingEnd_apply])
      (fun x y z => by simp [mul_add]) (fun a x y => by simp [smul_eq_mul, mul_left_comm]),
      fun _ _ => rfl⟩
  have hs₀ : h₀.IsSymm := by
    first
      | (intro x y; simp [hh, starRingEnd_apply, mul_comm])
      | (constructor; intro x y; simp [hh, starRingEnd_apply, mul_comm])
  have hd₀ : IsTotPosDef h₀ := by
    intro x hx φ
    have hx' : φ x ≠ 0 := (map_ne_zero φ).mpr hx
    have : φ (h₀ x x) = ((Complex.normSq (φ x) : ℝ) : ℂ) := by
      rw [hh, map_mul, hK.2.1 φ x, Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hx'
  have hn₀ : h₀ 1 1 ≠ 0 := by simp [hh]
  set L₀ : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
  have hL₀ : Submodule.IsLattice K L₀ := by
    refine ⟨Submodule.fg_span_singleton _, ?_⟩
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : (1 : K) ∈ Submodule.span K (L₀ : Set K) :=
      Submodule.subset_span (Submodule.subset_span rfl)
    simpa using Submodule.smul_mem _ y h1
  obtain ⟨hex₀, -, hpos₀⟩ := Formalism.HermitianLatticesTheory.massBasic K K h₀ hs₀ (RankOne.trace_pos hd₀) L₀ hL₀
  refine ⟨Formalism.HermitianLatticesTheory.mass h₀ L₀, hpos₀, ?_⟩
  intro V _ _ _ _ _ h L hs hd h1 hL hLi
  obtain ⟨h', A, hn', hA, -, hm⟩ := RankOne.exists_model hs hd h1 hL
  have hlam : lamG F h L = 1 := by
    unfold lamG
    exact (tprod_congr fun p => localFactor_rank_one hK hF hs hd hL hLi h1 p.2).trans tprod_one
  rw [hlam, mul_one, ← hm]
  exact RankOne.mass_eq_of_lattices hn₀ hn' hL₀ hA hex₀

end Formalism.HermitianLattices.Ext.L3
