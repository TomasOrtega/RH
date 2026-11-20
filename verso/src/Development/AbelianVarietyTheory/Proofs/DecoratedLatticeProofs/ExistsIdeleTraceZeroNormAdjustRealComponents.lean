import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`.
-/
private theorem tmulOne_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (σ : E →ₐ[F] E) (x : R) :
    (Algebra.TensorProduct.map f σ).toRingHom (x ⊗ₜ[F] (1 : E)) = f x ⊗ₜ[F] (1 : E) := by
  change Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]

/- English proof (translation)
Use `set c := sigR (AF F) σ with hc`. Use `set e : AF F ⊗[F] E := pairA F 1 0 ⊗ₜ[F] (1 : E) with he`. Establish `hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0` using `Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))`. Establish `hee : e * e = e` using `by rw [he, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]`. Establish `hce : c e = e` using `tmulOne_map F E (AlgHom.id F (AF F)) σ _`.

Establish `hfe : ∀ v, compFin F E v e = 0`. Introduce `v`. Use `(tmulOne_map F E (evFin F v) (AlgHom.id F E) _).trans ?_` and prove the remaining obligations. Rewrite using `[evFin, AlgHom.comp_apply, show sndA F (pairA F 1 0) = 0 from rfl, map_zero, TensorProduct.zero_tmul]`. Establish `hie : ∀ w, compInf F E w e = 1`.

Introduce `w`. Use `(tmulOne_map F E (evInf F w) (AlgHom.id F E) _).trans ?_` and prove the remaining obligations. Rewrite using `[evInf, AlgHom.comp_apply, show fstA F (pairA F 1 0) = 1 from rfl, map_one, Algebra.TensorProduct.one_def]`. Set `R : AF F` to `pairA F (fun w => r w) 1`. Set `R' : AF F` to `pairA F (fun w => (r w)⁻¹) 1`.

Establish `hRR : R * R' = 1` using `Prod.ext (funext fun w => mul_inv_cancel₀ (hr w)) (mul_one (1 : Af F))`. Use `set a : AF F ⊗[F] E := R ⊗ₜ[F] (1 : E) with ha`. Use `set a' : AF F ⊗[F] E := R' ⊗ₜ[F] (1 : E) with ha'`. Establish `haa : a * a' = 1`. Rewrite using `[ha, ha', Algebra.TensorProduct.tmul_mul_tmul, mul_one, hRR, Algebra.TensorProduct.one_def]`.

Establish `hca : c a = a` using `tmulOne_map F E (AlgHom.id F (AF F)) σ _`. Establish `hia : ∀ w, compInf F E w a = r w ⊗ₜ[F] (1 : E)` using `fun w => tmulOne_map F E (evInf F w) (AlgHom.id F E) _`. Establish `hu0 : (u₀ : AF F ⊗[F] E) * ↑u₀⁻¹ = 1` using `Units.mul_inv u₀`. Use `set x : AF F ⊗[F] E := e * a + (1 - e) * u₀ with hx`. Use `set x' : AF F ⊗[F] E := e * a' + (1 - e) * ↑u₀⁻¹ with hx'`.

Establish `hxx : x * x' = 1`. Rewrite using `[hx, hx']`. Take the linear combination `(2 - a * ↑u₀⁻¹ - (u₀ : AF F ⊗[F] E) * a') * hee + e * e * haa + (1 - e) * (1 - e) * hu0`. Set `U : (AF F ⊗[F] E)ˣ` to `⟨x, x', hxx, by rw [mul_comm]; exact hxx⟩`. Establish `hshape : ∀ y, c (e * a + (1 - e) * y) = e * a + (1 - e) * c y`.

Introduce `y`. Rewrite using `[map_add, map_mul, map_mul, map_sub, map_one, hce, hca]`. Establish `hread : ∀ w y, compInf F E w (e * a + (1 - e) * y) = r w ⊗ₜ[F] (1 : E)`. Introduce `w y`. Rewrite using `[map_add, map_mul, map_mul, map_sub, map_one, hie, hia]`.

Expand and normalize the polynomial expressions, which then agree. Set `M : (AF F ⊗[F] E)ˣ` to `Units.map (inclR (AF F) : E →+* AF F ⊗[F] E).toMonoidHom (Units.mk0 μ hμ)`. Set `P : (AF F ⊗[F] E)ˣ` to `U * Units.map c.toMonoidHom U`. Use `⟨U, M * P⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ((P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (U * c U) = 1`.

Use `Units.inv_mul P` as an intermediate fact. Simplify `this` using `[P]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = inclR (AF F) μ := by rw [h1, mul_one]; rfl`. Introduce `v`. Express the relevant statement in the definitionally equal form `compFin F E v x = _`. Rewrite using `[hx, map_add, map_mul, map_mul, map_sub, map_one, hfe]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `w set φ := compInf F E w with hφ set ρ : w.Completion ⊗[F] E := r w ⊗ₜ[F] (1 : E) with hρdef`. Establish `hρ : ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) = 1`. Rewrite using `[hρdef, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ (hr w), Algebra.TensorProduct.one_def]`. Establish `hP : (P : AF F ⊗[F] E) = x * c x` using `rfl`. Establish `hM : (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] μ` using `rfl`.

Establish `hε : ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (x * c x) = M`. Rewrite using `[← hP, ← Units.val_mul, inv_mul_cancel_right]`. Establish `hε'` using `congrArg c hε`. Rewrite `hε'` using `[map_mul, map_mul]`. Establish `hall : (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * ((x * c x) * (c x * c (c x))) = (M : AF F ⊗[F] E) * c M`.

Rewrite using `[← hε', ← hε]`. Expand and normalize the polynomial expressions, which then agree. Establish `hφx : φ x = ρ` using `hread w _`. Establish `hφcx : φ (c x) = ρ` using `by rw [hx, hshape, hread]`. Establish `hφccx : φ (c (c x)) = ρ` using `by rw [hx, hshape, hshape, hread]`.

Establish `hcM : c (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] σ μ`. Rewrite using `[hM, hc]`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] μ) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Establish `hφ1 : ∀ z : E, φ ((1 : AF F) ⊗ₜ[F] z) = (1 : w.Completion) ⊗ₜ[F] z`.

Introduce `z`. Rewrite using `[hφ]`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] z) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]`. Establish `hrhs : φ ((M : AF F ⊗[F] E) * c M) = 4 * ρ ^ 4`.

Rewrite using `[map_mul, hcM, hM, hφ1, hφ1, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hN w]`. Establish `key` using `congrArg φ hall`. Establish `hB : φ ((x * c x) * (c x * c (c x))) = ρ * ρ * (ρ * ρ)`. Rewrite using `[map_mul, map_mul, map_mul, hφx, hφcx, hφccx]`. Rewrite `key` using `[map_mul φ _ ((x * c x) * (c x * c (c x))), hB, hrhs]`.

Take the linear combination `((r w)⁻¹ ⊗ₜ[F] (1 : E)) ^ 4 * key - (φ (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) - 4) * (1 + ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 2 + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 3) * hρ`.
-/
private theorem scal_gen (σ : E →ₐ[F] E) (μ : E) (hμ : μ ≠ 0)
    (r : ∀ w : InfinitePlace F, w.Completion) (hr : ∀ w, r w ≠ 0)
    (hN : ∀ w, ((1 : w.Completion) ⊗ₜ[F] (μ * σ μ) : w.Completion ⊗[F] E) = 4 * (r w ⊗ₜ[F] (1 : E)) ^ 4)
    (u₀ : (AF F ⊗[F] E)ˣ) :
    ∃ u ε : (AF F ⊗[F] E)ˣ, (ε : AF F ⊗[F] E) * (u : AF F ⊗[F] E) * sigR (AF F) σ (u : AF F ⊗[F] E) = inclR (AF F) μ ∧
      (∀ v, compFin F E v u = compFin F E v u₀) ∧
      ∀ w, compInf F E w ((ε : AF F ⊗[F] E) * sigR (AF F) σ (ε : AF F ⊗[F] E)) = 4 := by
  set c := sigR (AF F) σ with hc
  set e : AF F ⊗[F] E := pairA F 1 0 ⊗ₜ[F] (1 : E) with he
  have hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0 :=
    Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))
  have hee : e * e = e := by rw [he, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  have hce : c e = e := tmulOne_map F E (AlgHom.id F (AF F)) σ _
  have hfe : ∀ v, compFin F E v e = 0 := by
    intro v
    refine (tmulOne_map F E (evFin F v) (AlgHom.id F E) _).trans ?_
    rw [evFin, AlgHom.comp_apply, show sndA F (pairA F 1 0) = 0 from rfl, map_zero, TensorProduct.zero_tmul]
  have hie : ∀ w, compInf F E w e = 1 := by
    intro w
    refine (tmulOne_map F E (evInf F w) (AlgHom.id F E) _).trans ?_
    rw [evInf, AlgHom.comp_apply, show fstA F (pairA F 1 0) = 1 from rfl, map_one, Algebra.TensorProduct.one_def]
  let R : AF F := pairA F (fun w => r w) 1
  let R' : AF F := pairA F (fun w => (r w)⁻¹) 1
  have hRR : R * R' = 1 := Prod.ext (funext fun w => mul_inv_cancel₀ (hr w)) (mul_one (1 : Af F))
  set a : AF F ⊗[F] E := R ⊗ₜ[F] (1 : E) with ha
  set a' : AF F ⊗[F] E := R' ⊗ₜ[F] (1 : E) with ha'
  have haa : a * a' = 1 := by
    rw [ha, ha', Algebra.TensorProduct.tmul_mul_tmul, mul_one, hRR, Algebra.TensorProduct.one_def]
  have hca : c a = a := tmulOne_map F E (AlgHom.id F (AF F)) σ _
  have hia : ∀ w, compInf F E w a = r w ⊗ₜ[F] (1 : E) := fun w =>
    tmulOne_map F E (evInf F w) (AlgHom.id F E) _
  have hu0 : (u₀ : AF F ⊗[F] E) * ↑u₀⁻¹ = 1 := Units.mul_inv u₀
  set x : AF F ⊗[F] E := e * a + (1 - e) * u₀ with hx
  set x' : AF F ⊗[F] E := e * a' + (1 - e) * ↑u₀⁻¹ with hx'
  have hxx : x * x' = 1 := by
    rw [hx, hx']
    linear_combination (2 - a * ↑u₀⁻¹ - (u₀ : AF F ⊗[F] E) * a') * hee + e * e * haa + (1 - e) * (1 - e) * hu0
  let U : (AF F ⊗[F] E)ˣ := ⟨x, x', hxx, by rw [mul_comm]; exact hxx⟩

  have hshape : ∀ y, c (e * a + (1 - e) * y) = e * a + (1 - e) * c y := by
    intro y; rw [map_add, map_mul, map_mul, map_sub, map_one, hce, hca]
  have hread : ∀ w y, compInf F E w (e * a + (1 - e) * y) = r w ⊗ₜ[F] (1 : E) := by
    intro w y; rw [map_add, map_mul, map_mul, map_sub, map_one, hie, hia]; ring
  let M : (AF F ⊗[F] E)ˣ := Units.map (inclR (AF F) : E →+* AF F ⊗[F] E).toMonoidHom (Units.mk0 μ hμ)
  let P : (AF F ⊗[F] E)ˣ := U * Units.map c.toMonoidHom U
  refine ⟨U, M * P⁻¹, ?_, ?_, ?_⟩
  · have h1 : ((P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (U * c U) = 1 := by
      have := Units.inv_mul P
      simpa [P] using this
    calc ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * U * c U
        = (M : AF F ⊗[F] E) * (((P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (U * c U)) := by
          rw [Units.val_mul]; ring
      _ = inclR (AF F) μ := by rw [h1, mul_one]; rfl
  · intro v
    change compFin F E v x = _
    rw [hx, map_add, map_mul, map_mul, map_sub, map_one, hfe]; ring
  · intro w
    set φ := compInf F E w with hφ
    set ρ : w.Completion ⊗[F] E := r w ⊗ₜ[F] (1 : E) with hρdef
    have hρ : ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) = 1 := by
      rw [hρdef, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ (hr w), Algebra.TensorProduct.one_def]
    have hP : (P : AF F ⊗[F] E) = x * c x := rfl
    have hM : (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] μ := rfl
    have hε : ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * (x * c x) = M := by
      rw [← hP, ← Units.val_mul, inv_mul_cancel_right]
    have hε' := congrArg c hε
    rw [map_mul, map_mul] at hε'
    have hall : (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *
        ((x * c x) * (c x * c (c x))) = (M : AF F ⊗[F] E) * c M := by
      rw [← hε', ← hε]; ring
    have hφx : φ x = ρ := hread w _
    have hφcx : φ (c x) = ρ := by rw [hx, hshape, hread]
    have hφccx : φ (c (c x)) = ρ := by rw [hx, hshape, hshape, hread]
    have hcM : c (M : AF F ⊗[F] E) = (1 : AF F) ⊗ₜ[F] σ μ := by
      rw [hM, hc]
      change Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] μ) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hφ1 : ∀ z : E, φ ((1 : AF F) ⊗ₜ[F] z) = (1 : w.Completion) ⊗ₜ[F] z := by
      intro z
      rw [hφ]
      change Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] z) = _
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    have hrhs : φ ((M : AF F ⊗[F] E) * c M) = 4 * ρ ^ 4 := by
      rw [map_mul, hcM, hM, hφ1, hφ1, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hN w]
    have key := congrArg φ hall
    have hB : φ ((x * c x) * (c x * c (c x))) = ρ * ρ * (ρ * ρ) := by
      rw [map_mul, map_mul, map_mul, hφx, hφcx, hφccx]
    rw [map_mul φ _ ((x * c x) * (c x * c (c x))), hB, hrhs] at key
    linear_combination ((r w)⁻¹ ⊗ₜ[F] (1 : E)) ^ 4 * key -
      (φ (((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * c ((M * P⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) - 4) *
        (1 + ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E)) + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 2 + (ρ * ((r w)⁻¹ ⊗ₜ[F] (1 : E))) ^ 3) * hρ
end

/- English proof (translation)
Use `set hw := NumberField.IsTotallyReal.isReal w`. Use `set n : D.host.F := ⟨μ * star μ, (IsCMField.complexConj_eq_self_iff D.host.E _).1 (by`. Express the relevant statement in the definitionally equal form `star (μ * star μ) = μ * star μ`. Rewrite using `[star_mul, star_star])⟩ with hn`. Use `letI : Algebra D.host.F ℂ := w.embedding.toAlgebra`.

Set `φ : D.host.E →ₐ[D.host.F] ℂ` to `by set_option synthInstance.maxHeartbeats 400000 in exact IsAlgClosed.lift`. Establish `h1 : φ (algebraMap D.host.F D.host.E n) = w.embedding n` using `φ.commutes n`. Establish `h2 : (algebraMap D.host.F D.host.E n) = μ * star μ` using `rfl`. Establish `h3 : φ (star μ) = starRingEnd ℂ (φ μ)` using `IsCMField.complexEmbedding_complexConj D.host.E (φ : D.host.E →+* ℂ) μ`. Rewrite `h1` using `[h2, map_mul, h3, Complex.mul_conj]`.

Establish `h4 : ((InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) : ℂ) = w.embedding n`. Simplify using the standard rewrite rules. Establish `h5 : 0 < Complex.normSq (φ μ)` using `Complex.normSq_pos.2 (by simpa using hμ)`. Establish `h6` using `h4.trans h1.symm`. Establish `h7 : (InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) = Complex.normSq (φ μ)`.

Conclude with `h6` after adjusting the coercions. Rewrite using `[h7]`. Conclude with `h5`.
-/
private theorem scal_pos (D : D7) (μ : D.host.E) (hμ : μ ≠ 0) (w : InfinitePlace D.host.F) :
    0 < InfinitePlace.Completion.ringEquivRealOfIsReal (NumberField.IsTotallyReal.isReal w)
      (algebraMap D.host.F w.Completion ⟨μ * star μ, (IsCMField.complexConj_eq_self_iff D.host.E _).1 (by
        change star (μ * star μ) = μ * star μ; rw [star_mul, star_star])⟩) := by
  set hw := NumberField.IsTotallyReal.isReal w
  set n : D.host.F := ⟨μ * star μ, (IsCMField.complexConj_eq_self_iff D.host.E _).1 (by
        change star (μ * star μ) = μ * star μ; rw [star_mul, star_star])⟩ with hn
  letI : Algebra D.host.F ℂ := w.embedding.toAlgebra
  let φ : D.host.E →ₐ[D.host.F] ℂ := by
    set_option synthInstance.maxHeartbeats 400000 in exact IsAlgClosed.lift
  have h1 : φ (algebraMap D.host.F D.host.E n) = w.embedding n := φ.commutes n
  have h2 : (algebraMap D.host.F D.host.E n) = μ * star μ := rfl
  have h3 : φ (star μ) = starRingEnd ℂ (φ μ) :=
    IsCMField.complexEmbedding_complexConj D.host.E (φ : D.host.E →+* ℂ) μ
  rw [h2, map_mul, h3, Complex.mul_conj] at h1
  have h4 : ((InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) : ℂ) = w.embedding n := by
    simp
  have h5 : 0 < Complex.normSq (φ μ) := Complex.normSq_pos.2 (by simpa using hμ)
  have h6 := h4.trans h1.symm
  have h7 : (InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap D.host.F w.Completion n) : ℝ) = Complex.normSq (φ μ) := by
    exact_mod_cast h6
  rw [h7]; exact h5

/- English proof (translation)
Use `set f := InfinitePlace.Completion.ringEquivRealOfIsReal hw`. Use `set t := f (algebraMap F w.Completion n) with ht`. Establish `h0 : 0 < √(√(t / 4))` using `by positivity`. Establish `h4 : 4 * (f.symm √(√(t / 4))) ^ 4 = algebraMap F w.Completion n`. Apply `f.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, map_pow, map_ofNat, RingEquiv.apply_symm_apply, ← ht, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨f.symm √(√(t / 4)), (map_ne_zero f.symm).2 h0.ne', ?_⟩` and prove the remaining obligations. Establish `h5` using `congrArg (Algebra.TensorProduct.includeLeftRingHom : w.Completion →+* w.Completion ⊗[F] E) h4`. Rewrite `h5` using `[map_mul, map_pow, map_ofNat, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply]`.

Rewrite using `[h5, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.
-/
private theorem scal_root (F E : Type) [Field F] [Field E] [Algebra F E] (w : InfinitePlace F) (hw : w.IsReal) (n : F)
    (hn : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion n)) :
    ∃ r : w.Completion, r ≠ 0 ∧
      ((1 : w.Completion) ⊗ₜ[F] (algebraMap F E n) : w.Completion ⊗[F] E) = 4 * (r ⊗ₜ[F] (1 : E)) ^ 4 := by
  set f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set t := f (algebraMap F w.Completion n) with ht
  have h0 : 0 < √(√(t / 4)) := by positivity
  have h4 : 4 * (f.symm √(√(t / 4))) ^ 4 = algebraMap F w.Completion n := by
    apply f.injective
    rw [map_mul, map_pow, map_ofNat, RingEquiv.apply_symm_apply, ← ht, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
    ring
  refine ⟨f.symm √(√(t / 4)), (map_ne_zero f.symm).2 h0.ne', ?_⟩
  have h5 := congrArg (Algebra.TensorProduct.includeLeftRingHom : w.Completion →+* w.Completion ⊗[F] E) h4
  rw [map_mul, map_pow, map_ofNat, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply] at h5
  rw [h5, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/- English proof (translation)
Introduce `D μ hμ u₀`. Use `choose r hr hN using fun w : InfinitePlace D.host.F => scal_root D.host.F D.host.E w _ _ (scal_pos D μ hμ.1 w)`. Conclude with `scal_gen D.host.F D.host.E D.sp.cm.sig μ hμ.1 r hr hN u₀`.
-/
theorem exists_scal_real : ∀ (D : D7) (μ : D.host.E), IsSkew μ → ∀ u₀ : (AE D)ˣ, ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ (∀ v, compFin D.host.F D.host.E v u = compFin D.host.F D.host.E v u₀) ∧ ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4 := by
  intro D μ hμ u₀
  choose r hr hN using fun w : InfinitePlace D.host.F =>
    scal_root D.host.F D.host.E w _ _ (scal_pos D μ hμ.1 w)
  exact scal_gen D.host.F D.host.E D.sp.cm.sig μ hμ.1 r hr hN u₀

end GlobalTheory.StdUnn
