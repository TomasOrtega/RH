import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocalizedModuleSubtype

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HomDual

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `h : ∀ x : D.host.E, star x = D.host.conj x` using `bridge_star_holds D.R D.host`. Rewrite using `[← h, ← h, star_star]`.
-/
theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← h, ← h, star_star]

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `h : ∀ x : D.host.E, star x = D.host.conj x` using `bridge_star_holds D.R D.host`. Take `⟨c, hc⟩` from `(hL.2.2 x).1 hx u hu`. Use `⟨c, hc.trans ?_⟩` and prove the remaining obligations. Simplify using `only [stdH, h]`.
-/
theorem pairing_mem (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L)
    {u x : Fin N → D.host.E} (hu : u ∈ L) (hx : x ∈ L) :
    ∃ c : 𝓞 D.host.E, (c : D.host.E) = ∑ b, D.host.conj (u b) * x b := by
  letI := D.host.cmStar
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨c, hc⟩ := (hL.2.2 x).1 hx u hu
  refine ⟨c, hc.trans ?_⟩
  simp only [stdH, h]

/- English proof (translation)
Use `letI := D.host.cmStar`. Use `haveI : IsCMField D.host.E := D.host.isCMField_hostE`. Establish `h : ∀ x : D.host.E, star x = D.host.conj x` using `bridge_star_holds D.R D.host`. Establish `h' : ∀ x : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x` using `h`. Establish `hh : ∀ x y : Fin N → D.host.E, ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x = stdH D.host.E N x y`.

Introduce `x y`. Rewrite using `[GlobalTheory.DualFamily.herm_one_eq]`. Simplify using `only [stdH, h, h', mul_comm]`. Establish `hr : ∀ z : D.host.E, z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ z` using `fun z => ⟨fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩`. Take `⟨-, m, v, w, hv, hw, he⟩` from `GlobalTheory.exists_dual_family L hL.1 (fun x hx y hy => by rw [hh, ← hr]; exact (hL.2.2 x).1 hx y hy) (fun x hx => (hL.2.2 x).2 fun y hy => by rw [hr, ← hh]; exact hx y hy)`.

Use `⟨m, v, w, hv, hw, fun u a => ?_⟩` and prove the remaining obligations. Use `congrFun (he u) a` as an intermediate fact. Simplify `this` using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.DualFamily.herm_one_eq, h']`.
-/
theorem exists_resolution (D : D7) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : SD D L) : ∃ (m : ℕ) (v w : Fin m → Fin N → D.host.E), (∀ i, v i ∈ L) ∧ (∀ i, w i ∈ L) ∧
      ∀ (u : Fin N → D.host.E) (a : Fin N),
        u a = ∑ i, (∑ b, u b * D.host.conj (w i b)) * v i a := by
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have h : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h' : ∀ x : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x := h
  have hh : ∀ x y : Fin N → D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x = stdH D.host.E N x y := by
    intro x y
    rw [GlobalTheory.DualFamily.herm_one_eq]
    simp only [stdH, h, h', mul_comm]
  have hr : ∀ z : D.host.E, z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ z :=
    fun z => ⟨fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨-, m, v, w, hv, hw, he⟩ := GlobalTheory.exists_dual_family L hL.1
    (fun x hx y hy => by rw [hh, ← hr]; exact (hL.2.2 x).1 hx y hy)
    (fun x hx => (hL.2.2 x).2 fun y hy => by rw [hr, ← hh]; exact hx y hy)
  refine ⟨m, v, w, hv, hw, fun u a => ?_⟩
  have := congrFun (he u) a
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.DualFamily.herm_one_eq, h']
    using this

/- English proof (translation)
Use `Submodule.subset_span ⟨c, hc, _, Submodule.subset_span fun x hx => ?_, rfl⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `pairing_mem D hL hu hx`. Establish `: (Matrix.of fun a b => v a * D.host.conj (u b)).mulVec x = e • v`. Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `∑ b, v a * D.host.conj (u b) * x b = (e : D.host.E) * v a`.

Rewrite using `[he, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun b _ => by ring`. Rewrite using `[this]`. Conclude with `L'.smul_mem e hv`.
-/
theorem rank_one_mem (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) {c : D.host.E}
    (hc : c ∈ D.host.AA0) {u : Fin N → D.host.E} (hu : u ∈ L) {v : Fin N' → D.host.E}
    (hv : v ∈ L') :
    c • (Matrix.of fun a b => v a * D.host.conj (u b)) ∈ YYl D L L' := by
  refine Submodule.subset_span ⟨c, hc, _, Submodule.subset_span fun x hx => ?_, rfl⟩
  obtain ⟨e, he⟩ := pairing_mem D hL hu hx
  have : (Matrix.of fun a b => v a * D.host.conj (u b)).mulVec x = e • v := by
    funext a
    change ∑ b, v a * D.host.conj (u b) * x b = (e : D.host.E) * v a
    rw [he, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this]
  exact L'.smul_mem e hv

/- English proof (translation)
Introduce and unpack `D ⟨r, a, a', ha, ha', ht⟩ N N' L L' hL hL'`. Take `⟨m, u, u', hu, hu', eu⟩` from `exists_resolution D hL`. Take `⟨m', v, v', hv, hv', ev⟩` from `exists_resolution D hL'`. Set `Y : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E` to `fun p => a p.2.2 • Matrix.of fun s t => v p.1 s * D.host.conj (u p.2.1 t)`. Set `Y' : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E` to `fun p => a' p.2.2 • Matrix.of fun s t => v' p.1 s * D.host.conj (u' p.2.1 t)`.

Set `e` to `(Fintype.equivFin (Fin m' × Fin m × Fin r)).symm`. Use `⟨_, Y ∘ e, Y' ∘ e, fun i => rank_one_mem D hL (ha _) (hu _) (hv _), fun i => rank_one_mem D hL (ha' _) (hu' _) (hv' _), fun x => ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ (e.sum_comp fun p => hYY D x (Y' p) • Y p).symm` and prove the remaining obligations. Use `Matrix.ext fun s t => ?_` and prove the remaining obligations. Establish `eu' : ∀ (z : Fin N → D.host.E) (t : Fin N), z t = ∑ i, (∑ b, z b * u' i b) * D.host.conj (u i t)`.

Introduce `z t`. Use `congrArg D.host.conj (eu (fun b => D.host.conj (z b)) t)` as an intermediate fact. Simplify `this` using `only [map_sum, map_mul, conj_conj]`. Establish `hT : ∀ j i k, hYY D x (Y' (j, i, k)) = Algebra.trace D.host.K D.host.E ((∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b) * D.host.conj (a' k))`. Introduce `j i k`.

Unfold `hYY`. Use `congr 1`. Simplify using `only [Y', Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, conj_conj, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Rewrite using `[Matrix.sum_apply, Fintype.sum_prod_type, ev (fun c => x c t) s]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type, eu' (fun b => ∑ c, x c b * D.host.conj (v' j c)) t, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ht (∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b), Finset.sum_mul, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hT]`. Simplify using `only [Y, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, smul_mul_assoc]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_dual_family_hom : ∀ (D : D7), (∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∃ (r : ℕ) (y y' : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ YYl D L L') ∧ (∀ i, y' i ∈ YYl D L L') ∧ ∀ x : Matrix (Fin N') (Fin N) D.host.E, x = ∑ i, hYY D x (y' i) • y i := by
  rintro D ⟨r, a, a', ha, ha', ht⟩ N N' L L' hL hL'
  obtain ⟨m, u, u', hu, hu', eu⟩ := exists_resolution D hL
  obtain ⟨m', v, v', hv, hv', ev⟩ := exists_resolution D hL'
  let Y : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a p.2.2 • Matrix.of fun s t => v p.1 s * D.host.conj (u p.2.1 t)
  let Y' : Fin m' × Fin m × Fin r → Matrix (Fin N') (Fin N) D.host.E :=
    fun p => a' p.2.2 • Matrix.of fun s t => v' p.1 s * D.host.conj (u' p.2.1 t)
  let e := (Fintype.equivFin (Fin m' × Fin m × Fin r)).symm
  refine ⟨_, Y ∘ e, Y' ∘ e, fun i => rank_one_mem D hL (ha _) (hu _) (hv _),
    fun i => rank_one_mem D hL (ha' _) (hu' _) (hv' _), fun x => ?_⟩
  refine Eq.trans ?_ (e.sum_comp fun p => hYY D x (Y' p) • Y p).symm
  refine Matrix.ext fun s t => ?_
  have eu' : ∀ (z : Fin N → D.host.E) (t : Fin N),
      z t = ∑ i, (∑ b, z b * u' i b) * D.host.conj (u i t) := by
    intro z t
    have := congrArg D.host.conj (eu (fun b => D.host.conj (z b)) t)
    simpa only [map_sum, map_mul, conj_conj] using this
  have hT : ∀ j i k, hYY D x (Y' (j, i, k)) = Algebra.trace D.host.K D.host.E
      ((∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b) * D.host.conj (a' k)) := by
    intro j i k
    unfold hYY
    congr 1
    simp only [Y', Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, conj_conj,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.sum_apply, Fintype.sum_prod_type, ev (fun c => x c t) s]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, eu' (fun b => ∑ c, x c b * D.host.conj (v' j c)) t, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ht (∑ b, (∑ c, x c b * D.host.conj (v' j c)) * u' i b), Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hT]
  simp only [Y, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, smul_mul_assoc]
  congr 1
  ring

end GlobalTheory.HomDual
