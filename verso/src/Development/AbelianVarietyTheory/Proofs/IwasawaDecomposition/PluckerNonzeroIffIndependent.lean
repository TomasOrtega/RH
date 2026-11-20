import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjective
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

noncomputable section

namespace GlobalTheory.FlagEmb.PlkSpan

/- English proof (translation)
Take `⟨q, hq⟩` from `Function.ne_iff.1 h`. Use `set r := GlobalTheory.FlagEmb.plE N k q`. Establish `hdet : (Matrix.of fun l l' => u l (r l')).det ≠ 0` using `hq`. Establish `hA` using `Matrix.linearIndependent_rows_of_det_ne_zero hdet`. Use `LinearIndependent.of_comp (LinearMap.funLeft K K r) ?_` and prove the remaining obligations.

Conclude with `hA`.
-/
theorem indep_of_plk_ne_zero (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : plk u id ≠ 0) : LinearIndependent K u := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h
  set r := GlobalTheory.FlagEmb.plE N k q
  have hdet : (Matrix.of fun l l' => u l (r l')).det ≠ 0 := hq
  have hA := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  refine LinearIndependent.of_comp (LinearMap.funLeft K K r) ?_
  exact hA

/- English proof (translation)
Set `Q : Matrix (Fin (N + 1)) (Fin k) K` to `(Matrix.of u).transpose`. Establish `hinj : Function.Injective Q.mulVec`. Introduce `x y hxy`. Establish `h0 : Q.mulVec (x - y) = 0` using `by rw [Matrix.mulVec_sub, hxy, sub_self]`. Establish `h1 : ∑ l, (x - y) l • u l = 0`.

Use function extensionality and compare the values at `r`. Use `congrFun h0 r` as an intermediate fact. Simplify using `only [Q, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.zero_apply] at this`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Rewrite using `[← this]`.

Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`. Establish `h2` using `(Fintype.linearIndependent_iff.1 h) _ h1`. Use function extensionality and compare the values at `l`. Conclude with `sub_eq_zero.1 (h2 l)`. Take `⟨Q', hQ'⟩` from `GlobalTheory.matrix_exists_left_inverse_of_field Q hinj`.

Establish `hCB` using `GlobalTheory.FlagEmb.CauchyBinet.lform_plk K N k (Fin k) (Fin k) (fun l => Q' l) u id id`. Establish `hM : (Matrix.of fun l l' => ∑ r, (fun l => Q' l) (id l') r * u (id l) r) = (Q' * Q).transpose`. Use extensionality with `l l'`. Simplify using `[Q, Matrix.mul_apply, mul_comm]`. Rewrite `hCB` using `[hM, hQ', Matrix.transpose_one, Matrix.det_one]`.

Introduce `h0`. Rewrite `hCB` using `[h0]`. Simplify using `at hCB`.
-/
theorem plk_ne_zero_of_indep (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : LinearIndependent K u) : plk u id ≠ 0 := by
  let Q : Matrix (Fin (N + 1)) (Fin k) K := (Matrix.of u).transpose
  have hinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have h0 : Q.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 : ∑ l, (x - y) l • u l = 0 := by
      funext r
      have := congrFun h0 r
      simp only [Q, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have h2 := (Fintype.linearIndependent_iff.1 h) _ h1
    funext l
    exact sub_eq_zero.1 (h2 l)
  obtain ⟨Q', hQ'⟩ := GlobalTheory.matrix_exists_left_inverse_of_field Q hinj
  have hCB := GlobalTheory.FlagEmb.CauchyBinet.lform_plk K N k (Fin k) (Fin k) (fun l => Q' l) u id id
  have hM : (Matrix.of fun l l' => ∑ r, (fun l => Q' l) (id l') r * u (id l) r) = (Q' * Q).transpose := by
    ext l l'
    simp [Q, Matrix.mul_apply, mul_comm]
  rw [hM, hQ', Matrix.transpose_one, Matrix.det_one] at hCB
  intro h0
  rw [h0] at hCB
  simp at hCB

/- English proof (translation)
Use function extensionality and compare the values at `q`. Simplify using `only [plk, id, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← Matrix.det_mul]`. Use `congr 1`. Use extensionality with `l l'`.

Simplify using `[Matrix.mul_apply, Finset.sum_apply]`.
-/
theorem plk_comb (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K) (T : Matrix (Fin k) (Fin k) K) :
    plk (fun l => ∑ j, T l j • u j) id = T.det • plk u id := by
  funext q
  simp only [plk, id, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.det_mul]
  congr 1
  ext l l'
  simp [Matrix.mul_apply, Finset.sum_apply]

/- English proof (translation)
Introduce `K _ N k u u'`. Use `⟨⟨indep_of_plk_ne_zero K N k u, plk_ne_zero_of_indep K N k u⟩, fun hu => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨hu', hs⟩ choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun K).1 (hs ▸ Submodule.subset_span ⟨l, rfl⟩ : u' l ∈ Submodule.span K (Set.range u))`. Establish `h1` using `plk_comb K N k u (Matrix.of c)`. Establish `h2 : (fun l => ∑ j, (Matrix.of c) l j • u j) = u'` using `funext hc`.

Rewrite `h1` using `[h2]`. Establish `hd : (Matrix.of c).det ≠ 0`. Introduce `h0`. Conclude with `plk_ne_zero_of_indep K N k u' hu' (by rw [h1, h0, zero_smul])`. Conclude with `⟨Units.mk0 _ hd, h1⟩`.

Introduce and unpack `⟨r, hr⟩`. Establish `h0` using `plk_ne_zero_of_indep K N k u hu`. Establish `h0' : plk u' id ≠ 0`. Rewrite using `[hr]`. Conclude with `smul_ne_zero r.ne_zero h0`.

Establish `hr' : plk u id = (r : K)⁻¹ • plk u' id`. Rewrite using `[hr, smul_smul, inv_mul_cancel₀ r.ne_zero, one_smul]`. Use `⟨indep_of_plk_ne_zero K N k u' h0', le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`.

Conclude with `mem_span_of_plk_eq_smul K N k u u' _ h0' hr l`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `mem_span_of_plk_eq_smul K N k u' u _ h0 hr' l`.
-/
theorem main : ∀ (K : Type) [Field K] (N k : ℕ) (u u' : Fin k → Fin (N + 1) → K), (plk u id ≠ 0 ↔ LinearIndependent K u) ∧ (LinearIndependent K u → ((LinearIndependent K u' ∧ Submodule.span K (Set.range u') = Submodule.span K (Set.range u)) ↔ ∃ r : Kˣ, plk u' id = (r : K) • plk u id)) := by
  intro K _ N k u u'
  refine ⟨⟨indep_of_plk_ne_zero K N k u, plk_ne_zero_of_indep K N k u⟩, fun hu => ⟨?_, ?_⟩⟩
  · rintro ⟨hu', hs⟩
    choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun K).1
      (hs ▸ Submodule.subset_span ⟨l, rfl⟩ : u' l ∈ Submodule.span K (Set.range u))
    have h1 := plk_comb K N k u (Matrix.of c)
    have h2 : (fun l => ∑ j, (Matrix.of c) l j • u j) = u' := funext hc
    rw [h2] at h1
    have hd : (Matrix.of c).det ≠ 0 := by
      intro h0
      exact plk_ne_zero_of_indep K N k u' hu' (by rw [h1, h0, zero_smul])
    exact ⟨Units.mk0 _ hd, h1⟩
  · rintro ⟨r, hr⟩
    have h0 := plk_ne_zero_of_indep K N k u hu
    have h0' : plk u' id ≠ 0 := by
      rw [hr]
      exact smul_ne_zero r.ne_zero h0
    have hr' : plk u id = (r : K)⁻¹ • plk u' id := by
      rw [hr, smul_smul, inv_mul_cancel₀ r.ne_zero, one_smul]
    refine ⟨indep_of_plk_ne_zero K N k u' h0', le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u u' _ h0' hr l
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u' u _ h0 hr' l

end GlobalTheory.FlagEmb.PlkSpan
