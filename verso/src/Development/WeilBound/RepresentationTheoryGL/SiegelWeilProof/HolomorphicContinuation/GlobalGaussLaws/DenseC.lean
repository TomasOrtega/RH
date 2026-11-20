import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseB
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousAtMN
import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharDual

noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DenseP

open Formalism.IndefR.Eqv (psiT psiT_inclR)

variable {D : D7} {n : ℕ}

/- English proof (translation)
Establish `hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ)` using `Subfield.isClosed_topologicalClosure _`. Break down `Complex.subfield_eq_of_closed hc with h1 | h1` into its components or cases. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Establish `hx : σ x ∈ σ.fieldRange.topologicalClosure` using `Subfield.le_topologicalClosure _ ⟨x, rfl⟩`. Rewrite `hx` using `[h1]`. Take `⟨r, hr⟩` from `hx`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq, ← hr]`.

Conclude with `Complex.conj_ofReal r`. Establish `: closure (Set.range σ) = Set.univ`. Use `congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1` as an intermediate fact. Conclude with `this`. Conclude with `dense_iff_closure_eq.2 this`.
-/
theorem denseRange_of_not_isReal' {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ NumberField.ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[NumberField.ComplexEmbedding.isReal_iff]`. Establish `h1 : starRingEnd ℂ (tauE D τ D.host.xi0) = tauE D τ D.host.xi0`. Use `congrArg (fun f : D.host.E →+* ℂ => f D.host.xi0) h` as an intermediate fact. Simplify `this` using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`.

Establish `h2 : tauE D τ (star D.host.xi0) = starRingEnd ℂ (tauE D τ D.host.xi0)` using `Formalism.IndefR.Eqv.tauE_star D τ _`. Rewrite `h2` using `[Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, map_neg, h1]`. Establish `h3 : tauE D τ D.host.xi0 = 0`. Establish `: (2 : ℂ) * tauE D τ D.host.xi0 = 0` using `by linear_combination -h2`. Conclude with `(mul_eq_zero.1 this).resolve_left two_ne_zero`.

Conclude with `Formalism.IndefR.Fin.embedding_xi_zero_ne_zero ((map_eq_zero_iff _ (tauE D τ).injective).1 h3)`.
-/
theorem tauE_not_real (τ : D.what₂.Tau) : ¬ NumberField.ComplexEmbedding.IsReal (tauE D τ) := by
  intro h
  rw [NumberField.ComplexEmbedding.isReal_iff] at h
  have h1 : starRingEnd ℂ (tauE D τ D.host.xi0) = tauE D τ D.host.xi0 := by
    have := congrArg (fun f : D.host.E →+* ℂ => f D.host.xi0) h
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this
  have h2 : tauE D τ (star D.host.xi0) = starRingEnd ℂ (tauE D τ D.host.xi0) := Formalism.IndefR.Eqv.tauE_star D τ _
  rw [Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, map_neg, h1] at h2
  have h3 : tauE D τ D.host.xi0 = 0 := by
    have : (2 : ℂ) * tauE D τ D.host.xi0 = 0 := by linear_combination -h2
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact Formalism.IndefR.Fin.embedding_xi_zero_ne_zero ((map_eq_zero_iff _ (tauE D τ).injective).1 h3)

/- English proof (translation)
The claim follows from `denseRange_of_not_isReal' _ (tauE_not_real τ)`.
-/
theorem denseRange_tauE (τ : D.what₂.Tau) : DenseRange (tauE D τ) := denseRange_of_not_isReal' _ (tauE_not_real τ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sig_apply (x : D.host.E) : D.sp.cm.sig x = star x := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply, sig_apply, Formalism.IndefR.Eqv.tauE_star]`.
-/
theorem cT_map_tauE (τ : D.what₂.Tau) {k : ℕ} (u : Matrix (Fin k) (Fin k) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u).map (tauE D τ) = (u.map (tauE D τ))ᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, sig_apply, Formalism.IndefR.Eqv.tauE_star]

/- English proof (translation)
Rewrite using `[blk4, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]`.
-/
theorem block_matrix_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  rw [blk4, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

/- English proof (translation)
The claim follows from `map_zero (RingHom.mapMatrix (tauE D τ))`.
-/
theorem map0 (τ : D.what₂.Tau) : (0 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 0 :=
  map_zero (RingHom.mapMatrix (tauE D τ))

/- English proof (translation)
The claim follows from `map_one (RingHom.mapMatrix (tauE D τ))`.
-/
theorem map1 (τ : D.what₂.Tau) : (1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 1 :=
  map_one (RingHom.mapMatrix (tauE D τ))

/- English proof (translation)
Use `show RingHom.mapMatrix (tauE D τ) (-1) = -1`. Rewrite using `[map_neg, map_one]`.
-/
theorem mapn1 (τ : D.what₂.Tau) : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = -1 := by
  show RingHom.mapMatrix (tauE D τ) (-1) = -1
  rw [map_neg, map_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.map_apply, Matrix.smul_apply]`.
-/
theorem map_smul_E (τ : D.what₂.Tau) {k : ℕ} (c : D.host.E) (X : Matrix (Fin k) (Fin k) D.host.E) :
    (c • X).map (tauE D τ) = (tauE D τ c) • X.map (tauE D τ) := by
  ext i j; simp [Matrix.map_apply, Matrix.smul_apply]

/- English proof (translation)
Rewrite using `[Jst, block_matrix_map, map0, map1, mapn1]`. Both sides reduce to the same expression.
-/
theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = Glob.reidx (JJ n) := by
  rw [Jst, block_matrix_map, map0, map1, mapn1]
  rfl

/- English proof (translation)
Simplify using `[Glob.reidx, Matrix.submatrix_mul_equiv]`.
-/
theorem reidx_mul (a b : M2 n) : Glob.reidx (a * b) = Glob.reidx a * Glob.reidx b := by
  simp [Glob.reidx, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Simplify using `[Glob.reidx, Matrix.submatrix_one_equiv]`.
-/
theorem reidx_one : Glob.reidx (1 : M2 n) = 1 := by
  simp [Glob.reidx, Matrix.submatrix_one_equiv]

/- English proof (translation)
Simplify using `[Glob.reidx, Matrix.conjTranspose_submatrix]`.
-/
theorem reidx_conjTranspose (a : M2 n) : Glob.reidx aᴴ = (Glob.reidx a)ᴴ := by
  simp [Glob.reidx, Matrix.conjTranspose_submatrix]

/- English proof (translation)
Simplify using `only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem inG_JJc : InG (JJ n) := by
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp

/- English proof (translation)
Simplify using `[mat]`.
-/
theorem mat_one : mat (1 : G D n) = 1 := by simp [mat]

/- English proof (translation)
Simplify using `[mat]`.
-/
theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by simp [mat]

/- English proof (translation)
Establish `hdet : IsUnit u.det`. Establish `h1 : tauE D τ u.det = M.det`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hu, Glob.reidx, Matrix.det_submatrix_equiv_self]`. Establish `h2 : M.det ≠ 0` using `(isUnit_det_of_inG hM).ne_zero`. Use `isUnit_iff_ne_zero.2 fun h0 => h2 ?_` and prove the remaining obligations.

Rewrite using `[← h1, h0, map_zero]`. Set `U : GL (Fin (n + n)) D.host.E` to `⟨u, u⁻¹, Matrix.mul_nonsing_inv u hdet, Matrix.nonsing_inv_mul u hdet⟩`. Establish `hU : U ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n)` using `by show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u = Jst D n`. Establish `key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u).map (tauE D τ) = (Jst D n).map (tauE D τ)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, cT_map_tauE, Jst_map, hu, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, hM]`.

Conclude with `Matrix.map_injective (tauE D τ).injective key`. Use `⟨GlobalTheory.AdelicU.ratEmb D.sp.cm.sig (Jst D n) ⟨U, hU⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show _ ∈ GlobalTheory.AdelicU.ratPts D.sp.cm.sig (Jst D n)`. Rewrite using `[← GlobalTheory.AdelicU.range_ratEmb]`. Conclude with `MonoidHom.mem_range.2 ⟨_, rfl⟩`.

Use `show (u.map (inclR (AF D.host.F))).map (psiT D τ) = _`. Rewrite using `[Matrix.map_map]`. Establish `: (⇑(psiT D τ) ∘ ⇑(inclR (AF D.host.F))) = ⇑(tauE D τ)` using `funext fun e => psiT_inclR D τ e`. Rewrite using `[this, hu]`.
-/
theorem ratPt_of (τ : D.what₂.Tau) (u : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (M : M2 n) (hM : InG M)
    (hu : u.map (tauE D τ) = Glob.reidx M) : ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx M := by
  have hdet : IsUnit u.det := by
    have h1 : tauE D τ u.det = M.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hu, Glob.reidx, Matrix.det_submatrix_equiv_self]
    have h2 : M.det ≠ 0 := (isUnit_det_of_inG hM).ne_zero
    refine isUnit_iff_ne_zero.2 fun h0 => h2 ?_
    rw [← h1, h0, map_zero]
  let U : GL (Fin (n + n)) D.host.E := ⟨u, u⁻¹, Matrix.mul_nonsing_inv u hdet, Matrix.nonsing_inv_mul u hdet⟩
  have hU : U ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := by
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u = Jst D n
    have key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u).map (tauE D τ) =
        (Jst D n).map (tauE D τ) := by
      rw [Matrix.map_mul, Matrix.map_mul, cT_map_tauE, Jst_map, hu, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, hM]
    exact Matrix.map_injective (tauE D τ).injective key
  refine ⟨GlobalTheory.AdelicU.ratEmb D.sp.cm.sig (Jst D n) ⟨U, hU⟩, ?_, ?_⟩
  · show _ ∈ GlobalTheory.AdelicU.ratPts D.sp.cm.sig (Jst D n)
    rw [← GlobalTheory.AdelicU.range_ratEmb]; exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  · show (u.map (inclR (AF D.host.F))).map (psiT D τ) = _
    rw [Matrix.map_map]
    have : (⇑(psiT D τ) ∘ ⇑(inclR (AF D.host.F))) = ⇑(tauE D τ) := funext fun e => psiT_inclR D τ e
    rw [this, hu]

def gam (D : D7) (n : ℕ) (τ : D.what₂.Tau) : Subgroup (GR n) where
  carrier := {y | ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx (mR y)}
  one_mem' := ⟨1, one_mem _, by
    rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact reidx_one.symm⟩
  mul_mem' := by
    rintro a b ⟨γ, hγ, ea⟩ ⟨γ', hγ', eb⟩
    refine ⟨γ * γ', mul_mem hγ hγ', ?_⟩
    rw [mat_mul, Matrix.map_mul, ea, eb]
    exact (reidx_mul _ _).symm
  inv_mem' := by
    rintro a ⟨γ, hγ, ea⟩
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    have h1 : (mat γ⁻¹).map (psiT D τ) * (mat γ).map (psiT D τ) = 1 := by
      rw [← Matrix.map_mul, ← mat_mul, inv_mul_cancel, mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : Glob.reidx (mR a) * Glob.reidx (mR a⁻¹) = 1 := by
      rw [← reidx_mul]
      show Glob.reidx (mR (a * a⁻¹)) = 1
      rw [mul_inv_cancel]; exact reidx_one
    calc (mat γ⁻¹).map (psiT D τ) = (mat γ⁻¹).map (psiT D τ) * (Glob.reidx (mR a) * Glob.reidx (mR a⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = Glob.reidx (mR a⁻¹) := by rw [← Matrix.mul_assoc, ← ea, h1, Matrix.one_mul]

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext e)`.
-/
theorem mkGR_ext {g : M2 n} (hg : InG g) {h : GR n} (e : mR h = g) : h = mkGR g hg :=
  Subtype.ext (Units.ext e)

/- English proof (translation)
Break down `hh with ⟨b, hb, e⟩ | ⟨A, hA, e⟩ | e` into its components or cases. Establish `hh : h = nuE b`. Rewrite using `[mkGR_ext (inG_nUh (hpart_herm b)) (show mR h = nU (hpart b) by rw [hpart_of_herm hb]; exact e)]; rfl`. Rewrite using `[hh]`. Use `closure_mono ?_ (nuE_mem_closure (tauE D τ) (denseRange_tauE τ) b)` and prove the remaining obligations.

Introduce and unpack `_ ⟨e', rfl⟩`. Establish `hβ : ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')).map (tauE D τ) = hpart (e'.map (tauE D τ))`. Rewrite using `[map_smul_E, Matrix.map_add _ (map_add (tauE D τ)), cT_map_tauE, map_inv₀, map_ofNat, hpart, one_div]`. Take `⟨γ, hγ, he⟩` from `ratPt_of τ (blk4 1 ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')) 0 1) (nU (hpart (e'.map (tauE D τ)))) (inG_nUh (hpart_herm _)) (by`. Rewrite using `[block_matrix_map, map0, map1, hβ]`.

Use the proof step `rfl)`. Conclude with `⟨γ, hγ, he⟩`. Establish `hh : h = mlE A` using `by rw [mlE_of hA]; exact mkGR_ext (inG_mL hA) e`. Rewrite using `[hh]`. Use `closure_mono ?_ (mlE_mem_closure (tauE D τ) (denseRange_tauE τ) A hA)` and prove the remaining obligations.

Introduce and unpack `_ ⟨B, ⟨hB, e', rfl⟩, rfl⟩`. Establish `hdet : IsUnit e'.det`. Establish `h1 : tauE D τ e'.det = (e'.map (tauE D τ)).det` using `by rw [RingHom.map_det, RingHom.mapMatrix_apply]`. Use `isUnit_iff_ne_zero.2 fun h0 => (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero ?_` and prove the remaining obligations. Rewrite using `[← h1, h0, map_zero]`.

Establish `hcd : IsUnit (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det`. Establish `h1 : tauE D τ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det = ((e'.map (tauE D τ))ᴴ).det`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, cT_map_tauE]`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Establish `: ((e'.map (tauE D τ))ᴴ).det = 0` using `by rw [← h1, h0, map_zero]`.

Rewrite `this` using `[Matrix.det_conjTranspose, star_eq_zero]`. Conclude with `(hB : IsUnit (e'.map (tauE D τ)).det).ne_zero this`. Establish `hinv : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹).map (tauE D τ) = ((e'.map (tauE D τ))⁻¹)ᴴ`. Rewrite using `[Matrix.conjTranspose_nonsing_inv, ← cT_map_tauE]`. Use `(Matrix.inv_eq_right_inv ?_).symm` and prove the remaining obligations.

Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hcd, Matrix.map_one _ (map_zero _) (map_one _)]`. Take `⟨γ, hγ, he⟩` from `ratPt_of τ (blk4 e' 0 0 (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹) (fromBlocks (e'.map (tauE D τ)) 0 0 ((e'.map (tauE D τ))⁻¹)ᴴ) (inG_mL hB) (by`. Rewrite using `[block_matrix_map, hinv, map0]`. Use the proof step `rfl)`. Use `⟨γ, hγ, ?_⟩` and prove the remaining obligations.

Rewrite using `[he, mlE_of hB]`. Both sides reduce to the same expression. Use `(gam D n τ).le_topologicalClosure ?_` and prove the remaining obligations. Take `⟨γ, hγ, he⟩` from `ratPt_of τ (Jst D n) (JJ n) inG_JJc (Jst_map τ)`. Conclude with `⟨γ, hγ, by rw [he, e]⟩`.
-/
theorem gens_mem (τ : D.what₂.Tau) (h : GR n) (hh : IsNElt h ∨ IsMElt h ∨ IsWElt h) :
    h ∈ (gam D n τ).topologicalClosure := by
  rcases hh with ⟨b, hb, e⟩ | ⟨A, hA, e⟩ | e
  · have hh : h = nuE b := by
      rw [mkGR_ext (inG_nUh (hpart_herm b)) (show mR h = nU (hpart b) by rw [hpart_of_herm hb]; exact e)]; rfl
    rw [hh]
    refine closure_mono ?_ (nuE_mem_closure (tauE D τ) (denseRange_tauE τ) b)
    rintro _ ⟨e', rfl⟩
    have hβ : ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')).map (tauE D τ) =
        hpart (e'.map (tauE D τ)) := by
      rw [map_smul_E, Matrix.map_add _ (map_add (tauE D τ)), cT_map_tauE, map_inv₀, map_ofNat, hpart, one_div]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 1 ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')) 0 1)
      (nU (hpart (e'.map (tauE D τ)))) (inG_nUh (hpart_herm _)) (by
        rw [block_matrix_map, map0, map1, hβ]
        rfl)
    exact ⟨γ, hγ, he⟩
  · have hh : h = mlE A := by rw [mlE_of hA]; exact mkGR_ext (inG_mL hA) e
    rw [hh]
    refine closure_mono ?_ (mlE_mem_closure (tauE D τ) (denseRange_tauE τ) A hA)
    rintro _ ⟨B, ⟨hB, e', rfl⟩, rfl⟩
    have hdet : IsUnit e'.det := by
      have h1 : tauE D τ e'.det = (e'.map (tauE D τ)).det := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
      refine isUnit_iff_ne_zero.2 fun h0 => (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero ?_
      rw [← h1, h0, map_zero]
    have hcd : IsUnit (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det := by
      have h1 : tauE D τ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det = ((e'.map (tauE D τ))ᴴ).det := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, cT_map_tauE]
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have : ((e'.map (tauE D τ))ᴴ).det = 0 := by rw [← h1, h0, map_zero]
      rw [Matrix.det_conjTranspose, star_eq_zero] at this
      exact (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero this
    have hinv : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹).map (tauE D τ) =
        ((e'.map (tauE D τ))⁻¹)ᴴ := by
      rw [Matrix.conjTranspose_nonsing_inv, ← cT_map_tauE]
      refine (Matrix.inv_eq_right_inv ?_).symm
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hcd, Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 e' 0 0 (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹)
      (fromBlocks (e'.map (tauE D τ)) 0 0 ((e'.map (tauE D τ))⁻¹)ᴴ) (inG_mL hB) (by
        rw [block_matrix_map, hinv, map0]
        rfl)
    refine ⟨γ, hγ, ?_⟩
    rw [he, mlE_of hB]
    rfl
  · refine (gam D n τ).le_topologicalClosure ?_
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (Jst D n) (JJ n) inG_JJc (Jst_map τ)
    exact ⟨γ, hγ, by rw [he, e]⟩

/- English proof (translation)
Establish `h1 : Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h} ≤ (gam D n τ).topologicalClosure` using `(Subgroup.closure_le _).2 fun h hh => gens_mem τ h hh`. Conclude with `h1 (hgen n g)`.
-/
theorem gam_dense (hgen : GenSt) (τ : D.what₂.Tau) (g : GR n) : g ∈ closure (gam D n τ : Set (GR n)) := by
  have h1 : Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h} ≤ (gam D n τ).topologicalClosure :=
    (Subgroup.closure_le _).2 fun h hh => gens_mem τ h hh
  exact h1 (hgen n g)

end PositivityTheory.Rg.Sw.Glob.DenseP
