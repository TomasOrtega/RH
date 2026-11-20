import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HeightBoundOfQuasiHeightLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Establish `hb' : (b.val : Matrix (Fin a) (Fin a) (Ad E)).IsUpperTriangular` using `hb`. Rewrite using `[Units.val_mul, Units.val_mul, Reduction.coe_diagUnits, Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[Matrix.mul_diagonal]`. Expand and normalize the polynomial expressions, which then agree. Introduce `l _ hl`.

Establish `hlt : l < i`. Establish `h1` using `l.2`. Establish `h2 : l.val ≠ i.val` using `fun h => hl (Fin.ext h)`. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Matrix.mul_diagonal, hb' hlt, zero_mul, zero_mul]`. Simplify using the standard rewrite rules.
-/
private theorem row_last (i : Fin a) (hi : i.val + 1 = a) (b k : GA E a)
    (hb : b ∈ Reduction.adelicBorel (K := E) (n := a)) (d : Fin a → (Ad E)ˣ) (j : Fin a) :
    (b * Reduction.diagUnits a d * k : GA E a).val i j = (d i : Ad E) * (b.val i i * k.val i j) := by
  have hb' : (b.val : Matrix (Fin a) (Fin a) (Ad E)).IsUpperTriangular := hb
  rw [Units.val_mul, Units.val_mul, Reduction.coe_diagUnits, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.mul_diagonal]; ring
  · intro l _ hl
    have hlt : l < i := by
      have h1 := l.2
      have h2 : l.val ≠ i.val := fun h => hl (Fin.ext h)
      rw [Fin.lt_def]; omega
    rw [Matrix.mul_diagonal, hb' hlt, zero_mul, zero_mul]
  · simp

/- English proof (translation)
Rewrite using `[Units.val_mul, Matrix.mul_apply, map_sum, Matrix.vecMul, dotProduct]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
private theorem row_map {R : Type} [CommRing R] (f : Ad E →+* R) (γ : GL (Fin a) E) (g : GA E a) (i j : Fin a) :
    ((fun l => f (algebraMap E (Ad E) (γ.val i l))) ᵥ* (GeneralLinearGroup.map f g).val) j =
      f ((ratGL E a γ * g).val i j) := by
  rw [Units.val_mul, Matrix.mul_apply, map_sum, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]
  rfl

variable [IsTotallyComplex E]

/- English proof (translation)
The claim follows from `(InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x.1 w)`.
-/
private theorem norm_pInf (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x.1 w)

/- English proof (translation)
The claim follows from `continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst)`.
-/
private theorem cont_pInf : Continuous (pInf E) :=
  continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

end

/- English proof (translation)
Introduce `E _ _ _ a ha`. Take `⟨Ω, C, N, hΩ, hB, h⟩` from `UpperTheory.height_bound_of_quasiHeight_le E a`. Set `i : Fin a` to `⟨a - 1, by omega⟩`. Establish `hi : i.val + 1 = a` using `by simp only [i]; omega`. Set `Φ : GA E a × GA E a → Fin a → Ad E` to `fun p j => p.1.val i i * p.2.val i j`.

Establish `hΦ : ∀ j, Continuous fun p => Φ p j` using `fun j => ((Units.continuous_val.comp continuous_fst).matrix_elem i i).mul ((Units.continuous_val.comp continuous_snd).matrix_elem i j)`. Establish `hS` using `hΩ.prod (Reduction.isCompact_maxCompact (K := E) (n := a))`. Establish `hF : Continuous fun (p : GA E a × GA E a) (j : Fin a) => pFin E (Φ p j)` using `continuous_pi fun j => continuous_snd.comp (hΦ j)`. Establish `hI : Continuous fun p : GA E a × GA E a => qf fun j => pInf E (Φ p j)` using `continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun w _ => ((continuous_apply w).comp (cont_pInf.comp (hΦ j))).norm.pow 2`. Take `⟨M, hM⟩` from `hS.exists_bound_of_continuousOn hI.continuousOn`.

Use `⟨_, C * M ^ N, N, hS.image hF, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, b, k, ρ, hρ, hb, hk, e, hq⟩` from `h g`. Establish `hrow : ∀ j, (ratGL E a γ * g.1).val i j = ((Reduction.posIdele (K` using `E) (ρ i) (hρ i) : (Ad E)ˣ) : Ad E) * Φ (b, k) j := fun j => by`. Rewrite using `[e]`. Conclude with `row_last i hi b k (hB b hb) _ j`.

Use `⟨γ.val i, fun h0 => ?_, ⟨(b, k), ⟨hb, hk⟩, funext fun j => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun (congrFun γ.mul_inv i) i`. Simplify using `[Matrix.mul_apply, h0] at h1`. Use `Eq.trans ?_ (row_map (pFin E) γ g.1 i j).symm` and prove the remaining obligations. Establish `h1 : pFin E ((Reduction.posIdele (K` using `E) (ρ i) (hρ i) : (Ad E)ˣ) : Ad E) = 1 := IsDedekindDomain.FiniteAdeleRing.ext _ fun v => Reduction.posIdele_finite (K := E) (ρ i) (hρ i) v`.

Rewrite using `[hrow, map_mul, h1, one_mul]`. Establish `h1 : qf (pt (E` using `E) (a := a) g.1 (γ.val i)) = ρ i ^ 2 * qf fun j => pInf E (Φ (b, k) j) := by`. Unfold `qf`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `h2 : pt (E` using `E) (a := a) g.1 (γ.val i) j = _ := row_map (pInf E) γ g.1 i j`. Rewrite using `[h2, hrow, map_mul, Pi.mul_apply, norm_mul, norm_pInf, Reduction.norm_posIdele_infinite, mul_pow]`. Establish `h3 : (qf fun j => pInf E (Φ (b, k) j)) ≤ M` using `(Real.le_norm_self _).trans (hM (b, k) ⟨hb, hk⟩)`.

Establish `h4 : 0 ≤ qht (E` using `E) (a := a) g.1 := Real.iInf_nonneg fun _ => (AutomorphicForm.height_pos _).le`. Establish `h5` using `(hq i).1 hi`. Establish `h6 : 0 ≤ qht (E` using `E) (a := a) g.1 * ρ i ^ (2 * N) := mul_nonneg h4 (pow_nonneg (hρ i).le _)`. Rewrite using `[h1, mul_pow, ← pow_mul, ← mul_assoc]`. Conclude with `mul_le_mul h5 (pow_le_pow_left₀ (qf_nonneg _) h3 N) (pow_nonneg (qf_nonneg _) N) (h6.trans h5)`.
-/
theorem UpperTheory.infinite_place_norm_continuity :
    SiegelRow := by
  intro E _ _ _ a ha
  obtain ⟨Ω, C, N, hΩ, hB, h⟩ := UpperTheory.height_bound_of_quasiHeight_le E a
  let i : Fin a := ⟨a - 1, by omega⟩
  have hi : i.val + 1 = a := by simp only [i]; omega
  let Φ : GA E a × GA E a → Fin a → Ad E := fun p j => p.1.val i i * p.2.val i j
  have hΦ : ∀ j, Continuous fun p => Φ p j := fun j =>
    ((Units.continuous_val.comp continuous_fst).matrix_elem i i).mul
      ((Units.continuous_val.comp continuous_snd).matrix_elem i j)
  have hS := hΩ.prod (Reduction.isCompact_maxCompact (K := E) (n := a))
  have hF : Continuous fun (p : GA E a × GA E a) (j : Fin a) => pFin E (Φ p j) :=
    continuous_pi fun j => continuous_snd.comp (hΦ j)
  have hI : Continuous fun p : GA E a × GA E a => qf fun j => pInf E (Φ p j) :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun w _ =>
      ((continuous_apply w).comp (cont_pInf.comp (hΦ j))).norm.pow 2
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hI.continuousOn
  refine ⟨_, C * M ^ N, N, hS.image hF, fun g => ?_⟩
  obtain ⟨γ, b, k, ρ, hρ, hb, hk, e, hq⟩ := h g
  have hrow : ∀ j, (ratGL E a γ * g.1).val i j =
      ((Reduction.posIdele (K := E) (ρ i) (hρ i) : (Ad E)ˣ) : Ad E) * Φ (b, k) j := fun j => by
    rw [e]
    exact row_last i hi b k (hB b hb) _ j
  refine ⟨γ.val i, fun h0 => ?_, ⟨(b, k), ⟨hb, hk⟩, funext fun j => ?_⟩, ?_⟩
  · have h1 := congrFun (congrFun γ.mul_inv i) i
    simp [Matrix.mul_apply, h0] at h1
  · refine Eq.trans ?_ (row_map (pFin E) γ g.1 i j).symm
    have h1 : pFin E ((Reduction.posIdele (K := E) (ρ i) (hρ i) : (Ad E)ˣ) : Ad E) = 1 :=
      IsDedekindDomain.FiniteAdeleRing.ext _ fun v => Reduction.posIdele_finite (K := E) (ρ i) (hρ i) v
    rw [hrow, map_mul, h1, one_mul]
  · have h1 : qf (pt (E := E) (a := a) g.1 (γ.val i)) = ρ i ^ 2 * qf fun j => pInf E (Φ (b, k) j) := by
      unfold qf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      have h2 : pt (E := E) (a := a) g.1 (γ.val i) j = _ := row_map (pInf E) γ g.1 i j
      rw [h2, hrow, map_mul, Pi.mul_apply, norm_mul, norm_pInf, Reduction.norm_posIdele_infinite, mul_pow]
    have h3 : (qf fun j => pInf E (Φ (b, k) j)) ≤ M := (Real.le_norm_self _).trans (hM (b, k) ⟨hb, hk⟩)
    have h4 : 0 ≤ qht (E := E) (a := a) g.1 := Real.iInf_nonneg fun _ => (AutomorphicForm.height_pos _).le
    have h5 := (hq i).1 hi
    have h6 : 0 ≤ qht (E := E) (a := a) g.1 * ρ i ^ (2 * N) := mul_nonneg h4 (pow_nonneg (hρ i).le _)
    rw [h1, mul_pow, ← pow_mul, ← mul_assoc]
    exact mul_le_mul h5 (pow_le_pow_left₀ (qf_nonneg _) h3 N) (pow_nonneg (qf_nonneg _) N) (h6.trans h5)
