import Formalism.LatticeSlopes.Statement
import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram

open Module Submodule

noncomputable section

namespace Formalism.F

universe u

/- English proof (translation)
Set `V` to `span ℝ (L : Set E)`. Set `L' : Submodule ℤ V` to `L.comap (V.subtype.restrictScalars ℤ)`. Set `φ : L' ≃ₗ[ℤ] L` to `{ toFun := fun x => ⟨((x : V) : E), x.2⟩ invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Use `haveI : DiscreteTopology L' := DiscreteTopology.of_continuous_injective (f := fun x : L' => (⟨((x : V) : E), x.2⟩ : L)) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) (fun a b h => by`. Establish `h'` using `congrArg Subtype.val h`.

Simplify using `only at h'`. Conclude with `Subtype.ext (Subtype.ext h'))`. Use `haveI : IsZLattice ℝ L' := ⟨Submodule.span_span_coe_preimage⟩`. Conclude with `φ.finrank_eq.symm.trans (ZLattice.rank ℝ L')`.
-/
private theorem finrank_int_eq_finrank_span_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (span ℝ (L : Set E)) := by

  let V := span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L' ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : V) : E), x.2⟩
      invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : L' => (⟨((x : V) : E), x.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨Submodule.span_span_coe_preimage⟩
  exact φ.finrank_eq.symm.trans (ZLattice.rank ℝ L')

/- English proof (translation)
Establish `hspanZ : span ℤ (Set.range fun i => (e i : E)) = L`. Establish `: (Set.range fun i => (e i : E)) = L.subtype '' Set.range e` using `Set.range_comp _ _`. Rewrite using `[this, ← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]`. Establish `hspanR : span ℝ (Set.range fun i => (e i : E)) = span ℝ (L : Set E)`. Rewrite using `[← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (e i : E)), hspanZ]`.

Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR, ← finrank_int_eq_finrank_span_real L, Module.finrank_eq_card_basis e]`.
-/
theorem linearIndependent_coe_basis' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (e i : E)) := by
  have hspanZ : span ℤ (Set.range fun i => (e i : E)) = L := by
    have : (Set.range fun i => (e i : E)) = L.subtype '' Set.range e := Set.range_comp _ _
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
  have hspanR : span ℝ (Set.range fun i => (e i : E)) = span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (e i : E)), hspanZ]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR, ← finrank_int_eq_finrank_span_real L,
    Module.finrank_eq_card_basis e]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, RingHom.mapMatrix_apply, Matrix.map_apply]`. Conclude with `Finset.sum_congr rfl (fun _ _ => mul_comm _ _)`.
-/
theorem gram_intMatrix_eq_map {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin m) κ ℤ) :
    Matrix.gram ℝ (fun j => (WithLp.toLp 2 (fun i => (M i j : ℝ)) : EuclideanSpace ℝ (Fin m)))
      = (Int.castRingHom ℝ).mapMatrix (M.transpose * M) := by
  ext i j
  simp [Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/- English proof (translation)
Introduce `E _ _ _ L hL`. Use `haveI := hL`. Set `e` to `Module.finBasis ℤ L`. Establish `he : LinearIndependent ℝ (fun i => (e i : E))` using `linearIndependent_coe_basis' L e`. Set `S : EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) →ₗ[ℝ] E` to `{ toFun := fun x => ∑ i, WithLp.ofLp x i • (e i : E) map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }`.

Establish `hSinj : LinearMap.ker S = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `x hx`. Establish `h0` using `Fintype.linearIndependent_iff.mp he (fun i => WithLp.ofLp x i) hx`. Establish `h1 : WithLp.ofLp x = 0` using `funext h0`.

Simplify using `using congrArg (WithLp.toLp 2) h1`. Take `⟨K, hK0, hK⟩` from `S.exists_antilipschitzWith hSinj`. Establish `hKpos : (0 : ℝ) < K` using `hK0`. Use `⟨Real.log K, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨N, hNL, hN0, rfl⟩`.

Use `haveI hN : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hNL`. Set `f` to `Module.finBasis ℤ N`. Set `M : Matrix (Fin (Module.finrank ℤ L)) (Fin (Module.finrank ℤ N)) ℤ` to `fun i j => e.repr ⟨(f j : E), hNL (f j).2⟩ i`. Establish `hfj : ∀ j, (f j : E) = ∑ i, (M i j : ℝ) • (e i : E)`. Introduce `j`.

Establish `h` using `congrArg Subtype.val (e.sum_repr ⟨(f j : E), hNL (f j).2⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`. Simplify using `only [M, Int.cast_smul_eq_zsmul]`. Conclude with `h.symm`. Set `w : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ L))` to `fun j => WithLp.toLp 2 (fun i => (M i j : ℝ))`.

Establish `hSw : ∀ j, S (w j) = (f j : E)`. Introduce `j`. Rewrite using `[hfj j]`. Simplify using `[S, w]`. Establish `hcomp : ∀ c : Fin (Module.finrank ℤ N) → ℝ, ‖∑ j, c j • w j‖ ≤ (K : ℝ) * ‖∑ j, c j • (f j : E)‖`.

Introduce `c`. Establish `h1 : S (∑ j, c j • w j) = ∑ j, c j • (f j : E)`. Simplify using `only [map_sum, map_smul, hSw]`. Rewrite using `[← h1]`. Simplify `hK.le_mul_dist (∑ j, c j • w j) 0` using `[dist_eq_norm]`.

Establish `hdet` using `hG E (EuclideanSpace ℝ (Fin (Module.finrank ℤ L))) (Fin (Module.finrank ℤ N)) (fun j => (f j : E)) w K hcomp`. Rewrite `hdet` using `[gram_intMatrix_eq_map M, ← RingHom.map_det, Fintype.card_fin]`. Establish `hwli : LinearIndependent ℝ w`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`.

Establish `h2 : ∑ j, c j • (f j : E) = 0`. Rewrite using `[← map_zero S, ← hc]`. Simplify using `only [map_sum, map_smul, hSw]`. Conclude with `Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis' N f) c h2`. Establish `hwpos : 0 < (Matrix.gram ℝ w).det` using `(Matrix.posDef_gram_of_linearIndependent hwli).det_pos`.

Rewrite `hwpos` using `[gram_intMatrix_eq_map M, ← RingHom.map_det]`. Establish `hd1 : (1 : ℝ) ≤ (Int.castRingHom ℝ) (M.transpose * M).det`. Simplify using `only [eq_intCast] at hwpos ⊢`. Establish `: (0 : ℤ) < (M.transpose * M).det` using `by exact_mod_cast hwpos`. Conclude with `this` after adjusting the coercions.

Establish `hk : (0 : ℝ) < (Module.finrank ℤ N : ℝ)` using `by haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0`. Conclude with `Module.finrank_pos` after adjusting the coercions. Use `set g := (Matrix.gram ℝ (fun j => (f j : E))).det with hg`. Establish `hgK : 1 ≤ (K : ℝ) ^ (2 * Module.finrank ℤ N) * g` using `hd1.trans hdet`. Establish `hgpos : 0 < g`.

Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `: (K : ℝ) ^ (2 * Module.finrank ℤ N) * g ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog : -(2 * (Module.finrank ℤ N : ℝ)) * Real.log K ≤ Real.log g`.

Establish `h1 : Real.log 1 ≤ Real.log ((K : ℝ) ^ (2 * Module.finrank ℤ N) * g)` using `Real.log_le_log one_pos hgK`. Rewrite `h1` using `[Real.log_one, Real.log_mul (by positivity) hgpos.ne', Real.log_pow]`. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcov : covol N = Real.sqrt g` using `by rw [covol, dif_pos hN]`.

Use `show -Real.log (covol N) / (Module.finrank ℤ N : ℝ) ≤ Real.log K`. Rewrite using `[hcov, Real.log_sqrt hgpos.le, div_le_iff₀ hk]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem slopesBdd_of (hG : GramDetLe.{u, 0, 0}) : SlopesBdd.{u} := by
  intro E _ _ _ L hL
  haveI := hL
  let e := Module.finBasis ℤ L
  have he : LinearIndependent ℝ (fun i => (e i : E)) := linearIndependent_coe_basis' L e

  let S : EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, WithLp.ofLp x i • (e i : E)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h0 := Fintype.linearIndependent_iff.mp he (fun i => WithLp.ofLp x i) hx
    have h1 : WithLp.ofLp x = 0 := funext h0
    simpa using congrArg (WithLp.toLp 2) h1
  obtain ⟨K, hK0, hK⟩ := S.exists_antilipschitzWith hSinj
  have hKpos : (0 : ℝ) < K := hK0
  refine ⟨Real.log K, ?_⟩
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI hN : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hNL
  let f := Module.finBasis ℤ N
  let M : Matrix (Fin (Module.finrank ℤ L)) (Fin (Module.finrank ℤ N)) ℤ :=
    fun i j => e.repr ⟨(f j : E), hNL (f j).2⟩ i
  have hfj : ∀ j, (f j : E) = ∑ i, (M i j : ℝ) • (e i : E) := by
    intro j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hNL (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simp only [M, Int.cast_smul_eq_zsmul]
    exact h.symm
  let w : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) :=
    fun j => WithLp.toLp 2 (fun i => (M i j : ℝ))
  have hSw : ∀ j, S (w j) = (f j : E) := by
    intro j
    rw [hfj j]
    simp [S, w]
  have hcomp : ∀ c : Fin (Module.finrank ℤ N) → ℝ,
      ‖∑ j, c j • w j‖ ≤ (K : ℝ) * ‖∑ j, c j • (f j : E)‖ := by
    intro c
    have h1 : S (∑ j, c j • w j) = ∑ j, c j • (f j : E) := by
      simp only [map_sum, map_smul, hSw]
    rw [← h1]
    simpa [dist_eq_norm] using hK.le_mul_dist (∑ j, c j • w j) 0
  have hdet := hG E (EuclideanSpace ℝ (Fin (Module.finrank ℤ L))) (Fin (Module.finrank ℤ N))
    (fun j => (f j : E)) w K hcomp
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det, Fintype.card_fin] at hdet

  have hwli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h2 : ∑ j, c j • (f j : E) = 0 := by
      rw [← map_zero S, ← hc]
      simp only [map_sum, map_smul, hSw]
    exact Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis' N f) c h2
  have hwpos : 0 < (Matrix.gram ℝ w).det := (Matrix.posDef_gram_of_linearIndependent hwli).det_pos
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det] at hwpos
  have hd1 : (1 : ℝ) ≤ (Int.castRingHom ℝ) (M.transpose * M).det := by
    simp only [eq_intCast] at hwpos ⊢
    have : (0 : ℤ) < (M.transpose * M).det := by exact_mod_cast hwpos
    exact_mod_cast this
  have hk : (0 : ℝ) < (Module.finrank ℤ N : ℝ) := by
    haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
    exact_mod_cast Module.finrank_pos
  set g := (Matrix.gram ℝ (fun j => (f j : E))).det with hg
  have hgK : 1 ≤ (K : ℝ) ^ (2 * Module.finrank ℤ N) * g := hd1.trans hdet
  have hgpos : 0 < g := by
    by_contra hneg
    push_neg at hneg
    have : (K : ℝ) ^ (2 * Module.finrank ℤ N) * g ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hlog : -(2 * (Module.finrank ℤ N : ℝ)) * Real.log K ≤ Real.log g := by
    have h1 : Real.log 1 ≤ Real.log ((K : ℝ) ^ (2 * Module.finrank ℤ N) * g) :=
      Real.log_le_log one_pos hgK
    rw [Real.log_one, Real.log_mul (by positivity) hgpos.ne', Real.log_pow] at h1
    push_cast at h1
    linarith
  have hcov : covol N = Real.sqrt g := by rw [covol, dif_pos hN]
  show -Real.log (covol N) / (Module.finrank ℤ N : ℝ) ≤ Real.log K
  rw [hcov, Real.log_sqrt hgpos.le, div_le_iff₀ hk]
  nlinarith

end Formalism.F
