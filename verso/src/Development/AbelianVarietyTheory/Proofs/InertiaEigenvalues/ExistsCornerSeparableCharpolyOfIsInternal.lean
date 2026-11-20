import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

/- English proof (translation)
Establish `hfg : ∀ w : Fin t → K, b.mulVecLin (a.mulVecLin w) = w` using `fun w => by`. Simplify using `[Matrix.mulVec_mulVec, hba]`. Establish `hE : (a * b).mulVecLin = a.mulVecLin ∘ₗ b.mulVecLin` using `Matrix.mulVecLin_mul a b`. Establish `hback : ∀ S : Submodule K (Fin n → K), S.map (a * b).mulVecLin ≤ S → (S.map b.mulVecLin).map a.mulVecLin ≤ S`. Introduce `S hS`.

Rewrite using `[← Submodule.map_comp, ← hE]` and apply the resulting hypothesis. Establish `hVj : ∀ j, (Vs j).map (a * b).mulVecLin ≤ Vs j`. Introduce and unpack `j _ ⟨v, hv, rfl⟩`. Conclude with `he j v hv`. Rewrite `hV`, the goal using `[DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]`.

Take `⟨hind, htop⟩` from `hV`. Prove the components needed by the constructor for the conclusion. Rewrite `hind`, the goal using `[iSupIndep_def]`. Introduce `j`. Rewrite using `[Submodule.disjoint_def]`.

Introduce `x hx1 hx2`. Establish `hrest : (⨆ k, ⨆ (_ : k ≠ j), Vs k).map (a * b).mulVecLin ≤ ⨆ k, ⨆ (_ : k ≠ j), Vs k`. Repeatedly rewrite using `[Submodule.map_iSup]`. Conclude with `iSup₂_mono fun k _ => hVj k`. Establish `hx2' : x ∈ (⨆ k, ⨆ (_ : k ≠ j), Vs k).map b.mulVecLin`.

Repeatedly rewrite using `[Submodule.map_iSup]`. Conclude with `hx2`. Establish `h1 : a.mulVecLin x ∈ Vs j` using `hback _ (hVj j) (Submodule.mem_map_of_mem hx1)`. Establish `h2 : a.mulVecLin x ∈ ⨆ k, ⨆ (_ : k ≠ j), Vs k` using `hback _ hrest (Submodule.mem_map_of_mem hx2')`. Rewrite using `[← hfg x, Submodule.disjoint_def.1 (hind j) _ h1 h2, map_zero]`.

Rewrite using `[← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `fun w => ⟨a.mulVecLin w, hfg w⟩`.
-/
theorem isInternal_map_of_corner {K : Type} [Field K] {n t : ℕ} (ι : Type) [Fintype ι]
    [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hV : DirectSum.IsInternal Vs) (hba : b * a = 1)
    (he : ∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) :
    DirectSum.IsInternal (fun j => (Vs j).map b.mulVecLin) := by
  classical
  have hfg : ∀ w : Fin t → K, b.mulVecLin (a.mulVecLin w) = w := fun w => by
    simp [Matrix.mulVec_mulVec, hba]
  have hE : (a * b).mulVecLin = a.mulVecLin ∘ₗ b.mulVecLin := Matrix.mulVecLin_mul a b

  have hback : ∀ S : Submodule K (Fin n → K), S.map (a * b).mulVecLin ≤ S →
      (S.map b.mulVecLin).map a.mulVecLin ≤ S := by
    intro S hS
    rwa [← Submodule.map_comp, ← hE]
  have hVj : ∀ j, (Vs j).map (a * b).mulVecLin ≤ Vs j := by
    rintro j _ ⟨v, hv, rfl⟩
    exact he j v hv
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hV ⊢
  obtain ⟨hind, htop⟩ := hV
  constructor
  · rw [iSupIndep_def] at hind ⊢
    intro j
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hrest : (⨆ k, ⨆ (_ : k ≠ j), Vs k).map (a * b).mulVecLin ≤ ⨆ k, ⨆ (_ : k ≠ j), Vs k := by
      simp_rw [Submodule.map_iSup]
      exact iSup₂_mono fun k _ => hVj k
    have hx2' : x ∈ (⨆ k, ⨆ (_ : k ≠ j), Vs k).map b.mulVecLin := by
      simp_rw [Submodule.map_iSup]
      exact hx2
    have h1 : a.mulVecLin x ∈ Vs j := hback _ (hVj j) (Submodule.mem_map_of_mem hx1)
    have h2 : a.mulVecLin x ∈ ⨆ k, ⨆ (_ : k ≠ j), Vs k :=
      hback _ hrest (Submodule.mem_map_of_mem hx2')
    rw [← hfg x, Submodule.disjoint_def.1 (hind j) _ h1 h2, map_zero]
  · rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
    exact fun w => ⟨a.mulVecLin w, hfg w⟩

/- English proof (translation)
Set `v : ∀ j, Module.Basis (Fin (Module.finrank K (W j))) K (W j)` to `fun j => Module.finBasis K (W j)`. Set `B` to `hW.collectedBasis v`. Set `μ : (Σ j, Fin (Module.finrank K (W j))) → K` to `fun s => Infinite.natEmbedding K (Fintype.equivFin _ s)`. Establish `hμ : Function.Injective μ` using `(Infinite.natEmbedding K).injective.comp (Fin.val_injective.comp (Fintype.equivFin _).injective)`. Set `φ : (Fin t → K) →ₗ[K] (Fin t → K)` to `B.constr K (fun s => μ s • B s)`.

Establish `hφB : ∀ s, φ (B s) = μ s • B s` using `fun s => B.constr_basis K _ s`. Use `⟨LinearMap.toMatrix' φ, ?_, ?_⟩` and prove the remaining obligations. Introduce `j w hw`. Establish `hD : (LinearMap.toMatrix' φ).mulVec w = φ w`. Rewrite using `[← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']`.

Establish `hw' : w = ((∑ k, (v j).repr ⟨w, hw⟩ k • v j k : W j) : Fin t → K)`. Rewrite using `[(v j).sum_repr]`. Rewrite using `[hD, hw', Submodule.coe_sum, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, map_smul]`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hk : ((v j k : W j) : Fin t → K) = B ⟨j, k⟩` using `by simp [B]`. Rewrite using `[hk, hφB]`. Conclude with `Submodule.smul_mem _ _ (hW.collectedBasis_mem v ⟨j, k⟩)`. Establish `h1 : (LinearMap.toMatrix' φ).charpoly = φ.charpoly`.

Rewrite using `[← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix]`. Establish `h2 : LinearMap.toMatrix B B φ = Matrix.diagonal μ`. Use extensionality with `s s'`. Rewrite using `[LinearMap.toMatrix_apply, hφB, map_smul, B.repr_self, Matrix.diagonal_apply]`. Distinguish the cases in `h : s = s'`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[h1, ← LinearMap.charpoly_toMatrix φ B, h2, Matrix.charpoly_diagonal]`. Conclude with `Polynomial.separable_prod_X_sub_C_iff.2 hμ`.
-/
theorem exists_separable_charpoly_of_isInternal {K : Type} [Field K] [Infinite K] {t : ℕ}
    (ι : Type) [Fintype ι] [DecidableEq ι] (W : ι → Submodule K (Fin t → K))
    (hW : DirectSum.IsInternal W) :
    ∃ D : Matrix (Fin t) (Fin t) K, (∀ j, ∀ w ∈ W j, D.mulVec w ∈ W j) ∧
      D.charpoly.Separable := by
  classical

  let v : ∀ j, Module.Basis (Fin (Module.finrank K (W j))) K (W j) := fun j => Module.finBasis K (W j)
  let B := hW.collectedBasis v
  let μ : (Σ j, Fin (Module.finrank K (W j))) → K :=
    fun s => Infinite.natEmbedding K (Fintype.equivFin _ s)
  have hμ : Function.Injective μ :=
    (Infinite.natEmbedding K).injective.comp (Fin.val_injective.comp (Fintype.equivFin _).injective)
  let φ : (Fin t → K) →ₗ[K] (Fin t → K) := B.constr K (fun s => μ s • B s)
  have hφB : ∀ s, φ (B s) = μ s • B s := fun s => B.constr_basis K _ s
  refine ⟨LinearMap.toMatrix' φ, ?_, ?_⟩
  · intro j w hw
    have hD : (LinearMap.toMatrix' φ).mulVec w = φ w := by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    have hw' : w = ((∑ k, (v j).repr ⟨w, hw⟩ k • v j k : W j) : Fin t → K) := by
      rw [(v j).sum_repr]
    rw [hD, hw', Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Submodule.coe_smul, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have hk : ((v j k : W j) : Fin t → K) = B ⟨j, k⟩ := by simp [B]
    rw [hk, hφB]
    exact Submodule.smul_mem _ _ (hW.collectedBasis_mem v ⟨j, k⟩)
  · have h1 : (LinearMap.toMatrix' φ).charpoly = φ.charpoly := by
      rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix]
    have h2 : LinearMap.toMatrix B B φ = Matrix.diagonal μ := by
      ext s s'
      rw [LinearMap.toMatrix_apply, hφB, map_smul, B.repr_self, Matrix.diagonal_apply]
      by_cases h : s = s'
      · subst h; simp
      · simp [h]
    rw [h1, ← LinearMap.charpoly_toMatrix φ B, h2, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.2 hμ

/- English proof (translation)
Introduce `K _ _ n t ι _ _ Vs a b hV hba he`. Take `⟨D, hD, hsep⟩` from `exists_separable_charpoly_of_isInternal ι _ (isInternal_map_of_corner ι Vs a b hV hba he)`. Use `⟨a * D * b, ?_, ?_⟩` and prove the remaining obligations. Introduce `j v hv`. Take `⟨u, hu, hu'⟩` from `hD j (b.mulVec v) (Submodule.mem_map_of_mem hv)`.

Establish `hm : (a * D * b).mulVec v = (a * b).mulVec u`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Use `congr 1`. Conclude with `hu'.symm`. Rewrite using `[hm]`.

Conclude with `he j u hu`. Establish `hc : b * (a * D * b) * a = D`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc]`. Conclude with `hsep`.
-/
theorem exists_corner_separable_charpoly :
    ∀ {K : Type} [Field K] [Infinite K] {n t : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), DirectSum.IsInternal Vs → b * a = 1 → (∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) → ∃ m : Matrix (Fin n) (Fin n) K, (∀ j, ∀ v ∈ Vs j, m.mulVec v ∈ Vs j) ∧ (b * m * a).charpoly.Separable := by
  intro K _ _ n t ι _ _ Vs a b hV hba he
  obtain ⟨D, hD, hsep⟩ :=
    exists_separable_charpoly_of_isInternal ι _ (isInternal_map_of_corner ι Vs a b hV hba he)
  refine ⟨a * D * b, ?_, ?_⟩
  · intro j v hv
    obtain ⟨u, hu, hu'⟩ := hD j (b.mulVec v) (Submodule.mem_map_of_mem hv)
    have hm : (a * D * b).mulVec v = (a * b).mulVec u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      congr 1
      exact hu'.symm
    rw [hm]
    exact he j u hu
  · have hc : b * (a * D * b) * a = D := by
      calc b * (a * D * b) * a = (b * a) * D * (b * a) := by simp only [Matrix.mul_assoc]
        _ = D := by rw [hba, Matrix.one_mul, Matrix.mul_one]
    rw [hc]
    exact hsep

end GlobalTheory.SpanRing
