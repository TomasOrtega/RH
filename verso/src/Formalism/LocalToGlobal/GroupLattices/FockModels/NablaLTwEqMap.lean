import Formalism.LocalToGlobal.GroupLattices.FockModels.MkP

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

def BC {R R' X X' : Type*} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [AddCommGroup X']
    [Module R' X'] (μ : X → X') (A : Submodule R X) (A' : Submodule R' X') : Prop :=
  A' = Submodule.span R' (μ '' (A : Set X))

/- English proof (translation)
Rewrite using `[h]`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`.
-/
theorem BC.mem {R R' X X' : Type*} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [AddCommGroup X']
    [Module R' X'] {μ : X → X'} {A : Submodule R X} {A' : Submodule R' X'} (h : BC μ A A') {x : X} (hx : x ∈ A) :
    μ x ∈ A' := by
  rw [h]; exact Submodule.subset_span ⟨x, hx, rfl⟩

/- English proof (translation)
Unfold `BC`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Establish `h : Submodule.span R S ≤ (Submodule.span R' (μ '' S)).comap μ`. Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`. Conclude with `h hx`.
-/
theorem bc_span {R R' X X' : Type*} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [AddCommGroup X']
    [Module R' X'] {φ : R →+* R'} (μ : X →ₛₗ[φ] X') (S : Set X) :
    BC μ (Submodule.span R S) (Submodule.span R' (μ '' S)) := by
  unfold BC
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h : Submodule.span R S ≤ (Submodule.span R' (μ '' S)).comap μ := by
      rw [Submodule.span_le]
      intro y hy
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    exact h hx

section Maps

variable {R K R' K' : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing R'] [CommRing K'] [Algebra R' K']
  (φ : R →+* R') (φK : K →+* K') (hφ : ∀ x : R, φK (algebraMap R K x) = algebraMap R' K' (φ x))

def muS (τ : Type) : MvPolynomial τ K →ₛₗ[φ] MvPolynomial τ K' where
  toFun := MvPolynomial.map φK
  map_add' := map_add _
  map_smul' := by
    intro c P
    rw [← algebraMap_smul K c P, ← algebraMap_smul K' (φ c), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, hφ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem muS_coe (τ : Type) : (muS φ φK hφ τ : MvPolynomial τ K → MvPolynomial τ K') = MvPolynomial.map φK := rfl

def vecS (k : ℕ) : (Fin k → K) →ₛₗ[φ] (Fin k → K') where
  toFun := fun v i => φK (v i)
  map_add' := by intro x y; funext i; simp
  map_smul' := by
    intro c x; funext i
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, hφ]

/- English proof (translation)
Rewrite using `[smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]`.
-/
theorem map_smulK {τ : Type} (c : K) (P : MvPolynomial τ K) :
    MvPolynomial.map φK (c • P) = φK c • MvPolynomial.map φK P := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

end Maps

/- English proof (translation)
Unfold `BC`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨b', hb', h2⟩` from `sSBasis R' k n ν`. Rewrite using `[← hb'.2.1, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Take `⟨-, -, K, sz, hsz, I, hshape, -, hbm⟩` from `h2 i`. Rewrite using `[hbm]`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨bideterminant R sz hsz I, ?_, ldlat_map_bidet φ sz hsz I⟩` and prove the remaining obligations. Use `bidetMem R k n K sz hsz I` as an intermediate fact.

Rewrite `this` using `[hshape]`. Conclude with `this`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `dualWeylMap R R' φ k n ν f hf`.
-/
theorem bc_dualWeyl {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (k n : ℕ)
    (ν : Fin n → ℕ) : BC (MvPolynomial.map φ) (dualWeyl R k n ν) (dualWeyl R' k n ν) := by
  unfold BC
  apply le_antisymm
  · obtain ⟨b', hb', h2⟩ := sSBasis R' k n ν
    rw [← hb'.2.1, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨-, -, K, sz, hsz, I, hshape, -, hbm⟩ := h2 i
    rw [hbm]
    apply Submodule.subset_span
    refine ⟨bideterminant R sz hsz I, ?_, ldlat_map_bidet φ sz hsz I⟩
    have := bidetMem R k n K sz hsz I
    rw [hshape] at this
    exact this
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact dualWeylMap R R' φ k n ν f hf

section Fields

variable {R K R' K' : Type} [CommRing R] [Field K] [Algebra R K] [CommRing R'] [IsDomain R'] [Field K']
  [Algebra R' K'] (φ : R →+* R') (φK : K →+* K')
  (hφ : ∀ x : R, φK (algebraMap R K x) = algebraMap R' K' (φ x))

include hφ in
/- English proof (translation)
Establish `h : (algebraMap R' K').comp φ = φK.comp (algebraMap R K)` using `RingHom.ext fun x => (hφ x).symm`. Rewrite using `[MvPolynomial.map_map, MvPolynomial.map_map, h]`.
-/
theorem map_map_alg {τ : Type} (f : MvPolynomial τ R) :
    MvPolynomial.map (algebraMap R' K') (MvPolynomial.map φ f) =
      MvPolynomial.map φK (MvPolynomial.map (algebraMap R K) f) := by
  have h : (algebraMap R' K').comp φ = φK.comp (algebraMap R K) := RingHom.ext fun x => (hφ x).symm
  rw [MvPolynomial.map_map, MvPolynomial.map_map, h]

/- English proof (translation)
The claim follows from `(RingHom.map_det φK g).symm`.
-/
theorem det_map {k : ℕ} (g : Matrix (Fin k) (Fin k) K) : (g.map φK).det = φK g.det :=
  (RingHom.map_det φK g).symm

/- English proof (translation)
Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Establish `h1 : g.map φK * (g⁻¹).map φK = (g * g⁻¹).map φK` using `(Matrix.map_mul).symm`. Rewrite using `[h1, Matrix.mul_nonsing_inv g hg]`. Conclude with `Matrix.map_one φK (map_zero _) (map_one _)`.
-/
theorem inv_map {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) : (g.map φK)⁻¹ = (g⁻¹).map φK := by
  apply Matrix.inv_eq_right_inv
  have h1 : g.map φK * (g⁻¹).map φK = (g * g⁻¹).map φK := (Matrix.map_mul).symm
  rw [h1, Matrix.mul_nonsing_inv g hg]
  exact Matrix.map_one φK (map_zero _) (map_one _)

def psiL (R K : Type) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R →ₗ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K where
  toFun := fun f => g.det ^ (-(lam (Fin.last m))) • rowAct K g⁻¹ (MvPolynomial.map (algebraMap R K) f)
  map_add' := by intro x y; rw [map_add, map_add, smul_add]
  map_smul' := by
    intro c x
    have h1 : MvPolynomial.map (algebraMap R K) (c • x) =
        algebraMap R K c • MvPolynomial.map (algebraMap R K) x := by
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
    rw [RingHom.id_apply, h1, map_smul, smul_comm, algebraMap_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psiL_apply (R K : Type) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :
    psiL R K m lam g f =
      g.det ^ (-(lam (Fin.last m))) • rowAct K g⁻¹ (MvPolynomial.map (algebraMap R K) f) := rfl

/- English proof (translation)
Use extensionality with `F`. Rewrite using `[nablaLTwMem R K m lam g hg, Submodule.mem_map, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, hfe⟩`. Use `⟨f, hf, ?_⟩` and prove the remaining obligations.

Establish `h2 : (mapAlgHom (Algebra.ofId R K)).toLinearMap f = MvPolynomial.map (algebraMap R K) f` using `rfl`. Rewrite using `[psiL_apply, ← h2, hfe, map_smul, ldlat_rowAct_inv_right rowActMul _ hg, smul_smul, ← zpow_add₀ hg.ne_zero, neg_add_cancel, zpow_zero, one_smul]`. Introduce and unpack `⟨f, hf, rfl⟩`. Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Establish `h2 : (mapAlgHom (Algebra.ofId R K)).toLinearMap f = MvPolynomial.map (algebraMap R K) f` using `rfl`.

Rewrite using `[psiL_apply, map_smul, ldlat_rowAct_inv_left rowActMul _ hg, smul_smul, ← zpow_add₀ hg.ne_zero, add_neg_cancel, zpow_zero, one_smul, h2]`.
-/
theorem nablaLTw_eq_map (R K : Type) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) :
    nablaLTw R K m lam g =
      (dualWeyl R (m + 1) (m + 1) (fun t => (lam t - lam (Fin.last m)).toNat)).map (psiL R K m lam g) := by
  ext F
  rw [nablaLTwMem R K m lam g hg, Submodule.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, hfe⟩
    refine ⟨f, hf, ?_⟩
    have h2 : (mapAlgHom (Algebra.ofId R K)).toLinearMap f = MvPolynomial.map (algebraMap R K) f := rfl
    rw [psiL_apply, ← h2, hfe, map_smul, ldlat_rowAct_inv_right rowActMul _ hg, smul_smul,
      ← zpow_add₀ hg.ne_zero, neg_add_cancel, zpow_zero, one_smul]
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f, hf, ?_⟩
    have h2 : (mapAlgHom (Algebra.ofId R K)).toLinearMap f = MvPolynomial.map (algebraMap R K) f := rfl
    rw [psiL_apply, map_smul, ldlat_rowAct_inv_left rowActMul _ hg, smul_smul,
      ← zpow_add₀ hg.ne_zero, add_neg_cancel, zpow_zero, one_smul, h2]

/- English proof (translation)
Unfold `BC at h ⊢`. Rewrite using `[h, Submodule.map_span, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp]`. Use `congr 1`. Conclude with `Set.image_congr fun a _ => (hT a).symm`.
-/
theorem bc_map {R R' X X' Y Y' : Type*} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [AddCommGroup X']
    [Module R' X'] [AddCommGroup Y] [Module R Y] [AddCommGroup Y'] [Module R' Y'] {μ₁ : X → X'} {μ₂ : Y → Y'}
    {A : Submodule R X} {A' : Submodule R' X'} (h : BC μ₁ A A') (T : X →ₗ[R] Y) (T' : X' →ₗ[R'] Y')
    (hT : ∀ a, μ₂ (T a) = T' (μ₁ a)) : BC μ₂ (A.map T) (A'.map T') := by
  unfold BC at h ⊢
  rw [h, Submodule.map_span, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp]
  congr 1
  exact Set.image_congr fun a _ => (hT a).symm

include hφ in

/- English proof (translation)
Establish `hg' : IsUnit (g.map φK).det` using `by rw [det_map]; exact hg.map φK`. Rewrite using `[nablaLTw_eq_map R K m lam g hg, nablaLTw_eq_map R' K' m lam _ hg']`. Use `bc_map (bc_dualWeyl φ (m + 1) (m + 1) _) _ _ fun f => ?_` and prove the remaining obligations. Rewrite using `[psiL_apply, psiL_apply, map_map_alg φ φK hφ, map_smulK, ldtwist_map_rowAct, map_zpow₀, det_map, inv_map φK g hg]`.
-/
theorem bc_nablaLTw (m : ℕ) (lam : Fin (m + 1) → ℤ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hg : IsUnit g.det) :
    BC (MvPolynomial.map φK) (nablaLTw R K m lam g) (nablaLTw R' K' m lam (g.map φK)) := by
  have hg' : IsUnit (g.map φK).det := by rw [det_map]; exact hg.map φK
  rw [nablaLTw_eq_map R K m lam g hg, nablaLTw_eq_map R' K' m lam _ hg']
  refine bc_map (bc_dualWeyl φ (m + 1) (m + 1) _) _ _ fun f => ?_
  rw [psiL_apply, psiL_apply, map_map_alg φ φK hφ, map_smulK, ldtwist_map_rowAct, map_zpow₀, det_map,
    inv_map φK g hg]

/- English proof (translation)
Unfold `blockEmb`. Conclude with `(MvPolynomial.map_rename φK _ F)`.
-/
theorem map_blockEmb {S : Type} {k n : ℕ} (s : S) (F : MvPolynomial (Fin k × Fin n) K) :
    MvPolynomial.map φK (blockEmb K s F) = blockEmb K' s (MvPolynomial.map φK F) := by
  unfold blockEmb
  exact (MvPolynomial.map_rename φK _ F)

include hφ in

/- English proof (translation)
Establish `h0` using `bc_span (muS φ φK hφ (S × (Fin k × Fin n))) {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ M s) ∧ P = ∏ s, blockEmb K s (F s)}`. Rewrite `h0` using `[muS_coe]`. Unfold `BC at h0 ⊢`. Unfold `tensorLat`. Rewrite using `[← h0]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F', hF', rfl⟩`. Use `set T : S → Set (MvPolynomial (S × (Fin k × Fin n)) K') := fun s => (fun F => blockEmb K' s (MvPolynomial.map φK F)) '' (M s : Set _) with hT`. Establish `h1 : ∀ s, blockEmb K' s (F' s) ∈ Submodule.span R' (T s)`.

Introduce `s`. Establish `h2 : M' s ≤ (Submodule.span R' (T s)).comap ((blockEmb K' (k` using `k) (n := n) s).toLinearMap.restrictScalars R') := by`. Rewrite using `[h s, Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Conclude with `Submodule.subset_span ⟨F, hF, rfl⟩`.

Conclude with `h2 (hF' s)`. Establish `h3` using `fn_prod_mem (R := R') Finset.univ (fun s => Submodule.span R' (T s)) (fun s => blockEmb K' s (F' s)) (fun s _ => h1 s)`. Rewrite `h3` using `[Submodule.prod_span]`. Use `Submodule.span_mono ?_ h3` and prove the remaining obligations. Introduce `P hP`.

Rewrite `hP` using `[Set.mem_finsetProd]`. Take `⟨gf, hgf, rfl⟩` from `hP`. Establish `h4 : ∀ s, ∃ F, F ∈ M s ∧ blockEmb K' s (MvPolynomial.map φK F) = gf s`. Introduce `s`. Take `⟨F, hF, hFe⟩` from `hgf (Finset.mem_univ s)`.

Conclude with `⟨F, hF, hFe⟩`. Use `choose F hF hFe using h4`. Use `⟨∏ s, blockEmb K s (F s), ⟨F, hF, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun s _ => by rw [map_blockEmb, hFe]`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨F, hF, rfl⟩, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun s => MvPolynomial.map φK (F s), fun s => (h s).mem (hF s), ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_congr rfl fun s _ => map_blockEmb φK s (F s)`.
-/
theorem bc_tensorLat {S : Type} [Fintype S] {k n : ℕ} (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (M' : S → Submodule R' (MvPolynomial (Fin k × Fin n) K'))
    (h : ∀ s, BC (MvPolynomial.map φK) (M s) (M' s)) :
    BC (MvPolynomial.map φK) (tensorLat R K M) (tensorLat R' K' M') := by
  classical
  have h0 := bc_span (muS φ φK hφ (S × (Fin k × Fin n)))
    {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ M s) ∧ P = ∏ s, blockEmb K s (F s)}
  rw [muS_coe] at h0
  unfold BC at h0 ⊢
  unfold tensorLat
  rw [← h0]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨F', hF', rfl⟩
    set T : S → Set (MvPolynomial (S × (Fin k × Fin n)) K') :=
      fun s => (fun F => blockEmb K' s (MvPolynomial.map φK F)) '' (M s : Set _) with hT
    have h1 : ∀ s, blockEmb K' s (F' s) ∈ Submodule.span R' (T s) := by
      intro s
      have h2 : M' s ≤ (Submodule.span R' (T s)).comap ((blockEmb K' (k := k) (n := n) s).toLinearMap.restrictScalars R') := by
        rw [h s, Submodule.span_le]
        rintro _ ⟨F, hF, rfl⟩
        exact Submodule.subset_span ⟨F, hF, rfl⟩
      exact h2 (hF' s)
    have h3 := fn_prod_mem (R := R') Finset.univ (fun s => Submodule.span R' (T s))
      (fun s => blockEmb K' s (F' s)) (fun s _ => h1 s)
    rw [Submodule.prod_span] at h3
    refine Submodule.span_mono ?_ h3
    intro P hP
    rw [Set.mem_finsetProd] at hP
    obtain ⟨gf, hgf, rfl⟩ := hP
    have h4 : ∀ s, ∃ F, F ∈ M s ∧ blockEmb K' s (MvPolynomial.map φK F) = gf s := by
      intro s
      obtain ⟨F, hF, hFe⟩ := hgf (Finset.mem_univ s)
      exact ⟨F, hF, hFe⟩
    choose F hF hFe using h4
    refine ⟨∏ s, blockEmb K s (F s), ⟨F, hF, rfl⟩, ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => by rw [map_blockEmb, hFe]
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun s => MvPolynomial.map φK (F s), fun s => (h s).mem (hF s), ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => map_blockEmb φK s (F s)

include hφ in

/- English proof (translation)
Establish `h0` using `bc_span (vecS φ φK hφ k) (Set.range fun c : Fin k => fun i => g i c)`. Establish `h1 : (vecS φ φK hφ k) '' (Set.range fun c : Fin k => fun i => g i c) = Set.range fun c : Fin k => fun i => (g.map φK) i c`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite `h0` using `[h1]`.

Conclude with `h0`.
-/
theorem bc_colSpan {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    BC (vecS φ φK hφ k) (colSpan R g) (colSpan R' (g.map φK)) := by
  have h0 := bc_span (vecS φ φK hφ k) (Set.range fun c : Fin k => fun i => g i c)
  have h1 : (vecS φ φK hφ k) '' (Set.range fun c : Fin k => fun i => g i c) =
      Set.range fun c : Fin k => fun i => (g.map φK) i c := by
    rw [← Set.range_comp]; rfl
  rw [h1] at h0
  exact h0

include hφ in

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hΛ`. Establish `h1 : Λ' = colSpan R' (g.map φK)` using `hb.trans (bc_colSpan φ φK hφ g).symm`. Establish `hg' : IsUnit (g.map φK).det` using `by rw [det_map]; exact hg.map φK`. Rewrite using `[h1, H0_eq_twisted_nabla (la_indep hinj) m lam hlam g hg, H0_eq_twisted_nabla (la_indep hinj') m lam hlam _ hg']`. Conclude with `bc_nablaLTw φ φK hφ m lam g hg`.
-/
theorem base_change_H0 (hinj : Function.Injective (algebraMap R K)) (hinj' : Function.Injective (algebraMap R' K'))
    (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (Λ : Submodule R (Fin (m + 1) → K)) (Λ' : Submodule R' (Fin (m + 1) → K')) (hΛ : IsLattice R Λ)
    (hb : BC (vecS φ φK hφ (m + 1)) Λ Λ') :
    BC (MvPolynomial.map φK) (H0 R m lam Λ) (H0 R' m lam Λ') := by
  obtain ⟨g, hg, rfl⟩ := hΛ
  have h1 : Λ' = colSpan R' (g.map φK) := hb.trans (bc_colSpan φ φK hφ g).symm
  have hg' : IsUnit (g.map φK).det := by rw [det_map]; exact hg.map φK
  rw [h1, H0_eq_twisted_nabla (la_indep hinj) m lam hlam g hg, H0_eq_twisted_nabla (la_indep hinj') m lam hlam _ hg']
  exact bc_nablaLTw φ φK hφ m lam g hg

end Fields

end Formalism.L2.G.Model
