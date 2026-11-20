import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDSingleLeviEmbEqZero

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.LieTensor

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in

/- English proof (translation)
Use `⟨fun t => (Matrix.isUnit_exp (t • Z)).unit, Units.ext (by simp), ?_, fun hZ t => ?_⟩` and prove the remaining obligations. Use `open scoped Matrix.Norms.Operator in`. Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)`. Rewrite `h` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Conclude with `h`.

Rewrite using `[IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hZ, star_trivial, smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel, NormedSpace.exp_zero]`.
-/
theorem exists_curve {a : ℕ} (Z : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).val) (toL Z) 0 ∧
      (Z.conjTranspose = -Z → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  refine ⟨fun t => (Matrix.isUnit_exp (t • Z)).unit, Units.ext (by simp), ?_, fun hZ t => ?_⟩
  · open scoped Matrix.Norms.Operator in
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  · rw [IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hZ, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

/- English proof (translation)
Take `⟨c, h0, hc, hu⟩` from `exists_curve S`. Use `set W := Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)`. Establish `hf : FiniteDimensional ℂ W` using `hψ`. Set `W' : Submodule ℂ (GA E N → ℂ)` to `W.map (Sm E N).subtype`. Establish `hcl : IsClosed (W' : Set (GA E N → ℂ))` using `W'.closed_of_finiteDimensional`.

Set `F : ℝ → GA E N → ℂ` to `fun t g => ψ.1 (g * infGL E N (c t))`. Establish `hF : ∀ t, F t ∈ W'` using `fun t => ⟨cptRep E N ⟨(c t).val, hu hS t⟩ ψ, Submodule.subset_span ⟨_, rfl⟩, funext fun g => by`. Establish `: Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E N) = c t` using `Units.ext rfl`. Express the relevant statement in the definitionally equal form `ψ.1 (g * infGL E N (Unitary.toUnits _)) = _`. Rewrite using `[this]⟩`.

Establish `hd : Filter.Tendsto (slope F 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD (toL S) ψ.1))` using `tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve ψ g c (toL S) h0 hc)`. Establish `hm : lieD (toL S) ψ.1 ∈ W'` using `hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t => W'.smul_of_tower_mem _ (W'.sub_mem (hF t) (hF 0)))`. Take `⟨w, hw, e⟩` from `hm`. Rewrite using `[show lie E N (toL S) ψ = w from Subtype.ext e.symm]` and apply the resulting hypothesis.
-/
theorem lie_skew_mem_span {N : ℕ} (ψ : Sm E N)
    (hψ : ψ ∈ finVec (cptRep E N)) (S : Matrix (Fin N) (Fin N) (Cinf E)) (hS : S.conjTranspose = -S) :
    lie E N (toL S) ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k ψ) := by
  obtain ⟨c, h0, hc, hu⟩ := exists_curve S
  set W := Submodule.span ℂ (Set.range fun k => cptRep E N k ψ)
  have hf : FiniteDimensional ℂ W := hψ
  let W' : Submodule ℂ (GA E N → ℂ) := W.map (Sm E N).subtype
  have hcl : IsClosed (W' : Set (GA E N → ℂ)) := W'.closed_of_finiteDimensional
  let F : ℝ → GA E N → ℂ := fun t g => ψ.1 (g * infGL E N (c t))
  have hF : ∀ t, F t ∈ W' := fun t =>
    ⟨cptRep E N ⟨(c t).val, hu hS t⟩ ψ, Submodule.subset_span ⟨_, rfl⟩, funext fun g => by
      have : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E N) = c t := Units.ext rfl
      change ψ.1 (g * infGL E N (Unitary.toUnits _)) = _
      rw [this]⟩
  have hd : Filter.Tendsto (slope F 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD (toL S) ψ.1)) :=
    tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve ψ g c (toL S) h0 hc)
  have hm : lieD (toL S) ψ.1 ∈ W' := hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t =>
    W'.smul_of_tower_mem _ (W'.sub_mem (hF t) (hF 0)))
  obtain ⟨w, hw, e⟩ := hm
  rwa [show lie E N (toL S) ψ = w from Subtype.ext e.symm]

/- English proof (translation)
Use extensionality with `a b`. Take `⟨⟨i, a⟩, rfl⟩` from `e.surjective a`. Take `⟨⟨j, b⟩, rfl⟩` from `e.surjective b`. Express the relevant statement in the definitionally equal form `p ((leviEmb R e x).val _ _) = _`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Rewrite using `[leviEmb_apply_same, leviEmb_apply_same]`. Both sides reduce to the same expression. Rewrite using `[leviEmb_apply_ne _ _ _ h, leviEmb_apply_ne _ _ _ h, map_zero]`.
-/
theorem map_leviEmb {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {c N : ℕ} {n : Fin c → ℕ}
    (e : (Σ i, Fin (n i)) ≃ Fin N) (x : ∀ i, GL (Fin (n i)) R) :
    Matrix.GeneralLinearGroup.map p (leviEmb R e x) = leviEmb S e fun i => Matrix.GeneralLinearGroup.map p (x i) := by
  ext a b
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨j, b⟩, rfl⟩ := e.surjective b
  change p ((leviEmb R e x).val _ _) = _
  by_cases h : i = j
  · subst h
    rw [leviEmb_apply_same, leviEmb_apply_same]
    rfl
  · rw [leviEmb_apply_ne _ _ _ h, leviEmb_apply_ne _ _ _ h, map_zero]

/- English proof (translation)
Use `ga_ext ?_ ?_` and prove the remaining obligations. Simplify using `only [map_leviEmb, pInf_infGL]`. Simplify using `only [map_leviEmb, pFin_infGL]`. Conclude with `(map_one (leviEmb (Af E) e)).symm`.
-/
theorem infGL_leviEmb {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (x : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) e x) = leviEmb (Ad E) e fun i => infGL E (n i) (x i) := by
  refine ga_ext ?_ ?_
  · simp only [map_leviEmb, pInf_infGL]
  · simp only [map_leviEmb, pFin_infGL]
    exact (map_one (leviEmb (Af E) e)).symm

/- English proof (translation)
Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F hF`. Take `⟨φ, rfl⟩` from `hF`. Use `⟨∑ i, fun m => ∏ j, (Function.update φ i ⟨_, (π i).stable (.lie (Z i)) _ (φ i).2⟩ j).1.1 (m j), Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩, fun m => ?_⟩` and prove the remaining obligations. Establish `h` using `HasDerivAt.fun_finsetProd (u := Finset.univ) fun i _ => hasDerivAt_curve (φ i).1 (m i) (γ i) (Z i) (h0 i) (hγ i)`.

Use `h.congr_deriv (Eq.symm ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self, smul_eq_mul]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hj), h0, map_one, mul_one]`. Consider the case `zero => exact ⟨0, zero_mem _, fun m => hasDerivAt_const _ _⟩`. Consider the case `add F F' _ _ hF hF'`. Take `⟨G, hG, h⟩` from `hF`.

Take `⟨G', hG', h'⟩` from `hF'`. Conclude with `⟨G + G', add_mem hG hG', fun m => (h m).add (h' m)⟩`. Consider the case `smul z F _ hF`. Take `⟨G, hG, h⟩` from `hF`. Conclude with `⟨z • G, Submodule.smul_mem _ z hG, fun m => (h m).const_mul z⟩`.
-/
theorem exists_deriv_tensorForms {c : ℕ} {n : Fin c → ℕ} (π : ∀ i, CuspSub E (n i))
    (γ : ∀ i, ℝ → GL (Fin (n i)) (Cinf E)) (Z : ∀ i, Lie E (n i)) (h0 : ∀ i, γ i 0 = 1)
    (hγ : ∀ i, HasDerivAt (fun t => toL (γ i t).val) (Z i) 0) {F : (∀ i, GA E (n i)) → ℂ} (hF : F ∈ tensorForms π) :
    ∃ G ∈ tensorForms π, ∀ m, HasDerivAt (fun t => F fun i => m i * infGL E (n i) (γ i t)) (G m) 0 := by
  classical
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ, rfl⟩ := hF
    refine ⟨∑ i, fun m => ∏ j, (Function.update φ i ⟨_, (π i).stable (.lie (Z i)) _ (φ i).2⟩ j).1.1 (m j),
      Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩, fun m => ?_⟩
    have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
      fun i _ => hasDerivAt_curve (φ i).1 (m i) (γ i) (Z i) (h0 i) (hγ i)
    refine h.congr_deriv (Eq.symm ?_)
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), h0, map_one, mul_one]
  | zero => exact ⟨0, zero_mem _, fun m => hasDerivAt_const _ _⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨G, hG, h⟩ := hF
    obtain ⟨G', hG', h'⟩ := hF'
    exact ⟨G + G', add_mem hG hG', fun m => (h m).add (h' m)⟩
  | smul z F _ hF =>
    obtain ⟨G, hG, h⟩ := hF
    exact ⟨z • G, Submodule.smul_mem _ z hG, fun m => (h m).const_mul z⟩

/- English proof (translation)
Use `choose γ h0 hγ _ using fun i => exists_curve (Z i)`. Take `⟨G, hG, h⟩` from `exists_deriv_tensorForms π γ (fun i => toL (Z i)) h0 hγ hψ`. Establish `hc : HasDerivAt (fun t => toL (leviEmb (Cinf E) e fun i => γ i t).val) (toL (Matrix.reindex e e (Matrix.blockDiagonal' Z))) 0`. Use `hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_` and prove the remaining obligations. Take `⟨⟨i, a⟩, rfl⟩` from `e.surjective a`.

Take `⟨⟨j, b⟩, rfl⟩` from `e.surjective b`. Express the relevant statement in the definitionally equal form `HasDerivAt (fun t => (leviEmb (Cinf E) e fun i => γ i t).val (e ⟨i, a⟩) (e ⟨j, b⟩)) (Matrix.reindex e e (Matrix.blockDiagonal' Z) (e ⟨i, a⟩) (e ⟨j, b⟩)) 0`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [leviEmb_apply_same, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_eq]`.

Conclude with `hasDerivAt_pi.1 (hasDerivAt_pi.1 (hγ i) a) b`. Simplify using `only [leviEmb_apply_ne _ _ _ hij, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hij]`. Conclude with `hasDerivAt_const _ _`. Use `hG using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`.

Establish `h1` using `hasDerivAt_curve ψ (leviEmb (Ad E) e m) (fun t => leviEmb (Cinf E) e fun i => γ i t) _ (by simp only [h0]; exact map_one _) hc`. Use `h1.unique ?_` and prove the remaining obligations. Simplify using `only [infGL_leviEmb, ← map_mul]`. Conclude with `h m`.
-/
theorem lie_block_tensor {c N : ℕ} (n : Fin c → ℕ)
    (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i)) (ψ : Sm E N)
    (hψ : (fun m => ψ.1 (leviEmb (Ad E) e m)) ∈ tensorForms π)
    (Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E)) :
    (fun m => (lie E N (toL (Matrix.reindex e e (Matrix.blockDiagonal' Z))) ψ).1 (leviEmb (Ad E) e m))
      ∈ tensorForms π := by
  choose γ h0 hγ _ using fun i => exists_curve (Z i)
  obtain ⟨G, hG, h⟩ := exists_deriv_tensorForms π γ (fun i => toL (Z i)) h0 hγ hψ
  have hc : HasDerivAt (fun t => toL (leviEmb (Cinf E) e fun i => γ i t).val)
      (toL (Matrix.reindex e e (Matrix.blockDiagonal' Z))) 0 := by
    refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
    obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ := e.surjective b
    change HasDerivAt (fun t => (leviEmb (Cinf E) e fun i => γ i t).val (e ⟨i, a⟩) (e ⟨j, b⟩))
      (Matrix.reindex e e (Matrix.blockDiagonal' Z) (e ⟨i, a⟩) (e ⟨j, b⟩)) 0
    by_cases hij : i = j
    · subst hij
      simp only [leviEmb_apply_same, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.blockDiagonal'_apply_eq]
      exact hasDerivAt_pi.1 (hasDerivAt_pi.1 (hγ i) a) b
    · simp only [leviEmb_apply_ne _ _ _ hij, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.blockDiagonal'_apply_ne _ _ _ hij]
      exact hasDerivAt_const _ _
  convert hG using 1
  funext m
  have h1 := hasDerivAt_curve ψ (leviEmb (Ad E) e m) (fun t => leviEmb (Cinf E) e fun i => γ i t) _
    (by simp only [h0]; exact map_one _) hc
  refine h1.unique ?_
  simp only [infGL_leviEmb, ← map_mul]
  exact h m

omit [IsTotallyComplex E] in

/- English proof (translation)
Set `L : Matrix (Fin N) (Fin N) (Cinf E)` to `Matrix.of fun p q => if blk e q < blk e p then Y p q else 0`. Set `S` to `L - L.conjTranspose`. Set `Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E)` to `fun i => Matrix.of fun a b => (Y - S) (e ⟨i, a⟩) (e ⟨i, b⟩)`. Use `⟨S, Z, Y - S - Matrix.reindex e e (Matrix.blockDiagonal' Z), ?_, ?_, by abel⟩` and prove the remaining obligations. Simplify using `only [S, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]`.

Introduce `p q hpq`. Take `⟨⟨i, a⟩, rfl⟩` from `e.surjective p`. Take `⟨⟨j, b⟩, rfl⟩` from `e.surjective q`. Simplify using `only [blk_apply, not_lt] at hpq`. Break down `hpq.lt_or_eq with h | h` into its components or cases.

Establish `hij : i ≠ j` using `h.ne'`. Simplify using `[S, L, Z, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply, hij, h, not_lt_of_gt h]`. Substitute `h` using the available equality. Simplify using `[Z, Matrix.blockDiagonal'_apply]`.
-/
theorem exists_decomp {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N)
    (Y : Matrix (Fin N) (Fin N) (Cinf E)) :
    ∃ (S : Matrix (Fin N) (Fin N) (Cinf E)) (Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E))
      (U : Matrix (Fin N) (Fin N) (Cinf E)),
      S.conjTranspose = -S ∧ (∀ p q, ¬ blk e p < blk e q → U p q = 0) ∧
      Y = S + Matrix.reindex e e (Matrix.blockDiagonal' Z) + U := by
  let L : Matrix (Fin N) (Fin N) (Cinf E) := Matrix.of fun p q => if blk e q < blk e p then Y p q else 0
  let S := L - L.conjTranspose
  let Z : ∀ i, Matrix (Fin (n i)) (Fin (n i)) (Cinf E) := fun i => Matrix.of fun a b => (Y - S) (e ⟨i, a⟩) (e ⟨i, b⟩)
  refine ⟨S, Z, Y - S - Matrix.reindex e e (Matrix.blockDiagonal' Z), ?_, ?_, by abel⟩
  · simp only [S, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]
  · intro p q hpq
    obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨j, b⟩, rfl⟩ := e.surjective q
    simp only [blk_apply, not_lt] at hpq
    rcases hpq.lt_or_eq with h | h
    · have hij : i ≠ j := h.ne'
      simp [S, L, Z, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply, hij, h, not_lt_of_gt h]
    · subst h
      simp [Z, Matrix.blockDiagonal'_apply]

def LeviTensor {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i)) (ψ : Sm E N)
    (A : Matrix (Fin N) (Fin N) (Cinf E)) : Prop :=
  (fun m => (lie E N (toL A) ψ).1 (leviEmb (Ad E) e m)) ∈ tensorForms π

/- English proof (translation)
Establish `: (fun m => (lie E N (toL (0 : Matrix (Fin N) (Fin N) (Cinf E))) ψ).1 (leviEmb (Ad E) e m)) = 0`. Use function extensionality and compare the values at `m`. Rewrite using `[show toL (0 : Matrix (Fin N) (Fin N) (Cinf E)) = 0 from rfl, map_zero]`. Both sides reduce to the same expression. Unfold `LeviTensor`.

Rewrite using `[this]`. Conclude with `zero_mem _`.
-/
theorem leviTensor_zero {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i))
    (ψ : Sm E N) : LeviTensor e π ψ 0 := by
  have : (fun m => (lie E N (toL (0 : Matrix (Fin N) (Fin N) (Cinf E))) ψ).1 (leviEmb (Ad E) e m)) = 0 := by
    funext m
    rw [show toL (0 : Matrix (Fin N) (Fin N) (Cinf E)) = 0 from rfl, map_zero]
    rfl
  unfold LeviTensor
  rw [this]
  exact zero_mem _

/- English proof (translation)
Establish `: (fun m => (lie E N (toL (A + B)) ψ).1 (leviEmb (Ad E) e m)) = (fun m => (lie E N (toL A) ψ).1 (leviEmb (Ad E) e m)) + (fun m => (lie E N (toL B) ψ).1 (leviEmb (Ad E) e m))`. Use function extensionality and compare the values at `m`. Rewrite using `[show toL (A + B) = toL A + toL B from rfl, map_add]`. Both sides reduce to the same expression. Unfold `LeviTensor`.

Rewrite using `[this]`. Conclude with `add_mem hA hB`.
-/
theorem leviTensor_add {c N : ℕ} {n : Fin c → ℕ} {e : (Σ i, Fin (n i)) ≃ Fin N} {π : ∀ i, CuspSub E (n i)}
    {ψ : Sm E N} {A B : Matrix (Fin N) (Fin N) (Cinf E)} (hA : LeviTensor e π ψ A) (hB : LeviTensor e π ψ B) :
    LeviTensor e π ψ (A + B) := by
  have : (fun m => (lie E N (toL (A + B)) ψ).1 (leviEmb (Ad E) e m)) =
      (fun m => (lie E N (toL A) ψ).1 (leviEmb (Ad E) e m)) + (fun m => (lie E N (toL B) ψ).1 (leviEmb (Ad E) e m)) := by
    funext m
    rw [show toL (A + B) = toL A + toL B from rfl, map_add]
    rfl
  unfold LeviTensor
  rw [this]
  exact add_mem hA hB

/- English proof (translation)
The claim follows from `Finset.sum_induction A (LeviTensor e π ψ) (fun _ _ => leviTensor_add) (leviTensor_zero e π ψ) h`.
-/
theorem leviTensor_sum {c N : ℕ} {n : Fin c → ℕ} {e : (Σ i, Fin (n i)) ≃ Fin N} {π : ∀ i, CuspSub E (n i)}
    {ψ : Sm E N} {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin N) (Fin N) (Cinf E))
    (h : ∀ i ∈ s, LeviTensor e π ψ (A i)) : LeviTensor e π ψ (∑ i ∈ s, A i) :=
  Finset.sum_induction A (LeviTensor e π ψ) (fun _ _ => leviTensor_add) (leviTensor_zero e π ψ) h

/- English proof (translation)
Take `⟨S, Z, U, hS, hU, rfl⟩` from `exists_decomp e Y`. Use `leviTensor_add (leviTensor_add ?_ ?_) ?_` and prove the remaining obligations. Conclude with `h2 _ (lie_skew_mem_span ψ h3 S hS)`. Conclude with `lie_block_tensor n e π ψ (h2 ψ (Submodule.subset_span ⟨1, by simp⟩)) Z`. Rewrite using `[Matrix.matrix_eq_sum_single U]`.

Use `leviTensor_sum _ _ fun p _ => leviTensor_sum _ _ fun q _ => ?_` and prove the remaining obligations. Distinguish the cases in `hpq : blk e p < blk e q`. Establish `: (fun m => (lie E N (toL (Matrix.single p q (U p q))) ψ).1 (leviEmb (Ad E) e m)) = 0`. Use function extensionality and compare the values at `fun m => GlobalTheory.UnipZero.lieD_single_leviEmb_eq_zero E n e ψ h1 p q hpq (U p q) m`. Unfold `LeviTensor`.

Rewrite using `[this]`. Conclude with `zero_mem _`. Rewrite using `[hU p q hpq, Matrix.single_zero]`. Conclude with `leviTensor_zero e π ψ`.
-/
theorem leviTensor_all {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N) (π : ∀ i, CuspSub E (n i))
    (ψ : Sm E N) (h1 : ∀ u ∈ unipRad (Ad E) e, ∀ g, ψ.1 (u * g) = ψ.1 g)
    (h2 : ∀ w ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k ψ),
      (fun m => w.1 (leviEmb (Ad E) e m)) ∈ tensorForms π)
    (h3 : ψ ∈ finVec (cptRep E N)) (Y : Matrix (Fin N) (Fin N) (Cinf E)) : LeviTensor e π ψ Y := by
  obtain ⟨S, Z, U, hS, hU, rfl⟩ := exists_decomp e Y
  refine leviTensor_add (leviTensor_add ?_ ?_) ?_
  · exact h2 _ (lie_skew_mem_span ψ h3 S hS)
  · exact lie_block_tensor n e π ψ (h2 ψ (Submodule.subset_span ⟨1, by simp⟩)) Z
  · rw [Matrix.matrix_eq_sum_single U]
    refine leviTensor_sum _ _ fun p _ => leviTensor_sum _ _ fun q _ => ?_
    by_cases hpq : blk e p < blk e q
    · have : (fun m => (lie E N (toL (Matrix.single p q (U p q))) ψ).1 (leviEmb (Ad E) e m)) = 0 :=
        funext fun m => GlobalTheory.UnipZero.lieD_single_leviEmb_eq_zero E n e ψ h1 p q hpq (U p q) m
      unfold LeviTensor
      rw [this]
      exact zero_mem _
    · rw [hU p q hpq, Matrix.single_zero]
      exact leviTensor_zero e π ψ

/- English proof (translation)
Introduce `E _ _ _ c N n h π X φ hφ k g`. Establish `hφ'` using `fin_mem_indForms hφ g`. Use `set ψ' : Sm E N := act (.fin g) φ with hψ'`. Use `set y := Unitary.toUnits k with hy`. Use `set ψ : Sm E N := rt E N (infGL E N y) ψ' with hψ`.

Establish `key : ∀ x, (lie E N X φ).1 (x * (infGL E N y * finGL E N g)) = (lie E N (toL (y.val * Matrix.of X * (y⁻¹).val)) ψ).1 x`. Introduce `x`. Establish `h1` using `congrArg (fun f : Module.End ℂ (Sm E N) => (f ψ').1 x) (GlobalTheory.CapAdInv.rt_lie (E := E) y (Matrix.of X))`. Establish `h2` using `congrArg (fun f : Module.End ℂ (Sm E N) => (f φ).1 (x * infGL E N y)) (lie_rt_fin (E := E) X g)`. Simplify using `only [Module.End.mul_apply, rt_apply] at h1 h2`.

Rewrite using `[← mul_assoc, ← h2]`. Conclude with `h1`. Establish `hfun : (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N y * finGL E N g))) = fun m => (lie E N (toL (y.val * Matrix.of X * (y⁻¹).val)) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m)`. Use function extensionality and compare the values at `fun m => key _`. Rewrite using `[hfun]`.

Establish `hψv : ∀ x, ψ.1 x = φ.1 (x * (infGL E N y * finGL E N g))` using `fun x => by`. Rewrite using `[← mul_assoc]`. Both sides reduce to the same expression. Use `leviTensor_all (stdBlocks n h) π ψ (fun u hu x => ?_) (fun w hw => ?_) ?_ _` and prove the remaining obligations. Rewrite using `[hψv, hψv, mul_assoc, hφ.1 u hu]`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨k', rfl⟩` from `hw`. Use `hφ.2.2.2 (k' * k) g` as an intermediate fact. Use `this using 2 with m` and compare the differences between its conclusion and the goal.

Express the relevant statement in the definitionally equal form `ψ.1 (_ * infGL E N (Unitary.toUnits k')) = _`. Rewrite using `[hψv, map_mul, map_mul, mul_assoc, mul_assoc]`. Consider the case `zero => exact zero_mem _`. Consider the case `add w w' _ _ hw hw' => exact add_mem hw hw'`. Consider the case `smul z w _ hw => exact Submodule.smul_mem _ z hw`.

Establish `hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ'))` using `hφ'.2.2.1`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E N k ψ')) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k', rfl⟩`. Use `Submodule.subset_span ⟨k' * k, ?_⟩` and prove the remaining obligations. Use `show cptRep E N (k' * k) ψ' = cptRep E N k' ψ`.

Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem lie_tensorForms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N) (φ : Sm E N), φ ∈ indForms h π →
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g)))
        ∈ tensorForms π := by
  intro E _ _ _ c N n h π X φ hφ k g
  have hφ' := fin_mem_indForms hφ g
  set ψ' : Sm E N := act (.fin g) φ with hψ'
  set y := Unitary.toUnits k with hy
  set ψ : Sm E N := rt E N (infGL E N y) ψ' with hψ
  have key : ∀ x, (lie E N X φ).1 (x * (infGL E N y * finGL E N g)) =
      (lie E N (toL (y.val * Matrix.of X * (y⁻¹).val)) ψ).1 x := by
    intro x
    have h1 := congrArg (fun f : Module.End ℂ (Sm E N) => (f ψ').1 x) (GlobalTheory.CapAdInv.rt_lie (E := E) y (Matrix.of X))
    have h2 := congrArg (fun f : Module.End ℂ (Sm E N) => (f φ).1 (x * infGL E N y)) (lie_rt_fin (E := E) X g)
    simp only [Module.End.mul_apply, rt_apply] at h1 h2
    rw [← mul_assoc, ← h2]
    exact h1
  have hfun : (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N y * finGL E N g))) =
      fun m => (lie E N (toL (y.val * Matrix.of X * (y⁻¹).val)) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) :=
    funext fun m => key _
  rw [hfun]
  have hψv : ∀ x, ψ.1 x = φ.1 (x * (infGL E N y * finGL E N g)) := fun x => by
    rw [← mul_assoc]; rfl
  refine leviTensor_all (stdBlocks n h) π ψ (fun u hu x => ?_) (fun w hw => ?_) ?_ _
  · rw [hψv, hψv, mul_assoc, hφ.1 u hu]
  · induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k', rfl⟩ := hw
      have := hφ.2.2.2 (k' * k) g
      convert this using 2 with m
      change ψ.1 (_ * infGL E N (Unitary.toUnits k')) = _
      rw [hψv, map_mul, map_mul, mul_assoc, mul_assoc]
    | zero => exact zero_mem _
    | add w w' _ _ hw hw' => exact add_mem hw hw'
    | smul z w _ hw => exact Submodule.smul_mem _ z hw
  · have hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k ψ')) := hφ'.2.2.1
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E N k ψ'))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k', rfl⟩
    refine Submodule.subset_span ⟨k' * k, ?_⟩
    show cptRep E N (k' * k) ψ' = cptRep E N k' ψ
    rw [map_mul]
    rfl

end GlobalTheory.LieTensor
