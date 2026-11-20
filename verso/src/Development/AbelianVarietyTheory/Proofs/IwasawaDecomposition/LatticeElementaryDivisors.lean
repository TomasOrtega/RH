import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqMulDiagonal
open IsDedekindDomain NumberField

namespace GlobalTheory.LatticeMinuscule

open Matrix

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem map_mulVec_algebraMap (M : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    (M.map (algebraMap R K)).mulVec (fun i => algebraMap R K (z i))
      = fun i => algebraMap R K (M.mulVec z i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

/- English proof (translation)
Use `haveI : Submodule.IsLattice K Λ := ⟨hfg, hsp⟩`. Establish `hr : Module.finrank R Λ = n`. Rewrite using `[Submodule.IsLattice.finrank_of_pi K Λ, Fintype.card_fin]`. Set `b : Module.Basis (Fin n) R Λ` to `Module.finBasisOfFinrankEq R Λ hr`. Establish `key : ∀ z : Fin n → R, ((Pi.basisFun K (Fin n)).toMatrix (b.extendOfIsLattice K)).mulVec (fun i => algebraMap R K (z i)) = ((∑ j, z j • b j : Λ) : Fin n → K)`.

Introduce `z`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Algebra.smul_def, mul_comm]`. Use `⟨(Pi.basisFun K (Fin n)).toMatrix (b.extendOfIsLattice K), ?_, fun y => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← Module.Basis.det_apply]`.

Conclude with `Module.Basis.isUnit_det _ _`. Introduce `hy`. Use `⟨b.repr ⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[key, b.sum_repr]`. Introduce and unpack `⟨z, rfl⟩`.

Rewrite using `[key]`. Conclude with `Subtype.prop _`.
-/
theorem exists_frame [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
    (Λ : Submodule R (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ C : Matrix (Fin n) (Fin n) K, IsUnit C.det ∧
      ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i)) := by
  haveI : Submodule.IsLattice K Λ := ⟨hfg, hsp⟩
  have hr : Module.finrank R Λ = n := by
    rw [Submodule.IsLattice.finrank_of_pi K Λ, Fintype.card_fin]
  let b : Module.Basis (Fin n) R Λ := Module.finBasisOfFinrankEq R Λ hr
  have key : ∀ z : Fin n → R,
      ((Pi.basisFun K (Fin n)).toMatrix (b.extendOfIsLattice K)).mulVec
        (fun i => algebraMap R K (z i)) = ((∑ j, z j • b j : Λ) : Fin n → K) := by
    intro z
    funext i
    simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Algebra.smul_def, mul_comm]
  refine ⟨(Pi.basisFun K (Fin n)).toMatrix (b.extendOfIsLattice K), ?_, fun y => ⟨?_, ?_⟩⟩
  · rw [← Module.Basis.det_apply]; exact Module.Basis.isUnit_det _ _
  · intro hy
    refine ⟨b.repr ⟨y, hy⟩, ?_⟩
    rw [key, b.sum_repr]
  · rintro ⟨z, rfl⟩
    rw [key]
    exact Subtype.prop _

/- English proof (translation)
Establish `h : ∀ j : Fin n, ∃ z : Fin n → R, a.mulVec (C.mulVec (fun i => algebraMap R K ((Pi.single j 1 : Fin n → R) i))) = C.mulVec (fun i => algebraMap R K (z i))` using `fun j => (hC _).mp (ha _ ((hC _).mpr ⟨_, rfl⟩))`. Use `choose z hz using h`. Use `⟨Matrix.of fun i j => z j i, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h1` using `congrFun (hz j) i`.

Establish `h2 : (fun i => algebraMap R K ((Pi.single j 1 : Fin n → R) i)) = Pi.single j 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hk]`. Rewrite `h1` using `[h2, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`. Conclude with `h1`.
-/
theorem exists_mul_eq (Λ : Submodule R (Fin n → K)) (C : Matrix (Fin n) (Fin n) K)
    (hC : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i)))
    (a : Matrix (Fin n) (Fin n) K) (ha : ∀ y ∈ Λ, a.mulVec y ∈ Λ) :
    ∃ M : Matrix (Fin n) (Fin n) R, a * C = C * M.map (algebraMap R K) := by
  have h : ∀ j : Fin n, ∃ z : Fin n → R,
      a.mulVec (C.mulVec (fun i => algebraMap R K ((Pi.single j 1 : Fin n → R) i)))
        = C.mulVec (fun i => algebraMap R K (z i)) :=
    fun j => (hC _).mp (ha _ ((hC _).mpr ⟨_, rfl⟩))
  choose z hz using h
  refine ⟨Matrix.of fun i j => z j i, ?_⟩
  ext i j
  have h1 := congrFun (hz j) i
  have h2 : (fun i => algebraMap R K ((Pi.single j 1 : Fin n → R) i)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [h2, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h1
  exact h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Use `⟨P⁻¹.mulVec z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, map_mulVec_algebraMap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]`. Introduce and unpack `⟨z, rfl⟩`.

Conclude with `⟨P.mulVec z, by rw [← Matrix.mulVec_mulVec, map_mulVec_algebraMap]⟩`.
-/
theorem exists_mul_unit_iff (C : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin n) (Fin n) R)
    (hP : IsUnit P.det) (y : Fin n → K) :
    (∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i))) ↔
      ∃ z : Fin n → R,
        y = (C * P.map (algebraMap R K)).mulVec (fun i => algebraMap R K (z i)) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨P⁻¹.mulVec z, ?_⟩
    rw [← Matrix.mulVec_mulVec, map_mulVec_algebraMap, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  · rintro ⟨z, rfl⟩
    exact ⟨P.mulVec z, by rw [← Matrix.mulVec_mulVec, map_mulVec_algebraMap]⟩

open IsDedekindDomain NumberField in
open Matrix in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ} in
/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hϖ0 : algebraMap R K ϖ ≠ 0` using `(map_ne_zero_iff _ hinj).mpr hϖ.ne_zero`. Use `haveI : Module.Finite R Λ := Module.Finite.iff_fg.mpr hfg`. Use `haveI : Module.Free R Λ := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.Free.chooseBasis R Λ`.

Establish `hli : LinearIndependent K (fun i => (b i : Fin n → K))` using `(LinearIndependent.iff_fractionRing R K).mp (b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ))`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex R Λ) = n`. Establish `hspan : ⊤ ≤ Submodule.span K (Set.range fun i => (b i : Fin n → K))`. Rewrite using `[← hsp, Submodule.span_le]`. Introduce `x hx`.

Rewrite using `[← show ((⟨x, hx⟩ : Λ) : Fin n → K) = x from rfl, ← b.sum_repr ⟨x, hx⟩, Submodule.coe_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, ← algebraMap_smul K]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `h` using `Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)`.

Rewrite `h` using `[Module.finrank_fin_fun]`. Conclude with `h.symm`. Set `b'` to `b.reindex (Fintype.equivFinOfCardEq hcard)`. Set `B0 : Matrix (Fin n) (Fin n) K` to `Matrix.of fun i j => (b' j : Fin n → K) i`. Establish `key : ∀ z : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) = ((b'.equivFun.symm z : Λ) : Fin n → K)`.

Introduce `z`. Use extensionality with `i`. Simplify using `[B0, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Finset.sum_apply, Algebra.smul_def, mul_comm]`. Establish `memL : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B0 *ᵥ (fun i => algebraMap R K (z i))`. Introduce `y`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨b'.equivFun ⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[key, LinearEquiv.symm_apply_apply]`. Introduce and unpack `⟨z, rfl⟩`.

Rewrite using `[key]`. Conclude with `Subtype.prop _`. Establish `keyinj : ∀ z w : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) = B0 *ᵥ (fun i => algebraMap R K (w i)) → z = w`. Introduce `z w h`. Rewrite `h` using `[key, key]`.

Conclude with `b'.equivFun.symm.injective (Subtype.coe_injective h)`. Establish `hmap : ∀ (N : Matrix (Fin n) (Fin n) R) (z : Fin n → R), N.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (z i)) = fun i => algebraMap R K ((N *ᵥ z) i)`. Introduce `N z`. Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (algebraMap R K) N z i).symm`.

Establish `h1' : ∀ j, ∃ z : Fin n → R, a *ᵥ (b' j : Fin n → K) = B0 *ᵥ (fun i => algebraMap R K (z i))` using `fun j => (memL _).1 (h1 _ (b' j).2)`. Use `choose zM hzM using h1'`. Set `M : Matrix (Fin n) (Fin n) R` to `Matrix.of fun i j => zM j i`. Establish `haB : a * B0 = B0 * M.map (algebraMap R K)`. Use extensionality with `i j`.

Use `congrFun (hzM j) i` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, B0, M]`. Establish `h2' : ∀ j, ∃ z : Fin n → R, algebraMap R K ϖ • (b' j : Fin n → K) = a *ᵥ (B0 *ᵥ (fun i => algebraMap R K (z i)))`. Introduce `j`. Take `⟨x, hx, hxe⟩` from `h2 _ (b' j).2`.

Take `⟨z, rfl⟩` from `(memL x).1 hx`. Conclude with `⟨z, hxe⟩`. Use `choose zM' hzM' using h2'`. Set `M' : Matrix (Fin n) (Fin n) R` to `Matrix.of fun i j => zM' j i`. Establish `hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R)`.

Use extensionality with `i j`. Establish `h` using `hzM' j`. Rewrite `h` using `[Matrix.mulVec_mulVec, haB, ← Matrix.mulVec_mulVec, hmap]`. Establish `hl : algebraMap R K ϖ • (b' j : Fin n → K) = B0 *ᵥ (fun i => algebraMap R K ((ϖ • Pi.single j (1 : R) : Fin n → R) i))`. Rewrite using `[key, map_smul, Module.Basis.equivFun_symm_apply]`.

Simplify using `[Pi.single_apply, algebraMap_smul]`. Establish `h3` using `congrFun (keyinj _ _ (hl.symm.trans h)) i`. Rewrite using `[show (M * M') i j = (M *ᵥ zM' j) i from rfl, ← h3]`. Simplify using `[Matrix.one_apply, Pi.single_apply]`. Establish `hsurj : Function.Surjective B0.mulVec`.

Introduce `y`. Establish `hy : y ∈ Submodule.span K (Λ : Set (Fin n → K))` using `hsp ▸ Submodule.mem_top`. Establish `hle : Submodule.span K (Λ : Set (Fin n → K)) ≤ LinearMap.range (Matrix.mulVecLin B0)`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`.

Take `⟨z, rfl⟩` from `(memL x).1 hx`. Conclude with `⟨_, rfl⟩`. Take `⟨w, hw⟩` from `hle hy`. Conclude with `⟨w, hw⟩`. Establish `hB0 : B0.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det B0).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)).ne_zero`.

Establish `hdetM : Associated M.det (ϖ ^ k)`. Establish `h` using `congrArg Matrix.det haB`. Establish `hdm : (M.map (algebraMap R K)).det = algebraMap R K M.det` using `(RingHom.map_det _ _).symm`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, mul_comm, hdet, hdm, ← map_pow, ← map_mul]`. Establish `h'` using `hinj (mul_left_cancel₀ hB0 h)`.

Conclude with `⟨u⁻¹, by rw [← h', mul_assoc, Units.mul_inv, mul_one]⟩`. Take `⟨P, Q, hP, hQ, hMQ⟩` from `_root_.GlobalTheory.SmithBetween.smith_between R ϖ hϖ n k hk M M' hMM hdetM`. Establish `haa' : a' * a = 1` using `mul_eq_one_comm.mp haa`. Establish `hE : ∀ z : Fin n → R, a *ᵥ ((B0 * Q.map (algebraMap R K)) *ᵥ (fun i => algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) = B0 *ᵥ (fun i => algebraMap R K ((P *ᵥ z) i))`. Introduce `z`.

Establish `hdw : ((Matrix.diagonal fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ).map (algebraMap R K)) *ᵥ (fun i => algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i)) = fun i => algebraMap R K (z i)`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.mulVec_diagonal]`. Apply the tactic sequence `by_cases hi : i.1 < n - k <;> simp [hi, hϖ0]`.

Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.mul_assoc, haB, Matrix.mul_assoc, ← Matrix.map_mul, hMQ, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdw, hmap]`. Use `⟨B0 * Q.map (algebraMap R K), fun y => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[memL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`.

Use `⟨Q⁻¹ *ᵥ z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, hmap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hQ, Matrix.one_mulVec]`. Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨Q *ᵥ z, by rw [← Matrix.mulVec_mulVec, hmap]⟩`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨z, rfl⟩` from `(memL x).1 hx`. Use `⟨P⁻¹ *ᵥ z, ?_⟩` and prove the remaining obligations. Establish `h` using `hE (P⁻¹ *ᵥ z)`. Establish `hz : P *ᵥ (P⁻¹ *ᵥ z) = z`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]`. Rewrite `h` using `[hz]`. Rewrite using `[← h, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]`. Introduce and unpack `⟨z, rfl⟩`. Use `⟨_, (memL _).2 ⟨P *ᵥ z, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hE z, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]`.
-/
theorem _root_.GlobalTheory.LatticeMinuscule.lattice_elementary_divisors (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (Λ : Submodule R (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (a a' : Matrix (Fin n) (Fin n) K)
    (haa : a * a' = 1) (h1 : ∀ y ∈ Λ, a.mulVec y ∈ Λ)
    (h2 : ∀ y ∈ Λ, ∃ z ∈ Λ, algebraMap R K ϖ • y = a.mulVec z) (u : Rˣ)
    (hdet : a.det = algebraMap R K ϖ ^ k * algebraMap R K (u : R)) :
    ∃ B : Matrix (Fin n) (Fin n) K,
      (∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B.mulVec (fun i => algebraMap R K (z i))) ∧
      (∀ y, (∃ x ∈ Λ, y = a'.mulVec x) ↔ ∃ z : Fin n → R, y = B.mulVec (fun i =>
        algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖ0 : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  haveI : Module.Finite R Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free R Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R Λ
  have hli : LinearIndependent K (fun i => (b i : Fin n → K)) :=
    (LinearIndependent.iff_fractionRing R K).mp
      (b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ))
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R Λ) = n := by
    have hspan : ⊤ ≤ Submodule.span K (Set.range fun i => (b i : Fin n → K)) := by
      rw [← hsp, Submodule.span_le]
      intro x hx
      rw [← show ((⟨x, hx⟩ : Λ) : Fin n → K) = x from rfl, ← b.sum_repr ⟨x, hx⟩,
        Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, ← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  let b' := b.reindex (Fintype.equivFinOfCardEq hcard)
  let B0 : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (b' j : Fin n → K) i
  have key : ∀ z : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      ((b'.equivFun.symm z : Λ) : Fin n → K) := by
    intro z; ext i
    simp [B0, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Submodule.coe_sum,
      Finset.sum_apply, Algebra.smul_def, mul_comm]
  have memL : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B0 *ᵥ (fun i => algebraMap R K (z i)) := by
    intro y; constructor
    · intro hy; refine ⟨b'.equivFun ⟨y, hy⟩, ?_⟩; rw [key, LinearEquiv.symm_apply_apply]
    · rintro ⟨z, rfl⟩; rw [key]; exact Subtype.prop _
  have keyinj : ∀ z w : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      B0 *ᵥ (fun i => algebraMap R K (w i)) → z = w := by
    intro z w h; rw [key, key] at h; exact b'.equivFun.symm.injective (Subtype.coe_injective h)
  have hmap : ∀ (N : Matrix (Fin n) (Fin n) R) (z : Fin n → R),
      N.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (z i)) =
        fun i => algebraMap R K ((N *ᵥ z) i) := by
    intro N z; funext i; exact (RingHom.map_mulVec (algebraMap R K) N z i).symm
  have h1' : ∀ j, ∃ z : Fin n → R,
      a *ᵥ (b' j : Fin n → K) = B0 *ᵥ (fun i => algebraMap R K (z i)) :=
    fun j => (memL _).1 (h1 _ (b' j).2)
  choose zM hzM using h1'
  let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM j i
  have haB : a * B0 = B0 * M.map (algebraMap R K) := by
    ext i j
    have := congrFun (hzM j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, B0, M] using this
  have h2' : ∀ j, ∃ z : Fin n → R, algebraMap R K ϖ • (b' j : Fin n → K) =
      a *ᵥ (B0 *ᵥ (fun i => algebraMap R K (z i))) := by
    intro j
    obtain ⟨x, hx, hxe⟩ := h2 _ (b' j).2
    obtain ⟨z, rfl⟩ := (memL x).1 hx
    exact ⟨z, hxe⟩
  choose zM' hzM' using h2'
  let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM' j i
  have hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    have h := hzM' j
    rw [Matrix.mulVec_mulVec, haB, ← Matrix.mulVec_mulVec, hmap] at h
    have hl : algebraMap R K ϖ • (b' j : Fin n → K) =
        B0 *ᵥ (fun i => algebraMap R K ((ϖ • Pi.single j (1 : R) : Fin n → R) i)) := by
      rw [key, map_smul, Module.Basis.equivFun_symm_apply]
      simp [Pi.single_apply, algebraMap_smul]
    have h3 := congrFun (keyinj _ _ (hl.symm.trans h)) i
    rw [show (M * M') i j = (M *ᵥ zM' j) i from rfl, ← h3]
    simp [Matrix.one_apply, Pi.single_apply]
  have hsurj : Function.Surjective B0.mulVec := by
    intro y
    have hy : y ∈ Submodule.span K (Λ : Set (Fin n → K)) := hsp ▸ Submodule.mem_top
    have hle : Submodule.span K (Λ : Set (Fin n → K)) ≤ LinearMap.range (Matrix.mulVecLin B0) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hle hy
    exact ⟨w, hw⟩
  have hB0 : B0.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B0).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)).ne_zero
  have hdetM : Associated M.det (ϖ ^ k) := by
    have h := congrArg Matrix.det haB
    have hdm : (M.map (algebraMap R K)).det = algebraMap R K M.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, hdet, hdm, ← map_pow, ← map_mul] at h
    have h' := hinj (mul_left_cancel₀ hB0 h)
    exact ⟨u⁻¹, by rw [← h', mul_assoc, Units.mul_inv, mul_one]⟩
  obtain ⟨P, Q, hP, hQ, hMQ⟩ :=
    _root_.GlobalTheory.SmithBetween.smith_between R ϖ hϖ n k hk M M' hMM hdetM
  have haa' : a' * a = 1 := mul_eq_one_comm.mp haa
  have hE : ∀ z : Fin n → R, a *ᵥ ((B0 * Q.map (algebraMap R K)) *ᵥ (fun i =>
      algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) =
        B0 *ᵥ (fun i => algebraMap R K ((P *ᵥ z) i)) := by
    intro z
    have hdw : ((Matrix.diagonal fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ).map
        (algebraMap R K)) *ᵥ (fun i =>
          algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i)) =
        fun i => algebraMap R K (z i) := by
      rw [Matrix.diagonal_map (map_zero _)]
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hi : i.1 < n - k <;> simp [hi, hϖ0]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, haB, Matrix.mul_assoc, ← Matrix.map_mul, hMQ,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdw, hmap]
  refine ⟨B0 * Q.map (algebraMap R K), fun y => ?_, fun y => ?_⟩
  · rw [memL]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Q⁻¹ *ᵥ z, ?_⟩
      rw [← Matrix.mulVec_mulVec, hmap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hQ,
        Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      exact ⟨Q *ᵥ z, by rw [← Matrix.mulVec_mulVec, hmap]⟩
  · constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      refine ⟨P⁻¹ *ᵥ z, ?_⟩
      have h := hE (P⁻¹ *ᵥ z)
      have hz : P *ᵥ (P⁻¹ *ᵥ z) = z := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
      rw [hz] at h
      rw [← h, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      refine ⟨_, (memL _).2 ⟨P *ᵥ z, rfl⟩, ?_⟩
      rw [← hE z, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]

end GlobalTheory.LatticeMinuscule
