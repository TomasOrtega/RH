import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
open TensorProduct Module

noncomputable section

namespace GlobalTheory.RegularRing

/- English proof (translation)
Distinguish the cases in `hn : IsEmpty n`. Use `⟨1, fun g => ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Conclude with `isEmptyElim i`. Rewrite `hn` using `[not_isEmpty_iff]`.

Set `WE : Submodule E (n → B)` to `{ carrier := W add_mem' := W.add_mem zero_mem' := W.zero_mem smul_mem' := by`. Introduce `c x hx`. Rewrite `hx`, the goal using `[SetLike.mem_coe, hW]`. Introduce `g`. Establish `h1 : (fun i => act g ((c • x) i)) = algebraMap E B c • fun i => act g (x i)`.

Use function extensionality and compare the values at `i`. Simplify using `[Algebra.smul_def, hE]`. Rewrite using `[h1, Matrix.mulVec_smul, hx g]`. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.smul_def] }`.

Establish `hWE : ∀ x, x ∈ WE ↔ x ∈ W` using `fun x => Iff.rfl`. Establish `hfr : finrank E ↥WE = Fintype.card n`. Establish `h1` using `Module.finrank_mul_finrank F E ↥WE`. Establish `h2 : finrank F ↥WE = finrank F ↥W` using `((Submodule.restrictScalarsEquiv F E (n → B) WE).restrictScalars F).finrank_eq.symm.trans (by congr 1)`. Rewrite `h1` using `[h2, hdim]`.

Conclude with `Nat.eq_of_mul_eq_mul_left finrank_pos h1`. Use `haveI : Module.Finite E ↥WE := Module.finite_of_finrank_pos (by rw [hfr]; exact Fintype.card_pos)`. Set `b : Basis n E ↥WE` to `(Module.finBasisOfFinrankEq E ↥WE hfr).reindex (Fintype.equivFin n).symm`. Set `v : n → (n → B)` to `fun j => (b j : n → B)`. Establish `hv : ∀ g j, ((A g).map (algebraMap F B)).mulVec (fun i => act g (v j i)) = v j` using `fun g j => (hW _).1 ((hWE _).1 (b j).2) g`.

Set `σ : G → (n → B) →+ (n → B)` to `fun g => { toFun := fun x => ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i)) map_zero' := by`. Simplify using `only [Pi.zero_apply, map_zero]`. Conclude with `Matrix.mulVec_zero _`. Use the proof step `map_add' := by`. Introduce `x y`.

Simplify using `only [Pi.add_apply, map_add]`. Conclude with `Matrix.mulVec_add _ _ _ }`. Establish `hσ : ∀ g (c : B) (w : n → B), σ g (c • w) = act g c • σ g w`. Introduce `g c w`. Express the relevant statement in the definitionally equal form `((A g).map (algebraMap F B)).mulVec (fun i => act g ((c • w) i)) = act g c • ((A g).map (algebraMap F B)).mulVec (fun i => act g (w i))`.

Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hvE : LinearIndependent E v` using `b.linearIndependent.map' WE.subtype WE.ker_subtype`.

Establish `hvB : LinearIndependent B v`. Rewrite using `[linearIndependent_iff_finset_linearIndependent]`. Introduce `s`. Conclude with `linearIndepOn_of_invariant (fun g c => act g c) σ hσ hreg v hv s (hvE.linearIndepOn _)`. Set `Q : Matrix n n B` to `Matrix.of fun i j => v j i`.

Establish `hQ : ∀ g, (A g).map (algebraMap F B) * Q.map (act g) = Q`. Introduce `g`. Use extensionality with `i j`. Use `congrFun (hv g j) i` as an intermediate fact. Rewrite using `[Matrix.mul_apply]`.

Simplify `this` using `[Q, Matrix.mulVec, dotProduct]`. Establish `hdet0 : Q.det ≠ 0`. Introduce `h0`. Take `⟨c, hc, hc0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hc` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Use `Fintype.linearIndependent_iff.1 hvB c ?_ j` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `congrFun hc0 i` as an intermediate fact. Simplify `this` using `[Q, Matrix.mulVec, dotProduct, mul_comm]`.

Establish `hdetU : IsUnit Q.det`. Use `hu _ hdet0 fun g => ?_` and prove the remaining obligations. Establish `h2` using `congrArg Matrix.det (hQ g)`. Rewrite `h2` using `[Matrix.det_mul]`. Establish `h3 : ((A g).map (algebraMap F B)).det = algebraMap F B (A g).det` using `(RingHom.map_det _ _).symm`.

Establish `h4 : (Q.map (act g)).det = act g Q.det` using `(RingHom.map_det _ _).symm`. Rewrite `h2` using `[h3, h4]`. Use `⟨(A g).det⁻¹, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← h2]`. Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ (hA g), map_one, one_mul]`.

Conclude with `⟨Matrix.GeneralLinearGroup.mk'' Q hdetU, hQ⟩`.
-/
theorem exists_periodMatrix_of_finrank (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (B : Type) [CommRing B] [IsDomain B] [Algebra F B] [Algebra E B] [IsScalarTower F E B]
    (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n F)
    (hA : ∀ g, (A g).det ≠ 0) (hE : ∀ g (c : E), act g (algebraMap E B c) = algebraMap E B c)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : E, b' = algebraMap E B c * b)
    (hu : ∀ b : B, b ≠ 0 → (∀ g, ∃ x : F, act g b = algebraMap F B x * b) → IsUnit b)
    (W : Submodule F (n → B))
    (hW : ∀ x, x ∈ W ↔ ∀ g, ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i)) = x)
    (hdim : finrank F ↥W = finrank F E * Fintype.card n) :
    ∃ Q : GL n B, ∀ g, (A g).map (algebraMap F B) * (Q : Matrix n n B).map (act g) = Q := by
  classical
  by_cases hn : IsEmpty n
  · refine ⟨1, fun g => ?_⟩
    ext i
    exact isEmptyElim i
  rw [not_isEmpty_iff] at hn
  let WE : Submodule E (n → B) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        intro c x hx
        rw [SetLike.mem_coe, hW] at hx ⊢
        intro g
        have h1 : (fun i => act g ((c • x) i)) = algebraMap E B c • fun i => act g (x i) := by
          funext i
          simp [Algebra.smul_def, hE]
        rw [h1, Matrix.mulVec_smul, hx g]
        funext i
        simp [Algebra.smul_def] }
  have hWE : ∀ x, x ∈ WE ↔ x ∈ W := fun x => Iff.rfl
  have hfr : finrank E ↥WE = Fintype.card n := by
    have h1 := Module.finrank_mul_finrank F E ↥WE
    have h2 : finrank F ↥WE = finrank F ↥W :=
      ((Submodule.restrictScalarsEquiv F E (n → B) WE).restrictScalars F).finrank_eq.symm.trans
        (by congr 1)
    rw [h2, hdim] at h1
    exact Nat.eq_of_mul_eq_mul_left finrank_pos h1
  haveI : Module.Finite E ↥WE := Module.finite_of_finrank_pos (by rw [hfr]; exact Fintype.card_pos)
  let b : Basis n E ↥WE := (Module.finBasisOfFinrankEq E ↥WE hfr).reindex (Fintype.equivFin n).symm
  let v : n → (n → B) := fun j => (b j : n → B)
  have hv : ∀ g j, ((A g).map (algebraMap F B)).mulVec (fun i => act g (v j i)) = v j :=
    fun g j => (hW _).1 ((hWE _).1 (b j).2) g
  let σ : G → (n → B) →+ (n → B) := fun g =>
    { toFun := fun x => ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i))
      map_zero' := by
        simp only [Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add]
        exact Matrix.mulVec_add _ _ _ }
  have hσ : ∀ g (c : B) (w : n → B), σ g (c • w) = act g c • σ g w := by
    intro g c w
    change ((A g).map (algebraMap F B)).mulVec (fun i => act g ((c • w) i)) =
      act g c • ((A g).map (algebraMap F B)).mulVec (fun i => act g (w i))
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp
  have hvE : LinearIndependent E v :=
    b.linearIndependent.map' WE.subtype WE.ker_subtype
  have hvB : LinearIndependent B v := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    exact linearIndepOn_of_invariant (fun g c => act g c) σ hσ hreg v hv s (hvE.linearIndepOn _)
  let Q : Matrix n n B := Matrix.of fun i j => v j i
  have hQ : ∀ g, (A g).map (algebraMap F B) * Q.map (act g) = Q := by
    intro g
    ext i j
    have := congrFun (hv g j) i
    rw [Matrix.mul_apply]
    simpa [Q, Matrix.mulVec, dotProduct] using this
  have hdet0 : Q.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc
    funext j
    refine Fintype.linearIndependent_iff.1 hvB c ?_ j
    funext i
    have := congrFun hc0 i
    simpa [Q, Matrix.mulVec, dotProduct, mul_comm] using this
  have hdetU : IsUnit Q.det := by
    refine hu _ hdet0 fun g => ?_
    have h2 := congrArg Matrix.det (hQ g)
    rw [Matrix.det_mul] at h2
    have h3 : ((A g).map (algebraMap F B)).det = algebraMap F B (A g).det := (RingHom.map_det _ _).symm
    have h4 : (Q.map (act g)).det = act g Q.det := (RingHom.map_det _ _).symm
    rw [h3, h4] at h2
    refine ⟨(A g).det⁻¹, ?_⟩
    conv_rhs => rw [← h2]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hA g), map_one, one_mul]
  exact ⟨Matrix.GeneralLinearGroup.mk'' Q hdetU, hQ⟩

end GlobalTheory.RegularRing
