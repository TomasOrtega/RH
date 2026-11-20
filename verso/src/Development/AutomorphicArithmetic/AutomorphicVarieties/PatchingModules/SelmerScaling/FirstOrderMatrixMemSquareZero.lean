import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LowerEntriesZeroOfCommutingTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.InverseWeylLiftEqPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.HomBasic
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

noncomputable section

namespace UpperTheory.V.Pa.Lift1

variable {X : Type} [CommRing X] {g n : ℕ}

private def hA : DD X g →+ X := ⟨⟨fun u => u.a, rfl⟩, fun _ _ => rfl⟩
private def hE (j : Fin g) : DD X g →+ X := ⟨⟨fun u => u.ep j, rfl⟩, fun _ _ => rfl⟩
private def hE' (j : Fin g) : DD X g →+ X := ⟨⟨fun u => u.ep' j, rfl⟩, fun _ _ => rfl⟩
private def hH : DD X g →+ X := ⟨⟨fun u => u.eta, rfl⟩, fun _ _ => rfl⟩

/- English proof (translation)
The claim follows from `map_sum hA f s`.
-/
private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum hA f s
/- English proof (translation)
The claim follows from `map_sum (hE j) f s`.
-/
private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) : (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j :=
  map_sum (hE j) f s
/- English proof (translation)
The claim follows from `map_sum (hE' j) f s`.
-/
private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) : (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j :=
  map_sum (hE' j) f s
/- English proof (translation)
The claim follows from `map_sum hH f s`.
-/
private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta :=
  map_sum hH f s

private def pi1 : DD X g →+* DD X g where
  toFun u := ⟨u.a, u.ep, 0, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private def SM (X : Type) [CommRing X] (g n : ℕ) : Subring (Matrix (Fin n) (Fin n) (DD X g)) :=
  RingHom.eqLocus (pi1 (X := X) (g := g)).mapMatrix (RingHom.id _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hM i j`. Use `congrFun (congrFun (show M.map pi1 = M from hM) i) j` as an intermediate fact. Rewrite using `[← this]`. Conclude with `⟨rfl, rfl⟩`.

Introduce `hM show M.map pi1 = M`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hM i j`. Conclude with `DD.ext rfl rfl h1.symm h2.symm`.
-/
private theorem mem_SM {M : Matrix (Fin n) (Fin n) (DD X g)} :
    M ∈ SM X g n ↔ ∀ i j, (M i j).ep' = 0 ∧ (M i j).eta = 0 := by
  constructor
  · intro hM i j
    have := congrFun (congrFun (show M.map pi1 = M from hM) i) j
    rw [← this]
    exact ⟨rfl, rfl⟩
  · intro hM
    show M.map pi1 = M
    refine Matrix.ext fun i j => ?_
    obtain ⟨h1, h2⟩ := hM i j
    exact DD.ext rfl rfl h1.symm h2.symm

private def aM : Matrix (Fin n) (Fin n) (DD X g) →+* Matrix (Fin n) (Fin n) X := (DD.aug X g).toRingHom.mapMatrix

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem aM_apply (M : Matrix (Fin n) (Fin n) (DD X g)) (i j) : aM M i j = (M i j).a := rfl

private def pM (k : Fin g) : Matrix (Fin n) (Fin n) (DD X g) →+ Matrix (Fin n) (Fin n) X := (hE' k).mapMatrix

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem pM_apply (k : Fin g) (M : Matrix (Fin n) (Fin n) (DD X g)) (i j) : pM k M i j = (M i j).ep' k := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[pM_apply, aM_apply, Matrix.mul_apply, sum_ep', Finset.sum_add_distrib]`.
-/
private theorem pM_mul (k : Fin g) (M N : Matrix (Fin n) (Fin n) (DD X g)) :
    pM k (M * N) = aM M * pM k N + pM k M * aM N := by
  ext i j
  simp [pM_apply, aM_apply, Matrix.mul_apply, sum_ep', Finset.sum_add_distrib]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[pM_apply, (mem_SM.1 hM i j).1]`.
-/
private theorem pM_SM (k : Fin g) {M : Matrix (Fin n) (Fin n) (DD X g)} (hM : M ∈ SM X g n) : pM k M = 0 := by
  ext i j
  simp [pM_apply, (mem_SM.1 hM i j).1]

/- English proof (translation)
Rewrite using `[pM_mul, pM_mul, pM_SM k hP, pM_SM k hQ]`. Simplify using the standard rewrite rules.
-/
private theorem pM_conj (k : Fin g) {P Q : Matrix (Fin n) (Fin n) (DD X g)} (hP : P ∈ SM X g n) (hQ : Q ∈ SM X g n)
    (M : Matrix (Fin n) (Fin n) (DD X g)) : pM k (P * M * Q) = aM P * pM k M * aM Q := by
  rw [pM_mul, pM_mul, pM_SM k hP, pM_SM k hQ]
  simp

private def e (j : Fin g) : DD X g := ⟨0, 0, Pi.single j 1, 0⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `mem_SM.1 hM i j`. Use `DD.ext ha ?_ h1 h2` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Use `congrArg DD.eta (he k)` as an intermediate fact. Simplify `this` using `[e, Pi.single_apply]`.
-/
private theorem zero_of {M : Matrix (Fin n) (Fin n) (DD X g)} (hM : M ∈ SM X g n) {i j : Fin n}
    (ha : aM M i j = 0) (he : ∀ k, ((e k : DD X g) • M) i j = 0) : M i j = 0 := by
  obtain ⟨h1, h2⟩ := mem_SM.1 hM i j
  refine DD.ext ha ?_ h1 h2
  funext k
  have := congrArg DD.eta (he k)
  simpa [e, Pi.single_apply] using this

private def mk1 (Z : Matrix (Fin n) (Fin n) X) (H : Fin g → Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun a b => ⟨Z a b, fun j => H j a b, 0, 0⟩

private def mk2 (Q : Fin g → Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun a b => ⟨0, 0, fun j => Q j a b, 0⟩

/- English proof (translation)
The claim follows from `mem_SM.2 fun _ _ => ⟨rfl, rfl⟩`.
-/
private theorem first_order_matrix_mem_square_zero (Z : Matrix (Fin n) (Fin n) X) (H : Fin g → Matrix (Fin n) (Fin n) X) : mk1 Z H ∈ SM X g n :=
  mem_SM.2 fun _ _ => ⟨rfl, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem constant_part_first_order_matrix (Z : Matrix (Fin n) (Fin n) X) (H : Fin g → Matrix (Fin n) (Fin n) X) : aM (mk1 Z H) = Z := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem second_order_part_of_matrix (k) (Q : Fin g → Matrix (Fin n) (Fin n) X) : pM k (mk2 Q) = Q k := rfl

/- English proof (translation)
Apply the tactic sequence `ext i j <;> simp [mk2, Matrix.mul_apply, sum_a, sum_ep, sum_ep', sum_eta]`.
-/
private theorem conjugate_second_order_matrix (P R : Matrix (Fin n) (Fin n) X) (Q : Fin g → Matrix (Fin n) (Fin n) X) :
    P.map DD.C * mk2 Q * R.map DD.C = mk2 fun k => P * Q k * R := by
  ext i j <;> simp [mk2, Matrix.mul_apply, sum_a, sum_ep, sum_ep', sum_eta]

/- English proof (translation)
Apply the tactic sequence `ext i j <;> simp [DD.epM, Matrix.mul_apply, sum_a, sum_ep, sum_ep', sum_eta]`.
-/
private theorem epM_sq (Y : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Y * DD.epM Y = 0 := by
  ext i j <;> simp [DD.epM, Matrix.mul_apply, sum_a, sum_ep, sum_ep', sum_eta]

/- English proof (translation)
The claim follows from `mem_SM.2 fun _ _ => ⟨rfl, rfl⟩`.
-/
private theorem epM_SM (Y : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Y ∈ SM X g n :=
  mem_SM.2 fun _ _ => ⟨rfl, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem aM_epM (Y : Fin g → Matrix (Fin n) (Fin n) X) : aM (DD.epM Y) = 0 := rfl

/- English proof (translation)
The claim follows from `mem_SM.2 fun _ _ => ⟨rfl, rfl⟩`.
-/
private theorem C_SM (P : Matrix (Fin n) (Fin n) X) : P.map DD.C ∈ SM X g n :=
  mem_SM.2 fun _ _ => ⟨rfl, rfl⟩

variable {A : Type} [CommRing A] [Algebra A X] {a : ℕ}

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `⟨fun hij => Submodule.sum_mem _ fun k _ => ?_, fun hij => Submodule.sum_mem _ fun k _ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)`. Conclude with `h11 _ ((hM i k).1 hk) _ ((hN k j).1 (by tauto))`.

Conclude with `h22 _ ((hM i k).2 hk) _ ((hN k j).2 (by tauto))`. Distinguish the cases in `hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)`. Conclude with `h12 _ ((hM i k).1 hk) _ ((hN k j).2 (by tauto))`. Conclude with `h21 _ ((hM i k).2 hk) _ ((hN k j).1 (by tauto))`.
-/
private theorem blk_mul {R : Type} [CommRing R] [Algebra A R] {V₁ V₂ T₁ T₂ U₁ U₂ : Submodule A R}
    (h11 : ∀ u ∈ V₁, ∀ v ∈ T₁, u * v ∈ U₁) (h22 : ∀ u ∈ V₂, ∀ v ∈ T₂, u * v ∈ U₁)
    (h12 : ∀ u ∈ V₁, ∀ v ∈ T₂, u * v ∈ U₂) (h21 : ∀ u ∈ V₂, ∀ v ∈ T₁, u * v ∈ U₂)
    {M N : Matrix (Fin n) (Fin n) R} (hM : M ∈ blkMat n a V₁ V₂) (hN : N ∈ blkMat n a T₁ T₂) :
    M * N ∈ blkMat n a U₁ U₂ := by
  intro i j
  rw [Matrix.mul_apply]
  refine ⟨fun hij => Submodule.sum_mem _ fun k _ => ?_, fun hij => Submodule.sum_mem _ fun k _ => ?_⟩
  · by_cases hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
    · exact h11 _ ((hM i k).1 hk) _ ((hN k j).1 (by tauto))
    · exact h22 _ ((hM i k).2 hk) _ ((hN k j).2 (by tauto))
  · by_cases hk : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
    · exact h12 _ ((hM i k).1 hk) _ ((hN k j).2 (by tauto))
    · exact h21 _ ((hM i k).2 hk) _ ((hN k j).1 (by tauto))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_dd {u : DD X g} {b1 b2 b3 b4 : Bool} : u ∈ ddPart A X g b1 b2 b3 b4 ↔
    (b1 = false → u.a = 0) ∧ (b2 = false → u.ep = 0) ∧ (b3 = false → u.ep' = 0) ∧ (b4 = false → u.eta = 0) := Iff.rfl

/- English proof (translation)
Apply the tactic sequence `refine blk_mul ?_ ?_ ?_ ?_ hM hN <;>`. Introduce `u hu v hv`. Simplify using `only [mem_dd, funext_iff] at hu hv ⊢`. Simplify the hypotheses and the goal together.
-/
private theorem twoSubspaceIntersection {M N : Matrix (Fin n) (Fin n) (DD X g)} (hM : M ∈ W1 n A X g a) (hN : N ∈ W2 n A X g a) :
    M * N ∈ W2 n A X g a := by
  refine blk_mul ?_ ?_ ?_ ?_ hM hN <;>
  · intro u hu v hv
    simp only [mem_dd, funext_iff] at hu hv ⊢
    simp_all

/- English proof (translation)
Apply the tactic sequence `refine blk_mul ?_ ?_ ?_ ?_ hM hN <;>`. Introduce `u hu v hv`. Simplify using `only [mem_dd, funext_iff] at hu hv ⊢`. Simplify the hypotheses and the goal together.
-/
private theorem second_order_mul_first_order_mem {M N : Matrix (Fin n) (Fin n) (DD X g)} (hM : M ∈ W2 n A X g a) (hN : N ∈ W1 n A X g a) :
    M * N ∈ W2 n A X g a := by
  refine blk_mul ?_ ?_ ?_ ?_ hM hN <;>
  · intro u hu v hv
    simp only [mem_dd, funext_iff] at hu hv ⊢
    simp_all

/- English proof (translation)
Introduce `i j`. Use `⟨fun hij => ⟨by simp, fun _ => ?_, fun _ => rfl, fun _ => rfl⟩, fun hij => ⟨fun _ => (hZ i j).2 hij, by simp, fun _ => rfl, fun _ => rfl⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Conclude with `((hH k) i j).1 hij`.
-/
private theorem first_order_matrix_mem {Z : Matrix (Fin n) (Fin n) X} {H : Fin g → Matrix (Fin n) (Fin n) X}
    (hZ : Z ∈ Ev A X n a) (hH : ∀ j, H j ∈ Od A X n a) : mk1 Z H ∈ W1 n A X g a := by
  intro i j
  refine ⟨fun hij => ⟨by simp, fun _ => ?_, fun _ => rfl, fun _ => rfl⟩,
    fun hij => ⟨fun _ => (hZ i j).2 hij, by simp, fun _ => rfl, fun _ => rfl⟩⟩
  funext k
  exact ((hH k) i j).1 hij

/- English proof (translation)
Introduce `i j`. Use `⟨fun hij => ⟨fun _ => rfl, fun _ => rfl, by simp, fun _ => rfl⟩, fun hij => ⟨fun _ => rfl, fun _ => rfl, fun _ => ?_, by simp⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Conclude with `((hQ k) i j).2 hij`.
-/
private theorem second_order_matrix_mem {Q : Fin g → Matrix (Fin n) (Fin n) X} (hQ : ∀ j, Q j ∈ Ev A X n a) : mk2 Q ∈ W2 n A X g a := by
  intro i j
  refine ⟨fun hij => ⟨fun _ => rfl, fun _ => rfl, by simp, fun _ => rfl⟩,
    fun hij => ⟨fun _ => rfl, fun _ => rfl, fun _ => ?_, by simp⟩⟩
  funext k
  exact ((hQ k) i j).2 hij

/- English proof (translation)
Introduce `i j` and use `⟨fun hij => ((hM i j).1 hij).2.2.2 rfl, fun _ => trivial⟩`.
-/
private theorem eta_Od {M : Matrix (Fin n) (Fin n) (DD X g)} (hM : M ∈ W2 n A X g a) : M.map DD.eta ∈ Od A X n a :=
  fun i j => ⟨fun hij => ((hM i j).1 hij).2.2.2 rfl, fun _ => trivial⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun _ => trivial, fun hij => congrFun (((hM i j).2 hij).2.2.1 rfl) k⟩`.
-/
private theorem pM_Ev {M : Matrix (Fin n) (Fin n) (DD X g)} (hM : M ∈ W2 n A X g a) (k) : pM k M ∈ Ev A X n a :=
  fun i j => ⟨fun _ => trivial, fun hij => congrFun (((hM i j).2 hij).2.2.1 rfl) k⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun _ => trivial, fun hij => Matrix.one_apply_ne fun e => hij (by rw [e])⟩`.
-/
private theorem one_Ev : (1 : Matrix (Fin n) (Fin n) X) ∈ Ev A X n a :=
  fun i j => ⟨fun _ => trivial, fun hij => Matrix.one_apply_ne fun e => hij (by rw [e])⟩

/- English proof (translation)
Establish `: (1 : Matrix (Fin n) (Fin n) (DD X g)) = mk1 1 0`. Apply the tactic sequence `ext i j <;> by_cases hij : i = j <;> simp [mk1, Matrix.one_apply, hij]`. Rewrite using `[this]`. Conclude with `first_order_matrix_mem one_Ev fun _ => Submodule.zero_mem _`.
-/
private theorem one_mem_first_order : (1 : Matrix (Fin n) (Fin n) (DD X g)) ∈ W1 n A X g a := by
  have : (1 : Matrix (Fin n) (Fin n) (DD X g)) = mk1 1 0 := by
    ext i j <;> by_cases hij : i = j <;> simp [mk1, Matrix.one_apply, hij]
  rw [this]
  exact first_order_matrix_mem one_Ev fun _ => Submodule.zero_mem _

/- English proof (translation)
The claim follows from `first_order_matrix_mem (Z := 0) (Submodule.zero_mem _) hY`.
-/
private theorem epsilon_matrix_mem_first_order {Y : Fin g → Matrix (Fin n) (Fin n) X} (hY : ∀ j, Y j ∈ Od A X n a) : DD.epM Y ∈ W1 n A X g a :=
  first_order_matrix_mem (Z := 0) (Submodule.zero_mem _) hY

/- English proof (translation)
Use `Matrix.ext fun r s => ?_` and prove the remaining obligations. Establish `h0 : (M r s).a = 0 ∧ (M r s).ep = 0`. Distinguish the cases in `hrs : ((r : ℕ) < a) ↔ ((s : ℕ) < a)`. Conclude with `⟨((hM r s).1 hrs).1 rfl, ((hM r s).1 hrs).2.1 rfl⟩`. Conclude with `⟨((hM r s).2 hrs).1 rfl, ((hM r s).2 hrs).2.1 rfl⟩`.

Use extensionality with `i`. Simplify using `[e, mk1, h0.1]`. Simplify using `[e, mk1, h0.2]`. Use `congrFun (congrFun (hp i) r) s` as an intermediate fact. Rewrite `this` using `[pM_apply]`.

Rewrite using `[this]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [e, mk1, hij]`. Simplify using `[e, mk1, Pi.single_apply, hH]`.
-/
private theorem toE {M : Matrix (Fin n) (Fin n) (DD X g)} (hM : M ∈ W2 n A X g a) {Z : Matrix (Fin n) (Fin n) X}
    {H : Fin g → Matrix (Fin n) (Fin n) X} {j : Fin g} (hp : ∀ i, pM i M = (Pi.single j Z : Fin g → _) i)
    (hH : H j = M.map DD.eta) : (e j : DD X g) • mk1 Z H = M := by
  refine Matrix.ext fun r s => ?_
  have h0 : (M r s).a = 0 ∧ (M r s).ep = 0 := by
    by_cases hrs : ((r : ℕ) < a) ↔ ((s : ℕ) < a)
    · exact ⟨((hM r s).1 hrs).1 rfl, ((hM r s).1 hrs).2.1 rfl⟩
    · exact ⟨((hM r s).2 hrs).1 rfl, ((hM r s).2 hrs).2.1 rfl⟩
  ext i
  · simp [e, mk1, h0.1]
  · simp [e, mk1, h0.2]
  · have := congrFun (congrFun (hp i) r) s
    rw [pM_apply] at this
    rw [this]
    by_cases hij : i = j <;> simp [e, mk1, hij]
  · simp [e, mk1, Pi.single_apply, hH]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hB h, zero_mul]`. Rewrite using `[hT h, mul_zero]`.
-/
private theorem tri_diag {R : Type} [CommRing R] {B T : Matrix (Fin n) (Fin n) R} (hB : B.BlockTriangular id)
    (hT : T.BlockTriangular id) (i) : (B * T) i i = B i i * T i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hB h, zero_mul]
  · rw [hT h, mul_zero]

/- English proof (translation)
Use `⟨fun i j hij => (((hB.mul hT).mul hB').sub hT) hij, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, tri_diag (hB.mul hT) hB', tri_diag hB hT]`. Take the linear combination `T i i * hd i`.
-/
private theorem tri_conj {R : Type} [CommRing R] {B T B' : Matrix (Fin n) (Fin n) R} (hB : B.BlockTriangular id)
    (hT : T.BlockTriangular id) (hB' : B'.BlockTriangular id) (hd : ∀ i, B i i * B' i i = 1) :
    (∀ i j, j < i → (B * T * B' - T) i j = 0) ∧ ∀ i, (B * T * B' - T) i i = 0 := by
  refine ⟨fun i j hij => (((hB.mul hT).mul hB').sub hT) hij, fun i => ?_⟩
  rw [Matrix.sub_apply, tri_diag (hB.mul hT) hB', tri_diag hB hT]
  linear_combination T i i * hd i

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem smul_conj {R : Type} [CommRing R] (c : R) (P M Q : Matrix (Fin n) (Fin n) R) :
    c • (P * M * Q) = P * (c • M) * Q := by
  simp

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `Matrix.ext fun i j => zero_of (sub_mem hM hN) (by rw [map_sub, ha, sub_self]; rfl) fun k => ?_` and prove the remaining obligations. Rewrite using `[smul_sub, he k, sub_self]`. Both sides reduce to the same expression.
-/
private theorem eq_of {M N : Matrix (Fin n) (Fin n) (DD X g)} (hM : M ∈ SM X g n) (hN : N ∈ SM X g n)
    (ha : aM M = aM N) (he : ∀ k, (e k : DD X g) • M = (e k : DD X g) • N) : M = N := by
  rw [← sub_eq_zero]
  refine Matrix.ext fun i j => zero_of (sub_mem hM hN) (by rw [map_sub, ha, sub_self]; rfl) fun k => ?_
  rw [smul_sub, he k, sub_self]; rfl

section K

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {x : NP F n} (k : Kap x) (R : Type) [CommRing R] [Algebra x.A R]

/- English proof (translation)
The claim follows from `mul_mem (add_mem (one_mem _) (epM_SM _)) (C_SM (x.ρX R γ))`.
-/
private theorem ρ1_SM (γ) : k.ρ1 R γ ∈ SM R k.g n :=
  mul_mem (add_mem (one_mem _) (epM_SM _)) (C_SM (x.ρX R γ))

/- English proof (translation)
The claim follows from `mul_mem (sub_mem (one_mem _) (epM_SM _)) (C_SM (x.wX R v))`.
-/
private theorem weyl_lift_mem_square_zero (v) : k.w1 R v ∈ SM R k.g n :=
  mul_mem (sub_mem (one_mem _) (epM_SM _)) (C_SM (x.wX R v))

/- English proof (translation)
The claim follows from `mul_mem (C_SM (x.wiX R v)) (add_mem (one_mem _) (epM_SM _))`.
-/
private theorem inverse_weyl_lift_mem_square_zero (v) : k.wi1 R v ∈ SM R k.g n :=
  mul_mem (C_SM (x.wiX R v)) (add_mem (one_mem _) (epM_SM _))

/- English proof (translation)
Rewrite using `[Kap.ρ1, map_mul, map_add, map_one, aM_epM, add_zero, one_mul]`. Both sides reduce to the same expression.
-/
private theorem aM_ρ1 (γ) : aM (k.ρ1 R γ) = x.ρX R γ := by
  rw [Kap.ρ1, map_mul, map_add, map_one, aM_epM, add_zero, one_mul]; rfl

/- English proof (translation)
Rewrite using `[Kap.w1, map_mul, map_sub, map_one, aM_epM, sub_zero, one_mul]`. Both sides reduce to the same expression.
-/
private theorem constant_part_weyl_lift (v) : aM (k.w1 R v) = x.wX R v := by
  rw [Kap.w1, map_mul, map_sub, map_one, aM_epM, sub_zero, one_mul]; rfl

/- English proof (translation)
Rewrite using `[Kap.wi1, map_mul, map_add, map_one, aM_epM, add_zero, mul_one]`. Both sides reduce to the same expression.
-/
private theorem constant_part_inverse_weyl_lift (v) : aM (k.wi1 R v) = x.wiX R v := by
  rw [Kap.wi1, map_mul, map_add, map_one, aM_epM, add_zero, mul_one]; rfl

private def EY (v : F.Vl) : Matrix (Fin n) (Fin n) (DD R k.g) := DD.epM fun j => (k.Y j v).map (algebraMap x.A R)

/- English proof (translation)
Use `epsilon_matrix_mem_first_order fun j r s => ⟨fun hrs => ?_, fun _ => trivial⟩` and prove the remaining obligations. Establish `: k.Y j v r s = 0` using `(k.Y_mem j v r s).1 hrs`. Simplify using `[this]`.
-/
private theorem weyl_correction_mem_first_order (v) : EY k R v ∈ W1 n x.A R k.g x.a := by
  refine epsilon_matrix_mem_first_order fun j r s => ⟨fun hrs => ?_, fun _ => trivial⟩
  have : k.Y j v r s = 0 := (k.Y_mem j v r s).1 hrs
  simp [this]

private def corr (v : F.Vl) (Q : Fin k.g → Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (DD R k.g) :=
  (1 - EY k R v) * mk2 Q * (1 + EY k R v)

/- English proof (translation)
The claim follows from `second_order_mul_first_order_mem (twoSubspaceIntersection (sub_mem one_mem_first_order (weyl_correction_mem_first_order k R v)) (second_order_matrix_mem hQ)) (add_mem one_mem_first_order (weyl_correction_mem_first_order k R v))`.
-/
private theorem weyl_correction_mem_second_order (v) {Q : Fin k.g → Matrix (Fin n) (Fin n) R} (hQ : ∀ j, Q j ∈ Ev x.A R n x.a) :
    corr k R v Q ∈ W2 n x.A R k.g x.a :=
  second_order_mul_first_order_mem (twoSubspaceIntersection (sub_mem one_mem_first_order (weyl_correction_mem_first_order k R v)) (second_order_matrix_mem hQ)) (add_mem one_mem_first_order (weyl_correction_mem_first_order k R v))

/- English proof (translation)
Rewrite using `[corr, EY, pM_conj i (sub_mem (one_mem _) (epM_SM _)) (add_mem (one_mem _) (epM_SM _)), map_sub, map_add, aM_epM, second_order_part_of_matrix]`. Simplify using the standard rewrite rules.
-/
private theorem pM_corr (v) (Q : Fin k.g → Matrix (Fin n) (Fin n) R) (i) : pM i (corr k R v Q) = Q i := by
  rw [corr, EY, pM_conj i (sub_mem (one_mem _) (epM_SM _)) (add_mem (one_mem _) (epM_SM _)), map_sub, map_add, aM_epM, second_order_part_of_matrix]
  simp

/- English proof (translation)
Establish `h1 : (1 + EY k R v) * (1 - EY k R v) = 1`. Establish `: EY k R v * EY k R v = 0` using `epM_sq _`. Rewrite using `[add_mul, mul_sub, mul_sub, this]`. Simplify using the standard rewrite rules. Rewrite using `[← conjugate_second_order_matrix]`.

Use `show (x.wiX R v).map DD.C * (1 + EY k R v) * ((1 - EY k R v) * mk2 Q * (1 + EY k R v)) * ((1 - EY k R v) * (x.wX R v).map DD.C) = _`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem corr_conj (v) (Q : Fin k.g → Matrix (Fin n) (Fin n) R) :
    k.wi1 R v * corr k R v Q * k.w1 R v = mk2 fun i => x.wiX R v * Q i * x.wX R v := by
  have h1 : (1 + EY k R v) * (1 - EY k R v) = 1 := by
    have : EY k R v * EY k R v = 0 := epM_sq _
    rw [add_mul, mul_sub, mul_sub, this]; simp
  rw [← conjugate_second_order_matrix]
  show (x.wiX R v).map DD.C * (1 + EY k R v) * ((1 - EY k R v) * mk2 Q * (1 + EY k R v)) *
    ((1 - EY k R v) * (x.wX R v).map DD.C) = _
  calc _ = (x.wiX R v).map DD.C * ((1 + EY k R v) * (1 - EY k R v)) * mk2 Q * ((1 + EY k R v) *
    (1 - EY k R v)) * (x.wX R v).map DD.C := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, mul_one, mul_one]

end K

end UpperTheory.V.Pa.Lift1

open UpperTheory.V.Pa.Lift1

/- English proof (translation)
Introduce `l _ L G G0 h n x k z hz hb hl`. Use `choose Ψ hΨ hΨb hΨe using hl`. Take `⟨z1, -, z3, z4, z5, z6⟩` from `hz`. Establish `hp : ∀ j γ i, pM i (Ψ j γ) = (Pi.single j (z γ) : Fin k.g → _) i`. Introduce `j γ i`.

Use extensionality with `a b`. Rewrite using `[pM_apply, hΨe]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij]`. Use `set y : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g) := fun γ => mk1 (z γ) fun j => (Ψ j γ).map DD.eta with hy`. Establish `hE : ∀ j γ, (e j : DD x.Fr k.g) • y γ = Ψ j γ` using `fun j γ => toE ((hΨ j).1 γ) (hp j γ) rfl`.

Establish `hS : ∀ γ, y γ ∈ SM x.Fr k.g n` using `fun γ => first_order_matrix_mem_square_zero _ _`. Establish `ha : ∀ γ, aM (y γ) = z γ` using `fun γ => rfl`. Use `⟨y, ⟨fun γ => first_order_matrix_mem (z1 γ) fun j => eta_Od ((hΨ j).1 γ), fun i j N => ?_, fun γ δ => ?_, fun γ => ?_, fun u γ hγ => ?_, fun v => ?_⟩, fun i j => ⟨hb i j, fun r => (hΨb r i j).2.2.2, fun r => ?_, ?_⟩, fun γ => rfl⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap x.A (DD x.Fr k.g) x.t)` using `IsUnit.map DD.C (Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective x.A x.Fr)).2 PowerSeries.X_ne_zero))`. Use `IsLocallyConstant.of_constant _ fun a b => ?_` and prove the remaining obligations.

Rewrite using `[Ideal.Quotient.eq, Ideal.span_singleton_eq_top.2 hu, Ideal.top_pow]`. Discharge the goal by the elementary cases of `trivial`. Use `eq_of (hS _) (add_mem (hS _) (mul_mem (mul_mem (ρ1_SM k _ _) (hS _)) (ρ1_SM k _ _))) ?_ fun j => ?_` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, aM_ρ1, aM_ρ1, ha, ha, ha]`. Conclude with `z3 γ δ`.

Rewrite using `[smul_add, smul_conj, hE, hE, hE]`. Conclude with `(hΨ j).2.2.1 γ δ`. Use extensionality with `a b r`. Conclude with `congrFun (congrFun (z4 γ) a) b`. Conclude with `congrArg DD.eta (congrFun (congrFun ((hΨ r).2.2.2.1 γ) a) b)`.

Conclude with `neg_zero.symm`. Conclude with `neg_zero.symm`. Use `eq_of (hS _) (zero_mem _) ?_ fun j => ?_` and prove the remaining obligations. Rewrite using `[ha, map_zero]`. Conclude with `z5 u γ hγ`.

Rewrite using `[hE, smul_zero]`. Conclude with `(hΨ j).2.2.2.2.1 u γ hγ`. Take `⟨Y, hY, hloc⟩` from `z6 v choose Yj hYj hlocj using fun j => (hΨ j).2.2.2.2.2 v`. Establish `hφ` using `(homBasic l L G G0 h).2.2.2.1 v`. Establish `hφ' : ∀ g, h.p₀ (G.φ v g)⁻¹ = (G0.φ v g)⁻¹` using `fun g => by rw [map_inv, hφ]`.

Take `⟨hw1, hw2, htri⟩` from `(rho1Tri l L G G0 h n x k x.Fr).2.2.2.2.2 v`. Use `set Q : Fin k.g → Fin k.g → Matrix (Fin n) (Fin n) x.Fr := fun j i => pM i (Yj j) - (Pi.single j Y : Fin k.g → _) i with hQ`. Establish `hQe : ∀ j i, Q j i ∈ Ev x.A x.Fr n x.a`. Introduce `j i`. Use `sub_mem (pM_Ev (hYj j) i) ?_` and prove the remaining obligations.

Distinguish the cases in `hij : i = j`. Simplify `hY` using `[hij]`. Simplify using `[hij]`. Establish `hQt : ∀ j i a b, b < a → (x.wiX x.Fr v * Q j i * x.wX x.Fr v) a b = 0`. Introduce `j i`.

Use `localInvariants_eq_zero l L G G0 h n x v (Q j i) fun g a b hab => ?_` and prove the remaining obligations. Establish `h1 : pM i (k.wi1 x.Fr v * (Ψ j (G.φ v g) - (k.ρ1 x.Fr (h.p₀ (G.φ v g)) * Yj j * k.ρ1 x.Fr (h.p₀ (G.φ v g)⁻¹) - Yj j)) * k.w1 x.Fr v) a b = 0`. Rewrite using `[pM_apply]`. Conclude with `congrArg (fun u => DD.ep' u i) ((hlocj j g).1 a b hab)`. Establish `h2 : (x.wiX x.Fr v * (z (G.φ v g) - (x.ρX x.Fr (h.p₀ (G.φ v g)) * Y * x.ρX x.Fr (h.p₀ (G.φ v g)⁻¹) - Y)) * x.wX x.Fr v) a b = 0` using `(hloc g).1 a b hab`.

Rewrite `h1` using `[pM_conj i (inverse_weyl_lift_mem_square_zero k _ _) (weyl_lift_mem_square_zero k _ _), map_sub, map_sub, pM_conj i (ρ1_SM k _ _) (ρ1_SM k _ _), aM_ρ1, aM_ρ1, constant_part_weyl_lift, constant_part_inverse_weyl_lift, hp]`. Rewrite `h1`, `h2` using `[hφ, hφ']`. Simplify using `only [dY, hQ]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `only [Pi.single_eq_same, mul_sub, sub_mul, Matrix.sub_apply] at h1 h2 ⊢`. Take the linear combination `h2 - h1`. Simplify using `only [Pi.single_eq_of_ne hij, mul_sub, sub_mul, Matrix.sub_apply, mul_zero, zero_mul, Matrix.zero_apply, sub_zero] at h1 ⊢`. Take the linear combination `-h1`. Establish `hW : ∀ j, Yj j - corr k x.Fr v (Q j) ∈ W2 n x.A x.Fr k.g x.a` using `fun j => sub_mem (hYj j) (weyl_correction_mem_second_order k _ v (hQe j))`.

Use `set Y' : Matrix (Fin n) (Fin n) (DD x.Fr k.g) := mk1 Y fun j => (Yj j - corr k x.Fr v (Q j)).map DD.eta with hY'`. Establish `hE' : ∀ j, (e j : DD x.Fr k.g) • Y' = Yj j - corr k x.Fr v (Q j)` using `fun j => toE (hW j) (fun i => by rw [map_sub, pM_corr]; simp only [hQ, sub_sub_cancel]) rfl`. Establish `hS' : Y' ∈ SM x.Fr k.g n` using `first_order_matrix_mem_square_zero _ _`. Use `⟨Y', first_order_matrix_mem hY fun j => eta_Od (hW j), fun g => ?_⟩` and prove the remaining obligations. Use `set r := k.ρ1 x.Fr (h.p₀ (G.φ v g)) with hr`.

Use `set r' := k.ρ1 x.Fr (h.p₀ (G.φ v g)⁻¹) with hr'`. Establish `hM : k.wi1 x.Fr v * (y (G.φ v g) - (r * Y' * r' - Y')) * k.w1 x.Fr v ∈ SM x.Fr k.g n` using `mul_mem (mul_mem (inverse_weyl_lift_mem_square_zero k _ _) (sub_mem (hS _) (sub_mem (mul_mem (mul_mem (ρ1_SM k _ _) hS') (ρ1_SM k _ _)) hS'))) (weyl_lift_mem_square_zero k _ _)`. Establish `hA : aM (k.wi1 x.Fr v * (y (G.φ v g) - (r * Y' * r' - Y')) * k.w1 x.Fr v) = x.wiX x.Fr v * (z (G.φ v g) - (x.ρX x.Fr (h.p₀ (G.φ v g)) * Y * x.ρX x.Fr (h.p₀ (G.φ v g)⁻¹) - Y)) * x.wX x.Fr v`. Rewrite using `[map_mul, map_mul, map_sub, map_sub, map_mul, map_mul, aM_ρ1, aM_ρ1, constant_part_weyl_lift, constant_part_inverse_weyl_lift, ha, constant_part_first_order_matrix]`. Establish `hB : ∀ j, (e j : DD x.Fr k.g) • (k.wi1 x.Fr v * (y (G.φ v g) - (r * Y' * r' - Y')) * k.w1 x.Fr v) = k.wi1 x.Fr v * (Ψ j (G.φ v g) - (r * Yj j * r' - Yj j)) * k.w1 x.Fr v + ((k.wi1 x.Fr v * r * k.w1 x.Fr v) * (k.wi1 x.Fr v * corr k x.Fr v (Q j) * k.w1 x.Fr v) * (k.wi1 x.Fr v * r' …`.

Introduce `j`. Establish `e1 : ∀ P : Matrix (Fin n) (Fin n) (DD x.Fr k.g), k.w1 x.Fr v * (k.wi1 x.Fr v * P) = P` using `fun P => by`. Rewrite using `[← mul_assoc, hw1, one_mul]`. Rewrite using `[smul_conj, smul_sub, smul_sub, smul_conj, hE, hE']`. Simplify using `only [mul_sub, sub_mul, mul_assoc, e1]`.

Normalize the expressions using the abelian group laws. Establish `hC : ∀ j, _` using `fun j => tri_conj (B := k.wi1 x.Fr v * r * k.w1 x.Fr v) (T := k.wi1 x.Fr v * corr k x.Fr v (Q j) * k.w1 x.Fr v) (B' := k.wi1 x.Fr v * r' * k.w1 x.Fr v) (fun a b hab => by rw [hr, hφ]; exact (htri g).1 a b hab) (fun a b hab => by`. Rewrite using `[corr_conj]`. Conclude with `DD.ext rfl rfl (funext fun i => hQt j i a b hab) rfl)`. Use the proof step `(fun a b hab => by rw [hr', hφ', ← map_inv]; exact (htri g⁻¹).1 a b hab)`.

Use the proof step `(fun a => by`. Rewrite using `[hr, hr', hφ, hφ', ← map_inv, (htri g).2, (htri g⁻¹).2, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one])`. Use `⟨fun a b hab => zero_of hM ?_ fun j => ?_, fun hg a => zero_of hM ?_ fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hA]`. Conclude with `(hloc g).1 a b hab`.

Rewrite using `[hB, Matrix.add_apply, (hC j).1 a b hab, add_zero]`. Conclude with `(hlocj j g).1 a b hab`. Rewrite using `[hA]`. Conclude with `(hloc g).2 hg a`. Rewrite using `[hB, Matrix.add_apply, (hC j).2 a, add_zero]`.

Conclude with `(hlocj j g).2 hg a`. Conclude with `(bndOps x.K G.G₀).1 0`. Conclude with `(bndOps x.K G.G₀).1 0`.
-/
theorem UpperTheory.V.Pa.lift1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ z ∈ SelP h x x.Fr, BndM x.t z → (∀ j, Lifts h k (Pi.single j z)) → ∃ y ∈ Sel1 h x.Fr k, BndD x.t y ∧ ∀ γ, (y γ).map (fun a => a.a) = z γ := by
  intro l _ L G G0 h n x k z hz hb hl
  choose Ψ hΨ hΨb hΨe using hl
  obtain ⟨z1, -, z3, z4, z5, z6⟩ := hz
  have hp : ∀ j γ i, pM i (Ψ j γ) = (Pi.single j (z γ) : Fin k.g → _) i := by
    intro j γ i
    ext a b
    rw [pM_apply, hΨe]
    by_cases hij : i = j <;> simp [hij]
  set y : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g) := fun γ => mk1 (z γ) fun j => (Ψ j γ).map DD.eta with hy
  have hE : ∀ j γ, (e j : DD x.Fr k.g) • y γ = Ψ j γ := fun j γ => toE ((hΨ j).1 γ) (hp j γ) rfl
  have hS : ∀ γ, y γ ∈ SM x.Fr k.g n := fun γ => first_order_matrix_mem_square_zero _ _
  have ha : ∀ γ, aM (y γ) = z γ := fun γ => rfl
  refine ⟨y, ⟨fun γ => first_order_matrix_mem (z1 γ) fun j => eta_Od ((hΨ j).1 γ), fun i j N => ?_, fun γ δ => ?_, fun γ => ?_,
    fun u γ hγ => ?_, fun v => ?_⟩, fun i j => ⟨hb i j, fun r => (hΨb r i j).2.2.2, fun r => ?_, ?_⟩, fun γ => rfl⟩
  · have hu : IsUnit (algebraMap x.A (DD x.Fr k.g) x.t) :=
      IsUnit.map DD.C (Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective x.A x.Fr)).2 PowerSeries.X_ne_zero))
    refine IsLocallyConstant.of_constant _ fun a b => ?_
    rw [Ideal.Quotient.eq, Ideal.span_singleton_eq_top.2 hu, Ideal.top_pow]
    trivial
  · refine eq_of (hS _) (add_mem (hS _) (mul_mem (mul_mem (ρ1_SM k _ _) (hS _)) (ρ1_SM k _ _))) ?_ fun j => ?_
    · rw [map_add, map_mul, map_mul, aM_ρ1, aM_ρ1, ha, ha, ha]
      exact z3 γ δ
    · rw [smul_add, smul_conj, hE, hE, hE]
      exact (hΨ j).2.2.1 γ δ
  · ext a b r
    · exact congrFun (congrFun (z4 γ) a) b
    · exact congrArg DD.eta (congrFun (congrFun ((hΨ r).2.2.2.1 γ) a) b)
    · exact neg_zero.symm
    · exact neg_zero.symm
  · refine eq_of (hS _) (zero_mem _) ?_ fun j => ?_
    · rw [ha, map_zero]; exact z5 u γ hγ
    · rw [hE, smul_zero]; exact (hΨ j).2.2.2.2.1 u γ hγ
  · obtain ⟨Y, hY, hloc⟩ := z6 v
    choose Yj hYj hlocj using fun j => (hΨ j).2.2.2.2.2 v
    have hφ := (homBasic l L G G0 h).2.2.2.1 v
    have hφ' : ∀ g, h.p₀ (G.φ v g)⁻¹ = (G0.φ v g)⁻¹ := fun g => by rw [map_inv, hφ]
    obtain ⟨hw1, hw2, htri⟩ := (rho1Tri l L G G0 h n x k x.Fr).2.2.2.2.2 v
    set Q : Fin k.g → Fin k.g → Matrix (Fin n) (Fin n) x.Fr :=
      fun j i => pM i (Yj j) - (Pi.single j Y : Fin k.g → _) i with hQ
    have hQe : ∀ j i, Q j i ∈ Ev x.A x.Fr n x.a := by
      intro j i
      refine sub_mem (pM_Ev (hYj j) i) ?_
      by_cases hij : i = j
      · simpa [hij] using hY
      · simp [hij]
    have hQt : ∀ j i a b, b < a → (x.wiX x.Fr v * Q j i * x.wX x.Fr v) a b = 0 := by
      intro j i
      refine localInvariants_eq_zero l L G G0 h n x v (Q j i) fun g a b hab => ?_
      have h1 : pM i (k.wi1 x.Fr v * (Ψ j (G.φ v g) - (k.ρ1 x.Fr (h.p₀ (G.φ v g)) * Yj j *
          k.ρ1 x.Fr (h.p₀ (G.φ v g)⁻¹) - Yj j)) * k.w1 x.Fr v) a b = 0 := by
        rw [pM_apply]
        exact congrArg (fun u => DD.ep' u i) ((hlocj j g).1 a b hab)
      have h2 : (x.wiX x.Fr v * (z (G.φ v g) - (x.ρX x.Fr (h.p₀ (G.φ v g)) * Y *
          x.ρX x.Fr (h.p₀ (G.φ v g)⁻¹) - Y)) * x.wX x.Fr v) a b = 0 := (hloc g).1 a b hab
      rw [pM_conj i (inverse_weyl_lift_mem_square_zero k _ _) (weyl_lift_mem_square_zero k _ _), map_sub, map_sub, pM_conj i (ρ1_SM k _ _) (ρ1_SM k _ _),
        aM_ρ1, aM_ρ1, constant_part_weyl_lift, constant_part_inverse_weyl_lift, hp] at h1
      rw [hφ, hφ'] at h1 h2
      simp only [dY, hQ]
      by_cases hij : i = j
      · subst hij
        simp only [Pi.single_eq_same, mul_sub, sub_mul, Matrix.sub_apply] at h1 h2 ⊢
        linear_combination h2 - h1
      · simp only [Pi.single_eq_of_ne hij, mul_sub, sub_mul, Matrix.sub_apply, mul_zero, zero_mul,
          Matrix.zero_apply, sub_zero] at h1 ⊢
        linear_combination -h1
    have hW : ∀ j, Yj j - corr k x.Fr v (Q j) ∈ W2 n x.A x.Fr k.g x.a :=
      fun j => sub_mem (hYj j) (weyl_correction_mem_second_order k _ v (hQe j))
    set Y' : Matrix (Fin n) (Fin n) (DD x.Fr k.g) := mk1 Y fun j => (Yj j - corr k x.Fr v (Q j)).map DD.eta with hY'
    have hE' : ∀ j, (e j : DD x.Fr k.g) • Y' = Yj j - corr k x.Fr v (Q j) := fun j =>
      toE (hW j) (fun i => by rw [map_sub, pM_corr]; simp only [hQ, sub_sub_cancel]) rfl
    have hS' : Y' ∈ SM x.Fr k.g n := first_order_matrix_mem_square_zero _ _
    refine ⟨Y', first_order_matrix_mem hY fun j => eta_Od (hW j), fun g => ?_⟩
    set r := k.ρ1 x.Fr (h.p₀ (G.φ v g)) with hr
    set r' := k.ρ1 x.Fr (h.p₀ (G.φ v g)⁻¹) with hr'
    have hM : k.wi1 x.Fr v * (y (G.φ v g) - (r * Y' * r' - Y')) * k.w1 x.Fr v ∈ SM x.Fr k.g n :=
      mul_mem (mul_mem (inverse_weyl_lift_mem_square_zero k _ _) (sub_mem (hS _) (sub_mem (mul_mem (mul_mem (ρ1_SM k _ _) hS') (ρ1_SM k _ _)) hS')))
        (weyl_lift_mem_square_zero k _ _)
    have hA : aM (k.wi1 x.Fr v * (y (G.φ v g) - (r * Y' * r' - Y')) * k.w1 x.Fr v) =
        x.wiX x.Fr v * (z (G.φ v g) - (x.ρX x.Fr (h.p₀ (G.φ v g)) * Y *
          x.ρX x.Fr (h.p₀ (G.φ v g)⁻¹) - Y)) * x.wX x.Fr v := by
      rw [map_mul, map_mul, map_sub, map_sub, map_mul, map_mul, aM_ρ1, aM_ρ1, constant_part_weyl_lift, constant_part_inverse_weyl_lift, ha, constant_part_first_order_matrix]
    have hB : ∀ j, (e j : DD x.Fr k.g) • (k.wi1 x.Fr v * (y (G.φ v g) - (r * Y' * r' - Y')) * k.w1 x.Fr v) =
        k.wi1 x.Fr v * (Ψ j (G.φ v g) - (r * Yj j * r' - Yj j)) * k.w1 x.Fr v +
        ((k.wi1 x.Fr v * r * k.w1 x.Fr v) * (k.wi1 x.Fr v * corr k x.Fr v (Q j) * k.w1 x.Fr v) *
          (k.wi1 x.Fr v * r' * k.w1 x.Fr v) - k.wi1 x.Fr v * corr k x.Fr v (Q j) * k.w1 x.Fr v) := by
      intro j
      have e1 : ∀ P : Matrix (Fin n) (Fin n) (DD x.Fr k.g), k.w1 x.Fr v * (k.wi1 x.Fr v * P) = P := fun P => by
        rw [← mul_assoc, hw1, one_mul]
      rw [smul_conj, smul_sub, smul_sub, smul_conj, hE, hE']
      simp only [mul_sub, sub_mul, mul_assoc, e1]
      abel
    have hC : ∀ j, _ := fun j => tri_conj (B := k.wi1 x.Fr v * r * k.w1 x.Fr v)
      (T := k.wi1 x.Fr v * corr k x.Fr v (Q j) * k.w1 x.Fr v) (B' := k.wi1 x.Fr v * r' * k.w1 x.Fr v)
      (fun a b hab => by rw [hr, hφ]; exact (htri g).1 a b hab)
      (fun a b hab => by
        rw [corr_conj]
        exact DD.ext rfl rfl (funext fun i => hQt j i a b hab) rfl)
      (fun a b hab => by rw [hr', hφ', ← map_inv]; exact (htri g⁻¹).1 a b hab)
      (fun a => by
        rw [hr, hr', hφ, hφ', ← map_inv, (htri g).2, (htri g⁻¹).2, ← map_mul, ← Units.val_mul, ← map_mul,
          mul_inv_cancel, map_one, Units.val_one, map_one])
    refine ⟨fun a b hab => zero_of hM ?_ fun j => ?_, fun hg a => zero_of hM ?_ fun j => ?_⟩
    · rw [hA]; exact (hloc g).1 a b hab
    · rw [hB, Matrix.add_apply, (hC j).1 a b hab, add_zero]; exact (hlocj j g).1 a b hab
    · rw [hA]; exact (hloc g).2 hg a
    · rw [hB, Matrix.add_apply, (hC j).2 a, add_zero]; exact (hlocj j g).2 hg a
  · exact (bndOps x.K G.G₀).1 0
  · exact (bndOps x.K G.G₀).1 0
