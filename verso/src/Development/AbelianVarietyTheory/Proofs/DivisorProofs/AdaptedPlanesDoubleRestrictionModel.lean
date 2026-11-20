import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBaseChangeMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticExtensionSymplecticCoordinates

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv

noncomputable section

namespace GlobalTheory.TwoPlanes

abbrev Ix (m : ℕ) : Type := Option (Option (Fin m))

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n m d n₁ d₁ : ℕ}

def vec3 {S : Type} (s t : S) (u : Fin m → S) : Ix m → S := fun a => a.elim s fun b => b.elim t u

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem vec_three_none {S : Type} (s t : S) (u : Fin m → S) : vec3 s t u none = s := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem vec_three_some_none {S : Type} (s t : S) (u : Fin m → S) : vec3 s t u (some none) = t := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem vec_three_some_some {S : Type} (s t : S) (u : Fin m → S) (i : Fin m) : vec3 s t u (some (some i)) = u i := rfl

def frame {S : Type} (x y : Fin n → S) (ι : Matrix (Fin n) (Fin m) S) : Matrix (Fin n) (Ix m) S :=
  Matrix.of fun r => vec3 (x r) (y r) (ι r)

def gramM (ε : S) (J : Matrix (Fin m) (Fin m) S) : Matrix (Ix m) (Ix m) S :=
  Matrix.of (vec3 (vec3 0 1 0) (vec3 ε 0 0) fun i => vec3 0 0 (J i))

def embM (z : Matrix (Fin n₁) (Fin d₁) S) : Matrix (Ix n₁) (Ix d₁) S :=
  Matrix.of (vec3 0 0 fun i => vec3 0 0 (z i))

/- English proof (translation)
Use function extensionality and compare the values at `r`. Simplify using `[frame, Matrix.mulVec, dotProduct, Fintype.sum_option]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frame_mulVec (x y : Fin n → S) (ι : Matrix (Fin n) (Fin m) S) (s t : S) (u : Fin m → S) :
    frame x y ι *ᵥ vec3 s t u = s • x + ι *ᵥ u + t • y := by
  funext r
  simp [frame, Matrix.mulVec, dotProduct, Fintype.sum_option]
  ring

/- English proof (translation)
Use extensionality with `r l`. Simplify using `[frame, embM, Matrix.mul_apply, Fintype.sum_option]`.
-/
theorem frame_embM (x y : Fin n → S) (ι : Matrix (Fin n) (Fin n₁) S) (x' y' : Fin d → S) (ι' : Matrix (Fin d) (Fin d₁) S)
    (z : Matrix (Fin n₁) (Fin d₁) S) : frame x y ι * embM z * (frame x' y' ι')ᵀ = ι * z * ι'ᵀ := by
  ext r l
  simp [frame, embM, Matrix.mul_apply, Fintype.sum_option]

def mom (Z : Matrix (Ix n₁) (Ix d₁) S) : Ix n₁ ⊕ Fin d₁ → S :=
  Sum.elim (fun i => Z i none) fun j => Z none (some (some j))

def pos (Z : Matrix (Ix n₁) (Ix d₁) S) : Ix n₁ ⊕ Fin d₁ → S :=
  Sum.elim (fun i => Z i (some none)) fun j => Z (some none) (some (some j))

def core (Z : Matrix (Ix n₁) (Ix d₁) S) : Matrix (Fin n₁) (Fin d₁) S := Matrix.of fun i j => Z (some (some i)) (some (some j))

variable (R) in

def shuffle : Matrix (Ix n₁) (Ix d₁) S ≃ₗ[R]
    ((Ix n₁ ⊕ Fin d₁ → S) × (Ix n₁ ⊕ Fin d₁ → S)) × Matrix (Fin n₁) (Fin d₁) S where
  toFun Z := ((pos Z, mom Z), core Z)
  invFun u := Matrix.of fun i => vec3 (u.1.2 (.inl i)) (u.1.1 (.inl i))
    fun j => vec3 (u.1.2 (.inr j)) (u.1.1 (.inr j)) (fun i' => u.2 i' j) i
  map_add' Z Z' := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext k; rcases k with k | k <;> rfl
    · funext k; rcases k with k | k <;> rfl
    · rfl
  map_smul' a Z := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext k; rcases k with k | k <;> rfl
    · funext k; rcases k with k | k <;> rfl
    · rfl
  left_inv Z := by
    ext i l
    rcases l with _ | _ | l
    · rfl
    · rfl
    · rcases i with _ | _ | i <;> rfl
  right_inv u := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext k; rcases k with k | k <;> rfl
    · funext k; rcases k with k | k <;> rfl
    · rfl

/- English proof (translation)
Simplify using `only [hTens, Fintype.sum_sum_type, pos, mom, core, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.zero_apply, gramM, Matrix.of_apply, Fintype.sum_option, vec_three_no …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_gramM (c : S →ₐ[R] S) (J₁ : Matrix (Fin n₁) (Fin n₁) S) (K₁ : Matrix (Fin d₁) (Fin d₁) S)
    (Z Z' : Matrix (Ix n₁) (Ix d₁) S) :
    hTens c (gramM 1 J₁) (gramM (-1) K₁) Z Z' = hTens c J₁ K₁ (core Z) (core Z') +
      ∑ i, ∑ j, pos Z i * Matrix.fromBlocks (-gramM 1 J₁) 0 0 K₁ i j * c (mom Z' j) +
      ∑ i, ∑ j, mom Z i * Matrix.fromBlocks (gramM 1 J₁) 0 0 K₁ i j * c (pos Z' j) := by
  simp only [hTens, Fintype.sum_sum_type, pos, mom, core, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.zero_apply,
    gramM, Matrix.of_apply, Fintype.sum_option, vec_three_none, vec_three_some_none, vec_three_some_some, Pi.zero_apply, mul_zero, zero_mul,
    neg_zero, Finset.sum_const_zero, add_zero, zero_add, mul_one, mul_neg, neg_mul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  ring

/- English proof (translation)
Rewrite using `[hTens_eq_trace, hTens_eq_trace, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem hTens_mul_right (c : S →ₐ[R] S) {α β β' : Type} [Fintype α] [Fintype β] [Fintype β']
    (JA : Matrix α α S) (JB : Matrix β β S) (P : Matrix β β' S) (z z' : Matrix α β' S) :
    hTens c JA JB (z * Pᵀ) (z' * Pᵀ) = hTens c JA (Pᵀ * JB * P.map c) z z' := by
  rw [hTens_eq_trace, hTens_eq_trace, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map,
    Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hc, hJ, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_swap (c : S →ₐ[R] S) (hc : ∀ a, c (c a) = a) {α β : Type} [Fintype α] [Fintype β] (ε : S)
    (J : Matrix α α S) (hJ : ∀ i j, c (J j i) = ε * J i j) (P : Matrix α β S) (i j : β) :
    c ((Pᵀ * J * P.map c) j i) = ε * (Pᵀ * J * P.map c) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hc, hJ, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

def glue {A V₁ κ ι κ₁ : Type} [AddCommGroup A] [Module R A] [AddCommGroup V₁] [Module R V₁] (eq : κ ≃ ι ⊕ κ₁)
    (p q : A ≃ₗ[R] (ι → R)) (e₁ : V₁ ≃ₗ[R] (κ₁ → R) × (κ₁ → R)) : ((A × A) × V₁) ≃ₗ[R] (κ → R) × (κ → R) :=
  ((q.prodCongr p).prodCongr e₁) ≪≫ₗ LinearEquiv.prodProdProdComm R _ _ _ _ ≪≫ₗ
    (((LinearEquiv.sumArrowLequivProdArrow ι κ₁ R R).symm ≪≫ₗ LinearEquiv.funCongrLeft R R eq).prodCongr
      ((LinearEquiv.sumArrowLequivProdArrow ι κ₁ R R).symm ≪≫ₗ LinearEquiv.funCongrLeft R R eq))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glue_apply {A V₁ κ ι κ₁ : Type} [AddCommGroup A] [Module R A] [AddCommGroup V₁] [Module R V₁] (eq : κ ≃ ι ⊕ κ₁)
    (p q : A ≃ₗ[R] (ι → R)) (e₁ : V₁ ≃ₗ[R] (κ₁ → R) × (κ₁ → R)) (b a : A) (z : V₁) :
    glue eq p q e₁ ((b, a), z) = (fun k => Sum.elim (q b) (e₁ z).1 (eq k), fun k => Sum.elim (p a) (e₁ z).2 (eq k)) := rfl

/- English proof (translation)
Simplify using `only [dotProduct]`. Rewrite using `[eq.sum_comp fun k => Sum.elim f g k * Sum.elim f' g' k, Fintype.sum_sum_type]`. Both sides reduce to the same expression.
-/
theorem dot_elim {κ ι κ₁ : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁) (f f' : ι → R) (g g' : κ₁ → R) :
    (fun k => Sum.elim f g (eq k)) ⬝ᵥ (fun k => Sum.elim f' g' (eq k)) = f ⬝ᵥ f' + g ⬝ᵥ g' := by
  simp only [dotProduct]
  rw [eq.sum_comp fun k => Sum.elim f g k * Sum.elim f' g' k, Fintype.sum_sum_type]
  rfl

def conj {α α' β β' : Type} [Fintype α] [Fintype α'] [Fintype β] [Fintype β'] [DecidableEq α] [DecidableEq α']
    [DecidableEq β] [DecidableEq β'] (P : Matrix α α' S) (Q : Matrix α' α S) (P' : Matrix β β' S) (Q' : Matrix β' β S)
    (h1 : P * Q = 1) (h2 : Q * P = 1) (h1' : P' * Q' = 1) (h2' : Q' * P' = 1) : Matrix α β S ≃ₗ[R] Matrix α' β' S where
  toFun w := Q * w * Q'ᵀ
  invFun z := P * z * P'ᵀ
  map_add' w w' := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a w := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv w := by
    show P * (Q * w * Q'ᵀ) * P'ᵀ = w
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h1',
      Matrix.transpose_one, Matrix.mul_one]
  right_inv w := by
    show Q * (P * w * P'ᵀ) * Q'ᵀ = w
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h2',
      Matrix.transpose_one, Matrix.mul_one]

end Alg

section Form

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n₁ d₁ : ℕ}

/- English proof (translation)
Set `eA : S ≃ₐ[R] S` to `AlgEquiv.ofBijective c (Function.Involutive.bijective hc)`. Establish `hb : ∀ i j, c (Matrix.fromBlocks (-gramM 1 J₁) 0 0 K₁ i j) = -Matrix.fromBlocks (gramM 1 J₁) 0 0 K₁ j i`. Apply the tactic sequence `rintro (i | i) (j | j) <;> simp [hJ, hK]`. Establish `h : c (-∑ i, ∑ j, pos Z' i * Matrix.fromBlocks (-gramM 1 J₁) 0 0 K₁ i j * c (mom Z j)) = ∑ i, ∑ j, mom Z i * Matrix.fromBlocks (gramM 1 J₁) 0 0 K₁ i j * c (pos Z' j)`. Simplify using `only [map_neg, map_sum, map_mul, hc, hb, ← Finset.sum_neg_distrib]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `ht : ∀ a, Algebra.trace R S (c a) = Algebra.trace R S a` using `fun a => Algebra.trace_eq_of_algEquiv eA a`. Rewrite using `[← ht (-∑ i, ∑ j, pos Z' i * Matrix.fromBlocks (-gramM 1 J₁) 0 0 K₁ i j * c (mom Z j)), h, symp, symp, hTens_gramM, ← map_add, ← map_sub]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem symp_gramM (c : S →ₐ[R] S) (hc : ∀ a, c (c a) = a) (J₁ : Matrix (Fin n₁) (Fin n₁) S)
    (K₁ : Matrix (Fin d₁) (Fin d₁) S) (hJ : ∀ i j, c (gramM 1 J₁ j i) = gramM 1 J₁ i j)
    (hK : ∀ i j, c (K₁ j i) = -K₁ i j) (Z Z' : Matrix (Ix n₁) (Ix d₁) S) :
    symp c (-1) (gramM 1 J₁) (gramM (-1) K₁) Z Z' = symp c (-1) J₁ K₁ (core Z) (core Z') +
      Algebra.trace R S (-∑ i, ∑ j, pos Z i * Matrix.fromBlocks (-gramM 1 J₁) 0 0 K₁ i j * c (mom Z' j)) -
      Algebra.trace R S (-∑ i, ∑ j, pos Z' i * Matrix.fromBlocks (-gramM 1 J₁) 0 0 K₁ i j * c (mom Z j)) := by
  let eA : S ≃ₐ[R] S := AlgEquiv.ofBijective c (Function.Involutive.bijective hc)
  have hb : ∀ i j, c (Matrix.fromBlocks (-gramM 1 J₁) 0 0 K₁ i j) = -Matrix.fromBlocks (gramM 1 J₁) 0 0 K₁ j i := by
    rintro (i | i) (j | j) <;> simp [hJ, hK]
  have h : c (-∑ i, ∑ j, pos Z' i * Matrix.fromBlocks (-gramM 1 J₁) 0 0 K₁ i j * c (mom Z j)) =
      ∑ i, ∑ j, mom Z i * Matrix.fromBlocks (gramM 1 J₁) 0 0 K₁ i j * c (pos Z' j) := by
    simp only [map_neg, map_sum, map_mul, hc, hb, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have ht : ∀ a, Algebra.trace R S (c a) = Algebra.trace R S a := fun a => Algebra.trace_eq_of_algEquiv eA a
  rw [← ht (-∑ i, ∑ j, pos Z' i * Matrix.fromBlocks (-gramM 1 J₁) 0 0 K₁ i j * c (mom Z j)), h, symp, symp, hTens_gramM, ← map_add, ← map_sub]
  congr 1
  ring

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp [gramM]`.
-/
theorem gramM_map {T : Type} [CommRing T] (f : S →+* T) (ε : S) (J : Matrix (Fin n₁) (Fin n₁) S) :
    (gramM ε J).map f = gramM (f ε) (J.map f) := by
  ext a b
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp [gramM]

/- English proof (translation)
Use extensionality with `r a`. Apply the tactic sequence `rcases a with _ | _ | a <;> rfl`.
-/
theorem frame_map {T : Type} {n : ℕ} (f : S → T) (x y : Fin n → S) (ι : Matrix (Fin n) (Fin n₁) S) :
    (frame x y ι).map f = frame (fun i => f (x i)) (fun i => f (y i)) (ι.map f) := by
  ext r a
  rcases a with _ | _ | a <;> rfl

/- English proof (translation)
Rewrite using `[Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]`.
-/
theorem mul_vecMulVec_mul {α α' β β' : Type} [Fintype α] [Fintype β] (Q : Matrix α' α S) (Q' : Matrix β' β S)
    (a : α → S) (b : β → S) : Q * Matrix.vecMulVec a b * Q'ᵀ = Matrix.vecMulVec (Q *ᵥ a) (Q' *ᵥ b) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/- English proof (translation)
Establish `k : ∀ s t u, Q *ᵥ (s • x + ι *ᵥ u + t • y) = vec3 s t u` using `fun s t u => by`. Rewrite using `[← frame_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]`. Conclude with `⟨by simpa using k 1 0 0, by simpa using k 0 1 0, fun u => by simpa using k 0 0 u⟩`.
-/
theorem inv_frame {n : ℕ} {x y : Fin n → S} {ι : Matrix (Fin n) (Fin n₁) S} {Q : Matrix (Ix n₁) (Fin n) S}
    (h : Q * frame x y ι = 1) : Q *ᵥ x = vec3 1 0 0 ∧ Q *ᵥ y = vec3 0 1 0 ∧ ∀ u, Q *ᵥ (ι *ᵥ u) = vec3 0 0 u := by
  have k : ∀ s t u, Q *ᵥ (s • x + ι *ᵥ u + t • y) = vec3 s t u := fun s t u => by
    rw [← frame_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  exact ⟨by simpa using k 1 0 0, by simpa using k 0 1 0, fun u => by simpa using k 0 0 u⟩

end Form

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n m : ℕ}

/- English proof (translation)
Simplify using `only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem gram_apply (σ : E →ₐ[F] E) {α : Type} [Fintype α] (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) α E) (a b : α) :
    (Pᵀ * J * P.map σ) a b = form σ J (fun r => P r a) (fun r => P r b) := by
  simp only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Use `choose s t u h using fun i : Fin n => hspan (Pi.single i 1)`. Set `Q : Matrix (Ix m) (Fin n) E` to `Matrix.of fun a i => vec3 (s i) (t i) (u i) a`. Establish `h1 : frame x y ι * Q = 1`. Use extensionality with `r i`. Use `congrFun ((frame_mulVec x y ι (s i) (t i) (u i)).trans (h i).symm) r` as an intermediate fact.

Rewrite using `[Matrix.one_apply, ← Pi.single_apply, ← this]`. Both sides reduce to the same expression. Establish `h2 : Q * frame x y ι = 1` using `(Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 h1`. Establish `hsw` using `gram_swap σ hσ ε J hJ (frame x y ι)`. Establish `hne : ε ≠ 0` using `fun h0 => by simp [h0] at hε`.

Establish `col : ∀ i, (fun r => frame x y ι r (some (some i))) = ι *ᵥ Pi.single i 1` using `fun i => by`. Use function extensionality and compare the values at `r`. Simplify using `[frame, Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `e20 : ∀ i, ((frame x y ι)ᵀ * J * (frame x y ι).map σ) (some (some i)) none = 0` using `fun i => by`. Rewrite using `[gram_apply, col]`.

Conclude with `(horth _).1`. Establish `e21 : ∀ i, ((frame x y ι)ᵀ * J * (frame x y ι).map σ) (some (some i)) (some none) = 0` using `fun i => by`. Rewrite using `[gram_apply, col]`. Conclude with `(horth _).2`. Establish `e01 : ((frame x y ι)ᵀ * J * (frame x y ι).map σ) none (some none) = 1`.

Rewrite using `[gram_apply]`. Conclude with `hxy`. Establish `hG : (frame x y ι)ᵀ * J * (frame x y ι).map σ = gramM ε J₁`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with _ | _ | a <;> rcases b with _ | _ | b`.

Rewrite using `[gram_apply]`. Conclude with `hxx`. Conclude with `e01`. Use `hsw none (some (some b))` as an intermediate fact. Rewrite `this` using `[e20, map_zero]`.

Conclude with `(mul_eq_zero.1 this.symm).resolve_left hne`. Use `hsw (some none) none` as an intermediate fact. Rewrite `this` using `[e01, map_one]`. Use `show _ = ε`. Take the linear combination `(-ε) * this - ((frame x y ι)ᵀ * J * (frame x y ι).map σ) (some none) none * hε`.

Rewrite using `[gram_apply]`. Conclude with `hyy`. Use `hsw (some none) (some (some b))` as an intermediate fact. Rewrite `this` using `[e21, map_zero]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left hne`.

Conclude with `e20 a`. Conclude with `e21 a`. Use `show _ = J₁ a b`. Rewrite using `[← hgram, gram_apply, gram_apply]`. Both sides reduce to the same expression.

Establish `hGd : (gramM ε J₁).det ≠ 0`. Use `(Matrix.isUnit_det_of_left_inverse (B := Q.map σ * J⁻¹ * Qᵀ) ?_).ne_zero` and prove the remaining obligations. Rewrite using `[← hG]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`.

Use `_ = 1 := by`. Rewrite using `[h1, Matrix.transpose_one, Matrix.one_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), Matrix.mul_one, ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `⟨Q, h1, h2, hG, hGd, fun h0 => ?_, fun i j => hG ▸ hsw i j⟩` and prove the remaining obligations. Take `⟨v, hv0, hv⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h0`. Use `hGd (Matrix.exists_vecMul_eq_zero_iff.1 ⟨vec3 0 0 v, fun h' => hv0 (funext fun i => congrFun h' (some (some i))), ?_⟩)` and prove the remaining obligations.

Use function extensionality and compare the values at `b`. Break down `b with _ | _ | b` into its components or cases. Simplify using `[gramM, Matrix.vecMul, dotProduct, Fintype.sum_option]`. Simplify using `[gramM, Matrix.vecMul, dotProduct, Fintype.sum_option]`. Simplify `congrFun hv b` using `[gramM, Matrix.vecMul, dotProduct, Fintype.sum_option]`.
-/
theorem frame_spec (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (ε : E) (hε : ε * ε = 1) (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = ε * J i j) (hdet : J.det ≠ 0) (hn : n = m + 2) (x y : Fin n → E)
    (ι : Matrix (Fin n) (Fin m) E) (J₁ : Matrix (Fin m) (Fin m) E) (hxx : form σ J x x = 0) (hyy : form σ J y y = 0)
    (hxy : form σ J x y = 1) (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hgram : ιᵀ * J * ι.map σ = J₁) (hspan : ∀ v, ∃ (s t : E) (u : Fin m → E), v = s • x + ι *ᵥ u + t • y) :
    ∃ Q : Matrix (Ix m) (Fin n) E, frame x y ι * Q = 1 ∧ Q * frame x y ι = 1 ∧ (frame x y ι)ᵀ * J * (frame x y ι).map σ = gramM ε J₁ ∧
      (gramM ε J₁).det ≠ 0 ∧ J₁.det ≠ 0 ∧ (∀ i j, σ (gramM ε J₁ j i) = ε * gramM ε J₁ i j) := by
  choose s t u h using fun i : Fin n => hspan (Pi.single i 1)
  let Q : Matrix (Ix m) (Fin n) E := Matrix.of fun a i => vec3 (s i) (t i) (u i) a
  have h1 : frame x y ι * Q = 1 := by
    ext r i
    have := congrFun ((frame_mulVec x y ι (s i) (t i) (u i)).trans (h i).symm) r
    rw [Matrix.one_apply, ← Pi.single_apply, ← this]
    rfl
  have h2 : Q * frame x y ι = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 h1
  have hsw := gram_swap σ hσ ε J hJ (frame x y ι)
  have hne : ε ≠ 0 := fun h0 => by simp [h0] at hε
  have col : ∀ i, (fun r => frame x y ι r (some (some i))) = ι *ᵥ Pi.single i 1 := fun i => by
    funext r
    simp [frame, Matrix.mulVec, dotProduct, Pi.single_apply]
  have e20 : ∀ i, ((frame x y ι)ᵀ * J * (frame x y ι).map σ) (some (some i)) none = 0 := fun i => by
    rw [gram_apply, col]; exact (horth _).1
  have e21 : ∀ i, ((frame x y ι)ᵀ * J * (frame x y ι).map σ) (some (some i)) (some none) = 0 := fun i => by
    rw [gram_apply, col]; exact (horth _).2
  have e01 : ((frame x y ι)ᵀ * J * (frame x y ι).map σ) none (some none) = 1 := by
    rw [gram_apply]; exact hxy
  have hG : (frame x y ι)ᵀ * J * (frame x y ι).map σ = gramM ε J₁ := by
    ext a b
    rcases a with _ | _ | a <;> rcases b with _ | _ | b
    · rw [gram_apply]; exact hxx
    · exact e01
    · have := hsw none (some (some b))
      rw [e20, map_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hne
    · have := hsw (some none) none
      rw [e01, map_one] at this
      show _ = ε
      linear_combination (-ε) * this - ((frame x y ι)ᵀ * J * (frame x y ι).map σ) (some none) none * hε
    · rw [gram_apply]; exact hyy
    · have := hsw (some none) (some (some b))
      rw [e21, map_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hne
    · exact e20 a
    · exact e21 a
    · show _ = J₁ a b
      rw [← hgram, gram_apply, gram_apply]; rfl
  have hGd : (gramM ε J₁).det ≠ 0 := by
    refine (Matrix.isUnit_det_of_left_inverse (B := Q.map σ * J⁻¹ * Qᵀ) ?_).ne_zero
    rw [← hG]
    calc Q.map σ * J⁻¹ * Qᵀ * ((frame x y ι)ᵀ * J * (frame x y ι).map σ)
        = Q.map σ * (J⁻¹ * ((frame x y ι * Q)ᵀ * J)) * (frame x y ι).map σ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), Matrix.mul_one,
            ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨Q, h1, h2, hG, hGd, fun h0 => ?_, fun i j => hG ▸ hsw i j⟩
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  refine hGd (Matrix.exists_vecMul_eq_zero_iff.1 ⟨vec3 0 0 v, fun h' => hv0 (funext fun i => congrFun h' (some (some i))), ?_⟩)
  funext b
  rcases b with _ | _ | b
  · simp [gramM, Matrix.vecMul, dotProduct, Fintype.sum_option]
  · simp [gramM, Matrix.vecMul, dotProduct, Fintype.sum_option]
  · simpa [gramM, Matrix.vecMul, dotProduct, Fintype.sum_option] using congrFun hv b

end Field

section Pair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hrk : Module.finrank F (Fin d → E) = 2 * d`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[h2, mul_comm]`. Set `β : Module.Basis (Fin (2 * d)) F (Fin d → E)` to `Module.finBasisOfFinrankEq F (Fin d → E) hrk`. Set `hnd` to `GlobalTheory.PairCoords.nondegenerate_pairBil σ hσ hdet`.

Set `β₂` to `(GlobalTheory.PairCoords.pairBil σ K).dualBasis hnd β`. Set `e` to `TensorProduct.piRight F (AF F) (AF F) (fun _ : Fin d => E)`. Establish `hinc : ∀ v : Fin d → E, e ((1 : AF F) ⊗ₜ[F] v) = incV F v` using `fun v => by`. Use function extensionality and compare the values at `i`. Both sides reduce to the same expression.

Set `B₁` to `(β.baseChange (AF F)).map e`. Set `B₂` to `(β₂.baseChange (AF F)).map e`. Establish `hB₁ : ∀ l, B₁ l = incV F (β l)` using `fun l => by`. Simplify using `only [B₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]`. Establish `hB₂ : ∀ l, B₂ l = incV F (β₂ l)` using `fun l => by`.

Simplify using `only [B₂, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]`. Establish `hk : ∀ k l, GlobalTheory.PairCoords.pairBil (cA σ) (incM F K) (B₂ k) (B₁ l) = if l = k then 1 else 0`. Introduce `k l`. Rewrite using `[hB₁, hB₂, GlobalTheory.PairCoords.pairBil_incV, LinearMap.BilinForm.apply_dualBasis_left]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h1 : ∀ a b, B₂.equivFun b ⬝ᵥ B₁.equivFun a = Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))`. Introduce `a b`. Rewrite using `[← GlobalTheory.PairCoords.pairBil_apply]`. Use `conv_rhs => rw [← B₂.sum_equivFun b, ← B₁.sum_equivFun a]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]`.

Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hrat : ∀ (b : Module.Basis (Fin (2 * d)) F (Fin d → E)) (a : Fin d → E), ((b.baseChange (AF F)).map e).equivFun (incV F a) = fun k => algebraMap F (AF F) (b.repr a k)`. Introduce `b a`. Use function extensionality and compare the values at `k`. Rewrite using `[← hinc, Module.Basis.equivFun_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]`.

Conclude with `⟨B₁.equivFun, B₂.equivFun, h1, fun a => ⟨_, hrat β a⟩, fun a => ⟨_, hrat β₂ a⟩⟩`.
-/
theorem exists_pair_fin (σ : E →ₐ[F] E) (d : ℕ) (K : Matrix (Fin d) (Fin d) E) (hσ : ∀ a, σ (σ a) = a)
    (h2 : Module.finrank F E = 2) (hdet : K.det ≠ 0) :
    ∃ p q : (Fin d → AE F E) ≃ₗ[AF F] (Fin (2 * d) → AF F),
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))) ∧
      (∀ a : Fin d → E, ∃ y : Fin (2 * d) → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin d → E, ∃ y : Fin (2 * d) → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  classical
  have hrk : Module.finrank F (Fin d → E) = 2 * d := by
    rw [Module.finrank_pi_fintype]
    simp [h2, mul_comm]
  let β : Module.Basis (Fin (2 * d)) F (Fin d → E) := Module.finBasisOfFinrankEq F (Fin d → E) hrk
  let hnd := GlobalTheory.PairCoords.nondegenerate_pairBil σ hσ hdet
  let β₂ := (GlobalTheory.PairCoords.pairBil σ K).dualBasis hnd β
  let e := TensorProduct.piRight F (AF F) (AF F) (fun _ : Fin d => E)
  have hinc : ∀ v : Fin d → E, e ((1 : AF F) ⊗ₜ[F] v) = incV F v := fun v => by
    funext i
    rfl
  let B₁ := (β.baseChange (AF F)).map e
  let B₂ := (β₂.baseChange (AF F)).map e
  have hB₁ : ∀ l, B₁ l = incV F (β l) := fun l => by
    simp only [B₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hB₂ : ∀ l, B₂ l = incV F (β₂ l) := fun l => by
    simp only [B₂, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hk : ∀ k l, GlobalTheory.PairCoords.pairBil (cA σ) (incM F K) (B₂ k) (B₁ l) = if l = k then 1 else 0 := by
    intro k l
    rw [hB₁, hB₂, GlobalTheory.PairCoords.pairBil_incV, LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have h1 : ∀ a b, B₂.equivFun b ⬝ᵥ B₁.equivFun a =
      Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l)) := by
    intro a b
    rw [← GlobalTheory.PairCoords.pairBil_apply]
    conv_rhs => rw [← B₂.sum_equivFun b, ← B₁.sum_equivFun a]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hrat : ∀ (b : Module.Basis (Fin (2 * d)) F (Fin d → E)) (a : Fin d → E),
      ((b.baseChange (AF F)).map e).equivFun (incV F a) = fun k => algebraMap F (AF F) (b.repr a k) := by
    intro b a
    funext k
    rw [← hinc, Module.Basis.equivFun_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]
  exact ⟨B₁.equivFun, B₂.equivFun, h1, fun a => ⟨_, hrat β a⟩, fun a => ⟨_, hrat β₂ a⟩⟩

/- English proof (translation)
Set `g : Fin d ≃ γ` to `(Fintype.equivFinOfCardEq hd).symm`. Take `⟨p, q, h1, hp, hq⟩` from `exists_pair_fin σ d (K.submatrix g g) hσ h2 (by rwa [Matrix.det_submatrix_equiv_self])`. Use `⟨LinearEquiv.funCongrLeft (AF F) (AE F E) g ≪≫ₗ p, LinearEquiv.funCongrLeft (AF F) (AE F E) g ≪≫ₗ q, fun a b => ?_, fun a => hp (a ∘ g), fun a => hq (a ∘ g)⟩` and prove the remaining obligations. Use `(h1 (a ∘ g) (b ∘ g)).trans ?_` and prove the remaining obligations. Use `congr 2`.

Rewrite using `[← g.sum_comp]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← g.sum_comp]`. Both sides reduce to the same expression.
-/
theorem exists_pair (σ : E →ₐ[F] E) {γ : Type} [Fintype γ] [DecidableEq γ] (d : ℕ) (hd : Fintype.card γ = d)
    (K : Matrix γ γ E) (hσ : ∀ a, σ (σ a) = a) (h2 : Module.finrank F E = 2) (hdet : K.det ≠ 0) :
    ∃ p q : (γ → AE F E) ≃ₗ[AF F] (Fin (2 * d) → AF F),
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))) ∧
      (∀ a : γ → E, ∃ y : Fin (2 * d) → F, p (fun i => inclR (F := F) (AF F) (a i)) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : γ → E, ∃ y : Fin (2 * d) → F,
        q (fun i => inclR (F := F) (AF F) (a i)) = fun k => algebraMap F (AF F) (y k)) := by
  let g : Fin d ≃ γ := (Fintype.equivFinOfCardEq hd).symm
  obtain ⟨p, q, h1, hp, hq⟩ := exists_pair_fin σ d (K.submatrix g g) hσ h2 (by rwa [Matrix.det_submatrix_equiv_self])
  refine ⟨LinearEquiv.funCongrLeft (AF F) (AE F E) g ≪≫ₗ p, LinearEquiv.funCongrLeft (AF F) (AE F E) g ≪≫ₗ q,
    fun a b => ?_, fun a => hp (a ∘ g), fun a => hq (a ∘ g)⟩
  refine (h1 (a ∘ g) (b ∘ g)).trans ?_
  congr 2
  rw [← g.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← g.sum_comp]
  rfl

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E))`. Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Establish `hle : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.range (frame H.x H.y H.ι).mulVecLin`. Rewrite using `[Submodule.span_le]`.

Introduce `z hz`. Take `⟨s, t, u, -, -, -, h⟩` from `hH.split z hz`. Conclude with `⟨vec3 s t u, (frame_mulVec _ _ _ s t u).trans h.symm⟩`. Take `⟨c, hc⟩` from `hle hv`. Use `⟨c none, c (some none), fun i => c (some (some i)), ?_⟩` and prove the remaining obligations.

Rewrite using `[← frame_mulVec, ← hc, Matrix.mulVecLin_apply]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `rcases a with _ | _ | a <;> rfl`.
-/
theorem span_of_adapted {σ : E →ₐ[F] E} {B : Base F E} {n n₁ i₀ i₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n}
    {Y₁ : Spc F E n₁} (hL : Y.L.IsLattice E) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (v : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  have hle : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.range (frame H.x H.y H.ι).mulVecLin := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨vec3 s t u, (frame_mulVec _ _ _ s t u).trans h.symm⟩
  obtain ⟨c, hc⟩ := hle hv
  refine ⟨c none, c (some none), fun i => c (some (some i)), ?_⟩
  rw [← frame_mulVec, ← hc, Matrix.mulVecLin_apply]
  congr 1
  funext a
  rcases a with _ | _ | a <;> rfl

end Pair

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M₁ hB hX hW hH hH' hM₁`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hσ : ∀ x, σ (σ x) = x` using `fun x => by`. Apply `((B.emb w).1 : E →+* ℂ).injective` to reduce the goal to its premises. Rewrite using `[hB.cm.2.2.2, hB.cm.2.2.2, star_star]`.

Establish `hX' : X.J.det ≠ 0` using `fun h0 => by`. Apply `GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)` to reduce the goal to its premises. Use `((B.emb w).1 : E →+* ℂ).map_det X.J` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `this.symm`.

Establish `hW' : W.J.det ≠ 0` using `fun h0 => by`. Apply `GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hW.cartan w)` to reduce the goal to its premises. Use `((B.emb w).1 : E →+* ℂ).map_det W.J` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Rewrite using `[Matrix.det_smul]`.

Conclude with `mul_eq_zero_of_right _ this.symm`. Take `⟨Q, h1, h2, hG, hGd, -, hGs⟩` from `frame_spec σ hσ 1 (one_mul 1) X.J (fun i j => by rw [one_mul, hX.herm]) hX' hH.rank H.x H.y H.ι X₁.J hH.xx hH.yy hH.xy hH.orth hH.gram (span_of_adapted hX.lat hH)`. Take `⟨Q', h1', h2', hG', -, hKd, hKs⟩` from `frame_spec σ hσ (-1) (by ring) W.J (fun i j => by rw [neg_one_mul, hW.skew]) hW' hH'.rank H'.x H'.y H'.ι W₁.J hH'.xx hH'.yy hH'.xy hH'.orth hH'.gram (span_of_adapted hW.lat hH')`. Take `⟨p, q, hpq, hp, hq⟩` from `exists_pair σ (n + d₁) (by simp [hH.rank]) (Matrix.fromBlocks (-gramM 1 X₁.J) 0 0 W₁.J) hσ hB.cm.2.2.1 (by`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]`.

Conclude with `mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hGd) hKd)`. Set `eq : Fin n × Fin d ≃ Fin (2 * (n + d₁)) ⊕ (Fin n₁ × Fin d₁)` to `Fintype.equivOfCardEq (by`. Simplify using `only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]`. Rewrite using `[hH.rank, hH'.rank]`. Use the proof step `ring)`.

Establish `hinc : ∀ {a b c : Type} [Fintype b] (U : Matrix a b E) (V : Matrix b c E), incM F (U * V) = incM F U * incM F V` using `fun U V => Matrix.map_mul`. Establish `hinc1 : ∀ {a : Type} [DecidableEq a], incM F (1 : Matrix a a E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hc : ∀ e : E, cA σ (inclR (F` using `F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl`. Use `set P : Matrix (Fin n) (Ix n₁) (AE F E) := frame (incV F H.x) (incV F H.y) (incM F H.ι) with hPdef`. Use `set P' : Matrix (Fin d) (Ix d₁) (AE F E) := frame (incV F H'.x) (incV F H'.y) (incM F H'.ι) with hPdef'`.

Establish `hP : incM F (frame H.x H.y H.ι) = P` using `frame_map _ _ _ _`. Establish `hP' : incM F (frame H'.x H'.y H'.ι) = P'` using `frame_map _ _ _ _`. Establish `k1 : P * incM F Q = 1` using `by rw [← hP, ← hinc, h1, hinc1]`. Establish `k2 : incM F Q * P = 1` using `by rw [← hP, ← hinc, h2, hinc1]`. Establish `k1' : P' * incM F Q' = 1` using `by rw [← hP', ← hinc, h1', hinc1]`.

Establish `k2' : incM F Q' * P' = 1` using `by rw [← hP', ← hinc, h2', hinc1]`. Establish `g1 : incM F (gramM 1 X₁.J) = gramM 1 (incM F X₁.J)`. Rewrite using `[incM, gramM_map, map_one]`. Both sides reduce to the same expression. Establish `g2 : incM F (gramM (-1) W₁.J) = gramM (-1) (incM F W₁.J)`.

Rewrite using `[incM, gramM_map, map_neg, map_one]`. Both sides reduce to the same expression. Establish `kG : Pᵀ * incM F X.J * P.map (cA σ) = gramM 1 (incM F X₁.J)`. Rewrite using `[← g1, ← hG, hinc, hinc, ← hP]`. Both sides reduce to the same expression.

Establish `kG' : P'ᵀ * incM F W.J * P'.map (cA σ) = gramM (-1) (incM F W₁.J)`. Rewrite using `[← g2, ← hG', hinc, hinc, ← hP']`. Both sides reduce to the same expression. Establish `kB : incM F (Matrix.fromBlocks (-gramM 1 X₁.J) 0 0 W₁.J) = Matrix.fromBlocks (-gramM 1 (incM F X₁.J)) 0 0 (incM F W₁.J)`. Rewrite using `[← g1]`.

Apply the tactic sequence `ext (i | i) (j | j) <;> simp [incM]`. Set `D` to `conj (R := AF F) P (incM F Q) P' (incM F Q') k1 k2 k1' k2'`. Establish `hD : ∀ u, D u = incM F Q * u * (incM F Q')ᵀ` using `fun _ => rfl`. Establish `hDs : ∀ Z, D.symm Z = P * Z * P'ᵀ` using `fun _ => rfl`. Set `e` to `D ≪≫ₗ shuffle (AF F) ≪≫ₗ glue eq p q M₁.co.e`.

Establish `he : ∀ u, e u = (fun k => Sum.elim (q (pos (D u))) (M₁.co.e (core (D u))).1 (eq k), fun k => Sum.elim (p (mom (D u))) (M₁.co.e (core (D u))).2 (eq k))` using `fun _ => rfl`. Take `⟨qx, qy, qι⟩` from `inv_frame k2`. Take `⟨qx', qy', qι'⟩` from `inv_frame k2'`. Establish `hA : ∀ u, pos (D u) = 0 → core (D u) = 0 → (e u).1 = 0 ∧ ∀ j, (e u).2 (eq.symm (Sum.inr j)) = 0`. Introduce `u ha hb`.

Rewrite using `[he, ha, hb, map_zero, map_zero]`. Use `⟨funext fun k => ?_, fun j => by simp⟩` and prove the remaining obligations. Use `show Sum.elim _ _ (eq k) = _`. Apply the tactic sequence `cases eq k <;> rfl`. Establish `hAd : ∀ u, mom (D u) = 0 → core (D u) = 0 → (e u).2 = 0 ∧ ∀ j, (e u).1 (eq.symm (Sum.inr j)) = 0`.

Introduce `u ha hb`. Rewrite using `[he, ha, hb, map_zero, map_zero]`. Use `⟨funext fun k => ?_, fun j => by simp⟩` and prove the remaining obligations. Use `show Sum.elim _ _ (eq k) = _`. Apply the tactic sequence `cases eq k <;> rfl`.

Use `⟨⟨e, fun u u' => ?_⟩, eq, fun x => ?_, fun z => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he, he]`. Simplify using `only []`. Rewrite using `[dot_elim, dot_elim, hpq, hpq, kB]`. Use `conv_lhs => rw [← D.symm_apply_apply u, ← D.symm_apply_apply u', hDs, hDs, symp, hTens_mul_right, kG', ← symp, symp_mul_left, kG]`.

Rewrite using `[symp_gramM (cA σ) (GlobalTheory.PairCoords.cA_cA σ hσ) _ _ (fun i j => ?_) (fun i j => ?_), M₁.co.form]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← g1] show cA σ (inclR (F := F) (AF F) _) = inclR (F := F) (AF F) _`. Rewrite using `[hc, hGs, one_mul]`. Use `show cA σ (inclR (F := F) (AF F) _) = -inclR (F := F) (AF F) _`.

Use `hKs (some (some i)) (some (some j))` as an intermediate fact. Rewrite `this` using `[neg_one_mul]`. Rewrite using `[hc, ← map_neg]`. Conclude with `congrArg _ this`. Use `show ∃ y z : Fin n × Fin d → F, e _ = _`.

Establish `hx : D (incM F x) = incM F (Q * x * Q'ᵀ)` using `by rw [hD, hinc, hinc]; rfl`. Take `⟨y₁, z₁, hM⟩` from `hM₁.rat (core (Q * x * Q'ᵀ))`. Take `⟨a, ha⟩` from `hq (pos (Q * x * Q'ᵀ))`. Take `⟨b, hb⟩` from `hp (mom (Q * x * Q'ᵀ))`. Use `⟨fun k => Sum.elim a y₁ (eq k), fun k => Sum.elim b z₁ (eq k), ?_⟩` and prove the remaining obligations.

Establish `e1 : pos (incM F (Q * x * Q'ᵀ)) = fun i => inclR (F` using `F) (AF F) (pos (Q * x * Q'ᵀ) i) := by`. Apply the tactic sequence `funext k; rcases k with k | k <;> rfl`. Establish `e2 : mom (incM F (Q * x * Q'ᵀ)) = fun i => inclR (F` using `F) (AF F) (mom (Q * x * Q'ᵀ) i) := by`. Apply the tactic sequence `funext k; rcases k with k | k <;> rfl`. Establish `e3 : core (incM F (Q * x * Q'ᵀ)) = incM F (core (Q * x * Q'ᵀ))` using `rfl`.

Rewrite using `[he, hx, e1, e2, e3, ha, hb, hM]`. Use `Prod.ext (funext fun k => ?_) (funext fun k => ?_)` and prove the remaining obligations. Use `show Sum.elim _ _ (eq k) = algebraMap F (AF F) (Sum.elim _ _ (eq k))`. Apply the tactic sequence `cases eq k <;> rfl`. Use `show Sum.elim _ _ (eq k) = algebraMap F (AF F) (Sum.elim _ _ (eq k))`.

Apply the tactic sequence `cases eq k <;> rfl`. Use `show e _ = _`. Establish `hz : D (incM F H.ι * z * (incM F H'.ι)ᵀ) = embM z`. Rewrite using `[← frame_embM (incV F H.x) (incV F H.y) _ (incV F H'.x) (incV F H'.y), ← hDs, D.apply_symm_apply]`. Establish `e1 : pos (embM z) = 0`.

Apply the tactic sequence `funext k; rcases k with (_ | _ | k) | k <;> rfl`. Establish `e2 : mom (embM z) = 0`. Apply the tactic sequence `funext k; rcases k with (_ | _ | k) | k <;> rfl`. Establish `e3 : core (embM z) = z` using `rfl`. Rewrite using `[he, hz, e1, e2, e3, map_zero, map_zero]`.

Both sides reduce to the same expression. Introduce and unpack `u (⟨y, rfl⟩ | ⟨z, rfl⟩)`. Use `hA _ ?_ ?_` and prove the remaining obligations. Rewrite using `[hD, mul_vecMulVec_mul, qx']`. Apply the tactic sequence `funext k; rcases k with k | k <;> simp [pos, Matrix.vecMulVec_apply]`.

Rewrite using `[hD, mul_vecMulVec_mul, qx']`. Use extensionality with `i j`. Simplify using `[core, Matrix.vecMulVec_apply]`. Use `hA _ ?_ ?_` and prove the remaining obligations. Rewrite using `[hD, mul_vecMulVec_mul, qx, qι']`.

Apply the tactic sequence `funext k; rcases k with k | k <;> simp [pos, Matrix.vecMulVec_apply]`. Rewrite using `[hD, mul_vecMulVec_mul, qx, qι']`. Use extensionality with `i j`. Simplify using `[core, Matrix.vecMulVec_apply]`. Introduce and unpack `u (⟨y, rfl⟩ | ⟨z, rfl⟩)`.

Use `hAd _ ?_ ?_` and prove the remaining obligations. Rewrite using `[hD, mul_vecMulVec_mul, qy']`. Apply the tactic sequence `funext k; rcases k with k | k <;> simp [mom, Matrix.vecMulVec_apply]`. Rewrite using `[hD, mul_vecMulVec_mul, qy']`. Use extensionality with `i j`.

Simplify using `[core, Matrix.vecMulVec_apply]`. Use `hAd _ ?_ ?_` and prove the remaining obligations. Rewrite using `[hD, mul_vecMulVec_mul, qy, qι']`. Apply the tactic sequence `funext k; rcases k with k | k <;> simp [mom, Matrix.vecMulVec_apply]`. Rewrite using `[hD, mul_vecMulVec_mul, qy, qι']`.

Use extensionality with `i j`. Simplify using `[core, Matrix.vecMulVec_apply]`.
-/
theorem exists_adapted_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
      (eq : Fin n × Fin d ≃ Fin (2 * (n + d₁)) ⊕ (Fin n₁ × Fin d₁)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ z, co.e (incM F H.ι * z * (incM F H'.ι)ᵀ) = (ext0 eq (M₁.co.e z).1, ext0 eq (M₁.co.e z).2)) ∧
      (∀ u ∈ isoA H H', (co.e u).1 = 0 ∧ ∀ j, (co.e u).2 (eq.symm (Sum.inr j)) = 0) ∧
      ∀ u ∈ isoAd H H', (co.e u).2 = 0 ∧ ∀ j, (co.e u).1 (eq.symm (Sum.inr j)) = 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M₁ hB hX hW hH hH' hM₁
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hX' : X.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hW' : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hW.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  obtain ⟨Q, h1, h2, hG, hGd, -, hGs⟩ := frame_spec σ hσ 1 (one_mul 1) X.J (fun i j => by rw [one_mul, hX.herm]) hX'
    hH.rank H.x H.y H.ι X₁.J hH.xx hH.yy hH.xy hH.orth hH.gram (span_of_adapted hX.lat hH)
  obtain ⟨Q', h1', h2', hG', -, hKd, hKs⟩ := frame_spec σ hσ (-1) (by ring) W.J (fun i j => by rw [neg_one_mul, hW.skew]) hW'
    hH'.rank H'.x H'.y H'.ι W₁.J hH'.xx hH'.yy hH'.xy hH'.orth hH'.gram (span_of_adapted hW.lat hH')
  obtain ⟨p, q, hpq, hp, hq⟩ := exists_pair σ (n + d₁) (by simp [hH.rank])
    (Matrix.fromBlocks (-gramM 1 X₁.J) 0 0 W₁.J) hσ hB.cm.2.2.1 (by
      rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hGd) hKd)
  let eq : Fin n × Fin d ≃ Fin (2 * (n + d₁)) ⊕ (Fin n₁ × Fin d₁) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
    rw [hH.rank, hH'.rank]; ring)
  have hinc : ∀ {a b c : Type} [Fintype b] (U : Matrix a b E) (V : Matrix b c E),
      incM F (U * V) = incM F U * incM F V := fun U V => Matrix.map_mul
  have hinc1 : ∀ {a : Type} [DecidableEq a], incM F (1 : Matrix a a E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  set P : Matrix (Fin n) (Ix n₁) (AE F E) := frame (incV F H.x) (incV F H.y) (incM F H.ι) with hPdef
  set P' : Matrix (Fin d) (Ix d₁) (AE F E) := frame (incV F H'.x) (incV F H'.y) (incM F H'.ι) with hPdef'
  have hP : incM F (frame H.x H.y H.ι) = P := frame_map _ _ _ _
  have hP' : incM F (frame H'.x H'.y H'.ι) = P' := frame_map _ _ _ _
  have k1 : P * incM F Q = 1 := by rw [← hP, ← hinc, h1, hinc1]
  have k2 : incM F Q * P = 1 := by rw [← hP, ← hinc, h2, hinc1]
  have k1' : P' * incM F Q' = 1 := by rw [← hP', ← hinc, h1', hinc1]
  have k2' : incM F Q' * P' = 1 := by rw [← hP', ← hinc, h2', hinc1]
  have g1 : incM F (gramM 1 X₁.J) = gramM 1 (incM F X₁.J) := by
    rw [incM, gramM_map, map_one]; rfl
  have g2 : incM F (gramM (-1) W₁.J) = gramM (-1) (incM F W₁.J) := by
    rw [incM, gramM_map, map_neg, map_one]; rfl
  have kG : Pᵀ * incM F X.J * P.map (cA σ) = gramM 1 (incM F X₁.J) := by
    rw [← g1, ← hG, hinc, hinc, ← hP]; rfl
  have kG' : P'ᵀ * incM F W.J * P'.map (cA σ) = gramM (-1) (incM F W₁.J) := by
    rw [← g2, ← hG', hinc, hinc, ← hP']; rfl
  have kB : incM F (Matrix.fromBlocks (-gramM 1 X₁.J) 0 0 W₁.J) =
      Matrix.fromBlocks (-gramM 1 (incM F X₁.J)) 0 0 (incM F W₁.J) := by
    rw [← g1]
    ext (i | i) (j | j) <;> simp [incM]
  let D := conj (R := AF F) P (incM F Q) P' (incM F Q') k1 k2 k1' k2'
  have hD : ∀ u, D u = incM F Q * u * (incM F Q')ᵀ := fun _ => rfl
  have hDs : ∀ Z, D.symm Z = P * Z * P'ᵀ := fun _ => rfl
  let e := D ≪≫ₗ shuffle (AF F) ≪≫ₗ glue eq p q M₁.co.e
  have he : ∀ u, e u = (fun k => Sum.elim (q (pos (D u))) (M₁.co.e (core (D u))).1 (eq k),
      fun k => Sum.elim (p (mom (D u))) (M₁.co.e (core (D u))).2 (eq k)) := fun _ => rfl
  obtain ⟨qx, qy, qι⟩ := inv_frame k2
  obtain ⟨qx', qy', qι'⟩ := inv_frame k2'
  have hA : ∀ u, pos (D u) = 0 → core (D u) = 0 → (e u).1 = 0 ∧ ∀ j, (e u).2 (eq.symm (Sum.inr j)) = 0 := by
    intro u ha hb
    rw [he, ha, hb, map_zero, map_zero]
    refine ⟨funext fun k => ?_, fun j => by simp⟩
    show Sum.elim _ _ (eq k) = _
    cases eq k <;> rfl
  have hAd : ∀ u, mom (D u) = 0 → core (D u) = 0 → (e u).2 = 0 ∧ ∀ j, (e u).1 (eq.symm (Sum.inr j)) = 0 := by
    intro u ha hb
    rw [he, ha, hb, map_zero, map_zero]
    refine ⟨funext fun k => ?_, fun j => by simp⟩
    show Sum.elim _ _ (eq k) = _
    cases eq k <;> rfl
  refine ⟨⟨e, fun u u' => ?_⟩, eq, fun x => ?_, fun z => ?_, ?_, ?_⟩
  · rw [he, he]
    simp only []
    rw [dot_elim, dot_elim, hpq, hpq, kB]
    conv_lhs => rw [← D.symm_apply_apply u, ← D.symm_apply_apply u', hDs, hDs, symp, hTens_mul_right, kG', ← symp,
      symp_mul_left, kG]
    rw [symp_gramM (cA σ) (GlobalTheory.PairCoords.cA_cA σ hσ) _ _ (fun i j => ?_) (fun i j => ?_), M₁.co.form]
    · ring
    · rw [← g1]
      show cA σ (inclR (F := F) (AF F) _) = inclR (F := F) (AF F) _
      rw [hc, hGs, one_mul]
    · show cA σ (inclR (F := F) (AF F) _) = -inclR (F := F) (AF F) _
      have := hKs (some (some i)) (some (some j))
      rw [neg_one_mul] at this
      rw [hc, ← map_neg]
      exact congrArg _ this
  · show ∃ y z : Fin n × Fin d → F, e _ = _
    have hx : D (incM F x) = incM F (Q * x * Q'ᵀ) := by rw [hD, hinc, hinc]; rfl
    obtain ⟨y₁, z₁, hM⟩ := hM₁.rat (core (Q * x * Q'ᵀ))
    obtain ⟨a, ha⟩ := hq (pos (Q * x * Q'ᵀ))
    obtain ⟨b, hb⟩ := hp (mom (Q * x * Q'ᵀ))
    refine ⟨fun k => Sum.elim a y₁ (eq k), fun k => Sum.elim b z₁ (eq k), ?_⟩
    have e1 : pos (incM F (Q * x * Q'ᵀ)) = fun i => inclR (F := F) (AF F) (pos (Q * x * Q'ᵀ) i) := by
      funext k; rcases k with k | k <;> rfl
    have e2 : mom (incM F (Q * x * Q'ᵀ)) = fun i => inclR (F := F) (AF F) (mom (Q * x * Q'ᵀ) i) := by
      funext k; rcases k with k | k <;> rfl
    have e3 : core (incM F (Q * x * Q'ᵀ)) = incM F (core (Q * x * Q'ᵀ)) := rfl
    rw [he, hx, e1, e2, e3, ha, hb, hM]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show Sum.elim _ _ (eq k) = algebraMap F (AF F) (Sum.elim _ _ (eq k))
      cases eq k <;> rfl
    · show Sum.elim _ _ (eq k) = algebraMap F (AF F) (Sum.elim _ _ (eq k))
      cases eq k <;> rfl
  · show e _ = _
    have hz : D (incM F H.ι * z * (incM F H'.ι)ᵀ) = embM z := by
      rw [← frame_embM (incV F H.x) (incV F H.y) _ (incV F H'.x) (incV F H'.y), ← hDs, D.apply_symm_apply]
    have e1 : pos (embM z) = 0 := by
      funext k; rcases k with (_ | _ | k) | k <;> rfl
    have e2 : mom (embM z) = 0 := by
      funext k; rcases k with (_ | _ | k) | k <;> rfl
    have e3 : core (embM z) = z := rfl
    rw [he, hz, e1, e2, e3, map_zero, map_zero]
    rfl
  · rintro u (⟨y, rfl⟩ | ⟨z, rfl⟩)
    · refine hA _ ?_ ?_
      · rw [hD, mul_vecMulVec_mul, qx']
        funext k; rcases k with k | k <;> simp [pos, Matrix.vecMulVec_apply]
      · rw [hD, mul_vecMulVec_mul, qx']
        ext i j; simp [core, Matrix.vecMulVec_apply]
    · refine hA _ ?_ ?_
      · rw [hD, mul_vecMulVec_mul, qx, qι']
        funext k; rcases k with k | k <;> simp [pos, Matrix.vecMulVec_apply]
      · rw [hD, mul_vecMulVec_mul, qx, qι']
        ext i j; simp [core, Matrix.vecMulVec_apply]
  · rintro u (⟨y, rfl⟩ | ⟨z, rfl⟩)
    · refine hAd _ ?_ ?_
      · rw [hD, mul_vecMulVec_mul, qy']
        funext k; rcases k with k | k <;> simp [mom, Matrix.vecMulVec_apply]
      · rw [hD, mul_vecMulVec_mul, qy']
        ext i j; simp [core, Matrix.vecMulVec_apply]
    · refine hAd _ ?_ ?_
      · rw [hD, mul_vecMulVec_mul, qy, qι']
        funext k; rcases k with k | k <;> simp [mom, Matrix.vecMulVec_apply]
      · rw [hD, mul_vecMulVec_mul, qy, qι']
        ext i j; simp [core, Matrix.vecMulVec_apply]

end GlobalTheory.TwoPlanes
