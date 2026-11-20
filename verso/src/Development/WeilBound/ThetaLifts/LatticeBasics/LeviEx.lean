import Development.WeilBound.ThetaLifts.LatticeBasics.SchToPol

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

/- English proof (translation)
Establish `mm : ∀ {a b e : Type} [Fintype b] (A : Matrix a b R) (B : Matrix b e R), (A * B).map c = A.map c * B.map c` using `fun A B => Matrix.map_mul (f := c.toRingHom)`. Establish `u : ∀ A B : Matrix k k R, A * B = 1 → P * A * Q * (P * B * Q) = 1` using `fun A B e => by`. Rewrite using `[show P * A * Q * (P * B * Q) = P * (A * (Q * P) * B) * Q by simp only [Matrix.mul_assoc], h2, mul_one, e, Matrix.mul_one, h1]`. Use `⟨⟨⟨P * D * Q, P * D' * Q, u _ _ h3, u _ _ h4⟩, ?_⟩, by simp only [Matrix.mul_assoc, h2, Matrix.mul_one]⟩` and prove the remaining obligations. Use `show (P * D * Q)ᵀ * J * (P * D * Q).map c = J`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_conj {S R : Type} [CommRing S] [CommRing R] [Algebra S R] (c : R →ₐ[S] R) {n k : Type} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] (J : Matrix n n R) (P : Matrix n k R) (Q : Matrix k n R) (h1 : P * Q = 1) (h2 : Q * P = 1)
    (D D' : Matrix k k R) (h3 : D * D' = 1) (h4 : D' * D = 1) (h : Dᵀ * (Pᵀ * J * P.map c) * D.map c = Pᵀ * J * P.map c) :
    ∃ g : UG c J, g.1.1 * P = P * D := by
  have mm : ∀ {a b e : Type} [Fintype b] (A : Matrix a b R) (B : Matrix b e R), (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := c.toRingHom)
  have u : ∀ A B : Matrix k k R, A * B = 1 → P * A * Q * (P * B * Q) = 1 := fun A B e => by
    rw [show P * A * Q * (P * B * Q) = P * (A * (Q * P) * B) * Q by simp only [Matrix.mul_assoc], h2, mul_one, e,
      Matrix.mul_one, h1]
  refine ⟨⟨⟨P * D * Q, P * D' * Q, u _ _ h3, u _ _ h4⟩, ?_⟩, by simp only [Matrix.mul_assoc, h2, Matrix.mul_one]⟩
  show (P * D * Q)ᵀ * J * (P * D * Q).map c = J
  calc _ = Qᵀ * (Dᵀ * (Pᵀ * J * P.map c) * D.map c) * Q.map c := by simp only [mm, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (P * Q)ᵀ * J * (P * Q).map c := by rw [h]; simp only [mm, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = J := by rw [h1, Matrix.map_one _ (map_zero c) (map_one c)]; simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in
/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem incM_mul {a b e : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b e E) : incM F (A * B) = incM F A * incM F B :=
  Matrix.map_mul

omit [NumberField E] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, cA, inclR]`.
-/
theorem incM_conj {a b : Type} (A : Matrix a b E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j
  simp [incM, cA, inclR]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d d₁ W W₁ H i₀ i₁ r s hB hW hH h₁`. Establish `inv : ∀ x, σ (σ x) = x` using `fun x => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`. Set `N : Matrix (Fin d) (Fin 2) E` to `(Matrix.of ![H.x, H.y])ᵀ`.

Set `P` to `Matrix.fromCols H.ι N`. Establish `su : Function.Surjective P.mulVec` using `fun z => by`. Establish `hz : z ∈ Submodule.span E (W.L : Set (Fin d → E))` using `hW.lat.span_eq_top ▸ Submodule.mem_top`. Use `(Submodule.span_le (p := LinearMap.range P.mulVecLin)).2 (fun z hz => ?_) hz` and prove the remaining obligations. Take `⟨a, b, u, -, -, -, rfl⟩` from `hH.split z hz`.

Use `⟨Sum.elim u ![a, b], ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[P, N, Matrix.mulVec, dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨Q, h1⟩` from `Matrix.mulVec_surjective_iff_exists_right_inverse.1 su`.

Establish `h2 : Q * P = 1` using `(Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp [hH.rank]))).1 h1`. Establish `o1 : H.ιᵀ * W.J * N.map σ = 0`. Use extensionality with `i j`. Use `hH.orth (Pi.single i 1)` as an intermediate fact. Rewrite using `[Matrix.mul_assoc]`.

Use `fin_cases j`. Simplify `this.1` using `[form, N, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply]`. Simplify `this.2` using `[form, N, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `o2 : Nᵀ * W.J * H.ι.map σ = 0`. Use extensionality with `j i`.

Use `congrArg σ (congrFun (congrFun o1 i) j)` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, inv, hW.skew, Matrix.zero_apply, map_zero, Finset.sum_mul] at this ⊢`. Rewrite using `[Finset.sum_comm, ← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`.

Conclude with `Finset.sum_congr rfl fun b _ => by ring`. Establish `gr : Pᵀ * W.J * P.map σ = Matrix.fromBlocks W₁.J 0 0 (Nᵀ * W.J * N.map σ)`. Rewrite using `[← hH.gram, ← o1]`. Use `conv_rhs => enter [3]`. Rewrite using `[← o2]`.

Simplify using `only [P]`. Rewrite using `[Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromCols_map, Matrix.fromRows_mul_fromCols]`. Establish `one : ∀ {k : Type} [DecidableEq k], incM F (1 : Matrix k k E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `gr' : (incM F P)ᵀ * incM F W.J * (incM F P).map (cA σ) = Matrix.fromBlocks (incM F W₁.J) 0 0 (incM F (Nᵀ * W.J * N.map σ))`. Rewrite using `[incM_conj, show (incM F P)ᵀ = incM F Pᵀ from rfl, ← incM_mul, ← incM_mul, gr, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]`.

Both sides reduce to the same expression. Take `⟨m, hm⟩` from `exists_conj (cA σ) (incM F W.J) (incM F P) (incM F Q) (by rw [← incM_mul, h1, one]) (by rw [← incM_mul, h2, one]) (Matrix.fromBlocks (mat h₁) 0 0 1) (Matrix.fromBlocks (h₁.1⁻¹).1 0 0 1) (by simp [Matrix.fromBlocks_multiply, mat]) (by simp [Matrix.fromBlocks_multiply, mat]) (by`. Establish `e : (mat h₁)ᵀ * incM F W₁.J * (mat h₁).map (cA σ) = incM F W₁.J` using `h₁.2`. Rewrite using `[gr', Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]`. Simplify using `[Matrix.fromBlocks_multiply, e])`.

Rewrite `hm` using `[show incM F P = Matrix.fromCols (incM F H.ι) (incM F N) from Matrix.fromCols_map _ _ _, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_ext_iff]`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add] at hm`. Use `⟨m, ?_, ?_, hm.1⟩` and prove the remaining obligations. Rewrite using `[Units.val_one, one_smul]`. Conclude with `funext fun i => congrFun (congrFun hm.2 i) 0`.

Rewrite using `[inv_one, Units.val_one, map_one, one_smul]`. Conclude with `funext fun i => congrFun (congrFun hm.2 i) 1`.
-/
theorem leviEx : LeviEx := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H i₀ i₁ r s hB hW hH h₁
  have inv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  let N : Matrix (Fin d) (Fin 2) E := (Matrix.of ![H.x, H.y])ᵀ
  let P := Matrix.fromCols H.ι N
  have su : Function.Surjective P.mulVec := fun z => by
    have hz : z ∈ Submodule.span E (W.L : Set (Fin d → E)) := hW.lat.span_eq_top ▸ Submodule.mem_top
    refine (Submodule.span_le (p := LinearMap.range P.mulVecLin)).2 (fun z hz => ?_) hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hH.split z hz
    refine ⟨Sum.elim u ![a, b], ?_⟩
    ext i
    simp [P, N, Matrix.mulVec, dotProduct]
    ring
  obtain ⟨Q, h1⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 su
  have h2 : Q * P = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp [hH.rank]))).1 h1
  have o1 : H.ιᵀ * W.J * N.map σ = 0 := by
    ext i j
    have := hH.orth (Pi.single i 1)
    rw [Matrix.mul_assoc]
    fin_cases j
    · simpa [form, N, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this.1
    · simpa [form, N, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this.2
  have o2 : Nᵀ * W.J * H.ι.map σ = 0 := by
    ext j i
    have := congrArg σ (congrFun (congrFun o1 i) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, inv, hW.skew, Matrix.zero_apply,
      map_zero, Finset.sum_mul] at this ⊢
    rw [Finset.sum_comm, ← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have gr : Pᵀ * W.J * P.map σ = Matrix.fromBlocks W₁.J 0 0 (Nᵀ * W.J * N.map σ) := by
    rw [← hH.gram, ← o1]
    conv_rhs => enter [3]; rw [← o2]
    simp only [P]
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromCols_map, Matrix.fromRows_mul_fromCols]
  have one : ∀ {k : Type} [DecidableEq k], incM F (1 : Matrix k k E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have gr' : (incM F P)ᵀ * incM F W.J * (incM F P).map (cA σ) =
      Matrix.fromBlocks (incM F W₁.J) 0 0 (incM F (Nᵀ * W.J * N.map σ)) := by
    rw [incM_conj, show (incM F P)ᵀ = incM F Pᵀ from rfl, ← incM_mul, ← incM_mul, gr, incM, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    rfl
  obtain ⟨m, hm⟩ := exists_conj (cA σ) (incM F W.J) (incM F P) (incM F Q) (by rw [← incM_mul, h1, one])
    (by rw [← incM_mul, h2, one]) (Matrix.fromBlocks (mat h₁) 0 0 1) (Matrix.fromBlocks (h₁.1⁻¹).1 0 0 1)
    (by simp [Matrix.fromBlocks_multiply, mat]) (by simp [Matrix.fromBlocks_multiply, mat]) (by
      have e : (mat h₁)ᵀ * incM F W₁.J * (mat h₁).map (cA σ) = incM F W₁.J := h₁.2
      rw [gr', Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
      simp [Matrix.fromBlocks_multiply, e])
  rw [show incM F P = Matrix.fromCols (incM F H.ι) (incM F N) from Matrix.fromCols_map _ _ _, Matrix.mul_fromCols,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_ext_iff] at hm
  simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add] at hm
  refine ⟨m, ?_, ?_, hm.1⟩
  · rw [Units.val_one, one_smul]
    exact funext fun i => congrFun (congrFun hm.2 i) 0
  · rw [inv_one, Units.val_one, map_one, one_smul]
    exact funext fun i => congrFun (congrFun hm.2 i) 1

end GlobalTheory.ThK.Dbl

end
