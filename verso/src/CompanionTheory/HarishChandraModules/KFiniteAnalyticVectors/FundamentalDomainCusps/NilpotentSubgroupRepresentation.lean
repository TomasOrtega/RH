import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.NilpAlg

open Matrix

noncomputable section

namespace CompanionTheory.D.gk.RF

variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}

omit [StarRing K] in
/- English proof (translation)
The claim follows from `Matrix.ext fun i j => by simpa using congrFun (h (Pi.single j 1)) i`.
-/
theorem mat_extC {A B : Matrix (Fin n) (Fin n) K} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B :=
  Matrix.ext fun i j => by simpa using congrFun (h (Pi.single j 1)) i

/- English proof (translation)
The claim follows from `mat_extC fun z => by rw [← mulVec_mulVec, ← mulVec_mulVec, hA.1 _ (hB.2.1 _ (hC.2.2 z)), zero_mulVec]`.
-/
theorem Lowers.triple {A B C : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B)
    (hC : Lowers J W C) : A * (B * C) = 0 :=
  mat_extC fun z => by rw [← mulVec_mulVec, ← mulVec_mulVec, hA.1 _ (hB.2.1 _ (hC.2.2 z)), zero_mulVec]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w hw => by rw [add_mulVec, hA.1 w hw, hB.1 w hw, add_zero], fun z hz => by rw [add_mulVec]; exact W.add_mem (hA.2.1 z hz) (hB.2.1 z hz), fun z => by rw [add_mulVec]; exact (perp J W).add_mem (hA.2.2 z) (hB.2.2 z)⟩`.
-/
theorem Lowers.add {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) : Lowers J W (A + B) :=
  ⟨fun w hw => by rw [add_mulVec, hA.1 w hw, hB.1 w hw, add_zero],
    fun z hz => by rw [add_mulVec]; exact W.add_mem (hA.2.1 z hz) (hB.2.1 z hz),
    fun z => by rw [add_mulVec]; exact (perp J W).add_mem (hA.2.2 z) (hB.2.2 z)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w hw => by rw [smul_mulVec, hA.1 w hw, smul_zero], fun z hz => by rw [smul_mulVec]; exact W.smul_mem c (hA.2.1 z hz), fun z => by rw [smul_mulVec]; exact (perp J W).smul_mem c (hA.2.2 z)⟩`.
-/
theorem Lowers.smul {A : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (c : K) : Lowers J W (c • A) :=
  ⟨fun w hw => by rw [smul_mulVec, hA.1 w hw, smul_zero],
    fun z hz => by rw [smul_mulVec]; exact W.smul_mem c (hA.2.1 z hz),
    fun z => by rw [smul_mulVec]; exact (perp J W).smul_mem c (hA.2.2 z)⟩

/- English proof (translation)
Simplify using `using hA.smul (-1)`.
-/
theorem Lowers.neg {A : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) : Lowers J W (-A) := by
  simpa using hA.smul (-1)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun z hz => by rw [← mulVec_mulVec, hA.1 _ (hB.2.1 z hz)], fun z => by rw [← mulVec_mulVec]; exact hA.2.1 _ (hB.2.2 z)⟩`.
-/
theorem Lowers.mul_perp {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) :
    (∀ z ∈ perp J W, (A * B) *ᵥ z = 0) ∧ ∀ z, (A * B) *ᵥ z ∈ W :=
  ⟨fun z hz => by rw [← mulVec_mulVec, hA.1 _ (hB.2.1 z hz)],
    fun z => by rw [← mulVec_mulVec]; exact hA.2.1 _ (hB.2.2 z)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w hw => h1 w (hW hw), fun z _ => h2 z, fun z => hW (h2 z)⟩`.
-/
theorem lowers_of_Z (hW : Isot J W) {Z : Matrix (Fin n) (Fin n) K} (h1 : ∀ z ∈ perp J W, Z *ᵥ z = 0)
    (h2 : ∀ z, Z *ᵥ z ∈ W) : Lowers J W Z :=
  ⟨fun w hw => h1 w (hW hw), fun z _ => h2 z, fun z => hW (h2 z)⟩

/- English proof (translation)
The claim follows from `lowers_of_Z hW (hA.mul_perp hB).1 (hA.mul_perp hB).2`.
-/
theorem Lowers.mul (hW : Isot J W) {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) :
    Lowers J W (A * B) := lowers_of_Z hW (hA.mul_perp hB).1 (hA.mul_perp hB).2

variable [CharZero K]

/- English proof (translation)
Establish `t1` using `hX.triple hX hY`. Establish `t2` using `hX.triple hY hY`. Simplify using `only [ex2, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, t1, t2, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, smul_zero, add_zero]`. Normalize the expressions using the abelian group laws.
-/
theorem second_order_exp_mul {X Y : Matrix (Fin n) (Fin n) K} (hX : Lowers J W X) (hY : Lowers J W Y) :
    ex2 X * ex2 Y = 1 + X + Y + (2 : K)⁻¹ • (X * X) + X * Y + (2 : K)⁻¹ • (Y * Y) := by
  have t1 := hX.triple hX hY
  have t2 := hX.triple hY hY
  simp only [ex2, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, t1, t2, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, smul_zero, add_zero]
  abel

omit [CharZero K] in
/- English proof (translation)
Rewrite using `[star_inv₀, star_ofNat]`.
-/
theorem star_half : star (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [star_inv₀, star_ofNat]

omit [CharZero K] in
/- English proof (translation)
The claim follows from `eq_neg_of_add_eq_zero_left h`.
-/
theorem skew_eq {X : Matrix (Fin n) (Fin n) K} (h : Xᴴ * J + J * X = 0) : Xᴴ * J = -(J * X) :=
  eq_neg_of_add_eq_zero_left h

omit [CharZero K] in
/- English proof (translation)
Rewrite using `[conjTranspose_mul, Matrix.mul_assoc, skew_eq hX, Matrix.mul_neg, ← Matrix.mul_assoc, skew_eq hY, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`.
-/
theorem skew_mul {X Y : Matrix (Fin n) (Fin n) K} (hX : Xᴴ * J + J * X = 0) (hY : Yᴴ * J + J * Y = 0) :
    (X * Y)ᴴ * J = J * (Y * X) := by
  rw [conjTranspose_mul, Matrix.mul_assoc, skew_eq hX, Matrix.mul_neg, ← Matrix.mul_assoc, skew_eq hY,
    Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

/- English proof (translation)
Introduce `K _ _ _ n J W _ _ hW`. Establish `inv : ∀ X, Lowers J W X → ex2 X * ex2 (-X) = 1` using `fun X hX => by`. Rewrite using `[second_order_exp_mul hX hX.neg]`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]`. Use `module`.

Establish `hneg : ∀ X, InL J W X → InL J W (-X)` using `fun X hX => ⟨by rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX.1, neg_zero], hX.2.neg⟩`. Use `⟨fun X hX => ⟨?_, ?_, inv X hX.2, hneg X hX⟩, fun g hg hA => ?_, fun X Y hX hY => ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩, fun Z hZ => ⟨⟨hZ.1, lowers_of_Z hW hZ.2.1 hZ.2.2⟩, ⟨?_, fun z hz => ?_, fun z => ?_⟩, fun X hX => ⟨?_, ?_⟩⟩⟩` and prove the remaining obligations. Establish `h1 : (ex2 X)ᴴ * J = J * ex2 (-X)`. Simplify using `only [ex2, conjTranspose_add, conjTranspose_one, conjTranspose_smul, star_half, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, skew_mul hX.1 hX.1, skew_eq hX.1, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]`. Establish `h2` using `inv _ hX.2.neg`.

Rewrite `h2` using `[neg_neg]`. Rewrite using `[h1, Matrix.mul_assoc, h2, Matrix.mul_one]`. Establish `: ex2 X - 1 = X + (2 : K)⁻¹ • (X * X)` using `by unfold ex2; abel`. Rewrite using `[this]`. Conclude with `hX.2.add ((hX.2.mul hW hX.2).smul _)`.

Take `⟨A, rfl⟩ : ∃ A, g = 1 + A` from `⟨g - 1, by abel⟩`. Rewrite `hA` using `[add_sub_cancel_left]`. Establish `t` using `hA.triple hA hA`. Establish `h1 : (Aᴴ * J + J * (A - A * A)) * (1 + A) = 0`. Establish `e : (1 + A)ᴴ * J * (1 + A) - J = 0` using `by rw [hg, sub_self]`.

Rewrite using `[← e]`. Simplify using `only [conjTranspose_add, conjTranspose_one, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_assoc, t, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero]`. Normalize the expressions using the abelian group laws. Establish `h2 : (1 + A) * (1 - A + A * A) = 1`. Simplify using `only [mul_add, add_mul, mul_sub, t, Matrix.one_mul, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Establish `h3 : Aᴴ * J = -(J * (A - A * A))`. Use `congrArg (· * (1 - A + A * A)) h1` as an intermediate fact. Simplify using `only [Matrix.mul_assoc _ (1 + A), h2, Matrix.mul_one, Matrix.zero_mul] at this`. Conclude with `eq_neg_of_add_eq_zero_left this`.

Establish `h4 : (A * A)ᴴ * J = J * (A * A)`. Rewrite using `[conjTranspose_mul, Matrix.mul_assoc, h3, Matrix.mul_neg, ← Matrix.mul_assoc, h3]`. Simplify using `only [Matrix.neg_mul, neg_neg, mul_sub, sub_mul, Matrix.mul_assoc, t, Matrix.mul_zero, sub_zero, neg_zero]`. Use `⟨A + (-(2 : K)⁻¹) • (A * A), ⟨?_, hA.add ((hA.mul hW hA).smul _)⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [conjTranspose_add, conjTranspose_smul, star_neg, star_half, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h3, h4, mul_sub] module`.

Simplify using `only [ex2, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, t, Matrix.mul_zero, smul_zero, add_zero] module`. Conclude with `⟨by rw [conjTranspose_add, add_mul, mul_add, skew_eq hX.1, skew_eq hY.1]; abel, hX.2.add hY.2⟩`. Simplify using `only [conjTranspose_smul, conjTranspose_sub, star_half, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, skew_mul hX.1 hY.1, skew_mul hY.1 hX.1] module`. Introduce `z hz`. Rewrite using `[smul_mulVec, sub_mulVec, (hX.2.mul_perp hY.2).1 z hz, (hY.2.mul_perp hX.2).1 z hz, sub_zero, smul_zero]`.

Introduce `z`. Rewrite using `[smul_mulVec, sub_mulVec]`. Conclude with `W.smul_mem _ (W.sub_mem ((hX.2.mul_perp hY.2).2 z) ((hY.2.mul_perp hX.2).2 z))`. Establish `a` using `hX.2`. Establish `b` using `hY.2`.

Rewrite using `[second_order_exp_mul a b]`. Simplify using `only [ex2, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, a.triple a a, a.triple a b, a.triple b a, a.triple b b, b.triple a a, b.triple a b, b.triple b a, b.triple b b, Matrix.mul_zero, smul_zero, sub_zero, add_zero, sub_self]`. Use `module`. Rewrite using `[conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hZ.1, neg_zero]`. Rewrite using `[neg_mulVec, hZ.2.1 z hz, neg_zero]`.

Rewrite using `[neg_mulVec]`. Conclude with `W.neg_mem (hZ.2.2 z)`. Conclude with `mat_extC fun z => by rw [← mulVec_mulVec, hZ.2.1 _ (hX.2.2.2 z), zero_mulVec]`. Conclude with `mat_extC fun z => by rw [← mulVec_mulVec, hX.2.1 _ (hZ.2.2 z), zero_mulVec]`.
-/
theorem nilpotent_lie_algebra : NilpAlg := by
  intro K _ _ _ n J W _ _ hW
  have inv : ∀ X, Lowers J W X → ex2 X * ex2 (-X) = 1 := fun X hX => by
    rw [second_order_exp_mul hX hX.neg]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    module
  have hneg : ∀ X, InL J W X → InL J W (-X) := fun X hX =>
    ⟨by rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX.1, neg_zero], hX.2.neg⟩
  refine ⟨fun X hX => ⟨?_, ?_, inv X hX.2, hneg X hX⟩, fun g hg hA => ?_, fun X Y hX hY => ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩,
    fun Z hZ => ⟨⟨hZ.1, lowers_of_Z hW hZ.2.1 hZ.2.2⟩, ⟨?_, fun z hz => ?_, fun z => ?_⟩, fun X hX => ⟨?_, ?_⟩⟩⟩
  · have h1 : (ex2 X)ᴴ * J = J * ex2 (-X) := by
      simp only [ex2, conjTranspose_add, conjTranspose_one, conjTranspose_smul, star_half, add_mul, mul_add,
        smul_mul_assoc, mul_smul_comm, skew_mul hX.1 hX.1, skew_eq hX.1, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    have h2 := inv _ hX.2.neg
    rw [neg_neg] at h2
    rw [h1, Matrix.mul_assoc, h2, Matrix.mul_one]
  · have : ex2 X - 1 = X + (2 : K)⁻¹ • (X * X) := by unfold ex2; abel
    rw [this]
    exact hX.2.add ((hX.2.mul hW hX.2).smul _)
  · obtain ⟨A, rfl⟩ : ∃ A, g = 1 + A := ⟨g - 1, by abel⟩
    rw [add_sub_cancel_left] at hA
    have t := hA.triple hA hA
    have h1 : (Aᴴ * J + J * (A - A * A)) * (1 + A) = 0 := by
      have e : (1 + A)ᴴ * J * (1 + A) - J = 0 := by rw [hg, sub_self]
      rw [← e]
      simp only [conjTranspose_add, conjTranspose_one, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_assoc, t,
        Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero]
      abel
    have h2 : (1 + A) * (1 - A + A * A) = 1 := by
      simp only [mul_add, add_mul, mul_sub, t, Matrix.one_mul, Matrix.mul_one]
      abel
    have h3 : Aᴴ * J = -(J * (A - A * A)) := by
      have := congrArg (· * (1 - A + A * A)) h1
      simp only [Matrix.mul_assoc _ (1 + A), h2, Matrix.mul_one, Matrix.zero_mul] at this
      exact eq_neg_of_add_eq_zero_left this
    have h4 : (A * A)ᴴ * J = J * (A * A) := by
      rw [conjTranspose_mul, Matrix.mul_assoc, h3, Matrix.mul_neg, ← Matrix.mul_assoc, h3]
      simp only [Matrix.neg_mul, neg_neg, mul_sub, sub_mul, Matrix.mul_assoc, t, Matrix.mul_zero, sub_zero,
        neg_zero]
    refine ⟨A + (-(2 : K)⁻¹) • (A * A), ⟨?_, hA.add ((hA.mul hW hA).smul _)⟩, ?_⟩
    · simp only [conjTranspose_add, conjTranspose_smul, star_neg, star_half, add_mul, mul_add, smul_mul_assoc,
        mul_smul_comm, h3, h4, mul_sub]
      module
    · simp only [ex2, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, t, Matrix.mul_zero,
        smul_zero, add_zero]
      module
  · exact ⟨by rw [conjTranspose_add, add_mul, mul_add, skew_eq hX.1, skew_eq hY.1]; abel, hX.2.add hY.2⟩
  · simp only [conjTranspose_smul, conjTranspose_sub, star_half, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub,
      skew_mul hX.1 hY.1, skew_mul hY.1 hX.1]
    module
  · intro z hz
    rw [smul_mulVec, sub_mulVec, (hX.2.mul_perp hY.2).1 z hz, (hY.2.mul_perp hX.2).1 z hz, sub_zero, smul_zero]
  · intro z
    rw [smul_mulVec, sub_mulVec]
    exact W.smul_mem _ (W.sub_mem ((hX.2.mul_perp hY.2).2 z) ((hY.2.mul_perp hX.2).2 z))
  · have a := hX.2
    have b := hY.2
    rw [second_order_exp_mul a b]
    simp only [ex2, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc,
      a.triple a a, a.triple a b, a.triple b a, a.triple b b, b.triple a a, b.triple a b, b.triple b a,
      b.triple b b, Matrix.mul_zero, smul_zero, sub_zero, add_zero, sub_self]
    module
  · rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hZ.1, neg_zero]
  · rw [neg_mulVec, hZ.2.1 z hz, neg_zero]
  · rw [neg_mulVec]; exact W.neg_mem (hZ.2.2 z)
  · exact mat_extC fun z => by rw [← mulVec_mulVec, hZ.2.1 _ (hX.2.2.2 z), zero_mulVec]
  · exact mat_extC fun z => by rw [← mulVec_mulVec, hX.2.1 _ (hZ.2.2 z), zero_mulVec]

end CompanionTheory.D.gk.RF

namespace CompanionTheory.D.gk.RF

variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}

/- English proof (translation)
Simplify using `only [xw, sub_mulVec, vecMulVec_mulVec, hf, dotProduct_mulVec, op_smul_eq_smul]`.
-/
theorem xw_mulVec (w b z : Fin n → K) : xw J w b *ᵥ z = hf J b z • w - hf J w z • b := by
  simp only [xw, sub_mulVec, vecMulVec_mulVec, hf, dotProduct_mulVec, op_smul_eq_smul]

/- English proof (translation)
Unfold `hf`. Rewrite using `[← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec]`.
-/
theorem hf_star (hJ : Jᴴ = J) (x y : Fin n → K) : star (hf J x y) = hf J y x := by
  unfold hf
  rw [← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec]

/- English proof (translation)
Simplify using `only [hf, mulVec_sub, dotProduct_sub]`.
-/
theorem hf_sub_right (x y z : Fin n → K) : hf J x (y - z) = hf J x y - hf J x z := by
  simp only [hf, mulVec_sub, dotProduct_sub]

/- English proof (translation)
Simplify using `only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem hf_smul_right (c : K) (x y : Fin n → K) : hf J x (c • y) = c * hf J x y := by
  simp only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [hf, mulVec_sum, dotProduct_sum]`.
-/
theorem hf_sum_right {ι : Type} (s : Finset ι) (x : Fin n → K) (y : ι → Fin n → K) :
    hf J x (∑ i ∈ s, y i) = ∑ i ∈ s, hf J x (y i) := by
  simp only [hf, mulVec_sum, dotProduct_sum]

/- English proof (translation)
Simplify using `only [hf, star_add, add_dotProduct]`.
-/
theorem hf_add_leftC (x y z : Fin n → K) : hf J (x + y) z = hf J x z + hf J y z := by
  simp only [hf, star_add, add_dotProduct]

/- English proof (translation)
Simplify using `only [hf, star_neg, neg_dotProduct]`.
-/
theorem hf_neg_left (x z : Fin n → K) : hf J (-x) z = -hf J x z := by
  simp only [hf, star_neg, neg_dotProduct]

/- English proof (translation)
Simplify using `only [hf, star_smul, smul_dotProduct, smul_eq_mul]`.
-/
theorem hf_smul_leftC (c : K) (x y : Fin n → K) : hf J (c • x) y = star c * hf J x y := by
  simp only [hf, star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Simplify using `only [hf, star_sum, sum_dotProduct]`.
-/
theorem hf_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin n → K) (y : Fin n → K) :
    hf J (∑ i ∈ s, x i) y = ∑ i ∈ s, hf J (x i) y := by
  simp only [hf, star_sum, sum_dotProduct]

/- English proof (translation)
Unfold `hf`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, skew_eq h, neg_mulVec, dotProduct_neg, mulVec_mulVec]`.
-/
theorem hf_skew {X : Matrix (Fin n) (Fin n) K} (h : Xᴴ * J + J * X = 0) (x y : Fin n → K) :
    hf J (X *ᵥ x) y = -hf J x (X *ᵥ y) := by
  unfold hf
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, skew_eq h, neg_mulVec, dotProduct_neg, mulVec_mulVec]

/- English proof (translation)
Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Unfold `hf at this`. Rewrite `this` using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← dotProduct_neg, ← neg_mulVec]`. Establish `e : star (Pi.single i 1 : Fin n → K) = Pi.single i 1`.

Apply the tactic sequence `ext k; by_cases hk : k = i <;> simp [hk]`. Simplify using `only [e, mulVec_single_one, single_one_dotProduct, Matrix.col_apply, Matrix.neg_apply] at this`. Simplify using `[this]`.
-/
theorem skew_of_hf {X : Matrix (Fin n) (Fin n) K} (h : ∀ x y, hf J (X *ᵥ x) y = -hf J x (X *ᵥ y)) :
    Xᴴ * J + J * X = 0 := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  unfold hf at this
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← dotProduct_neg, ← neg_mulVec] at this
  have e : star (Pi.single i 1 : Fin n → K) = Pi.single i 1 := by
    ext k; by_cases hk : k = i <;> simp [hk]
  simp only [e, mulVec_single_one, single_one_dotProduct, Matrix.col_apply, Matrix.neg_apply] at this
  simp [this]

/- English proof (translation)
The claim follows from `skew_of_hf fun x y => by rw [xw_mulVec, xw_mulVec, sub_eq_add_neg, hf_add_leftC, hf_neg_left, hf_smul_leftC, hf_smul_leftC, hf_sub_right, hf_smul_right, hf_smul_right, hf_star hJ, hf_star hJ] ring`.
-/
theorem skew_xw (hJ : Jᴴ = J) (w b : Fin n → K) : (xw J w b)ᴴ * J + J * xw J w b = 0 :=
  skew_of_hf fun x y => by
    rw [xw_mulVec, xw_mulVec, sub_eq_add_neg, hf_add_leftC, hf_neg_left, hf_smul_leftC, hf_smul_leftC, hf_sub_right,
      hf_smul_right, hf_smul_right, hf_star hJ, hf_star hJ]
    ring

/- English proof (translation)
Rewrite using `[← hf_star hJ, hb w hw, star_zero]`.
-/
theorem perp_symm (hJ : Jᴴ = J) {b w : Fin n → K} (hb : b ∈ perp J W) (hw : w ∈ W) : hf J b w = 0 := by
  rw [← hf_star hJ, hb w hw, star_zero]

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨i, rfl⟩ := hx`. Conclude with `h i`. Consider the case `zero => simp [hf]`.

Consider the case `add a b _ _ ha hb => rw [hf_add_leftC, ha, hb, add_zero]`. Consider the case `smul c a _ ha => rw [hf_smul_leftC, ha, mul_zero]`.
-/
theorem mem_perp_spanC {ι : Type} {w : ι → Fin n → K} {z : Fin n → K} (h : ∀ i, hf J (w i) z = 0) :
    z ∈ perp J (Submodule.span K (Set.range w)) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_leftC, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_leftC, ha, mul_zero]

/- English proof (translation)
Establish `hk : LinearMap.ker (Fintype.linearCombination K v) = ⊥` using `LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hv c hc)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hk`. Use `⟨fun i => J⁻¹ *ᵥ star fun k => g (Pi.single k 1) i, fun i j => ?_⟩` and prove the remaining obligations. Establish `h1 : g (v j) = Pi.single j 1`. Use `LinearMap.congr_fun hg (Pi.single j 1)` as an intermediate fact.

Simplify `this` using `[Fintype.linearCombination_apply_single]`. Establish `h2 : (J⁻¹)ᴴ = J⁻¹` using `by rw [conjTranspose_nonsing_inv, hJ]`. Unfold `hf`. Rewrite using `[star_mulVec, star_star, h2, dotProduct_mulVec, vecMul_vecMul, nonsing_inv_mul J hd, vecMul_one]`. Establish `h3 : v j = ∑ k, v j k • (Pi.single k 1 : Fin n → K)`.

Use extensionality with `l`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `h4` using `congrFun h1 i`. Rewrite `h4` using `[h3, map_sum, Finset.sum_apply]`. Rewrite `h4` using `[Pi.single_apply]`.

Rewrite using `[← h4]`. Simplify using `only [dotProduct, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]`.
-/
theorem exists_dual (hJ : Jᴴ = J) (hd : IsUnit J.det) {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → Fin n → K}
    (hv : LinearIndependent K v) : ∃ u : κ → Fin n → K, ∀ i j, hf J (u i) (v j) = if i = j then 1 else 0 := by
  have hk : LinearMap.ker (Fintype.linearCombination K v) = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hv c hc)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨fun i => J⁻¹ *ᵥ star fun k => g (Pi.single k 1) i, fun i j => ?_⟩
  have h1 : g (v j) = Pi.single j 1 := by
    have := LinearMap.congr_fun hg (Pi.single j 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have h2 : (J⁻¹)ᴴ = J⁻¹ := by rw [conjTranspose_nonsing_inv, hJ]
  unfold hf
  rw [star_mulVec, star_star, h2, dotProduct_mulVec, vecMul_vecMul, nonsing_inv_mul J hd, vecMul_one]
  have h3 : v j = ∑ k, v j k • (Pi.single k 1 : Fin n → K) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  have h4 := congrFun h1 i
  rw [h3, map_sum, Finset.sum_apply] at h4
  rw [Pi.single_apply] at h4
  rw [← h4]
  simp only [dotProduct, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_dual hJ hd hv`. Establish `hu' : ∀ i j, hf J (v i) (u j) = if i = j then 1 else 0` using `fun i j => by`. Apply the tactic sequence `rw [← hf_star hJ, hu]; by_cases h : i = j <;> simp [h, eq_comm]`. Establish `hvW : ∀ k, v k ∈ W` using `fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩`. Establish `hexp : ∀ w ∈ W, ∑ i, hf J (u i) w • v i = w`.

Introduce `w hw`. Rewrite `hw` using `[← hs]`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hw`. Simplify using `only [hf_sum_right, hf_smul_right, hu, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Set `s : κ → κ → K` to `fun i k => hf J (u i) (X *ᵥ u k)`.

Establish `hss : ∀ i k, star (s k i) = -s i k` using `fun i k => by`. Simplify using `only [s]`. Rewrite using `[hf_star hJ, hf_skew hX.1]`. Set `b : κ → Fin n → K` to `fun k => -(X *ᵥ u k) + ∑ i, ((2 : K)⁻¹ * s i k) • v i`. Establish `hsum : ∀ k, ∑ i, ((2 : K)⁻¹ * s i k) • v i ∈ W` using `fun k => W.sum_mem fun i _ => W.smul_mem _ (hvW i)`.

Use `⟨b, fun k => (perp J W).add_mem ((perp J W).neg_mem (hX.2.2.2 _)) (hW (hsum k)), fun h k => W.add_mem (W.neg_mem (h _)) (hsum k), ?_⟩` and prove the remaining obligations. Establish `e1 : ∀ z ∈ perp J W, (∑ k, xw J (v k) (b k)) *ᵥ z = X *ᵥ z` using `fun z hz => by`. Rewrite using `[sum_mulVec, ← hexp _ (hX.2.2.1 z hz)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[xw_mulVec, hz _ (hvW k), zero_smul, sub_zero]`.

Simplify using `only [b]`. Rewrite using `[hf_add_leftC, hz _ (hsum k), add_zero, hf_neg_left, hf_skew hX.1, neg_neg]`. Establish `e2 : ∀ j, (∑ k, xw J (v k) (b k)) *ᵥ u j = X *ᵥ u j` using `fun j => by`. Establish `hb : ∀ k, hf J (b k) (u j) = (2 : K)⁻¹ * s k j` using `fun k => by`. Simplify using `only [b]`.

Rewrite using `[hf_add_leftC, hf_neg_left, hf_skew hX.1, neg_neg, hf_sum_left]`. Simplify using `only [hf_smul_leftC, hu', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, star_mul', star_half, hss]`. Use `show s k j + _ = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sum_mulVec]`.

Simplify using `only [xw_mulVec, hb, hu', ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [b]`. Normalize the expressions using the abelian group laws. Use `mat_extC fun z => ?_` and prove the remaining obligations. Establish `hz : z - ∑ j, hf J (v j) z • u j ∈ perp J W`.

Rewrite using `[← hs]`. Use `mem_perp_spanC fun i => ?_` and prove the remaining obligations. Simplify using `only [hf_sub_right, hf_sum_right, hf_smul_right, hu', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]`. Rewrite using `[← sub_add_cancel z (∑ j, hf J (v j) z • u j), mulVec_add, mulVec_add, e1 _ hz, mulVec_sum, mulVec_sum]`. Simplify using `only [mulVec_smul, e2]`.
-/
theorem rep_basis [CharZero K] (hJ : Jᴴ = J) (hd : IsUnit J.det) (hW : Isot J W) {κ : Type} [Fintype κ]
    [DecidableEq κ] {v : κ → Fin n → K} (hv : LinearIndependent K v) (hs : Submodule.span K (Set.range v) = W)
    {X : Matrix (Fin n) (Fin n) K} (hX : InL J W X) :
    ∃ b : κ → Fin n → K, (∀ k, b k ∈ perp J W) ∧ ((∀ z, X *ᵥ z ∈ W) → ∀ k, b k ∈ W) ∧ X = ∑ k, xw J (v k) (b k) := by
  obtain ⟨u, hu⟩ := exists_dual hJ hd hv
  have hu' : ∀ i j, hf J (v i) (u j) = if i = j then 1 else 0 := fun i j => by
    rw [← hf_star hJ, hu]; by_cases h : i = j <;> simp [h, eq_comm]
  have hvW : ∀ k, v k ∈ W := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  have hexp : ∀ w ∈ W, ∑ i, hf J (u i) w • v i = w := by
    intro w hw
    rw [← hs] at hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
    simp only [hf_sum_right, hf_smul_right, hu, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  let s : κ → κ → K := fun i k => hf J (u i) (X *ᵥ u k)
  have hss : ∀ i k, star (s k i) = -s i k := fun i k => by
    simp only [s]; rw [hf_star hJ, hf_skew hX.1]
  let b : κ → Fin n → K := fun k => -(X *ᵥ u k) + ∑ i, ((2 : K)⁻¹ * s i k) • v i
  have hsum : ∀ k, ∑ i, ((2 : K)⁻¹ * s i k) • v i ∈ W := fun k =>
    W.sum_mem fun i _ => W.smul_mem _ (hvW i)
  refine ⟨b, fun k => (perp J W).add_mem ((perp J W).neg_mem (hX.2.2.2 _)) (hW (hsum k)),
    fun h k => W.add_mem (W.neg_mem (h _)) (hsum k), ?_⟩
  have e1 : ∀ z ∈ perp J W, (∑ k, xw J (v k) (b k)) *ᵥ z = X *ᵥ z := fun z hz => by
    rw [sum_mulVec, ← hexp _ (hX.2.2.1 z hz)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [xw_mulVec, hz _ (hvW k), zero_smul, sub_zero]
    simp only [b]
    rw [hf_add_leftC, hz _ (hsum k), add_zero, hf_neg_left, hf_skew hX.1, neg_neg]
  have e2 : ∀ j, (∑ k, xw J (v k) (b k)) *ᵥ u j = X *ᵥ u j := fun j => by
    have hb : ∀ k, hf J (b k) (u j) = (2 : K)⁻¹ * s k j := fun k => by
      simp only [b]
      rw [hf_add_leftC, hf_neg_left, hf_skew hX.1, neg_neg, hf_sum_left]
      simp only [hf_smul_leftC, hu', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        star_mul', star_half, hss]
      show s k j + _ = _
      ring
    rw [sum_mulVec]
    simp only [xw_mulVec, hb, hu', ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simp only [b]
    abel
  refine mat_extC fun z => ?_
  have hz : z - ∑ j, hf J (v j) z • u j ∈ perp J W := by
    rw [← hs]
    refine mem_perp_spanC fun i => ?_
    simp only [hf_sub_right, hf_sum_right, hf_smul_right, hu', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self]
  rw [← sub_add_cancel z (∑ j, hf J (v j) z • u j), mulVec_add, mulVec_add, e1 _ hz, mulVec_sum, mulVec_sum]
  simp only [mulVec_smul, e2]

/- English proof (translation)
Take `⟨κ, a, ha, hsp, hli⟩` from `exists_linearIndependent' K w`. Use `Fintype.ofInjective a ha` as an intermediate fact. Take `⟨b, h1, h2, h3⟩` from `rep_basis hJ hd hW hli (hsp.trans hs) hX`. Establish `hP : ∀ (S : Submodule K (Fin n → K)), (∀ k, b k ∈ S) → ∀ i, Function.extend a b 0 i ∈ S` using `fun S h i => by`. Distinguish the cases in `hi : ∃ k, a k = i`.

Take `⟨k, rfl⟩` from `hi`. Rewrite using `[ha.extend_apply]`. Conclude with `h k`. Rewrite using `[Function.extend_apply' _ _ _ hi]`. Conclude with `S.zero_mem`.

Use `⟨Function.extend a b 0, hP _ h1, fun h => hP _ (h2 h), h3.trans ?_⟩` and prove the remaining obligations. Use `Fintype.sum_of_injective a ha _ _ (fun i hi => ?_) fun k => by rw [ha.extend_apply]; rfl` and prove the remaining obligations. Rewrite using `[Function.extend_apply' _ _ _ hi]`. Simplify using `[xw]`.
-/
theorem rep_span [CharZero K] (hJ : Jᴴ = J) (hd : IsUnit J.det) (hW : Isot J W) {d : ℕ} {w : Fin d → Fin n → K}
    (hs : Submodule.span K (Set.range w) = W) {X : Matrix (Fin n) (Fin n) K} (hX : InL J W X) :
    ∃ b : Fin d → Fin n → K, (∀ k, b k ∈ perp J W) ∧ ((∀ z, X *ᵥ z ∈ W) → ∀ k, b k ∈ W) ∧
      X = ∑ k, xw J (w k) (b k) := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K w
  have := Fintype.ofInjective a ha
  obtain ⟨b, h1, h2, h3⟩ := rep_basis hJ hd hW hli (hsp.trans hs) hX
  have hP : ∀ (S : Submodule K (Fin n → K)), (∀ k, b k ∈ S) → ∀ i, Function.extend a b 0 i ∈ S := fun S h i => by
    by_cases hi : ∃ k, a k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [ha.extend_apply]; exact h k
    · rw [Function.extend_apply' _ _ _ hi]; exact S.zero_mem
  refine ⟨Function.extend a b 0, hP _ h1, fun h => hP _ (h2 h), h3.trans ?_⟩
  refine Fintype.sum_of_injective a ha _ _ (fun i hi => ?_) fun k => by rw [ha.extend_apply]; rfl
  rw [Function.extend_apply' _ _ _ hi]
  simp [xw]

/- English proof (translation)
Introduce `K _ _ _ n J W hJ hd hW d w hs`. Establish `hwW : ∀ k, w k ∈ W` using `fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩`. Establish `sk : ∀ b : Fin d → Fin n → K, (∑ i, xw J (w i) (b i))ᴴ * J + J * ∑ i, xw J (w i) (b i) = 0` using `fun b => by`. Rewrite using `[conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_eq_zero fun i _ => skew_xw hJ _ _`.

Use `⟨fun b hb => ⟨sk b, fun z hz => ?_, fun z hz => ?_, fun z => ?_⟩, fun b hb => ⟨sk b, fun z hz => ?_, fun z => ?_⟩, fun X hX => ?_, fun X hX => ?_⟩` and prove the remaining obligations. Rewrite using `[sum_mulVec]`. Conclude with `Finset.sum_eq_zero fun i _ => by`. Rewrite using `[xw_mulVec, perp_symm hJ (hb i) hz, hW hz _ (hwW i), zero_smul, zero_smul, sub_zero]`. Rewrite using `[sum_mulVec]`.

Conclude with `W.sum_mem fun i _ => by`. Rewrite using `[xw_mulVec, hz _ (hwW i), zero_smul, sub_zero]`. Conclude with `W.smul_mem _ (hwW i)`. Rewrite using `[sum_mulVec]`. Conclude with `(perp J W).sum_mem fun i _ => by`.

Rewrite using `[xw_mulVec]`. Conclude with `(perp J W).sub_mem ((perp J W).smul_mem _ (hW (hwW i))) ((perp J W).smul_mem _ (hb i))`. Rewrite using `[sum_mulVec]`. Conclude with `Finset.sum_eq_zero fun i _ => by`. Rewrite using `[xw_mulVec, hz _ (hwW i), hz _ (hb i), zero_smul, zero_smul, sub_zero]`.

Rewrite using `[sum_mulVec]`. Conclude with `W.sum_mem fun i _ => by`. Rewrite using `[xw_mulVec]`. Conclude with `W.sub_mem (W.smul_mem _ (hwW i)) (W.smul_mem _ (hb i))`. Take `⟨b, h1, -, h3⟩` from `rep_span hJ hd hW hs hX`.

Conclude with `⟨b, h1, h3⟩`. Take `⟨b, -, h2, h3⟩` from `rep_span hJ hd hW hs ⟨hX.1, lowers_of_Z hW hX.2.1 hX.2.2⟩`. Conclude with `⟨b, h2 hX.2.2, h3⟩`.
-/
theorem nilpotent_subgroup_representation : NilpRep := by
  intro K _ _ _ n J W hJ hd hW d w hs
  have hwW : ∀ k, w k ∈ W := fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩
  have sk : ∀ b : Fin d → Fin n → K, (∑ i, xw J (w i) (b i))ᴴ * J + J * ∑ i, xw J (w i) (b i) = 0 := fun b => by
    rw [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => skew_xw hJ _ _
  refine ⟨fun b hb => ⟨sk b, fun z hz => ?_, fun z hz => ?_, fun z => ?_⟩, fun b hb => ⟨sk b, fun z hz => ?_,
    fun z => ?_⟩, fun X hX => ?_, fun X hX => ?_⟩
  · rw [sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => by
      rw [xw_mulVec, perp_symm hJ (hb i) hz, hW hz _ (hwW i), zero_smul, zero_smul, sub_zero]
  · rw [sum_mulVec]
    exact W.sum_mem fun i _ => by
      rw [xw_mulVec, hz _ (hwW i), zero_smul, sub_zero]; exact W.smul_mem _ (hwW i)
  · rw [sum_mulVec]
    exact (perp J W).sum_mem fun i _ => by
      rw [xw_mulVec]
      exact (perp J W).sub_mem ((perp J W).smul_mem _ (hW (hwW i))) ((perp J W).smul_mem _ (hb i))
  · rw [sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => by
      rw [xw_mulVec, hz _ (hwW i), hz _ (hb i), zero_smul, zero_smul, sub_zero]
  · rw [sum_mulVec]
    exact W.sum_mem fun i _ => by
      rw [xw_mulVec]; exact W.sub_mem (W.smul_mem _ (hwW i)) (W.smul_mem _ (hb i))
  · obtain ⟨b, h1, -, h3⟩ := rep_span hJ hd hW hs hX
    exact ⟨b, h1, h3⟩
  · obtain ⟨b, -, h2, h3⟩ := rep_span hJ hd hW hs ⟨hX.1, lowers_of_Z hW hX.2.1 hX.2.2⟩
    exact ⟨b, h2 hX.2.2, h3⟩

/- English proof (translation)
Introduce `K _ n A ν s₀ η hs hη hη1 ⟨u₀, hu₀, hne, hν⟩`. Set `S : ℕ → Set (Fin n → K)` to `fun j => {u | u ∈ A ∧ ν u ≤ s₀ * η ^ j}`. Set `Wj : ℕ → Submodule K (Fin n → K)` to `fun j => Submodule.span K (S j)`. Establish `hmono : ∀ j, Wj (j + 1) ≤ Wj j` using `fun j => Submodule.span_mono fun u hu => ⟨hu.1, hu.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1.le (Nat.le_succ j)) hs.le)⟩`. Establish `hnz : ∀ j ≤ n + 1, Wj j ≠ ⊥` using `fun j hj h => hne (by`.

Establish `: u₀ ∈ Wj j` using `Submodule.subset_span ⟨hu₀, hν.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1.le hj) hs.le)⟩`. Rewrite using `[h, Submodule.mem_bot] at this)` and apply the resulting hypothesis. Establish `hex : ∃ j ≤ n, Wj (j + 1) = Wj j`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Establish `: ∀ j ≤ n + 1, Module.finrank K (Wj j) + j ≤ n`. Introduce `j hj`. Proceed by induction on `j with`. Consider the case `zero => simpa using (Wj 0).finrank_le`. Consider the case `succ j ih`.

Establish `h1` using `Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono j) (hc j (by omega)))`. Establish `h2` using `ih (by omega)`. Use linear arithmetic over natural numbers and integers. Use `this (n + 1) le_rfl` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨j, hj, he⟩` from `hex`. Take `⟨B, hBS, hBsp, hli⟩` from `exists_linearIndependent K (S (j + 1))`. Establish `hfin : B.Finite` using `hli.setFinite`. Use `hfin.fintype` as an intermediate fact. Set `e` to `Fintype.equivFin B`.

Establish `hr : Set.range (fun i => ((e.symm i : B) : Fin n → K)) = B`. Rewrite using `[show (fun i => ((e.symm i : B) : Fin n → K)) = Subtype.val ∘ e.symm from rfl, e.symm.surjective.range_comp, Subtype.range_coe]`. Use `⟨s₀ * η ^ j, by positivity, mul_le_of_le_one_right hs.le (pow_le_one₀ hη.le hη1.le), _, fun i => e.symm i, by simpa using hli.fintype_card_le_finrank, fun i => ⟨(hBS (e.symm i).2).1, (hBS (e.symm i).2).2.trans (le_of_eq (by ring))⟩, ?_, fun u hu hut => ?_⟩` and prove the remaining obligations. Rewrite using `[hr, hBsp]; exact hnz (j + 1) (by omega)`. Rewrite using `[hr, hBsp] show u ∈ Wj (j + 1)`.

Rewrite using `[he]`. Conclude with `Submodule.subset_span ⟨hu, hut⟩`.
-/
theorem successive_minima_gap : Gap := by
  classical
  intro K _ n A ν s₀ η hs hη hη1 ⟨u₀, hu₀, hne, hν⟩
  let S : ℕ → Set (Fin n → K) := fun j => {u | u ∈ A ∧ ν u ≤ s₀ * η ^ j}
  let Wj : ℕ → Submodule K (Fin n → K) := fun j => Submodule.span K (S j)
  have hmono : ∀ j, Wj (j + 1) ≤ Wj j := fun j => Submodule.span_mono fun u hu =>
    ⟨hu.1, hu.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1.le (Nat.le_succ j)) hs.le)⟩
  have hnz : ∀ j ≤ n + 1, Wj j ≠ ⊥ := fun j hj h => hne (by
    have : u₀ ∈ Wj j := Submodule.subset_span ⟨hu₀, hν.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1.le hj) hs.le)⟩
    rwa [h, Submodule.mem_bot] at this)
  have hex : ∃ j ≤ n, Wj (j + 1) = Wj j := by
    by_contra hc
    push Not at hc
    have : ∀ j ≤ n + 1, Module.finrank K (Wj j) + j ≤ n := by
      intro j hj
      induction j with
      | zero => simpa using (Wj 0).finrank_le
      | succ j ih =>
        have h1 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono j) (hc j (by omega)))
        have h2 := ih (by omega)
        omega
    have := this (n + 1) le_rfl
    omega
  obtain ⟨j, hj, he⟩ := hex
  obtain ⟨B, hBS, hBsp, hli⟩ := exists_linearIndependent K (S (j + 1))
  have hfin : B.Finite := hli.setFinite
  have := hfin.fintype
  let e := Fintype.equivFin B
  have hr : Set.range (fun i => ((e.symm i : B) : Fin n → K)) = B := by
    rw [show (fun i => ((e.symm i : B) : Fin n → K)) = Subtype.val ∘ e.symm from rfl, e.symm.surjective.range_comp,
      Subtype.range_coe]
  refine ⟨s₀ * η ^ j, by positivity, mul_le_of_le_one_right hs.le (pow_le_one₀ hη.le hη1.le), _,
    fun i => e.symm i, by simpa using hli.fintype_card_le_finrank, fun i => ⟨(hBS (e.symm i).2).1,
      (hBS (e.symm i).2).2.trans (le_of_eq (by ring))⟩, ?_, fun u hu hut => ?_⟩
  · rw [hr, hBsp]; exact hnz (j + 1) (by omega)
  · rw [hr, hBsp]
    show u ∈ Wj (j + 1)
    rw [he]
    exact Submodule.subset_span ⟨hu, hut⟩

end CompanionTheory.D.gk.RF
