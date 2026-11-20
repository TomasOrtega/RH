import Mathlib
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero

open Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaInter

noncomputable section

namespace GlobalTheory.KerLaw

variable {V : Type} [AddCommGroup V] [Module ℂ V]

omit [Module ℂ V] in
/- English proof (translation)
Use `choose! r hr hr' using h'.2.2`. Use `Finset.sum_bij (fun x _ => r x) (fun x hx => hr x (h.1 x hx)) (fun x hx y hy e => ?_) (fun y hy => ?_) fun x hx => ?_` and prove the remaining obligations. Use `h.2.1 x hx y hy ?_` and prove the remaining obligations. Use `Λ₁.sub_mem (hr' x (h.1 x hx)) (hr' y (h.1 y hy))` as an intermediate fact. Rewrite `this` using `[e, sub_sub_sub_cancel_right]`. Then use the resulting hypothesis.

Take `⟨x, hx, e⟩` from `h.2.2 y (h'.1 y hy)`. Use `⟨x, hx, h'.2.1 _ (hr x (h.1 x hx)) _ hy ?_⟩` and prove the remaining obligations. Use `Λ₁.neg_mem (Λ₁.add_mem e (hr' x (h.1 x hx)))` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel, neg_sub]`. Then use the resulting hypothesis. Establish `h2` using `h'.1 _ (hr x (h.1 x hx))`.

Rewrite using `[← hf _ h2 _ (Λ₂.sub_mem (h.1 x hx) h2) (hr' x (h.1 x hx)), add_sub_cancel]`.
-/
theorem sum_reps {Λ₁ Λ₂ : AddSubgroup V} {S S' : Finset V} (h : IsReps Λ₁ Λ₂ S) (h' : IsReps Λ₁ Λ₂ S') (f : V → ℂ)
    (hf : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → f (x + l) = f x) : ∑ x ∈ S, f x = ∑ x ∈ S', f x := by
  choose! r hr hr' using h'.2.2
  refine Finset.sum_bij (fun x _ => r x) (fun x hx => hr x (h.1 x hx)) (fun x hx y hy e => ?_) (fun y hy => ?_) fun x hx => ?_
  · refine h.2.1 x hx y hy ?_
    have := Λ₁.sub_mem (hr' x (h.1 x hx)) (hr' y (h.1 y hy))
    rwa [e, sub_sub_sub_cancel_right] at this
  · obtain ⟨x, hx, e⟩ := h.2.2 y (h'.1 y hy)
    refine ⟨x, hx, h'.2.1 _ (hr x (h.1 x hx)) _ hy ?_⟩
    have := Λ₁.neg_mem (Λ₁.add_mem e (hr' x (h.1 x hx)))
    rwa [sub_add_sub_cancel, neg_sub] at this
  · have h2 := h'.1 _ (hr x (h.1 x hx))
    rw [← hf _ h2 _ (Λ₂.sub_mem (h.1 x hx) h2) (hr' x (h.1 x hx)), add_sub_cancel]

omit [Module ℂ V] in
/- English proof (translation)
Rewrite using `[← sum_reps (S := S.map φ.toEmbedding) ?_ h f hf, Finset.sum_map]`. Both sides reduce to the same expression. Use `⟨fun x hx => ?_, fun x hx y hy e => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, hx', rfl⟩` from `Finset.mem_map.1 hx`. Conclude with `(h2 x).2 (h.1 x hx')`.

Take `⟨x, hx', rfl⟩` from `Finset.mem_map.1 hx`. Take `⟨y, hy', rfl⟩` from `Finset.mem_map.1 hy`. Rewrite using `[h.2.1 x hx' y hy' ((h1 x y).1 e)]`. Take `⟨y, rfl⟩` from `φ.surjective y`. Take `⟨x, hx, e⟩` from `h.2.2 y ((h2 y).1 hy)`.

Conclude with `⟨φ x, Finset.mem_map_of_mem _ hx, (h1 y x).2 e⟩`.
-/
theorem sum_reps_equiv {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (h : IsReps Λ₁ Λ₂ S) (φ : V ≃ V)
    (h2 : ∀ x, φ x ∈ Λ₂ ↔ x ∈ Λ₂) (h1 : ∀ x y, φ x - φ y ∈ Λ₁ ↔ x - y ∈ Λ₁) (f : V → ℂ)
    (hf : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → f (x + l) = f x) : ∑ x ∈ S, f (φ x) = ∑ x ∈ S, f x := by
  rw [← sum_reps (S := S.map φ.toEmbedding) ?_ h f hf, Finset.sum_map]
  · rfl
  refine ⟨fun x hx => ?_, fun x hx y hy e => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hx', rfl⟩ := Finset.mem_map.1 hx
    exact (h2 x).2 (h.1 x hx')
  · obtain ⟨x, hx', rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y, hy', rfl⟩ := Finset.mem_map.1 hy
    rw [h.2.1 x hx' y hy' ((h1 x y).1 e)]
  · obtain ⟨y, rfl⟩ := φ.surjective y
    obtain ⟨x, hx, e⟩ := h.2.2 y ((h2 y).1 hy)
    exact ⟨φ x, Finset.mem_map_of_mem _ hx, (h1 y x).2 e⟩

variable {H : Sesq V} {α : V → ℂ}

/- English proof (translation)
Unfold `brk chi`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem brk_eq (y t : V) : brk H y t = chi H t y := by
  unfold brk chi
  congr 1
  ring

/- English proof (translation)
Establish `h1` using `alpha_sq hs (A.add_mem hx hy)`. Establish `h2` using `alpha_sq hs hx`. Establish `h3` using `alpha_sq hs hy`. Rewrite `h1` using `[hs.2 x hx y hy]`. Establish `h4 : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) = 1`.

Take the linear combination `h1 - (α y * α y * h2 + h3) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) ^ 2`. Rewrite `h4` using `[← Complex.exp_add]`. Rewrite using `[chi, Complex.exp_neg, ← inv_one, ← h4]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem int_of_semi {A : AddSubgroup V} (hs : IsSemiChar H A α) {x y : V} (hx : x ∈ A) (hy : y ∈ A) : chi H x y = 1 := by
  have h1 := alpha_sq hs (A.add_mem hx hy)
  have h2 := alpha_sq hs hx
  have h3 := alpha_sq hs hy
  rw [hs.2 x hx y hy] at h1
  have h4 : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) = 1 := by
    linear_combination h1 - (α y * α y * h2 + h3) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) ^ 2
  rw [← Complex.exp_add] at h4
  rw [chi, Complex.exp_neg, ← inv_one, ← h4]
  congr 2
  ring

/- English proof (translation)
Establish `h` using `int_of_semi hs hx hy`. Establish `e : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) = Complex.exp (-(Real.pi * Complex.I * (altE H x y : ℂ)))`. Rewrite using `[← mul_one (Complex.exp ((Real.pi : ℂ) * _ * _)), ← h, chi, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[opU_mul, opU_opU hH, hs.2 x hx y hy, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem w_add (hH : IsHerm H) {A : AddSubgroup V} (hs : IsSemiChar H A α) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (F : V → ℂ) (z : V) : α (x + y) * opU H (x + y) F z = α x * opU H x (fun w => α y * opU H y F w) z := by
  have h := int_of_semi hs hx hy
  have e : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) =
      Complex.exp (-(Real.pi * Complex.I * (altE H x y : ℂ))) := by
    rw [← mul_one (Complex.exp ((Real.pi : ℂ) * _ * _)), ← h, chi, ← Complex.exp_add]
    congr 1
    ring
  rw [opU_mul, opU_opU hH, hs.2 x hx y hy, e]
  ring

/- English proof (translation)
The claim follows from `Complex.exp_ne_zero _`.
-/
theorem chi_ne (x y : V) : chi H x y ≠ 0 := Complex.exp_ne_zero _

/- English proof (translation)
Establish `tU : ∀ x F w, opU H (T x) F (T w) = opU H x (fun v => F (T v)) w` using `fun x F w => by`. Simplify using `only [opU, tH, map_add]`. Establish `tc : ∀ x y, chi H (T x) (T y) = chi H x y` using `fun x y => by simp only [chi, altE, tH]`. Establish `invA : ∀ x ∈ A, ∀ y ∈ B, ∀ t ∈ Λ ⊓ A, ∀ l ∈ Λ ⊓ A, l ∈ B → Φ (t + l - x) * (brk H y (t + l))⁻¹ = Φ (t - x) * (brk H y t)⁻¹` using `fun x hx y hy t ht l hl hl' => by`. Rewrite using `[add_sub_right_comm, hΦ _ (A.sub_mem ht.2 hx) l hl.2 hl', brk_eq, brk_eq, chi_add_left, int_of_semi hB hl' hy, mul_one]`.

Establish `hatT : ∀ x ∈ A, ∀ y ∈ B, hatS H vol SA (fun s => Φ (s - T x)) (T y) = k * hatS H vol SA (fun s => Φ (s - x)) y`. Introduce `x hx y hy`. Unfold `hatS`. Rewrite using `[← sum_reps_equiv hSA T.toEquiv (fun t => and_congr (tΛ t) (tA t)) (fun t u => by`. Express the relevant statement in the definitionally equal form `T t - T u ∈ B ↔ _`.

Rewrite using `[← map_sub, tB]) (fun t => Φ (t - T x) * (brk H (T y) t)⁻¹) (invA _ ((tA x).2 hx) _ ((tB y).2 hy))]`. Establish `: ∀ t, Φ (T.toEquiv t - T x) * (brk H (T y) (T.toEquiv t))⁻¹ = k * (Φ (t - x) * (brk H y t)⁻¹)` using `fun t => by`. Express the relevant statement in the definitionally equal form `Φ (T t - T x) * (brk H (T y) (T t))⁻¹ = _`. Rewrite using `[← map_sub, tΦ, brk_eq, brk_eq, tc, mul_assoc]`. Simplify using `only [this, ← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hatL : ∀ x ∈ A, ∀ y ∈ B, ∀ l ∈ A, l ∈ Λ → hatS H vol SA (fun s => Φ (s - (x + l))) y = (chi H l y)⁻¹ * hatS H vol SA (fun s => Φ (s - x)) y`. Introduce `x hx y hy l hl hl'`. Unfold `hatS`. Rewrite using `[← sum_reps_equiv hSA (Equiv.addRight l) (fun t => (Λ ⊓ A).add_mem_cancel_right ⟨hl', hl⟩) (fun t u => by simp) (fun t => Φ (t - (x + l)) * (brk H y t)⁻¹) (invA _ (A.add_mem hx hl) _ hy)]`.

Establish `: ∀ t, Φ (Equiv.addRight l t - (x + l)) * (brk H y (Equiv.addRight l t))⁻¹ = (chi H l y)⁻¹ * (Φ (t - x) * (brk H y t)⁻¹)` using `fun t => by`. Rewrite using `[Equiv.coe_addRight, add_sub_add_right_eq_sub, brk_eq, brk_eq, chi_add_left, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.

Establish `invB : ∀ (Ψ : V → ℂ) w, ∀ y ∈ B, ∀ l ∈ B, l ∈ Λ → hatS H vol SA Ψ (y + l) * α (y + l) * opU H (y + l) θ w = hatS H vol SA Ψ y * α y * opU H y θ w`. Introduce `Ψ w y hy l hl hl'`. Establish `e1 : hatS H vol SA Ψ (y + l) = hatS H vol SA Ψ y`. Unfold `hatS`. Use `congr 2`.

Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Rewrite using `[brk_eq, brk_eq, chi_add_right, int_of_semi hΛ (hSA.1 t ht).1 hl', mul_one]`. Rewrite using `[e1, mul_assoc, w_add hH hB hy hl, funext (hθ l hl'), mul_assoc]`. Establish `xiT : ∀ x ∈ A, ∀ w, xiS H α vol SA SB (fun s => Φ (s - T x)) θ (T w) = k * xiS H α vol SA SB (fun s => Φ (s - x)) θ w`. Introduce `x hx w`.

Unfold `xiS sumU`. Rewrite using `[← sum_reps_equiv hSB T.toEquiv tB (fun t u => by`. Express the relevant statement in the definitionally equal form `T t - T u ∈ Λ ↔ _`. Rewrite using `[← map_sub, tΛ]) _ (invB _ _), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `hatS H vol SA _ (T y) * α (T y) * opU H (T y) θ (T w) = _`. Rewrite using `[hatT x hx y (hSB.1 y hy), tα, tU, funext tθ]`. Expand and normalize the polynomial expressions, which then agree. Establish `invX : ∀ w, ∀ x ∈ A, ∀ l ∈ A, l ∈ Λ → α (x + l) * opU H (x + l) (xiS H α vol SA SB (fun s => Φ (s - (x + l))) θ) w = α x * opU H x (xiS H α vol SA SB (fun s => Φ (s - x)) θ) w`. Introduce `w x hx l hl hl'`.

Rewrite using `[w_add hH hA hx hl]`. Use `congr 2`. Use function extensionality and compare the values at `v`. Unfold `xiS sumU`. Rewrite using `[opU_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[opU_mul, opU_comm hH, hatL x hx y (hSB.1 y hy) l hl hl', opU_of_fixed hΛ hθ hl', opU_mul]`. Establish `h1` using `alpha_sq hΛ hl'`. Establish `h2` using `chi_ne (H := H) l y`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(hatS H vol SA (fun s => Φ (s - x)) y * α y * opU H y θ v) * h1`. Unfold `xiL`. Rewrite using `[← sum_reps_equiv hX T.toEquiv tA (fun t u => by`. Express the relevant statement in the definitionally equal form `T t - T u ∈ Λ ↔ _`.

Rewrite using `[← map_sub, tΛ]) _ (invX _), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `α (T x) * opU H (T x) (xiS H α vol SA SB (fun s => Φ (s - T x)) θ) (T z) = _`. Rewrite using `[tα, tU, funext (xiT x (hX.1 x hx)), opU_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xiL_stab (hH : IsHerm H) {A B Λ : AddSubgroup V} (hA : IsSemiChar H A α) (hB : IsSemiChar H B α)
    (hΛ : IsSemiChar H Λ α) {SX SA SB : Finset V} (hX : IsReps Λ A SX) (hSA : IsReps B (Λ ⊓ A) SA) (hSB : IsReps Λ B SB)
    (vol : ℝ) {θ : V → ℂ} (hθ : θ ∈ fixedBy H α Λ) {Φ : V → ℂ} (hΦ : InvOn A B Φ) (T : V ≃+ V)
    (tH : ∀ x y, H (T x) (T y) = H x y) (tα : ∀ x, α (T x) = α x) (tA : ∀ x, T x ∈ A ↔ x ∈ A) (tB : ∀ x, T x ∈ B ↔ x ∈ B)
    (tΛ : ∀ x, T x ∈ Λ ↔ x ∈ Λ) (tθ : ∀ z, θ (T z) = θ z) (k : ℂ) (tΦ : ∀ x, Φ (T x) = k * Φ x) (z : V) :
    xiL H α vol SX SA SB Φ θ (T z) = k * xiL H α vol SX SA SB Φ θ z := by
  have tU : ∀ x F w, opU H (T x) F (T w) = opU H x (fun v => F (T v)) w := fun x F w => by
    simp only [opU, tH, map_add]
  have tc : ∀ x y, chi H (T x) (T y) = chi H x y := fun x y => by simp only [chi, altE, tH]
  have invA : ∀ x ∈ A, ∀ y ∈ B, ∀ t ∈ Λ ⊓ A, ∀ l ∈ Λ ⊓ A, l ∈ B →
      Φ (t + l - x) * (brk H y (t + l))⁻¹ = Φ (t - x) * (brk H y t)⁻¹ := fun x hx y hy t ht l hl hl' => by
    rw [add_sub_right_comm, hΦ _ (A.sub_mem ht.2 hx) l hl.2 hl', brk_eq, brk_eq, chi_add_left, int_of_semi hB hl' hy, mul_one]
  have hatT : ∀ x ∈ A, ∀ y ∈ B, hatS H vol SA (fun s => Φ (s - T x)) (T y) = k * hatS H vol SA (fun s => Φ (s - x)) y := by
    intro x hx y hy
    unfold hatS
    rw [← sum_reps_equiv hSA T.toEquiv (fun t => and_congr (tΛ t) (tA t)) (fun t u => by
      change T t - T u ∈ B ↔ _
      rw [← map_sub, tB]) (fun t => Φ (t - T x) * (brk H (T y) t)⁻¹) (invA _ ((tA x).2 hx) _ ((tB y).2 hy))]
    have : ∀ t, Φ (T.toEquiv t - T x) * (brk H (T y) (T.toEquiv t))⁻¹ = k * (Φ (t - x) * (brk H y t)⁻¹) := fun t => by
      change Φ (T t - T x) * (brk H (T y) (T t))⁻¹ = _
      rw [← map_sub, tΦ, brk_eq, brk_eq, tc, mul_assoc]
    simp only [this, ← Finset.mul_sum]
    ring
  have hatL : ∀ x ∈ A, ∀ y ∈ B, ∀ l ∈ A, l ∈ Λ →
      hatS H vol SA (fun s => Φ (s - (x + l))) y = (chi H l y)⁻¹ * hatS H vol SA (fun s => Φ (s - x)) y := by
    intro x hx y hy l hl hl'
    unfold hatS
    rw [← sum_reps_equiv hSA (Equiv.addRight l) (fun t => (Λ ⊓ A).add_mem_cancel_right ⟨hl', hl⟩) (fun t u => by simp)
      (fun t => Φ (t - (x + l)) * (brk H y t)⁻¹) (invA _ (A.add_mem hx hl) _ hy)]
    have : ∀ t, Φ (Equiv.addRight l t - (x + l)) * (brk H y (Equiv.addRight l t))⁻¹ =
        (chi H l y)⁻¹ * (Φ (t - x) * (brk H y t)⁻¹) := fun t => by
      rw [Equiv.coe_addRight, add_sub_add_right_eq_sub, brk_eq, brk_eq, chi_add_left, mul_inv]
      ring
    simp only [this, ← Finset.mul_sum]
    ring
  have invB : ∀ (Ψ : V → ℂ) w, ∀ y ∈ B, ∀ l ∈ B, l ∈ Λ →
      hatS H vol SA Ψ (y + l) * α (y + l) * opU H (y + l) θ w = hatS H vol SA Ψ y * α y * opU H y θ w := by
    intro Ψ w y hy l hl hl'
    have e1 : hatS H vol SA Ψ (y + l) = hatS H vol SA Ψ y := by
      unfold hatS
      congr 2
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [brk_eq, brk_eq, chi_add_right, int_of_semi hΛ (hSA.1 t ht).1 hl', mul_one]
    rw [e1, mul_assoc, w_add hH hB hy hl, funext (hθ l hl'), mul_assoc]
  have xiT : ∀ x ∈ A, ∀ w, xiS H α vol SA SB (fun s => Φ (s - T x)) θ (T w) = k * xiS H α vol SA SB (fun s => Φ (s - x)) θ w := by
    intro x hx w
    unfold xiS sumU
    rw [← sum_reps_equiv hSB T.toEquiv tB (fun t u => by
      change T t - T u ∈ Λ ↔ _
      rw [← map_sub, tΛ]) _ (invB _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    change hatS H vol SA _ (T y) * α (T y) * opU H (T y) θ (T w) = _
    rw [hatT x hx y (hSB.1 y hy), tα, tU, funext tθ]
    ring
  have invX : ∀ w, ∀ x ∈ A, ∀ l ∈ A, l ∈ Λ →
      α (x + l) * opU H (x + l) (xiS H α vol SA SB (fun s => Φ (s - (x + l))) θ) w =
        α x * opU H x (xiS H α vol SA SB (fun s => Φ (s - x)) θ) w := by
    intro w x hx l hl hl'
    rw [w_add hH hA hx hl]
    congr 2
    funext v
    unfold xiS sumU
    rw [opU_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    beta_reduce
    rw [opU_mul, opU_comm hH, hatL x hx y (hSB.1 y hy) l hl hl', opU_of_fixed hΛ hθ hl', opU_mul]
    have h1 := alpha_sq hΛ hl'
    have h2 := chi_ne (H := H) l y
    field_simp
    linear_combination (hatS H vol SA (fun s => Φ (s - x)) y * α y * opU H y θ v) * h1
  unfold xiL
  rw [← sum_reps_equiv hX T.toEquiv tA (fun t u => by
      change T t - T u ∈ Λ ↔ _
      rw [← map_sub, tΛ]) _ (invX _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  change α (T x) * opU H (T x) (xiS H α vol SA SB (fun s => Φ (s - T x)) θ) (T z) = _
  rw [tα, tU, funext (xiT x (hX.1 x hx)), opU_mul]
  ring

end GlobalTheory.KerLaw
