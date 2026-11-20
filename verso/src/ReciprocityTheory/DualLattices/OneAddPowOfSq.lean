import ReciprocityTheory.DualLattices.NsetExpInjectiveSurjective

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

/- English proof (translation)
Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp [BX.ev]`. Consider the case `tmul g r => simp [BX.ev]`. Consider the case `add a b ha hb`. Simplify using `only [BX.ev, map_add] at ha hb ⊢`.

Rewrite using `[ha, hb]`.
-/
lemma BX.ev_map (B : BX R₀) {R S : LAlg R₀} (f : (R : Type u) →ₐ[R₀] (S : Type u))
    (h : B.gg →ₗ[R₀] (R : Type u)) (v : B.gg ⊗[R₀] (R : Type u)) :
    f (B.ev h v) = B.ev (f.toLinearMap ∘ₗ h) (LinearMap.lTensor B.gg f.toLinearMap v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul g r => simp [BX.ev]
  | add a b ha hb =>
    simp only [BX.ev, map_add] at ha hb ⊢
    rw [ha, hb]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ih]`. Use `push_cast`.

Take the linear combination `(k : S) * ha`.
-/
private lemma one_add_pow_of_sq {S : Type*} [CommRing S] (a : S) (ha : a * a = 0) (k : ℕ) :
    (1 + a) ^ k = 1 + k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : S) * ha

/- English proof (translation)
Introduce `Dp ι τ E ht bt h1 h2 h3 i j`. Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `Tw.sep` to reduce the goal to its premises. Introduce `n`. Take `⟨k, hk, hpair⟩` from `h1 i j n`.

Take `⟨thi, wi, hmi, hNi, hwi⟩` from `h3 i n`. Take `⟨thj, wj, hmj, hNj, hwj⟩` from `h3 j n`. Establish `hsurjL : Function.Surjective (Tw.π n).1.toLinearMap` using `Tw.surj n`. Take `⟨hsi, hsi_spec⟩` from `Module.projective_lifting_property (Tw.π n).1.toLinearMap ((Tw.q n).1.toLinearMap ∘ₗ ht i) hsurjL`. Take `⟨hsj, hsj_spec⟩` from `Module.projective_lifting_property (Tw.π n).1.toLinearMap ((Tw.q n).1.toLinearMap ∘ₗ ht j) hsurjL`.

Take `⟨-, -, -, -, -, -, hnat, -⟩` from `hB1`. Establish `hpq` using `hnat _ _ (Tw.q n) _ _ _ _ hpair`. Rewrite `hpq` using `[← hmi, ← hmj]`. Establish `hB3'` using `hB3 (Tw.R' n) (Tw.R n) (Tw.π n) (Tw.ξ n) (Dp n) (p ^ (n + 1)) (Tw.surj n) (Tw.ker_eq n) (Tw.ξ_sq n) (Tw.ann n) (Tw.char n) thi thj (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wi) (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wj) h …`. Establish `hev : ∀ (h : B.gg →ₗ[R₀] (Tw.R' n : Type u)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)), B.evK (Tw.π n) h (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) = Tw.ξ n * B.ev h w`.

Introduce `h w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp [BX.evK, BX.ev]`. Consider the case `tmul g r`. Simplify using `[BX.evK, BX.ev, ξmul]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `add a b ha hb`. Simplify using `only [BX.evK, BX.ev, map_add] at ha hb ⊢`. Rewrite using `[ha, hb, mul_add]`. Rewrite `hB3'` using `[hev, hev]`.

Establish `hpow : ((Tw.zh n ^ k : (Tw.R' n : Type u)ˣ) : (Tw.R' n : Type u)) ^ (p ^ (n + 1)) = 1 + (k : (Tw.R' n : Type u)) * (Tw.cp n * Tw.ξ n)`. Rewrite using `[Units.val_pow_eq_pow_val, pow_right_comm, Tw.zh_pow n]`. Apply `one_add_pow_of_sq` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hξ : ((k : (Tw.R' n : Type u)) * Tw.cp n - (B.ev hsj wi - B.ev hsi wj)) * Tw.ξ n = 0`.

Establish `hh` using `hB3'.symm.trans hpow`. Take the linear combination `-hh`. Establish `hmem` using `Tw.ann n _ hξ`. Rewrite `hmem` using `[← Tw.ker_eq n, RingHom.mem_ker]`. Establish `e1 : (Tw.π n).1 (B.ev hsj wi) = (Tw.q n).1 (B.ev (ht j) (bt i))`.

Rewrite using `[BX.ev_map B (Tw.π n).1 hsj wi, hsj_spec, hwi, ← BX.ev_map B (Tw.q n).1 (ht j) (bt i)]`. Establish `e2 : (Tw.π n).1 (B.ev hsi wj) = (Tw.q n).1 (B.ev (ht i) (bt j))`. Rewrite using `[BX.ev_map B (Tw.π n).1 hsi wj, hsi_spec, hwj, ← BX.ev_map B (Tw.q n).1 (ht i) (bt j)]`. Simplify using `only [map_sub, map_mul, map_natCast, Tw.cp_spec, e1, e2] at hmem`. Rewrite using `[map_sub, map_sub, map_mul, hk]`.

Take the linear combination `hmem`.
-/
theorem b4 (B : BX R₀) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) {p : ℕ}
    (Tw : ATower R₀ p) : NsetExpInjectiveSurjective B Tw := by
  intro Dp ι τ E ht bt h1 h2 h3 i j
  apply sub_eq_zero.mp
  apply Tw.sep
  intro n
  obtain ⟨k, hk, hpair⟩ := h1 i j n
  obtain ⟨thi, wi, hmi, hNi, hwi⟩ := h3 i n
  obtain ⟨thj, wj, hmj, hNj, hwj⟩ := h3 j n
  have hsurjL : Function.Surjective (Tw.π n).1.toLinearMap := Tw.surj n
  obtain ⟨hsi, hsi_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht i) hsurjL
  obtain ⟨hsj, hsj_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht j) hsurjL
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  have hpq := hnat _ _ (Tw.q n) _ _ _ _ hpair
  rw [← hmi, ← hmj] at hpq
  have hB3' := hB3 (Tw.R' n) (Tw.R n) (Tw.π n) (Tw.ξ n) (Dp n) (p ^ (n + 1)) (Tw.surj n)
    (Tw.ker_eq n) (Tw.ξ_sq n) (Tw.ann n) (Tw.char n) thi thj
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wi)
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wj)
    hsi hsj (Tw.zh n ^ k) _ hNi hNj
    (by rw [hmi, hsi_spec]; exact h2 i n) (by rw [hmj, hsj_spec]; exact h2 j n) hpq
    (Units.ext (by simp [Tw.ζ_spec]))
  have hev : ∀ (h : B.gg →ₗ[R₀] (Tw.R' n : Type u)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.evK (Tw.π n) h (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) =
        Tw.ξ n * B.ev h w := by
    intro h w
    induction w using TensorProduct.induction_on with
    | zero => simp [BX.evK, BX.ev]
    | tmul g r =>
      simp [BX.evK, BX.ev, ξmul]
      ring
    | add a b ha hb =>
      simp only [BX.evK, BX.ev, map_add] at ha hb ⊢
      rw [ha, hb, mul_add]
  rw [hev, hev] at hB3'
  have hpow : ((Tw.zh n ^ k : (Tw.R' n : Type u)ˣ) : (Tw.R' n : Type u)) ^ (p ^ (n + 1)) =
      1 + (k : (Tw.R' n : Type u)) * (Tw.cp n * Tw.ξ n) := by
    rw [Units.val_pow_eq_pow_val, pow_right_comm, Tw.zh_pow n]
    apply one_add_pow_of_sq
    calc Tw.cp n * Tw.ξ n * (Tw.cp n * Tw.ξ n) = Tw.cp n * Tw.cp n * (Tw.ξ n * Tw.ξ n) := by ring
      _ = 0 := by rw [Tw.ξ_sq n, mul_zero]
  have hξ : ((k : (Tw.R' n : Type u)) * Tw.cp n - (B.ev hsj wi - B.ev hsi wj)) * Tw.ξ n = 0 := by
    have hh := hB3'.symm.trans hpow
    linear_combination -hh
  have hmem := Tw.ann n _ hξ
  rw [← Tw.ker_eq n, RingHom.mem_ker] at hmem
  have e1 : (Tw.π n).1 (B.ev hsj wi) = (Tw.q n).1 (B.ev (ht j) (bt i)) := by
    rw [BX.ev_map B (Tw.π n).1 hsj wi, hsj_spec, hwi, ← BX.ev_map B (Tw.q n).1 (ht j) (bt i)]
  have e2 : (Tw.π n).1 (B.ev hsi wj) = (Tw.q n).1 (B.ev (ht i) (bt j)) := by
    rw [BX.ev_map B (Tw.π n).1 hsi wj, hsi_spec, hwj, ← BX.ev_map B (Tw.q n).1 (ht i) (bt j)]
  simp only [map_sub, map_mul, map_natCast, Tw.cp_spec, e1, e2] at hmem
  rw [map_sub, map_sub, map_mul, hk]
  linear_combination hmem

end ReciprocityTheory.PGsh
