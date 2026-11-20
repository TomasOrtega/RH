import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.MomOne.Frame

variable {g : ℕ}

/- English proof (translation)
Simplify using `only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring` and prove the remaining obligations.
-/
theorem hf_sum_left {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm (∑ i, z i • x i) w = ∑ i, z i * hf Hm (x i) w := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Simplify using `only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring` and prove the remaining obligations.
-/
theorem hf_sum_right {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * hf Hm w (x i) := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Simplify using `only [beta, hf_sum_left, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem beta_sum_left {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm (∑ i, z i • x i) w = ∑ i, z i * beta d Hm (x i) w := by
  simp only [beta, hf_sum_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Simplify using `only [beta, hf_sum_right, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem beta_sum_right {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * beta d Hm w (x i) := by
  simp only [beta, hf_sum_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

section
variable {d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {x : Fin g → Fin g → ℂ} {a : Fin g → ℕ}

/- English proof (translation)
Simplify using `[beta_sum_left, hx]`.
-/
theorem beta_coord (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z : Fin g → ℂ) (j : Fin g) :
    beta d Hm (∑ i, z i • x i) (x j) = z j * a j := by
  simp [beta_sum_left, hx]

/- English proof (translation)
Rewrite using `[beta_sum_right]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [beta_coord hx]; ring`.
-/
theorem beta_frame (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * (z i * conj (w i)) := by
  rw [beta_sum_right]
  exact Finset.sum_congr rfl fun i _ => by rw [beta_coord hx]; ring

/- English proof (translation)
Establish `hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0`. Establish `: Real.sqrt d ≠ 0` using `by positivity`. Conclude with `this` after adjusting the coercions. Establish `h` using `beta_frame hx z w`. Establish `e : hf Hm (∑ i, z i • x i) (∑ i, w i • x i) = ((2 / Real.sqrt d : ℝ) : ℂ) * beta d Hm (∑ i, z i • x i) (∑ i, w i • x i)`.

Rewrite using `[beta]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, h, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [h1]; ring`.
-/
theorem hf_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    hf Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 d (z i) (w i) := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : Real.sqrt d ≠ 0 := by positivity
    exact_mod_cast this
  have h := beta_frame hx z w
  have e : hf Hm (∑ i, z i • x i) (∑ i, w i • x i) =
      ((2 / Real.sqrt d : ℝ) : ℂ) * beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) := by
    rw [beta]; push_cast; field_simp
  rw [e, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1]; ring

/- English proof (translation)
Establish `ha' : ∀ i, (a i : ℂ) ≠ 0` using `fun i => by exact_mod_cast (ha i).ne'`. Set `L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `Fintype.linearCombination ℂ x`. Establish `hL : ∀ z, L z = ∑ i, z i • x i` using `fun z => Fintype.linearCombination_apply _ _ _`. Establish `hinj : Function.Injective L`. Introduce `z w h`.

Use function extensionality and compare the values at `j`. Establish `h1` using `beta_coord hx z j`. Establish `h2` using `beta_coord hx w j`. Rewrite `h1`, `h2` using `[← hL]`. Rewrite `h1` using `[h, h2]`.

Conclude with `(mul_right_cancel₀ (ha' j) h1).symm`. Take `⟨z, rfl⟩` from `(LinearMap.injective_iff_surjective.1 hinj) v`. Rewrite using `[hL]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[beta_coord hx, mul_div_cancel_right₀ _ (ha' i)]`.
-/
theorem expand (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (ha : ∀ i, 0 < a i)
    (v : Fin g → ℂ) : v = ∑ i, (beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have ha' : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).ne'
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ x
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have hinj : Function.Injective L := by
    intro z w h
    funext j
    have h1 := beta_coord hx z j
    have h2 := beta_coord hx w j
    rw [← hL] at h1 h2
    rw [h, h2] at h1
    exact (mul_right_cancel₀ (ha' j) h1).symm
  obtain ⟨z, rfl⟩ := (LinearMap.injective_iff_surjective.1 hinj) v
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [beta_coord hx, mul_div_cancel_right₀ _ (ha' i)]

/- English proof (translation)
Establish `e : (∑ i, z i • x i) + ∑ i, t i • x i = ∑ i, (z + t) i • x i`. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Rewrite using `[opU, e, hG, hf_frame hd hx, hf_frame hd hx, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [U1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_assoc]`.

Use `congr 3`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem opU_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opU Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 d (t i) (f j i) (z i) ^ a i := by
  have e : (∑ i, z i • x i) + ∑ i, t i • x i = ∑ i, (z + t) i • x i := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [opU, e, hG, hf_frame hd hx, hf_frame hd hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [U1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Pi.add_apply,
    Finset.mul_sum, ← Finset.sum_sub_distrib, mul_assoc]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Establish `e : (((beta d Hm (∑ i, t i • x i) (∑ i, t i • x i)).re : ℝ) : ℂ) = ∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ)`. Rewrite using `[beta_frame hx]`. Simplify using `only [Complex.mul_conj]`. Establish `: (∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ)) = ((∑ i, (a i : ℝ) * Complex.normSq (t i) : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this, Complex.ofReal_re]`.

Rewrite using `[opW, opU_frame hd hx c f G hG, e, Finset.mul_sum _ (fun j => c j * _)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [W1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Finset.mul_sum]`. Rewrite using `[mul_left_comm]`. Use `congr 3`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem opW_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opW d Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 d (t i) (f j i) (z i) ^ a i := by
  have e : (((beta d Hm (∑ i, t i • x i) (∑ i, t i • x i)).re : ℝ) : ℂ) =
      ∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ) := by
    rw [beta_frame hx]
    simp only [Complex.mul_conj]
    have : (∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ)) = ((∑ i, (a i : ℝ) * Complex.normSq (t i) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  rw [opW, opU_frame hd hx c f G hG, e, Finset.mul_sum _ (fun j => c j * _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [W1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Finset.mul_sum]
  rw [mul_left_comm]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

end

/- English proof (translation)
Set `L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)` to `LinearMap.toContinuousLinearMap (Fintype.linearCombination ℂ x)`. Establish `hL : ∀ z, L z = ∑ i, z i • x i` using `fun z => Fintype.linearCombination_apply _ _ _`. Establish `e : (fun z : Fin g → ℂ => G (∑ i, z i • x i)) = G ∘ L`. Use function extensionality and compare the values at `z`. Simplify using `[hL]`.

Rewrite using `[e, L.iteratedFDeriv_comp_right hG 0 le_top, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, jetV]`. Simplify using `only [hL]`.
-/
theorem jetV_frame (x : Fin g → Fin g → ℂ) (G : (Fin g → ℂ) → ℂ) (hG : ContDiff ℂ ⊤ G) (k : ℕ)
    (ys : Fin k → Fin g → ℂ) :
    jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys := by
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (Fintype.linearCombination ℂ x)
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have e : (fun z : Fin g → ℂ => G (∑ i, z i • x i)) = G ∘ L := by
    funext z; simp [hL]
  rw [e, L.iteratedFDeriv_comp_right hG 0 le_top, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, jetV]
  simp only [hL]

/- English proof (translation)
Introduce `_ _ x _ hd hx ha` and use `⟨expand hx ha, hf_frame hd hx, fun _ c f G hG t z => ⟨opU_frame hd hx c f G hG t z, opW_frame hd hx c f G hG t z⟩, jetV_frame x⟩`.
-/
theorem coord : ∀ (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), 0 < S.d → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i) → (∀ v : Fin g → ℂ, v = ∑ i, (beta S.d S.Hm v (x i) / (a i : ℂ)) • x i) ∧ (∀ z w : Fin g → ℂ, hf S.Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 S.d (z i) (w i)) ∧ (∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ), (∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) → ∀ t z : Fin g → ℂ, opU S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 S.d (t i) (f j i) (z i) ^ a i ∧ opW S.d S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 S.d (t i) (f j i) (z i) ^ a i) ∧ ∀ (G : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ G → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ), jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys :=
  fun _ _ x _ hd hx ha =>
    ⟨expand hx ha, hf_frame hd hx,
      fun _ c f G hG t z => ⟨opU_frame hd hx c f G hG t z, opW_frame hd hx c f G hG t z⟩,
      jetV_frame x⟩

end GlobalTheory.MomOne.Frame
