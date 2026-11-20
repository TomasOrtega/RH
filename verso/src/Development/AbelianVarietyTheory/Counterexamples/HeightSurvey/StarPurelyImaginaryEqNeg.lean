import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.DualPairCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a e`. Simplify using `only [cA, sigR]`.

Simplify using the standard rewrite rules. Use `congr 1`. Conclude with `star_star e`.
-/
theorem cA_cA (x : Formalism.L2.Theta.AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    simp only [cA, sigR]
    simp
    congr 1
    exact star_star e

/- English proof (translation)
Simplify using `only [cA, sigR, incA, inclR]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (star e) := by
  simp only [cA, sigR, incA, inclR]
  simp
  rfl

/- English proof (translation)
The claim follows from `V.herm.eq (V.frame i) (V.frame j)`.
-/
theorem gram_star (V : HSp D) (i j) : star (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

section Generic
variable {A : Type} [CommRing A] {m n : ℕ}

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem sum_small (σ : A →+* A) (P : Matrix (Fin m) (Fin m) A) (Q : Matrix (Fin n) (Fin n) A)
    (x y : Matrix (Fin m) (Fin n) A) :
    ∑ i, ∑ j, ∑ k, ∑ l, σ (x i j) * P k i * Q j l * y k l = (x.map σ * Q * yᵀ * P).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `sum_small σ Q P xᵀ yᵀ` as an intermediate fact. Simplify using `only [Matrix.transpose_apply, Matrix.transpose_transpose] at this`. Rewrite using `[← Matrix.transpose_map, ← this, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring` and prove the remaining obligations.
-/
theorem sum_large (σ : A →+* A) (P : Matrix (Fin m) (Fin m) A) (Q : Matrix (Fin n) (Fin n) A)
    (x y : Matrix (Fin m) (Fin n) A) :
    ∑ i, ∑ j, ∑ k, ∑ l, σ (x i j) * P i k * Q l j * y k l = ((x.map σ)ᵀ * P * y * Q).trace := by
  have := sum_small σ Q P xᵀ yᵀ
  simp only [Matrix.transpose_apply, Matrix.transpose_transpose] at this
  rw [← Matrix.transpose_map, ← this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Establish `e : (g.map σ).map σ = g` using `by ext i j; simp [hσ]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`.

Rewrite using `[Matrix.trace_mul_comm, hh, Matrix.mul_assoc _ _ g, hg]`.
-/
theorem inv_small (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P g : Matrix (Fin m) (Fin m) A)
    (Q h : Matrix (Fin n) (Fin n) A) (hg : (g.map σ)ᵀ * P * g = P) (hh : (h.map σ)ᵀ * Q * h = Q)
    (x y : Matrix (Fin m) (Fin n) A) :
    ((g.map σ * x * hᵀ).map σ * Q * (g.map σ * y * hᵀ)ᵀ * P).trace = (x.map σ * Q * yᵀ * P).trace := by
  have e : (g.map σ).map σ = g := by ext i j; simp [hσ]
  rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  calc _ = (g * (x.map σ * ((h.map σ)ᵀ * Q * h) * yᵀ * ((g.map σ)ᵀ * P))).trace := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Matrix.trace_mul_comm, hh, Matrix.mul_assoc _ _ g, hg]

/- English proof (translation)
Establish `c` using `inv_small σ hσ _ _ _ _ hh hg xᵀ yᵀ`. Simplify using `only [Matrix.transpose_transpose, Matrix.transpose_map] at c`. Rewrite using `[← c]`. Use `congr 1`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map, Matrix.mul_assoc]`.
-/
theorem inv_large (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P g : Matrix (Fin m) (Fin m) A)
    (Q h : Matrix (Fin n) (Fin n) A) (hg : (g.map σ)ᵀ * P * g = P) (hh : (h.map σ)ᵀ * Q * h = Q)
    (x y : Matrix (Fin m) (Fin n) A) :
    (((g * x * (h.map σ)ᵀ).map σ)ᵀ * P * (g * y * (h.map σ)ᵀ) * Q).trace = ((x.map σ)ᵀ * P * y * Q).trace := by
  have c := inv_small σ hσ _ _ _ _ hh hg xᵀ yᵀ
  simp only [Matrix.transpose_transpose, Matrix.transpose_map] at c
  rw [← c]
  congr 1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map,
    Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [map_sum, map_mul, hσ, hP, hQ]`. Establish `a : ∀ f : Fin m → Fin n → Fin m → Fin n → A, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n, f p.1 p.2 q.1 q.2`. Introduce `f`. Simplify using `only [Fintype.sum_prod_type]`. Rewrite using `[a, a, Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem herm_small (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P : Fin m → Fin m → A) (Q : Fin n → Fin n → A)
    (hP : ∀ i k, σ (P i k) = P k i) (hQ : ∀ i k, σ (Q i k) = Q k i) (x y : Matrix (Fin m) (Fin n) A) :
    σ (∑ i, ∑ j, ∑ k, ∑ l, σ (x i j) * P k i * Q j l * y k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, σ (y i j) * P k i * Q j l * x k l := by
  simp only [map_sum, map_mul, hσ, hP, hQ]
  have a : ∀ f : Fin m → Fin n → Fin m → Fin n → A, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l =
      ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n, f p.1 p.2 q.1 q.2 := by
    intro f; simp only [Fintype.sum_prod_type]
  rw [a, a, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Generic

/- English proof (translation)
The claim follows from `g.2`.
-/
theorem mt_unit (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2

/- English proof (translation)
Unfold `hHom`. Use `split_ifs with hr`. Conclude with `herm_small (cA D) cA_cA (fun i k => incA D (V.gram i k)) (fun i k => incA D (W.gram i k)) (fun i k => by rw [cA_incA, gram_star]) (fun i k => by rw [cA_incA, gram_star]) x y`. Conclude with `herm_small (cA D) cA_cA (fun i k => incA D (V.gram k i)) (fun i k => incA D (W.gram k i)) (fun i k => by rw [cA_incA, gram_star]) (fun i k => by rw [cA_incA, gram_star]) x y`.
-/
theorem hHom_herm (V W : HSp D) (x y : WA V W) : cA D (hHom V W x y) = hHom V W y x := by
  unfold hHom
  split_ifs with hr
  · exact herm_small (cA D) cA_cA (fun i k => incA D (V.gram i k)) (fun i k => incA D (W.gram i k))
      (fun i k => by rw [cA_incA, gram_star]) (fun i k => by rw [cA_incA, gram_star]) x y
  · exact herm_small (cA D) cA_cA (fun i k => incA D (V.gram k i)) (fun i k => incA D (W.gram k i))
      (fun i k => by rw [cA_incA, gram_star]) (fun i k => by rw [cA_incA, gram_star]) x y

/- English proof (translation)
Take `⟨h1, h2, v, ε, ⟨α, hε, hv, -⟩, h3⟩` from `he`. Introduce `h`. Rewrite `h2` using `[h, h1]`. Rewrite `h3` using `[h2, map_zero, add_zero]`. Establish `hinj : Function.Injective (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D))` using `Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective`.

Establish `: ε = 0` using `hinj (by rw [← h3, map_zero])`. Establish `hα : α = 0`. Rewrite `this` using `[hε]`. Conclude with `congrArg Prod.snd this`. Rewrite `hv` using `[hα, map_zero]`.

Conclude with `zero_ne_one hv`.
-/
theorem split_ne (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e) : cA D e ≠ e := by
  obtain ⟨h1, h2, v, ε, ⟨α, hε, hv, -⟩, h3⟩ := he
  intro h
  rw [h, h1] at h2
  rw [h2, map_zero, add_zero] at h3
  have hinj : Function.Injective (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have : ε = 0 := hinj (by rw [← h3, map_zero])
  have hα : α = 0 := by
    rw [hε] at this
    exact congrArg Prod.snd this
  rw [hα, map_zero] at hv
  exact zero_ne_one hv

/- English proof (translation)
Set `f : Formalism.L2.Theta.AE D →ₐ[AF D.host.F] Formalism.L2.Theta.AE D` to `Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig`. Set `e : Formalism.L2.Theta.AE D ≃ₐ[AF D.host.F] Formalism.L2.Theta.AE D` to `AlgEquiv.ofAlgHom f f (AlgHom.ext fun x => cA_cA x) (AlgHom.ext fun x => cA_cA x)`. Conclude with `Algebra.trace_eq_of_algEquiv e x`.
-/
theorem trace_cA (x : Formalism.L2.Theta.AE D) :
    Algebra.trace (AF D.host.F) (Formalism.L2.Theta.AE D) (cA D x) = Algebra.trace (AF D.host.F) (Formalism.L2.Theta.AE D) x := by
  let f : Formalism.L2.Theta.AE D →ₐ[AF D.host.F] Formalism.L2.Theta.AE D :=
    Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig
  let e : Formalism.L2.Theta.AE D ≃ₐ[AF D.host.F] Formalism.L2.Theta.AE D :=
    AlgEquiv.ofAlgHom f f (AlgHom.ext fun x => cA_cA x) (AlgHom.ext fun x => cA_cA x)
  exact Algebra.trace_eq_of_algEquiv e x

/- English proof (translation)
Establish `hs : star D.host.sqrtMinusD = -D.host.sqrtMinusD`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Establish `h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`. Use `D.host.isCMField_hostE` as an intermediate fact. Establish `h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD)` using `NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD`.

Rewrite using `[h2, map_neg, h1]`. Simplify using the standard rewrite rules. Unfold `Host.xi0`. Rewrite using `[star_div₀, star_mul', hs, star_natCast, star_neg, star_one, mul_neg, div_neg]`.
-/
theorem star_purely_imaginary_eq_neg (D : D7) : star D.host.xi0 = -D.host.xi0 := by
  have hs : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have := D.host.isCMField_hostE
    have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
      NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
    rw [h2, map_neg, h1]
    simp
  unfold Host.xi0
  rw [star_div₀, star_mul', hs, star_natCast, star_neg, star_one, mul_neg, div_neg]

/- English proof (translation)
Unfold `sympl`. Rewrite using `[← trace_cA, map_mul, cA_incA, star_purely_imaginary_eq_neg, hHom_herm, map_neg, neg_mul, map_neg]`.
-/
theorem sympl_skew (V W : HSp D) (x y : WA V W) :
    sympl V W y x = -sympl V W x y := by
  unfold sympl
  rw [← trace_cA, map_mul, cA_incA, star_purely_imaginary_eq_neg, hHom_herm, map_neg, neg_mul, map_neg]

/- English proof (translation)
Unfold `symplH sympl hHom`. Apply the tactic sequence `split_ifs <;> simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]`.
-/
theorem symplH_add_left (V W : HSp D) (x x' y : WA V W) :
    symplH V W (x + x') y = symplH V W x y + symplH V W x' y := by
  unfold symplH sympl hHom
  split_ifs <;> simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Unfold `symplH sympl hHom`. Apply the tactic sequence `split_ifs <;> simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]`.
-/
theorem symplH_add_right (V W : HSp D) (x y y' : WA V W) :
    symplH V W x (y + y') = symplH V W x y + symplH V W x y' := by
  unfold symplH sympl hHom
  split_ifs <;> simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `only [Heisenberg₂, Pi.smul_apply, smul_eq_mul, symplH_add_left, symplH_add_right, AddChar.map_add_eq_mul, add_assoc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heis_heis (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (w w' : WA V W) (f : WA V W → ℂ) :
    Heisenberg₂ ψ V W w (Heisenberg₂ ψ V W w' f) = ψ (symplH V W w w') • Heisenberg₂ ψ V W (w + w') f := by
  funext u
  simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul, symplH_add_left, symplH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

/- English proof (translation)
Simplify using `only [Heisenberg₂]`. Rewrite using `[add_assoc, hf, symplH_add_left, symplH_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heis_quasi (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (w₀ : WA V W) (f : WA V W → ℂ)
    (hf : ∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) (γ w) :
    Heisenberg₂ ψ V W w₀ f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * Heisenberg₂ ψ V W w₀ f w := by
  simp only [Heisenberg₂]
  rw [add_assoc, hf, symplH_add_left, symplH_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 2
  ring

end GlobalTheory.DualPairCheck
