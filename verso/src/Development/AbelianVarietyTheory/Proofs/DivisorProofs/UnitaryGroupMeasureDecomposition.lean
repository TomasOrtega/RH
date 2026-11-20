import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureDetOneFactorNearIdentityLeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.MassUp

/- English proof (translation)
Establish `h0` using `(hI ρ).2`. Establish `h1 : (permM (e ρ))ᵀ * A ρ * mat x (σ ρ) = 1` using `by rw [Matrix.mul_assoc, h0, transpose_mul_permM]`. Establish `h2 : mat x (σ ρ) * ((permM (e ρ))ᵀ * A ρ) = 1` using `mul_eq_one_comm.1 h1`. Use `⟨h1, h2, ?_, by rw [Matrix.mul_assoc, h2]⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, h0, permM_mul_transpose]`.
-/
theorem inv_facts {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) :
    (permM (e ρ))ᵀ * A ρ * mat x (σ ρ) = 1 ∧ mat x (σ ρ) * ((permM (e ρ))ᵀ * A ρ) = 1 ∧
    A ρ * (mat x (σ ρ) * (permM (e ρ))ᵀ) = 1 ∧ mat x (σ ρ) * (permM (e ρ))ᵀ * A ρ = 1 := by
  have h0 := (hI ρ).2
  have h1 : (permM (e ρ))ᵀ * A ρ * mat x (σ ρ) = 1 := by rw [Matrix.mul_assoc, h0, transpose_mul_permM]
  have h2 : mat x (σ ρ) * ((permM (e ρ))ᵀ * A ρ) = 1 := mul_eq_one_comm.1 h1
  refine ⟨h1, h2, ?_, by rw [Matrix.mul_assoc, h2]⟩
  rw [← Matrix.mul_assoc, h0, permM_mul_transpose]

/- English proof (translation)
Take `⟨-, -, h3, h4⟩` from `inv_facts hI ρ`. Use `set B := mat x (σ ρ) * (permM (e ρ))ᵀ`. Establish `hJ` using `GlobalTheory.UpqTopology.jpq_sq (P := p ρ) (Q := q ρ)`. Establish `key : (-(G.map (σ ρ).1)ᵀ) * (B * Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ) = 1`. Rewrite using `[← (hI ρ).1]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[h3, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.Jpq (p ρ) (q ρ)), hJ, Matrix.one_mul, ← Matrix.conjTranspose_mul, h4, Matrix.conjTranspose_one]`. Establish `hd` using `Matrix.det_ne_zero_of_right_inverse key`.

Rewrite `hd` using `[Matrix.det_neg, Matrix.det_transpose]`. Establish `hd' : (G.map (σ ρ).1).det ≠ 0` using `fun h => hd (by rw [h, mul_zero])`. Introduce `h0`. Apply `hd'` to reduce the goal to its premises. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`.
-/
theorem det_ne {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) : G.det ≠ 0 := by
  obtain ⟨-, -, h3, h4⟩ := inv_facts hI ρ
  set B := mat x (σ ρ) * (permM (e ρ))ᵀ
  have hJ := GlobalTheory.UpqTopology.jpq_sq (P := p ρ) (Q := q ρ)
  have key : (-(G.map (σ ρ).1)ᵀ) * (B * Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ) = 1 := by
    rw [← (hI ρ).1]
    calc (A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ * (B * Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ)
        = (A ρ)ᴴ * (Formalism.UG.Jpq (p ρ) (q ρ) * ((A ρ * B) * (Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [h3, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.Jpq (p ρ) (q ρ)), hJ, Matrix.one_mul,
            ← Matrix.conjTranspose_mul, h4, Matrix.conjTranspose_one]
  have hd := Matrix.det_ne_zero_of_right_inverse key
  rw [Matrix.det_neg, Matrix.det_transpose] at hd
  have hd' : (G.map (σ ρ).1).det ≠ 0 := fun h => hd (by rw [h, mul_zero])
  intro h0
  apply hd'
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply]`.
-/
theorem perm_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix ι ι ℂ) (a b : Fin r) :
    ((permM e)ᵀ * M * permM e) a b = M (e.symm a) (e.symm b) := by
  simp [Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply]

/- English proof (translation)
Introduce `E _ _ _ r κ p q Ψ G x σ A e a₀ π hI hP ε`. Use extensionality with `b`. Simplify using `only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq, frBall]`. Establish `key : ∀ ρ, (mat x (σ ρ))⁻¹ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x (σ ρ) - 1 = (permM (e ρ))ᵀ * (sMat (a₀ ρ) (b ρ) - 1) * permM (e ρ)`. Introduce `ρ`.

Take `⟨h1, -, -, -⟩` from `inv_facts hI ρ`. Establish `hinv : (mat x (σ ρ))⁻¹ = (permM (e ρ))ᵀ * A ρ` using `Matrix.inv_eq_left_inv h1`. Rewrite using `[hinv, Matrix.mul_assoc (permM (e ρ))ᵀ (A ρ), hP b ρ]`. Simplify using `only [Matrix.mul_assoc, (hI ρ).2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, transpose_mul_permM]`. Prove the components needed by the constructor for the conclusion.

Introduce `h ρ i j`. Use `h (σ ρ) (e ρ i) (e ρ j)` as an intermediate fact. Rewrite `this` using `[key ρ, perm_conj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Then use the resulting hypothesis. Introduce `h τ i j`. Take `⟨ρ, rfl⟩` from `σ.surjective τ`.

Rewrite using `[key ρ, perm_conj]`. Conclude with `h ρ _ _`.
-/
theorem preimage_frBall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G), IsIdent p q Ψ G x σ A e → IsProj p q Ψ G σ A a₀ π → ∀ ε : ℝ, π ⁻¹' frBall Ψ G x ε = Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) | ∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε}) := by
  intro E _ _ _ r κ p q Ψ G x σ A e a₀ π hI hP ε
  ext b
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq, frBall]
  have key : ∀ ρ, (mat x (σ ρ))⁻¹ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x (σ ρ) - 1
      = (permM (e ρ))ᵀ * (sMat (a₀ ρ) (b ρ) - 1) * permM (e ρ) := by
    intro ρ
    obtain ⟨h1, -, -, -⟩ := inv_facts hI ρ
    have hinv : (mat x (σ ρ))⁻¹ = (permM (e ρ))ᵀ * A ρ := Matrix.inv_eq_left_inv h1
    rw [hinv, Matrix.mul_assoc (permM (e ρ))ᵀ (A ρ), hP b ρ]
    simp only [Matrix.mul_assoc, (hI ρ).2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      transpose_mul_permM]
  constructor
  · intro h ρ i j
    have := h (σ ρ) (e ρ i) (e ρ j)
    rwa [key ρ, perm_conj, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · intro h τ i j
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    rw [key ρ, perm_conj]
    exact h ρ _ _
/- English proof (translation)
Introduce `E _ _ _ r κ p q Ψ G x σ A e hI s`. Establish `key : ∀ ρ, ∃ b : UpqT (p ρ) (q ρ), UpqT.mat b = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat x (σ ρ) * (permM (e ρ))ᵀ)`. Introduce `ρ`. Rewrite using `[← Set.mem_range, GlobalTheory.UpqTopology.range_mat]`. Use `show _ = _`.

Use `set Sm := ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)`. Use `set Bm := mat x (σ ρ) * (permM (e ρ))ᵀ`. Establish `hmem` using `((GlobalTheory.SUVol.DensOne.mem_realSU_iff Ψ G s.1).1 s.2 (σ ρ)).1`. Establish `h2 : Smᴴ * (G.map (σ ρ).1)ᵀ * Sm = (G.map (σ ρ).1)ᵀ`. Use `congrArg Matrix.transpose hmem` as an intermediate fact.

Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`. Rewrite using `[Matrix.mul_assoc]`. Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = Bmᴴ * ((A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ) * Bm := by`. Rewrite using `[(hI ρ).1, Matrix.mul_neg, Matrix.neg_mul, h2]`. Use `_ = (A ρ * Bm)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * (A ρ * Bm) := by`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Formalism.UG.Jpq (p ρ) (q ρ) := by`.

Rewrite using `[(inv_facts hI ρ).2.2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Use `choose b hb using key`. Use `⟨b, fun ρ => ?_⟩` and prove the remaining obligations. Rewrite using `[hb ρ, Matrix.mul_assoc (A ρ * _), (inv_facts hI ρ).2.2.2, Matrix.mul_one]`.
-/
theorem exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), IsIdent p q Ψ G x σ A e → ∀ s : realSU Ψ G, ∃ b₀ : ∀ ρ, UpqT (p ρ) (q ρ), ∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  intro E _ _ _ r κ p q Ψ G x σ A e hI s
  have key : ∀ ρ, ∃ b : UpqT (p ρ) (q ρ), UpqT.mat b =
      A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat x (σ ρ) * (permM (e ρ))ᵀ) := by
    intro ρ
    rw [← Set.mem_range, GlobalTheory.UpqTopology.range_mat]
    show _ = _
    set Sm := ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    set Bm := mat x (σ ρ) * (permM (e ρ))ᵀ
    have hmem := ((GlobalTheory.SUVol.DensOne.mem_realSU_iff Ψ G s.1).1 s.2 (σ ρ)).1
    have h2 : Smᴴ * (G.map (σ ρ).1)ᵀ * Sm = (G.map (σ ρ).1)ᵀ := by
      have := congrArg Matrix.transpose hmem
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
      rw [Matrix.mul_assoc]
      exact this
    calc (A ρ * Sm * Bm)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * (A ρ * Sm * Bm)
        = Bmᴴ * (Smᴴ * ((A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ) * Sm) * Bm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bmᴴ * ((A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ) * Bm := by
          rw [(hI ρ).1, Matrix.mul_neg, Matrix.neg_mul, h2]
      _ = (A ρ * Bm)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * (A ρ * Bm) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.UG.Jpq (p ρ) (q ρ) := by
          rw [(inv_facts hI ρ).2.2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  choose b hb using key
  refine ⟨b, fun ρ => ?_⟩
  rw [hb ρ, Matrix.mul_assoc (A ρ * _), (inv_facts hI ρ).2.2.2, Matrix.mul_one]
/- English proof (translation)
Introduce `f r ε hf hr hε`. Establish `hf' : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hr' : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hN : 1 ≤ f * r ^ 2` using `by have := Nat.one_le_pow 2 r hr; nlinarith`. Establish `hnN : f * (r ^ 2 - 1) ≤ f * r ^ 2` using `Nat.mul_le_mul_left _ (Nat.sub_le _ _)`.

Establish `hL : ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ f = (200 * (r : ℝ)) ^ (f * r ^ 2) * ε ^ (f * (r ^ 2 - 1))`. Rewrite using `[mul_pow, ← pow_mul, ← pow_mul, mul_comm (r ^ 2) f, mul_comm (r ^ 2 - 1) f]`. Rewrite using `[hL, div_pow]`. Generalize the expression as in `hN' : f * r ^ 2 = N at hN hnN`. Generalize the expression as in `hn' : f * (r ^ 2 - 1) = n at hnN`.

Establish `hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2` using `one_le_pow₀ hr'`. Establish `ha1 : (1 : ℝ) ≤ 2 * ((f : ℝ) * (r : ℝ) ^ 2)` using `by nlinarith`. Generalize the expression as in `ha : 2 * ((f : ℝ) * (r : ℝ) ^ 2) = a at ha1`. Establish `ha0 : 0 < a` using `by linarith`. Establish `e1 : 1000 * (f : ℝ) * (r : ℝ) ^ 3 = (5 / 2) * (200 * (r : ℝ) * a)` using `by rw [← ha]; ring`.

Establish `han : a ^ n ≤ a ^ N` using `pow_le_pow_right₀ ha1 hnN`. Establish `hq : 0 ≤ 200 * (r : ℝ) * a` using `mul_nonneg (by positivity) ha0.le`. Establish `h52 : (2 : ℝ) ≤ (5 / 2) ^ N`. Combine the equalities or inequalities in the displayed calculation. Establish `key : (200 * (r : ℝ)) ^ N * a ^ N * 2 ≤ (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ N`.

Rewrite using `[e1, mul_pow (5 / 2 : ℝ), ← mul_pow (200 * (r : ℝ)) a N]`. Establish `hp : 0 ≤ (200 * (r : ℝ) * a) ^ N` using `pow_nonneg hq _`. Use the polynomial consequences of the given equalities and inequalities. Establish `hεn : 0 < ε ^ n` using `pow_pos hε _`. Establish `han0 : 0 < a ^ n` using `pow_pos ha0 _`.

Establish `hw : 0 ≤ ε ^ n / a ^ n / 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ ((200 * (r : ℝ)) ^ N * a ^ N * 2) * (ε ^ n / a ^ n / 2) := by gcongr`. Use `_ ≤ _ := mul_le_mul_of_nonneg_right key hw`.
-/
theorem constant_bound : ∀ (f r : ℕ) (ε : ℝ), 1 ≤ f → 1 ≤ r → 0 < ε → ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ f ≤ (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ (f * r ^ 2) * ((ε / (2 * ((f : ℝ) * (r : ℝ) ^ 2))) ^ (f * (r ^ 2 - 1)) / 2) := by
  intro f r ε hf hr hε
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN : 1 ≤ f * r ^ 2 := by have := Nat.one_le_pow 2 r hr; nlinarith
  have hnN : f * (r ^ 2 - 1) ≤ f * r ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hL : ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ f =
      (200 * (r : ℝ)) ^ (f * r ^ 2) * ε ^ (f * (r ^ 2 - 1)) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (r ^ 2) f, mul_comm (r ^ 2 - 1) f]
  rw [hL, div_pow]
  generalize hN' : f * r ^ 2 = N at hN hnN
  generalize hn' : f * (r ^ 2 - 1) = n at hnN
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr'
  have ha1 : (1 : ℝ) ≤ 2 * ((f : ℝ) * (r : ℝ) ^ 2) := by nlinarith
  generalize ha : 2 * ((f : ℝ) * (r : ℝ) ^ 2) = a at ha1
  have ha0 : 0 < a := by linarith
  have e1 : 1000 * (f : ℝ) * (r : ℝ) ^ 3 = (5 / 2) * (200 * (r : ℝ) * a) := by rw [← ha]; ring
  have han : a ^ n ≤ a ^ N := pow_le_pow_right₀ ha1 hnN
  have hq : 0 ≤ 200 * (r : ℝ) * a := mul_nonneg (by positivity) ha0.le
  have h52 : (2 : ℝ) ≤ (5 / 2) ^ N := by
    calc (2 : ℝ) ≤ 5 / 2 := by norm_num
      _ = (5 / 2) ^ 1 := (pow_one _).symm
      _ ≤ (5 / 2) ^ N := pow_le_pow_right₀ (by norm_num) hN
  have key : (200 * (r : ℝ)) ^ N * a ^ N * 2 ≤ (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ N := by
    rw [e1, mul_pow (5 / 2 : ℝ), ← mul_pow (200 * (r : ℝ)) a N]
    have hp : 0 ≤ (200 * (r : ℝ) * a) ^ N := pow_nonneg hq _
    nlinarith
  have hεn : 0 < ε ^ n := pow_pos hε _
  have han0 : 0 < a ^ n := pow_pos ha0 _
  have hw : 0 ≤ ε ^ n / a ^ n / 2 := by positivity
  calc (200 * (r : ℝ)) ^ N * ε ^ n = ((200 * (r : ℝ)) ^ N * a ^ n * 2) * (ε ^ n / a ^ n / 2) := by
        field_simp
    _ ≤ ((200 * (r : ℝ)) ^ N * a ^ N * 2) * (ε ^ n / a ^ n / 2) := by
        gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right key hw

/- English proof (translation)
Introduce `E _ _ _ r κ _ p q Ψ G x σ A e a₀ π m hr hΨ hI hπc hP hT hm S hS`. Use `haveI : ∀ ρ, IsTopologicalGroup (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).1`. Use `haveI : ∀ ρ, LocallyCompactSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.1`. Use `haveI : ∀ ρ, SecondCountableTopology (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.1`. Use `haveI : ∀ ρ, BorelSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.1`.

Use `haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1`. Establish `hcard : Fintype.card κ = Ψ.card`. Rewrite using `[Fintype.card_congr σ]`. Simplify using the standard rewrite rules. Establish `hne : Nonempty κ`.

Rewrite using `[← Fintype.card_pos_iff, hcard]`. Use linear arithmetic over natural numbers and integers. Take `⟨ρ₀⟩` from `hne`. Establish `hG : G.det ≠ 0` using `det_ne hI ρ₀`. Establish `hx : ∀ τ, (mat x τ).det ≠ 0`.

Introduce `τ`. Take `⟨ρ, rfl⟩` from `σ.surjective τ`. Conclude with `Matrix.det_ne_zero_of_right_inverse (inv_facts hI ρ).2.1`. Establish `hpq : ∀ ρ, p ρ + q ρ = r`. Introduce `ρ`.

Simplify using `using Fintype.card_congr (e ρ)`. Establish `hπm : Measurable π` using `hπc.measurable`. Use `set μ := Measure.pi m with hμ`. Use `set ν := μ.map π with hν`. Use `haveI hinv : ν.IsMulLeftInvariant := by`.

Prove the components needed by the constructor for the conclusion. Introduce `s`. Take `⟨b₀, hb₀⟩` from `exists_lift E r κ p q Ψ G x σ A e hI s`. Rewrite using `[hν, Measure.map_map (measurable_const_mul s) hπm]`. Establish `h : (fun y => s * y) ∘ π = π ∘ (fun b => b₀ * b)` using `funext fun b => (hT s b₀ hb₀ b).symm`.

Rewrite using `[h, ← Measure.map_map hπm (measurable_const_mul b₀), map_mul_left_eq_self]`. Establish `hopen : ∀ ε, IsOpen (frBall Ψ G x ε)`. Introduce `ε`. Establish `hc : ∀ τ a b, Continuous fun s : realSU Ψ G => ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖`. Introduce `τ a b`.

Establish `h1 : Continuous fun s : realSU Ψ G => ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)` using `Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)`. Conclude with `((((continuous_const.matrix_mul h1).matrix_mul continuous_const).sub continuous_const).matrix_elem a b).norm`. Establish `: frBall Ψ G x ε = ⋂ τ, ⋂ a, ⋂ b, {s : realSU Ψ G | ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε}`. Use extensionality with `s`. Simplify using `[frBall]`.

Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => isOpen_lt (hc τ a b) continuous_const`. Establish `h1mem : ∀ ε, 0 < ε → (1 : realSU Ψ G) ∈ frBall Ψ G x ε`. Introduce `ε hε τ a b`. Establish `: (mat x τ)⁻¹ * ((((1 : realSU Ψ G).1 τ : GL (Fin r) ℂ)) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 1`.

Simplify using `[Matrix.nonsing_inv_mul _ (hx τ).isUnit]`. Rewrite using `[this, sub_self]`. Simplify using `using hε`. Establish `hplace` using `fun ρ => GlobalTheory.T.measure_detOneFactor_nearIdentity_le (p ρ) (q ρ) (a₀ ρ) (m ρ) (hm ρ)`. Use `choose εp hεp hbp using hplace`.

Take `⟨εl, hεl, hbl⟩` from `GlobalTheory.T.riemannianHaar_frameBall_lower_bound E r Ψ G x hr hG hx`. Use `set δ := Finset.univ.inf' ⟨ρ₀, Finset.mem_univ _⟩ εp with hδdef`. Establish `hδ : 0 < δ` using `(Finset.lt_inf'_iff _).2 fun ρ _ => hεp ρ`. Use `set ε := min δ εl / 2 with hεdef`. Establish `hεm : ε < min δ εl` using `half_lt_self (lt_min hδ hεl)`.

Establish `hε : 0 < ε` using `half_pos (lt_min hδ hεl)`. Establish `hεδ : ∀ ρ, ε < εp ρ` using `fun ρ => lt_of_lt_of_le (lt_of_lt_of_le hεm (min_le_left _ _)) (Finset.inf'_le _ (Finset.mem_univ ρ))`. Establish `hεl' : ε < εl` using `lt_of_lt_of_le hεm (min_le_right _ _)`. Use `set U := ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ Ψ.card with hU`. Establish `hνB : ν (frBall Ψ G x ε) ≤ ENNReal.ofReal U`.

Rewrite using `[hν, Measure.map_apply hπm (hopen ε).measurableSet, preimage_frBall E r κ p q Ψ G x σ A e a₀ π hI hP ε, hμ, Measure.pi_pi]`. Combine the equalities or inequalities in the displayed calculation. Use `hbp ρ ε hε (hεδ ρ)` as an intermediate fact. Rewrite `this` using `[hpq ρ]`. Conclude with `this`.

Use `_ = ENNReal.ofReal U := by`. Rewrite using `[Finset.prod_const, Finset.card_univ, hcard, ← ENNReal.ofReal_pow (by positivity)]`. Establish `hfinB : ν (frBall Ψ G x ε) < ∞` using `lt_of_le_of_lt hνB ENNReal.ofReal_lt_top`. Use `haveI : IsLocallyFiniteMeasure ν := ⟨fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' frBall Ψ G x ε, (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by show frBall Ψ G x ε ∈ nhds (g⁻¹ * g)`. Rewrite using `[inv_mul_cancel]`.

Conclude with `(hopen ε).mem_nhds (h1mem ε hε)),`. Use `by rw [measure_preimage_mul]; exact hfinB⟩⟩`. Use `haveI hH : (riemHaar Ψ G x).IsHaarMeasure := (GlobalTheory.SUVol.DensOne.tangentHaar_riemLie (Ψ := Ψ) (G := G) (hG := hG) (x := x) (hx := hx)).1`. Establish `hc` using `Measure.isMulLeftInvariant_eq_smul ν (riemHaar Ψ G x)`. Use `set c := ν.haarScalarFactor (riemHaar Ψ G x) with hcdef`.

Establish `hL` using `hbl ε hε hεl'`. Establish `hf : (0 : ℝ) < Ψ.card` using `by exact_mod_cast hΨ`. Establish `hr' : (0 : ℝ) < r` using `by exact_mod_cast hr`. Use `set L := (ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2 with hLdef`. Establish `hLpos : 0 < L` using `div_pos (pow_pos (div_pos hε (mul_pos two_pos (mul_pos hf (pow_pos hr' 2)))) _) two_pos`.

Establish `hcL : (c : ℝ) * L ≤ U`. Establish `h1 : (c : ℝ≥0∞) * ENNReal.ofReal L ≤ ENNReal.ofReal U`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Use `_ ≤ _ := hνB`.

Rewrite `h1` using `[← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]`. Conclude with `(ENNReal.ofReal_le_ofReal_iff (pow_nonneg (mul_nonneg (by positivity) (pow_nonneg hε.le _)) _)).1 h1`. Establish `hUC` using `constant_bound Ψ.card r ε hΨ hr hε`. Establish `hcC : (c : ℝ) ≤ (1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)` using `le_of_mul_le_mul_right (hcL.trans hUC) hLpos`. Rewrite using `[← Measure.map_apply hπm hS, ← hν, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`.

Establish `hcC' : (c : ℝ≥0∞) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2))`. Rewrite using `[← ENNReal.ofReal_coe_nnreal]`. Conclude with `ENNReal.ofReal_le_ofReal hcC`. Conclude with `mul_le_mul_of_nonneg_right hcC' (zero_le)`.
-/
theorem massUp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))), 1 ≤ r → 1 ≤ Ψ.card → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → Measure.pi m (π ⁻¹' S) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ π m hr hΨ hI hπc hP hT hm S hS
  classical
  haveI : ∀ ρ, IsTopologicalGroup (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  haveI : ∀ ρ, LocallyCompactSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.1
  haveI : ∀ ρ, SecondCountableTopology (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.1
  haveI : ∀ ρ, BorelSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.1
  haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1

  have hcard : Fintype.card κ = Ψ.card := by
    rw [Fintype.card_congr σ]; simp
  have hne : Nonempty κ := by
    rw [← Fintype.card_pos_iff, hcard]; omega
  obtain ⟨ρ₀⟩ := hne
  have hG : G.det ≠ 0 := det_ne hI ρ₀
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    exact Matrix.det_ne_zero_of_right_inverse (inv_facts hI ρ).2.1
  have hpq : ∀ ρ, p ρ + q ρ = r := by
    intro ρ; simpa using Fintype.card_congr (e ρ)
  have hπm : Measurable π := hπc.measurable
  set μ := Measure.pi m with hμ
  set ν := μ.map π with hν

  haveI hinv : ν.IsMulLeftInvariant := by
    constructor
    intro s
    obtain ⟨b₀, hb₀⟩ := exists_lift E r κ p q Ψ G x σ A e hI s
    rw [hν, Measure.map_map (measurable_const_mul s) hπm]
    have h : (fun y => s * y) ∘ π = π ∘ (fun b => b₀ * b) := funext fun b => (hT s b₀ hb₀ b).symm
    rw [h, ← Measure.map_map hπm (measurable_const_mul b₀), map_mul_left_eq_self]

  have hopen : ∀ ε, IsOpen (frBall Ψ G x ε) := by
    intro ε
    have hc : ∀ τ a b, Continuous fun s : realSU Ψ G =>
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ := by
      intro τ a b
      have h1 : Continuous fun s : realSU Ψ G => ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
        Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)
      exact ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).sub continuous_const).matrix_elem a b).norm
    have : frBall Ψ G x ε = ⋂ τ, ⋂ a, ⋂ b, {s : realSU Ψ G |
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε} := by
      ext s; simp [frBall]
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => isOpen_lt (hc τ a b) continuous_const
  have h1mem : ∀ ε, 0 < ε → (1 : realSU Ψ G) ∈ frBall Ψ G x ε := by
    intro ε hε τ a b
    have : (mat x τ)⁻¹ * ((((1 : realSU Ψ G).1 τ : GL (Fin r) ℂ)) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 1 := by
      simp [Matrix.nonsing_inv_mul _ (hx τ).isUnit]
    rw [this, sub_self]; simpa using hε
  have hplace := fun ρ => GlobalTheory.T.measure_detOneFactor_nearIdentity_le (p ρ) (q ρ) (a₀ ρ) (m ρ) (hm ρ)
  choose εp hεp hbp using hplace
  obtain ⟨εl, hεl, hbl⟩ := GlobalTheory.T.riemannianHaar_frameBall_lower_bound E r Ψ G x hr hG hx
  set δ := Finset.univ.inf' ⟨ρ₀, Finset.mem_univ _⟩ εp with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun ρ _ => hεp ρ
  set ε := min δ εl / 2 with hεdef
  have hεm : ε < min δ εl := half_lt_self (lt_min hδ hεl)
  have hε : 0 < ε := half_pos (lt_min hδ hεl)
  have hεδ : ∀ ρ, ε < εp ρ := fun ρ =>
    lt_of_lt_of_le (lt_of_lt_of_le hεm (min_le_left _ _)) (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hεl' : ε < εl := lt_of_lt_of_le hεm (min_le_right _ _)
  set U := ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ Ψ.card with hU
  have hνB : ν (frBall Ψ G x ε) ≤ ENNReal.ofReal U := by
    rw [hν, Measure.map_apply hπm (hopen ε).measurableSet,
      preimage_frBall E r κ p q Ψ G x σ A e a₀ π hI hP ε, hμ, Measure.pi_pi]
    calc _ ≤ ∏ _ρ : κ, ENNReal.ofReal ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) :=
          Finset.prod_le_prod' fun ρ _ => by
            have := hbp ρ ε hε (hεδ ρ)
            rw [hpq ρ] at this
            exact this
      _ = ENNReal.ofReal U := by
          rw [Finset.prod_const, Finset.card_univ, hcard, ← ENNReal.ofReal_pow (by positivity)]
  have hfinB : ν (frBall Ψ G x ε) < ∞ := lt_of_le_of_lt hνB ENNReal.ofReal_lt_top
  haveI : IsLocallyFiniteMeasure ν := ⟨fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' frBall Ψ G x ε,
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by
      show frBall Ψ G x ε ∈ nhds (g⁻¹ * g)
      rw [inv_mul_cancel]; exact (hopen ε).mem_nhds (h1mem ε hε)),
    by rw [measure_preimage_mul]; exact hfinB⟩⟩
  haveI hH : (riemHaar Ψ G x).IsHaarMeasure :=
    (GlobalTheory.SUVol.DensOne.tangentHaar_riemLie (Ψ := Ψ) (G := G) (hG := hG) (x := x) (hx := hx)).1
  have hc := Measure.isMulLeftInvariant_eq_smul ν (riemHaar Ψ G x)
  set c := ν.haarScalarFactor (riemHaar Ψ G x) with hcdef
  have hL := hbl ε hε hεl'
  have hf : (0 : ℝ) < Ψ.card := by exact_mod_cast hΨ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set L := (ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2 with hLdef
  have hLpos : 0 < L := div_pos (pow_pos (div_pos hε (mul_pos two_pos (mul_pos hf (pow_pos hr' 2)))) _) two_pos
  have hcL : (c : ℝ) * L ≤ U := by
    have h1 : (c : ℝ≥0∞) * ENNReal.ofReal L ≤ ENNReal.ofReal U := by
      calc (c : ℝ≥0∞) * ENNReal.ofReal L ≤ c * riemHaar Ψ G x (frBall Ψ G x ε) := mul_le_mul_of_nonneg_left hL (zero_le)
        _ = ν (frBall Ψ G x ε) := by
          conv_rhs => rw [hc]
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        _ ≤ _ := hνB
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (mul_nonneg (by positivity) (pow_nonneg hε.le _)) _)).1 h1
  have hUC := constant_bound Ψ.card r ε hΨ hr hε
  have hcC : (c : ℝ) ≤ (1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2) :=
    le_of_mul_le_mul_right (hcL.trans hUC) hLpos
  rw [← Measure.map_apply hπm hS, ← hν, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcC' : (c : ℝ≥0∞) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hcC
  exact mul_le_mul_of_nonneg_right hcC' (zero_le)

end GlobalTheory.CovTop.VolUp.MassUp
