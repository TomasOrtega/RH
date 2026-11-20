import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierAdelicPi
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D.FourierTransformSplitting

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Simplify using `[ψ, AddChar.map_add_eq_mul]`.
-/
private theorem psi_add (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp [ψ, AddChar.map_add_eq_mul]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Use extensionality with `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]`.
-/
private theorem cons_eq {n : ℕ} :
    (fun p : A F × (Fin n → A F) => (Fin.cons p.1 p.2 : Fin (n + 1) → A F)) =
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A F) 0).symm := by
  funext p
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]

/- English proof (translation)
Rewrite using `[cons_eq]`. Conclude with `(measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => adeleMeasure F) 0).symm`.
-/
private theorem fub_mp {n : ℕ} : MeasurePreserving
    (fun p : A F × (Fin n → A F) => (Fin.cons p.1 p.2 : Fin (n + 1) → A F))
    ((adeleMeasure F).prod (adeleMeasurePi F)) (adeleMeasurePi F) := by
  rw [cons_eq]
  exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => adeleMeasure F) 0).symm

/- English proof (translation)
Rewrite using `[cons_eq]`. Conclude with `(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A F) 0).symm.measurableEmbedding`.
-/
private theorem fub_emb {n : ℕ} : MeasurableEmbedding
    (fun p : A F × (Fin n → A F) => (Fin.cons p.1 p.2 : Fin (n + 1) → A F)) := by
  rw [cons_eq]
  exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A F) 0).symm.measurableEmbedding

/- English proof (translation)
Assemble the required witnesses or components as `⟨(fub_mp.integrable_comp_emb fub_emb).2 hf, (fub_mp.integral_comp fub_emb f).symm⟩`.
-/
private theorem fub {n : ℕ} {f : (Fin (n + 1) → A F) → ℂ} (hf : Integrable f (adeleMeasurePi F)) :
    Integrable (fun p : A F × (Fin n → A F) => f (Fin.cons p.1 p.2))
        ((adeleMeasure F).prod (adeleMeasurePi F)) ∧
      ∫ x, f x ∂(adeleMeasurePi F) = ∫ p : A F × (Fin n → A F), f (Fin.cons p.1 p.2)
        ∂((adeleMeasure F).prod (adeleMeasurePi F)) :=
  ⟨(fub_mp.integrable_comp_emb fub_emb).2 hf, (fub_mp.integral_comp fub_emb f).symm⟩

/- English proof (translation)
The claim follows from `((measurePreserving_funUnique (adeleMeasure F) (Fin 1)).symm.integral_comp' h).symm`.
-/
private theorem one_int (h : (Fin 1 → A F) → ℂ) :
    ∫ a, h a ∂(adeleMeasurePi F) = ∫ s : A F, h (fun _ => s) ∂(adeleMeasure F) :=
  ((measurePreserving_funUnique (adeleMeasure F) (Fin 1)).symm.integral_comp' h).symm

/- English proof (translation)
Establish `h` using `GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi ((1 : Matrix ι ι F).submatrix e id) ((1 : Matrix ι ι F).submatrix id e) (by rw [Matrix.submatrix_mul_equiv]; simp) (by`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.one_apply]) hf`. Use `h using 2` and compare the differences between its conclusion and the goal. Name the introduced variables `x`.

Use `congr 1`. Use extensionality with `k`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply]`.
-/
private theorem reindex_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    {f : (κ → A F) → ℂ} (hf : f ∈ schwartzBruhatPi F κ) :
    (fun x : ι → A F => f (x ∘ e)) ∈ schwartzBruhatPi F ι := by
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi
    ((1 : Matrix ι ι F).submatrix e id) ((1 : Matrix ι ι F).submatrix id e)
    (by rw [Matrix.submatrix_mul_equiv]; simp) (by
      ext i j
      simp [Matrix.mul_apply, Matrix.one_apply]) hf
  convert h using 2
  rename_i x
  congr 1
  ext k
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
private theorem elim_cons (a : Fin 1 → A F) (y : Fin 3 → A F) :
    (Sum.elim a y) ∘ (finSumFinEquiv (m := 1) (n := 3)).symm = (Fin.cons (a 0) y : Fin 4 → A F) := by
  ext i
  fin_cases i <;> rfl

/- English proof (translation)
Establish `h1 : (fun x : (Fin 1 ⊕ Fin 3) → A F => φ (x ∘ (finSumFinEquiv (m` using `1) (n := 3)).symm)) ∈ schwartzBruhatPi F (Fin 1 ⊕ Fin 3) := reindex_mem (finSumFinEquiv (m := 1) (n := 3)).symm hφ`. Establish `h2` using `GroundTheory.Heights₂.Theta.partialFourierPi_mem h1`. Establish `h3` using `reindex_mem (Equiv.sumComm (Fin 1) (Fin 3)) h2`. Establish `h4` using `GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h3 η`. Use `h4 using 2` and compare the differences between its conclusion and the goal.

Name the introduced variables `a`. Establish `e : (Sum.elim η a : (Fin 3 ⊕ Fin 1) → A F) ∘ (Equiv.sumComm (Fin 1) (Fin 3)) = Sum.elim a η`. Use extensionality with `s`. Apply the tactic sequence `cases s <;> rfl`. Rewrite using `[e, GroundTheory.Heights₂.Theta.partialFourierPi_sumElim]`.

Simplify using `only [elim_cons]`.
-/
private theorem g_mem {φ : (Fin 4 → A F) → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4))
    (η : Fin 3 → A F) :
    (fun a : Fin 1 → A F => adelicFourierPi F (fun y : Fin 3 → A F => φ (Fin.cons (a 0) y)) η)
      ∈ schwartzBruhatPi F (Fin 1) := by
  have h1 : (fun x : (Fin 1 ⊕ Fin 3) → A F => φ (x ∘ (finSumFinEquiv (m := 1) (n := 3)).symm))
      ∈ schwartzBruhatPi F (Fin 1 ⊕ Fin 3) :=
    reindex_mem (finSumFinEquiv (m := 1) (n := 3)).symm hφ
  have h2 := GroundTheory.Heights₂.Theta.partialFourierPi_mem h1
  have h3 := reindex_mem (Equiv.sumComm (Fin 1) (Fin 3)) h2
  have h4 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h3 η
  convert h4 using 2
  rename_i a
  have e : (Sum.elim η a : (Fin 3 ⊕ Fin 1) → A F) ∘ (Equiv.sumComm (Fin 1) (Fin 3)) = Sum.elim a η := by
    ext s
    cases s <;> rfl
  rw [e, GroundTheory.Heights₂.Theta.partialFourierPi_sumElim]
  simp only [elim_cons]

/- English proof (translation)
Establish `h1 : (fun x : (Fin 1 ⊕ Fin 3) → A F => φ (x ∘ (finSumFinEquiv (m` using `1) (n := 3)).symm)) ∈ schwartzBruhatPi F (Fin 1 ⊕ Fin 3) := reindex_mem (finSumFinEquiv (m := 1) (n := 3)).symm hφ`. Establish `h4` using `GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 (fun _ => b)`. Use `h4 using 2` and compare the differences between its conclusion and the goal. Name the introduced variables `y`. Rewrite using `[elim_cons]`.
-/
private theorem slice_mem {φ : (Fin 4 → A F) → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4))
    (b : A F) :
    (fun y : Fin 3 → A F => φ (Fin.cons b y)) ∈ schwartzBruhatPi F (Fin 3) := by
  have h1 : (fun x : (Fin 1 ⊕ Fin 3) → A F => φ (x ∘ (finSumFinEquiv (m := 1) (n := 3)).symm))
      ∈ schwartzBruhatPi F (Fin 1 ⊕ Fin 3) :=
    reindex_mem (finSumFinEquiv (m := 1) (n := 3)).symm hφ
  have h4 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 (fun _ => b)
  convert h4 using 2
  rename_i y
  rw [elim_cons]

/- English proof (translation)
Establish `hint` using `integrable_mul_adelicChar_pi (integrable_of_mem_schwartzBruhatPi hφ) ξ`. Take `⟨h1, h2⟩` from `fub hint`. Rewrite using `[adelicFourierPi, h2, integral_prod _ h1]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `only [adelicFourierPi]`.

Rewrite using `[← integral_mul_const]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [Fin.sum_univ_succ (n := 3), Fin.cons_zero, Fin.cons_succ, Fin.tail]`. Use `psi_add (a * ξ 0) (∑ i : Fin 3, y i * ξ i.succ)` as an intermediate fact. Simplify using `only [ψ] at this ⊢`.

Rewrite using `[this, mul_assoc]`. Conclude with `congrArg _ (mul_comm _ _)`.
-/
private theorem ft_split {φ : (Fin 4 → A F) → ℂ} (hφ : φ ∈ schwartzBruhatPi F (Fin 4))
    (ξ : Fin 4 → A F) :
    adelicFourierPi F φ ξ = ∫ a : A F,
      adelicFourierPi F (fun y : Fin 3 → A F => φ (Fin.cons a y)) (Fin.tail ξ) * ψ (a * ξ 0)
        ∂(adeleMeasure F) := by
  have hint := integrable_mul_adelicChar_pi (integrable_of_mem_schwartzBruhatPi hφ) ξ
  obtain ⟨h1, h2⟩ := fub hint
  rw [adelicFourierPi, h2, integral_prod _ h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [adelicFourierPi]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Fin.sum_univ_succ (n := 3), Fin.cons_zero, Fin.cons_succ, Fin.tail]
  have := psi_add (a * ξ 0) (∑ i : Fin 3, y i * ξ i.succ)
  simp only [ψ] at this ⊢
  rw [this, mul_assoc]
  exact congrArg _ (mul_comm _ _)

/- English proof (translation)
Rewrite using `[ft4, adelicFourierPi]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `e : B4 δ x (Function.update v 1 s) = ∑ i, x i * (![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] : Fin 4 → A F) i`. Simplify using `[B4, Fin.sum_univ_four]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [ψ, e]`.
-/
private theorem quaternaryFourier_eq_adelic (δ : F) (f : V4 F → ℂ) (v : V4 F) (s : A F) :
    ft4 δ f (Function.update v 1 s) =
      adelicFourierPi F f ![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] := by
  rw [ft4, adelicFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e : B4 δ x (Function.update v 1 s) =
      ∑ i, x i * (![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] : Fin 4 → A F) i := by
    simp [B4, Fin.sum_univ_four]
    ring
  simp only [ψ, e]

/- English proof (translation)
Establish `ht : Fin.tail (![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] : Fin 4 → A F) = η`. Rewrite using `[hη]`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Rewrite using `[quaternaryFourier_eq_adelic, ft_split φ.2, adelicFourierPi, one_int, ht]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Simplify using `[ψ]`.
-/
private theorem g_hat (δ : F) (φ : S4 F) (v : V4 F) (η : Fin 3 → A F)
    (hη : η = ![-v 0, 2 * v 2, -(2 * (rt δ * v 3))]) (s : A F) :
    ft4 δ φ.1 (Function.update v 1 s) = adelicFourierPi F
      (fun a : Fin 1 → A F => adelicFourierPi F (fun y : Fin 3 → A F => φ.1 (Fin.cons (a 0) y)) η)
      (fun _ => -s) := by
  have ht : Fin.tail (![-s, -v 0, 2 * v 2, -(2 * (rt δ * v 3))] : Fin 4 → A F) = η := by
    rw [hη]
    ext i
    fin_cases i <;> rfl
  rw [quaternaryFourier_eq_adelic, ft_split φ.2, adelicFourierPi, one_int, ht]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp [ψ]

end UpperTheory.ConvolutionTheory.R2.D.FourierTransformSplitting

open UpperTheory.ConvolutionTheory.R2.D.FourierTransformSplitting in
/- English proof (translation)
Introduce `F _ _ δ φ v _`. Take `⟨η, hη⟩ : ∃ η : Fin 3 → A F, η = ![-v 0, 2 * v 2, -(2 * (rt δ * v 3))]` from `⟨_, rfl⟩`. Establish `hg` using `g_mem φ.2 η`. Establish `inv` using `congrFun (adelicFourierPi_adelicFourierPi hg) (fun _ => v 1)`. Rewrite `inv` using `[adelicFourierPi, one_int]`.

Establish `hB : hat (ft4 δ φ.1) v = adelicFourierPi F (fun y : Fin 3 → A F => φ.1 (Fin.cons (-v 1) y)) η`. Use `Eq.trans ?_ inv` and prove the remaining obligations. Rewrite using `[hat, ← integral_neg_eq_self]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [g_hat δ φ v η hη]`.

Simplify using `[ψ]`. Rewrite using `[hB, adelicFourierPi]`. Establish `hint` using `integrable_mul_adelicChar_pi (integrable_of_mem_schwartzBruhatPi (slice_mem φ.2 (-v 1))) η`. Take `⟨h1, h2⟩` from `fub hint`. Rewrite using `[h2, integral_prod_symm _ h1]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only []`. Rewrite using `[hat, ← integral_mul_const]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Establish `e1 : (Fin.cons (-v 1) (Fin.cons s z : Fin 3 → A F) : Fin 4 → A F) = Function.update ![-v 1, v 0, z 0, z 1] 1 s`.

Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [Function.update] <;> rfl`. Establish `e2 : ∑ i, (Fin.cons s z : Fin 3 → A F) i * η i = -(s * v 0) + 2 * (z 0 * v 2 - rt δ * (z 1 * v 3))`. Establish `hc : (Fin.cons s z : Fin 3 → A F) 2 = z 1` using `rfl`. Simplify using `[hη, Fin.sum_univ_three, hc]`.

Expand and normalize the polynomial expressions, which then agree. Use `psi_add (-(s * v 0)) (2 * (z 0 * v 2 - rt δ * (z 1 * v 3)))` as an intermediate fact. Simplify using `only [ψ] at this ⊢`. Simplify using `only [e1, e2, this]`. Simplify using `[mul_assoc]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.D.hatW :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (φ : S4 F) (v : V4 F), δ ≠ 0 → hat (ft4 δ φ.1) v =
      ∫ z : Fin 2 → A F, hat φ.1 ![-v 1, v 0, z 0, z 1] * ψ (2 * (z 0 * v 2 - rt δ * (z 1 * v 3))) ∂(adeleMeasurePi F) := by
  intro F _ _ δ φ v _
  obtain ⟨η, hη⟩ : ∃ η : Fin 3 → A F, η = ![-v 0, 2 * v 2, -(2 * (rt δ * v 3))] := ⟨_, rfl⟩
  have hg := g_mem φ.2 η
  have inv := congrFun (adelicFourierPi_adelicFourierPi hg) (fun _ => v 1)
  rw [adelicFourierPi, one_int] at inv
  have hB : hat (ft4 δ φ.1) v =
      adelicFourierPi F (fun y : Fin 3 → A F => φ.1 (Fin.cons (-v 1) y)) η := by
    refine Eq.trans ?_ inv
    rw [hat, ← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [g_hat δ φ v η hη]
    simp [ψ]
  rw [hB, adelicFourierPi]
  have hint := integrable_mul_adelicChar_pi
    (integrable_of_mem_schwartzBruhatPi (slice_mem φ.2 (-v 1))) η
  obtain ⟨h1, h2⟩ := fub hint
  rw [h2, integral_prod_symm _ h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only []
  rw [hat, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have e1 : (Fin.cons (-v 1) (Fin.cons s z : Fin 3 → A F) : Fin 4 → A F) =
      Function.update ![-v 1, v 0, z 0, z 1] 1 s := by
    ext i
    fin_cases i <;> simp [Function.update] <;> rfl
  have e2 : ∑ i, (Fin.cons s z : Fin 3 → A F) i * η i =
      -(s * v 0) + 2 * (z 0 * v 2 - rt δ * (z 1 * v 3)) := by
    have hc : (Fin.cons s z : Fin 3 → A F) 2 = z 1 := rfl
    simp [hη, Fin.sum_univ_three, hc]
    ring
  have := psi_add (-(s * v 0)) (2 * (z 0 * v 2 - rt δ * (z 1 * v 3)))
  simp only [ψ] at this ⊢
  simp only [e1, e2, this]
  simp [mul_assoc]
