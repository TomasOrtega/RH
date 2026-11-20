import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVariableMultiplicationMemSpanHeisenbergOpera
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorMvPolynomialSubmoduleEqTopOfOneMulX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorISignatureConjApplyOne

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace PositivityTheory.ThKEnd.Comp.PR

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem atPl_eq' (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

/- English proof (translation)
Simplify using `only [atPl_eq', MultilinearMap.map_update_add]`.
-/
theorem atPl_add' (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq', MultilinearMap.map_update_add]

/- English proof (translation)
Simplify using `only [atPl_eq', MultilinearMap.map_update_smul]`.
-/
theorem atPl_smul' (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq', MultilinearMap.map_update_smul]

/- English proof (translation)
Simplify using `only [atPl_eq', MultilinearMap.map_update_zero]`.
-/
theorem atPl_zero' (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq', MultilinearMap.map_update_zero]

/- English proof (translation)
Rewrite using `[atPl, PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = w`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`.
-/
theorem atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

end Tensor

/- English proof (translation)
Simplify using `[heisOp]`.
-/
theorem heisOp_zero {P Q R S : ℕ} : heisOp (P := P) (Q := Q) (R := R) (S := S) 0 = 0 := by
  simp [heisOp]

/- English proof (translation)
Simplify using `[Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]`.
-/
theorem Jm_transpose' (p q : ℕ) : (Jm p q)ᵀ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

/- English proof (translation)
The claim follows from `GlobalTheory.PolRangeInf.exists_at_inf_values hcm τ z`.
-/
theorem exists_at_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (z : InfinitePlace F → ℂ) : ∃ a : AE F E, At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := GlobalTheory.PolRangeInf.exists_at_inf_values hcm τ z

/- English proof (translation)
Use `choose a ha using fun i j => exists_at_piInf hcm τ (fun w => z w i j)`. Use `⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]`. Conclude with `(ha i j).1 x hx`.

Use extensionality with `i j`. Simplify using `[(ha i j).2 w]`.
-/
theorem exists_mat_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => exists_at_piInf hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

/- English proof (translation)
The claim follows from `GlobalTheory.MulVarSpan.mulX_mem_span l`.
-/
theorem mulX_mem_span {P Q R S : ℕ} (l : Ln P Q R S) :
    LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈
      Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := GlobalTheory.MulVarSpan.mulX_mem_span l

/- English proof (translation)
The claim follows from `GlobalTheory.RealLift.tensor_submodule_eq_top N h1 hN`.
-/
theorem tens_top {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ))
    (h1 : PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N)
    (hN : ∀ w l, ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) : N = ⊤ := GlobalTheory.RealLift.tensor_submodule_eq_top N h1 hN

/- English proof (translation)
Use `tens_top N h1 fun w l T hT => ?_` and prove the remaining obligations. Set `K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))` to `{ carrier := {L | ∀ T ∈ N, atPl w L T ∈ N} add_mem' := fun {a b} ha hb T hT => by`. Rewrite using `[atPl_add', LinearMap.add_apply]`. Conclude with `N.add_mem (ha T hT) (hb T hT)`. Use the proof step `zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem`.

Use the proof step `smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }`. Establish `hK : Submodule.span ℂ (Set.range (heisOp (P` using `P) (Q := Q) (R := R) (S := S))) ≤ K := Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)`. Conclude with `hK (mulX_mem_span l) T hT`.
-/
theorem tens_top_heis {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}
    (N : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S))
    (h1 : PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ∈ N)
    (hN : ∀ w c, ∀ T ∈ N, atPl w (heisOp (P := P) (Q := Q) (R := R) (S := S) c) T ∈ N) : N = ⊤ := by
  refine tens_top N h1 fun w l T hT => ?_
  let K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)) :=
    { carrier := {L | ∀ T ∈ N, atPl w L T ∈ N}
      add_mem' := fun {a b} ha hb T hT => by
        rw [atPl_add', LinearMap.add_apply]; exact N.add_mem (ha T hT) (hb T hT)
      zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem
      smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }
  have hK : Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) ≤ K :=
    Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)
  exact hK (mulX_mem_span l) T hT

/- English proof (translation)
The claim follows from `GlobalTheory.RealLift.heisOp_twist_one c`.
-/
theorem heisOp_twist_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := GlobalTheory.RealLift.heisOp_twist_one c

/- English proof (translation)
Simplify using `only [sumPl, LinearMap.sum_apply, Finset.smul_sum, atPl_tprod, heisOp_twist_one]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Conclude with `(PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _`.
-/
theorem sumPl_twist_one {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S))) (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)))
      = Complex.I • sumPl (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S))) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, atPl_tprod, heisOp_twist_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ`. Establish `hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0`. Introduce `u t`. Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr]`.

Establish `toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ → ActsD (evI F) (M.heisLine ψ u) f f₁` using `fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h`. Establish `uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ → ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂` using `fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2`. Use `choose A' hA' using fun w => (hfr.2.1 w).2`. Use `choose C' hC' using fun w => (hfr.2.2 w).2`. Establish `decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ`.

Introduce `u w`. Rewrite using `[show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ = (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by`. Rewrite using `[Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc], hA', hC']`. Simplify using the standard rewrite rules.

Establish `der : ∀ u, At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ, (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T, ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))` using `fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)`. Establish `tw : ∀ w (c : Matrix (Ix P Q) (Ix R S) ℂ) (e : ℂ), A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ)`. Introduce `w c e`. Establish `h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm R S * (C w)ᵀ`. Rewrite using `[← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]`. Establish `gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S))))`. Use `⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩` and prove the remaining obligations.

Establish `hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ` using `decomp u`. Establish `hc' : ∀ w, u'.map (piInf (τ w)) = A w * (Complex.I • (Jm P Q * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm R S)) * (C w)ᵀ`. Introduce `w`. Rewrite using `[hrel w, tw, ← hc w]`. Simplify using the standard rewrite rules.

Rewrite using `[uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPl_twist_one, map_smul]`. Establish `gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ` using `fun f₀ h => by`. Unfold `Model.Pol`. Conclude with `Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h`. Establish `pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ`.

Introduce `u hu f hf f₁ h1`. Unfold `Model.Pol at hf ⊢`. Conclude with `Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨T, rfl⟩`.

Establish `htop : (M.Pol ψ τ).comap Φ = ⊤`. Use `tens_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_` and prove the remaining obligations. Take `⟨u, hu, hu'⟩` from `exists_mat_at hcm τ (fun w' => A w' * Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w' * (C w')ᵀ)`. Establish `hs : sumPl (fun w' => heisOp (Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w')) T = atPl w (heisOp c) T`. Rewrite using `[sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Function.update_of_ne hb, heisOp_zero, atPl_zero']`. Simplify using the standard rewrite rules. Use `pol_der u hu _ hT _ (der u hu _ hu' T)` as an intermediate fact.

Rewrite `this` using `[hs]`. Then use the resulting hypothesis. Establish `: T ∈ (M.Pol ψ τ).comap Φ` using `htop ▸ Submodule.mem_top`. Conclude with `this`. Unfold `Model.Pol`. Use `sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩` and prove the remaining obligations.

Take `⟨ε, hε⟩` from `hf₀`. Take `⟨z, hz⟩` from `hV F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1 Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' => hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))`. Conclude with `⟨z • PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)), by rw [map_smul, hz]⟩`. Take `⟨T, rfl⟩` from `hf`. Conclude with `⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩`.
-/
theorem polRange_of (hL : ActsLaws) (_hD : DerEx) (hV : VacLine) : PolRange := by
  intro F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  have uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂ := fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have der : ∀ u, At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T,
      ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T)) :=
    fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)
  have tw : ∀ w (c : Matrix (Ix P Q) (Ix R S) ℂ) (e : ℂ),
      A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm R S * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']
    calc A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • ((A w * Jm P Q) * c * (Jm R S * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  have gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)))) := by
    refine ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
    have hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := decomp u
    have hc' : ∀ w, u'.map (piInf (τ w)) =
        A w * (Complex.I • (Jm P Q * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm R S)) * (C w)ᵀ := by
      intro w; rw [hrel w, tw, ← hc w]; simp
    rw [uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPl_twist_one, map_smul]
  have gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h => by
    unfold Model.Pol
    exact Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := by
    intro u hu f hf f₁ h1
    unfold Model.Pol at hf ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    have htop : (M.Pol ψ τ).comap Φ = ⊤ := by
      refine tens_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_
      obtain ⟨u, hu, hu'⟩ := exists_mat_at hcm τ
        (fun w' => A w' * Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w' * (C w')ᵀ)
      have hs : sumPl (fun w' => heisOp (Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w')) T =
          atPl w (heisOp c) T := by
        rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]
        · simp
        · intro b _ hb; simp [Function.update_of_ne hb, heisOp_zero, atPl_zero']
        · simp
      have := pol_der u hu _ hT _ (der u hu _ hu' T)
      rwa [hs] at this
    have : T ∈ (M.Pol ψ τ).comap Φ := htop ▸ Submodule.mem_top
    exact this
  · unfold Model.Pol
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩
    · obtain ⟨ε, hε⟩ := hf₀
      obtain ⟨z, hz⟩ := hV F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
        Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
          hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
      exact ⟨z • PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)), by rw [map_smul, hz]⟩
    · obtain ⟨T, rfl⟩ := hf
      exact ⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩

end PositivityTheory.ThKEnd.Comp.PR
