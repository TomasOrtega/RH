import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumLinePlacewiseSignaturesStatement

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.PolRangeD

open GlobalTheory.RealLift.PolRangePf

/- English proof (translation)
Establish `key : ∀ s : Finset ι, ∀ f : ∀ w, MvPolynomial (σ w) ℂ, (∀ i ∉ s, f i = 1) → PiTensorProduct.tprod ℂ f ∈ N`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `f hf`.

Establish `: f = fun w => 1` using `funext fun i => hf i (Finset.notMem_empty i)`. Rewrite using `[this]`. Conclude with `h1`. Consider the case `insert w₀ s hw₀ ih`. Introduce `f hf`.

Set `S : Submodule ℂ (MvPolynomial (σ w₀) ℂ)` to `N.comap ((PiTensorProduct.tprod ℂ : MultilinearMap ℂ (fun w : ι => MvPolynomial (σ w) ℂ) (⨂[ℂ] w : ι, MvPolynomial (σ w) ℂ)).toLinearMap f w₀)`. Establish `hS1 : (1 : MvPolynomial (σ w₀) ℂ) ∈ S` using `by show PiTensorProduct.tprod ℂ (Function.update f w₀ 1) ∈ N`. Apply `ih` to reduce the goal to its premises. Introduce `i hi`. Distinguish the cases in `h : i = w₀`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne h]; exact hf i (by simp [h, hi])`. Establish `hSX : ∀ (l : σ w₀), ∀ p ∈ S, MvPolynomial.X l * p ∈ S`. Introduce `l p hp`.

Establish `hp' : PiTensorProduct.tprod ℂ (Function.update f w₀ p) ∈ N` using `hp`. Use `show PiTensorProduct.tprod ℂ (Function.update f w₀ (MvPolynomial.X l * p)) ∈ N`. Use `hX w₀ l _ hp'` as an intermediate fact. Rewrite `this` using `[GlobalTheory.RealLift.atPl_tprod]`. Simplify using `using this`.

Establish `htop` using `GlobalTheory.RealLift.mvPolynomial_submodule_eq_top S hS1 hSX`. Establish `hf0 : f w₀ ∈ S` using `by rw [htop]; trivial`. Establish `: PiTensorProduct.tprod ℂ (Function.update f w₀ (f w₀)) ∈ N` using `hf0`. Simplify using `using this`. Rewrite using `[eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]`.

Introduce and unpack `_ ⟨f, rfl⟩`. Conclude with `key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)`.
-/
theorem tensD_top {ι : Type} [Fintype ι] [DecidableEq ι] {σ : ι → Type}
    (N : Submodule ℂ (⨂[ℂ] w : ι, MvPolynomial (σ w) ℂ))
    (h1 : PiTensorProduct.tprod ℂ (fun w => (1 : MvPolynomial (σ w) ℂ)) ∈ N)
    (hX : ∀ (w : ι) (l : σ w), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial (σ w) ℂ)) T ∈ N) :
    N = ⊤ := by
  have key : ∀ s : Finset ι, ∀ f : ∀ w, MvPolynomial (σ w) ℂ, (∀ i ∉ s, f i = 1) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = fun w => 1 := funext fun i => hf i (Finset.notMem_empty i)
      rw [this]; exact h1
    | insert w₀ s hw₀ ih =>
      intro f hf
      let S : Submodule ℂ (MvPolynomial (σ w₀) ℂ) :=
        N.comap ((PiTensorProduct.tprod ℂ : MultilinearMap ℂ (fun w : ι => MvPolynomial (σ w) ℂ)
          (⨂[ℂ] w : ι, MvPolynomial (σ w) ℂ)).toLinearMap f w₀)
      have hS1 : (1 : MvPolynomial (σ w₀) ℂ) ∈ S := by
        show PiTensorProduct.tprod ℂ (Function.update f w₀ 1) ∈ N
        apply ih
        intro i hi
        by_cases h : i = w₀
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hf i (by simp [h, hi])
      have hSX : ∀ (l : σ w₀), ∀ p ∈ S, MvPolynomial.X l * p ∈ S := by
        intro l p hp
        have hp' : PiTensorProduct.tprod ℂ (Function.update f w₀ p) ∈ N := hp
        show PiTensorProduct.tprod ℂ (Function.update f w₀ (MvPolynomial.X l * p)) ∈ N
        have := hX w₀ l _ hp'
        rw [GlobalTheory.RealLift.atPl_tprod] at this
        simpa using this
      have htop := GlobalTheory.RealLift.mvPolynomial_submodule_eq_top S hS1 hSX
      have hf0 : f w₀ ∈ S := by rw [htop]; trivial
      have : PiTensorProduct.tprod ℂ (Function.update f w₀ (f w₀)) ∈ N := hf0
      simpa using this
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)

/- English proof (translation)
Use `tensD_top N h1 fun w l T hT => ?_` and prove the remaining obligations. Set `K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))` to `{ carrier := {L | ∀ T ∈ N, atPl w L T ∈ N} add_mem' := fun {a b} ha hb T hT => by`. Rewrite using `[atPl_add', LinearMap.add_apply]`. Conclude with `N.add_mem (ha T hT) (hb T hT)`. Use the proof step `zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem`.

Use the proof step `smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }`. Establish `hK : Submodule.span ℂ (Set.range (heisOp (P` using `P w) (Q := Q w) (R := R w) (S := S w))) ≤ K := Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)`. Conclude with `hK (mulX_mem_span l) T hT`.
-/
theorem tensD_top_heis {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (N : Submodule ℂ (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h1 : PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))) ∈ N)
    (hN : ∀ w c, ∀ T ∈ N, atPl w (heisOp (P := P w) (Q := Q w) (R := R w) (S := S w) c) T ∈ N) : N = ⊤ := by
  refine tensD_top N h1 fun w l T hT => ?_
  let K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))) :=
    { carrier := {L | ∀ T ∈ N, atPl w L T ∈ N}
      add_mem' := fun {a b} ha hb T hT => by
        rw [atPl_add', LinearMap.add_apply]; exact N.add_mem (ha T hT) (hb T hT)
      zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem
      smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }
  have hK : Submodule.span ℂ (Set.range (heisOp (P := P w) (Q := Q w) (R := R w) (S := S w))) ≤ K :=
    Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)
  exact hK (mulX_mem_span l) T hT

/- English proof (translation)
Simplify using `only [sumPl, LinearMap.sum_apply, Finset.smul_sum, GlobalTheory.RealLift.atPl_tprod, GlobalTheory.RealLift.heisOp_twist_one]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Conclude with `(PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _`.
-/
theorem sumPlD_twist_one {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (c : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    sumPl (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
        (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))))
      = Complex.I • sumPl (fun w => heisOp (c w))
        (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, GlobalTheory.RealLift.atPl_tprod, GlobalTheory.RealLift.heisOp_twist_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ`. Establish `hL` using `GlobalTheory.RealLift.actsLaws`. Establish `hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0`. Introduce `u t`. Use function extensionality and compare the values at `x`.

Simplify using `[Darboux.rho, schr]`. Establish `toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ → ActsD (evI F) (M.heisLine ψ u) f f₁` using `fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h`. Establish `uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ → ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂` using `fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2`. Use `choose A' hA' using fun w => (hfr.2.1 w).2`. Use `choose C' hC' using fun w => (hfr.2.2 w).2`.

Establish `decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ`. Introduce `u w`. Rewrite using `[show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ = (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by`. Rewrite using `[Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc], hA', hC']`.

Simplify using the standard rewrite rules. Establish `der : ∀ u, At (evI F) u → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ, (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T, ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))` using `fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)`. Establish `tw : ∀ w (c : Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (e : ℂ), A w * (e • (Jm (P w) (Q w) * c * Jm (R w) (S w))) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ)`. Introduce `w c e`. Establish `h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm (R w) (S w) * (C w)ᵀ`.

Rewrite using `[← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]`. Establish `gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))))`.

Use `⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ` using `decomp u`. Establish `hc' : ∀ w, u'.map (piInf (τ w)) = A w * (Complex.I • (Jm (P w) (Q w) * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm (R w) (S w))) * (C w)ᵀ`. Introduce `w`. Rewrite using `[hrel w, tw, ← hc w]`.

Simplify using the standard rewrite rules. Rewrite using `[uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPlD_twist_one, map_smul]`. Establish `gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ` using `fun f₀ h => by`. Unfold `Model.Pol`. Conclude with `Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h`.

Establish `pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ`. Introduce `u hu f hf f₁ h1`. Unfold `Model.Pol at hf ⊢`. Conclude with `Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨T, rfl⟩`. Establish `htop : (M.Pol ψ τ).comap Φ = ⊤`. Use `tensD_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_` and prove the remaining obligations. Take `⟨u, hu, hu'⟩` from `exists_mat_at hcm τ (fun w' => A w' * Function.update (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w' * (C w')ᵀ)`. Establish `hs : sumPl (fun w' => heisOp (Function.update (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w')) T = atPl w (heisOp c) T`.

Rewrite using `[sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Function.update_of_ne hb, heisOp_zero, atPl_zero']`. Simplify using the standard rewrite rules.

Use `pol_der u hu _ hT _ (der u hu _ hu' T)` as an intermediate fact. Rewrite `this` using `[hs]`. Then use the resulting hypothesis. Establish `: T ∈ (M.Pol ψ τ).comap Φ` using `htop ▸ Submodule.mem_top`. Conclude with `this`. Unfold `Model.Pol`.

Use `sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩` and prove the remaining obligations. Take `⟨ε, hε⟩` from `hf₀`. Take `⟨z, hz⟩` from `GlobalTheory.T.fock_vacuum_line_placewise_signatures F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1 Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' => hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ …`. Conclude with `⟨z • PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))), by rw [map_smul, hz]⟩`. Take `⟨T, rfl⟩` from `hf`.

Conclude with `⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩`.
-/
theorem polRangeD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (P Q R S : InfinitePlace F → ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → IsStd ψ →
    FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Jm (P w) (Q w)) →
    (∀ w, W.θ w * C w = C w * Jm (R w) (S w)) → IsFockMapD ψ τ M.co A C Φ → LinearMap.range Φ = M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ
  have hL := GlobalTheory.RealLift.actsLaws
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
  have der : ∀ u, At (evI F) u → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T,
      ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T)) :=
    fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)
  have tw : ∀ w (c : Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (e : ℂ),
      A w * (e • (Jm (P w) (Q w) * c * Jm (R w) (S w))) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm (R w) (S w) * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']
    calc A w * (e • (Jm (P w) (Q w) * c * Jm (R w) (S w))) * (C w)ᵀ
          = e • ((A w * Jm (P w) (Q w)) * c * (Jm (R w) (S w) * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  have gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))))) := by
    refine ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
    have hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := decomp u
    have hc' : ∀ w, u'.map (piInf (τ w)) =
        A w * (Complex.I • (Jm (P w) (Q w) * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm (R w) (S w))) * (C w)ᵀ := by
      intro w; rw [hrel w, tw, ← hc w]; simp
    rw [uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPlD_twist_one, map_smul]
  have gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h => by
    unfold Model.Pol
    exact Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := by
    intro u hu f hf f₁ h1
    unfold Model.Pol at hf ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    have htop : (M.Pol ψ τ).comap Φ = ⊤ := by
      refine tensD_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_
      obtain ⟨u, hu, hu'⟩ := exists_mat_at hcm τ
        (fun w' => A w' * Function.update (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w' * (C w')ᵀ)
      have hs : sumPl (fun w' => heisOp (Function.update
          (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w')) T = atPl w (heisOp c) T := by
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
      obtain ⟨z, hz⟩ := GlobalTheory.T.fock_vacuum_line_placewise_signatures F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
        Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
          hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
      exact ⟨z • PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))), by rw [map_smul, hz]⟩
    · obtain ⟨T, rfl⟩ := hf
      exact ⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩

end GlobalTheory.HoweD.PolRangeD

end
