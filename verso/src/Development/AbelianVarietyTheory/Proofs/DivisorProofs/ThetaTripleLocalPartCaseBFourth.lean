import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarMemIdelesAtOfIsLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvLocOpComm
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.ConeLinLevi

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ v t g₀ g hlev hg hg₀ φ hφ`. Establish `hA : ActsEx` using `GlobalTheory.T.theta_action_exists hP`. Establish `hPr` using `GlobalTheory.ThK.Inhab.pairV' hT`. Establish `hPr₁` using `GlobalTheory.ThK.Inhab.pairV' hT₁`. Establish `h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v)` using `one_mem (UAtSub σ G.W (evFin F v))`.

Establish `h1W₁ : (1 : UA σ G₁.W.J) ∈ UAt σ G₁.W (evFin F v)` using `one_mem (UAtSub σ G₁.W (evFin F v))`. Use `set c : ℂ := fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t with hc`. Establish `hact : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), Acts (evFin F v) (fun Φ => c • om₁' (g₀, 1) Φ) ψ (c • locOp v (om₁' (g₀, 1)) ψ)`. Introduce `ψ hψ r hr`. Use `beta_reduce`.

Rewrite using `[acts_locOp_om hA hPr₁ hg₀ h1W₁ hψ r hr]`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Establish `hevSB : ev' v φ ∈ SB (Fin b × Fin (a + b) → Fv F v)` using `(hL.2.1 v).2 ▸ Submodule.mem_map_of_mem hφ`. Establish `key` using `GlobalTheory.EvLocIntertwine.ev_locOp_comm B.ψ G.M' G₁.M' e' ei' ev' hT.geo.hM' hT₁.geo.hM' hL v (om' (g, 1)) (fun Φ => c • om₁' (g₀, 1) Φ) (fun ψ hψ => ⟨_, locOp_mem v _ ψ, acts_locOp_om hA hPr hg h1W hψ⟩) (fun ψ hψ => ⟨_, (SB _).smul_mem c (locOp_mem v _ ψ), hact ψ hψ⟩) ((Globa …`.

Rewrite using `[key, locOp_eq hevSB ((SB _).smul_mem c (locOp_mem v _ _)) (hact _ hevSB)]`.
-/
theorem finLaw : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) t g₀ g, IsLevi (W₁ := G₁.V') H t g₀ g → g ∈ UAt σ G.V' (evFin F v) → g₀ ∈ UAt σ G₁.V' (evFin F v) →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      ev' v (locOp v (om' (g, 1)) φ) = fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t • locOp v (om₁' (g₀, 1)) (ev' v φ) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ v t g₀ g hlev hg hg₀ φ hφ
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hP
  have hPr := GlobalTheory.ThK.Inhab.pairV' hT
  have hPr₁ := GlobalTheory.ThK.Inhab.pairV' hT₁
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := one_mem (UAtSub σ G.W (evFin F v))
  have h1W₁ : (1 : UA σ G₁.W.J) ∈ UAt σ G₁.W (evFin F v) := one_mem (UAtSub σ G₁.W (evFin F v))
  set c : ℂ := fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t with hc
  have hact : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v),
      Acts (evFin F v) (fun Φ => c • om₁' (g₀, 1) Φ) ψ (c • locOp v (om₁' (g₀, 1)) ψ) := by
    intro ψ hψ r hr
    beta_reduce
    rw [acts_locOp_om hA hPr₁ hg₀ h1W₁ hψ r hr]
    funext x
    simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hevSB : ev' v φ ∈ SB (Fin b × Fin (a + b) → Fv F v) := (hL.2.1 v).2 ▸ Submodule.mem_map_of_mem hφ
  have key := GlobalTheory.EvLocIntertwine.ev_locOp_comm B.ψ G.M' G₁.M' e' ei' ev' hT.geo.hM' hT₁.geo.hM' hL v
    (om' (g, 1)) (fun Φ => c • om₁' (g₀, 1) Φ)
    (fun ψ hψ => ⟨_, locOp_mem v _ ψ, acts_locOp_om hA hPr hg h1W hψ⟩)
    (fun ψ hψ => ⟨_, (SB _).smul_mem c (locOp_mem v _ ψ), hact ψ hψ⟩)
    ((GlobalTheory.ThK.EvLawBLeft.globalLaw hP F E σ B a b G G₁ H H' hC e' he X om om' om₁ om₁' hT hT₁).2 t g₀ g hlev) φ hφ
  rw [key, locOp_eq hevSB ((SB _).smul_mem c (locOp_mem v _ _)) (hact _ hevSB)]

/- English proof (translation)
Rewrite using `[shiftB, shiftB, Matrix.mul_smul, Matrix.mul_vecMulVec, hm.2.1, Matrix.smul_vecMulVec, smul_smul, ← map_mul, Units.val_mul, mul_comm (t : AE F E), mul_assoc, Units.mul_inv, mul_one]`.
-/
theorem mat_mul_shiftB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} (H' : Plane E d d₁)
    {t : (AE F E)ˣ} {g₀ : UA σ X₁.J} {m : UA σ X.J} (hm : IsLevi (W₁ := X₁) H t g₀ m) (s : (AE F E)ˣ) :
    mat m * shiftB σ H H' (t * s) = shiftB σ H H' s := by
  rw [shiftB, shiftB, Matrix.mul_smul, Matrix.mul_vecMulVec, hm.2.1, Matrix.smul_vecMulVec, smul_smul, ← map_mul,
    Units.val_mul, mul_comm (t : AE F E), mul_assoc, Units.mul_inv, mul_one]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ v μ hμ l hl φ hφ t g₀ m hlev hm hg₀ g hg`. Establish `ht : t ∈ idelesAt E (evFin F v)` using `GlobalTheory.LeviScalarAt.scalar_mem_idelesAt_of_isLevi B H 0 (b + 1) hC.hH v t g₀ m hlev hm`. Take `⟨_, _, _, _, _⟩` from `idelesAt_facts E (evFin F v)`. Use `haveI := hμ`. Establish `hPr` using `GlobalTheory.ThK.Inhab.pairV' hT`.

Establish `h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v)` using `one_mem (UAtSub σ G.W (evFin F v))`. Establish `hevSB : ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ev' v ψ ∈ SB (Fin b × Fin (a + b) → Fv F v)` using `fun ψ hψ => (hL.2.1 v).2 ▸ Submodule.mem_map_of_mem hψ`. Establish `hcomp` using `GlobalTheory.T.local_operator_mul_of_classicalTheorems hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hPr v (m, 1) (g, 1) hm h1W hg h1W φ hφ`. Rewrite `hcomp` using `[Prod.mk_mul_mk, mul_one]`. Use `set F₀ := locOp v (om' (g, 1)) φ with hF₀`.

Establish `hF₀m : F₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)` using `locOp_mem _ _ _`. Set `h' : idelesAt E (evFin F v) → ℂ` to `fun y => l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' (t * y.1)))) F₀)) * (X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)`. Set `c : ℂ` to `(X.ν t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)`. Establish `hint : ∀ y : idelesAt E (evFin F v), l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' y.1))) (locOp v (om' (m * g, 1)) φ))) * (X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) = fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t * h' y`. Introduce `y`.

Establish `hc` using `GlobalTheory.T.local_weil_action_compatibility hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hPr v m 1 hm h1W (shiftB σ H H' (t * y.1)) F₀ hF₀m`. Rewrite `hc` using `[GlobalTheory.StabHaar.mat_one, Matrix.transpose_one, Matrix.mul_one, mat_mul_shiftB H' hlev]`. Rewrite using `[hcomp, ← hc, finLaw hP F E σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ v t g₀ m hlev hm hg₀ _ (locOp_mem _ _ _), map_smul, smul_eq_mul, hl g₀ hg₀ _ (hevSB _ (locOp_mem _ _ _))]`. Simplify using `only [h']`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsh : ∀ y : idelesAt E (evFin F v), l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' ((⟨t, ht⟩ : idelesAt E (evFin F v)) * y).1))) F₀)) * (X.ν ((⟨t, ht⟩ : idelesAt E (evFin F v)) * y).1 : ℂ) * ((absE F E ((⟨t, ht⟩ : idelesAt E (evFin F v)) * y).1 : ℝ) : ℂ) ^ ((a - (b …`. Introduce `y`. Simplify using `only [h', c, Subgroup.coe_mul, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfac : fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t = c * ((absE F E t : ℝ) : ℂ) ^ (b + 1)`.

Take `⟨r, hr⟩` from `hT.geo.even`. Establish `hlt` using `hT.geo.lt`. Establish `hN : a + (b + 2) = 2 * (b + 1 + ((a - (b + 2)) / 2 + 1))` using `by omega`. Establish `hd : (((a + (b + 2) : ℕ) : ℝ) / 2) = ((b + 1 + ((a - (b + 2)) / 2 + 1) : ℕ) : ℝ)`. Rewrite using `[hN]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [fac, c, hd, Real.rpow_natCast, pow_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `key` using `integral_mul_left_eq_self (μ := μ) (fun y : idelesAt E (evFin F v) => l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' y.1))) F₀)) * (X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) ⟨t, ht⟩`. Simplify using `only [hsh] at key`. Simplify using `only [coneLin]`. Rewrite using `[integral_congr_ae (Eventually.of_forall hint), integral_const_mul, hfac, ← hF₀, ← key, integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coneLin_levi : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μ : Measure (idelesAt E (evFin F v))), μ.IsHaarMeasure → ∀ l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l (locOp v (om₁' (g₀, 1)) ψ) = l ψ) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ∀ t g₀ m, IsLevi H t g₀ m → m ∈ UAt σ G.V' (evFin F v) →
        g₀ ∈ UAt σ G₁.V' (evFin F v) → ∀ g ∈ UAt σ G.V' (evFin F v),
          coneLin B G.M' om' v (ev' v) μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l φ (m * g) = ((absE F E t : ℝ) : ℂ) ^ (b + 1) * coneLin B G.M' om' v (ev' v) μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l φ g := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ v μ hμ l hl φ hφ t g₀ m hlev hm hg₀ g hg
  have ht : t ∈ idelesAt E (evFin F v) :=
    GlobalTheory.LeviScalarAt.scalar_mem_idelesAt_of_isLevi B H 0 (b + 1) hC.hH v t g₀ m hlev hm
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ
  have hPr := GlobalTheory.ThK.Inhab.pairV' hT
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := one_mem (UAtSub σ G.W (evFin F v))
  have hevSB : ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ev' v ψ ∈ SB (Fin b × Fin (a + b) → Fv F v) :=
    fun ψ hψ => (hL.2.1 v).2 ▸ Submodule.mem_map_of_mem hψ
  have hcomp := GlobalTheory.T.local_operator_mul_of_classicalTheorems hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hPr v (m, 1) (g, 1) hm h1W hg h1W φ hφ
  rw [Prod.mk_mul_mk, mul_one] at hcomp
  set F₀ := locOp v (om' (g, 1)) φ with hF₀
  have hF₀m : F₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) := locOp_mem _ _ _
  let h' : idelesAt E (evFin F v) → ℂ := fun y =>
    l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' (t * y.1)))) F₀)) * (X.ν y.1 : ℂ) *
      ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)
  let c : ℂ := (X.ν t : ℂ) * ((absE F E t : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)
  have hint : ∀ y : idelesAt E (evFin F v),
      l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' y.1))) (locOp v (om' (m * g, 1)) φ))) *
        (X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) =
        fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t * h' y := by
    intro y
    have hc := GlobalTheory.T.local_weil_action_compatibility hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hPr v m 1 hm h1W (shiftB σ H H' (t * y.1))
      F₀ hF₀m
    rw [GlobalTheory.StabHaar.mat_one, Matrix.transpose_one, Matrix.mul_one, mat_mul_shiftB H' hlev] at hc
    rw [hcomp, ← hc, finLaw hP F E σ B a b G G₁ H H' hC e' he ei' ev' hL X om om' om₁ om₁' hT hT₁ v t g₀ m hlev hm hg₀ _
      (locOp_mem _ _ _), map_smul, smul_eq_mul, hl g₀ hg₀ _ (hevSB _ (locOp_mem _ _ _))]
    simp only [h']
    ring
  have hsh : ∀ y : idelesAt E (evFin F v),
      l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' ((⟨t, ht⟩ : idelesAt E (evFin F v)) * y).1))) F₀)) *
        (X.ν ((⟨t, ht⟩ : idelesAt E (evFin F v)) * y).1 : ℂ) *
        ((absE F E ((⟨t, ht⟩ : idelesAt E (evFin F v)) * y).1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) = c * h' y := by
    intro y
    simp only [h', c, Subgroup.coe_mul, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]
    ring
  have hfac : fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t = c * ((absE F E t : ℝ) : ℂ) ^ (b + 1) := by
    obtain ⟨r, hr⟩ := hT.geo.even
    have hlt := hT.geo.lt
    have hN : a + (b + 2) = 2 * (b + 1 + ((a - (b + 2)) / 2 + 1)) := by omega
    have hd : (((a + (b + 2) : ℕ) : ℝ) / 2) = ((b + 1 + ((a - (b + 2)) / 2 + 1) : ℕ) : ℝ) := by
      rw [hN]; push_cast; ring
    simp only [fac, c, hd, Real.rpow_natCast, pow_add]
    push_cast
    ring
  have key := integral_mul_left_eq_self (μ := μ)
    (fun y : idelesAt E (evFin F v) =>
      l (ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' y.1))) F₀)) * (X.ν y.1 : ℂ) *
        ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) ⟨t, ht⟩
  simp only [hsh] at key
  simp only [coneLin]
  rw [integral_congr_ae (Eventually.of_forall hint), integral_const_mul, hfac, ← hF₀, ← key, integral_const_mul]
  ring

end GlobalTheory.ThK.ConeLinLevi

end
