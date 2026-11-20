import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.QPl GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw.RescTest
variable {D : D7} {c : Comm D} {t : Tup c}

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Introduce and unpack `rfl`. Simplify using `[hn.ne'] at h`.
-/
theorem root_ne {z : ℂ} (h : ∃ n : ℕ, 0 < n ∧ z ^ n = 1) : z ≠ 0 := by
  obtain ⟨n, hn, h⟩ := h
  rintro rfl
  simp [hn.ne'] at h

/- English proof (translation)
Establish `h : ∀ j α γ, s' j α * (s' (j + 1) γ)⁻¹ * (s j α * (s (j + 1) γ)⁻¹) = s' j α * s j α * (s' (j + 1) γ * s (j + 1) γ)⁻¹` using `fun j α γ => by rw [mul_inv]; ring`. Consider the cases of `w`. Simplify using `only [resc, smul_smul, h]`.
-/
theorem resc_resc (w : VTup t) (s s' : ∀ j, t.Ch j → ℂ) : resc (resc w s) s' = resc w (fun j α => s' j α * s j α) := by
  have h : ∀ j α γ, s' j α * (s' (j + 1) γ)⁻¹ * (s j α * (s (j + 1) γ)⁻¹) = s' j α * s j α * (s' (j + 1) γ * s (j + 1) γ)⁻¹ :=
    fun j α γ => by rw [mul_inv]; ring
  cases w; simp only [resc, smul_smul, h]

/- English proof (translation)
Establish `h : ∀ j α, (s j α)⁻¹ = s j α` using `fun j α => inv_eq_of_mul_eq_one_right (by rw [← sq, hs])`. Simplify using `only [twist, resc, h]`.
-/
theorem twist_eq (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ^ 2 = 1) : twist w s = resc w s := by
  have h : ∀ j α, (s j α)⁻¹ = s j α := fun j α => inv_eq_of_mul_eq_one_right (by rw [← sq, hs])
  simp only [twist, resc, h]

/- English proof (translation)
Take `⟨w₀, s, hs, h, e⟩` from `h`. Conclude with `⟨w₀, s, fun j α => ⟨2, two_pos, hs j α⟩, h, e.trans (twist_eq _ _ hs)⟩`.
-/
theorem of_qpinS {v : VCom c} {w : VTup t} (h : QPinS v w) : QPinU v w := by
  obtain ⟨w₀, s, hs, h, e⟩ := h
  exact ⟨w₀, s, fun j α => ⟨2, two_pos, hs j α⟩, h, e.trans (twist_eq _ _ hs)⟩

/- English proof (translation)
Take `⟨w₀, s, hs, h, rfl⟩` from `h`. Use `⟨w₀, _, fun j α => ?_, h, resc_resc _ _ _⟩` and prove the remaining obligations. Take `⟨n, hn, e⟩` from `hs j α`. Take `⟨m, hm, e'⟩` from `hs' j α`. Conclude with `⟨n * m, Nat.mul_pos hn hm, by rw [mul_pow, pow_mul (s j α), e, mul_comm n, pow_mul, e']; simp⟩`.
-/
theorem qpinU_resc {v : VCom c} {w : VTup t} (h : QPinU v w) (s' : ∀ j, t.Ch j → ℂ)
    (hs' : ∀ j α, ∃ n : ℕ, 0 < n ∧ s' j α ^ n = 1) : QPinU v (resc w s') := by
  obtain ⟨w₀, s, hs, h, rfl⟩ := h
  refine ⟨w₀, _, fun j α => ?_, h, resc_resc _ _ _⟩
  obtain ⟨n, hn, e⟩ := hs j α
  obtain ⟨m, hm, e'⟩ := hs' j α
  exact ⟨n * m, Nat.mul_pos hn hm, by rw [mul_pow, pow_mul (s j α), e, mul_comm n, pow_mul, e']; simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem comb_lc (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T e f = Finsupp.linearCombination ℂ (fun x => heisO ψ S T x f) e := rfl

/- English proof (translation)
Rewrite using `[comb_lc, comb_lc, map_smul]`.
-/
theorem comb_smul_left (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • e) f = a • comb ψ S T e f := by
  rw [comb_lc, comb_lc, map_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trc_lc {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) :
    trc e f = Finsupp.linearCombination ℂ (fun g => rTrans g f) e := rfl

/- English proof (translation)
Rewrite using `[trc_lc, trc_lc, map_smul]`.
-/
theorem trc_smul_left {V : HSp D} (a : ℂ) (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (a • e) f = a • trc e f := by
  rw [trc_lc, trc_lc, map_smul]

/- English proof (translation)
Use function extensionality and compare the values at `u x`. Simplify using `only [biComb, comb_smul_left, Pi.smul_apply, smul_eq_mul]`. Establish `: (fun u' => b * comb ψ S A' e' (C u') x) = b • fun u' => comb ψ S A' e' (C u') x` using `rfl`. Rewrite using `[this]`. Establish `h2 : ∀ f : WO A S → ℂ, comb ψ A S e (b • f) = b • comb ψ A S e f` using `fun f => by`.

Use function extensionality and compare the values at `y`. Simplify using `only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[h2, Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem biComb_smul2 (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a b : ℂ) (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' (a • e) (b • e') C = (a * b) • biComb ψ A S A' e e' C := by
  funext u x
  simp only [biComb, comb_smul_left, Pi.smul_apply, smul_eq_mul]
  have : (fun u' => b * comb ψ S A' e' (C u') x) = b • fun u' => comb ψ S A' e' (C u') x := rfl
  rw [this]
  have h2 : ∀ f : WO A S → ℂ, comb ψ A S e (b • f) = b • comb ψ A S e f := fun f => by
    funext y
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h2, Pi.smul_apply, smul_eq_mul, mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `h`. Simplify using `only [biLift, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]`.
-/
theorem biLift_move {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS (a • φ) C = a • biLift oma omb vA vS φ C := by
  funext h
  simp only [biLift, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

/- English proof (translation)
Use function extensionality and compare the values at `h₂`. Establish `h2 : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) 0 = a * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0`. Introduce `h₀ h₁`. Establish `e : (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) = a • (fun v => oma (h₀, h₁) (fun u => C u v) 0)`. Use function extensionality and compare the values at `fun v => by`.

Rewrite using `[show (fun u => a * C u v) = a • (fun u => C u v) from rfl, map_smul]`. Both sides reduce to the same expression. Rewrite using `[e, map_smul]`. Both sides reduce to the same expression. Simplify using `only [biLift, Pi.smul_apply, smul_eq_mul, h2]`.

Repeatedly rewrite using `[show ∀ x y : ℂ, x * (a * y) = a * (x * y) from fun x y => mul_left_comm x a y, integral_const_mul]`.
-/
theorem biLift_smul' {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS φ (a • C) = a • biLift oma omb vA vS φ C := by
  funext h₂
  have h2 : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) 0 =
      a * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 := by
    intro h₀ h₁
    have e : (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) = a • (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
      funext fun v => by
        rw [show (fun u => a * C u v) = a • (fun u => C u v) from rfl, map_smul]
        rfl
    rw [e, map_smul]
    rfl
  simp only [biLift, Pi.smul_apply, smul_eq_mul, h2]
  simp_rw [show ∀ x y : ℂ, x * (a * y) = a * (x * y) from fun x y => mul_left_comm x a y, integral_const_mul]

/- English proof (translation)
Establish `e : ∀ Ξ, handBF s₁ l (a • φ) Ξ = star a • handBF s₁ l φ Ξ` using `fun Ξ => by`. Use function extensionality and compare the values at `h w`. Simplify using `only [GlobalTheory.Unf.handBF, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Rewrite using `[integral_const_mul, star_mul']`. Unfold `Chain.hand`.

Use `GlobalTheory.HandHom.handFB_smul s₂ vL (star a) 1 (handBF s₁ l φ (flatBF s₁ (s₁.om (g, h₁) Φ₁))) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))` as an intermediate fact. Rewrite `this` using `[one_smul, star_star, mul_one]`. Rewrite using `[e, this]`.
-/
theorem hand_smul_fun {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (a : ℂ)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ (a • φ) g h₁ h₂ = a • Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ := by
  have e : ∀ Ξ, handBF s₁ l (a • φ) Ξ = star a • handBF s₁ l φ Ξ := fun Ξ => by
    funext h w
    simp only [GlobalTheory.Unf.handBF, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, star_mul']
  unfold Chain.hand
  have := GlobalTheory.HandHom.handFB_smul s₂ vL (star a) 1 (handBF s₁ l φ (flatBF s₁ (s₁.om (g, h₁) Φ₁))) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))
  rw [one_smul, star_star, mul_one] at this
  rw [e, this]

/- English proof (translation)
Establish `h : ∀ (e : G →₀ ℂ) (F : G → ℂ), ∑ g ∈ e.support, e g * F g = Finsupp.linearCombination ℂ F e` using `fun _ _ => rfl`. Rewrite using `[h, map_smul, ← h, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem sum_supp {G : Type} (a : ℂ) (e : G →₀ ℂ) (F : G → ℂ) :
    ∑ g ∈ (a • e).support, (a • e) g * F g = ∑ g ∈ e.support, e g * (a * F g) := by
  have h : ∀ (e : G →₀ ℂ) (F : G → ℂ), ∑ g ∈ e.support, e g * F g = Finsupp.linearCombination ℂ F e := fun _ _ => rfl
  rw [h, map_smul, ← h, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun γ hγ g => by simp only [Pi.smul_apply, h.1 γ hγ g], h.2.const_smul a⟩`.
-/
theorem contAut_smul {V : HSp D} (a : ℂ) {φ : GA D V → ℂ} (h : IsContAut V φ) : IsContAut V (a • φ) :=
  ⟨fun γ hγ g => by simp only [Pi.smul_apply, h.1 γ hγ g], h.2.const_smul a⟩

def free (w : VTup t) : VTup t := { w with FX := fun _ _ => Set.univ }

/- English proof (translation)
Take `⟨F, h⟩` from `h`. Conclude with `⟨F, h.inj, h.places, h.kom, h.mid, h.lastc, h.eQ, h.eQT, h.dQ, h.ε, h.εT, h.FY, h.cQ⟩`.
-/
theorem qpin_free {v : VCom c} {w : VTup t} (h : QPin v w) : QPin v (free w) := by
  obtain ⟨F, h⟩ := h
  exact ⟨F, h.inj, h.places, h.kom, h.mid, h.lastc, h.eQ, h.eQT, h.dQ, h.ε, h.εT, h.FY, h.cQ⟩

/- English proof (translation)
Simplify using `only [Finset.smul_sum]`. Use `Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Simplify using `only [resc, biComb_smul2, Comm.bl, biLift_smul', biLift_move, smul_smul]`. Use `congr 1`. Use `hs (j + 1) γ` as an intermediate fact.

Clear the denominators using the available nonvanishing facts.
-/
theorem inner (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ≠ 0) (w : VTup t) (j : ℕ) (β : t.Ch (j + 1 + 1))
    (φ : t.Ch j → GA D (c.X j) → ℂ) (C) :
    (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ ((resc w s).dQ j α γ) ((resc w s).dQ (j + 1) γ β) C)) =
      (s (j + 1 + 1) β)⁻¹ • ∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (s j α • φ α)
        (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) C) := by
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
  simp only [resc, biComb_smul2, Comm.bl, biLift_smul', biLift_move, smul_smul]
  congr 1
  have := hs (j + 1) γ
  field_simp

/- English proof (translation)
Introduce `j h Ψ₁ Ψ₂ h₁ h₂ φ hφ f hf hf'`. Use `H j h Ψ₁ Ψ₂ h₁ h₂ (fun α => s j α • φ α) (fun α => ⟨contAut_smul _ (hφ α).1, trivial⟩) f hf hf'` as an intermediate fact. Simplify using `only [inner s hs]`. Use `Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (this.trans (congrArg _ (Finset.sum_congr rfl fun β _ => Eq.symm ?_)))` and prove the remaining obligations. Use `(sum_supp _ _ _).trans (Finset.sum_congr rfl fun g _ => ?_)` and prove the remaining obligations.

Simplify using `only [Comm.bl, biLift_move, Pi.smul_apply, smul_eq_mul, mul_left_comm (f _) (s j α), integral_const_mul]`. Both sides reduce to the same expression. Use `congr 1`. Use function extensionality and compare the values at `h'`. Establish `e : trc ((resc w s).εT (j + 1 + 1) h β) f = s (j + 1 + 1) β • trc (w.εT (j + 1 + 1) h β) f` using `trc_smul_left _ _ _`.

Rewrite using `[e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, mul_inv_cancel₀ (hs _ _), one_mul]`. Both sides reduce to the same expression.
-/
theorem qlast_resc (v : VCom c) (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ≠ 0) (H : QLast v (free w)) :
    QLast v (resc w s) := by
  intro j h Ψ₁ Ψ₂ h₁ h₂ φ hφ f hf hf'
  have := H j h Ψ₁ Ψ₂ h₁ h₂ (fun α => s j α • φ α) (fun α => ⟨contAut_smul _ (hφ α).1, trivial⟩) f hf hf'
  simp only [inner s hs]
  refine Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (this.trans (congrArg _ (Finset.sum_congr rfl fun β _ => Eq.symm ?_)))
  · refine (sum_supp _ _ _).trans (Finset.sum_congr rfl fun g _ => ?_)
    simp only [Comm.bl, biLift_move, Pi.smul_apply, smul_eq_mul, mul_left_comm (f _) (s j α), integral_const_mul]
    rfl
  · congr 1
    funext h'
    have e : trc ((resc w s).εT (j + 1 + 1) h β) f = s (j + 1 + 1) β • trc (w.εT (j + 1 + 1) h β) f := trc_smul_left _ _ _
    rw [e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, mul_inv_cancel₀ (hs _ _), one_mul]
    rfl

/- English proof (translation)
Introduce `j σ h ρ₁ μ₁ ρ₂ μ₂ n₁ n₂ Ψ₁ Ψ₂ h₁ h₂ φ hφ f hf hf'`. Use `H j σ h ρ₁ μ₁ ρ₂ μ₂ n₁ n₂ Ψ₁ Ψ₂ h₁ h₂ (fun α => s j α • φ α) (fun α => ⟨contAut_smul _ (hφ α).1, trivial⟩) f hf hf'` as an intermediate fact. Simplify using `only [inner s hs]`. Use `cast (congrArg₂ (Iter2 ρ₁ μ₁ ρ₂ μ₂) (Eq.symm ?_) (Eq.symm ?_)) this` and prove the remaining obligations. Use function extensionality and compare the values at `q₁ q₂`.

Use `Finset.sum_congr rfl fun α _ => (sum_supp _ _ _).trans (Finset.sum_congr rfl fun g _ => ?_)` and prove the remaining obligations. Use `congr 1`. Establish `e` using `GlobalTheory.HandHom.per_smul (c.B (j + 1 + 1) σ (idx_step h)) c.ψ (s j α) 1 (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (w.eQ j) Ψ₁) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)`. Rewrite `e` using `[one_smul, mul_one, ← hand_smul_fun]`. Conclude with `e.symm`.

Use `congrArg _ (Finset.sum_congr rfl fun β _ => ?_)` and prove the remaining obligations. Establish `e : trc ((resc w s).ε (j + 1 + 1) β) f = s (j + 1 + 1) β • trc (w.ε (j + 1 + 1) β) f` using `trc_smul_left _ _ _`. Rewrite using `[e]`. Use `(GlobalTheory.HandHom.per_smul _ _ _ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[inv_mul_cancel₀ (hs _ _), one_mul]`.

Both sides reduce to the same expression.
-/
theorem qlaw_resc (v : VCom c) (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, s j α ≠ 0) (H : QLaw v (free w)) :
    QLaw v (resc w s) := by
  intro j σ h ρ₁ μ₁ ρ₂ μ₂ n₁ n₂ Ψ₁ Ψ₂ h₁ h₂ φ hφ f hf hf'
  have := H j σ h ρ₁ μ₁ ρ₂ μ₂ n₁ n₂ Ψ₁ Ψ₂ h₁ h₂ (fun α => s j α • φ α) (fun α => ⟨contAut_smul _ (hφ α).1, trivial⟩) f hf hf'
  simp only [inner s hs]
  refine cast (congrArg₂ (Iter2 ρ₁ μ₁ ρ₂ μ₂) (Eq.symm ?_) (Eq.symm ?_)) this
  · funext q₁ q₂
    refine Finset.sum_congr rfl fun α _ => (sum_supp _ _ _).trans (Finset.sum_congr rfl fun g _ => ?_)
    congr 1
    have e := GlobalTheory.HandHom.per_smul (c.B (j + 1 + 1) σ (idx_step h)) c.ψ (s j α) 1
      (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (w.eQ j) Ψ₁)
            (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)
    rw [one_smul, mul_one, ← hand_smul_fun] at e
    exact e.symm
  · refine congrArg _ (Finset.sum_congr rfl fun β _ => ?_)
    have e : trc ((resc w s).ε (j + 1 + 1) β) f = s (j + 1 + 1) β • trc (w.ε (j + 1 + 1) β) f := trc_smul_left _ _ _
    rw [e]
    refine (GlobalTheory.HandHom.per_smul _ _ _ _ _ _).trans ?_
    rw [inv_mul_cancel₀ (hs _ _), one_mul]
    rfl

/- English proof (translation)
Introduce `j σ h`. Take `⟨K, T, a, b, c', d, e, f⟩` from `H j σ h`. Conclude with `⟨K, T, a, b, c', d, e, fun Ψ hΨ α g hg => f Ψ hΨ α g (Finsupp.support_smul hg)⟩`.
-/
theorem qfin_resc (v : VCom c) (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (H : QFin v w) : QFin v (resc w s) := by
  intro j σ h
  obtain ⟨K, T, a, b, c', d, e, f⟩ := H j σ h
  exact ⟨K, T, a, b, c', d, e, fun Ψ hΨ α g hg => f Ψ hΨ α g (Finsupp.support_smul hg)⟩

/- English proof (translation)
Take `⟨w₀, s, hs, h, rfl⟩` from `h`. Conclude with `⟨qlaw_resc v _ s (fun j α => root_ne (hs j α)) (H _ (qpin_free h)).1, qlast_resc v _ s (fun j α => root_ne (hs j α)) (H _ (qpin_free h)).2.1, qfin_resc v _ s (H _ h).2.2⟩`.
-/
theorem laws_of_qpinU (v : VCom c) (H : ∀ w : VTup t, QPin v w → QLaw v w ∧ QLast v w ∧ QFin v w) (w : VTup t)
    (h : QPinU v w) : QLaw v w ∧ QLast v w ∧ QFin v w := by
  obtain ⟨w₀, s, hs, h, rfl⟩ := h
  exact ⟨qlaw_resc v _ s (fun j α => root_ne (hs j α)) (H _ (qpin_free h)).1,
    qlast_resc v _ s (fun j α => root_ne (hs j α)) (H _ (qpin_free h)).2.1, qfin_resc v _ s (H _ h).2.2⟩

/- English proof (translation)
Establish `key : ∀ (w : VTup t) (s : ∀ j, t.Ch j → ℂ), (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) → (∀ j α, ∃ n : ℕ, 0 < n ∧ (s j α)⁻¹ ^ n = 1) ∧ resc (resc w s) (fun j α => (s j α)⁻¹) = w` using `fun w s hs => ⟨fun j α => (hs j α).imp fun n h => ⟨h.1, by rw [inv_pow, h.2, inv_one]⟩, by`. Rewrite using `[resc_resc]`. Simplify using `only [inv_mul_cancel₀ (root_ne (hs _ _)), resc_one]⟩`. Conclude with `⟨fun ⟨w₀, s, hs, h, e⟩ => ⟨_, (key w₀ s hs).1, by rw [e, (key w₀ s hs).2]; exact h⟩, fun ⟨s, hs, h⟩ => ⟨_, _, (key w s hs).1, h, (key w s hs).2.symm⟩⟩`.
-/
theorem qpinU_iff {v : VCom c} {w : VTup t} :
    QPinU v w ↔ ∃ s : ∀ j, t.Ch j → ℂ, (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) ∧ QPin v (resc w s) := by
  have key : ∀ (w : VTup t) (s : ∀ j, t.Ch j → ℂ), (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) →
      (∀ j α, ∃ n : ℕ, 0 < n ∧ (s j α)⁻¹ ^ n = 1) ∧ resc (resc w s) (fun j α => (s j α)⁻¹) = w := fun w s hs =>
    ⟨fun j α => (hs j α).imp fun n h => ⟨h.1, by rw [inv_pow, h.2, inv_one]⟩, by
      rw [resc_resc]
      simp only [inv_mul_cancel₀ (root_ne (hs _ _)), resc_one]⟩
  exact ⟨fun ⟨w₀, s, hs, h, e⟩ => ⟨_, (key w₀ s hs).1, by rw [e, (key w₀ s hs).2]; exact h⟩,
    fun ⟨s, hs, h⟩ => ⟨_, _, (key w s hs).1, h, (key w s hs).2.symm⟩⟩

/- English proof (translation)
Establish `h : ∀ j α, ‖s j α‖ = 1` using `fun j α => by`. Take `⟨n, hn, e⟩` from `hs j α`. Conclude with `Complex.norm_eq_one_of_pow_eq_one e hn.ne'`. Simplify using `[resc, h]`.
-/
theorem norm_dQ (w : VTup t) (s : ∀ j, t.Ch j → ℂ) (hs : ∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) (j α γ x) :
    ‖(resc w s).dQ j α γ x‖ = ‖w.dQ j α γ x‖ := by
  have h : ∀ j α, ‖s j α‖ = 1 := fun j α => by
    obtain ⟨n, hn, e⟩ := hs j α
    exact Complex.norm_eq_one_of_pow_eq_one e hn.ne'
  simp [resc, h]

end GlobalTheory.QTw.RescTest
end
