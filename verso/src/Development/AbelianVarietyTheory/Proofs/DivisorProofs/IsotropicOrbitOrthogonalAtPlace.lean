import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.IsoOrthLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]`.
-/
theorem sigma_sigma {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Consider the case `tmul a x => show a ⊗ₜ[F] σ (σ x) = a ⊗ₜ[F] x`. Rewrite using `[hσ]`.
-/
theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x =>
    show a ⊗ₜ[F] σ (σ x) = a ⊗ₜ[F] x
    rw [hσ]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hJ, hσ]`. Simplify using `only [Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_skew {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x w : Fin d → E) : form σ J x w = -σ (form σ J w x) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hJ, hσ]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Set `S : Submodule E (Fin n → E)` to `{ carrier := {z | ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y} add_mem' := by`. Introduce and unpack `a b ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩`. Use `⟨s + s', t + t', u + u', ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_add, add_smul, add_smul]`. Normalize the expressions using the abelian group laws.

Use the proof step `zero_mem' := ⟨0, 0, 0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨s, t, u, rfl⟩`. Use `⟨c * s, c * t, c • u, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul] }`.

Establish `h1 : Submodule.span E (L : Set (Fin n → E)) ≤ S` using `Submodule.span_le.2 fun z hz => hs z hz`. Rewrite `h1` using `[hL.span_eq_top]`. Conclude with `h1 Submodule.mem_top`.
-/
theorem span_decomp {n n₁ : ℕ} (H : Plane E n n₁) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E)
    (hs : ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y) (z : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y := by
  let S : Submodule E (Fin n → E) :=
    { carrier := {z | ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y}
      add_mem' := by
        rintro a b ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩
        refine ⟨s + s', t + t', u + u', ?_⟩
        rw [Matrix.mulVec_add, add_smul, add_smul]
        abel
      zero_mem' := ⟨0, 0, 0, by simp⟩
      smul_mem' := by
        rintro c a ⟨s, t, u, rfl⟩
        refine ⟨c * s, c * t, c • u, ?_⟩
        rw [Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul] }
  have h1 : Submodule.span E (L : Set (Fin n → E)) ≤ S := Submodule.span_le.2 fun z hz => hs z hz
  rw [hL.span_eq_top] at h1
  exact h1 Submodule.mem_top

/- English proof (translation)
Use `show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _`. Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]`.
-/
theorem trace_inclR (e : E) : Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) =
    algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

/- English proof (translation)
Set `b` to `Module.finBasis F E`. Set `dd` to `(Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b`. Establish `key : ∀ t : AE F E, t = ∑ i, Algebra.trace (AF F) (AE F E) (t * inclR (F` using `F) (AF F) (b i)) • inclR (F := F) (AF F) (dd i) := by`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => conv_lhs => rw [hx, hy]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[add_mul, map_add, add_smul]`.

Consider the case `tmul a x`. Establish `e1 : ∀ i, (a ⊗ₜ[F] x : AE F E) * inclR (F` using `F) (AF F) (b i) = a • inclR (F := F) (AF F) (x * b i) := by`. Introduce `i`. Use `show (a ⊗ₜ[F] x : AF F ⊗[F] E) * ((1 : AF F) ⊗ₜ[F] b i) = a • ((1 : AF F) ⊗ₜ[F] (x * b i))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Simplify using `only [e1, LinearMap.map_smul, trace_inclR, smul_eq_mul]`. Establish `e2 : ∀ i, (a * algebraMap F (AF F) (Algebra.trace F E (x * b i))) • inclR (F` using `F) (AF F) (dd i) = a ⊗ₜ[F] (Algebra.trace F E (x * b i) • dd i) := by`. Introduce `i`. Use `show (a * algebraMap F (AF F) (Algebra.trace F E (x * b i))) • ((1 : AF F) ⊗ₜ[F] dd i) = _`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]`.

Simplify using `only [e2]`. Rewrite using `[← TensorProduct.tmul_sum]`. Use `congr 1`. Use `conv_lhs => rw [← dd.sum_repr x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]`. Rewrite using `[key t]`. Simplify using `[h]`.
-/
theorem tr_nondeg (t : AE F E) (h : ∀ e : E, Algebra.trace (AF F) (AE F E) (t * inclR (F := F) (AF F) e) = 0) :
    t = 0 := by
  classical
  let b := Module.finBasis F E
  let dd := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b
  have key : ∀ t : AE F E, t = ∑ i, Algebra.trace (AF F) (AE F E) (t * inclR (F := F) (AF F) (b i)) •
      inclR (F := F) (AF F) (dd i) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      conv_lhs => rw [hx, hy]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [add_mul, map_add, add_smul]
    | tmul a x =>
      have e1 : ∀ i, (a ⊗ₜ[F] x : AE F E) * inclR (F := F) (AF F) (b i) = a • inclR (F := F) (AF F) (x * b i) := by
        intro i
        show (a ⊗ₜ[F] x : AF F ⊗[F] E) * ((1 : AF F) ⊗ₜ[F] b i) = a • ((1 : AF F) ⊗ₜ[F] (x * b i))
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [e1, LinearMap.map_smul, trace_inclR, smul_eq_mul]
      have e2 : ∀ i, (a * algebraMap F (AF F) (Algebra.trace F E (x * b i))) • inclR (F := F) (AF F) (dd i) =
          a ⊗ₜ[F] (Algebra.trace F E (x * b i) • dd i) := by
        intro i
        show (a * algebraMap F (AF F) (Algebra.trace F E (x * b i))) • ((1 : AF F) ⊗ₜ[F] dd i) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
      simp only [e2]
      rw [← TensorProduct.tmul_sum]
      congr 1
      conv_lhs => rw [← dd.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  rw [key t]
  simp [h]

/- English proof (translation)
Rewrite using `[co.form]`. Simplify using `[GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]`.
-/
theorem locCo_form {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : Pl F) (x u : W) :
    (GlobalTheory.LatVac.locCo co v x).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v x).2 = evFin F v (B x u) := by
  rw [co.form]
  simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

/- English proof (translation)
Use `⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[← LinearEquiv.map_smul, ← co.e.symm.map_zero]`. Use `congr 1`. Use `Prod.ext (funext fun k => ?_) (funext fun k => ?_)` and prove the remaining obligations.

Conclude with `GlobalTheory.LatVac.at_liftV v _ a ha`. Conclude with `GlobalTheory.LatVac.at_liftV v _ a ha`. Apply the tactic sequence `refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>`. Simplify using `[GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]`.
-/
theorem locCo_surj {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : Pl F)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = w := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩
  · intro a ha
    rw [← LinearEquiv.map_smul, ← co.e.symm.map_zero]
    congr 1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

/- English proof (translation)
Use extensionality with `i l`. Simplify using `only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, incV, incM, Matrix.map_apply]`. Establish `h1 : m i l = ∑ j, m i j * inclR (F` using `F) (AF F) (s j * x l + ∑ q, ι l q * U q j + t j * y l) := by`. Simplify using `only [hE, apply_ite (inclR (F := F) (AF F)), map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[h1]`.

Simplify using `only [map_add, map_mul, map_sum, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]`. Use `congr 1`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem decomp {n d d₁ : ℕ} (x y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E) (s t : Fin d → E)
    (U : Matrix (Fin d₁) (Fin d) E)
    (hE : ∀ j l, s j * x l + ∑ q, ι l q * U q j + t j * y l = if l = j then 1 else 0)
    (m : Matrix (Fin n) (Fin d) (AE F E)) :
    m = Matrix.vecMulVec (m *ᵥ incV F s) (incV F x) + m * (incM F U)ᵀ * (incM F ι)ᵀ +
      Matrix.vecMulVec (m *ᵥ incV F t) (incV F y) := by
  ext i l
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, incV, incM, Matrix.map_apply]
  have h1 : m i l = ∑ j, m i j * inclR (F := F) (AF F) (s j * x l + ∑ q, ι l q * U q j + t j * y l) := by
    simp only [hE, apply_ite (inclR (F := F) (AF F)), map_one, map_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [h1]
  simp only [map_add, map_mul, map_sum, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => ?_; ring
  · refine Finset.sum_congr rfl fun j _ => ?_; ring

/- English proof (translation)
Establish `hc : ∀ e : E, cA σ (inclR (F` using `F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl`. Establish `hx' : ∀ l, ∑ j, inclR (F` using `F) (AF F) (x j) * inclR (F := F) (AF F) (JW j l) = inclR (F := F) (AF F) (σ (t l)) := by`. Introduce `l`. Rewrite using `[← hx l, map_sum]`. Simplify using `only [map_mul]`.

Simplify using `only [hTens, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, hc, incV, incM, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `congrArg (fun z => yv i * inclR (F := F) (AF F) (JX i k) * cA σ (m k l) * z) (hx' l)` as an intermediate fact. Simplify using `only [Finset.mul_sum] at this`. Rewrite using `[show yv i * inclR (F := F) (AF F) (JX i k) * (cA σ (m k l) * inclR (F := F) (AF F) (σ (t l))) = yv i * inclR (F := F) (AF F) (JX i k) * cA σ (m k l) * inclR (F := F) (AF F) (σ (t l)) by ring, ← this]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_left (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x t : Fin d → E) (hx : ∀ l, ∑ j, x j * JW j l = σ (t l)) (yv : Fin n → AE F E)
    (m : Matrix (Fin n) (Fin d) (AE F E)) :
    hTens (cA σ) (incM F JX) (incM F JW) (Matrix.vecMulVec yv (incV F x)) m =
      ∑ i, ∑ k, yv i * incM F JX i k * cA σ ((m *ᵥ incV F t) k) := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have hx' : ∀ l, ∑ j, inclR (F := F) (AF F) (x j) * inclR (F := F) (AF F) (JW j l) =
      inclR (F := F) (AF F) (σ (t l)) := by
    intro l; rw [← hx l, map_sum]; simp only [map_mul]
  simp only [hTens, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, hc, incV, incM,
    Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := congrArg (fun z => yv i * inclR (F := F) (AF F) (JX i k) * cA σ (m k l) * z) (hx' l)
  simp only [Finset.mul_sum] at this
  rw [show yv i * inclR (F := F) (AF F) (JX i k) * (cA σ (m k l) * inclR (F := F) (AF F) (σ (t l))) =
    yv i * inclR (F := F) (AF F) (JX i k) * cA σ (m k l) * inclR (F := F) (AF F) (σ (t l)) by ring, ← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `u hu`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.smul_sum, Pi.zero_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `h` using `congrFun (congrFun (hm u hu) i) j`.

Simplify using `only [Matrix.smul_apply, Matrix.zero_apply] at h`. Rewrite using `[← smul_mul_assoc, h, zero_mul]`.
-/
theorem at_mulVec {n d : ℕ} {v : Pl F} {m : Matrix (Fin n) (Fin d) (AE F E)} (hm : At (evFin F v) m) (e : Fin d → AE F E) :
    At (evFin F v) (m *ᵥ e) := by
  intro u hu
  funext i
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.smul_sum, Pi.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h := congrFun (congrFun (hm u hu) i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply] at h
  rw [← smul_mul_assoc, h, zero_mul]

/- English proof (translation)
Introduce `u hu`. Rewrite using `[← Matrix.smul_mul, hm u hu, Matrix.zero_mul]`.
-/
theorem at_mul {n d k : ℕ} {v : Pl F} {m : Matrix (Fin n) (Fin d) (AE F E)} (hm : At (evFin F v) m)
    (N : Matrix (Fin d) (Fin k) (AE F E)) : At (evFin F v) (m * N) := by
  intro u hu
  rw [← Matrix.smul_mul, hm u hu, Matrix.zero_mul]

/- English proof (translation)
Introduce `u hu`. Use extensionality with `i j`. Establish `h` using `congrFun (hy u hu) i`. Simplify using `only [Pi.smul_apply, Pi.zero_apply] at h`. Simplify using `only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]`.

Rewrite using `[← smul_mul_assoc, h, zero_mul]`.
-/
theorem at_vecMulVec {n d : ℕ} {v : Pl F} {yv : Fin n → AE F E} (hy : At (evFin F v) yv) (x : Fin d → AE F E) :
    At (evFin F v) (Matrix.vecMulVec yv x) := by
  intro u hu
  ext i j
  have h := congrFun (hy u hu) i
  simp only [Pi.smul_apply, Pi.zero_apply] at h
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  rw [← smul_mul_assoc, h, zero_mul]

/- English proof (translation)
Simplify using `only [form]`. Rewrite using `[show (fun i => σ ((a + b) i)) = (fun i => σ (a i)) + (fun i => σ (b i)) from funext fun i => map_add σ _ _, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem form_add_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x a b : Fin d → E) :
    form σ J x (a + b) = form σ J x a + form σ J x b := by
  simp only [form]
  rw [show (fun i => σ ((a + b) i)) = (fun i => σ (a i)) + (fun i => σ (b i)) from funext fun i => map_add σ _ _,
    Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [form]`. Rewrite using `[show (fun i => σ ((c • a) i)) = σ c • (fun i => σ (a i)) from funext fun i => by simp [map_mul], Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem form_smul_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x a : Fin d → E) (c : E) :
    form σ J x (c • a) = σ c * form σ J x a := by
  simp only [form]
  rw [show (fun i => σ ((c • a) i)) = σ c • (fun i => σ (a i)) from funext fun i => by simp [map_mul],
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single l (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem form_single (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x : Fin d → E) (l : Fin d) :
    form σ J x (Pi.single l 1) = ∑ j, x j * J j l := by
  simp only [form, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single l (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
  simp

/- English proof (translation)
Use `set cb : Fin n → AE F E := fun k => cA σ (b k) with hcbdef`. Use `set β := incM F JX *ᵥ cb with hβdef`. Establish `hβat : ∀ i, At (evFin F v) (β i)`. Introduce `i u hu`. Establish `hcb : u • cb = 0`.

Use function extensionality and compare the values at `k`. Use `congrFun (hb u hu) k` as an intermediate fact. Simplify using `only [Pi.smul_apply, Pi.zero_apply] at this ⊢`. Rewrite using `[hcbdef]`. Simplify using `only`.

Rewrite using `[← map_smul, this, map_zero]`. Use `congrFun (congrArg (fun w => incM F JX *ᵥ w) hcb) i` as an intermediate fact. Simplify using `only [Matrix.mulVec_smul, Matrix.mulVec_zero, Pi.smul_apply, Pi.zero_apply] at this`. Conclude with `this`. Establish `hβ : ∀ i, β i = 0`.

Introduce `i`. Apply `tr_nondeg` to reduce the goal to its premises. Introduce `e`. Use `set T := Algebra.trace (AF F) (AE F E) (β i * inclR (F := F) (AF F) e) with hT`. Establish `hTat : At (evFin F v) T`.

Introduce `u hu`. Rewrite using `[hT, smul_eq_mul, ← smul_eq_mul, ← LinearMap.map_smul, ← smul_mul_assoc, hβat i u hu, zero_mul, map_zero]`. Establish `hev : evFin F v T = 0` using `by set l := GlobalTheory.LatVac.liftV v (1 : Fv F v) set r : AE F E := algebraMap (AF F) (AE F E) l * inclR (F := F) (AF F) e`. Establish `hr : At (evFin F v) (Pi.single i r : Fin n → AE F E)`. Introduce `u hu`.

Establish `hul : u * l = 0` using `GlobalTheory.LatVac.at_liftV v 1 u hu`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, r]`.

Rewrite using `[Algebra.smul_def, ← mul_assoc, ← map_mul, hul, map_zero, zero_mul]`. Simplify using `[Pi.single_apply, hj]`. Establish `h1` using `h _ hr`. Establish `e1 : ∑ i', ∑ k, (Pi.single i r : Fin n → AE F E) i' * incM F JX i' k * cA σ (b k) = r * β i`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]`.

Simplify using `only [Pi.single_eq_same, hβdef, Matrix.mulVec, dotProduct, Finset.mul_sum, cb]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, show -1 * (r * β i) = l • (-(β i * inclR (F := F) (AF F) e)) by`. Rewrite using `[Algebra.smul_def]`.

Simplify using `only [r]`. Use the proof step `ring, LinearMap.map_smul, smul_eq_mul, map_mul, map_neg,`. Use the proof step `GlobalTheory.LatVac.evFin_liftV, one_mul, ← hT] at h1`. Rewrite `h1` using `[map_neg, neg_eq_zero]`. Conclude with `h1`.

Rewrite using `[GlobalTheory.LatVacArith.eq_liftV_of_at hTat, GlobalTheory.LatVacArith.liftV_one_mul, hev, map_zero]`. Establish `hβ0 : incM F JX *ᵥ cb = 0` using `funext hβ`. Establish `hdet : IsUnit (incM F JX).det`. Rewrite using `[show incM F JX = (inclR (F := F) (AF F)).mapMatrix JX from rfl, ← RingHom.map_det]`. Conclude with `(isUnit_iff_ne_zero.2 hJX).map _`.

Establish `hcb0 : cb = 0`. Rewrite using `[← Matrix.one_mulVec cb, ← Matrix.nonsing_inv_mul _ hdet, ← Matrix.mulVec_mulVec, hβ0, Matrix.mulVec_zero]`. Use function extensionality and compare the values at `k`. Use `congrFun hcb0 k` as an intermediate fact. Simplify using `only [cb, Pi.zero_apply] at this`.

Rewrite using `[Pi.zero_apply, ← cA_cA hσ (b k), this, map_zero]`.
-/
theorem vanish_of_orth (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (JX : Matrix (Fin n) (Fin n) E)
    (hJX : JX.det ≠ 0) (v : Pl F) (b : Fin n → AE F E) (hb : At (evFin F v) b)
    (h : ∀ yv : Fin n → AE F E, At (evFin F v) yv →
      evFin F v (Algebra.trace (AF F) (AE F E) (-1 * ∑ i, ∑ k, yv i * incM F JX i k * cA σ (b k))) = 0) :
    b = 0 := by
  classical
  set cb : Fin n → AE F E := fun k => cA σ (b k) with hcbdef
  set β := incM F JX *ᵥ cb with hβdef
  have hβat : ∀ i, At (evFin F v) (β i) := by
    intro i u hu
    have hcb : u • cb = 0 := by
      funext k
      have := congrFun (hb u hu) k
      simp only [Pi.smul_apply, Pi.zero_apply] at this ⊢
      rw [hcbdef]
      simp only
      rw [← map_smul, this, map_zero]
    have := congrFun (congrArg (fun w => incM F JX *ᵥ w) hcb) i
    simp only [Matrix.mulVec_smul, Matrix.mulVec_zero, Pi.smul_apply, Pi.zero_apply] at this
    exact this
  have hβ : ∀ i, β i = 0 := by
    intro i
    apply tr_nondeg
    intro e
    set T := Algebra.trace (AF F) (AE F E) (β i * inclR (F := F) (AF F) e) with hT
    have hTat : At (evFin F v) T := by
      intro u hu
      rw [hT, smul_eq_mul, ← smul_eq_mul, ← LinearMap.map_smul, ← smul_mul_assoc, hβat i u hu, zero_mul, map_zero]
    have hev : evFin F v T = 0 := by
      set l := GlobalTheory.LatVac.liftV v (1 : Fv F v)
      set r : AE F E := algebraMap (AF F) (AE F E) l * inclR (F := F) (AF F) e
      have hr : At (evFin F v) (Pi.single i r : Fin n → AE F E) := by
        intro u hu
        have hul : u * l = 0 := GlobalTheory.LatVac.at_liftV v 1 u hu
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, r]
          rw [Algebra.smul_def, ← mul_assoc, ← map_mul, hul, map_zero, zero_mul]
        · simp [Pi.single_apply, hj]
      have h1 := h _ hr
      have e1 : ∑ i', ∑ k, (Pi.single i r : Fin n → AE F E) i' * incM F JX i' k * cA σ (b k) = r * β i := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
        simp only [Pi.single_eq_same, hβdef, Matrix.mulVec, dotProduct, Finset.mul_sum, cb]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [e1, show -1 * (r * β i) = l • (-(β i * inclR (F := F) (AF F) e)) by
        rw [Algebra.smul_def]; simp only [r]; ring, LinearMap.map_smul, smul_eq_mul, map_mul, map_neg,
        GlobalTheory.LatVac.evFin_liftV, one_mul, ← hT] at h1
      rw [map_neg, neg_eq_zero] at h1
      exact h1
    rw [GlobalTheory.LatVacArith.eq_liftV_of_at hTat, GlobalTheory.LatVacArith.liftV_one_mul, hev, map_zero]
  have hβ0 : incM F JX *ᵥ cb = 0 := funext hβ
  have hdet : IsUnit (incM F JX).det := by
    rw [show incM F JX = (inclR (F := F) (AF F)).mapMatrix JX from rfl, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hJX).map _
  have hcb0 : cb = 0 := by
    rw [← Matrix.one_mulVec cb, ← Matrix.nonsing_inv_mul _ hdet, ← Matrix.mulVec_mulVec, hβ0, Matrix.mulVec_zero]
  funext k
  have := congrFun hcb0 k
  simp only [cb, Pi.zero_apply] at this
  rw [Pi.zero_apply, ← cA_cA hσ (b k), this, map_zero]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M hB hX hW hH v`. Establish `hσ` using `sigma_sigma hB.cm`. Use `⟨fun u hu _ u' hu' _ => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[locCo_form M.co v u u', GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes F E σ n d d₁ X.J W.J H' hH.xx u hu u' hu', map_zero]`. Take `⟨m, hm, rfl⟩` from `locCo_surj M.co v w`.

Establish `hsp` using `span_decomp H' W.L hW.lat (fun z hz => by`. Take `⟨s, t, u, -, -, -, h⟩` from `hH.split z hz`. Conclude with `⟨s, t, u, h⟩)`. Use `choose s t u hstu using fun j : Fin d => hsp (Pi.single j 1)`. Set `U : Matrix (Fin d₁) (Fin d) E` to `fun q j => u j q`.

Establish `hE : ∀ j l, s j * H'.x l + ∑ q, H'.ι l q * U q j + t j * H'.y l = if l = j then 1 else 0`. Introduce `j l`. Establish `h` using `congrFun (hstu j) l`. Simplify using `only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h`. Rewrite using `[h]`.

Establish `hdec` using `decomp (n := n) H'.x H'.y H'.ι s t U hE m`. Establish `hx : ∀ l, ∑ j, H'.x j * W.J j l = σ (t l)`. Introduce `l`. Rewrite using `[← form_single σ W.J H'.x l, hstu l, form_add_right, form_add_right, form_smul_right, form_smul_right, hH.xx, hH.xy, form_skew hσ hW.skew H'.x (H'.ι *ᵥ u l), (hH.orth (u l)).1]`. Simplify using the standard rewrite rules.

Establish `hJX : X.J.det ≠ 0`. Take `⟨φ⟩ : Nonempty (F →+* ℂ)` from `inferInstance`. Establish `h0` using `GlobalTheory.IwLine.det_ne_zero_of_sig (hX.sig (InfinitePlace.mk φ))`. Introduce `e`. Apply `h0` to reduce the goal to its premises.

Rewrite using `[show X.J.map (B.emb (InfinitePlace.mk φ)).1 = RingHom.mapMatrix (B.emb (InfinitePlace.mk φ)).1 X.J from rfl, ← RingHom.map_det, e, map_zero]`. Establish `hb0 : m *ᵥ incV F t = 0`. Use `vanish_of_orth σ hσ X.J hJX v _ (at_mulVec hm _) fun yv hyv => ?_` and prove the remaining obligations. Establish `h` using `hw (Matrix.vecMulVec yv (incV F H'.x)) ⟨yv, rfl⟩ (at_vecMulVec hyv _)`. Rewrite `h` using `[locCo_form M.co v]`.

Rewrite using `[← h, symp, hTens_left σ X.J W.J H'.x t hx yv m]`. Use `⟨Matrix.vecMulVec (m *ᵥ incV F s) (incV F H'.x), ⟨_, rfl⟩, at_vecMulVec (at_mulVec hm _) _, m * (incM F U)ᵀ, at_mul hm _, ?_⟩` and prove the remaining obligations. Establish `h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite using `[h1, Matrix.one_mul, ← map_add]`. Use `congr 1`.

Use `conv_lhs => rw [hdec]`. Rewrite using `[hb0, Matrix.zero_vecMulVec, add_zero]`.
-/
theorem isotropic_orbit_orthogonal_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    (∀ u ∈ iso0 (F := F) n H', At (evFin F v) u → ∀ u' ∈ iso0 (F := F) n H', At (evFin F v) u' →
      (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u').2 -
        (GlobalTheory.LatVac.locCo M.co v u').1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0) ∧
    ∀ w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
      (∀ u ∈ iso0 (F := F) n H', At (evFin F v) u →
        (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0) →
      ∃ u ∈ iso0 (F := F) n H', At (evFin F v) u ∧ ∃ z : Matrix (Fin n) (Fin d₁) (AE F E), At (evFin F v) z ∧
        w = GlobalTheory.LatVac.locCo M.co v u +
          GlobalTheory.LatVac.locCo M.co v (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M hB hX hW hH v
  have hσ := sigma_sigma hB.cm
  refine ⟨fun u hu _ u' hu' _ => ?_, fun w hw => ?_⟩
  · rw [locCo_form M.co v u u', GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes F E σ n d d₁ X.J W.J H' hH.xx u hu u' hu', map_zero]
  · obtain ⟨m, hm, rfl⟩ := locCo_surj M.co v w
    have hsp := span_decomp H' W.L hW.lat (fun z hz => by
      obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
      exact ⟨s, t, u, h⟩)
    choose s t u hstu using fun j : Fin d => hsp (Pi.single j 1)
    let U : Matrix (Fin d₁) (Fin d) E := fun q j => u j q
    have hE : ∀ j l, s j * H'.x l + ∑ q, H'.ι l q * U q j + t j * H'.y l = if l = j then 1 else 0 := by
      intro j l
      have h := congrFun (hstu j) l
      simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h
      rw [h]
    have hdec := decomp (n := n) H'.x H'.y H'.ι s t U hE m
    have hx : ∀ l, ∑ j, H'.x j * W.J j l = σ (t l) := by
      intro l
      rw [← form_single σ W.J H'.x l, hstu l, form_add_right, form_add_right, form_smul_right, form_smul_right, hH.xx, hH.xy,
        form_skew hσ hW.skew H'.x (H'.ι *ᵥ u l), (hH.orth (u l)).1]
      simp
    have hJX : X.J.det ≠ 0 := by
      obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
      have h0 := GlobalTheory.IwLine.det_ne_zero_of_sig (hX.sig (InfinitePlace.mk φ))
      intro e
      apply h0
      rw [show X.J.map (B.emb (InfinitePlace.mk φ)).1 = RingHom.mapMatrix (B.emb (InfinitePlace.mk φ)).1 X.J from rfl,
        ← RingHom.map_det, e, map_zero]
    have hb0 : m *ᵥ incV F t = 0 := by
      refine vanish_of_orth σ hσ X.J hJX v _ (at_mulVec hm _) fun yv hyv => ?_
      have h := hw (Matrix.vecMulVec yv (incV F H'.x)) ⟨yv, rfl⟩ (at_vecMulVec hyv _)
      rw [locCo_form M.co v] at h
      rw [← h, symp, hTens_left σ X.J W.J H'.x t hx yv m]
    refine ⟨Matrix.vecMulVec (m *ᵥ incV F s) (incV F H'.x), ⟨_, rfl⟩, at_vecMulVec (at_mulVec hm _) _,
      m * (incM F U)ᵀ, at_mul hm _, ?_⟩
    have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, Matrix.one_mul, ← map_add]
    congr 1
    conv_lhs => rw [hdec]
    rw [hb0, Matrix.zero_vecMulVec, add_zero]

end GlobalTheory.IsoOrthLoc
