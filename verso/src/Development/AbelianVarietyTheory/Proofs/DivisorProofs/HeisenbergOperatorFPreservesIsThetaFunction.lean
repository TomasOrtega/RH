import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponential
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups

noncomputable section

open scoped TensorProduct Matrix Topology ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory

namespace GlobalTheory.HeisKeepF

/- English proof (translation)
Use `set c := deriv g 0`. Establish `hd : ∀ s, HasDerivAt g (c * g s) s` using `GlobalTheory.hasDerivAt_of_continuous_additive_to_mul g hc hm h0`. Establish `he : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(c * (s : ℂ)))) (Complex.exp (-(c * (s : ℂ))) * -c) s`. Introduce `s`. Establish `h1 : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-(c * ((1 : ℝ) : ℂ))) s` using `(((hasDerivAt_id s).ofReal_comp).const_mul c).neg`.

Use `replace h1 : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-c) s := h1.congr_deriv (by simp)`. Conclude with `h1.cexp`. Establish `hk : ∀ s, HasDerivAt (fun s : ℝ => g s * Complex.exp (-(c * (s : ℂ)))) 0 s`. Introduce `s`. Use `(hd s).mul (he s)` as an intermediate fact.

Conclude with `this.congr_deriv (by ring)`. Establish `hconst : ∀ s, g s * Complex.exp (-(c * (s : ℂ))) = 1`. Introduce `s`. Use `is_const_of_deriv_eq_zero (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) s 0` as an intermediate fact. Simplify `this` using `[h0]`.

Establish `hg : g = fun s : ℝ => Complex.exp (c * (s : ℂ))`. Use function extensionality and compare the values at `s`. Establish `h` using `hconst s`. Rewrite `h` using `[Complex.exp_neg]`. Clear denominators, using `at h` for the nonvanishing conditions.

Conclude with `h`. Rewrite using `[hg]`. Conclude with `Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)`.
-/
theorem contDiff_real_char (g : ℝ → ℂ) (hc : Continuous g) (hm : ∀ s t, g (s + t) = g s * g t) (h0 : g 0 = 1) :
    ContDiff ℝ ∞ g := by
  set c := deriv g 0
  have hd : ∀ s, HasDerivAt g (c * g s) s := GlobalTheory.hasDerivAt_of_continuous_additive_to_mul g hc hm h0
  have he : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(c * (s : ℂ)))) (Complex.exp (-(c * (s : ℂ))) * -c) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-(c * ((1 : ℝ) : ℂ))) s :=
      (((hasDerivAt_id s).ofReal_comp).const_mul c).neg
    replace h1 : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-c) s := h1.congr_deriv (by simp)
    exact h1.cexp
  have hk : ∀ s, HasDerivAt (fun s : ℝ => g s * Complex.exp (-(c * (s : ℂ)))) 0 s := by
    intro s
    have := (hd s).mul (he s)
    exact this.congr_deriv (by ring)
  have hconst : ∀ s, g s * Complex.exp (-(c * (s : ℂ))) = 1 := by
    intro s
    have := is_const_of_deriv_eq_zero (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) s 0
    simpa [h0] using this
  have hg : g = fun s : ℝ => Complex.exp (c * (s : ℂ)) := by
    funext s
    have h := hconst s
    rw [Complex.exp_neg] at h
    field_simp at h
    exact h
  rw [hg]
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

/- English proof (translation)
Establish `hsum : ∀ (s : Finset (Fin k)) (x : Fin k → Fin k → ℝ), χ (∑ i ∈ s, x i) = ∏ i ∈ s, χ (x i)`. Introduce `s x`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `[h0]`. Introduce `a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, hm, ih]`. Establish `hsplit : χ = fun t => ∏ i, χ (Pi.single i (t i))`. Use function extensionality and compare the values at `t`. Use `conv_lhs => rw [← Finset.univ_sum_single t]`. Conclude with `hsum _ _`.

Rewrite using `[hsplit]`. Use `contDiff_prod fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `have hsc : Continuous fun s : ℝ => (Pi.single i s : Fin k → ℝ) := by first | fun_prop | exact continuous_single i | exact (LinearMap.single ℝ (fun _ : Fin k => ℝ) i).continuous_of_finiteDimensional`. Establish `hi : ContDiff ℝ ∞ fun s : ℝ => χ (Pi.single i s)` using `contDiff_real_char _ (hc.comp hsc) (fun s t => by rw [Pi.single_add, hm]) (by rw [Pi.single_zero, h0])`. Conclude with `hi.comp (contDiff_apply ℝ ℝ i)`.
-/
theorem contDiff_char {k : ℕ} (χ : (Fin k → ℝ) → ℂ) (hc : Continuous χ) (hm : ∀ s t, χ (s + t) = χ s * χ t)
    (h0 : χ 0 = 1) : ContDiff ℝ ∞ χ := by
  have hsum : ∀ (s : Finset (Fin k)) (x : Fin k → Fin k → ℝ), χ (∑ i ∈ s, x i) = ∏ i ∈ s, χ (x i) := by
    intro s x
    refine Finset.induction_on s ?_ ?_
    · simp [h0]
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.prod_insert ha, hm, ih]
  have hsplit : χ = fun t => ∏ i, χ (Pi.single i (t i)) := by
    funext t
    conv_lhs => rw [← Finset.univ_sum_single t]
    exact hsum _ _
  rw [hsplit]
  refine contDiff_prod fun i _ => ?_
  have hsc : Continuous fun s : ℝ => (Pi.single i s : Fin k → ℝ) := by
    first | fun_prop | exact continuous_single i | exact (LinearMap.single ℝ (fun _ : Fin k => ℝ) i).continuous_of_finiteDimensional
  have hi : ContDiff ℝ ∞ fun s : ℝ => χ (Pi.single i s) :=
    contDiff_real_char _ (hc.comp hsc) (fun s t => by rw [Pi.single_add, hm])
      (by rw [Pi.single_zero, h0])
  exact hi.comp (contDiff_apply ℝ ℝ i)

/- English proof (translation)
Establish `hcont : Continuous fun a : Af F => ψ (pairA F 0 a)` using `hc.comp (continuous_const.prodMk continuous_id)`. Establish `hV : (fun a : Af F => ψ (pairA F 0 a)) ⁻¹' {z : ℂ | ‖z - 1‖ < 1 / 2} ∈ 𝓝 (0 : Af F)`. Use `((isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).preimage hcont).mem_nhds ?_` and prove the remaining obligations. Use `show ‖ψ (pairA F 0 0) - 1‖ < 1 / 2`. Rewrite using `[show pairA F 0 (0 : Af F) = 0 from rfl, ψ.map_zero_eq_one]`.

Evaluate the numerical expressions. Take `⟨N, hN, hNV⟩` from `GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV`. Use `Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Use `GroundTheory.Global.eq_one_of_sq_mem (s := {z | ∃ b : Af F, (∀ v, b v ∈ v.adicCompletionIntegers F) ∧ z = ψ (pairA F 0 (N • b))}) ?_ ?_ ⟨a, ha, rfl⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨b, hb, rfl⟩`. Use `⟨b + b, fun v => add_mem (hb v) (hb v), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two, ← AddChar.map_add_eq_mul]`. Use `congr 1`. Conclude with `Prod.ext (add_zero 0) (smul_add N b b).symm`.

Introduce and unpack `_ ⟨b, hb, rfl⟩`. Conclude with `hNV b hb`.
-/
theorem ker_fin_mem_nhds {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ) :
    {a : Af F | ψ (pairA F 0 a) = 1} ∈ 𝓝 (0 : Af F) := by
  have hcont : Continuous fun a : Af F => ψ (pairA F 0 a) := hc.comp (continuous_const.prodMk continuous_id)
  have hV : (fun a : Af F => ψ (pairA F 0 a)) ⁻¹' {z : ℂ | ‖z - 1‖ < 1 / 2} ∈ 𝓝 (0 : Af F) := by
    refine ((isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).preimage hcont).mem_nhds ?_
    show ‖ψ (pairA F 0 0) - 1‖ < 1 / 2
    rw [show pairA F 0 (0 : Af F) = 0 from rfl, ψ.map_zero_eq_one]
    norm_num
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  refine GroundTheory.Global.eq_one_of_sq_mem
    (s := {z | ∃ b : Af F, (∀ v, b v ∈ v.adicCompletionIntegers F) ∧ z = ψ (pairA F 0 (N • b))}) ?_ ?_ ⟨a, ha, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨b + b, fun v => add_mem (hb v) (hb v), ?_⟩
    rw [pow_two, ← AddChar.map_add_eq_mul]
    congr 1
    exact Prod.ext (add_zero 0) (smul_add N b b).symm
  · rintro _ ⟨b, hb, rfl⟩
    exact hNV b hb

section Form

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance modTopAEF : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
local instance topRingAEF : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

variable (F) in

def eInfF : AF F := pairA F 1 0

/- English proof (translation)
Set `s : Ainf F ⊗[F] E →ₗ[F] AEF F E` to `TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id`. Establish `key : ∀ a : AEF F E, eInfF F • a = s (infPartF F E a)`. Introduce `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp only [smul_zero, map_zero]`.

Consider the case `add a b ha hb => rw [smul_add, ha, hb, RingHom.map_add, map_add]`. Consider the case `tmul a x`. Rewrite using `[TensorProduct.smul_tmul']`. Establish `: eInfF F • a = LinearMap.inl F (Ainf F) (Af F) (fstA F a)` using `Prod.ext (one_mul _) (zero_mul _)`. Rewrite using `[this]`.

Both sides reduce to the same expression. Rewrite using `[key, h, map_zero]`.
-/
theorem smul_eq_zero_of_infF {a : AEF F E} (h : infPartF F E a = 0) : eInfF F • a = 0 := by
  let s : Ainf F ⊗[F] E →ₗ[F] AEF F E := TensorProduct.map (LinearMap.inl F (Ainf F) (Af F)) LinearMap.id
  have key : ∀ a : AEF F E, eInfF F • a = s (infPartF F E a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add a b ha hb => rw [smul_add, ha, hb, RingHom.map_add, map_add]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      have : eInfF F • a = LinearMap.inl F (Ainf F) (Af F) (fstA F a) := Prod.ext (one_mul _) (zero_mul _)
      rw [this]
      rfl
  rw [key, h, map_zero]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp only [smul_zero, map_zero]`. Consider the case `add a b ha hb => rw [smul_add, RingHom.map_add, RingHom.map_add, ha, hb, smul_add]`. Consider the case `tmul a x => rfl`.
-/
theorem cAF_smul (σ : E →ₐ[F] E) (c : AF F) (a : AEF F E) : cAF σ (c • a) = c • cAF σ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add a b ha hb => rw [smul_add, RingHom.map_add, RingHom.map_add, ha, hb, smul_add]
  | tmul a x => rfl

/- English proof (translation)
Set `l : AEF F E →ₗ[AF F] AEF F E` to `{ toFun := cAF σ, map_add' := map_add _, map_smul' := cAF_smul σ }`. Conclude with `IsModuleTopology.continuous_of_linearMap l`.
-/
theorem continuous_cAF (σ : E →ₐ[F] E) : Continuous (cAF σ : AEF F E → AEF F E) := by
  let l : AEF F E →ₗ[AF F] AEF F E := { toFun := cAF σ, map_add' := map_add _, map_smul' := cAF_smul σ }
  exact IsModuleTopology.continuous_of_linearMap l

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E)

/- English proof (translation)
Unfold `symplOHF symplOF hOF`. Simplify using `only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]`.
-/
theorem symplOHF_add_left (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (x + x') y = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Unfold `symplOHF symplOF hOF`. Simplify using `only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]`.
-/
theorem symplOHF_add_right (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (y + y') = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Establish `h : hOF σ JS JT (c • x) y = c • hOF σ JS JT x y`. Unfold `hOF`. Simplify using `only [Matrix.smul_apply, Finset.smul_sum, mul_smul_comm]`. Unfold `symplOHF symplOF`. Rewrite using `[h, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm]`.
-/
theorem symplOHF_smul_left (c : AF F) (x y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (c • x) y = c * symplOHF σ JS JT xi0 x y := by
  have h : hOF σ JS JT (c • x) y = c • hOF σ JS JT x y := by
    unfold hOF
    simp only [Matrix.smul_apply, Finset.smul_sum, mul_smul_comm]
  unfold symplOHF symplOF
  rw [h, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm]

/- English proof (translation)
Establish `h : hOF σ JS JT x (c • y) = c • hOF σ JS JT x y`. Unfold `hOF`. Simplify using `only [Matrix.smul_apply, Finset.smul_sum, cAF_smul, mul_smul_comm, smul_mul_assoc]`. Unfold `symplOHF symplOF`. Rewrite using `[h, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm]`.
-/
theorem symplOHF_smul_right (c : AF F) (x y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (c • y) = c * symplOHF σ JS JT xi0 x y := by
  have h : hOF σ JS JT x (c • y) = c • hOF σ JS JT x y := by
    unfold hOF
    simp only [Matrix.smul_apply, Finset.smul_sum, cAF_smul, mul_smul_comm, smul_mul_assoc]
  unfold symplOHF symplOF
  rw [h, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm]

/- English proof (translation)
Use `symplOHF_smul_left σ JS JT xi0 0 0 y` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_mul]`. Then use the resulting hypothesis.
-/
theorem symplOHF_zero_left (y : WOF F E nS nT) : symplOHF σ JS JT xi0 0 y = 0 := by
  have := symplOHF_smul_left σ JS JT xi0 0 0 y
  rwa [zero_smul, zero_mul] at this

/- English proof (translation)
Use `symplOHF_smul_right σ JS JT xi0 0 y 0` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_mul]`. Then use the resulting hypothesis.
-/
theorem symplOHF_zero_right (y : WOF F E nS nT) : symplOHF σ JS JT xi0 y 0 = 0 := by
  have := symplOHF_smul_right σ JS JT xi0 0 y 0
  rwa [zero_smul, zero_mul] at this

/- English proof (translation)
Establish `ht : Continuous (Algebra.trace (AF F) (AEF F E))` using `IsModuleTopology.continuous_of_linearMap _`. Unfold `symplOHF symplOF hOF`. Use `continuous_const.mul (ht.comp (continuous_const.mul ?_))` and prove the remaining obligations. Use `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => continuous_const.mul ?_` and prove the remaining obligations. Conclude with `(continuous_apply a).comp (continuous_apply d)`.
-/
theorem continuous_symplOHF_left (u : WOF F E nS nT) : Continuous fun w : WOF F E nS nT => symplOHF σ JS JT xi0 w u := by
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  unfold symplOHF symplOF hOF
  refine continuous_const.mul (ht.comp (continuous_const.mul ?_))
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
    continuous_finset_sum _ fun d _ => continuous_const.mul ?_
  exact (continuous_apply a).comp (continuous_apply d)

/- English proof (translation)
Establish `ht : Continuous (Algebra.trace (AF F) (AEF F E))` using `IsModuleTopology.continuous_of_linearMap _`. Unfold `symplOHF symplOF hOF`. Use `continuous_const.mul (ht.comp (continuous_const.mul ?_))` and prove the remaining obligations. Use `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ((continuous_const.mul ?_).mul continuous_const).mul continuous_const` and prove the remaining obligations. Conclude with `(continuous_cAF σ).comp ((continuous_apply b).comp (continuous_apply c))`.
-/
theorem continuous_symplOHF_right (u : WOF F E nS nT) : Continuous fun w : WOF F E nS nT => symplOHF σ JS JT xi0 u w := by
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  unfold symplOHF symplOF hOF
  refine continuous_const.mul (ht.comp (continuous_const.mul ?_))
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
    continuous_finset_sum _ fun d _ => ((continuous_const.mul ?_).mul continuous_const).mul continuous_const
  exact (continuous_cAF σ).comp ((continuous_apply b).comp (continuous_apply c))

variable {σ JS JT xi0}

/- English proof (translation)
Use extensionality with `i j`. Conclude with `smul_eq_zero_of_infF (congrFun (congrFun hu i) j)`.
-/
theorem smul_finF {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : eInfF F • u = 0 := by
  ext i j; exact smul_eq_zero_of_infF (congrFun (congrFun hu i) j)

end Form

section Main

local instance modTopAEF' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

local instance topRingAEF' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hc w₀ f hf`. Use `⟨fun γ w => ?_, ?_, ?_, fun k L hL hLf w => ?_⟩` and prove the remaining obligations. Simplify using `only [heisOF]`. Rewrite using `[add_assoc, hf.quasi, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨U, hU, hUf⟩` from `hf.level`. Set `c : WOF F E nS nT →+ AF F` to `AddMonoidHom.mk' (fun u => symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) (fun a b => by simp only [symplOHF_add_left, symplOHF_add_right]; ring)`. Set `g : WOF F E nS nT →+ AF F` to `AddMonoidHom.mk' (fun u => pairA F 0 (c u).2) (fun a b => by rw [map_add]; exact Prod.ext (add_zero 0).symm rfl)`. Set `Kψ : AddSubgroup (AF F)` to `{ carrier := {x | ψ x = 1} zero_mem' := ψ.map_zero_eq_one add_mem' := fun {a b} ha hb => by`.

Establish `ha' : ψ a = 1` using `ha`. Establish `hb' : ψ b = 1` using `hb`. Use `show ψ (a + b) = 1`. Rewrite using `[AddChar.map_add_eq_mul, ha', hb', one_mul]`. Use the proof step `neg_mem' := fun {a} ha => by`.

Establish `ha' : ψ a = 1` using `ha`. Use `show ψ (-a) = 1`. Use `AddChar.map_add_eq_mul ψ (-a) a` as an intermediate fact. Rewrite `this` using `[neg_add_cancel, ψ.map_zero_eq_one, ha', mul_one]`. Conclude with `this.symm }`.

Set `K : AddSubgroup (WOF F E nS nT)` to `Kψ.comap g`. Establish `hK : IsOpen (K : Set (WOF F E nS nT))`. Use `K.isOpen_of_mem_nhds (g := 0) ?_` and prove the remaining obligations. Establish `h1 : Continuous fun u : WOF F E nS nT => (c u).2` using `continuous_snd.comp ((continuous_symplOHF_left σ JS JT ξ₀ w₀).sub (continuous_symplOHF_right σ JS JT ξ₀ w₀))`. Establish `h2 : (fun u : WOF F E nS nT => (c u).2) ⁻¹' {a | ψ (pairA F 0 a) = 1} ∈ 𝓝 (0 : WOF F E nS nT)`.

Use `h1.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `ker_fin_mem_nhds hc`. Conclude with `Filter.mem_of_superset h2 fun u hu => hu`. Use `⟨U ⊓ K, hU.inter hK, fun u hu hu0 => ?_⟩` and prove the remaining obligations.

Establish `hfin : c u = pairA F 0 (c u).2`. Establish `h3 : eInfF F * c u = 0` using `by show eInfF F * (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) = 0`. Rewrite using `[mul_sub, ← symplOHF_smul_left, ← symplOHF_smul_right, smul_finF hu0, symplOHF_zero_left, symplOHF_zero_right, sub_self]`. Conclude with `Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl`. Establish `hψc : ψ (c u) = 1`.

Rewrite using `[hfin]`. Conclude with `hu.2`. Use function extensionality and compare the values at `w`. Establish `h` using `congrFun (hUf u hu.1 hu0) (w + w₀)`. Simplify using `only [heisOF] at h ⊢`.

Rewrite using `[← h, add_right_comm w u w₀]`. Establish `key : symplOHF σ JS JT ξ₀ w u + symplOHF σ JS JT ξ₀ (w + u) w₀ = (symplOHF σ JS JT ξ₀ w w₀ + symplOHF σ JS JT ξ₀ (w + w₀) u) + c u` using `by show _ = _ + (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)`. Rewrite using `[symplOHF_add_left, symplOHF_add_left]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, AddChar.map_add_eq_mul ψ _ (c u), hψc, mul_one]`.

Conclude with `(hc.comp (continuous_symplOHF_left σ JS JT ξ₀ w₀)).mul (hf.cont.comp (continuous_id.add continuous_const))`. Establish `hχ : ContDiff ℝ ∞ fun t => ψ (symplOHF σ JS JT ξ₀ (L t) w₀)`. Use `contDiff_char _ (hc.comp ((continuous_symplOHF_left σ JS JT ξ₀ w₀).comp hL)) (fun s t => ?_) ?_` and prove the remaining obligations. Rewrite using `[map_add, symplOHF_add_left, AddChar.map_add_eq_mul]`. Rewrite using `[map_zero, symplOHF_zero_left, ψ.map_zero_eq_one]`.

Establish `: (fun t => heisOF σ JS JT ξ₀ ψ w₀ f (w + L t)) = fun t => ψ (symplOHF σ JS JT ξ₀ w w₀) * (ψ (symplOHF σ JS JT ξ₀ (L t) w₀) * f (w + w₀ + L t))`. Use function extensionality and compare the values at `t`. Simplify using `only [heisOF]`. Rewrite using `[symplOHF_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]`. Rewrite using `[this]`.

Conclude with `contDiff_const.mul (hχ.mul (hf.smooth k L hL hLf (w + w₀)))`.
-/
theorem isThetaFunOF_heisOF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ),
    Continuous ψ → ∀ (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ ψ f →
      IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w₀ f) := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hc w₀ f hf
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL hLf w => ?_⟩
  · simp only [heisOF]
    rw [add_assoc, hf.quasi, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul]
    congr 2
    ring
  · obtain ⟨U, hU, hUf⟩ := hf.level
    let c : WOF F E nS nT →+ AF F :=
      AddMonoidHom.mk' (fun u => symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)
        (fun a b => by simp only [symplOHF_add_left, symplOHF_add_right]; ring)
    let g : WOF F E nS nT →+ AF F :=
      AddMonoidHom.mk' (fun u => pairA F 0 (c u).2) (fun a b => by rw [map_add]; exact Prod.ext (add_zero 0).symm rfl)
    let Kψ : AddSubgroup (AF F) :=
      { carrier := {x | ψ x = 1}
        zero_mem' := ψ.map_zero_eq_one
        add_mem' := fun {a b} ha hb => by
          have ha' : ψ a = 1 := ha
          have hb' : ψ b = 1 := hb
          show ψ (a + b) = 1
          rw [AddChar.map_add_eq_mul, ha', hb', one_mul]
        neg_mem' := fun {a} ha => by
          have ha' : ψ a = 1 := ha
          show ψ (-a) = 1
          have := AddChar.map_add_eq_mul ψ (-a) a
          rw [neg_add_cancel, ψ.map_zero_eq_one, ha', mul_one] at this
          exact this.symm }
    let K : AddSubgroup (WOF F E nS nT) := Kψ.comap g
    have hK : IsOpen (K : Set (WOF F E nS nT)) := by
      refine K.isOpen_of_mem_nhds (g := 0) ?_
      have h1 : Continuous fun u : WOF F E nS nT => (c u).2 :=
        continuous_snd.comp ((continuous_symplOHF_left σ JS JT ξ₀ w₀).sub (continuous_symplOHF_right σ JS JT ξ₀ w₀))
      have h2 : (fun u : WOF F E nS nT => (c u).2) ⁻¹' {a | ψ (pairA F 0 a) = 1} ∈ 𝓝 (0 : WOF F E nS nT) := by
        refine h1.continuousAt.preimage_mem_nhds ?_
        rw [map_zero]
        exact ker_fin_mem_nhds hc
      exact Filter.mem_of_superset h2 fun u hu => hu
    refine ⟨U ⊓ K, hU.inter hK, fun u hu hu0 => ?_⟩
    have hfin : c u = pairA F 0 (c u).2 := by
      have h3 : eInfF F * c u = 0 := by
        show eInfF F * (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) = 0
        rw [mul_sub, ← symplOHF_smul_left, ← symplOHF_smul_right, smul_finF hu0, symplOHF_zero_left,
          symplOHF_zero_right, sub_self]
      exact Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl
    have hψc : ψ (c u) = 1 := by
      rw [hfin]
      exact hu.2
    funext w
    have h := congrFun (hUf u hu.1 hu0) (w + w₀)
    simp only [heisOF] at h ⊢
    rw [← h, add_right_comm w u w₀]
    have key : symplOHF σ JS JT ξ₀ w u + symplOHF σ JS JT ξ₀ (w + u) w₀ =
        (symplOHF σ JS JT ξ₀ w w₀ + symplOHF σ JS JT ξ₀ (w + w₀) u) + c u := by
      show _ = _ + (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)
      rw [symplOHF_add_left, symplOHF_add_left]
      ring
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, AddChar.map_add_eq_mul ψ _ (c u),
      hψc, mul_one]
  · exact (hc.comp (continuous_symplOHF_left σ JS JT ξ₀ w₀)).mul (hf.cont.comp (continuous_id.add continuous_const))
  · have hχ : ContDiff ℝ ∞ fun t => ψ (symplOHF σ JS JT ξ₀ (L t) w₀) := by
      refine contDiff_char _ (hc.comp ((continuous_symplOHF_left σ JS JT ξ₀ w₀).comp hL)) (fun s t => ?_) ?_
      · rw [map_add, symplOHF_add_left, AddChar.map_add_eq_mul]
      · rw [map_zero, symplOHF_zero_left, ψ.map_zero_eq_one]
    have : (fun t => heisOF σ JS JT ξ₀ ψ w₀ f (w + L t)) =
        fun t => ψ (symplOHF σ JS JT ξ₀ w w₀) * (ψ (symplOHF σ JS JT ξ₀ (L t) w₀) * f (w + w₀ + L t)) := by
      funext t
      simp only [heisOF]
      rw [symplOHF_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]
    rw [this]
    exact contDiff_const.mul (hχ.mul (hf.smooth k L hL hLf (w + w₀)))

end Main

end GlobalTheory.HeisKeepF

end
