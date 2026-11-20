import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFn
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.SiegelOp

variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

def cons0 (x : Matrix (Fin n) (Fin N) E) : Matrix (Fin n) (Fin (N + 1)) E :=
  Matrix.of fun k => Fin.cons 0 (x k)

omit [NumberField E] in
/- English proof (translation)
Introduce `τ`. Establish `e : imH (pushZ Ψ Z v t τ) = imH (Z τ) + (t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a))`. Use extensionality with `a b`. Simplify using `only [imH, pushZ, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, conjTranspose_apply, vecMulVec_apply, smul_eq_mul, star_add, star_mul', Pi.star_apply, RCLike.star_def, conj_I, conj_ofReal, conj_conj]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(h τ).add_posSemidef ((posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.2 ht))`.
-/
theorem pushZ_mem {Z : CM Ψ N N} (h : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ} (ht : 0 ≤ t) :
    pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have e : imH (pushZ Ψ Z v t τ) = imH (Z τ) +
      (t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) := by
    ext a b
    simp only [imH, pushZ, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
      conjTranspose_apply, vecMulVec_apply, smul_eq_mul, star_add, star_mul', Pi.star_apply,
      RCLike.star_def, conj_I, conj_ofReal, conj_conj]
    field_simp
    ring
  rw [e]
  exact (h τ).add_posSemidef
    ((posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.2 ht))

noncomputable def col (x : Matrix (Fin n) (Fin (N + 1)) E) : ℝ :=
  ∑ τ : Ψ, ∑ k, normSq (τ.1 (x k 0))

end GlobalTheory.SW.SiegelOp

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
Set `e : Matrix (Fin n) (Fin N) E →+ Matrix (Fin n) (Fin (N + 1)) E` to `{ toFun := _root_.GlobalTheory.SW.SiegelOp.cons0 map_zero' := by`. Use extensionality with `k a`. Apply the tactic sequence `refine Fin.cases ?_ (fun b => ?_) a <;> simp [_root_.GlobalTheory.SW.SiegelOp.cons0]`. Use the proof step `map_add' := fun x y => by`. Use extensionality with `k a`.

Apply the tactic sequence `refine Fin.cases ?_ (fun b => ?_) a <;> simp [_root_.GlobalTheory.SW.SiegelOp.cons0] }`. Establish `h` using `_root_.GlobalTheory.SW.Dict.isSB_comp e 1 1 one_pos one_pos ?_ ?_ hφ`. Conclude with `h`. Introduce `x hx k a`. Use `Fin.cases ?_ (fun b => ?_) a` and prove the remaining obligations.

Simplify using `[e, _root_.GlobalTheory.SW.SiegelOp.cons0, isIntegral_zero]`. Simplify `hx k b` using `[e, _root_.GlobalTheory.SW.SiegelOp.cons0]`. Introduce `x hx k a`. Simplify `hx k a.succ` using `[e, _root_.GlobalTheory.SW.SiegelOp.cons0]`.
-/
private lemma isSB_dropF'
    (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ) (hφ : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB (_root_.GlobalTheory.SW.dropF φ) := by
  let e : Matrix (Fin n) (Fin N) E →+ Matrix (Fin n) (Fin (N + 1)) E :=
    { toFun := _root_.GlobalTheory.SW.SiegelOp.cons0
      map_zero' := by
        ext k a
        refine Fin.cases ?_ (fun b => ?_) a <;> simp [_root_.GlobalTheory.SW.SiegelOp.cons0]
      map_add' := fun x y => by
        ext k a
        refine Fin.cases ?_ (fun b => ?_) a <;> simp [_root_.GlobalTheory.SW.SiegelOp.cons0] }
  have h := _root_.GlobalTheory.SW.Dict.isSB_comp e 1 1 one_pos one_pos ?_ ?_ hφ
  · exact h
  · intro x hx k a
    refine Fin.cases ?_ (fun b => ?_) a
    · simp [e, _root_.GlobalTheory.SW.SiegelOp.cons0, isIntegral_zero]
    · simpa [e, _root_.GlobalTheory.SW.SiegelOp.cons0] using hx k b
  · intro x hx k a
    simpa [e, _root_.GlobalTheory.SW.SiegelOp.cons0] using hx k a.succ

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
Introduce `τ`. Establish `h` using `(hZ τ).submatrix (Fin.succ_injective N)`. Unfold `_root_.GlobalTheory.SW.imH at h ⊢`. Unfold `_root_.GlobalTheory.SW.dropZ`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `a b`. Simplify using `[conjTranspose_apply]`.
-/
private lemma dropZ_mem_Hn (Z : _root_.GlobalTheory.SW.CM Ψ (N + 1) (N + 1))
    (hZ : Z ∈ _root_.GlobalTheory.SW.Hn Ψ (N + 1)) :
    _root_.GlobalTheory.SW.dropZ Ψ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N := by
  intro τ
  have h := (hZ τ).submatrix (Fin.succ_injective N)
  unfold _root_.GlobalTheory.SW.imH at h ⊢
  unfold _root_.GlobalTheory.SW.dropZ
  convert h using 1
  ext a b
  simp [conjTranspose_apply]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
Introduce `τ`. Establish `hP` using `(posSemidef_vecMulVec_self_star (fun a ↦ (τ : E →+* ℂ) ((Pi.single 0 1 : Fin (N + 1) → E) a))).smul (a := t) ht`. Establish `h` using `(hZ τ).add_posSemidef hP`. Unfold `_root_.GlobalTheory.SW.imH at h ⊢`. Unfold `_root_.GlobalTheory.SW.pushZ`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, conjTranspose_apply, vecMulVec_apply, smul_eq_mul, star_add, star_smul, Pi.star_apply]`. Simplify using `only [star_mul', Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj, Complex.real_smul]`. Establish `hI : (2 * I) ≠ 0` using `mul_ne_zero two_ne_zero I_ne_zero`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma pushZ_single_zero_mem_Hn_of_nonneg (Z : _root_.GlobalTheory.SW.CM Ψ (N + 1) (N + 1))
    (hZ : Z ∈ _root_.GlobalTheory.SW.Hn Ψ (N + 1)) (t : ℝ) (ht : 0 ≤ t) :
    _root_.GlobalTheory.SW.pushZ Ψ Z (Pi.single 0 1) t ∈ _root_.GlobalTheory.SW.Hn Ψ (N + 1) := by
  intro τ
  have hP := (posSemidef_vecMulVec_self_star
    (fun a ↦ (τ : E →+* ℂ) ((Pi.single 0 1 : Fin (N + 1) → E) a))).smul (a := t) ht
  have h := (hZ τ).add_posSemidef hP
  unfold _root_.GlobalTheory.SW.imH at h ⊢
  unfold _root_.GlobalTheory.SW.pushZ
  convert h using 1
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, conjTranspose_apply,
    vecMulVec_apply, smul_eq_mul, star_add, star_smul, Pi.star_apply]
  simp only [star_mul', Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_conj, Complex.real_smul]
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  field_simp
  ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
Establish `hs : (fun a ↦ σ ((Pi.single 0 1 : Fin (N + 1) → E) a)) = Pi.single 0 1`. Use function extensionality and compare the values at `a`. Distinguish the cases in `h : a = 0`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, h]`. Rewrite using `[hs, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul]`. Use `congr 1`. Simplify using `[vecMulVec, mulVec, dotProduct, Pi.single_apply, Complex.mul_conj]`.
-/
private lemma dotProduct_add_smul_vecMulVec_single_zero_mulVec (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ : E →+* ℂ) (u : Fin (N + 1) → ℂ) (c : ℂ) :
    u ⬝ᵥ (M + c • vecMulVec (fun a ↦ σ ((Pi.single 0 1 : Fin (N + 1) → E) a))
      (fun a ↦ starRingEnd ℂ (σ ((Pi.single 0 1 : Fin (N + 1) → E) a)))) *ᵥ
        (fun a ↦ starRingEnd ℂ (u a)) =
      u ⬝ᵥ M *ᵥ (fun a ↦ starRingEnd ℂ (u a)) + c * (normSq (u 0) : ℂ) := by
  have hs : (fun a ↦ σ ((Pi.single 0 1 : Fin (N + 1) → E) a)) = Pi.single 0 1 := by
    funext a
    by_cases h : a = 0
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [hs, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul]
  congr 1
  simp [vecMulVec, mulVec, dotProduct, Pi.single_apply, Complex.mul_conj]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.SW.expo _root_.GlobalTheory.SW.pushZ _root_.GlobalTheory.SW.SiegelOp.col`. Repeatedly rewrite using `[dotProduct_add_smul_vecMulVec_single_zero_mulVec]`. Use `push_cast`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma expo_pushZ_single_zero (x : Matrix (Fin n) (Fin (N + 1)) E)
    (Z : _root_.GlobalTheory.SW.CM Ψ (N + 1) (N + 1)) (z z' : _root_.GlobalTheory.SW.CM Ψ n (N + 1))
    (t : ℝ) :
    _root_.GlobalTheory.SW.expo Ψ x (_root_.GlobalTheory.SW.pushZ Ψ Z (Pi.single 0 1) t) z z' =
      _root_.GlobalTheory.SW.expo Ψ x Z z z' + I * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x := by
  unfold _root_.GlobalTheory.SW.expo _root_.GlobalTheory.SW.pushZ _root_.GlobalTheory.SW.SiegelOp.col
  simp_rw [dotProduct_add_smul_vecMulVec_single_zero_mulVec]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
Establish `h : 2 * ↑Real.pi * I * (_root_.GlobalTheory.SW.expo Ψ x Z z z' + I * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x) = 2 * ↑Real.pi * I * _root_.GlobalTheory.SW.expo Ψ x Z z z' + ((-(2 * Real.pi * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x) : ℝ) : ℂ)`. Use `push_cast`. Take the linear combination `(2 * (Real.pi : ℂ) * t * (_root_.GlobalTheory.SW.SiegelOp.col Ψ x : ℂ)) * I_sq`. Rewrite using `[expo_pushZ_single_zero, h, Complex.exp_add, Complex.ofReal_exp]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma mul_cexp_expo_pushZ_single_zero (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ)
    (x : Matrix (Fin n) (Fin (N + 1)) E) (Z : _root_.GlobalTheory.SW.CM Ψ (N + 1) (N + 1))
    (z z' : _root_.GlobalTheory.SW.CM Ψ n (N + 1)) (t : ℝ) :
    φ x * cexp (2 * ↑Real.pi * I *
        _root_.GlobalTheory.SW.expo Ψ x (_root_.GlobalTheory.SW.pushZ Ψ Z (Pi.single 0 1) t) z z') =
      φ x * cexp (2 * ↑Real.pi * I * _root_.GlobalTheory.SW.expo Ψ x Z z z') *
        ((Real.exp (-(2 * Real.pi * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x)) : ℝ) : ℂ) := by
  have h : 2 * ↑Real.pi * I *
      (_root_.GlobalTheory.SW.expo Ψ x Z z z' + I * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x) =
      2 * ↑Real.pi * I * _root_.GlobalTheory.SW.expo Ψ x Z z z' +
        ((-(2 * Real.pi * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x) : ℝ) : ℂ) := by
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * t * (_root_.GlobalTheory.SW.SiegelOp.col Ψ x : ℂ)) * I_sq
  rw [expo_pushZ_single_zero, h, Complex.exp_add, Complex.ofReal_exp]
  ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _`.
-/
private lemma col_nonneg' (x : Matrix (Fin n) (Fin (N + 1)) E) :
    0 ≤ _root_.GlobalTheory.SW.SiegelOp.col Ψ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨σ, hσ⟩` from `hΨ`. Use `⟨fun k a => x k a.succ, ?_⟩` and prove the remaining obligations. Use extensionality with `k a`.

Use `Fin.cases ?_ (fun b => ?_) a` and prove the remaining obligations. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => Finset.sum_nonneg fun k _ => normSq_nonneg _)).mp h ⟨σ, hσ⟩ (Finset.mem_univ _)`. Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonneg (fun k _ => normSq_nonneg _)).mp h1 k (Finset.mem_univ _)`. Simplify `h2` using `[_root_.GlobalTheory.SW.SiegelOp.cons0]`. Simplify using `[_root_.GlobalTheory.SW.SiegelOp.cons0]`.

Introduce and unpack `⟨y, rfl⟩`. Simplify using `[_root_.GlobalTheory.SW.SiegelOp.col, _root_.GlobalTheory.SW.SiegelOp.cons0]`.
-/
private lemma col_eq_zero_iff_exists_eq_cons0 (hΨ : Ψ.Nonempty)
    (x : Matrix (Fin n) (Fin (N + 1)) E) :
    _root_.GlobalTheory.SW.SiegelOp.col Ψ x = 0 ↔ ∃ y, x = _root_.GlobalTheory.SW.SiegelOp.cons0 y := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := hΨ
    refine ⟨fun k a => x k a.succ, ?_⟩
    ext k a
    refine Fin.cases ?_ (fun b => ?_) a
    · have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => Finset.sum_nonneg fun k _ =>
        normSq_nonneg _)).mp h ⟨σ, hσ⟩ (Finset.mem_univ _)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => normSq_nonneg _)).mp h1 k
        (Finset.mem_univ _)
      simpa [_root_.GlobalTheory.SW.SiegelOp.cons0] using h2
    · simp [_root_.GlobalTheory.SW.SiegelOp.cons0]
  · rintro ⟨y, rfl⟩
    simp [_root_.GlobalTheory.SW.SiegelOp.col, _root_.GlobalTheory.SW.SiegelOp.cons0]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
Introduce `y y' h`. Use extensionality with `k a`. Simplify `congrFun (congrFun h k) a.succ` using `[_root_.GlobalTheory.SW.SiegelOp.cons0]`.
-/
private lemma cons0_injective :
    Function.Injective (_root_.GlobalTheory.SW.SiegelOp.cons0 : Matrix (Fin n) (Fin N) E → _) := by
  intro y y' h
  ext k a
  simpa [_root_.GlobalTheory.SW.SiegelOp.cons0] using congrFun (congrFun h k) a.succ

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.SW.expo _root_.GlobalTheory.SW.dropZ _root_.GlobalTheory.SW.SiegelOp.cons0`. Simplify using `[dotProduct, mulVec, Fin.sum_univ_succ]`.
-/
private lemma expo_cons0' (y : Matrix (Fin n) (Fin N) E)
    (Z : _root_.GlobalTheory.SW.CM Ψ (N + 1) (N + 1)) (z z' : _root_.GlobalTheory.SW.CM Ψ n (N + 1)) :
    _root_.GlobalTheory.SW.expo Ψ (_root_.GlobalTheory.SW.SiegelOp.cons0 y) Z z z' =
      _root_.GlobalTheory.SW.expo Ψ y (_root_.GlobalTheory.SW.dropZ Ψ Z)
        (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ) := by
  unfold _root_.GlobalTheory.SW.expo _root_.GlobalTheory.SW.dropZ _root_.GlobalTheory.SW.SiegelOp.cons0
  simp [dotProduct, mulVec, Fin.sum_univ_succ]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in

/- English proof (translation)
Introduce `E _ _ _ Ψ hΨ n N φ hφ`. Use `⟨isSB_dropF' φ hφ, fun Z hZ => ⟨dropZ_mem_Hn Ψ Z hZ, fun t ht => pushZ_single_zero_mem_Hn_of_nonneg Ψ Z hZ t ht, fun z z' => ?_⟩⟩` and prove the remaining obligations. Establish `hne : Ψ.Nonempty`. Set `σ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom`. Distinguish the cases in `h : σ ∈ Ψ`.

Conclude with `⟨σ, h⟩`. Use `⟨ComplexEmbedding.conjugate σ, (hΨ _).mpr ?_⟩` and prove the remaining obligations. Simplify using `using h`. Establish `hsum` using `(_root_.GlobalTheory.SW.thH_summable_and_inj E Ψ hΨ n (N + 1) φ hφ Z hZ).1 z z'`. Set `g : Matrix (Fin n) (Fin (N + 1)) E → ℂ` to `fun x => if _root_.GlobalTheory.SW.SiegelOp.col Ψ x = 0 then φ x * cexp (2 * ↑Real.pi * I * _root_.GlobalTheory.SW.expo Ψ x Z z z') else 0`.

Establish `hlim : Tendsto (fun t : ℝ => ∑' x, φ x * cexp (2 * ↑Real.pi * I * _root_.GlobalTheory.SW.expo Ψ x (_root_.GlobalTheory.SW.pushZ Ψ Z (Pi.single 0 1) t) z z')) atTop (𝓝 (∑' x, g x))`. Use `tendsto_tsum_of_dominated_convergence hsum (fun x => ?_) ?_` and prove the remaining obligations. Repeatedly rewrite using `[mul_cexp_expo_pushZ_single_zero]`. Distinguish the cases in `hc : _root_.GlobalTheory.SW.SiegelOp.col Ψ x = 0`. Simplify using `[g, hc]`.

Establish `hpos : 0 < _root_.GlobalTheory.SW.SiegelOp.col Ψ x` using `lt_of_le_of_ne (col_nonneg' Ψ x) (Ne.symm hc)`. Establish `h1 : Tendsto (fun t : ℝ => 2 * Real.pi * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x) atTop atTop` using `(tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)).atTop_mul_const hpos`. Establish `h2 : Tendsto (fun t : ℝ => Real.exp (-(2 * Real.pi * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x))) atTop (𝓝 0)` using `Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)`. Establish `h3` using `(Complex.continuous_ofReal.tendsto 0).comp h2`. Establish `h4` using `(tendsto_const_nhds (x := φ x * cexp (2 * ↑Real.pi * I * _root_.GlobalTheory.SW.expo Ψ x Z z z'))).mul h3`.

Simplify `h4` using `[g, hc]`. Use `filter_upwards [eventually_ge_atTop 0] with t ht x`. Rewrite using `[mul_cexp_expo_pushZ_single_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Use `mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_))` and prove the remaining obligations. Conclude with `mul_nonneg (mul_nonneg (by positivity) ht) (col_nonneg' Ψ x)`.

Establish `hsupp : Function.support g ⊆ Set.range _root_.GlobalTheory.SW.SiegelOp.cons0`. Introduce `x hx`. Assume the negation of the conclusion as `hr`. Apply `hx` to reduce the goal to its premises. Establish `hc : _root_.GlobalTheory.SW.SiegelOp.col Ψ x ≠ 0` using `fun h => hr ((col_eq_zero_iff_exists_eq_cons0 Ψ hne x).mp h |>.elim fun y hy => ⟨y, hy.symm⟩)`.

Simplify using `[g, hc]`. Establish `key : ∑' x, g x = ∑' y, _root_.GlobalTheory.SW.dropF φ y * cexp (2 * ↑Real.pi * I * _root_.GlobalTheory.SW.expo Ψ y (_root_.GlobalTheory.SW.dropZ Ψ Z) (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ))`. Rewrite using `[← cons0_injective.tsum_eq hsupp]`. Use `tsum_congr fun y => ?_` and prove the remaining obligations. Establish `hc : _root_.GlobalTheory.SW.SiegelOp.col Ψ (_root_.GlobalTheory.SW.SiegelOp.cons0 y) = 0` using `(col_eq_zero_iff_exists_eq_cons0 Ψ hne _).mpr ⟨y, rfl⟩`.

Simplify using `only [g, hc, if_true, expo_cons0']`. Both sides reduce to the same expression. Unfold `_root_.GlobalTheory.SW.thH`. Rewrite using `[← key]`. Conclude with `hlim`.
-/
theorem _root_.GlobalTheory.SW.thH_siegel_operator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ)
    (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ), _root_.GlobalTheory.SW.IsSB φ →
    _root_.GlobalTheory.SW.IsSB (_root_.GlobalTheory.SW.dropF φ) ∧
    ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ (N + 1),
    _root_.GlobalTheory.SW.dropZ Ψ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N ∧
    (∀ t : ℝ, 0 ≤ t → _root_.GlobalTheory.SW.pushZ Ψ Z (Pi.single 0 1) t ∈
      _root_.GlobalTheory.SW.Hn Ψ (N + 1)) ∧
    ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n (N + 1),
    Tendsto (fun t : ℝ => _root_.GlobalTheory.SW.thH Ψ φ (_root_.GlobalTheory.SW.pushZ Ψ Z (Pi.single 0 1) t)
      z z') atTop
      (𝓝 (_root_.GlobalTheory.SW.thH Ψ (_root_.GlobalTheory.SW.dropF φ) (_root_.GlobalTheory.SW.dropZ Ψ Z)
        (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ))) := by
  intro E _ _ _ Ψ hΨ n N φ hφ
  refine ⟨isSB_dropF' φ hφ, fun Z hZ =>
    ⟨dropZ_mem_Hn Ψ Z hZ, fun t ht => pushZ_single_zero_mem_Hn_of_nonneg Ψ Z hZ t ht, fun z z' => ?_⟩⟩
  have hne : Ψ.Nonempty := by
    let σ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    by_cases h : σ ∈ Ψ
    · exact ⟨σ, h⟩
    · refine ⟨ComplexEmbedding.conjugate σ, (hΨ _).mpr ?_⟩
      simpa using h
  have hsum := (_root_.GlobalTheory.SW.thH_summable_and_inj E Ψ hΨ n (N + 1) φ hφ Z hZ).1 z z'
  let g : Matrix (Fin n) (Fin (N + 1)) E → ℂ := fun x =>
    if _root_.GlobalTheory.SW.SiegelOp.col Ψ x = 0 then
      φ x * cexp (2 * ↑Real.pi * I * _root_.GlobalTheory.SW.expo Ψ x Z z z') else 0
  have hlim : Tendsto (fun t : ℝ => ∑' x, φ x * cexp (2 * ↑Real.pi * I *
      _root_.GlobalTheory.SW.expo Ψ x (_root_.GlobalTheory.SW.pushZ Ψ Z (Pi.single 0 1) t) z z')) atTop
      (𝓝 (∑' x, g x)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun x => ?_) ?_
    · simp_rw [mul_cexp_expo_pushZ_single_zero]
      by_cases hc : _root_.GlobalTheory.SW.SiegelOp.col Ψ x = 0
      · simp [g, hc]
      · have hpos : 0 < _root_.GlobalTheory.SW.SiegelOp.col Ψ x :=
          lt_of_le_of_ne (col_nonneg' Ψ x) (Ne.symm hc)
        have h1 : Tendsto (fun t : ℝ => 2 * Real.pi * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x) atTop
            atTop :=
          (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)).atTop_mul_const hpos
        have h2 : Tendsto (fun t : ℝ => Real.exp (-(2 * Real.pi * t * _root_.GlobalTheory.SW.SiegelOp.col Ψ x)))
            atTop (𝓝 0) := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
        have h3 := (Complex.continuous_ofReal.tendsto 0).comp h2
        have h4 := (tendsto_const_nhds
          (x := φ x * cexp (2 * ↑Real.pi * I * _root_.GlobalTheory.SW.expo Ψ x Z z z'))).mul h3
        simpa [g, hc] using h4
    · filter_upwards [eventually_ge_atTop 0] with t ht x
      rw [mul_cexp_expo_pushZ_single_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_))
      exact mul_nonneg (mul_nonneg (by positivity) ht) (col_nonneg' Ψ x)
  have hsupp : Function.support g ⊆ Set.range _root_.GlobalTheory.SW.SiegelOp.cons0 := by
    intro x hx
    by_contra hr
    apply hx
    have hc : _root_.GlobalTheory.SW.SiegelOp.col Ψ x ≠ 0 := fun h =>
      hr ((col_eq_zero_iff_exists_eq_cons0 Ψ hne x).mp h |>.elim fun y hy => ⟨y, hy.symm⟩)
    simp [g, hc]
  have key : ∑' x, g x = ∑' y, _root_.GlobalTheory.SW.dropF φ y * cexp (2 * ↑Real.pi * I *
      _root_.GlobalTheory.SW.expo Ψ y (_root_.GlobalTheory.SW.dropZ Ψ Z)
        (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ)) := by
    rw [← cons0_injective.tsum_eq hsupp]
    refine tsum_congr fun y => ?_
    have hc : _root_.GlobalTheory.SW.SiegelOp.col Ψ (_root_.GlobalTheory.SW.SiegelOp.cons0 y) = 0 :=
      (col_eq_zero_iff_exists_eq_cons0 Ψ hne _).mpr ⟨y, rfl⟩
    simp only [g, hc, if_true, expo_cons0']
    rfl
  unfold _root_.GlobalTheory.SW.thH
  rw [← key]
  exact hlim
