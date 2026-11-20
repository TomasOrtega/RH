import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.ResSumInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Establish `hne : ((ϖ : k)) ^ e ≠ 0` using `pow_ne_zero _ ϖ.ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Establish `hc' : ((a : k) - b) = (ϖ : k) ^ e * c`.

Use `congrArg (fun x : 𝒪[k] => (x : k)) hc` as an intermediate fact. Simplify using `using this`. Rewrite using `[hc']`. Establish `: (((ϖ ^ e)⁻¹ : kˣ) : k) * ((ϖ : k) ^ e * c) = c`. Rewrite using `[Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]`.

Rewrite using `[this]`. Conclude with `c.2`. Introduce `h`. Use `⟨⟨_, h⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[← mul_assoc, mul_inv_cancel₀ hne, one_mul]`.
-/
theorem mk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b) ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hne : ((ϖ : k)) ^ e ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  constructor
  · rintro ⟨c, hc⟩
    have hc' : ((a : k) - b) = (ϖ : k) ^ e * c := by
      have := congrArg (fun x : 𝒪[k] => (x : k)) hc
      simpa using this
    rw [hc']
    have : (((ϖ ^ e)⁻¹ : kˣ) : k) * ((ϖ : k) ^ e * c) = c := by
      rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [this]; exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hY l j)`.
-/
theorem mul_mem_int {A C B : Type} [Fintype C] {X : Matrix A C k} {Y : Matrix C B k}
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ 𝒪[k]) (i : A) (j : B) : (X * Y) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hY l j)

/- English proof (translation)
Take `⟨hM1, hM2⟩` from `(mem_KO_iff M).1 hM`. Use `set c : k := (((ϖ ^ e)⁻¹ : kˣ) : k) with hc`. Establish `hint : ∀ (S : A → B → Res k e) i j, (M.val * liftRes S) i j ∈ 𝒪[k]` using `fun S => mul_mem_int hM1 (liftRes_mem S)`. Set `φ : (A → B → Res k e) → (A → B → Res k e)` to `fun S i j => Ideal.Quotient.mk _ (⟨(M.val * liftRes S) i j, hint S i j⟩ : 𝒪[k])`. Establish `h1 : ∀ S i j, c * (liftRes (φ S) i j - (M.val * liftRes S) i j) ∈ 𝒪[k]`.

Introduce `S i j`. Use `(mk_eq_iff hϖ e (Quotient.out (φ S i j)) ⟨(M.val * liftRes S) i j, hint S i j⟩).1 (Ideal.Quotient.mk_out _)` as an intermediate fact. Conclude with `this`. Establish `hinj : Function.Injective φ`. Introduce `S S' h`.

Establish `hd : ∀ i j, c * ((M.val * liftRes S) i j - (M.val * liftRes S') i j) ∈ 𝒪[k]` using `fun i j => (mk_eq_iff hϖ e ⟨_, hint S i j⟩ ⟨_, hint S' i j⟩).1 (congrFun (congrFun h i) j)`. Establish `hD : ∀ i j, (c • (M.val * liftRes S - M.val * liftRes S')) i j ∈ 𝒪[k]` using `fun i j => by`. Simplify `hd i j` using `[mul_sub]`. Establish `hL : c • (liftRes S - liftRes S') = (M⁻¹).val * (c • (M.val * liftRes S - M.val * liftRes S'))`. Rewrite using `[Matrix.mul_smul, ← Matrix.mul_sub, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`.

Use function extensionality and compare the values at `i j`. Establish `hij : c * (((Quotient.out (S i j) : 𝒪[k]) : k) - ((Quotient.out (S' i j) : 𝒪[k]) : k)) ∈ 𝒪[k]`. Use `mul_mem_int hM2 hD i j` as an intermediate fact. Rewrite `this` using `[← hL]`. Simplify `this` using `[liftRes, mul_sub]`.

Use `(mk_eq_iff hϖ e (Quotient.out (S i j)) (Quotient.out (S' i j))).2 hij` as an intermediate fact. Rewrite `this` using `[Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]`. Then use the resulting hypothesis. Establish `hbij : Function.Bijective φ` using `Finite.injective_iff_bijective.1 hinj`. Rewrite using `[← Fintype.sum_bijective φ hbij (fun S => f ((ϖ ^ e)⁻¹ • liftRes (φ S))) (fun S => f ((ϖ ^ e)⁻¹ • liftRes S)) (fun _ => rfl)]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations.

Establish `hsm : ∀ N : Matrix A B k, (ϖ ^ e)⁻¹ • N = c • N` using `fun N => rfl`. Rewrite using `[hsm, hsm, Matrix.mul_smul]`. Establish `: c • liftRes (φ S) = c • (M.val * liftRes S) + c • (liftRes (φ S) - M.val * liftRes S)`. Rewrite using `[← smul_add, add_sub_cancel]`. Rewrite using `[this, hf]`.

Introduce `i j`. Simplify `h1 S i j` using `[mul_sub]`.
-/
theorem sum_res_mul_left {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (f : Matrix A B k → ℂ)
    (hf : ∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z)
    (M : GL A k) (hM : M ∈ KO k A) :
    ∑ S : A → B → Res k e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) =
      ∑ S : A → B → Res k e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  obtain ⟨hM1, hM2⟩ := (mem_KO_iff M).1 hM
  set c : k := (((ϖ ^ e)⁻¹ : kˣ) : k) with hc
  have hint : ∀ (S : A → B → Res k e) i j, (M.val * liftRes S) i j ∈ 𝒪[k] :=
    fun S => mul_mem_int hM1 (liftRes_mem S)
  let φ : (A → B → Res k e) → (A → B → Res k e) := fun S i j =>
    Ideal.Quotient.mk _ (⟨(M.val * liftRes S) i j, hint S i j⟩ : 𝒪[k])
  have h1 : ∀ S i j, c * (liftRes (φ S) i j - (M.val * liftRes S) i j) ∈ 𝒪[k] := by
    intro S i j
    have := (mk_eq_iff hϖ e (Quotient.out (φ S i j)) ⟨(M.val * liftRes S) i j, hint S i j⟩).1
      (Ideal.Quotient.mk_out _)
    exact this
  have hinj : Function.Injective φ := by
    intro S S' h
    have hd : ∀ i j, c * ((M.val * liftRes S) i j - (M.val * liftRes S') i j) ∈ 𝒪[k] := fun i j =>
      (mk_eq_iff hϖ e ⟨_, hint S i j⟩ ⟨_, hint S' i j⟩).1 (congrFun (congrFun h i) j)
    have hD : ∀ i j, (c • (M.val * liftRes S - M.val * liftRes S')) i j ∈ 𝒪[k] := fun i j => by
      simpa [mul_sub] using hd i j
    have hL : c • (liftRes S - liftRes S') = (M⁻¹).val * (c • (M.val * liftRes S - M.val * liftRes S')) := by
      rw [Matrix.mul_smul, ← Matrix.mul_sub, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
    funext i j
    have hij : c * (((Quotient.out (S i j) : 𝒪[k]) : k) - ((Quotient.out (S' i j) : 𝒪[k]) : k)) ∈ 𝒪[k] := by
      have := mul_mem_int hM2 hD i j
      rw [← hL] at this
      simpa [liftRes, mul_sub] using this
    have := (mk_eq_iff hϖ e (Quotient.out (S i j)) (Quotient.out (S' i j))).2 hij
    rwa [Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at this
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hinj
  rw [← Fintype.sum_bijective φ hbij (fun S => f ((ϖ ^ e)⁻¹ • liftRes (φ S))) (fun S => f ((ϖ ^ e)⁻¹ • liftRes S)) (fun _ => rfl)]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hsm : ∀ N : Matrix A B k, (ϖ ^ e)⁻¹ • N = c • N := fun N => rfl
  rw [hsm, hsm, Matrix.mul_smul]
  have : c • liftRes (φ S) = c • (M.val * liftRes S) + c • (liftRes (φ S) - M.val * liftRes S) := by
    rw [← smul_add, add_sub_cancel]
  rw [this, hf]
  intro i j
  simpa [mul_sub] using h1 S i j

end GlobalTheory.ResSumInv
