import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapFOneInjectiveOfSectionsSurjective

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module

universe t v u

noncomputable section

namespace GlobalTheory

namespace ExactSeq

section Ring

variable {R : Type*} [Ring R] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_of_isNoetherian (h : Function.Exact f g) [Module.Finite R A] [IsNoetherian R C] :
    Module.Finite R B :=
  Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
    (fun x ↦ by rw [← h x, Subtype.ext_iff]; rfl) g.surjective_rangeRestrict

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite [IsNoetherianRing R] (h : Function.Exact f g) [Module.Finite R A]
    [Module.Finite R C] : Module.Finite R B :=
  finite_of_isNoetherian h

end Ring

section Field

variable {k : Type*} [DivisionRing k]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_eq_range_add_range {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module k A] [Module k B] [Module k C] {f : A →ₗ[k] B} {g : B →ₗ[k] C}
    (h : Function.Exact f g) [Module.Finite k B] :
    finrank k B = finrank k (LinearMap.range f) + finrank k (LinearMap.range g) := by
  rw [← g.finrank_range_add_finrank_ker, h.linearMap_ker_eq, add_comm]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_le {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module k A] [Module k B] [Module k C] {f : A →ₗ[k] B} {g : B →ₗ[k] C}
    (h : Function.Exact f g) [Module.Finite k A] [Module.Finite k C] :
    finrank k B ≤ finrank k A + finrank k C := by
  have : Module.Finite k B := finite h
  rw [finrank_eq_range_add_range h]
  exact add_le_add f.finrank_range_le (Submodule.finrank_le _)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_neg_one_pow_finrank {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (f : ∀ i, V i →ₗ[k] V (i + 1)) (N : ℕ) (hV : ∀ i < N, Module.Finite k (V i))
    (h : ∀ i < N, Function.Exact (f i) (f (i + 1))) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (V i) =
      finrank k (LinearMap.ker (f 0)) - (-1) ^ N * finrank k (LinearMap.ker (f N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have := hV N N.lt_succ_self
    rw [Finset.sum_range_succ, ih (fun i hi ↦ hV i (by omega)) (fun i hi ↦ h i (by omega)),
      ← (f N).finrank_range_add_finrank_ker, (h N N.lt_succ_self).linearMap_ker_eq]
    push_cast
    ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_neg_one_pow_finrank_eq_zero {V : ℕ → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (f : ∀ i, V i →ₗ[k] V (i + 1)) (N : ℕ)
    (hV : ∀ i < N, Module.Finite k (V i)) (h₀ : Function.Injective (f 0))
    (h : ∀ i < N, Function.Exact (f i) (f (i + 1))) (hN : Subsingleton (V N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (V i) = 0 := by
  rw [sum_neg_one_pow_finrank f N hV h, LinearMap.ker_eq_bot.2 h₀, finrank_bot,
    finrank_zero_of_subsingleton (M := LinearMap.ker (f N))]
  simp

variable {A B C : ℕ → Type*} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module k (A i)] [∀ i, Module k (B i)] [∀ i, Module k (C i)]
  (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_neg_one_pow_finrank₃ (N : ℕ) (hA : ∀ i < N, Module.Finite k (A i))
    (hB : ∀ i < N, Module.Finite k (B i)) (hC : ∀ i < N, Module.Finite k (C i))
    (h₂ : ∀ i < N, Function.Exact (f i) (g i)) (h₃ : ∀ i < N, Function.Exact (g i) (δ i))
    (h₁ : ∀ i < N, Function.Exact (δ i) (f (i + 1))) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (finrank k (A i) - finrank k (B i) + finrank k (C i)) =
      finrank k (LinearMap.ker (f 0)) - (-1) ^ N * finrank k (LinearMap.ker (f N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN := N.lt_succ_self
    have := hA N hN
    have := hB N hN
    have := hC N hN
    rw [Finset.sum_range_succ, ih (fun i hi ↦ hA i (by omega)) (fun i hi ↦ hB i (by omega))
      (fun i hi ↦ hC i (by omega)) (fun i hi ↦ h₂ i (by omega)) (fun i hi ↦ h₃ i (by omega))
      (fun i hi ↦ h₁ i (by omega)), ← (f N).finrank_range_add_finrank_ker,
      finrank_eq_range_add_range (h₂ N hN), finrank_eq_range_add_range (h₃ N hN),
      (h₁ N hN).linearMap_ker_eq]
    push_cast
    ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_neg_one_pow_finrank_eq_add (N : ℕ) (hA : ∀ i < N, Module.Finite k (A i))
    (hB : ∀ i < N, Module.Finite k (B i)) (hC : ∀ i < N, Module.Finite k (C i))
    (h₀ : Function.Injective (f 0))
    (h₂ : ∀ i < N, Function.Exact (f i) (g i)) (h₃ : ∀ i < N, Function.Exact (g i) (δ i))
    (h₁ : ∀ i < N, Function.Exact (δ i) (f (i + 1))) (hN : Function.Injective (f N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (B i) =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (A i) +
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (C i) := by
  have := sum_neg_one_pow_finrank₃ f g δ N hA hB hC h₂ h₃ h₁
  rw [LinearMap.ker_eq_bot.2 h₀, LinearMap.ker_eq_bot.2 hN, finrank_bot, finrank_bot] at this
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Nat.cast_zero,
    mul_zero, sub_zero] at this
  linarith

end Field

end ExactSeq

variable {X : Scheme.{u}}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shortExact_toAbSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toAbSheaf X)).ShortExact :=
  SheafLES.shortExact_map_toSheaf X.ringCatSheaf hS

@[simps] def smulShortComplexHom (S : ShortComplex X.Modules) (r : Γ(X, ⊤)) : S ⟶ S where
  τ₁ := smulHom S.X₁ r
  τ₂ := smulHom S.X₂ r
  τ₃ := smulHom S.X₃ r
  comm₁₂ := smulHom_comp S.f r
  comm₂₃ := smulHom_comp S.g r

namespace cohOn

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)

def δ (U : X.Opens) (n : ℕ) : cohOn S.X₃ U n →ₗ[R] cohOn S.X₁ U (n + 1) :=
  WithAction.linearMap (action S.X₃ U n) (action S.X₁ U (n + 1)) R
    (SheafLES.δ.{u} (shortExact_toAbSheaf hS) n U) fun r x ↦ by
      rw [action_apply, action_apply]
      exact (SheafLES.δ_naturality.{u} (shortExact_toAbSheaf hS) (shortExact_toAbSheaf hS)
        ((toAbSheaf X).mapShortComplex.map (smulShortComplexHom S r)) n U x).symm

variable (U : X.Opens) (n : ℕ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma toH'_δ (x : cohOn S.X₃ U n) :
    toH' S.X₁ U (n + 1) (δ R hS U n x) =
      SheafLES.δ.{u} (shortExact_toAbSheaf hS) n U (toH' S.X₃ U n x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma δ_eq_δ (R' : Type t) [CommRing R'] [Algebra R' Γ(X, ⊤)] (x : cohOn S.X₃ U n) :
    δ R hS U n x = δ R' hS U n x := rfl

include hS in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exact₂ : Function.Exact (map R S.f U n) (map R S.g U n) :=
  SheafLES.exact₂.{u} (shortExact_toAbSheaf hS) n U

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exact₃ : Function.Exact (map R S.g U n) (δ R hS U n) :=
  SheafLES.exact₃.{u} (shortExact_toAbSheaf hS) n U

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exact₁ : Function.Exact (δ R hS U n) (map R S.f U (n + 1)) :=
  SheafLES.exact₁.{u} (shortExact_toAbSheaf hS) n U

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem map_zero_injective_of_mono {F G : X.Modules} (φ : F ⟶ G) [Mono φ] :
    Function.Injective (map R φ U 0) :=
  SheafLES.map_zero_injective_of_mono.{u} ((toAbSheaf X).map φ) U

include hS in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem injective_zero : Function.Injective (map R S.f U 0) :=
  SheafLES.injective_zero.{u} (shortExact_toAbSheaf hS) U

/- English proof (translation)
A detailed English derivation is pending.
-/
@[simp] lemma δ_map (x : cohOn S.X₂ U n) : δ R hS U n (map R S.g U n x) = 0 :=
  (exact₃ R hS U n).apply_apply_eq_zero x

/- English proof (translation)
A detailed English derivation is pending.
-/
@[simp] lemma map_δ (x : cohOn S.X₃ U n) : map R S.f U (n + 1) (δ R hS U n x) = 0 :=
  (exact₁ R hS U n).apply_apply_eq_zero x

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem δ_naturality {S' : ShortComplex X.Modules} (hS' : S'.ShortExact) (φ : S ⟶ S')
    (x : cohOn S.X₃ U n) :
    map R φ.τ₁ U (n + 1) (δ R hS U n x) = δ R hS' U n (map R φ.τ₃ U n x) :=
  SheafLES.δ_naturality.{u} (shortExact_toAbSheaf hS) (shortExact_toAbSheaf hS')
    ((toAbSheaf X).mapShortComplex.map φ) n U x

variable {U} in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem res_δ {V : X.Opens} (h : V ≤ U) (x : cohOn S.X₃ U n) :
    res R S.X₁ h (n + 1) (δ R hS U n x) = δ R hS V n (res R S.X₃ h n x) :=
  SheafLES.δ_res.{u} (shortExact_toAbSheaf hS) n (homOfLE h) x

include hS

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem map_g_surjective (h : Subsingleton (cohOn S.X₁ U (n + 1))) :
    Function.Surjective (map R S.g U n) :=
  fun x ↦ (exact₃ R hS U n x).1 (Subsingleton.elim _ _)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem map_f_injective (h : Subsingleton (cohOn S.X₃ U n)) :
    Function.Injective (map R S.f U (n + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact₁ R hS U n x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem app_surjective (h : Subsingleton (cohOn S.X₁ U 1)) : Function.Surjective (S.g.app U) :=
  SheafLES.sections_surjective_of_subsingleton.{u} (shortExact_toAbSheaf hS) U h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem subsingleton₂ (h₁ : Subsingleton (cohOn S.X₁ U n)) (h₃ : Subsingleton (cohOn S.X₃ U n)) :
    Subsingleton (cohOn S.X₂ U n) :=
  SheafLES.subsingleton₂.{u} (shortExact_toAbSheaf hS) n U h₁ h₃

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem subsingleton₃ (h₂ : Subsingleton (cohOn S.X₂ U n))
    (h₁ : Subsingleton (cohOn S.X₁ U (n + 1))) : Subsingleton (cohOn S.X₃ U n) :=
  SheafLES.subsingleton₃.{u} (shortExact_toAbSheaf hS) n U h₂ h₁

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem subsingleton₁ (h₃ : Subsingleton (cohOn S.X₃ U n))
    (h₂ : Subsingleton (cohOn S.X₂ U (n + 1))) : Subsingleton (cohOn S.X₁ U (n + 1)) :=
  SheafLES.subsingleton₁.{u} (shortExact_toAbSheaf hS) n U h₃ h₂

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem subsingleton₁_zero (h₂ : Subsingleton (cohOn S.X₂ U 0)) : Subsingleton (cohOn S.X₁ U 0) :=
  (injective_zero ℤ hS U).subsingleton

section Finite

variable [IsNoetherianRing R]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite₂ (h₁ : Module.Finite R (cohOn S.X₁ U n)) (h₃ : Module.Finite R (cohOn S.X₃ U n)) :
    Module.Finite R (cohOn S.X₂ U n) :=
  ExactSeq.finite (exact₂ R hS U n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite₃ (h₂ : Module.Finite R (cohOn S.X₂ U n))
    (h₁ : Module.Finite R (cohOn S.X₁ U (n + 1))) : Module.Finite R (cohOn S.X₃ U n) :=
  ExactSeq.finite (exact₃ R hS U n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite₁ (h₃ : Module.Finite R (cohOn S.X₃ U n))
    (h₂ : Module.Finite R (cohOn S.X₂ U (n + 1))) : Module.Finite R (cohOn S.X₁ U (n + 1)) :=
  ExactSeq.finite (exact₁ R hS U n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite₁_zero (h₂ : Module.Finite R (cohOn S.X₂ U 0)) : Module.Finite R (cohOn S.X₁ U 0) :=
  Module.Finite.of_injective _ (injective_zero R hS U)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem forall_finite₁ (h₂ : ∀ n, Module.Finite R (cohOn S.X₂ U n))
    (h₃ : ∀ n, Module.Finite R (cohOn S.X₃ U n)) : ∀ n, Module.Finite R (cohOn S.X₁ U n)
  | 0 => finite₁_zero R hS U (h₂ 0)
  | n + 1 => finite₁ R hS U n (h₃ n) (h₂ (n + 1))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem forall_finite₂ (h₁ : ∀ n, Module.Finite R (cohOn S.X₁ U n))
    (h₃ : ∀ n, Module.Finite R (cohOn S.X₃ U n)) : ∀ n, Module.Finite R (cohOn S.X₂ U n) :=
  fun n ↦ finite₂ R hS U n (h₁ n) (h₃ n)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem forall_finite₃ (h₁ : ∀ n, Module.Finite R (cohOn S.X₁ U n))
    (h₂ : ∀ n, Module.Finite R (cohOn S.X₂ U n)) : ∀ n, Module.Finite R (cohOn S.X₃ U n) :=
  fun n ↦ finite₃ R hS U n (h₂ n) (h₁ (n + 1))

end Finite

section Field

variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finrank₂_le (h₁ : Module.Finite k (cohOn S.X₁ U n))
    (h₃ : Module.Finite k (cohOn S.X₃ U n)) :
    finrank k (cohOn S.X₂ U n) ≤ finrank k (cohOn S.X₁ U n) + finrank k (cohOn S.X₃ U n) :=
  ExactSeq.finrank_le (exact₂ k hS U n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finrank₃_le (h₂ : Module.Finite k (cohOn S.X₂ U n))
    (h₁ : Module.Finite k (cohOn S.X₁ U (n + 1))) :
    finrank k (cohOn S.X₃ U n) ≤ finrank k (cohOn S.X₂ U n) + finrank k (cohOn S.X₁ U (n + 1)) :=
  ExactSeq.finrank_le (exact₃ k hS U n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finrank₁_le (h₃ : Module.Finite k (cohOn S.X₃ U n))
    (h₂ : Module.Finite k (cohOn S.X₂ U (n + 1))) :
    finrank k (cohOn S.X₁ U (n + 1)) ≤
      finrank k (cohOn S.X₃ U n) + finrank k (cohOn S.X₂ U (n + 1)) :=
  ExactSeq.finrank_le (exact₁ k hS U n)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finrank₁_zero_le (h₂ : Module.Finite k (cohOn S.X₂ U 0)) :
    finrank k (cohOn S.X₁ U 0) ≤ finrank k (cohOn S.X₂ U 0) :=
  LinearMap.finrank_le_finrank_of_injective (injective_zero k hS U)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_neg_one_pow_finrank (N : ℕ) (h₁ : ∀ i < N, Module.Finite k (cohOn S.X₁ U i))
    (h₂ : ∀ i < N, Module.Finite k (cohOn S.X₂ U i))
    (h₃ : ∀ i < N, Module.Finite k (cohOn S.X₃ U i)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (finrank k (cohOn S.X₁ U i) -
        finrank k (cohOn S.X₂ U i) + finrank k (cohOn S.X₃ U i)) =
      -(-1) ^ N * finrank k (LinearMap.ker (map k S.f U N)) := by
  rw [ExactSeq.sum_neg_one_pow_finrank₃ (fun i ↦ map k S.f U i) (fun i ↦ map k S.g U i)
    (fun i ↦ δ k hS U i) N h₁ h₂ h₃ (fun i _ ↦ exact₂ k hS U i) (fun i _ ↦ exact₃ k hS U i)
    (fun i _ ↦ exact₁ k hS U i), LinearMap.ker_eq_bot.2 (injective_zero k hS U), finrank_bot]
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sum_neg_one_pow_finrank_eq_add (N : ℕ)
    (h₁ : ∀ i < N, Module.Finite k (cohOn S.X₁ U i))
    (h₃ : ∀ i < N, Module.Finite k (cohOn S.X₃ U i)) (hN : Function.Injective (map k S.f U N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (cohOn S.X₂ U i) =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (cohOn S.X₁ U i) +
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (cohOn S.X₃ U i) :=
  ExactSeq.sum_neg_one_pow_finrank_eq_add (fun i ↦ map k S.f U i) (fun i ↦ map k S.g U i)
    (fun i ↦ δ k hS U i) N h₁ (fun i hi ↦ finite₂ k hS U i (h₁ i hi) (h₃ i hi)) h₃
    (injective_zero k hS U) (fun i _ ↦ exact₂ k hS U i) (fun i _ ↦ exact₃ k hS U i)
    (fun i _ ↦ exact₁ k hS U i) hN

end Field

end cohOn

section hdim

variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hdim₂_le (n : ℕ) (h₁ : Module.Finite k (coh S.X₁ n)) (h₃ : Module.Finite k (coh S.X₃ n)) :
    hdim k S.X₂ n ≤ hdim k S.X₁ n + hdim k S.X₃ n :=
  cohOn.finrank₂_le hS ⊤ n k h₁ h₃

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hdim₃_le (n : ℕ) (h₂ : Module.Finite k (coh S.X₂ n))
    (h₁ : Module.Finite k (coh S.X₁ (n + 1))) :
    hdim k S.X₃ n ≤ hdim k S.X₂ n + hdim k S.X₁ (n + 1) :=
  cohOn.finrank₃_le hS ⊤ n k h₂ h₁

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hdim₁_le (n : ℕ) (h₃ : Module.Finite k (coh S.X₃ n))
    (h₂ : Module.Finite k (coh S.X₂ (n + 1))) :
    hdim k S.X₁ (n + 1) ≤ hdim k S.X₃ n + hdim k S.X₂ (n + 1) :=
  cohOn.finrank₁_le hS ⊤ n k h₃ h₂

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hdim₁_zero_le (h₂ : Module.Finite k (coh S.X₂ 0)) : hdim k S.X₁ 0 ≤ hdim k S.X₂ 0 :=
  cohOn.finrank₁_zero_le hS ⊤ k h₂

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sum_neg_one_pow_hdim_eq_add (N : ℕ) (h₁ : ∀ i < N, Module.Finite k (coh S.X₁ i))
    (h₃ : ∀ i < N, Module.Finite k (coh S.X₃ i)) (hN : Subsingleton (coh S.X₁ N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₂ i =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₁ i +
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₃ i :=
  cohOn.sum_neg_one_pow_finrank_eq_add hS ⊤ k N h₁ h₃ (Function.injective_of_subsingleton _)

omit hS in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finsum_neg_one_pow_hdim_eq_sum (F : X.Modules) (N : ℕ)
    (hN : ∀ i, N ≤ i → Subsingleton (coh F i)) :
    ∑ᶠ i, (-1 : ℤ) ^ i * hdim k F i = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k F i := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  by_contra h
  have := hN i (by simpa using h)
  exact hi (by simp [hdim_eq_zero_of_subsingleton])

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finsum_neg_one_pow_hdim_eq_add (h₁ : ∀ i, Module.Finite k (coh S.X₁ i))
    (h₃ : ∀ i, Module.Finite k (coh S.X₃ i))
    (hv₁ : ∃ N, ∀ i, N ≤ i → Subsingleton (coh S.X₁ i))
    (hv₃ : ∃ N, ∀ i, N ≤ i → Subsingleton (coh S.X₃ i)) :
    ∑ᶠ i, (-1 : ℤ) ^ i * hdim k S.X₂ i =
      ∑ᶠ i, (-1 : ℤ) ^ i * hdim k S.X₁ i + ∑ᶠ i, (-1 : ℤ) ^ i * hdim k S.X₃ i := by
  obtain ⟨N₁, hv₁⟩ := hv₁
  obtain ⟨N₃, hv₃⟩ := hv₃
  have e₁ : ∀ i, max N₁ N₃ ≤ i → Subsingleton (coh S.X₁ i) := fun i hi ↦ hv₁ i (by omega)
  have e₃ : ∀ i, max N₁ N₃ ≤ i → Subsingleton (coh S.X₃ i) := fun i hi ↦ hv₃ i (by omega)
  rw [finsum_neg_one_pow_hdim_eq_sum k _ _ e₁, finsum_neg_one_pow_hdim_eq_sum k _ _ e₃,
    finsum_neg_one_pow_hdim_eq_sum k S.X₂ (max N₁ N₃)
      fun i hi ↦ cohOn.subsingleton₂ hS ⊤ i (e₁ i hi) (e₃ i hi)]
  exact sum_neg_one_pow_hdim_eq_add k hS _ (fun i _ ↦ h₁ i) (fun i _ ↦ h₃ i) (e₁ _ le_rfl)

end hdim

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem linear_longExact {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (∀ (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (U : X.Opens),
      (∃ d : ∀ n, cohOn S.X₃ U n →ₗ[R] cohOn S.X₁ U (n + 1),
        (∀ n x, cohOn.toH' S.X₁ U (n + 1) (d n x) =
          SheafLES.δ.{u} (shortExact_toAbSheaf hS) n U (cohOn.toH' S.X₃ U n x)) ∧
        Function.Injective (cohOn.map R S.f U 0) ∧ ∀ n,
          Function.Exact (cohOn.map R S.f U n) (cohOn.map R S.g U n) ∧
          Function.Exact (cohOn.map R S.g U n) (d n) ∧
          Function.Exact (d n) (cohOn.map R S.f U (n + 1))) ∧
      (IsNoetherianRing R →
        (Module.Finite R (cohOn S.X₂ U 0) → Module.Finite R (cohOn S.X₁ U 0)) ∧ ∀ n,
        (Module.Finite R (cohOn S.X₁ U n) → Module.Finite R (cohOn S.X₃ U n) →
          Module.Finite R (cohOn S.X₂ U n)) ∧
        (Module.Finite R (cohOn S.X₂ U n) → Module.Finite R (cohOn S.X₁ U (n + 1)) →
          Module.Finite R (cohOn S.X₃ U n)) ∧
        (Module.Finite R (cohOn S.X₃ U n) → Module.Finite R (cohOn S.X₂ U (n + 1)) →
          Module.Finite R (cohOn S.X₁ U (n + 1))))) ∧
    ∀ (k : Type v) [Field k] [Algebra k Γ(X, ⊤)],
      (∀ n, Module.Finite k (coh S.X₁ n) → Module.Finite k (coh S.X₃ n) →
        hdim k S.X₂ n ≤ hdim k S.X₁ n + hdim k S.X₃ n) ∧
      ∀ N, (∀ i < N, Module.Finite k (coh S.X₁ i)) → (∀ i < N, Module.Finite k (coh S.X₃ i)) →
        Subsingleton (coh S.X₁ N) →
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₂ i =
          ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₁ i +
            ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₃ i :=
  ⟨fun R _ _ U ↦ ⟨⟨cohOn.δ R hS U, cohOn.toH'_δ R hS U, cohOn.injective_zero R hS U,
      fun n ↦ ⟨cohOn.exact₂ R hS U n, cohOn.exact₃ R hS U n, cohOn.exact₁ R hS U n⟩⟩,
    fun _ ↦ ⟨cohOn.finite₁_zero R hS U, fun n ↦
      ⟨cohOn.finite₂ R hS U n, cohOn.finite₃ R hS U n, cohOn.finite₁ R hS U n⟩⟩⟩,
   fun k _ _ ↦ ⟨hdim₂_le k hS, sum_neg_one_pow_hdim_eq_add k hS⟩⟩

end GlobalTheory
