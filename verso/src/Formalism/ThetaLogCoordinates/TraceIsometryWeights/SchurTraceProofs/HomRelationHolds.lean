import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementA

namespace Formalism.InvariantFactorPaths.PW

open Finset

section gen

variable {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homAct_apply (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) (φ : V →ₗ[K] W) (x : V) :
    homAct EV EW a b φ x = EW a b (φ x) - φ (EV a b x) := rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `[homAct_apply, hθ]`.
-/
theorem homAct_postcomp {W' : Type} [AddCommGroup W'] [Module K W'] (EV : ι → ι → Module.End K V)
    (EW : ι → ι → Module.End K W) (EW' : ι → ι → Module.End K W') (θ : W →ₗ[K] W')
    (hθ : ∀ a b x, θ (EW a b x) = EW' a b (θ x)) (a b : ι) (φ : V →ₗ[K] W) :
    θ ∘ₗ (homAct EV EW a b φ) = homAct EV EW' a b (θ ∘ₗ φ) := by
  ext x
  simp [homAct_apply, hθ]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[homAct_apply, hι]`.
-/
theorem homAct_precomp {V' : Type} [AddCommGroup V'] [Module K V'] (EV : ι → ι → Module.End K V)
    (EV' : ι → ι → Module.End K V') (EW : ι → ι → Module.End K W) (ι' : V' →ₗ[K] V)
    (hι : ∀ a b x, ι' (EV' a b x) = EV a b (ι' x)) (a b : ι) (φ : V →ₗ[K] W) :
    (homAct EV EW a b φ) ∘ₗ ι' = homAct EV' EW a b (φ ∘ₗ ι') := by
  ext x
  simp [homAct_apply, hι]

def postC (X : Module.End K W) : Module.End K (V →ₗ[K] W) where
  toFun := fun φ => X ∘ₗ φ
  map_add' := by intro φ ψ; ext x; simp
  map_smul' := by intro c φ; ext x; simp

def preC (Y : Module.End K V) : Module.End K (V →ₗ[K] W) where
  toFun := fun φ => φ ∘ₗ Y
  map_add' := by intro φ ψ; ext x; simp
  map_smul' := by intro c φ; ext x; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem postC_apply (X : Module.End K W) (φ : V →ₗ[K] W) (x : V) : postC X φ x = X (φ x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem preC_apply (Y : Module.End K V) (φ : V →ₗ[K] W) (x : V) : preC (W := W) Y φ x = φ (Y x) := rfl

/- English proof (translation)
Proceed by induction on `i generalizing φ with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Rewrite using `[pow_succ (postC (V := V) X) i, pow_succ X i]`. Conclude with `ih (postC X φ)`.
-/
theorem postC_pow_apply (X : Module.End K W) (i : ℕ) (φ : V →ₗ[K] W) (x : V) :
    ((postC X) ^ i) φ x = (X ^ i) (φ x) := by
  induction i generalizing φ with
  | zero => simp
  | succ i ih =>
    rw [pow_succ (postC (V := V) X) i, pow_succ X i]
    exact ih (postC X φ)

/- English proof (translation)
Proceed by induction on `j generalizing φ with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ (preC (W := W) Y) j, pow_succ' Y j]`. Conclude with `ih (preC Y φ)`.
-/
theorem preC_pow_apply (Y : Module.End K V) (j : ℕ) (φ : V →ₗ[K] W) (x : V) :
    ((preC (W := W) Y) ^ j) φ x = φ ((Y ^ j) x) := by
  induction j generalizing φ with
  | zero => simp
  | succ j ih =>
    rw [pow_succ (preC (W := W) Y) j, pow_succ' Y j]
    exact ih (preC Y φ)

/- English proof (translation)
Use `show postC (V := V) X * preC (W := W) Y = preC (W := W) Y * postC (V := V) X`. Use extensionality with `φ x`. Both sides reduce to the same expression.
-/
theorem postC_preC_commute (X : Module.End K W) (Y : Module.End K V) :
    Commute (postC (V := V) X) (preC (W := W) Y) := by
  show postC (V := V) X * preC (W := W) Y = preC (W := W) Y * postC (V := V) X
  ext φ x
  rfl

/- English proof (translation)
Use extensionality with `φ x`. Simplify using `only [homAct_apply, LinearMap.add_apply, LinearMap.neg_apply, postC_apply, preC_apply, sub_eq_add_neg]`.
-/
theorem homAct_eq (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) :
    homAct EV EW a b = postC (EW a b) + -preC (EV a b) := by
  ext φ x
  simp only [homAct_apply, LinearMap.add_apply, LinearMap.neg_apply, postC_apply, preC_apply, sub_eq_add_neg]

/- English proof (translation)
Establish `hc : Commute (postC (V` using `V) (EW a b)) ((-1 : K) • preC (W := W) (EV a b)) := (postC_preC_commute (EW a b) (EV a b)).smul_right (-1 : K)`. Establish `he : homAct EV EW a b = postC (EW a b) + (-1 : K) • preC (EV a b)`. Rewrite using `[homAct_eq, neg_one_smul]`. Rewrite using `[he, hc.add_pow', LinearMap.sum_apply, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_pow, mul_smul_comm, ← Nat.cast_smul_eq_nsmul K, smul_smul]`. Simplify using `only [LinearMap.smul_apply, Module.End.mul_apply, postC_pow_apply, preC_pow_apply]`.
-/
theorem homAct_pow_apply (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W) (a b : ι) (k : ℕ)
    (φ : V →ₗ[K] W) (x : V) :
    ((homAct EV EW a b) ^ k) φ x =
      ∑ m ∈ antidiagonal k, ((k.choose m.1 : K) * (-1) ^ m.2) • ((EW a b) ^ m.1) (φ (((EV a b) ^ m.2) x)) := by
  have hc : Commute (postC (V := V) (EW a b)) ((-1 : K) • preC (W := W) (EV a b)) :=
    (postC_preC_commute (EW a b) (EV a b)).smul_right (-1 : K)
  have he : homAct EV EW a b = postC (EW a b) + (-1 : K) • preC (EV a b) := by
    rw [homAct_eq, neg_one_smul]
  rw [he, hc.add_pow', LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_pow, mul_smul_comm, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, postC_pow_apply, preC_pow_apply]

end gen

/- English proof (translation)
Introduce `K V W ι _ _ _ _ _ _ EV EW hV hW`. Unfold `GlRel at *`. Introduce `a b c d`. Use extensionality with `φ x`. Establish `h1` using `LinearMap.congr_fun (hW a b c d) (φ x)`.

Establish `h2` using `congrArg φ (LinearMap.congr_fun (hV a b c d) x)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, homAct_apply, map_sub] at h1 h2 ⊢`. Apply the tactic sequence `split_ifs at h1 h2 ⊢ <;>`. Apply the tactic sequence `simp only [LinearMap.zero_apply, map_zero, homAct_apply, sub_zero, zero_sub, map_neg, LinearMap.sub_apply, map_sub] at h1 h2 ⊢ <;>`. Apply the tactic sequence `rw [eq_add_of_sub_eq h1, eq_add_of_sub_eq h2] <;> abel`.
-/
theorem hom_relation_holds : HomRel := by
  intro K V W ι _ _ _ _ _ _ EV EW hV hW
  unfold GlRel at *
  intro a b c d
  ext φ x
  have h1 := LinearMap.congr_fun (hW a b c d) (φ x)
  have h2 := congrArg φ (LinearMap.congr_fun (hV a b c d) x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, homAct_apply, map_sub] at h1 h2 ⊢
  split_ifs at h1 h2 ⊢ <;>
    simp only [LinearMap.zero_apply, map_zero, homAct_apply, sub_zero, zero_sub, map_neg, LinearMap.sub_apply, map_sub] at h1 h2 ⊢ <;>
    rw [eq_add_of_sub_eq h1, eq_add_of_sub_eq h2] <;> abel

/- English proof (translation)
Introduce `p _ V W ι _ _ _ _ _ EV EW L M hM hL hW`. Unfold `ZpClosed DivStable HomLat at *`. Use `⟨fun c hc φ hφ => ?_, fun a b hab k φ hφ => ?_⟩` and prove the remaining obligations. Establish `hφ' : ∀ y ∈ L, φ y ∈ M` using `hφ show ∀ y ∈ L, (c • φ) y ∈ M`. Introduce `y hy`.

Conclude with `hM c hc _ (hφ' y hy)`. Establish `hφ' : ∀ y ∈ L, φ y ∈ M` using `hφ show ∀ y ∈ L, ((k.factorial : Padic p)⁻¹ • (homAct EV EW a b ^ k) φ) y ∈ M`. Introduce `x hx`. Rewrite using `[LinearMap.smul_apply, homAct_pow_apply, Finset.smul_sum]`. Use `AddSubgroup.sum_mem M fun m hm => ?_` and prove the remaining obligations.

Establish `hm' : m.1 + m.2 = k` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hm`. Establish `hx2` using `hL a b hab m.2 x hx`. Establish `hy` using `hW a b hab m.1 _ (hφ' _ hx2)`. Establish `hn : ‖((-1 : Padic p) ^ m.2)‖ ≤ 1` using `by simp`. Establish `hz` using `hM _ hn _ hy`.

Simplify using `only [map_smul, smul_smul] at hz`. Simplify using `only [smul_smul]`. Use `hz using 2` and compare the differences between its conclusion and the goal. Substitute `hm'` using the available equality. Establish `h1 : (m.1.factorial : Padic p) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero _`.

Establish `h2 : (m.2.factorial : Padic p) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero _`. Establish `hcn` using `Nat.add_choose_mul_factorial_mul_factorial m.2 m.1`. Rewrite `hcn` using `[add_comm m.2 m.1]`. Establish `hc : ((m.1 + m.2).choose m.1 : Padic p) * m.2.factorial * m.1.factorial = (m.1 + m.2).factorial`. Conclude with `hcn` after adjusting the coercions.

Rewrite using `[← hc]`. Establish `h3 : ((m.1 + m.2).choose m.1 : Padic p) ≠ 0`. Conclude with `(Nat.choose_pos (Nat.le_add_right m.1 m.2)).ne'` after adjusting the coercions. Clear the denominators using the available nonvanishing facts.
-/
theorem hom_divided_holds : HomDiv := by
  intro p _ V W ι _ _ _ _ _ EV EW L M hM hL hW
  unfold ZpClosed DivStable HomLat at *
  refine ⟨fun c hc φ hφ => ?_, fun a b hab k φ hφ => ?_⟩
  · have hφ' : ∀ y ∈ L, φ y ∈ M := hφ
    show ∀ y ∈ L, (c • φ) y ∈ M
    intro y hy
    exact hM c hc _ (hφ' y hy)
  · have hφ' : ∀ y ∈ L, φ y ∈ M := hφ
    show ∀ y ∈ L, ((k.factorial : Padic p)⁻¹ • (homAct EV EW a b ^ k) φ) y ∈ M
    intro x hx
    rw [LinearMap.smul_apply, homAct_pow_apply, Finset.smul_sum]
    refine AddSubgroup.sum_mem M fun m hm => ?_
    have hm' : m.1 + m.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hm
    have hx2 := hL a b hab m.2 x hx
    have hy := hW a b hab m.1 _ (hφ' _ hx2)
    have hn : ‖((-1 : Padic p) ^ m.2)‖ ≤ 1 := by simp
    have hz := hM _ hn _ hy
    simp only [map_smul, smul_smul] at hz
    simp only [smul_smul]
    convert hz using 2
    subst hm'
    have h1 : (m.1.factorial : Padic p) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : (m.2.factorial : Padic p) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hcn := Nat.add_choose_mul_factorial_mul_factorial m.2 m.1
    rw [add_comm m.2 m.1] at hcn
    have hc : ((m.1 + m.2).choose m.1 : Padic p) * m.2.factorial * m.1.factorial = (m.1 + m.2).factorial := by
      exact_mod_cast hcn
    rw [← hc]
    have h3 : ((m.1 + m.2).choose m.1 : Padic p) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right m.1 m.2)).ne'
    field_simp

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ EV ψ hψ`. Establish `h : (⨆ a, ⨆ b, ⨆ (_ : a ≠ b), LinearMap.range (homAct EV EV a b)) ≤ LinearMap.ker (LinearMap.trace K V)`. Use `iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, rfl⟩`. Rewrite using `[LinearMap.mem_ker]`.

Use `show LinearMap.trace K V (EV a b * φ - φ * EV a b) = 0`. Rewrite using `[map_sub, LinearMap.trace_mul_comm, sub_self]`. Conclude with `LinearMap.mem_ker.mp (h hψ)`.
-/
theorem hom_trace_holds : HomTrace := by
  intro K V ι _ _ _ _ _ EV ψ hψ
  have h : (⨆ a, ⨆ b, ⨆ (_ : a ≠ b), LinearMap.range (homAct EV EV a b)) ≤
      LinearMap.ker (LinearMap.trace K V) := by
    refine iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_
    rintro _ ⟨φ, rfl⟩
    rw [LinearMap.mem_ker]
    show LinearMap.trace K V (EV a b * φ - φ * EV a b) = 0
    rw [map_sub, LinearMap.trace_mul_comm, sub_self]
  exact LinearMap.mem_ker.mp (h hψ)

end Formalism.InvariantFactorPaths.PW
