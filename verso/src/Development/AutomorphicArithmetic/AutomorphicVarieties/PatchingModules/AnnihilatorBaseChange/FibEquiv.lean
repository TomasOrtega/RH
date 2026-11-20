import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Establish `hI : Ideal.span (Set.range y) ≤ Module.annihilator R X`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Module.mem_annihilator.mpr (hX a)`. Establish `hmap : (Ideal.span (Set.range y)).map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] X)`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `r hr`. Establish `hr'` using `Module.mem_annihilator.mp (hI hr)`. Rewrite using `[Ideal.mem_comap, Module.mem_annihilator]`. Introduce `u`.

Rewrite using `[algebraMap_smul]`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => exact smul_zero r`. Consider the case `tmul a b => rw [← TensorProduct.tmul_smul, hr' b, TensorProduct.tmul_zero]`. Consider the case `add u v hu hv => rw [smul_add, hu, hv, add_zero]`.

Conclude with `Module.mem_annihilator.mp (hmap hk) t`.
-/
private theorem fib_tmul_zero {R σ : Type} [CommRing R] (y : σ → R) (S : Type) [CommRing S] [Algebra R S]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (k : S) (hk : k ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) (t : S ⊗[R] X) : k • t = 0 := by
  have hI : Ideal.span (Set.range y) ≤ Module.annihilator R X := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact Module.mem_annihilator.mpr (hX a)
  have hmap : (Ideal.span (Set.range y)).map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] X) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have hr' := Module.mem_annihilator.mp (hI hr)
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro u
    rw [algebraMap_smul]
    induction u using TensorProduct.induction_on with
    | zero => exact smul_zero r
    | tmul a b => rw [← TensorProduct.tmul_smul, hr' b, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  exact Module.mem_annihilator.mp (hmap hk) t

/- English proof (translation)
Use `fib_tmul_zero y S X hX k hk (1 ⊗ₜ[R] x)` as an intermediate fact. Rewrite `this` using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Then use the resulting hypothesis.
-/
private theorem fib_tmul_zero' {R σ : Type} [CommRing R] (y : σ → R) (S : Type) [CommRing S] [Algebra R S]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (k : S) (hk : k ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) (x : X) : k ⊗ₜ[R] x = 0 := by
  have := fib_tmul_zero y S X hX k hk (1 ⊗ₜ[R] x)
  rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this

/- English proof (translation)
Use `set IB := (Ideal.span (Set.range y)).map (algebraMap R BB) with hIB`. Use `choose sel hsel using hD`. Establish `hz : ∀ (s1 s2 : S) (x : X), algebraMap S BB s1 - algebraMap S BB s2 ∈ IB → s1 ⊗ₜ[R] x = s2 ⊗ₜ[R] x`. Introduce `s1 s2 x h12`. Establish `h0` using `fib_tmul_zero' y S X hX (s1 - s2) (hS _ (by rwa [map_sub])) x`.

Rewrite `h0` using `[TensorProduct.sub_tmul, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hrt : ∀ (s : S) (x : X), LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x` using `fun s x => rfl`. Set `F : BB →ₗ[R] X →ₗ[R] S ⊗[R] X` to `LinearMap.mk₂ R (fun b x => sel b ⊗ₜ[R] x) (fun b1 b2 x => by`. Rewrite using `[← TensorProduct.add_tmul]`. Apply `hz` to reduce the goal to its premises.

Establish `e : algebraMap S BB (sel (b1 + b2)) - algebraMap S BB (sel b1 + sel b2) = (b1 - algebraMap S BB (sel b1)) + (b2 - algebraMap S BB (sel b2)) - (b1 + b2 - algebraMap S BB (sel (b1 + b2)))`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `sub_mem (add_mem (hsel b1) (hsel b2)) (hsel _))`.

Use the proof step `(fun r b x => by`. Rewrite using `[TensorProduct.smul_tmul']`. Apply `hz` to reduce the goal to its premises. Establish `e : algebraMap S BB (sel (r • b)) - algebraMap S BB (r • sel b) = algebraMap R BB r * (b - algebraMap S BB (sel b)) - (r • b - algebraMap S BB (sel (r • b)))`. Rewrite using `[Algebra.smul_def r (sel b), map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def r b]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `sub_mem (Ideal.mul_mem_left _ _ (hsel b)) (hsel _))`. Use the proof step `(fun b x1 x2 => TensorProduct.tmul_add _ _ _)`. Use the proof step `(fun r b x => TensorProduct.tmul_smul _ _ _)`.

Set `g` to `TensorProduct.lift F`. Establish `hg : ∀ (b : BB) (x : X), g (b ⊗ₜ[R] x) = sel b ⊗ₜ[R] x` using `fun b x => by`. Simplify using `[g, F]`. Prove the components needed by the constructor for the conclusion. Apply `Function.LeftInverse.injective (g := g)` to reduce the goal to its premises.

Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s x`. Rewrite using `[hrt, hg]`.

Apply `hz` to reduce the goal to its premises. Establish `e : algebraMap S BB (sel (algebraMap S BB s)) - algebraMap S BB s = -(algebraMap S BB s - algebraMap S BB (sel (algebraMap S BB s)))` using `by ring`. Rewrite using `[e]`. Conclude with `neg_mem (hsel _)`. Consider the case `add u v hu hv => rw [map_add, map_add, hu, hv]`.

Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul b x`. Use `⟨sel b ⊗ₜ[R] x, ?_⟩` and prove the remaining obligations.

Rewrite using `[hrt]`. Establish `h0` using `fib_tmul_zero' y BB X hX (b - algebraMap S BB (sel b)) (hsel b) x`. Rewrite `h0` using `[TensorProduct.sub_tmul, sub_eq_zero, eq_comm]`. Then use the resulting hypothesis. Consider the case `add u v hu hv`. Take `⟨a, ha⟩` from `hu`.

Take `⟨c, hc⟩` from `hv`. Conclude with `⟨a + c, by rw [map_add, ha, hc]⟩`.
-/
private theorem fib_bij {R σ : Type} [CommRing R] (y : σ → R) (S BB : Type) [CommRing S] [Algebra R S]
    [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (hD : ∀ b : BB, ∃ s : S, b - algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB))
    (hS : ∀ s : S, algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB) →
      s ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) :
    Function.Bijective (LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap) := by
  classical
  set IB := (Ideal.span (Set.range y)).map (algebraMap R BB) with hIB
  choose sel hsel using hD
  have hz : ∀ (s1 s2 : S) (x : X), algebraMap S BB s1 - algebraMap S BB s2 ∈ IB →
      s1 ⊗ₜ[R] x = s2 ⊗ₜ[R] x := by
    intro s1 s2 x h12
    have h0 := fib_tmul_zero' y S X hX (s1 - s2) (hS _ (by rwa [map_sub])) x
    rwa [TensorProduct.sub_tmul, sub_eq_zero] at h0
  have hrt : ∀ (s : S) (x : X), LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x := fun s x => rfl
  let F : BB →ₗ[R] X →ₗ[R] S ⊗[R] X := LinearMap.mk₂ R (fun b x => sel b ⊗ₜ[R] x)
    (fun b1 b2 x => by
      rw [← TensorProduct.add_tmul]
      apply hz
      have e : algebraMap S BB (sel (b1 + b2)) - algebraMap S BB (sel b1 + sel b2) = (b1 - algebraMap S BB (sel b1)) + (b2 - algebraMap S BB (sel b2)) - (b1 + b2 - algebraMap S BB (sel (b1 + b2))) := by
        rw [map_add]
        ring
      rw [e]
      exact sub_mem (add_mem (hsel b1) (hsel b2)) (hsel _))
    (fun r b x => by
      rw [TensorProduct.smul_tmul']
      apply hz
      have e : algebraMap S BB (sel (r • b)) - algebraMap S BB (r • sel b) = algebraMap R BB r * (b - algebraMap S BB (sel b)) - (r • b - algebraMap S BB (sel (r • b))) := by
        rw [Algebra.smul_def r (sel b), map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def r b]
        ring
      rw [e]
      exact sub_mem (Ideal.mul_mem_left _ _ (hsel b)) (hsel _))
    (fun b x1 x2 => TensorProduct.tmul_add _ _ _)
    (fun r b x => TensorProduct.tmul_smul _ _ _)
  let g := TensorProduct.lift F
  have hg : ∀ (b : BB) (x : X), g (b ⊗ₜ[R] x) = sel b ⊗ₜ[R] x := fun b x => by
    simp [g, F]
  constructor
  · apply Function.LeftInverse.injective (g := g)
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      rw [hrt, hg]
      apply hz
      have e : algebraMap S BB (sel (algebraMap S BB s)) - algebraMap S BB s = -(algebraMap S BB s - algebraMap S BB (sel (algebraMap S BB s))) := by ring
      rw [e]
      exact neg_mem (hsel _)
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul b x =>
      refine ⟨sel b ⊗ₜ[R] x, ?_⟩
      rw [hrt]
      have h0 := fib_tmul_zero' y BB X hX (b - algebraMap S BB (sel b)) (hsel b) x
      rwa [TensorProduct.sub_tmul, sub_eq_zero, eq_comm] at h0
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨c, hc⟩ := hv
      exact ⟨a + c, by rw [map_add, ha, hc]⟩

/- English proof (translation)
Take `⟨k, r, hkr⟩` from `h.dense 1 b`. Rewrite `hkr` using `[pow_one]`. Use `set v := algebraMap S BB (IsLocalization.Away.invSelf (S := S) f) with hv`. Establish `hvf : v * algebraMap R BB f = 1`. Rewrite using `[hv, IsScalarTower.algebraMap_apply R S BB f, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]`.

Use `⟨algebraMap R S r * (IsLocalization.Away.invSelf (S := S) f) ^ k, ?_⟩` and prove the remaining obligations. Establish `: b - algebraMap S BB (algebraMap R S r * IsLocalization.Away.invSelf (S` using `S) f ^ k) = v ^ k * (algebraMap R BB f ^ k * b - algebraMap R BB r) := by`. Rewrite using `[map_mul, map_pow, ← hv, ← IsScalarTower.algebraMap_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_left _ _ hkr`.
-/
private theorem fib_dense {R σ : Type} [CommRing R] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S]
    [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (h : IsYCpl y f BB) (b : BB) :
    ∃ s : S, b - algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB) := by
  obtain ⟨k, r, hkr⟩ := h.dense 1 b
  rw [pow_one] at hkr
  set v := algebraMap S BB (IsLocalization.Away.invSelf (S := S) f) with hv
  have hvf : v * algebraMap R BB f = 1 := by
    rw [hv, IsScalarTower.algebraMap_apply R S BB f, ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one]
  refine ⟨algebraMap R S r * (IsLocalization.Away.invSelf (S := S) f) ^ k, ?_⟩
  have : b - algebraMap S BB (algebraMap R S r * IsLocalization.Away.invSelf (S := S) f ^ k) = v ^ k * (algebraMap R BB f ^ k * b - algebraMap R BB r) := by
    rw [map_mul, map_pow, ← hv, ← IsScalarTower.algebraMap_apply]
    calc b - algebraMap R BB r * v ^ k = (v * algebraMap R BB f) ^ k * b - algebraMap R BB r * v ^ k := by rw [hvf, one_pow, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ hkr

/- English proof (translation)
Take `⟨⟨r, m⟩, hrm⟩` from `IsLocalization.surj (Submonoid.powers f) s`. Take `⟨k, hk⟩` from `m.2`. Simplify using `only at hrm`. Rewrite `hrm` using `[← hk]`. Establish `hB : algebraMap R BB r ∈ (Ideal.span (Set.range y) ^ 1).map (algebraMap R BB)`.

Rewrite using `[pow_one, IsScalarTower.algebraMap_apply R S BB r, ← hrm, map_mul]`. Conclude with `Ideal.mul_mem_right _ _ hs`. Take `⟨k', hk'⟩` from `h.strict 1 r hB`. Rewrite `hk'` using `[pow_one]`. Establish `hmem : s * algebraMap R S (f ^ (k' + k)) ∈ (Ideal.span (Set.range y)).map (algebraMap R S)`.

Rewrite using `[pow_add, map_mul, mul_comm (algebraMap R S (f ^ k')), ← mul_assoc, hrm, ← map_mul, mul_comm]`. Conclude with `Ideal.mem_map_of_mem _ hk'`. Establish `hu : IsUnit (algebraMap R S (f ^ (k' + k)))`. Rewrite using `[map_pow]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit f).pow _`.

Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `: s = s * algebraMap R S (f ^ (k' + k)) * w` using `by rw [mul_assoc, hw, mul_one]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ hmem`.
-/
private theorem fib_strict {R σ : Type} [CommRing R] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S]
    [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (h : IsYCpl y f BB) (s : S) (hs : algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB)) :
    s ∈ (Ideal.span (Set.range y)).map (algebraMap R S) := by
  obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers f) s
  obtain ⟨k, hk⟩ := m.2
  simp only at hrm
  rw [← hk] at hrm
  have hB : algebraMap R BB r ∈ (Ideal.span (Set.range y) ^ 1).map (algebraMap R BB) := by
    rw [pow_one, IsScalarTower.algebraMap_apply R S BB r, ← hrm, map_mul]
    exact Ideal.mul_mem_right _ _ hs
  obtain ⟨k', hk'⟩ := h.strict 1 r hB
  rw [pow_one] at hk'
  have hmem : s * algebraMap R S (f ^ (k' + k)) ∈ (Ideal.span (Set.range y)).map (algebraMap R S) := by
    rw [pow_add, map_mul, mul_comm (algebraMap R S (f ^ k')), ← mul_assoc, hrm, ← map_mul, mul_comm]
    exact Ideal.mem_map_of_mem _ hk'
  have hu : IsUnit (algebraMap R S (f ^ (k' + k))) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit f).pow _
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have : s = s * algebraMap R S (f ^ (k' + k)) * w := by rw [mul_assoc, hw, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hmem

/- English proof (translation)
Introduce `R σ _ _ y f S BB _ _ _ _ _ _ _ X _ _ MM _ _ _ _ q hC hX hq hker`. Establish `hbij` using `fib_bij y S BB X hX (fun b => fib_dense y f S BB hC b) (fun s hs => fib_strict y f S BB hC s hs)`. Use `set rT := LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap with hrTdef`. Establish `hrt : ∀ (s : S) (x : X), rT (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x` using `fun s x => rfl`. Establish `hrtS : ∀ (s : S) (t : S ⊗[R] X), rT (s • t) = algebraMap S BB s • rT t`.

Introduce `s t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [smul_zero, map_zero, smul_zero]`. Consider the case `tmul s' x`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, hrt, hrt, TensorProduct.smul_tmul', smul_eq_mul, map_mul]`.

Consider the case `add u v hu hv => rw [smul_add, map_add, map_add, hu, hv, smul_add]`. Establish `hJ : Ideal.span (Set.range fun a => algebraMap R BB (y a)) = (Ideal.span (Set.range y)).map (algebraMap R BB)`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hL : ∀ i ∈ (Ideal.span (Set.range y)).map (algebraMap R BB), ∀ m : MM, q (i • m) = 0`.

Introduce `i hi`. Use `Submodule.span_induction ?_ ?_ ?_ ?_ hi` and prove the remaining obligations. Introduce and unpack `_ ⟨r, hr, rfl⟩ m`. Rewrite using `[IsScalarTower.algebraMap_apply R S BB, algebraMap_smul, ← LinearMap.mem_ker, hker]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial`.

Introduce `m`. Rewrite using `[zero_smul, map_zero]`. Introduce `a c _ _ ha hc m`. Rewrite using `[add_smul, map_add, ha, hc, add_zero]`. Introduce `a c _ hc m`.

Rewrite using `[smul_eq_mul, mul_comm, mul_smul, hc]`. Set `φ : MM →ₗ[BB] BB ⊗[R] X` to `{ toFun := fun m => rT (q m) map_add' := fun a c => by rw [map_add, map_add] map_smul' := fun b m => by`. Take `⟨s, hs⟩` from `fib_dense y f S BB hC b`. Establish `e : b • m = s • m + (b - algebraMap S BB s) • m`. Rewrite using `[← algebraMap_smul BB s m, ← add_smul, add_sub_cancel]`.

Use `show rT (q (b • m)) = b • rT (q m)`. Rewrite using `[e, map_add, map_smul, hL _ hs m, add_zero, hrtS]`. Use `conv_rhs => rw [show b = algebraMap S BB s + (b - algebraMap S BB s) by ring, add_smul, fib_tmul_zero y BB X hX _ hs, add_zero] }`. Establish `hφ : Function.Surjective φ`. Introduce `t`.

Take `⟨u, hu⟩` from `hbij.2 t`. Take `⟨m, hm⟩` from `hq u`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use `show rT (q m) = t`. Rewrite using `[hm, hu]`.

Establish `hK : LinearMap.ker φ = (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `m hm`. Establish `h0 : q m = 0` using `hbij.1 ((LinearMap.mem_ker.mp hm).trans (map_zero rT).symm)`. Rewrite `h0` using `[← LinearMap.mem_ker, hker]`.

Establish `hle : ((Ideal.span (Set.range y)).map (algebraMap R S) • ⊤ : Submodule S MM) ≤ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM).restrictScalars S`. Rewrite using `[Submodule.smul_le]`. Introduce `s hs n _`. Rewrite using `[Submodule.restrictScalars_mem, ← algebraMap_smul BB s n]`. Use `Submodule.smul_mem_smul ?_ trivial` and prove the remaining obligations.

Rewrite using `[hJ, IsScalarTower.algebraMap_eq R S BB, ← Ideal.map_map]`. Conclude with `Ideal.mem_map_of_mem _ hs`. Conclude with `hle h0`. Rewrite using `[Submodule.smul_le]`. Introduce `i hi m _`.

Rewrite using `[LinearMap.mem_ker]`. Use `show rT (q (i • m)) = 0`. Rewrite `hi` using `[hJ]`. Rewrite using `[hL i hi m, map_zero]`. Conclude with `⟨(Submodule.quotEquivOfEq _ _ hK.symm).trans (φ.quotKerEquivOfSurjective hφ)⟩`.
-/
theorem UpperTheory.V.Pa.Core.fibEquiv :
    ∀ (R σ : Type) [CommRing R] [Fintype σ] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S] [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB] (X : Type) [AddCommGroup X] [Module R X] (MM : Type) [AddCommGroup MM] [Module S MM] [Module BB MM] [IsScalarTower S BB MM] (q : MM →ₗ[S] S ⊗[R] X), IsYCpl y f BB → (∀ a (x : X), y a • x = 0) → Function.Surjective q → LinearMap.ker q = (Ideal.span (Set.range y)).map (algebraMap R S) • ⊤ → Nonempty ((MM ⧸ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM)) ≃ₗ[BB] BB ⊗[R] X) := by
  intro R σ _ _ y f S BB _ _ _ _ _ _ _ X _ _ MM _ _ _ _ q hC hX hq hker
  have hbij := fib_bij y S BB X hX (fun b => fib_dense y f S BB hC b)
    (fun s hs => fib_strict y f S BB hC s hs)
  set rT := LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap with hrTdef
  have hrt : ∀ (s : S) (x : X), rT (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x := fun s x => rfl
  have hrtS : ∀ (s : S) (t : S ⊗[R] X), rT (s • t) = algebraMap S BB s • rT t := by
    intro s t
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul s' x =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hrt, hrt, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add u v hu hv => rw [smul_add, map_add, map_add, hu, hv, smul_add]
  have hJ : Ideal.span (Set.range fun a => algebraMap R BB (y a)) = (Ideal.span (Set.range y)).map (algebraMap R BB) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hL : ∀ i ∈ (Ideal.span (Set.range y)).map (algebraMap R BB), ∀ m : MM, q (i • m) = 0 := by
    intro i hi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hi
    · rintro _ ⟨r, hr, rfl⟩ m
      rw [IsScalarTower.algebraMap_apply R S BB, algebraMap_smul, ← LinearMap.mem_ker, hker]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
    · intro m
      rw [zero_smul, map_zero]
    · intro a c _ _ ha hc m
      rw [add_smul, map_add, ha, hc, add_zero]
    · intro a c _ hc m
      rw [smul_eq_mul, mul_comm, mul_smul, hc]
  let φ : MM →ₗ[BB] BB ⊗[R] X :=
    { toFun := fun m => rT (q m)
      map_add' := fun a c => by rw [map_add, map_add]
      map_smul' := fun b m => by
        obtain ⟨s, hs⟩ := fib_dense y f S BB hC b
        have e : b • m = s • m + (b - algebraMap S BB s) • m := by
          rw [← algebraMap_smul BB s m, ← add_smul, add_sub_cancel]
        show rT (q (b • m)) = b • rT (q m)
        rw [e, map_add, map_smul, hL _ hs m, add_zero, hrtS]
        conv_rhs => rw [show b = algebraMap S BB s + (b - algebraMap S BB s) by ring, add_smul, fib_tmul_zero y BB X hX _ hs, add_zero] }
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨u, hu⟩ := hbij.2 t
    obtain ⟨m, hm⟩ := hq u
    refine ⟨m, ?_⟩
    show rT (q m) = t
    rw [hm, hu]
  have hK : LinearMap.ker φ = (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM) := by
    apply le_antisymm
    · intro m hm
      have h0 : q m = 0 := hbij.1 ((LinearMap.mem_ker.mp hm).trans (map_zero rT).symm)
      rw [← LinearMap.mem_ker, hker] at h0
      have hle : ((Ideal.span (Set.range y)).map (algebraMap R S) • ⊤ : Submodule S MM) ≤ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM).restrictScalars S := by
        rw [Submodule.smul_le]
        intro s hs n _
        rw [Submodule.restrictScalars_mem, ← algebraMap_smul BB s n]
        refine Submodule.smul_mem_smul ?_ trivial
        rw [hJ, IsScalarTower.algebraMap_eq R S BB, ← Ideal.map_map]
        exact Ideal.mem_map_of_mem _ hs
      exact hle h0
    · rw [Submodule.smul_le]
      intro i hi m _
      rw [LinearMap.mem_ker]
      show rT (q (i • m)) = 0
      rw [hJ] at hi
      rw [hL i hi m, map_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hK.symm).trans (φ.quotKerEquivOfSurjective hφ)⟩
