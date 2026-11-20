import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRationalStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFactsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFactsStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.UnitTr

/- English proof (translation)
Unfold `TaylorLogMetric.lamC`. Rewrite using `[dif_pos hx, dif_pos hy, dif_pos (mul_mem hx hy), ← map_mul]`. Both sides reduce to the same expression.
-/
theorem lamC_mul_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos hx, dif_pos hy, dif_pos (mul_mem hx hy), ← map_mul]
  rfl

variable {X : Fields} (A : Amb X) {a b : ℕ}

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1`. Proceed by induction on `n with`. Consider the case `zero`. Use `(h 0 0 y).1` as an intermediate fact. Simplify using `only [add_zero] at this`.

Simplify using `only [Nat.cast_zero, zero_smul, zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).1, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coc_nat_left (n : ℕ) (x y : HomE X.E a b) : coc A ((n : X.E) • x) y = n * coc A x y := by
  have h := (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1
  induction n with
  | zero =>
    have := (h 0 0 y).1
    simp only [add_zero] at this
    simp only [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).1, ih]; push_cast; ring

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1`. Proceed by induction on `n with`. Consider the case `zero`. Use `(h x 0 0).2.1` as an intermediate fact. Simplify using `only [add_zero] at this`.

Simplify using `only [Nat.cast_zero, zero_smul, zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).2.1, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coc_nat_right (n : ℕ) (x y : HomE X.E a b) : coc A x ((n : X.E) • y) = n * coc A x y := by
  have h := (GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.1
  induction n with
  | zero =>
    have := (h x 0 0).2.1
    simp only [add_zero] at this
    simp only [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).2.1, ih]; push_cast; ring

/- English proof (translation)
Take `⟨hδ, -, -, -, hFG, hLa⟩` from `hL`. Establish `hfull` using `(GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hA hN hN').2.1`. Establish `hint` using `(GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N' hX hδ (hLa N N' hN hN').2).2.2`. Take `⟨n, hn, hx⟩` from `hfull x`. Take `⟨n', hn', hy⟩` from `hfull y`.

Take `⟨k, hk⟩` from `hint ((n : X.E) • x) ((n' : X.E) • y) fun Q => ⟨1, one_ne_zero, by simpa using le_locP Q _ hx, by simpa using le_locP (conjPrime₂ Q) _ hy⟩`. Rewrite `hk` using `[coc_nat_left, coc_nat_right]`. Use `⟨(k : ℚ) / (n * n'), ?_⟩` and prove the remaining obligations. Establish `h1 : (n : ℝ) ≠ 0` using `by positivity`. Establish `h2 : (n' : ℝ) ≠ 0` using `by positivity`.

Use `push_cast`. Rewrite using `[← hk]`. Clear the denominators using the available nonvanishing facts.
-/
theorem coc_rat (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hX : X.Ok) (hL : A.LaHyp a b ∅)
    (hA : A.AA ≠ ⊥) (hN : IsSdLat N) (hN' : IsSdLat N') (x y : HomE X.E a b) : ∃ r : ℚ, coc A x y = (r : ℝ) := by
  obtain ⟨hδ, -, -, -, hFG, hLa⟩ := hL
  have hfull := (GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hA hN hN').2.1
  have hint := (GlobalTheory.T.heisenbergCocycleForm_integral_selfDual X A a b N N' hX hδ (hLa N N' hN hN').2).2.2
  obtain ⟨n, hn, hx⟩ := hfull x
  obtain ⟨n', hn', hy⟩ := hfull y
  obtain ⟨k, hk⟩ := hint ((n : X.E) • x) ((n' : X.E) • y) fun Q =>
    ⟨1, one_ne_zero, by simpa using le_locP Q _ hx, by simpa using le_locP (conjPrime₂ Q) _ hy⟩
  rw [coc_nat_left, coc_nat_right] at hk
  refine ⟨(k : ℚ) / (n * n'), ?_⟩
  have h1 : (n : ℝ) ≠ 0 := by positivity
  have h2 : (n' : ℝ) ≠ 0 := by positivity
  push_cast
  rw [← hk]
  field_simp

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [Wx, opU]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wx_const_mul (x : HomE X.E a b) (c : ℂ) (F : VCx X.Tau a b → ℂ) :
    Wx A x (fun z => c * F z) = fun z => c * Wx A x F z := by
  funext z
  simp only [Wx, opU]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Conclude with `(hL.2.2.2.2.2 N N' hN hN').1 (emb A l) ⟨l, hl, rfl⟩ z`.
-/
theorem Wx_per (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hL : A.LaHyp a b ∅)
    (hN : IsSdLat N) (hN' : IsSdLat N') (l : HomE X.E a b) (hl : l ∈ per A N N') :
    Wx A l (A.e a b N N') = A.e a b N N' := by
  funext z
  exact (hL.2.2.2.2.2 N N' hN hN').1 (emb A l) ⟨l, hl, rfl⟩ z

/- English proof (translation)
Introduce `X A a b ϖ p N N' _ lam ι un hX hL hA hS hϖ hcop hN hN' hP t n hn ht`. Establish `hp : p.Prime` using `Fact.out`. Establish `hH` using `GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b`. Establish `hroot` using `(GlobalTheory.T.algebraicNumbers_padicPlaces_facts X.K p A.σ₀ ι).2.2 lam`. Establish `hϖE : (ϖ : X.E) * star (ϖ : X.E) = (p : X.E)`.

Use `congrArg (fun z : 𝓞 X.E => (z : X.E)) hϖ` as an intermediate fact. Simplify `this` using `[Fields.conjO, starRingEnd_apply]`. Establish `hϖ0 : (ϖ : X.E) ≠ 0`. Introduce `h`. Rewrite `hϖE` using `[h, zero_mul]`.

Conclude with `hp.ne_zero (by exact_mod_cast hϖE.symm)`. Establish `hbar : ((X.conjO ϖ : 𝓞 X.E) : X.E) = star (ϖ : X.E)`. Simplify using `[Fields.conjO, starRingEnd_apply]`. Establish `hnϖ : IsCoprime (n : 𝓞 X.E) ϖ`. Establish `h1 : IsCoprime (n : 𝓞 X.E) (p : 𝓞 X.E)` using `Nat.Coprime.cast hn`.

Rewrite `h1` using `[← hϖ]`. Conclude with `h1.of_mul_right_left`. Take `⟨α, β, hαβ⟩` from `hnϖ.mul_left hcop.symm`. Establish `hαβE : (α : X.E) * (n * star (ϖ : X.E)) + β * ϖ = 1`. Use `congrArg (fun z : 𝓞 X.E => (z : X.E)) hαβ` as an intermediate fact.

Simplify `this` using `[hbar]`. Establish `hsm : ∀ (r : 𝓞 X.E) (x : HomE X.E a b), x ∈ per A N N' → (r : X.E) • x ∈ per A N N'` using `fun r x hx => Submodule.smul_mem _ r hx`. Use `set t' : HomE X.E a b := ((β : X.E) * ϖ) • t with ht'`. Establish `ht'M : (n : X.E) • t' ∈ per A N N'`. Use `hsm β _ ht` as an intermediate fact.

Rewrite `this` using `[smul_smul]`. Rewrite using `[ht', smul_smul]`. Use `this using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨N₀, hN₀, hJ, hC⟩` from `hP N N' hN hN' t' ⟨n, hn, ht'M⟩`.

Take `⟨α', β', h'⟩ : IsCoprime (N₀ : 𝓞 X.E) (p : 𝓞 X.E)` from `Nat.Coprime.cast hN₀`. Establish `h'E : (α' : X.E) * N₀ + β' * (ϖ * star (ϖ : X.E)) = 1`. Use `congrArg (fun z : 𝓞 X.E => (z : X.E)) h'` as an intermediate fact. Rewrite using `[hϖE]`. Simplify using `using this`.

Use `set m₁ : HomE X.E a b := ((α' * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hm₁`. Use `set l : HomE X.E a b := ((β' * X.conjO ϖ * X.conjO ϖ * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hl`. Establish `hm₁M : m₁ ∈ per A N N'` using `hsm _ _ ht`. Establish `hlM : l ∈ per A N N'` using `hsm _ _ ht`. Use `set y : HomE X.E a b := ((N₀ : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • m₁ with hy`.

Establish `hdec : y + (t' + l) = t`. Rewrite using `[hy, hm₁, hl, ht']`. Simplify using `only [smul_smul, ← add_smul]`. Use `conv_rhs => rw [← one_smul X.E t]`. Use `congr 1`.

Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_mul] at hbar hαβE h'E hϖ0 ⊢`. Rewrite using `[hbar]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(α * n * star (ϖ : X.E)) * h'E + hαβE`. Take `⟨r₁, hr₁⟩` from `coc_rat A N N' hX hL hA hN hN' t' l`.

Take `⟨r₂, hr₂⟩` from `coc_rat A N N' hX hL hA hN hN' y (t' + l)`. Use `set ζ : ℂ := Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ)) with hζ`. Establish `hkey : Wx A t (A.e a b N N') = fun z => ζ * Wx A y (Wx A t' (A.e a b N N')) z`. Establish `e1` using `hH.1 t' l (A.e a b N N')`. Rewrite `e1` using `[Wx_per A N N' hL hN hN' l hlM]`.

Rewrite using `[e1, Wx_const_mul, hH.1 y (t' + l), hdec, hr₁, hr₂]`. Use function extensionality and compare the values at `z`. Rewrite using `[hζ, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]`. Establish `: -(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ) + -(2 * (Real.pi : ℂ)) * Complex.I * ((r₁ : ℝ) : ℂ) + -(2 * (Real.pi : ℂ)) * Complex.I * ((r₂ : ℝ) : ℂ) = 0` using `by push_cast; ring`. Rewrite using `[this, Complex.exp_zero, one_mul]`.

Establish `hjet : ∀ m, jetC A.cD (Wx A t (A.e a b N N')) m = ζ * jetC A.cD (Wx A y (Wx A t' (A.e a b N N'))) m`. Introduce `m`. Use `hH.2.2.2.2.2.2.2 Unit {()} (fun _ => ζ) (fun _ => Wx A y (Wx A t' (A.e a b N N'))) (fun _ _ => hH.2.2.2.2.2.2.1 _ _ (hH.2.2.2.2.2.2.1 _ _ (hS N N' hN hN'))) m` as an intermediate fact. Rewrite using `[hkey]`. Simplify `this` using `only [Finset.sum_singleton]`.

Establish `hζQ` using `hroot (-(r₁ + r₂))`. Use `⟨fun m => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hjet]`. Conclude with `mul_mem hζQ.1 (hJ m₁ hm₁M m)`. Establish `hbrk : ∀ x, ‖TaylorLogMetric.lamC lam (brkE A y x)‖ = 1`.

Introduce `x`. Take `⟨s₁, hs₁⟩` from `coc_rat A N N' hX hL hA hN hN' x y`. Take `⟨s₂, hs₂⟩` from `coc_rat A N N' hX hL hA hN hN' y x`. Use `(hroot (s₁ - s₂)).2` as an intermediate fact. Rewrite using `[hH.2.2.2.2.1, hH.2.2.1, hs₁, hs₂]`.

Rewrite `this` using `[Rat.cast_sub]`. Then use the resulting hypothesis. Use `clo_comb (Sup' := (per A N N' : Set (HomE X.E a b))) (tab' := ptTab ι un) (M' := Set.univ) hC ({()} : Finset Unit) (fun _ _ => TaylorLogMetric.lamC lam ζ) (fun _ m => (m₁, m)) (fun _ _ _ _ => hm₁M) (fun x => TaylorLogMetric.lamC lam ζ * TaylorLogMetric.lamC lam (brkE A y x)) (fun …` as an intermediate fact. Use `clo_congr this subset_rfl subset_rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_singleton]`. Rewrite using `[hjet, lamC_mul_of_mem lam hζQ.1 (hJ m₁ hm₁M m)]`.
-/
theorem moments_unit_translate : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]), X.Ok → A.LaHyp a b ∅ → A.AA ≠ ⊥ → A.ESmooth a b → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → IsSdLat N → IsSdLat N' → PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E)) → ∀ (t : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * (ϖ : X.E)) • t ∈ per A N N' → (∀ m, jetC A.cD (Wx A t (A.e a b N N')) m ∈ TaylorLogMetric.Qbar) ∧ InIntClosure (per A N N' : Set (HomE X.E a b)) (ptTab ι un) Set.univ fun m => TaylorLogMetric.lamC lam (jetC A.cD (Wx A t (A.e a b N N')) m) := by
  intro X A a b ϖ p N N' _ lam ι un hX hL hA hS hϖ hcop hN hN' hP t n hn ht
  have hp : p.Prime := Fact.out
  have hH := GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b
  have hroot := (GlobalTheory.T.algebraicNumbers_padicPlaces_facts X.K p A.σ₀ ι).2.2 lam
  have hϖE : (ϖ : X.E) * star (ϖ : X.E) = (p : X.E) := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) hϖ
    simpa [Fields.conjO, starRingEnd_apply] using this
  have hϖ0 : (ϖ : X.E) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hϖE
    exact hp.ne_zero (by exact_mod_cast hϖE.symm)
  have hbar : ((X.conjO ϖ : 𝓞 X.E) : X.E) = star (ϖ : X.E) := by
    simp [Fields.conjO, starRingEnd_apply]
  have hnϖ : IsCoprime (n : 𝓞 X.E) ϖ := by
    have h1 : IsCoprime (n : 𝓞 X.E) (p : 𝓞 X.E) := Nat.Coprime.cast hn
    rw [← hϖ] at h1
    exact h1.of_mul_right_left
  obtain ⟨α, β, hαβ⟩ := hnϖ.mul_left hcop.symm
  have hαβE : (α : X.E) * (n * star (ϖ : X.E)) + β * ϖ = 1 := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) hαβ
    simpa [hbar] using this
  have hsm : ∀ (r : 𝓞 X.E) (x : HomE X.E a b), x ∈ per A N N' → (r : X.E) • x ∈ per A N N' := fun r x hx =>
    Submodule.smul_mem _ r hx
  set t' : HomE X.E a b := ((β : X.E) * ϖ) • t with ht'
  have ht'M : (n : X.E) • t' ∈ per A N N' := by
    have := hsm β _ ht
    rw [smul_smul] at this
    rw [ht', smul_smul]
    convert this using 2
    ring
  obtain ⟨N₀, hN₀, hJ, hC⟩ := hP N N' hN hN' t' ⟨n, hn, ht'M⟩
  obtain ⟨α', β', h'⟩ : IsCoprime (N₀ : 𝓞 X.E) (p : 𝓞 X.E) := Nat.Coprime.cast hN₀
  have h'E : (α' : X.E) * N₀ + β' * (ϖ * star (ϖ : X.E)) = 1 := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) h'
    rw [hϖE]
    simpa using this
  set m₁ : HomE X.E a b := ((α' * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hm₁
  set l : HomE X.E a b := ((β' * X.conjO ϖ * X.conjO ϖ * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hl
  have hm₁M : m₁ ∈ per A N N' := hsm _ _ ht
  have hlM : l ∈ per A N N' := hsm _ _ ht
  set y : HomE X.E a b := ((N₀ : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • m₁ with hy
  have hdec : y + (t' + l) = t := by
    rw [hy, hm₁, hl, ht']
    simp only [smul_smul, ← add_smul]
    conv_rhs => rw [← one_smul X.E t]
    congr 1
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at hbar hαβE h'E hϖ0 ⊢
    rw [hbar]
    field_simp
    linear_combination (α * n * star (ϖ : X.E)) * h'E + hαβE
  obtain ⟨r₁, hr₁⟩ := coc_rat A N N' hX hL hA hN hN' t' l
  obtain ⟨r₂, hr₂⟩ := coc_rat A N N' hX hL hA hN hN' y (t' + l)
  set ζ : ℂ := Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ)) with hζ
  have hkey : Wx A t (A.e a b N N') = fun z => ζ * Wx A y (Wx A t' (A.e a b N N')) z := by
    have e1 := hH.1 t' l (A.e a b N N')
    rw [Wx_per A N N' hL hN hN' l hlM] at e1
    rw [e1, Wx_const_mul, hH.1 y (t' + l), hdec, hr₁, hr₂]
    funext z
    rw [hζ, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    have : -(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ) + -(2 * (Real.pi : ℂ)) * Complex.I * ((r₁ : ℝ) : ℂ) +
        -(2 * (Real.pi : ℂ)) * Complex.I * ((r₂ : ℝ) : ℂ) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero, one_mul]
  have hjet : ∀ m, jetC A.cD (Wx A t (A.e a b N N')) m = ζ * jetC A.cD (Wx A y (Wx A t' (A.e a b N N'))) m := by
    intro m
    have := hH.2.2.2.2.2.2.2 Unit {()} (fun _ => ζ) (fun _ => Wx A y (Wx A t' (A.e a b N N')))
      (fun _ _ => hH.2.2.2.2.2.2.1 _ _ (hH.2.2.2.2.2.2.1 _ _ (hS N N' hN hN'))) m
    rw [hkey]
    simpa only [Finset.sum_singleton] using this
  have hζQ := hroot (-(r₁ + r₂))
  refine ⟨fun m => ?_, ?_⟩
  · rw [hjet]
    exact mul_mem hζQ.1 (hJ m₁ hm₁M m)
  · have hbrk : ∀ x, ‖TaylorLogMetric.lamC lam (brkE A y x)‖ = 1 := by
      intro x
      obtain ⟨s₁, hs₁⟩ := coc_rat A N N' hX hL hA hN hN' x y
      obtain ⟨s₂, hs₂⟩ := coc_rat A N N' hX hL hA hN hN' y x
      have := (hroot (s₁ - s₂)).2
      rw [hH.2.2.2.2.1, hH.2.2.1, hs₁, hs₂]
      rwa [Rat.cast_sub] at this
    have := clo_comb (Sup' := (per A N N' : Set (HomE X.E a b))) (tab' := ptTab ι un) (M' := Set.univ) hC ({()} : Finset Unit)
      (fun _ _ => TaylorLogMetric.lamC lam ζ) (fun _ m => (m₁, m)) (fun _ _ _ _ => hm₁M)
      (fun x => TaylorLogMetric.lamC lam ζ * TaylorLogMetric.lamC lam (brkE A y x))
      (fun x _ => by rw [norm_mul, hbrk, hζQ.2, one_mul]) (fun _ h h' => absurd h h')
      (fun x _ m _ => by simp only [Finset.sum_singleton]; rw [mul_assoc])
    refine clo_congr this subset_rfl subset_rfl fun m _ => ?_
    simp only [Finset.sum_singleton]
    rw [hjet, lamC_mul_of_mem lam hζQ.1 (hJ m₁ hm₁M m)]

end GlobalTheory.MomT.UnitTr
