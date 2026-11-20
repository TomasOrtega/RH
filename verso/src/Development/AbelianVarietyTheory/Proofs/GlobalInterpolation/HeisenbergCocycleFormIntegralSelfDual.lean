import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.CocInt

variable {X : Fields} (A : Amb X) {a b : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hv_apply {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

/- English proof (translation)
Simplify using `only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _`.
-/
theorem hv_swap {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = (starRingEnd ℂ) (HV sc z w) := by
  simp only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem emb_apply (x : HomE X.E a b) (τ : X.Tau) (i : Fin b) (j : Fin a) :
    emb A x τ i j = A.δ * X.embC A.σ₀ τ (x (Pi.single j 1) i) := rfl

/- English proof (translation)
Rewrite using `[hv_apply, hv_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [emb_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hX.conjE, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hv_smul (hX : X.Ok) (r : X.E) (x y : HomE X.E a b) :
    HV A.sc (emb A (r • x)) (emb A y) = HV A.sc (emb A x) (emb A (star r • y)) := by
  rw [hv_apply, hv_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [emb_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hX.conjE, Complex.conj_conj]
  ring

/- English proof (translation)
The claim follows from `map_add (embH _ _) x y`.
-/
theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add (embH _ _) x y

/- English proof (translation)
Simplify using `only [coc, imH, altE, emb_add, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coc_add_left (x y z : HomE X.E a b) : coc A (x + y) z = coc A x z + coc A y z := by
  simp only [coc, imH, altE, emb_add, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

/- English proof (translation)
Use `coc_add_left A 0 0 z` as an intermediate fact. Rewrite `this` using `[add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coc_zero_left (z : HomE X.E a b) : coc A 0 z = 0 := by
  have := coc_add_left A 0 0 z
  rw [add_zero] at this
  linarith

/- English proof (translation)
Introduce `x y h`. Take `⟨τ⟩ : Nonempty X.Tau` from `Fintype.card_pos_iff.1 hX.f_pos`. Use `LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `congrFun (congrFun (congrFun h τ) i) j` as an intermediate fact.

Rewrite `this` using `[emb_apply, emb_apply]`. Simplify using `using (X.embC A.σ₀ τ).injective (mul_left_cancel₀ hδ this)`.
-/
theorem emb_injective (hX : X.Ok) (hδ : A.δ ≠ 0) : Function.Injective (emb A : HomE X.E a b → _) := by
  intro x y h
  obtain ⟨τ⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  rw [emb_apply, emb_apply] at this
  simpa using (X.embC A.σ₀ τ).injective (mul_left_cancel₀ hδ this)

variable {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

/- English proof (translation)
Assemble the required witnesses or components as `⟨x, hx, rfl⟩`.
-/
theorem emb_mem {x : HomE X.E a b} (hx : x ∈ per A N N') : emb A x ∈ LamC (X.embC A.σ₀) A.δ A.AA N N' :=
  ⟨x, hx, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Establish `h1` using `emb_mem A hx`. Rewrite `h1` using `[← hL.1]`. Conclude with `h1 _ (emb_mem A hy)`.

Introduce `h`. Establish `h1 : emb A x ∈ dualLat (HV A.sc) (LamC (X.embC A.σ₀) A.δ A.AA N N')`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `h y hy`. Rewrite `h1` using `[hL.1]`.

Take `⟨x', hx', e⟩` from `h1`. Rewrite using `[← emb_injective A hX hδ (a₁ := x') e]` and apply the resulting hypothesis.
-/
theorem mem_per_iff (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') (x : HomE X.E a b) :
    x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n := by
  constructor
  · intro hx y hy
    have h1 := emb_mem A hx
    rw [← hL.1] at h1
    exact h1 _ (emb_mem A hy)
  · intro h
    have h1 : emb A x ∈ dualLat (HV A.sc) (LamC (X.embC A.σ₀) A.δ A.AA N N') := by
      rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    rw [hL.1] at h1
    obtain ⟨x', hx', e⟩ := h1
    rwa [← emb_injective A hX hδ (a₁ := x') e]

/- English proof (translation)
Take `⟨m, hm⟩` from `(mem_per_iff A hX hδ hL x).1 hx y hy`. Establish `h` using `hL.2.2 _ (emb_mem A hx) _ (emb_mem A hy)`. Simplify using `only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h`. Rewrite `h` using `[← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]`. Take `⟨n, hn⟩` from `h`.

Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg Complex.im hn`. Establish `h3 : (HV A.sc (emb A y) (emb A x)).re = (HV A.sc (emb A x) (emb A y)).re`. Rewrite using `[hv_swap]`. Simplify using the standard rewrite rules.

Simplify using `only [imH] at hm`. Simplify using `only [map_add, LinearMap.add_apply, Complex.add_re, h3, hm] at h2`. Simplify using `at h2`. Simplify using `only [coc, imH, hm]`. Use `push_cast`.

Apply `mul_left_cancel₀ Real.pi_ne_zero` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coc_int (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') {x y : HomE X.E a b}
    (hx : x ∈ per A N N') (hy : y ∈ per A N N') : ∃ n : ℤ, coc A x y = n := by
  obtain ⟨m, hm⟩ := (mem_per_iff A hX hδ hL x).1 hx y hy
  have h := hL.2.2 _ (emb_mem A hx) _ (emb_mem A hy)
  simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n + m, ?_⟩
  have h2 := congrArg Complex.im hn
  have h3 : (HV A.sc (emb A y) (emb A x)).re = (HV A.sc (emb A x) (emb A y)).re := by
    rw [hv_swap]; simp
  simp only [imH] at hm
  simp only [map_add, LinearMap.add_apply, Complex.add_re, h3, hm] at h2
  simp at h2
  simp only [coc, imH, hm]
  push_cast
  apply mul_left_cancel₀ Real.pi_ne_zero
  linarith

/- English proof (translation)
Introduce `X A a b N N' hX hδ hL`. Establish `h1 : ∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y)`. Introduce `r x y`. Simplify using `only [coc, imH, altE, hv_smul A hX, and_self]`. Use `⟨h1, mem_per_iff A hX hδ hL, fun x y h => ?_⟩` and prove the remaining obligations.

Set `I : Ideal (𝓞 X.E)` to `{ carrier := {r | ∀ s : 𝓞 X.E, ∃ n : ℤ, coc A ((s * r) • x) y = n} zero_mem' := fun s => ⟨0, by simp [coc_zero_left]⟩ add_mem' := fun {r r'} hr hr' s => by`. Take `⟨n, hn⟩` from `hr s`. Take `⟨m, hm⟩` from `hr' s`. Conclude with `⟨n + m, by rw [mul_add, add_smul, coc_add_left, hn, hm, Int.cast_add]⟩`. Use the proof step `smul_mem' := fun c r hr s => by`.

Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hr _ }`. Establish `hI : I = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Set `Q : HeightOneSpectrum (𝓞 X.E)` to `⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField X.E)⟩`. Take `⟨k, hk, hx, hy⟩` from `h Q`. Take `⟨u, hu, hx⟩` from `(mem_locP _ _ _).1 hx`. Take `⟨v, hv, hy⟩` from `(mem_locP _ _ _).1 hy`. Establish `hmem : u * cO X.E v ∈ I`.

Introduce `s`. Take `⟨n, hn⟩` from `coc_int A hX hδ hL (Submodule.smul_mem _ s hx) hy`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn]`. Establish `e1 : (s * (u * cO X.E v)) • x = (star (algebraMap (𝓞 X.E) X.E v) * k) • (s • u • k⁻¹ • x)`.

Rewrite using `[← algebraMap_smul X.E s, ← algebraMap_smul X.E u, ← algebraMap_smul X.E (s * _), smul_smul, smul_smul, smul_smul, map_mul, map_mul, algebraMap_cO]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, (h1 _ _ _).1, star_mul', star_star, mul_smul, algebraMap_smul]`. Break down `hM.isPrime.mem_or_mem (hle hmem) with h' | h'` into its components or cases.

Conclude with `hu h'`. Conclude with `hv h'`. Establish `: (1 : 𝓞 X.E) ∈ I` using `hI ▸ Submodule.mem_top`. Simplify using `using this 1`.
-/
theorem cocycle_integral : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → A.δ ≠ 0 → LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N' → (∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y)) ∧ (∀ x : HomE X.E a b, x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n) ∧ ∀ x y : HomE X.E a b, (∀ Q : HeightOneSpectrum (𝓞 X.E), ∃ k : X.E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal (per A N N') ∧ star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal (per A N N')) → ∃ n : ℤ, coc A x y = n := by
  intro X A a b N N' hX hδ hL
  have h1 : ∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y) := by
    intro r x y
    simp only [coc, imH, altE, hv_smul A hX, and_self]
  refine ⟨h1, mem_per_iff A hX hδ hL, fun x y h => ?_⟩
  let I : Ideal (𝓞 X.E) :=
    { carrier := {r | ∀ s : 𝓞 X.E, ∃ n : ℤ, coc A ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [coc_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, coc_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun c r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 X.E) :=
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField X.E)⟩
    obtain ⟨k, hk, hx, hy⟩ := h Q
    obtain ⟨u, hu, hx⟩ := (mem_locP _ _ _).1 hx
    obtain ⟨v, hv, hy⟩ := (mem_locP _ _ _).1 hy
    have hmem : u * cO X.E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := coc_int A hX hδ hL (Submodule.smul_mem _ s hx) hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * cO X.E v)) • x = (star (algebraMap (𝓞 X.E) X.E v) * k) • (s • u • k⁻¹ • x) := by
        rw [← algebraMap_smul X.E s, ← algebraMap_smul X.E u, ← algebraMap_smul X.E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, algebraMap_cO]
        congr 1
        field_simp
      rw [e1, (h1 _ _ _).1, star_mul', star_star, mul_smul, algebraMap_smul]
    rcases hM.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 X.E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.MomT.CocInt
