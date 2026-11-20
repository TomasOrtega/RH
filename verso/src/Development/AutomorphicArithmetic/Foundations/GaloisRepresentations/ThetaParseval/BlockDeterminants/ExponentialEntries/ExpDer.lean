import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

open GlobalTheory.RealLift

noncomputable section

namespace UpperTheory.TP.RP.Der

variable {R : Type} [CommRing R] [Algebra ℂ R]

/- English proof (translation)
Establish `na` using `ha.summable.norm`. Establish `nb` using `hb.summable.norm`. Establish `e` using `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm na nb`. Rewrite `e` using `[ha.tsum_eq, hb.tsum_eq]`. Rewrite using `[e]`.

Conclude with `(summable_norm_sum_mul_antidiagonal_of_summable_norm na nb).of_norm.hasSum`.
-/
theorem hasSum_cauchy {a b : ℕ → ℂ} {A B : ℂ} (ha : HasSum a A) (hb : HasSum b B) :
    HasSum (fun k => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a p.1 * b p.2) (A * B) := by
  have na := ha.summable.norm
  have nb := hb.summable.norm
  have e := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm na nb
  rw [ha.tsum_eq, hb.tsum_eq] at e
  rw [e]
  exact (summable_norm_sum_mul_antidiagonal_of_summable_norm na nb).of_norm.hasSum

/- English proof (translation)
Establish `h` using `Nat.add_choose_mul_factorial_mul_factorial i j`. Rewrite `h` using `[← Nat.choose_symm_add]`. Establish `h' : ((i + j).choose i : ℂ) * i.factorial * j.factorial = (i + j).factorial` using `by exact_mod_cast h`. Establish `a : (i.factorial : ℂ) ≠ 0` using `by exact_mod_cast i.factorial_ne_zero`. Establish `b : (j.factorial : ℂ) ≠ 0` using `by exact_mod_cast j.factorial_ne_zero`.

Establish `f : ((i + j).factorial : ℂ) ≠ 0` using `by exact_mod_cast (i + j).factorial_ne_zero`. Rewrite using `[inv_mul_eq_div, div_eq_iff f, ← h']`. Clear the denominators using the available nonvanishing facts.
-/
theorem fact_choose {i j : ℕ} :
    (((i + j).factorial : ℂ))⁻¹ * ((i + j).choose i : ℂ) = ((i.factorial : ℂ))⁻¹ * ((j.factorial : ℂ))⁻¹ := by
  have h := Nat.add_choose_mul_factorial_mul_factorial i j
  rw [← Nat.choose_symm_add] at h
  have h' : ((i + j).choose i : ℂ) * i.factorial * j.factorial = (i + j).factorial := by exact_mod_cast h
  have a : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have b : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have f : ((i + j).factorial : ℂ) ≠ 0 := by exact_mod_cast (i + j).factorial_ne_zero
  rw [inv_mul_eq_div, div_eq_iff f, ← h']
  field_simp

/- English proof (translation)
Establish `st : ∀ (i : ℕ) (x : R), D ((D.toLinearMap ^ i) x) = (D.toLinearMap ^ (i + 1)) x` using `fun i x => by`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Both sides reduce to the same expression. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, Finset.sum_antidiagonal_choose_succ_mul (fun i j => (D.toLinearMap ^ i) P * (D.toLinearMap ^ j) Q) k, map_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hc : k.choose p.2 = k.choose p.1` using `(Nat.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.1 hp).symm).symm`. Rewrite using `[hc, ← nsmul_eq_mul, map_nsmul, ← mul_add, ← nsmul_eq_mul]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `D _ = _`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, st, st, mul_comm ((D.toLinearMap ^ p.2) Q)]`.
-/
theorem der_pow_mul (D : Derivation ℂ R R) (k : ℕ) (P Q : R) :
    (D.toLinearMap ^ k) (P * Q) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      (k.choose p.1 : R) * ((D.toLinearMap ^ p.1) P * (D.toLinearMap ^ p.2) Q) := by
  have st : ∀ (i : ℕ) (x : R), D ((D.toLinearMap ^ i) x) = (D.toLinearMap ^ (i + 1)) x := fun i x => by
    rw [pow_succ', Module.End.mul_apply]; rfl
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih,
      Finset.sum_antidiagonal_choose_succ_mul (fun i j => (D.toLinearMap ^ i) P * (D.toLinearMap ^ j) Q) k,
      map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hc : k.choose p.2 = k.choose p.1 :=
      (Nat.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.1 hp).symm).symm
    rw [hc, ← nsmul_eq_mul, map_nsmul, ← mul_add, ← nsmul_eq_mul]
    congr 1
    change D _ = _
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, st, st, mul_comm ((D.toLinearMap ^ p.2) Q)]

def Good (D : Derivation ℂ R R) (P u : R) : Prop :=
  (∃ N : Submodule ℂ R, FiniteDimensional ℂ N ∧ P ∈ N ∧ ∀ y ∈ N, D y ∈ N) ∧
    ∀ l : R →ₗ[ℂ] ℂ, HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) P)) (l u)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using hP`. Consider the case `succ n ih => rw [pow_succ', Module.End.mul_apply]`. Conclude with `hN _ ih`.
-/
theorem pow_mem {D : Derivation ℂ R R} {P : R} {N : Submodule ℂ R} (hP : P ∈ N) (hN : ∀ y ∈ N, D y ∈ N) (n : ℕ) :
    (D.toLinearMap ^ n) P ∈ N := by
  induction n with
  | zero => simpa using hP
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih

/- English proof (translation)
Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `l'`. Establish `a` using `h (l' ∘ₗ N.mkQ)`. Establish `e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (l' ∘ₗ N.mkQ) ((D.toLinearMap ^ n) P)) = fun _ => 0`. Use function extensionality and compare the values at `n`.

Simplify using `[(Submodule.Quotient.mk_eq_zero N).2 (pow_mem hP hN n)]`. Rewrite `a` using `[e]`. Conclude with `a.unique hasSum_zero`.
-/
theorem mem_of_sum {D : Derivation ℂ R R} {P u : R}
    (h : ∀ l : R →ₗ[ℂ] ℂ, HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) P)) (l u))
    {N : Submodule ℂ R} (hP : P ∈ N) (hN : ∀ y ∈ N, D y ∈ N) : u ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l'
  have a := h (l' ∘ₗ N.mkQ)
  have e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (l' ∘ₗ N.mkQ) ((D.toLinearMap ^ n) P)) = fun _ => 0 := by
    funext n
    simp [(Submodule.Quotient.mk_eq_zero N).2 (pow_mem hP hN n)]
  rw [e] at a
  exact a.unique hasSum_zero

/- English proof (translation)
Take `⟨⟨N₁, f₁, m₁, s₁⟩, h₁⟩` from `hP`. Take `⟨⟨N₂, f₂, m₂, s₂⟩, h₂⟩` from `hQ`. Use `⟨⟨N₁ ⊔ N₂, inferInstance, add_mem (Submodule.mem_sup_left m₁) (Submodule.mem_sup_right m₂), ?_⟩, fun l => ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hy`.

Rewrite using `[map_add]`. Conclude with `add_mem (Submodule.mem_sup_left (s₁ a ha)) (Submodule.mem_sup_right (s₂ b hb))`. Simplify `(h₁ l).add (h₂ l)` using `[mul_add]`.
-/
theorem Good.add {D : Derivation ℂ R R} {P Q u v : R} (hP : Good D P u) (hQ : Good D Q v) : Good D (P + Q) (u + v) := by
  obtain ⟨⟨N₁, f₁, m₁, s₁⟩, h₁⟩ := hP
  obtain ⟨⟨N₂, f₂, m₂, s₂⟩, h₂⟩ := hQ
  refine ⟨⟨N₁ ⊔ N₂, inferInstance, add_mem (Submodule.mem_sup_left m₁) (Submodule.mem_sup_right m₂), ?_⟩, fun l => ?_⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (s₁ a ha)) (Submodule.mem_sup_right (s₂ b hb))
  · simpa [mul_add] using (h₁ l).add (h₂ l)

/- English proof (translation)
Establish `hz : ∀ n : ℕ, n ≠ 0 → (D.toLinearMap ^ n) (algebraMap ℂ R a) = 0` using `fun n hn => by`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Establish `: D.toLinearMap (algebraMap ℂ R a) = 0` using `D.map_algebraMap a`. Rewrite using `[this, map_zero]`.

Use `⟨⟨Submodule.span ℂ {algebraMap ℂ R a}, inferInstance, Submodule.mem_span_singleton_self _, ?_⟩, fun l => ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Simplify using the standard rewrite rules. Use `hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) (algebraMap ℂ R a))) 0 (fun n hn => by simp [hz n hn]) using 1` and compare the differences between its conclusion and the goal.

Simplify using the standard rewrite rules.
-/
theorem Good.const (D : Derivation ℂ R R) (a : ℂ) : Good D (algebraMap ℂ R a) (algebraMap ℂ R a) := by
  have hz : ∀ n : ℕ, n ≠ 0 → (D.toLinearMap ^ n) (algebraMap ℂ R a) = 0 := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [pow_succ, Module.End.mul_apply]
    have : D.toLinearMap (algebraMap ℂ R a) = 0 := D.map_algebraMap a
    rw [this, map_zero]
  refine ⟨⟨Submodule.span ℂ {algebraMap ℂ R a}, inferInstance, Submodule.mem_span_singleton_self _, ?_⟩, fun l => ?_⟩
  · intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp
  · convert hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) (algebraMap ℂ R a))) 0
      (fun n hn => by simp [hz n hn]) using 1
    simp

/- English proof (translation)
Take `⟨⟨N₁, f₁, m₁, s₁⟩, h₁⟩` from `hP`. Take `⟨⟨N₂, f₂, m₂, s₂⟩, h₂⟩` from `hQ`. Use `⟨⟨N₁ * N₂, ?_, Submodule.mul_mem_mul m₁ m₂, ?_⟩, fun l => ?_⟩` and prove the remaining obligations. Conclude with `Module.Finite.iff_fg.2 (Submodule.FG.mul (Module.Finite.iff_fg.1 f₁) (Module.Finite.iff_fg.1 f₂))`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.mul_induction_on' with`. Consider the case `mem_mul_mem a ha b hb`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b]`. Conclude with `add_mem (Submodule.mul_mem_mul ha (s₂ b hb)) (Submodule.mul_mem_mul (s₁ a ha) hb)`. Consider the case `add x _ y _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Establish `hv : v ∈ N₂` using `mem_of_sum h₂ m₂ s₂`. Take `⟨π, hπ⟩` from `LinearMap.exists_leftInverse_of_injective N₂.subtype (Submodule.ker_subtype N₂)`. Set `b` to `Module.finBasis ℂ N₂`. Establish `dec : ∀ y (hy : y ∈ N₂), y = ∑ i, (b.coord i (π y)) • (b i : R)` using `fun y hy => by`.

Establish `e : π y = ⟨y, hy⟩` using `LinearMap.congr_fun hπ ⟨y, hy⟩`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Submodule.coe_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by simp [Module.Basis.coord_apply]`.

Establish `key : ∀ (a y : R), y ∈ N₂ → l (a * y) = ∑ i, l (a * b i) * b.coord i (π y)` using `fun a y hy => by conv_lhs => rw [dec y hy]`. Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_smul, smul_eq_mul, mul_comm]`. Establish `S` using `fun i => hasSum_cauchy (h₁ (l ∘ₗ LinearMap.mulRight ℂ (b i : R))) (h₂ (b.coord i ∘ₗ π))`.

Establish `T` using `hasSum_sum (s := Finset.univ) (fun i _ => S i)`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulRight_apply] at T`. Rewrite using `[key u v hv]`. Use `T using 2 with k` and compare the differences between its conclusion and the goal. Rewrite using `[der_pow_mul, map_sum, Finset.mul_sum, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Take `rfl : p.1 + p.2 = k` from `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`. Rewrite using `[← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, key _ _ (pow_mem m₂ s₂ _), ← mul_assoc, fact_choose, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Good.mul {D : Derivation ℂ R R} {P Q u v : R} (hP : Good D P u) (hQ : Good D Q v) : Good D (P * Q) (u * v) := by
  obtain ⟨⟨N₁, f₁, m₁, s₁⟩, h₁⟩ := hP
  obtain ⟨⟨N₂, f₂, m₂, s₂⟩, h₂⟩ := hQ
  refine ⟨⟨N₁ * N₂, ?_, Submodule.mul_mem_mul m₁ m₂, ?_⟩, fun l => ?_⟩
  · exact Module.Finite.iff_fg.2 (Submodule.FG.mul (Module.Finite.iff_fg.1 f₁) (Module.Finite.iff_fg.1 f₂))
  · intro y hy
    induction hy using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b]
      exact add_mem (Submodule.mul_mem_mul ha (s₂ b hb)) (Submodule.mul_mem_mul (s₁ a ha) hb)
    | add x _ y _ hx hy => rw [map_add]; exact add_mem hx hy
  · have hv : v ∈ N₂ := mem_of_sum h₂ m₂ s₂
    obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective N₂.subtype (Submodule.ker_subtype N₂)
    let b := Module.finBasis ℂ N₂
    have dec : ∀ y (hy : y ∈ N₂), y = ∑ i, (b.coord i (π y)) • (b i : R) := fun y hy => by
      have e : π y = ⟨y, hy⟩ := LinearMap.congr_fun hπ ⟨y, hy⟩
      rw [e]
      calc y = ((⟨y, hy⟩ : N₂) : R) := rfl
        _ = ((∑ i, b.repr ⟨y, hy⟩ i • b i : N₂) : R) := by rw [b.sum_repr]
        _ = _ := by
          rw [Submodule.coe_sum]
          exact Finset.sum_congr rfl fun i _ => by simp [Module.Basis.coord_apply]
    have key : ∀ (a y : R), y ∈ N₂ → l (a * y) = ∑ i, l (a * b i) * b.coord i (π y) := fun a y hy => by
      conv_lhs => rw [dec y hy]
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
    have S := fun i => hasSum_cauchy (h₁ (l ∘ₗ LinearMap.mulRight ℂ (b i : R))) (h₂ (b.coord i ∘ₗ π))
    have T := hasSum_sum (s := Finset.univ) (fun i _ => S i)
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at T
    rw [key u v hv]
    convert T using 2 with k
    rw [der_pow_mul, map_sum, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain rfl : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, key _ _ (pow_mem m₂ s₂ _), ← mul_assoc, fact_choose, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/- English proof (translation)
Establish `g : ∀ P, Good D P (φ P)` using `fun P => by`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Use `Good.const D a` as an intermediate fact. Rewrite `*` using `[show algebraMap ℂ (MvPolynomial σ ℂ) a = MvPolynomial.C a from rfl, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]`. Then use the resulting hypothesis.

Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp => rw [map_mul]`. Conclude with `hp.mul (h i)`. Conclude with `fun v l => (g v).2 l`.
-/
theorem isExp_of_gens {σ : Type} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (h : ∀ i, Good D (MvPolynomial.X i) (φ (MvPolynomial.X i))) :
    IsExp D.toLinearMap φ.toLinearMap := by
  have g : ∀ P, Good D P (φ P) := fun P => by
    induction P using MvPolynomial.induction_on with
    | C a =>
      have := Good.const D a
      rwa [show algebraMap ℂ (MvPolynomial σ ℂ) a = MvPolynomial.C a from rfl, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes] at *
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p i hp => rw [map_mul]; exact hp.mul (h i)
  exact fun v l => (g v).2 l

/- English proof (translation)
Introduce `v l`. Establish `hc : Commute L (s • (1 : Module.End ℂ V))` using `(Commute.one_right L).smul_right s`. Establish `b : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * s ^ n) (Complex.exp s)`. Use `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) s` as an intermediate fact. Rewrite `this` using `[← Complex.exp_eq_exp_ℂ]`.

Simplify `this` using `[smul_eq_mul]`. Establish `T` using `hasSum_cauchy (h v l) b`. Establish `e : l ((Complex.exp s • U) v) = l (U v) * Complex.exp s`. Simplify using `[mul_comm]`. Rewrite using `[e]`.

Use `T using 2 with k` and compare the differences between its conclusion and the goal. Rewrite using `[hc.add_pow', LinearMap.sum_apply, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Take `rfl : p.1 + p.2 = k` from `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`. Establish `: (s • (1 : Module.End ℂ V)) ^ p.2 = s ^ p.2 • 1` using `by rw [smul_pow, one_pow]`.

Rewrite using `[this, LinearMap.smul_apply, Module.End.mul_apply]`. Simplify using `only [mul_smul_comm, mul_one, LinearMap.smul_apply, Module.End.one_apply, map_nsmul, map_smul, smul_eq_mul, nsmul_eq_mul]`. Rewrite using `[← mul_assoc, fact_choose]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isExp_shift {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (h : IsExp L U) (s : ℂ) :
    IsExp (L + s • 1) (Complex.exp s • U) := by
  intro v l
  have hc : Commute L (s • (1 : Module.End ℂ V)) := (Commute.one_right L).smul_right s
  have b : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * s ^ n) (Complex.exp s) := by
    have := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) s
    rw [← Complex.exp_eq_exp_ℂ] at this
    simpa [smul_eq_mul] using this
  have T := hasSum_cauchy (h v l) b
  have e : l ((Complex.exp s • U) v) = l (U v) * Complex.exp s := by
    simp [mul_comm]
  rw [e]
  convert T using 2 with k
  rw [hc.add_pow', LinearMap.sum_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain rfl : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have : (s • (1 : Module.End ℂ V)) ^ p.2 = s ^ p.2 • 1 := by rw [smul_pow, one_pow]
  rw [this, LinearMap.smul_apply, Module.End.mul_apply]
  simp only [mul_smul_comm, mul_one, LinearMap.smul_apply, Module.End.one_apply, map_nsmul, map_smul, smul_eq_mul, nsmul_eq_mul]
  rw [← mul_assoc, fact_choose]
  ring

section Mat

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Establish `h` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y`. Establish `h1` using `h.map (Matrix.entryAddMonoidHom ℂ a c) (continuous_id.matrix_elem a c)`. Simplify using `only [Function.comp_def, Matrix.entryAddMonoidHom_apply, Matrix.smul_apply, smul_eq_mul] at h1`. Conclude with `h1`.
-/
theorem hasSum_exp_entry {τ : Type} [Fintype τ] [DecidableEq τ] (Y : Matrix τ τ ℂ) (a c : τ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (Y ^ n) a c) (NormedSpace.exp Y a c) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h1 := h.map (Matrix.entryAddMonoidHom ℂ a c) (continuous_id.matrix_elem a c)
  simp only [Function.comp_def, Matrix.entryAddMonoidHom_apply, Matrix.smul_apply, smul_eq_mul] at h1
  exact h1

end Mat

/- English proof (translation)
Establish `hp : ∀ (k : ℕ) c, (D.toLinearMap ^ k) (v c) = ∑ a, (Y ^ k) a c • v a` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => intro c`. Simplify using `[Matrix.one_apply, ite_smul]`. Consider the case `succ k ih`.

Introduce `c`. Rewrite using `[pow_succ, Module.End.mul_apply, show D.toLinearMap (v c) = _ from hD c, map_sum]`. Simplify using `only [map_smul, ih, pow_succ, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by rw [mul_comm]`.

Use `⟨⟨Submodule.span ℂ (Set.range v), FiniteDimensional.span_of_finite ℂ (Set.finite_range v), Submodule.subset_span ⟨c, rfl⟩, ?_⟩, fun l => ?_⟩` and prove the remaining obligations. Establish `: Submodule.span ℂ (Set.range v) ≤ (Submodule.span ℂ (Set.range v)).comap D.toLinearMap`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨e, rfl⟩`. Express the relevant statement in the definitionally equal form `D (v e) ∈ Submodule.span ℂ (Set.range v)`.

Rewrite using `[hD]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Conclude with `fun y hy => this hy`. Apply the tactic sequence `have T := hasSum_sum (s := Finset.univ) fun a _ => (hasSum_exp_entry Y a c).mul_right (l (v a))`. Establish `e1 : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) (v c))) = fun n : ℕ => ∑ a, ((n.factorial : ℂ))⁻¹ * (Y ^ n) a c * l (v a)`.

Use function extensionality and compare the values at `n`. Rewrite using `[hp, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_assoc]`. Establish `e2 : l (∑ a, NormedSpace.exp Y a c • v a) = ∑ a, NormedSpace.exp Y a c * l (v a)`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul]`. Rewrite using `[e1, e2]`. Conclude with `T`.
-/
theorem good_lin (D : Derivation ℂ R R) {τ : Type} [Fintype τ] [DecidableEq τ] (Y : Matrix τ τ ℂ) (v : τ → R)
    (hD : ∀ c, D (v c) = ∑ a, Y a c • v a) (c : τ) : Good D (v c) (∑ a, NormedSpace.exp Y a c • v a) := by
  have hp : ∀ (k : ℕ) c, (D.toLinearMap ^ k) (v c) = ∑ a, (Y ^ k) a c • v a := fun k => by
    induction k with
    | zero => intro c; simp [Matrix.one_apply, ite_smul]
    | succ k ih =>
      intro c
      rw [pow_succ, Module.End.mul_apply, show D.toLinearMap (v c) = _ from hD c, map_sum]
      simp only [map_smul, ih, pow_succ, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by rw [mul_comm]
  refine ⟨⟨Submodule.span ℂ (Set.range v), FiniteDimensional.span_of_finite ℂ (Set.finite_range v),
    Submodule.subset_span ⟨c, rfl⟩, ?_⟩, fun l => ?_⟩
  · have : Submodule.span ℂ (Set.range v) ≤ (Submodule.span ℂ (Set.range v)).comap D.toLinearMap := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨e, rfl⟩
      change D (v e) ∈ Submodule.span ℂ (Set.range v)
      rw [hD]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    exact fun y hy => this hy
  · have T := hasSum_sum (s := Finset.univ) fun a _ => (hasSum_exp_entry Y a c).mul_right (l (v a))
    have e1 : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((D.toLinearMap ^ n) (v c))) =
        fun n : ℕ => ∑ a, ((n.factorial : ℂ))⁻¹ * (Y ^ n) a c * l (v a) := by
      funext n
      rw [hp, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, smul_eq_mul, mul_assoc]
    have e2 : l (∑ a, NormedSpace.exp Y a c • v a) = ∑ a, NormedSpace.exp Y a c * l (v a) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul]
    rw [e1, e2]
    exact T

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => simp [Finset.sum_insert ha, ih]`.
-/
theorem der_sum_apply {ι : Type} (s : Finset ι) (f : ι → Derivation ℂ R R) (x : R) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

end UpperTheory.TP.RP.Der
