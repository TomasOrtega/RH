import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

/- English proof (translation)
Rewrite `h`, the goal using `[Finsupp.mem_support_iff]`. Establish `e : (monomial a * q).coeff c = 1 * q.coeff (-a + c)` using `AddMonoidAlgebra.coeff_single_mul_apply q 1 a c`. Rewrite `h` using `[e, one_mul]`. Conclude with `h`.
-/
private theorem UpperTheory.ConvolutionTheory.H.mem_supp_mono {n : ℕ} {a c : Fin n → ℤ} {q : LaurentRing n}
    (h : c ∈ (monomial a * q).coeff.support) : -a + c ∈ q.coeff.support := by
  rw [Finsupp.mem_support_iff] at h ⊢
  have e : (monomial a * q).coeff c = 1 * q.coeff (-a + c) :=
    AddMonoidAlgebra.coeff_single_mul_apply q 1 a c
  rw [e, one_mul] at h
  exact h

/- English proof (translation)
Use `set M : ℕ := ∑ b ∈ B, ∑ i, (b i).natAbs with hM`. Establish `hb : ∀ b ∈ B, ∀ i, (b i).natAbs ≤ M` using `fun b hb i => (Finset.single_le_sum (f := fun i => (b i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (Finset.single_le_sum (f := fun b : Fin n → ℤ => ∑ i, (b i).natAbs) (fun _ _ => Nat.zero_le _) hb)`. Use `⟨2 * M + 1, fun a ha b hbB i j hij => ?_⟩` and prove the remaining obligations. Establish `h1` using `ha i j hij`. Establish `h2` using `hb b hbB i`.

Establish `h3` using `hb b hbB j`. Simplify using `only [Pi.add_apply]`. Move the coercions through the operations in `at h1`. Use linear arithmetic over natural numbers and integers.
-/
private theorem UpperTheory.ConvolutionTheory.H.gap_strict {n : ℕ} (B : Finset (Fin n → ℤ)) :
    ∃ m : ℕ, ∀ a : Fin n → ℤ, Gap m a → ∀ b ∈ B, StrictAnti (a + b) := by
  classical
  set M : ℕ := ∑ b ∈ B, ∑ i, (b i).natAbs with hM
  have hb : ∀ b ∈ B, ∀ i, (b i).natAbs ≤ M := fun b hb i =>
    (Finset.single_le_sum (f := fun i => (b i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun b : Fin n → ℤ => ∑ i, (b i).natAbs)
        (fun _ _ => Nat.zero_le _) hb)
  refine ⟨2 * M + 1, fun a ha b hbB i j hij => ?_⟩
  have h1 := ha i j hij
  have h2 := hb b hbB i
  have h3 := hb b hbB j
  simp only [Pi.add_apply]
  push_cast at h1
  omega

/- English proof (translation)
Introduce `i j hij` and use `by have := ha i j hij have h' : (m : ℤ) ≤ m' := by exact_mod_cast h omega`.
-/
private theorem UpperTheory.ConvolutionTheory.H.Gap.mono {n : ℕ} {m m' : ℕ} (h : m ≤ m') {a : Fin n → ℤ}
    (ha : Gap m' a) : Gap m a := fun i j hij => by
  have := ha i j hij
  have h' : (m : ℤ) ≤ m' := by exact_mod_cast h
  omega

/- English proof (translation)
Introduce `i j hij` and use `by have h := ha i j hij have h' : (1 : ℤ) ≤ l := by exact_mod_cast hl have hm : (0 : ℤ) ≤ m := by positivity simp only [Pi.smul_apply, smul_eq_mul] nlinarith`.
-/
private theorem UpperTheory.ConvolutionTheory.H.Gap.scale {n : ℕ} {m l : ℕ} (hl : 1 ≤ l) {a : Fin n → ℤ}
    (ha : Gap m a) : Gap m ((l : ℤ) • a) := fun i j hij => by
  have h := ha i j hij
  have h' : (1 : ℤ) ≤ l := by exact_mod_cast hl
  have hm : (0 : ℤ) ≤ m := by positivity
  simp only [Pi.smul_apply, smul_eq_mul]
  nlinarith

/- English proof (translation)
Simplify using `only [bc, AddMonoidAlgebra.mapDomainAlgHom_apply, monomial, AddMonoidAlgebra.mapDomain_single]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.ConvolutionTheory.H.bc_monomial {n : ℕ} (l : ℕ) (a : Fin n → ℤ) :
    bc l (monomial a) = monomial ((l : ℤ) • a) := by
  simp only [bc, AddMonoidAlgebra.mapDomainAlgHom_apply, monomial, AddMonoidAlgebra.mapDomain_single]
  rfl

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp [monomial, AddMonoidAlgebra.one_def]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ← ih, ← monomial_add]`. Use `congr 1`.

Use `push_cast`. Rewrite using `[add_smul, one_smul]`.
-/
private theorem UpperTheory.ConvolutionTheory.H.monomial_pow {n : ℕ} (l : ℕ) (a : Fin n → ℤ) :
    monomial ((l : ℤ) • a) = monomial a ^ l := by
  induction l with
  | zero => simp [monomial, AddMonoidAlgebra.one_def]
  | succ k ih =>
    rw [pow_succ, ← ih, ← monomial_add]
    congr 1
    push_cast
    rw [add_smul, one_smul]

private noncomputable def UpperTheory.ConvolutionTheory.H.cof (n l : ℕ) (t : ℂ) : LaurentRing n :=
  ∏ p ∈ pairs n, ∑ k ∈ Finset.range l, varL p.1 ^ k * (t • varL p.2) ^ (l - 1 - k)

/- English proof (translation)
Simplify using `only [dPol, cof, map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, mul_comm, geom_sum₂_mul, smul_pow]`. Simplify using `only [varL, bc_monomial, monomial_pow]`.
-/
private theorem UpperTheory.ConvolutionTheory.H.bc_dPol (n l : ℕ) (t : ℂ) :
    bc l (dPol n (t ^ l)) = dPol n t * cof n l t := by
  simp only [dPol, cof, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, map_smul, mul_comm, geom_sum₂_mul, smul_pow]
  simp only [varL, bc_monomial, monomial_pow]

/- English proof (translation)
Introduce `n l hl t P ν ν'`. Take `⟨m₁, h₁⟩` from `gap_strict (P.biUnion fun p => (dPol n (t ^ l) * p).coeff.support)`. Take `⟨m₂, h₂⟩` from `gap_strict (P.biUnion fun p => p.coeff.support.image (· - ν))`. Take `⟨m₃, h₃⟩` from `gap_strict (P.biUnion fun p => (cof n l t * bc l p).coeff.support.image (· - ν'))`. Use `⟨m₁ + m₂ + m₃, fun a ha p hp => ⟨?_, ⟨monomial (a - ν) * p, ?_, ?_⟩, ⟨monomial ((l : ℤ) • a - ν') * (cof n l t * bc l p), ?_, ?_⟩⟩⟩` and prove the remaining obligations.

Introduce `c hc`. Rewrite `hc` using `[mul_assoc]`. Establish `hb` using `mem_supp_mono hc`. Use `h₁ a (Gap.mono (by omega) ha) (-a + c) (Finset.mem_biUnion.2 ⟨p, hp, hb⟩)` as an intermediate fact. Simplify using `using this`.

Introduce `c hc`. Establish `hb` using `mem_supp_mono hc`. Use `h₂ a (Gap.mono (by omega) ha) (-(a - ν) + c - ν) (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)` as an intermediate fact. Establish `e : a + (-(a - ν) + c - ν) = c` using `by abel`. Rewrite `this` using `[e]`.

Conclude with `this.antitone`. Establish `e : monomial a = monomial ν * monomial (a - ν)`. Rewrite using `[← monomial_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c hc`. Establish `hb` using `mem_supp_mono hc`. Use `h₃ ((l : ℤ) • a) (Gap.scale hl (Gap.mono (by omega) ha)) (-((l : ℤ) • a - ν') + c - ν') (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)` as an intermediate fact.

Establish `e : (l : ℤ) • a + (-((l : ℤ) • a - ν') + c - ν') = c` using `by abel`. Rewrite `this` using `[e]`. Conclude with `this.antitone`. Establish `e : monomial ((l : ℤ) • a) = monomial ν' * monomial ((l : ℤ) • a - ν')`. Rewrite using `[← monomial_add]`.

Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[map_mul, map_mul, bc_monomial, bc_dPol, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.H.depth :
    ∀ (n l : ℕ), 1 ≤ l → ∀ (t : ℂ) (P : Finset (LaurentRing n)) (ν ν' : Fin n → ℤ), ∃ m : ℕ, ∀ a : Fin n → ℤ, Gap m a → ∀ p ∈ P,
      SDom (monomial a * dPol n (t ^ l) * p) ∧
      (∃ r, Dom r ∧ monomial a * dPol n (t ^ l) * p = monomial ν * dPol n (t ^ l) * r) ∧
      ∃ r', Dom r' ∧ bc l (monomial a * dPol n (t ^ l) * p) = monomial ν' * dPol n t * r' := by
  classical
  intro n l hl t P ν ν'
  obtain ⟨m₁, h₁⟩ := gap_strict (P.biUnion fun p => (dPol n (t ^ l) * p).coeff.support)
  obtain ⟨m₂, h₂⟩ := gap_strict (P.biUnion fun p => p.coeff.support.image (· - ν))
  obtain ⟨m₃, h₃⟩ := gap_strict
    (P.biUnion fun p => (cof n l t * bc l p).coeff.support.image (· - ν'))
  refine ⟨m₁ + m₂ + m₃, fun a ha p hp => ⟨?_, ⟨monomial (a - ν) * p, ?_, ?_⟩,
    ⟨monomial ((l : ℤ) • a - ν') * (cof n l t * bc l p), ?_, ?_⟩⟩⟩
  · intro c hc
    rw [mul_assoc] at hc
    have hb := mem_supp_mono hc
    have := h₁ a (Gap.mono (by omega) ha) (-a + c)
      (Finset.mem_biUnion.2 ⟨p, hp, hb⟩)
    simpa using this
  · intro c hc
    have hb := mem_supp_mono hc
    have := h₂ a (Gap.mono (by omega) ha) (-(a - ν) + c - ν)
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)
    have e : a + (-(a - ν) + c - ν) = c := by abel
    rw [e] at this
    exact this.antitone
  · have e : monomial a = monomial ν * monomial (a - ν) := by
      rw [← monomial_add]; congr 1; abel
    rw [e]; ring
  · intro c hc
    have hb := mem_supp_mono hc
    have := h₃ ((l : ℤ) • a) (Gap.scale hl (Gap.mono (by omega) ha))
      (-((l : ℤ) • a - ν') + c - ν')
      (Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_image.2 ⟨_, hb, rfl⟩⟩)
    have e : (l : ℤ) • a + (-((l : ℤ) • a - ν') + c - ν') = c := by abel
    rw [e] at this
    exact this.antitone
  · have e : monomial ((l : ℤ) • a) = monomial ν' * monomial ((l : ℤ) • a - ν') := by
      rw [← monomial_add]; congr 1; abel
    rw [map_mul, map_mul, bc_monomial, bc_dPol, e]; ring
