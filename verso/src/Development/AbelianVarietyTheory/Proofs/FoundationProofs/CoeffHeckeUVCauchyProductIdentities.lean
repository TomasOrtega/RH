import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.FormalId

variable {R : Type} [CommRing R]

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `only [Uo, mul, Vo, mul_ite, mul_zero]`. Rewrite using `[← Finset.sum_filter]`. Use `symm`. Apply `Finset.sum_nbij' (fun p => (l * p.1, l * p.2)) (fun p => (p.1 / l, p.2 / l))` to reduce the goal to its premises.

Introduce `p hp`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢`. Conclude with `⟨by rw [← mul_add, hp], dvd_mul_right _ _⟩`. Introduce `p hp`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢`.

Take `⟨h1, h2⟩` from `hp`. Establish `h3 : l ∣ p.1`. Establish `: l ∣ p.1 + p.2` using `by rw [h1]; exact dvd_mul_right _ _`. Conclude with `(Nat.dvd_add_left h2).mp this`. Rewrite using `[← Nat.add_div_of_dvd_right h3, h1, Nat.mul_div_cancel_left _ hl]`.

Introduce `p _`. Simplify using `[Nat.mul_div_cancel_left _ hl]`. Introduce `p hp`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp`. Take `⟨h1, h2⟩` from `hp`.

Establish `h3 : l ∣ p.1`. Establish `: l ∣ p.1 + p.2` using `by rw [h1]; exact dvd_mul_right _ _`. Conclude with `(Nat.dvd_add_left h2).mp this`. Apply the tactic sequence `ext <;> simp [Nat.mul_div_cancel' h3, Nat.mul_div_cancel' h2]`. Introduce `p _`.

Simplify using `[Nat.mul_div_cancel_left _ hl]`.
-/
theorem uo_mul_vo (l : ℕ) (hl : 0 < l) (a b : ℕ → R) : Uo l (mul a (Vo l b)) = mul (Uo l a) b := by
  funext n
  simp only [Uo, mul, Vo, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun p => (l * p.1, l * p.2)) (fun p => (p.1 / l, p.2 / l))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    exact ⟨by rw [← mul_add, hp], dvd_mul_right _ _⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    rw [← Nat.add_div_of_dvd_right h3, h1, Nat.mul_div_cancel_left _ hl]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    ext <;> simp [Nat.mul_div_cancel' h3, Nat.mul_div_cancel' h2]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `only [mul]`. Use `conv_lhs => rw [← Finset.Nat.sum_antidiagonal_swap]`. Simplify using `[_root_.mul_comm]`.
-/
theorem mul_comm' (a b : ℕ → R) : mul a b = mul b a := by
  funext n
  simp only [mul]
  conv_lhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  simp [_root_.mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `[mul, _root_.mul_add, Finset.sum_add_distrib]`.
-/
theorem mul_add_right' (a b b' : ℕ → R) : mul a (b + b') = mul a b + mul a b' := by
  funext n
  simp [mul, _root_.mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Rewrite using `[mul_comm', mul_add_right', mul_comm' b, mul_comm' b]`.
-/
theorem mul_add_left' (a a' b : ℕ → R) : mul (a + a') b = mul a b + mul a' b := by
  rw [mul_comm', mul_add_right', mul_comm' b, mul_comm' b]

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `only [mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib, Finset.mul_sum]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem mul_lin (a b b' : ℕ → R) (c c' : R) :
    mul a (c • b + c' • b') = c • mul a b + c' • mul a b' := by
  funext n
  simp only [mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `[mul]`.
-/
theorem zero_mul' (b : ℕ → R) : mul 0 b = 0 := by
  funext n; simp [mul]

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `[Uo, dep]`.
-/
theorem uo_dep (l : ℕ) (a : ℕ → R) : Uo l (dep l a) = 0 := by
  funext n; simp [Uo, dep]

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `[Uo, Vo, Nat.mul_div_cancel_left _ hl]`.
-/
theorem uo_vo (l : ℕ) (hl : 0 < l) (a : ℕ → R) : Uo l (Vo l a) = a := by
  funext n; simp [Uo, Vo, Nat.mul_div_cancel_left _ hl]

/- English proof (translation)
Use function extensionality and compare the values at `n`. Distinguish the cases in `h : l ∣ n`. Simplify using `[dep, Vo, Uo, h, Nat.mul_div_cancel' h]`. Simplify using `[dep, Vo, Uo, h]`.
-/
theorem dep_add (l : ℕ) (hl : 0 < l) (a : ℕ → R) : a = dep l a + Vo l (Uo l a) := by
  funext n
  by_cases h : l ∣ n
  · simp [dep, Vo, Uo, h, Nat.mul_div_cancel' h]
  · simp [dep, Vo, Uo, h]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uo_add (l : ℕ) (x y : ℕ → R) : Uo l (x + y) = Uo l x + Uo l y := rfl

/- English proof (translation)
Establish `e : Uo l (mul a b) = Uo l (mul (dep l a) (dep l b)) + mul (Uo l a) (Uo l b)` using `by conv_lhs => rw [dep_add l hl a, dep_add l hl b]`. Rewrite using `[mul_add_left', mul_add_right', mul_add_right', uo_add, uo_add, uo_add, uo_mul_vo l hl, uo_dep, zero_mul', mul_comm' (Vo l (Uo l a)) (dep l b), uo_mul_vo l hl, uo_dep, zero_mul', uo_mul_vo l hl, uo_vo l hl]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Normalize the expressions using the abelian group laws.
-/
theorem uo_mul_dep (l : ℕ) (hl : 0 < l) (a b : ℕ → R) :
    Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b) := by
  have e : Uo l (mul a b) = Uo l (mul (dep l a) (dep l b)) + mul (Uo l a) (Uo l b) := by
    conv_lhs => rw [dep_add l hl a, dep_add l hl b]
    rw [mul_add_left', mul_add_right', mul_add_right', uo_add, uo_add, uo_add,
      uo_mul_vo l hl, uo_dep, zero_mul', mul_comm' (Vo l (Uo l a)) (dep l b), uo_mul_vo l hl, uo_dep,
      zero_mul', uo_mul_vo l hl, uo_vo l hl]
    abel
  rw [e]; abel

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `only [To, Vo]`. Distinguish the cases in `hn : l ∣ n`. Take `⟨m, rfl⟩` from `hn`. Break down `Nat.eq_zero_or_pos l with hl | hl` into its components or cases.

Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Establish `h1 : l ∣ q * (l * m)` using `⟨q * m, by ring⟩`. Rewrite using `[if_pos h1, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl, show q * (l * m) = l * (q * m) by ring, Nat.mul_div_cancel_left _ hl]`. Use `congr 1`.

Distinguish the cases in `hqm : q ∣ m`. Take `⟨t, rfl⟩` from `hqm`. Rewrite using `[if_pos ⟨l * t, by ring⟩, if_pos (dvd_mul_right _ _), show l * (q * t) = q * (l * t) by ring, Nat.mul_div_cancel_left _ hq0, Nat.mul_div_cancel_left _ hq0, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl]`. Rewrite using `[if_neg hqm, if_neg]`. Introduce `h`.

Conclude with `hqm ((Nat.Coprime.dvd_of_dvd_mul_left hq h))`. Establish `h1 : ¬ l ∣ q * n` using `fun h => hn (Nat.Coprime.dvd_of_dvd_mul_left hq.symm h)`. Rewrite using `[if_neg h1, if_neg hn]`. Distinguish the cases in `hqn : q ∣ n`. Rewrite using `[if_pos hqn, if_neg]`.

Simplify using the standard rewrite rules. Introduce `h`. Take `⟨t, ht⟩` from `hqn`. Apply `hn` to reduce the goal to its premises. Rewrite `h` using `[ht, Nat.mul_div_cancel_left _ hq0]`.

Conclude with `Dvd.dvd.mul_left h q |> fun h' => by rw [ht]; exact h'`. Simplify using `[hqn]`.
-/
theorem to_vo (l k q : ℕ) (c : R) (a : ℕ → R) (hq : q.Coprime l) (hq0 : 0 < q) :
    To k c q (Vo l a) = Vo l (To k c q a) := by
  funext n
  simp only [To, Vo]
  by_cases hn : l ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp
    have h1 : l ∣ q * (l * m) := ⟨q * m, by ring⟩
    rw [if_pos h1, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl,
      show q * (l * m) = l * (q * m) by ring, Nat.mul_div_cancel_left _ hl]
    congr 1
    by_cases hqm : q ∣ m
    · obtain ⟨t, rfl⟩ := hqm
      rw [if_pos ⟨l * t, by ring⟩, if_pos (dvd_mul_right _ _),
        show l * (q * t) = q * (l * t) by ring, Nat.mul_div_cancel_left _ hq0, Nat.mul_div_cancel_left _ hq0,
        if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl]
    · rw [if_neg hqm, if_neg]
      intro h
      exact hqm ((Nat.Coprime.dvd_of_dvd_mul_left hq h))
  · have h1 : ¬ l ∣ q * n := fun h => hn (Nat.Coprime.dvd_of_dvd_mul_left hq.symm h)
    rw [if_neg h1, if_neg hn]
    by_cases hqn : q ∣ n
    · rw [if_pos hqn, if_neg]
      · simp
      · intro h
        obtain ⟨t, ht⟩ := hqn
        apply hn
        rw [ht, Nat.mul_div_cancel_left _ hq0] at h
        exact Dvd.dvd.mul_left h q |> fun h' => by rw [ht]; exact h'
    · simp [hqn]

/- English proof (translation)
Simplify using `only [lam, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib, Finset.mul_sum]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem lam_lin (B : ℕ) (c a b : ℕ → R) (x y : R) :
    lam B c (x • a + y • b) = x * lam B c a + y * lam B c b := by
  simp only [lam, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.EisM.FormalId

/- English proof (translation)
Introduce `R _ l hl`. Conclude with `⟨FormalId.uo_mul_vo l hl, FormalId.uo_mul_dep l hl, FormalId.mul_comm', FormalId.mul_lin, fun k q c a hq hq0 => FormalId.to_vo l k q c a hq hq0, FormalId.lam_lin⟩`.
-/
theorem GlobalTheory.EisM.formal_identities : ∀ (R : Type) [CommRing R] (l : ℕ), 0 < l → (∀ a b : ℕ → R, Uo l (mul a (Vo l b)) = mul (Uo l a) b) ∧ (∀ a b : ℕ → R, Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b)) ∧ (∀ a b : ℕ → R, mul a b = mul b a) ∧ (∀ (a b b' : ℕ → R) (c c' : R), mul a (c • b + c' • b') = c • mul a b + c' • mul a b') ∧ (∀ (k q : ℕ) (c : R) (a : ℕ → R), q.Coprime l → 0 < q → To k c q (Vo l a) = Vo l (To k c q a)) ∧ (∀ (B : ℕ) (c a b : ℕ → R) (x y : R), lam B c (x • a + y • b) = x * lam B c a + y * lam B c b) := by
  intro R _ l hl
  exact ⟨FormalId.uo_mul_vo l hl, FormalId.uo_mul_dep l hl, FormalId.mul_comm', FormalId.mul_lin,
    fun k q c a hq hq0 => FormalId.to_vo l k q c a hq hq0, FormalId.lam_lin⟩
