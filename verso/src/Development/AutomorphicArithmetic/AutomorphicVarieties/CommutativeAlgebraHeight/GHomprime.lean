import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GHommem

open IsLocalRing

/- English proof (translation)
Establish `hfin : ∀ d : ℕ, {m : σ →₀ ℕ | m.degree = d}.Finite` using `fun d => (Finsupp.finite_of_degree_le (σ := σ) d).subset (fun m hm => le_of_eq hm)`. Use `⟨fun F d => ∑ m ∈ (hfin d).toFinset, MvPolynomial.monomial m (MvPowerSeries.coeff m F), ?_⟩` and prove the remaining obligations. Introduce `F d m`. Rewrite using `[MvPolynomial.coeff_sum]`. Repeatedly rewrite using `[MvPolynomial.coeff_monomial]`.

Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.V.CA.homprime_part (R σ : Type) [CommRing R] [Finite σ] :
    ∃ p : MvPowerSeries σ R → ℕ → MvPolynomial σ R, ∀ F d (m : σ →₀ ℕ),
      (p F d).coeff m = if m.degree = d then MvPowerSeries.coeff m F else 0 := by
  classical
  have hfin : ∀ d : ℕ, {m : σ →₀ ℕ | m.degree = d}.Finite := fun d =>
    (Finsupp.finite_of_degree_le (σ := σ) d).subset (fun m hm => le_of_eq hm)
  refine ⟨fun F d => ∑ m ∈ (hfin d).toFinset, MvPolynomial.monomial m (MvPowerSeries.coeff m F), ?_⟩
  intro F d m
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[MvPolynomial.coeff_sum]`. Repeatedly rewrite using `[MvPolynomial.coeff_mul, hp, MvPowerSeries.coeff_mul]`. Rewrite using `[Finset.sum_comm]`. Use `split_ifs with h`.

Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[Finset.sum_eq_single (x.1.degree, x.2.degree)]`. Simplify using the standard rewrite rules.

Introduce `q _ hq`. Distinguish the cases in `h1 : x.1.degree = q.1`. Establish `h2 : x.2.degree ≠ q.2`. Introduce `h2`. Conclude with `hq (Prod.ext h1.symm h2.symm)`.

Simplify using `[h2]`. Simplify using `[h1]`. Introduce `hq`. It suffices to derive a contradiction. Apply `hq` to reduce the goal to its premises.

Rewrite using `[Finset.HasAntidiagonal.mem_antidiagonal, ← h, ← hx, map_add]`. Use `symm`. Use `Finset.sum_eq_zero ?_` and prove the remaining obligations. Introduce `x hx`. Use `Finset.sum_eq_zero ?_` and prove the remaining obligations.

Introduce `q hq`. Rewrite `hx`, `hq` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Distinguish the cases in `h1 : x.1.degree = q.1`. Distinguish the cases in `h2 : x.2.degree = q.2`. It suffices to derive a contradiction.

Apply `h` to reduce the goal to its premises. Rewrite using `[← hx, map_add, h1, h2, hq]`. Simplify using `[h2]`. Simplify using `[h1]`.
-/
private theorem UpperTheory.V.CA.homprime_mul (R σ : Type) [CommRing R]
    (p : MvPowerSeries σ R → ℕ → MvPolynomial σ R) (hp : ∀ F d (m : σ →₀ ℕ),
      (p F d).coeff m = if m.degree = d then MvPowerSeries.coeff m F else 0)
    (F G : MvPowerSeries σ R) (n : ℕ) :
    p (F * G) n = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, p F q.1 * p G q.2 := by
  classical
  ext m
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_mul, hp, MvPowerSeries.coeff_mul]
  rw [Finset.sum_comm]
  split_ifs with h
  · refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [Finset.sum_eq_single (x.1.degree, x.2.degree)]
    · simp
    · intro q _ hq
      by_cases h1 : x.1.degree = q.1
      · have h2 : x.2.degree ≠ q.2 := by
          intro h2
          exact hq (Prod.ext h1.symm h2.symm)
        simp [h2]
      · simp [h1]
    · intro hq
      exfalso
      apply hq
      rw [Finset.HasAntidiagonal.mem_antidiagonal, ← h, ← hx, map_add]
  · symm
    refine Finset.sum_eq_zero ?_
    intro x hx
    refine Finset.sum_eq_zero ?_
    intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hq
    by_cases h1 : x.1.degree = q.1
    · by_cases h2 : x.2.degree = q.2
      · exfalso
        apply h
        rw [← hx, map_add, h1, h2, hq]
      · simp [h2]
    · simp [h1]

/- English proof (translation)
Introduce `R σ _ _ _ P hP hhom`. Take `⟨p, hp⟩` from `UpperTheory.V.CA.homprime_part R σ`. Establish `key : ∀ F : MvPowerSeries σ R, F ∈ P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ` using `σ) (R := R)) ↔ ∀ d, p F d ∈ P := by`. Introduce `F`. Rewrite using `[UpperTheory.V.CA.g_hommem R σ P hhom F]`.

Prove the components needed by the constructor for the conclusion. Introduce `h d`. Conclude with `h d (p F d) (hp F d)`. Introduce `h d g hg`. Establish `hg' : g = p F d`.

Use extensionality with `m`. Rewrite using `[hg, hp]`. Rewrite using `[hg']`. Conclude with `h d`. Establish `hcomap : (P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ` using `σ) (R := R))).comap (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) = P := by`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Rewrite `hf` using `[Ideal.mem_comap, key]`. Establish `hd : ∀ d, MvPolynomial.homogeneousComponent d f ∈ P`. Introduce `d`.

Establish `he : MvPolynomial.homogeneousComponent d f = p (MvPolynomial.coeToMvPowerSeries.ringHom (σ` using `σ) (R := R) f) d := by`. Use extensionality with `m`. Rewrite using `[MvPolynomial.coeff_homogeneousComponent, hp, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]`. Rewrite using `[he]`. Conclude with `hf d`.

Rewrite using `[← MvPolynomial.sum_homogeneousComponent f]`. Conclude with `Ideal.sum_mem _ (fun i _ => hd i)`. Conclude with `Ideal.le_comap_map`. Use `⟨⟨?_, ?_⟩, hcomap⟩` and prove the remaining obligations. Introduce `htop`.

Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[← hcomap, htop, Ideal.comap_top]`. Introduce `F G hFG`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Take `⟨hF, hG⟩` from `hne`. Rewrite `hF`, `hG`, `hFG` using `[key]`. Use `push_neg at hF hG`. Establish `ha : p F (Nat.find hF) ∉ P` using `Nat.find_spec hF`. Establish `hb : p G (Nat.find hG) ∉ P` using `Nat.find_spec hG`.

Establish `ha' : ∀ i < Nat.find hF, p F i ∈ P` using `fun i hi => by`. Simplify using `using Nat.find_min hF hi`. Establish `hb' : ∀ i < Nat.find hG, p G i ∈ P` using `fun i hi => by`. Simplify using `using Nat.find_min hG hi`. Establish `hsum` using `hFG (Nat.find hF + Nat.find hG)`.

Rewrite `hsum` using `[UpperTheory.V.CA.homprime_mul R σ p hp]`. Establish `hmem : (Nat.find hF, Nat.find hG) ∈ Finset.HasAntidiagonal.antidiagonal (Nat.find hF + Nat.find hG)`. Rewrite using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ hmem]`. Establish `hrest : ∑ q ∈ (Finset.HasAntidiagonal.antidiagonal (Nat.find hF + Nat.find hG)).erase (Nat.find hF, Nat.find hG), p F q.1 * p G q.2 ∈ P`.

Use `Ideal.sum_mem _ (fun q hq => ?_)` and prove the remaining obligations. Rewrite `hq` using `[Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal]`. Take `⟨hq2, hq1⟩` from `hq`. Break down `lt_or_ge q.1 (Nat.find hF) with h | h` into its components or cases. Conclude with `P.mul_mem_right _ (ha' _ h)`.

Establish `h2 : q.2 < Nat.find hG`. Break down `eq_or_lt_of_le h with h' | h'` into its components or cases. It suffices to derive a contradiction. Apply `hq2` to reduce the goal to its premises. Use `ext`.

Conclude with `h'.symm`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Conclude with `P.mul_mem_left _ (hb' _ h2)`.

Establish `hmain : p F (Nat.find hF) * p G (Nat.find hG) ∈ P`. Use `P.sub_mem hsum hrest` as an intermediate fact. Simplify using `using this`. Break down `hP.mem_or_mem hmain with h | h` into its components or cases. Conclude with `ha h`.

Conclude with `hb h`.
-/
theorem UpperTheory.V.CA.g_homprime :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (P : Ideal (MvPolynomial σ R)), P.IsPrime →
      (∀ f ∈ P, ∀ d : ℕ, MvPolynomial.homogeneousComponent d f ∈ P) →
        (P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R))).IsPrime ∧
          (P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R))).comap
            (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) = P := by
  intro R σ _ _ _ P hP hhom
  classical
  obtain ⟨p, hp⟩ := UpperTheory.V.CA.homprime_part R σ
  have key : ∀ F : MvPowerSeries σ R,
      F ∈ P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) ↔ ∀ d, p F d ∈ P := by
    intro F
    rw [UpperTheory.V.CA.g_hommem R σ P hhom F]
    constructor
    · intro h d
      exact h d (p F d) (hp F d)
    · intro h d g hg
      have hg' : g = p F d := by
        ext m
        rw [hg, hp]
      rw [hg']
      exact h d
  have hcomap : (P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R))).comap
      (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) = P := by
    apply le_antisymm
    · intro f hf
      rw [Ideal.mem_comap, key] at hf
      have hd : ∀ d, MvPolynomial.homogeneousComponent d f ∈ P := by
        intro d
        have he : MvPolynomial.homogeneousComponent d f =
            p (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R) f) d := by
          ext m
          rw [MvPolynomial.coeff_homogeneousComponent, hp,
            MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
        rw [he]
        exact hf d
      rw [← MvPolynomial.sum_homogeneousComponent f]
      exact Ideal.sum_mem _ (fun i _ => hd i)
    · exact Ideal.le_comap_map
  refine ⟨⟨?_, ?_⟩, hcomap⟩
  · intro htop
    apply hP.ne_top
    rw [← hcomap, htop, Ideal.comap_top]
  · intro F G hFG
    by_contra hne
    push_neg at hne
    obtain ⟨hF, hG⟩ := hne
    rw [key] at hF hG hFG
    push_neg at hF hG
    have ha : p F (Nat.find hF) ∉ P := Nat.find_spec hF
    have hb : p G (Nat.find hG) ∉ P := Nat.find_spec hG
    have ha' : ∀ i < Nat.find hF, p F i ∈ P := fun i hi => by
      simpa using Nat.find_min hF hi
    have hb' : ∀ i < Nat.find hG, p G i ∈ P := fun i hi => by
      simpa using Nat.find_min hG hi
    have hsum := hFG (Nat.find hF + Nat.find hG)
    rw [UpperTheory.V.CA.homprime_mul R σ p hp] at hsum
    have hmem : (Nat.find hF, Nat.find hG) ∈
        Finset.HasAntidiagonal.antidiagonal (Nat.find hF + Nat.find hG) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [← Finset.add_sum_erase _ _ hmem] at hsum
    have hrest : ∑ q ∈ (Finset.HasAntidiagonal.antidiagonal (Nat.find hF + Nat.find hG)).erase
        (Nat.find hF, Nat.find hG), p F q.1 * p G q.2 ∈ P := by
      refine Ideal.sum_mem _ (fun q hq => ?_)
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hq
      obtain ⟨hq2, hq1⟩ := hq
      rcases lt_or_ge q.1 (Nat.find hF) with h | h
      · exact P.mul_mem_right _ (ha' _ h)
      · have h2 : q.2 < Nat.find hG := by
          rcases eq_or_lt_of_le h with h' | h'
          · exfalso
            apply hq2
            ext
            · exact h'.symm
            · simp only
              omega
          · omega
        exact P.mul_mem_left _ (hb' _ h2)
    have hmain : p F (Nat.find hF) * p G (Nat.find hG) ∈ P := by
      have := P.sub_mem hsum hrest
      simpa using this
    rcases hP.mem_or_mem hmain with h | h
    · exact ha h
    · exact hb h
