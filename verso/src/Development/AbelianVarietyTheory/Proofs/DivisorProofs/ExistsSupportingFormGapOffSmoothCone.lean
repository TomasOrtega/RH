import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Gap

section Bound

variable {X : Type} [AddCommGroup X] {m : ℕ} {a : Fin m → X}

/- English proof (translation)
The claim follows from `|β x y| ≤ C * ∑ i, β (a i) (a i) := by have hx : x ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top have hy : y ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top have hl : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → 0 ≤ ∑ i, β (a i) (a i) := fun β hp => F …`.
-/
theorem exists_abs_apply_le (ha : Submodule.span ℤ (Set.range a) = ⊤) (x y : X) :
    ∃ C : ℕ, ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) →
      |β x y| ≤ C * ∑ i, β (a i) (a i) := by
  have hx : x ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  have hl : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → 0 ≤ ∑ i, β (a i) (a i) :=
    fun β hp => Finset.sum_nonneg fun i _ => hp _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      refine ⟨1, fun β hs hp => ?_⟩
      have h1 := hp (a i + a j)
      have h2 := hp (a i - a j)
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, hs (a j) (a i)] at h1 h2
      have h3 := Finset.single_le_sum (f := fun i => β (a i) (a i)) (fun i _ => hp _) (Finset.mem_univ i)
      have h4 := Finset.single_le_sum (f := fun i => β (a i) (a i)) (fun i _ => hp _) (Finset.mem_univ j)
      rw [abs_le]
      constructor <;> push_cast <;> linarith
    | zero => exact ⟨0, fun β _ _ => by simp⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨C, hC⟩ := h1
      obtain ⟨C', hC'⟩ := h2
      refine ⟨C + C', fun β hs hp => ?_⟩
      rw [map_add, Nat.cast_add, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hC β hs hp) (hC' β hs hp))
    | smul n y _ h1 =>
      obtain ⟨C, hC⟩ := h1
      refine ⟨n.natAbs * C, fun β hs hp => ?_⟩
      rw [map_smul, smul_eq_mul, abs_mul, Nat.cast_mul, Int.natCast_natAbs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC β hs hp) (abs_nonneg _)
  | zero => exact ⟨0, fun β _ _ => by simp⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨C, hC⟩ := h1
    obtain ⟨C', hC'⟩ := h2
    refine ⟨C + C', fun β hs hp => ?_⟩
    rw [map_add, LinearMap.add_apply, Nat.cast_add, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hC β hs hp) (hC' β hs hp))
  | smul n x _ h1 =>
    obtain ⟨C, hC⟩ := h1
    refine ⟨n.natAbs * C, fun β hs hp => ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul, Nat.cast_mul, Int.natCast_natAbs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC β hs hp) (abs_nonneg _)

/- English proof (translation)
The claim follows from `|lam β| ≤ C * ∑ i, β (a i) (a i) := by classical let b := Module.Free.chooseBasis ℤ X let E : _ → _ → LinearMap.BilinForm ℤ X := fun i j => (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j) have hE : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • E i j := fun β => …`.
-/
theorem exists_abs_lin_le [Module.Free ℤ X] [Module.Finite ℤ X] (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    ∃ C : ℕ, ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) →
      |lam β| ≤ C * ∑ i, β (a i) (a i) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let E : _ → _ → LinearMap.BilinForm ℤ X := fun i j => (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hE : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • E i j := fun β =>
    b.ext fun k => b.ext fun l => by
      simp [E, LinearMap.sum_apply, Finsupp.single_apply]
  choose C hC using exists_abs_apply_le ha
  refine ⟨∑ i, ∑ j, C (b i) (b j) * (lam (E i j)).natAbs, fun β hs hp => ?_⟩
  conv_lhs => rw [hE β]
  simp only [map_sum, map_smul, smul_eq_mul]
  push_cast
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (hC _ _ β hs hp) (abs_nonneg _)

end Bound

section Fan

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

/- English proof (translation)
Take `⟨S, hS, h⟩` from `hF.finite`. Take `⟨M, hM⟩` from `(hS.image fun β => φ.evalZ β).bddAbove`. Take `⟨N, hN⟩` from `exists_nat_ge M`. Use `⟨N, fun ρ hρ => ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `h 1 _ hρ`.

Establish `h1` using `hM ⟨_, he 0, rfl⟩`. Simplify using `only [evalZ_pull φ (r := e.toLinearMap) e.surjective, Matrix.cons_val_zero] at h1`. Conclude with `h1.trans hN`.
-/
theorem exists_ray_bound (hF : IsPolFanOn bar φ X) :
    ∃ M : ℕ, ∀ ρ : LinearMap.BilinForm ℤ X, IsCone bar φ ![ρ] → φ.evalZ ρ ≤ M := by
  obtain ⟨S, hS, h⟩ := hF.finite
  obtain ⟨M, hM⟩ := (hS.image fun β => φ.evalZ β).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge M
  refine ⟨N, fun ρ hρ => ?_⟩
  obtain ⟨e, he⟩ := h 1 _ hρ
  have h1 := hM ⟨_, he 0, rfl⟩
  simp only [evalZ_pull φ (r := e.toLinearMap) e.surjective, Matrix.cons_val_zero] at h1
  exact h1.trans hN

/- English proof (translation)
Establish `hB : toReal β ∈ psdCone bar X`. Simplify using `using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)`. Take `⟨m, γ, c, hγ, hc, hsum⟩` from `hF.cover _ hB`. Take `⟨nZ, hnZ⟩` from `Cover.coeff_int hγ.mem hγ.basis hβ hsum`. Establish `hn0 : ∀ i, 0 ≤ nZ i` using `fun i => by exact_mod_cast (hnZ i) ▸ hc i`.

Set `n : Fin m → ℕ` to `fun i => (nZ i).toNat`. Establish `hn : ∀ i, ((n i : ℤ) : ℝ) = c i` using `fun i => by simp [n, Int.toNat_of_nonneg (hn0 i), hnZ i]`. Use `⟨m, γ, n, hγ, LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun₂ hsum a b`. Simplify using `only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← hn] at h1`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul]`. Conclude with `h1` after adjusting the coercions.
-/
theorem exists_cone_nat [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (hF : IsPolFanOn bar φ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (s : ℕ) (δ : Fin s → LinearMap.BilinForm ℤ X) (n : Fin s → ℕ), IsCone bar φ δ ∧ β = ∑ i, n i • δ i := by
  have hB : toReal β ∈ psdCone bar X := by
    simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)
  obtain ⟨m, γ, c, hγ, hc, hsum⟩ := hF.cover _ hB
  obtain ⟨nZ, hnZ⟩ := Cover.coeff_int hγ.mem hγ.basis hβ hsum
  have hn0 : ∀ i, 0 ≤ nZ i := fun i => by exact_mod_cast (hnZ i) ▸ hc i
  let n : Fin m → ℕ := fun i => (nZ i).toNat
  have hn : ∀ i, ((n i : ℤ) : ℝ) = c i := fun i => by simp [n, Int.toNat_of_nonneg (hn0 i), hnZ i]
  refine ⟨m, γ, n, hγ, LinearMap.ext₂ fun a b => ?_⟩
  have h1 := LinearMap.congr_fun₂ hsum a b
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← hn] at h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul]
  exact_mod_cast h1

end Fan

/- English proof (translation)
Introduce `O _ _ _ _ bar φ d X _ _ _ _ _ _ hF r m γ a hγ hS lam hlam K`. Take `⟨C, hC⟩` from `exists_abs_lin_le hS.span lam`. Take `⟨M, hM⟩` from `exists_ray_bound hF`. Use `⟨C + K.natAbs + C * d * M, fun D hD => ?_⟩` and prove the remaining obligations. Establish `hray : ∀ ρ : LinearMap.BilinForm ℤ X, IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) → (D * d : ℝ) * φ.evalZ ρ + (K.natAbs : ℕ) ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ)`.

Introduce `ρ hρ hne`. Establish `hm : ρ ∈ balForms bar X` using `hρ.mem 0`. Establish `hp : ∀ y, 0 ≤ ρ y y` using `hρ.nonneg 0`. Take `⟨n, hn⟩` from `hF.exists_nat hm hp`. Establish `h1` using `hS.le ρ hm hp`.

Establish `h2 : (d : ℝ) * φ.evalZ ρ ≠ (∑ i, ρ (a i) (a i) : ℤ)` using `fun he => by`. Take `⟨k, c, hk, hc⟩` from `hS.only ρ hm hp he`. Take `⟨j, hj⟩` from `intCone_face O bar φ X hF 1 r ![ρ] γ hρ hγ ![k] c (by simp [hk]) (by simpa using hc) 0`. Conclude with `hne j hj`. Establish `h3` using `hM ρ hρ`.

Establish `h4` using `(abs_le.1 (hC ρ hm.1 hp)).1`. Rewrite `h1`, `h2`, `h3`, the goal using `[hn]`. Generalize the expression as in `∑ i, ρ (a i) (a i) = L at *`. Establish `h1' : (d : ℤ) * n ≤ L` using `by exact_mod_cast h1`. Establish `h2' : (d : ℤ) * n ≠ L` using `by exact_mod_cast h2`.

Establish `h3' : (n : ℤ) ≤ M` using `by exact_mod_cast h3`. Establish `hD' : (C : ℤ) + (K.natAbs : ℕ) + C * d * M ≤ D` using `by exact_mod_cast hD`. Establish `h5 : 0 ≤ L - d * n - 1` using `by omega`. Establish `h6 : (C : ℤ) * d * n ≤ C * d * M` using `mul_le_mul_of_nonneg_left h3' (by positivity)`. Establish `h7 : (0 : ℤ) ≤ C * d * M` using `by positivity`.

Establish `h8 : (0 : ℤ) ≤ (K.natAbs : ℕ)` using `by positivity`. Establish `h9 : 0 ≤ ((D : ℤ) - C) * (L - d * n - 1)` using `mul_nonneg (by linarith) h5`. Establish `: (D * d : ℤ) * n + (K.natAbs : ℕ) ≤ D * L + lam ρ` using `by nlinarith`. Establish `h10` using `(Int.cast_le (R := ℝ)).2 this`. Rewrite `h10` using `[Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]`. Then use the resulting hypothesis.

Use `⟨fun β hβ hp => ?_, fun ρ hρ hne => le_trans ?_ (hray ρ hρ hne)⟩` and prove the remaining obligations. Take `⟨s, δ, n, hδ, rfl⟩` from `exists_cone_nat hF hβ hp`. Establish `hall : ∀ i, (D * d : ℝ) * φ.evalZ (δ i) ≤ (D * ∑ l, δ i (a l) (a l) + lam (δ i) : ℤ)`. Introduce `i`. Distinguish the cases in `h : ∃ j, δ i = γ j`.

Take `⟨j, hj⟩` from `h`. Rewrite using `[hj, mul_assoc, hS.eq j]`. Use `hlam j` as an intermediate fact. Conclude with `(le_add_of_nonneg_right this)` after adjusting the coercions. Use `push_neg at h`.

Establish `hc : IsCone bar φ ![δ i]`. Use `hF.face _ _ δ ⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩ hδ` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Use `fin_cases u`.

Both sides reduce to the same expression. Conclude with `le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (hray _ hc h)`. Rewrite using `[intCone_evalZ_sum hδ.linear, Finset.mul_sum]`. Establish `e : (D * ∑ l, (∑ i, n i • δ i) (a l) (a l) + lam (∑ i, n i • δ i) : ℤ) = ∑ i, (n i : ℤ) * (D * ∑ l, δ i (a l) (a l) + lam (δ i))`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_nsmul, nsmul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[e, Int.cast_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Int.cast_mul, Int.cast_natCast, mul_left_comm]`. Conclude with `mul_le_mul_of_nonneg_left (hall i) (Nat.cast_nonneg _)`. Establish `: (K : ℝ) ≤ (K.natAbs : ℕ)`. Establish `h` using `(Int.cast_le (R := ℝ)).2 (Int.le_natAbs : K ≤ (K.natAbs : ℕ))`. Rewrite `h` using `[Int.cast_natCast]`. Then use the resulting hypothesis.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_gap : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a → ∀ lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (γ j)) → ∀ K : ℤ, ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (D * d : ℝ) * φ.evalZ β ≤ (D * ∑ i, β (a i) (a i) + lam β : ℤ)) ∧ ∀ (ρ : LinearMap.BilinForm ℤ X), IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) → (D * d : ℝ) * φ.evalZ ρ + K ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
  intro O _ _ _ _ bar φ d X _ _ _ _ _ _ hF r m γ a hγ hS lam hlam K
  obtain ⟨C, hC⟩ := exists_abs_lin_le hS.span lam
  obtain ⟨M, hM⟩ := exists_ray_bound hF
  refine ⟨C + K.natAbs + C * d * M, fun D hD => ?_⟩
  have hray : ∀ ρ : LinearMap.BilinForm ℤ X, IsCone bar φ ![ρ] → (∀ j, ρ ≠ γ j) →
      (D * d : ℝ) * φ.evalZ ρ + (K.natAbs : ℕ) ≤ (D * ∑ i, ρ (a i) (a i) + lam ρ : ℤ) := by
    intro ρ hρ hne
    have hm : ρ ∈ balForms bar X := hρ.mem 0
    have hp : ∀ y, 0 ≤ ρ y y := hρ.nonneg 0
    obtain ⟨n, hn⟩ := hF.exists_nat hm hp
    have h1 := hS.le ρ hm hp
    have h2 : (d : ℝ) * φ.evalZ ρ ≠ (∑ i, ρ (a i) (a i) : ℤ) := fun he => by
      obtain ⟨k, c, hk, hc⟩ := hS.only ρ hm hp he
      obtain ⟨j, hj⟩ := intCone_face O bar φ X hF 1 r ![ρ] γ hρ hγ ![k] c (by simp [hk]) (by simpa using hc) 0
      exact hne j hj
    have h3 := hM ρ hρ
    have h4 := (abs_le.1 (hC ρ hm.1 hp)).1
    rw [hn] at h1 h2 h3 ⊢
    generalize ∑ i, ρ (a i) (a i) = L at *
    have h1' : (d : ℤ) * n ≤ L := by exact_mod_cast h1
    have h2' : (d : ℤ) * n ≠ L := by exact_mod_cast h2
    have h3' : (n : ℤ) ≤ M := by exact_mod_cast h3
    have hD' : (C : ℤ) + (K.natAbs : ℕ) + C * d * M ≤ D := by exact_mod_cast hD
    have h5 : 0 ≤ L - d * n - 1 := by omega
    have h6 : (C : ℤ) * d * n ≤ C * d * M := mul_le_mul_of_nonneg_left h3' (by positivity)
    have h7 : (0 : ℤ) ≤ C * d * M := by positivity
    have h8 : (0 : ℤ) ≤ (K.natAbs : ℕ) := by positivity
    have h9 : 0 ≤ ((D : ℤ) - C) * (L - d * n - 1) := mul_nonneg (by linarith) h5
    have : (D * d : ℤ) * n + (K.natAbs : ℕ) ≤ D * L + lam ρ := by nlinarith
    have h10 := (Int.cast_le (R := ℝ)).2 this
    rwa [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast,
      Int.cast_natCast] at h10
  refine ⟨fun β hβ hp => ?_, fun ρ hρ hne => le_trans ?_ (hray ρ hρ hne)⟩
  · obtain ⟨s, δ, n, hδ, rfl⟩ := exists_cone_nat hF hβ hp
    have hall : ∀ i, (D * d : ℝ) * φ.evalZ (δ i) ≤ (D * ∑ l, δ i (a l) (a l) + lam (δ i) : ℤ) := by
      intro i
      by_cases h : ∃ j, δ i = γ j
      · obtain ⟨j, hj⟩ := h
        rw [hj, mul_assoc, hS.eq j]
        have := hlam j
        exact_mod_cast (le_add_of_nonneg_right this)
      · push_neg at h
        have hc : IsCone bar φ ![δ i] := by
          have := hF.face _ _ δ ⟨fun _ : Fin 1 => i, fun _ _ _ => Subsingleton.elim _ _⟩ hδ
          convert this using 1
          funext u
          fin_cases u
          rfl
        exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (hray _ hc h)
    rw [intCone_evalZ_sum hδ.linear, Finset.mul_sum]
    have e : (D * ∑ l, (∑ i, n i • δ i) (a l) (a l) + lam (∑ i, n i • δ i) : ℤ) =
        ∑ i, (n i : ℤ) * (D * ∑ l, δ i (a l) (a l) + lam (δ i)) := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_nsmul, nsmul_eq_mul, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e, Int.cast_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Int.cast_mul, Int.cast_natCast, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hall i) (Nat.cast_nonneg _)
  · have : (K : ℝ) ≤ (K.natAbs : ℕ) := by
      have h := (Int.cast_le (R := ℝ)).2 (Int.le_natAbs : K ≤ (K.natAbs : ℕ))
      rwa [Int.cast_natCast] at h
    linarith

end GlobalTheory.Poinc.Gap
