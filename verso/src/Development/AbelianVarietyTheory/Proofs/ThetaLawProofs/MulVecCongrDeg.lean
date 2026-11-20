import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa.KosKer
open Matrix

/- English proof (translation)
Simplify using `only [mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Distinguish the cases in `hq : deg q = deg p + 1`. Rewrite using `[hu q hq]`. Rewrite using `[h p q hq, zero_mul, zero_mul]`.
-/
theorem mulVec_congr_deg {R Ix : Type} [CommRing R] [Fintype Ix] {deg : Ix → ℕ} {D : Matrix Ix Ix R}
    (h : ∀ p q, deg q ≠ deg p + 1 → D p q = 0) (u u' : Ix → R) (p : Ix)
    (hu : ∀ q, deg q = deg p + 1 → u q = u' q) : (D *ᵥ u) p = (D *ᵥ u') p := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : deg q = deg p + 1
  · rw [hu q hq]
  · rw [h p q hq, zero_mul, zero_mul]

/- English proof (translation)
Establish `hm : ∀ y : Ix → O, (D.map (algebraMap O (FractionRing O))) *ᵥ (algebraMap O (FractionRing O) ∘ y) = algebraMap O (FractionRing O) ∘ (D *ᵥ y)` using `fun y => funext fun p => (RingHom.map_mulVec _ D y p).symm`. Take `⟨w, hw⟩` from `h (algebraMap O (FractionRing O) ∘ x) (by rw [hm, hx]; ext p; simp)`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w`. Use `choose u hu using hb`. Use `⟨b, nonZeroDivisors.coe_ne_zero b, u, funext fun p => ?_⟩` and prove the remaining obligations.

Apply `IsFractionRing.injective O (FractionRing O)` to reduce the goal to its premises. Establish `e : algebraMap O (FractionRing O) ∘ u = (b : O) • w` using `funext hu`. Establish `e2` using `congrFun (hm u) p`. Rewrite `e2` using `[e, mulVec_smul, hw]`. Simplify using `only [Function.comp, Pi.smul_apply] at e2 ⊢`.

Rewrite using `[← e2, smul_eq_mul, map_mul, Algebra.smul_def]`.
-/
theorem clear_denom {O Ix : Type} [CommRing O] [IsDomain O] [Fintype Ix] (D : Matrix Ix Ix O)
    (h : ∀ v, (D.map (algebraMap O (FractionRing O))) *ᵥ v = 0 →
      ∃ w, (D.map (algebraMap O (FractionRing O))) *ᵥ w = v) (x : Ix → O) (hx : D *ᵥ x = 0) :
    ∃ c : O, c ≠ 0 ∧ ∃ u, D *ᵥ u = c • x := by
  have hm : ∀ y : Ix → O, (D.map (algebraMap O (FractionRing O))) *ᵥ (algebraMap O (FractionRing O) ∘ y) =
      algebraMap O (FractionRing O) ∘ (D *ᵥ y) := fun y => funext fun p => (RingHom.map_mulVec _ D y p).symm
  obtain ⟨w, hw⟩ := h (algebraMap O (FractionRing O) ∘ x) (by rw [hm, hx]; ext p; simp)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
  choose u hu using hb
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, u, funext fun p => ?_⟩
  apply IsFractionRing.injective O (FractionRing O)
  have e : algebraMap O (FractionRing O) ∘ u = (b : O) • w := funext hu
  have e2 := congrFun (hm u) p
  rw [e, mulVec_smul, hw] at e2
  simp only [Function.comp, Pi.smul_apply] at e2 ⊢
  rw [← e2, smul_eq_mul, map_mul, Algebra.smul_def]

variable {g d : ℕ} {N : ℕ → ℕ}

/- English proof (translation)
Simplify using `only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_mul, Finset.sum_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single {i}]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[if_pos ⟨by simp, by simp⟩]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Introduce `J _ hJ`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[if_neg (fun h => hJ (by simpa using h.2)), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem mulVec_empty {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin (N 0)) :
    (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩) = (∑ i, m i 0 1 *ᵥ (fun k => u (.inl ⟨{i}, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single {i}]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos ⟨by simp, by simp⟩]
    simp
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun h => hJ (by simpa using h.2)), zero_mul]
  · simp

/- English proof (translation)
Simplify using `only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero]`. Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single ∅]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos rfl]`. Both sides reduce to the same expression.

Introduce `J _ hJ`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg hJ, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem mulVec_inr {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin d) :
    (kosD m ev *ᵥ u) (.inr a) = (ev 0 *ᵥ (fun k => u (.inl ⟨∅, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_sigma, Finset.sum_eq_single ∅]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos rfl]
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg hJ, zero_mul]
  · simp

/- English proof (translation)
Simplify using `only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero, map_sum, map_mul, hu, apply_ite f, map_zero, map_pow, map_neg, map_one, Matrix.map_apply]`.
-/
theorem mulVec_inl_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d' : ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (ev' : ∀ j, Matrix (Fin d') (Fin (N j)) S)
    (u : KIx g d N → R) (u' : KIx g d' N → S) (hu : ∀ q, u' (.inl q) = f (u (.inl q))) (p) :
    (kosD (fun i j j' => (m i j j').map f) ev' *ᵥ u') (.inl p) = f ((kosD m ev *ᵥ u) (.inl p)) := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    map_sum, map_mul, hu, apply_ite f, map_zero, map_pow, map_neg, map_one, Matrix.map_apply]

/- English proof (translation)
Establish `hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ π ∣ x` using `fun x => by`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Set `u' : KIx g d N → O` to `fun q => if kdeg q = 2 then u q else 0`. Establish `h1 : ∀ a : Fin (N 0), (kosD m ev *ᵥ u') (.inl ⟨∅, a⟩) = π * v a` using `fun a => by`. Rewrite using `[hu a]`.

Conclude with `mulVec_congr_deg hD.1 _ _ _ fun q hq => if_pos hq`. Take `⟨wb, hwb⟩` from `hk (Sum.elim (fun q => IsLocalRing.residue O (u' (.inl q))) 0) (by`. Use extensionality with `p`. Break down `p with ⟨I, a⟩ | a` into its components or cases. Rewrite using `[mulVec_inl_map (IsLocalRing.residue O) m ev _ u' _ (fun _ => rfl)]`.

Distinguish the cases in `hI : I = ∅`. Substitute `hI` using the available equality. Rewrite using `[h1 a]`. Conclude with `(hres _).2 (dvd_mul_right _ _)`. Rewrite using `[mulVec_congr_deg hD.1 u' 0 _ fun q hq => if_neg ?_]`.

Simplify using the standard rewrite rules. Establish `: I.card ≠ 0` using `by simpa using hI`. Rewrite using `[hq]`. Simplify using `only [kdeg]`. Use linear arithmetic over natural numbers and integers.

Conclude with `a.elim0)`. Use `choose w0 hw0 using fun q => IsLocalRing.residue_surjective (R := O) (wb (.inl q))`. Set `w : KIx g d N → O` to `Sum.elim w0 0`. Establish `h2 : ∀ q : KIx g d N, ∃ y, kdeg q = 2 → (u' - kosD m ev *ᵥ w) q = π * y`. Introduce and unpack `(p | a)`.

Distinguish the cases in `hp : p.1 = ∅`. Use `⟨0, fun h => ?_⟩` and prove the remaining obligations. Simplify using `[kdeg, hp] at h`. Establish `e` using `hwb p hp`. Rewrite `e` using `[mulVec_inl_map (IsLocalRing.residue O) m ev _ w _ (fun q => (hw0 q).symm)]`.

Take `⟨y, hy⟩` from `(hres ((u' - kosD m ev *ᵥ w) (.inl p))).1 (by`. Rewrite using `[Pi.sub_apply, map_sub, ← e]`. Conclude with `sub_self _)`. Conclude with `⟨y, fun _ => hy⟩`. Conclude with `⟨0, fun h => by simp [kdeg] at h⟩`.

Use `choose y hy using h2`. Use `⟨y, fun a => mul_left_cancel₀ hπ.ne_zero ?_⟩` and prove the remaining obligations. Establish `e` using `mulVec_congr_deg hD.1 (u' - kosD m ev *ᵥ w) (π • y) (.inl ⟨∅, a⟩) fun q hq => hy q hq`. Rewrite `e` using `[mulVec_sub, mulVec_mulVec, hD.2, zero_mulVec, sub_zero, mulVec_smul, h1 a]`. Conclude with `e`.
-/
theorem div_unif {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O)
    (hD : IsCx kdeg (kosD m ev))
    (hk : ∀ v : KIx g 0 N → IsLocalRing.ResidueField O,
      (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p))
    {π : O} (hπ : Irreducible π) (v : Fin (N 0) → O) (u : KIx g d N → O)
    (hu : ∀ a, π * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) :
    ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
  classical
  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ π ∣ x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  let u' : KIx g d N → O := fun q => if kdeg q = 2 then u q else 0
  have h1 : ∀ a : Fin (N 0), (kosD m ev *ᵥ u') (.inl ⟨∅, a⟩) = π * v a := fun a => by
    rw [hu a]
    exact mulVec_congr_deg hD.1 _ _ _ fun q hq => if_pos hq
  obtain ⟨wb, hwb⟩ := hk (Sum.elim (fun q => IsLocalRing.residue O (u' (.inl q))) 0) (by
    ext p
    rcases p with ⟨I, a⟩ | a
    · rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ u' _ (fun _ => rfl)]
      by_cases hI : I = ∅
      · subst hI
        rw [h1 a]
        exact (hres _).2 (dvd_mul_right _ _)
      · rw [mulVec_congr_deg hD.1 u' 0 _ fun q hq => if_neg ?_]
        · simp
        · have : I.card ≠ 0 := by simpa using hI
          rw [hq]
          simp only [kdeg]
          omega
    · exact a.elim0)
  choose w0 hw0 using fun q => IsLocalRing.residue_surjective (R := O) (wb (.inl q))
  let w : KIx g d N → O := Sum.elim w0 0
  have h2 : ∀ q : KIx g d N, ∃ y, kdeg q = 2 → (u' - kosD m ev *ᵥ w) q = π * y := by
    rintro (p | a)
    · by_cases hp : p.1 = ∅
      · refine ⟨0, fun h => ?_⟩
        simp [kdeg, hp] at h
      · have e := hwb p hp
        rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ w _ (fun q => (hw0 q).symm)] at e
        obtain ⟨y, hy⟩ := (hres ((u' - kosD m ev *ᵥ w) (.inl p))).1 (by
          rw [Pi.sub_apply, map_sub, ← e]; exact sub_self _)
        exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => by simp [kdeg] at h⟩
  choose y hy using h2
  refine ⟨y, fun a => mul_left_cancel₀ hπ.ne_zero ?_⟩
  have e := mulVec_congr_deg hD.1 (u' - kosD m ev *ᵥ w) (π • y) (.inl ⟨∅, a⟩) fun q hq => hy q hq
  rw [mulVec_sub, mulVec_mulVec, hD.2, zero_mulVec, sub_zero, mulVec_smul, h1 a] at e
  exact e

/- English proof (translation)
Introduce `O _ _ _ g d N m ev hD hK hk`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hpow : ∀ (n : ℕ) (v : Fin (N 0) → O), (∃ u : KIx g d N → O, ∀ a, π ^ n * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) → ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro v h`. Simplify using `using h`. Consider the case `succ n ih`. Introduce and unpack `v ⟨u, hu⟩`. Conclude with `ih v (div_unif m ev hD hk hπ (fun a => π ^ n * v a) u fun a => by rw [← hu a]; ring)`.

Use `⟨fun v hv => ?_, ?_⟩` and prove the remaining obligations. Set `x : KIx g d N → O` to `Sum.elim (fun p => if h : p.1 = ∅ then v (Fin.cast (by rw [h]; rfl) p.2) else 0) 0`. Establish `hx0 : ∀ a : Fin (N 0), x (.inl ⟨∅, a⟩) = v a` using `fun a => by`. Simplify using `only [x, Sum.elim_inl, dif_pos]`. Both sides reduce to the same expression.

Establish `hx : kosD m ev *ᵥ x = 0`. Use extensionality with `p`. Break down `p with p | a` into its components or cases. Rewrite using `[mulVec_congr_deg hD.1 x 0 _ ?_]`. Simplify using the standard rewrite rules.

Introduce and unpack `(q | q) hq`. Use `dif_neg fun h => ?_` and prove the remaining obligations. Simplify using `[kdeg, h] at hq`. Both sides reduce to the same expression. Rewrite using `[mulVec_inr, funext hx0, hv]`.

Both sides reduce to the same expression. Take `⟨c, hc, u, hu⟩` from `clear_denom _ hK x hx`. Take `⟨n, e, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ`. Take `⟨y, hy⟩` from `hpow n v ⟨(↑e⁻¹ : O) • u, fun a => by`. Rewrite using `[mulVec_smul, hu, smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Pi.smul_apply, hx0, smul_eq_mul]⟩`.

Conclude with `⟨fun i k => y (.inl ⟨{i}, k⟩), funext fun a => (hy a).trans (mulVec_empty m ev y a)⟩`. Establish `h1 : ∀ a : Fin d, ∃ c : O, c ≠ 0 ∧ ∃ v, ev 0 *ᵥ v = c • (Pi.single a 1 : Fin d → O)`. Introduce `a`. Take `⟨c, hc, u, hu⟩` from `clear_denom _ hK (Sum.elim 0 (Pi.single a 1)) (by`. Use extensionality with `p`.

Apply the tactic sequence `rcases p with p | p <;> simp [mulVec, dotProduct, Fintype.sum_sum_type, kosD])`. Use `⟨c, hc, fun k => u (.inl ⟨∅, k⟩), funext fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[← mulVec_inr m ev u b, hu]`. Both sides reduce to the same expression. Use `choose c hc v hv using h1`.

Use `⟨∏ a, c a, Finset.prod_ne_zero_iff.2 fun a _ => hc a, fun t => ?_⟩` and prove the remaining obligations. Use `choose e he using fun a => Finset.dvd_prod_of_mem c (Finset.mem_univ a)`. Use `⟨∑ a, (t a * e a) • v a, ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_sum]`. Use extensionality with `b`.

Simplify using `only [mulVec_smul, hv, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[he b]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ker_and_image : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g d : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O), IsCx kdeg (kosD m ev) → (∀ v, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec v = 0 → ∃ w, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec w = v) → (∀ v : KIx g 0 N → IsLocalRing.ResidueField O, (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p)) → (∀ v, (ev 0).mulVec v = 0 → ∃ w : Fin g → Fin (N 1) → O, v = ∑ i, (m i 0 1).mulVec (w i)) ∧ ∃ c : O, c ≠ 0 ∧ ∀ t, ∃ v, (ev 0).mulVec v = c • t := by
  intro O _ _ _ g d N m ev hD hK hk
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpow : ∀ (n : ℕ) (v : Fin (N 0) → O), (∃ u : KIx g d N → O, ∀ a, π ^ n * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) →
      ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
    intro n
    induction n with
    | zero => intro v h; simpa using h
    | succ n ih =>
      rintro v ⟨u, hu⟩
      exact ih v (div_unif m ev hD hk hπ (fun a => π ^ n * v a) u fun a => by rw [← hu a]; ring)
  refine ⟨fun v hv => ?_, ?_⟩
  · let x : KIx g d N → O := Sum.elim (fun p => if h : p.1 = ∅ then v (Fin.cast (by rw [h]; rfl) p.2) else 0) 0
    have hx0 : ∀ a : Fin (N 0), x (.inl ⟨∅, a⟩) = v a := fun a => by
      simp only [x, Sum.elim_inl, dif_pos]
      rfl
    have hx : kosD m ev *ᵥ x = 0 := by
      ext p
      rcases p with p | a
      · rw [mulVec_congr_deg hD.1 x 0 _ ?_]
        · simp
        · rintro (q | q) hq
          · refine dif_neg fun h => ?_
            simp [kdeg, h] at hq
          · rfl
      · rw [mulVec_inr, funext hx0, hv]
        rfl
    obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK x hx
    obtain ⟨n, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
    obtain ⟨y, hy⟩ := hpow n v ⟨(↑e⁻¹ : O) • u, fun a => by
      rw [mulVec_smul, hu, smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Pi.smul_apply, hx0, smul_eq_mul]⟩
    exact ⟨fun i k => y (.inl ⟨{i}, k⟩), funext fun a => (hy a).trans (mulVec_empty m ev y a)⟩
  · have h1 : ∀ a : Fin d, ∃ c : O, c ≠ 0 ∧ ∃ v, ev 0 *ᵥ v = c • (Pi.single a 1 : Fin d → O) := by
      intro a
      obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK (Sum.elim 0 (Pi.single a 1)) (by
        ext p
        rcases p with p | p <;> simp [mulVec, dotProduct, Fintype.sum_sum_type, kosD])
      refine ⟨c, hc, fun k => u (.inl ⟨∅, k⟩), funext fun b => ?_⟩
      rw [← mulVec_inr m ev u b, hu]
      rfl
    choose c hc v hv using h1
    refine ⟨∏ a, c a, Finset.prod_ne_zero_iff.2 fun a _ => hc a, fun t => ?_⟩
    choose e he using fun a => Finset.dvd_prod_of_mem c (Finset.mem_univ a)
    refine ⟨∑ a, (t a * e a) • v a, ?_⟩
    rw [mulVec_sum]
    ext b
    simp only [mulVec_smul, hv, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [he b]
    ring

end GlobalTheory.KeyKa.KosKer
end
