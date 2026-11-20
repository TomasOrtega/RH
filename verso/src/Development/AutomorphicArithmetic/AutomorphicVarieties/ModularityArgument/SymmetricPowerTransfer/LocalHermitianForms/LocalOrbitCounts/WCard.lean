import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `T Y _ _ C P F hP hFP hF hCF hPF hU`. Set `q : Y → MulAction.orbitRel.Quotient T Y` to `fun y => Quotient.mk _ y`. Establish `hq : ∀ a b : Y, q a = q b ↔ a ∈ MulAction.orbit T b`. Introduce `a b`. Rewrite using `[← MulAction.orbitRel_apply]`.

Conclude with `Quotient.eq`. Establish `hstab : ∀ (t : T) (y : Y), MulAction.stabilizer T (t • y) = MulAction.stabilizer T y`. Introduce `t y`. Use extensionality with `g`. Simplify using `only [MulAction.mem_stabilizer_iff]`.

Rewrite using `[smul_smul, mul_comm, ← smul_smul]`. Conclude with `(MulAction.injective t).eq_iff`. Establish `hstab' : ∀ a b : Y, a ∈ MulAction.orbit T b → MulAction.stabilizer T a = MulAction.stabilizer T b`. Introduce and unpack `a b ⟨s, rfl⟩`. Conclude with `hstab s b`.

Establish `hrel : ∀ z : Y, (MulAction.stabilizer T z).relIndex C = (MulAction.orbit C z).ncard`. Introduce `z`. Rewrite using `[← MulAction.index_stabilizer, Subgroup.relIndex]`. Use `congr 1`. Establish `hfib : ∀ z ∈ F, {y | y ∈ F ∧ q y = q z} = MulAction.orbit C z`.

Introduce `z hz`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, hyq⟩`. Take `⟨s, rfl⟩` from `(hq _ _).1 hyq`.

Take `⟨c, hc, hcs⟩` from `hU s z hz hy`. Conclude with `⟨⟨c, hc⟩, hcs⟩`. Introduce and unpack `⟨c, rfl⟩`. Use `⟨hCF c c.2 z hz, ?_⟩` and prove the remaining obligations. Conclude with `(hq _ _).2 ⟨(c : T), rfl⟩`.

Establish `hsupp : (Function.support fun o : MulAction.orbitRel.Quotient T Y => ((MulAction.stabilizer T (Quotient.out o)).relIndex C : ℂ) * P.indicator (fun _ => (1 : ℂ)) (Quotient.out o)) ⊆ ↑(hF.toFinset.image q)`. Introduce `o ho`. Establish `hmem : Quotient.out o ∈ P`. Assume the negation of the conclusion as `h`. Conclude with `ho (by simp [Set.indicator_of_notMem h])`.

Take `⟨t, ht⟩` from `hPF _ hmem`. Simplify using `only [Finset.coe_image, Set.Finite.coe_toFinset, Set.mem_image]`. Use `⟨t • Quotient.out o, ht, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `q (t • Quotient.out o) = o`. Use `conv_rhs => rw [← Quotient.out_eq o]`.

Conclude with `(hq _ _).2 ⟨t, rfl⟩`. Unfold `wcount`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp]`. Rewrite using `[Finset.sum_congr rfl (g := fun o => (({y ∈ hF.toFinset | q y = o}).card : ℂ))]`. Rewrite using `[← Nat.cast_sum, ← Finset.card_eq_sum_card_image, Set.ncard_eq_toFinset_card _ hF]`.

Introduce `o ho`. Take `⟨z, hz, rfl⟩` from `Finset.mem_image.1 ho`. Rewrite `hz` using `[Set.Finite.mem_toFinset]`. Establish `hzo : Quotient.out (q z) ∈ MulAction.orbit T z` using `(hq _ _).1 (Quotient.out_eq _)`. Establish `hP' : Quotient.out (q z) ∈ P`.

Take `⟨s, hs⟩` from `hzo`. Rewrite using `[← hs]`. Conclude with `hP s z (hFP hz)`. Rewrite using `[Set.indicator_of_mem hP', mul_one, hstab' _ _ hzo, hrel z, ← hfib z hz]`. Use `congr 1`.

Rewrite using `[← Set.ncard_coe_finset]`. Use `congr 1`. Use extensionality with `y`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Z.Sym.Loc.wCard :
    ∀ (T Y : Type) [CommGroup T] [MulAction T Y] (C : Subgroup T) (P F : Set Y), (∀ (t : T) y, y ∈ P → t • y ∈ P) → F ⊆ P → F.Finite →
    (∀ c ∈ C, ∀ y ∈ F, c • y ∈ F) → (∀ y ∈ P, ∃ t : T, t • y ∈ F) → (∀ (t : T), ∀ y ∈ F, t • y ∈ F → ∃ c ∈ C, c • y = t • y) →
    wcount C (P.indicator fun _ => (1 : ℂ)) = (F.ncard : ℂ) := by
  intro T Y _ _ C P F hP hFP hF hCF hPF hU
  classical
  let q : Y → MulAction.orbitRel.Quotient T Y := fun y => Quotient.mk _ y
  have hq : ∀ a b : Y, q a = q b ↔ a ∈ MulAction.orbit T b := by
    intro a b
    rw [← MulAction.orbitRel_apply]
    exact Quotient.eq
  have hstab : ∀ (t : T) (y : Y), MulAction.stabilizer T (t • y) = MulAction.stabilizer T y := by
    intro t y
    ext g
    simp only [MulAction.mem_stabilizer_iff]
    rw [smul_smul, mul_comm, ← smul_smul]
    exact (MulAction.injective t).eq_iff
  have hstab' : ∀ a b : Y, a ∈ MulAction.orbit T b →
      MulAction.stabilizer T a = MulAction.stabilizer T b := by
    rintro a b ⟨s, rfl⟩
    exact hstab s b
  have hrel : ∀ z : Y, (MulAction.stabilizer T z).relIndex C = (MulAction.orbit C z).ncard := by
    intro z
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
  have hfib : ∀ z ∈ F, {y | y ∈ F ∧ q y = q z} = MulAction.orbit C z := by
    intro z hz
    ext y
    constructor
    · rintro ⟨hy, hyq⟩
      obtain ⟨s, rfl⟩ := (hq _ _).1 hyq
      obtain ⟨c, hc, hcs⟩ := hU s z hz hy
      exact ⟨⟨c, hc⟩, hcs⟩
    · rintro ⟨c, rfl⟩
      refine ⟨hCF c c.2 z hz, ?_⟩
      exact (hq _ _).2 ⟨(c : T), rfl⟩
  have hsupp : (Function.support fun o : MulAction.orbitRel.Quotient T Y =>
      ((MulAction.stabilizer T (Quotient.out o)).relIndex C : ℂ) *
        P.indicator (fun _ => (1 : ℂ)) (Quotient.out o)) ⊆ ↑(hF.toFinset.image q) := by
    intro o ho
    have hmem : Quotient.out o ∈ P := by
      by_contra h
      exact ho (by simp [Set.indicator_of_notMem h])
    obtain ⟨t, ht⟩ := hPF _ hmem
    simp only [Finset.coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    refine ⟨t • Quotient.out o, ht, ?_⟩
    change q (t • Quotient.out o) = o
    conv_rhs => rw [← Quotient.out_eq o]
    exact (hq _ _).2 ⟨t, rfl⟩
  unfold wcount
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_congr rfl (g := fun o => (({y ∈ hF.toFinset | q y = o}).card : ℂ))]
  · rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_image, Set.ncard_eq_toFinset_card _ hF]
  · intro o ho
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ho
    rw [Set.Finite.mem_toFinset] at hz
    have hzo : Quotient.out (q z) ∈ MulAction.orbit T z := (hq _ _).1 (Quotient.out_eq _)
    have hP' : Quotient.out (q z) ∈ P := by
      obtain ⟨s, hs⟩ := hzo
      rw [← hs]
      exact hP s z (hFP hz)
    rw [Set.indicator_of_mem hP', mul_one, hstab' _ _ hzo, hrel z, ← hfib z hz]
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    simp
