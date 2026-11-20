import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScalingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroClassBoundedTorsionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleVanishesOnKerToGSOfInertiaCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotCongruentZeroIntCastMulPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualCocyclesModPrimePowUnramifiedOutsideSBouStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPrimePowTorsionSelmerClassesModPrimePowBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergWilesDualSelmerLowerBoundModPrimePowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

/- English proof (translation)
Introduce `hL l _ Ω _ _ _ e S A W hN hG`. Choose the witnesses or unpack the hypotheses as in `⟨y, hyZ, hyU, hyG, hyB⟩ : ∃ y ∈ Z1 (Loc.colRep W), Unr W y ∧ Gr W A y ∧ y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) := by`. Unfold `GrZero at hG`. Use `push_neg at hG`. Conclude with `hG`.

Establish `hcol : ∀ s (x : Fin 2 → Qbar l), Loc.colRep W s x = mat W s *ᵥ x` using `fun s x => by`. Simplify using `[Loc.colRep, Matrix.toLin'_apply]`. Take `⟨c0, hc0⟩` from `hN.int`. Take `⟨c, k, hle, hYi, hYu, -, hYg⟩` from `GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c0 y hN.cont hc0 hN.unr hyZ hyU A`. Establish `hW : ∀ s i j, mat W s i j ∈ c.O` using `fun s i j => hle (hc0 s i j)`.

Take `⟨Y, hY⟩ : ∃ Y : G ℚ Ω → Fin 2 → Qbar l, Y = fun s => ((l : ℕ) : Qbar l) ^ k • y s` from `⟨_, rfl⟩`. Establish `hYs : ∀ s, Y s = ((l : ℕ) : Qbar l) ^ k • y s` using `fun s => by rw [hY]`. Establish `hYZ : Y ∈ Z1 (Loc.colRep W)`. Establish `: Y = ((l : ℕ) : Qbar l) ^ k • y` using `by rw [hY]; rfl`. Rewrite using `[this]`.

Conclude with `(Z1 _).smul_mem _ hyZ`. Establish `hYcoc : ∀ s t, Y (s * t) = Y s + mat W s *ᵥ Y t` using `fun s t => by`. Rewrite using `[hYZ.2 s t, hcol]`. Establish `hYI : ∀ s i, Y s i ∈ c.O` using `fun s i => by`. Rewrite using `[hYs, Pi.smul_apply, smul_eq_mul]`.

Conclude with `hYi s i`. Establish `hl0 : ((l : ℕ) : Qbar l) ^ k ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Establish `hYB : Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W)`. Introduce `h`. Apply `hyB` to reduce the goal to its premises.

Rewrite `h`, the goal using `[mem_coboundaries1]`. Take `⟨x, hx⟩` from `h`. Use `⟨(((l : ℕ) : Qbar l) ^ k)⁻¹ • x, fun g => ?_⟩` and prove the remaining obligations. Establish `h1` using `hx g`. Rewrite `h1` using `[hYs]`.

Rewrite using `[map_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ hl0, one_smul]`. Take `⟨k0, hk0⟩` from `GlobalTheory.T.nonzero_class_bounded_torsion l Ω W c Y hW hYZ hYI hYB`. Establish `hY0 : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0`. Use `GlobalTheory.T.cocycle_vanishes_on_ker_toGS_of_inertia_coboundary l Ω e S A W Y hN hYZ fun q hq B hB => ?_` and prove the remaining obligations. Establish `hlq : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal` using `fun h => hq (hN.above q h)`.

Take `⟨x, -, hx⟩` from `hYu q hlq B hB`. Conclude with `⟨x, fun s hs => by rw [hYs]; exact hx s hs⟩`. Use `⟨c, hW, fun m => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `GlobalTheory.T.greenbergWiles_dualSelmer_lower_bound_mod_prime_pow hL l Ω e S A W hN c hW`. Take `⟨B, hB⟩` from `GlobalTheory.T.card_primePowTorsion_selmerClassesModPrimePow_bounded l Ω e S A W hN c hW (GlobalTheory.T.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded_alt hL l Ω e S A W hN c hW) m`.

Take `⟨t, ht⟩ : ∃ t : ℕ, t = C * B + 1` from `⟨_, rfl⟩`. Establish `hlt : C * B < l ^ t`. Use `Nat.lt_pow_self (Fact.out : l.Prime).one_lt (n := t)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hCv : ∀ {n : ℕ} (a b : Fin 2 → Qbar l), a = b → Cv n a b` using `fun a b h i => by`.

Substitute `h` using the available equality. Simplify using `[Cg]`. Set `yF : Fin (l ^ t) → G ℚ Ω → Fin 2 → Qbar l` to `fun j s => ((j : ℕ) : Qbar l) • Y s`. Establish `hjO : ∀ j : Fin (l ^ t), ((j : ℕ) : Qbar l) ∈ c.O` using `fun j => natCast_mem _ _`. Establish `hsel : ∀ j, GwCount.SelN c (t + k0) S A W (yF j)`.

Introduce `j`. Use `⟨⟨?_, fun s i => ?_, fun s _ r _ => hCv _ _ ?_⟩, fun a ha => hCv _ _ ?_, fun q _ hlq => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hYZ.1.const_smul ((j : ℕ) : Qbar l)).continuousOn`. Simplify using `only [yF, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_mem (hjO j) (hYI s i)`.

Simplify using `only [yF]`. Rewrite using `[hYcoc, smul_add, Matrix.mulVec_smul]`. Simplify using `only [yF]`. Rewrite using `[hY0 a ha, smul_zero]`. Take `⟨x, hxO, hx⟩` from `hYu q hlq (placeOf Ω q) (isPlaceOver_placeOf Ω q)`.

Use `⟨placeOf Ω q, isPlaceOver_placeOf Ω q, ((j : ℕ) : Qbar l) • x, fun i => ?_, fun s hs => hCv _ _ ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_mem (hjO j) (hxO i)`. Simplify using `only [yF]`. Rewrite using `[hYs, hx s hs, Matrix.mulVec_smul, smul_sub]`.

Take `⟨x, hxO, hx⟩` from `hYg hyG`. Use `⟨((j : ℕ) : Qbar l) * x, mul_mem (hjO j) hxO, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h1 : yF j s 1 = ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x)`. Simplify using `only [yF, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hYs, Pi.smul_apply, smul_eq_mul, hx s hs]`.

Establish `h2 : ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x) = mat W s 1 1 * (((j : ℕ) : Qbar l) * x) - ((j : ℕ) : Qbar l) * x` using `by ring`. Rewrite using `[h1, h2]`. Simplify using `[Cg]`. Establish `hne : ∀ i j, i ≠ j → ¬ Cob1 c (t + k0) W ⊤ (yF i - yF j)`. Introduce `i j hij h`.

Establish `e1 : yF i - yF j = fun s => ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : Qbar l) • Y s`. Use function extensionality and compare the values at `s`. Simplify using `only [yF, Pi.sub_apply]`. Use `push_cast`. Rewrite using `[sub_smul]`.

Rewrite `h` using `[e1]`. Establish `hd` using `hk0 (t + k0) _ (intCast_mem _ _) h`. Use `GlobalTheory.T.not_congruent_zero_intCast_mul_prime_pow l t k0 (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ?_ ?_ hd` and prove the remaining obligations. Introduce `h0`. Apply `hij` to reduce the goal to its premises.

Use `ext`. Use linear arithmetic over natural numbers and integers. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Establish `: ((l ^ t : ℕ) : ℤ) = (l : ℤ) ^ t` using `by push_cast; rfl`.

Apply the tactic sequence `rw [← this, abs_lt]; constructor <;> omega`. Take `⟨N', z, hNC, hzS, hzne⟩` from `hC (t + k0) (by omega) (l ^ t) yF hsel hne`. Establish `hex : ∃ i, ¬ Cob1 c (t + k0) (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s)`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Establish `h1` using `hB (t + k0) N' z hzS hzne h`. Establish `h2 : C * N' ≤ C * B` using `Nat.mul_le_mul_left C h1`. Use linear arithmetic over natural numbers and integers. Take `⟨i, hi⟩` from `hex`. Take `⟨h1, h2, h3, h4⟩` from `hzS i`.

Conclude with `⟨t + k0, z i, h1, h2, h3, h4, hi⟩`.
-/
theorem dual_classes_unbounded : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ¬ GrZero W A → ∃ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) ∧ ∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s) := by
  intro hL l _ Ω _ _ _ e S A W hN hG
  obtain ⟨y, hyZ, hyU, hyG, hyB⟩ : ∃ y ∈ Z1 (Loc.colRep W), Unr W y ∧ Gr W A y ∧
      y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) := by
    unfold GrZero at hG; push_neg at hG; exact hG
  have hcol : ∀ s (x : Fin 2 → Qbar l), Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  obtain ⟨c0, hc0⟩ := hN.int
  obtain ⟨c, k, hle, hYi, hYu, -, hYg⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c0 y hN.cont hc0 hN.unr hyZ hyU A
  have hW : ∀ s i j, mat W s i j ∈ c.O := fun s i j => hle (hc0 s i j)
  obtain ⟨Y, hY⟩ : ∃ Y : G ℚ Ω → Fin 2 → Qbar l, Y = fun s => ((l : ℕ) : Qbar l) ^ k • y s := ⟨_, rfl⟩
  have hYs : ∀ s, Y s = ((l : ℕ) : Qbar l) ^ k • y s := fun s => by rw [hY]
  have hYZ : Y ∈ Z1 (Loc.colRep W) := by
    have : Y = ((l : ℕ) : Qbar l) ^ k • y := by rw [hY]; rfl
    rw [this]; exact (Z1 _).smul_mem _ hyZ
  have hYcoc : ∀ s t, Y (s * t) = Y s + mat W s *ᵥ Y t := fun s t => by
    rw [hYZ.2 s t, hcol]
  have hYI : ∀ s i, Y s i ∈ c.O := fun s i => by
    rw [hYs, Pi.smul_apply, smul_eq_mul]; exact hYi s i
  have hl0 : ((l : ℕ) : Qbar l) ^ k ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hYB : Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) := by
    intro h; apply hyB
    rw [mem_coboundaries1] at h ⊢
    obtain ⟨x, hx⟩ := h
    refine ⟨(((l : ℕ) : Qbar l) ^ k)⁻¹ • x, fun g => ?_⟩
    have h1 := hx g
    rw [hYs] at h1
    rw [map_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  obtain ⟨k0, hk0⟩ := GlobalTheory.T.nonzero_class_bounded_torsion l Ω W c Y hW hYZ hYI hYB
  have hY0 : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
    refine GlobalTheory.T.cocycle_vanishes_on_ker_toGS_of_inertia_coboundary l Ω e S A W Y hN hYZ fun q hq B hB => ?_
    have hlq : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal := fun h => hq (hN.above q h)
    obtain ⟨x, -, hx⟩ := hYu q hlq B hB
    exact ⟨x, fun s hs => by rw [hYs]; exact hx s hs⟩
  refine ⟨c, hW, fun m => ?_⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.greenbergWiles_dualSelmer_lower_bound_mod_prime_pow hL l Ω e S A W hN c hW
  obtain ⟨B, hB⟩ := GlobalTheory.T.card_primePowTorsion_selmerClassesModPrimePow_bounded l Ω e S A W hN c hW (GlobalTheory.T.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded_alt hL l Ω e S A W hN c hW) m
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = C * B + 1 := ⟨_, rfl⟩
  have hlt : C * B < l ^ t := by
    have := Nat.lt_pow_self (Fact.out : l.Prime).one_lt (n := t)
    omega
  have hCv : ∀ {n : ℕ} (a b : Fin 2 → Qbar l), a = b → Cv n a b := fun a b h i => by
    subst h; simp [Cg]
  let yF : Fin (l ^ t) → G ℚ Ω → Fin 2 → Qbar l := fun j s => ((j : ℕ) : Qbar l) • Y s
  have hjO : ∀ j : Fin (l ^ t), ((j : ℕ) : Qbar l) ∈ c.O := fun j => natCast_mem _ _
  have hsel : ∀ j, GwCount.SelN c (t + k0) S A W (yF j) := by
    intro j
    refine ⟨⟨?_, fun s i => ?_, fun s _ r _ => hCv _ _ ?_⟩, fun a ha => hCv _ _ ?_, fun q _ hlq => ?_, ?_⟩
    · exact (hYZ.1.const_smul ((j : ℕ) : Qbar l)).continuousOn
    · simp only [yF, Pi.smul_apply, smul_eq_mul]; exact mul_mem (hjO j) (hYI s i)
    · simp only [yF]; rw [hYcoc, smul_add, Matrix.mulVec_smul]
    · simp only [yF]; rw [hY0 a ha, smul_zero]
    · obtain ⟨x, hxO, hx⟩ := hYu q hlq (placeOf Ω q) (isPlaceOver_placeOf Ω q)
      refine ⟨placeOf Ω q, isPlaceOver_placeOf Ω q, ((j : ℕ) : Qbar l) • x, fun i => ?_, fun s hs => hCv _ _ ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_mem (hjO j) (hxO i)
      · simp only [yF]; rw [hYs, hx s hs, Matrix.mulVec_smul, smul_sub]
    · obtain ⟨x, hxO, hx⟩ := hYg hyG
      refine ⟨((j : ℕ) : Qbar l) * x, mul_mem (hjO j) hxO, fun s hs => ?_⟩
      have h1 : yF j s 1 = ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x) := by
        simp only [yF, Pi.smul_apply, smul_eq_mul]; rw [hYs, Pi.smul_apply, smul_eq_mul, hx s hs]
      have h2 : ((j : ℕ) : Qbar l) * (mat W s 1 1 * x - x) = mat W s 1 1 * (((j : ℕ) : Qbar l) * x) - ((j : ℕ) : Qbar l) * x := by ring
      rw [h1, h2]; simp [Cg]
  have hne : ∀ i j, i ≠ j → ¬ Cob1 c (t + k0) W ⊤ (yF i - yF j) := by
    intro i j hij h
    have e1 : yF i - yF j = fun s => ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : Qbar l) • Y s := by
      funext s; simp only [yF, Pi.sub_apply]; push_cast; rw [sub_smul]
    rw [e1] at h
    have hd := hk0 (t + k0) _ (intCast_mem _ _) h
    refine GlobalTheory.T.not_congruent_zero_intCast_mul_prime_pow l t k0 (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ?_ ?_ hd
    · intro h0; apply hij; ext; omega
    · have hi := i.2; have hj := j.2
      have : ((l ^ t : ℕ) : ℤ) = (l : ℤ) ^ t := by push_cast; rfl
      rw [← this, abs_lt]; constructor <;> omega
  obtain ⟨N', z, hNC, hzS, hzne⟩ := hC (t + k0) (by omega) (l ^ t) yF hsel hne
  have hex : ∃ i, ¬ Cob1 c (t + k0) (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s) := by
    by_contra h
    push_neg at h
    have h1 := hB (t + k0) N' z hzS hzne h
    have h2 : C * N' ≤ C * B := Nat.mul_le_mul_left C h1
    omega
  obtain ⟨i, hi⟩ := hex
  obtain ⟨h1, h2, h3, h4⟩ := hzS i
  exact ⟨t + k0, z i, h1, h2, h3, h4, hi⟩

end GlobalTheory.Ord2.GwCount
