import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.TameInertiaTowers.TowerFieldFoundations
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow

noncomputable section

open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise

namespace Formalism.BasicNotions.Examples₂

instance instFinitePsi (φ : Formalism.HC.Frame) : Finite ↥(φ.Psi) := inferInstance

instance instFintypePsi (φ : Formalism.HC.Frame) : Fintype ↥(φ.Psi) := Fintype.ofFinite _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem natCard_Psi (φ : Formalism.HC.Frame) : Nat.card ↥(φ.Psi) = 2 * φ.ord := φ.natCard_Psi

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_Psi (φ : Formalism.HC.Frame) : Fintype.card ↥(φ.Psi) = 2 * φ.ord := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_Psi φ

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem card_examplePsi_eq : Fintype.card ↥(R0.Psi) = R0.f := by
  rw [card_Psi]; rfl

section Generic

variable {R : Ranks} (H : Host R)

instance instIsCMField : IsCMField H.E := H.isCMField_hostE

instance instIsGalois : IsGalois ℚ H.E := H.hostE_isGalois

instance instTotallyComplex : IsTotallyComplex H.E := inferInstance

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cmStar_apply (x : H.E) :
    (letI := H.cmStar; star x) = IsCMField.complexConj H.E x := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem emb_star (φ : H.E →+* ℂ) (x : H.E) :
    φ (letI := H.cmStar; star x) = starRingEnd ℂ (φ x) := by
  rw [cmStar_apply]
  exact IsCMField.complexEmbedding_complexConj H.E φ x

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem emb_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = starRingEnd ℂ (φ x) :=
  H.conjE_apply φ x

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem star_eq_conj (x : H.E) : (letI := H.cmStar; star x) = H.conj x := by
  apply H.φ₀.injective
  rw [emb_star, emb_conj]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem bridgeStar : Formalism.BasicNotions.bridge_star := fun _ H x => star_eq_conj H x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem conj_aE : H.conj (H.sqq) = - H.sqq := by
  rw [H.gal_sqq]
  simp [Formalism.HC.HostRaw.conj, Formalism.HC.Frame.cc]
  have hc : ((c0.1 : ℤˣ) : ℤ) = -1 := rfl
  rw [hc]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem conj_bE : H.conj (H.sqd) = - H.sqd := by
  rw [H.gal_sqd]
  simp [Formalism.HC.HostRaw.conj, Formalism.HC.Frame.cc]
  have hc : ((c0.2 : ℤˣ) : ℤ) = -1 := rfl
  rw [hc]
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem aE_sq : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conj_eq_self_iff (x : H.E) : H.conj x = x ↔ x ∈ H.F := by
  rw [← star_eq_conj, cmStar_apply]
  exact IsCMField.complexConj_eq_self_iff H.E x

def conjF : H.E →ₐ[H.F] H.E :=
  { (H.conj : H.E →+* H.E) with
    commutes' := fun x => by
      show H.conj (x : H.E) = (x : H.E)
      exact (conj_eq_self_iff H x).2 x.2 }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjF_apply (x : H.E) : conjF H x = H.conj x := rfl

end Generic

section CM

open Polynomial

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem isIntegral_half {K : Type} [Field K] [CharZero K] (x : K) (k : ℕ)
    (hx : x ^ 2 = -(4 * (k : K) + 3)) : IsIntegral ℤ ((1 + x) / 2) := by
  refine ⟨X ^ 2 - X + C ((k : ℤ) + 1), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_natCast, Int.cast_one]
  linear_combination (1 / 4 : K) * hx

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem q_mod_four : ∃ k : ℕ, H.q = 4 * k + 3 := ⟨H.q / 4, by have := H.hyp.2.2.1; omega⟩
/- English proof (translation)
Supply the required witnesses or components.
-/
theorem d_mod_four : ∃ k : ℕ, H.d = 4 * k + 3 := ⟨H.d / 4, by have := H.hyp.2.2.2.1; omega⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isIntegral_halfA : IsIntegral ℤ ((1 + H.sqq) / 2) := by
  obtain ⟨k, hk⟩ := q_mod_four H
  exact isIntegral_half H.sqq k (by rw [aE_sq H, hk]; push_cast; ring)

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isIntegral_halfB : IsIntegral ℤ ((1 + H.sqd) / 2) := by
  obtain ⟨k, hk⟩ := d_mod_four H
  exact isIntegral_half H.sqd k (by rw [bE_sq H, hk]; push_cast; ring)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem isIntegral_halfA' : IsIntegral ℤ ((1 - H.sqq) / 2) := by
  obtain ⟨k, hk⟩ := q_mod_four H
  have h := isIntegral_half (-H.sqq) k (by rw [neg_sq, aE_sq H, hk]; push_cast; ring)
  rwa [← sub_eq_add_neg] at h

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem isIntegral_halfB' : IsIntegral ℤ ((1 - H.sqd) / 2) := by
  obtain ⟨k, hk⟩ := d_mod_four H
  have h := isIntegral_half (-H.sqd) k (by rw [neg_sq, bE_sq H, hk]; push_cast; ring)
  rwa [← sub_eq_add_neg] at h

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem conj_half (x : H.E) : H.conj ((1 + x) / 2) = (1 + H.conj x) / 2 := by
  rw [map_div₀, map_add, map_one, map_ofNat]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem unram_at (P : Ideal (𝓞 H.E)) (hP : P.IsMaximal) :
    ∃ θ t : 𝓞 H.E, algebraMap (𝓞 H.E) H.E t = H.conj (algebraMap (𝓞 H.E) H.E θ) ∧ θ - t ∉ P := by
  have h := H.der.unramEF P hP.isPrime (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField H.E))
  push Not at h
  obtain ⟨x, hx⟩ := h
  refine ⟨x, H.conj • x, rfl, fun h1 => hx ?_⟩
  rw [← neg_sub]
  exact P.neg_mem h1

/- English proof (translation)
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem cmData : @CMData H.F H.E _ _ _ _ H.cmStar _ := by
  let _ := H.cmStar
  exact
  { cmUnram := ⟨inferInstance, emb_star H, fun P hP => by
      obtain ⟨θ, t, h1, h2⟩ := unram_at H P hP
      exact ⟨θ, t, by rw [h1, star_eq_conj], h2⟩⟩
    totReal := inferInstance
    deg2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
    fixed := fun a => by
      rw [star_eq_conj, conj_eq_self_iff]
      exact ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩ }

end CM

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem layer0_ex : ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ζ a b : L),
    IsLayer 4 571 599 ζ a b := Formalism.TwoAdicCyclotomicDecomposition.layerExists 4 571 599

def L0 : Type := Classical.choose layer0_ex

instance instFieldExampleLayer : Field L0 := Classical.choose (Classical.choose_spec layer0_ex)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exampleLayer_numberField : ∃ (_ : NumberField L0) (ζ a b : L0), IsLayer 4 571 599 ζ a b :=
  Classical.choose_spec (Classical.choose_spec layer0_ex)

instance instNFL0 : NumberField L0 := Classical.choose exampleLayer_numberField

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem exampleLayer_exists_generators : ∃ (ζ a b : L0), IsLayer 4 571 599 ζ a b := by
  obtain ⟨_, h⟩ := exampleLayer_numberField
  exact h

def ζ0 : L0 := Classical.choose exampleLayer_exists_generators
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exampleLayer_exists_second : ∃ (a b : L0), IsLayer 4 571 599 ζ0 a b := Classical.choose_spec exampleLayer_exists_generators
def a0 : L0 := Classical.choose exampleLayer_exists_second
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exampleLayer_exists_third : ∃ b : L0, IsLayer 4 571 599 ζ0 a0 b := Classical.choose_spec exampleLayer_exists_second
def b0 : L0 := Classical.choose exampleLayer_exists_third
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem layer0 : IsLayer 4 571 599 ζ0 a0 b0 := Classical.choose_spec exampleLayer_exists_third

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Evaluate the numerical expressions.
-/
theorem hostHyp0 : HostHyp 571 599 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Check the signs of the components of the expression.
-/
theorem exampleCMType_nonempty : (cmType ζ0 a0 b0 599).Nonempty := by
  apply Set.nonempty_of_ncard_ne_zero
  rw [(Formalism.FrobeniusOrbits.Final.cmType 2 571 599 hostHyp0.toHypOdd L0 ζ0 a0 b0 layer0).2.1]
  positivity

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exampleIdeal_principal_factor : ∃ 𝔟 : Ideal (𝓞 (hostE ζ0 a0 b0)),
    differentIdeal (𝓞 (KinE ζ0 a0 b0)) (𝓞 (hostE ζ0 a0 b0)) =
      𝔟 * (conjE (hypOdd_of_hostHyp hostHyp0) layer0 • 𝔟) ∧
    𝔟 ⊔ conjE (hypOdd_of_hostHyp hostHyp0) layer0 • 𝔟 = ⊤ :=
  Formalism.FrobeniusOrbits.hostPrincipal 2 571 599 hostHyp0 L0 ζ0 a0 b0 layer0 _
    (galE_conjE (hypOdd_of_hostHyp hostHyp0) layer0)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem top_primitive {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 1 < m) :
    ¬ (⊤ : Ideal (𝓞 K)) ≤ Ideal.span {(m : 𝓞 K)} := by
  intro h
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {(m : 𝓞 K)} := h Submodule.mem_top
  rw [Ideal.mem_span_singleton] at h1
  obtain ⟨y, hy⟩ := h1
  have h2 := congrArg (Algebra.norm ℤ) hy
  rw [map_one, map_mul, ← map_natCast (algebraMap ℤ (𝓞 K)) m, Algebra.norm_algebraMap] at h2
  have hu : IsUnit ((m : ℤ) ^ Module.finrank ℤ (𝓞 K)) := isUnit_of_dvd_one ⟨_, h2⟩
  have hn : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hn, Int.isUnit_iff] at hu
  omega

def hostAx0 : Formalism.HC.HostAx R0.toFrame :=
  Formalism.HC.D7.hostAx R0.toFrame exampleRanks_h_injective hostHyp0 (le_refl 2) layer0

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hostAx0_cm_nonempty : hostAx0.cmType.Nonempty := by
  exact exampleCMType_nonempty

def H0 : Host R0 where
  toHostAx := hostAx0
  flPS := Formalism.HC.D7.psQ R0.toFrame exampleRanks_h_injective hostHyp0 (le_refl 2) layer0
  sqq := Formalism.HC.D7.sqq R0.toFrame exampleRanks_h_injective hostHyp0 (le_refl 2) layer0
  sqq_sq := Formalism.HC.D7.sqq_sq R0.toFrame exampleRanks_h_injective hostHyp0 (le_refl 2) layer0
  gal_sqq := Formalism.HC.D7.gal_sqq R0.toFrame hostHyp0 layer0
  QS_exact := Formalism.HC.D7.exact R0.toFrame exampleRanks_h_injective hostHyp0 (le_refl 2) layer0
  QS_le := (by norm_num : 2 ^ (2 + 2) ≤ 4 ^ 2)
  o_pow := by rw [exampleRanks_o]; norm_num
  q_ne_three := (by norm_num : (571 : ℕ) ≠ 3)
  qd_big := (by norm_num : 4 * 15 * 9 + 1 < 571 ∧ 4 * 15 * 9 + 1 < 599)
  splitBound := 2
  split_small := fun p hp h2 hle => absurd (le_antisymm hle hp.two_le) h2
  small_le := fun l hl h2 hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
      (hl.dvd_of_dvd_pow (show l ∣ 2 ^ (2 + 2) from hd))) h2
  φ₀ := hostAx0_cm_nonempty.some
  φ₀_mem := hostAx0_cm_nonempty.some_mem
  𝔟 := hostAx0.der.principal.choose
  𝔟_spec := ⟨hostAx0.der.principal.choose_spec.1, hostAx0.der.principal.choose_spec.2.1⟩
  𝔟_stable := hostAx0.der.principal.choose_spec.2.2
  levelPrimes := {751, 991, 413718278401, 603339156001, 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937}
  g := ![413718278401, 603339156001]
  g_prime := by intro i; fin_cases i; exacts [gA_prime, gB_prime]
  g_ne := by norm_num
  g_level := by intro i; fin_cases i <;> simp
  pde := 751
  pde' := 991
  pde_prime := by norm_num
  pde'_prime := by norm_num
  pde_ne := by norm_num
  pde_level := by simp
  pde_mod := by norm_num
  pde_ne_g := by intro i; fin_cases i <;> simp
  level_coprimeS := by
    intro p hp
    show Nat.Coprime p (2 ^ (2 + 2))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  ccK := ⊤
  ccK_ne_bot := top_ne_bot
  ccK_primitive := fun m hm => top_primitive m hm
  ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
  ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
  ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
  TT := ∅
  T2 := {0}
  u0 := 0
  Lw := 50
  two_le_Lw := by norm_num
  second_set_range := by intro s hs; simp at hs; subst hs; rw [exampleRanks_baseRank]; norm_num
  second_set_no_relation := by
    intro s₁ h₁ s₂ h₂ _ _ h12
    simp at h₁ h₂
    exact absurd (h₁.trans h₂.symm) h12
  CT2 := 0

def T0 : ℕ := 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem examplePrime_prime : T0.Prime := prime_large

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem examplePrime_mem_levelPrimes : T0 ∈ H0.levelPrimes := by
  simp [H0, T0]

def e0 : ℕ := 331422217405443852448534754346203940024043203756279465408

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem modulus0 : (H0.QS * H0.q * H0.d * (H0.g 0 * H0.g 1) ^ 2 : ℕ) = 340969359470621247375035755500209814839550621148435664 := by
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem exampleSqrt_sq : H0.sqd ^ 2 = -599 := by
  rw [bE_sq]
  have h : H0.d = 599 := rfl
  rw [h]
  norm_num

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem exampleSqrt_isIntegral : IsIntegral ℤ (H0.sqd) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C 599, by monicity!, ?_⟩
  simp [exampleSqrt_sq]

def π0 : H0.E := 1 + (e0 : H0.E) * H0.sqd

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem π0_integral : IsIntegral ℤ π0 := by
  unfold π0
  refine IsIntegral.add isIntegral_one (IsIntegral.mul ?_ exampleSqrt_isIntegral)
  have h := isIntegral_algebraMap (R := ℤ) (A := H0.E) (x := (e0 : ℤ))
  simpa using h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem π0_mem_K : π0 ∈ H0.K := by
  have hb : H0.sqd ∈ H0.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have h1 : (1 : H0.E) ∈ H0.K := one_mem _
  have he : (e0 : H0.E) ∈ H0.K := by simp
  exact add_mem h1 (mul_mem he hb)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem π0_norm : π0 * H0.conj π0 = (T0 : H0.E) := by
  unfold π0
  rw [map_add, map_one, map_mul, map_natCast, conj_bE]
  have h := exampleSqrt_sq
  unfold T0 e0
  push_cast
  linear_combination (-(331422217405443852448534754346203940024043203756279465408 : H0.E) ^ 2) * h

def π0O : 𝓞 H0.E := ⟨π0, π0_integral⟩

def exampleSqrtInteger : 𝓞 H0.E := ⟨H0.sqd, exampleSqrt_isIntegral⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Replace the relevant objects with their definitions.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem π0_cong : π0O - 1 ∈ Ideal.span
    {((H0.QS * H0.q * H0.d * (H0.g 0 * H0.g 1) ^ 2 : ℕ) : 𝓞 H0.E)} := by
  rw [modulus0, Ideal.mem_span_singleton]
  refine ⟨972 * exampleSqrtInteger, ?_⟩
  apply RingOfIntegers.ext
  have e1 : ((π0O - 1 : 𝓞 H0.E) : H0.E) = (e0 : H0.E) * H0.sqd := by
    show π0 - 1 = _
    unfold π0
    ring
  rw [e1]
  push_cast
  show (e0 : H0.E) * H0.sqd = (340969359470621247375035755500209814839550621148435664 : H0.E) * (972 * H0.sqd)
  unfold e0
  push_cast
  ring

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem T_norm0 : ∃ π : 𝓞 H0.E, (π : H0.E) ∈ H0.K ∧
    (π : H0.E) * H0.conj (π : H0.E) = (T0 : H0.E) ∧
    (π - 1) ∈ Ideal.span {((H0.QS * H0.q * H0.d * (H0.g 0 * H0.g 1) ^ 2 : ℕ) : 𝓞 H0.E)} :=
  ⟨π0O, π0_mem_K, π0_norm, π0_cong⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem π0_star_norm : (letI := H0.cmStar; star π0 * π0) = (T0 : H0.E) := by
  rw [star_eq_conj, mul_comm]
  exact π0_norm

/- English proof (translation)
Replace the relevant objects with their definitions. Evaluate the numerical expressions.
-/
theorem examplePrime_ge : 55 ≤ T0 := by
  unfold T0
  norm_num

end Formalism.BasicNotions.Examples₂
