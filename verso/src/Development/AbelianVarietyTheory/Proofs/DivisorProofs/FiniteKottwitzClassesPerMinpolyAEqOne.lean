import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameElementSignAmbiguity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairFormRatioLocalScalarNormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PeriodicClassFixedPoints

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Simplify using `only [sh, map_mul, MulOpposite.unop_mul]`.
-/
theorem sh_mul' (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

/- English proof (translation)
Simplify using `[sh]`.
-/
theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by simp [sh]

/- English proof (translation)
Rewrite using `[← sh_mul', Units.inv_mul, sh_one']`.
-/
theorem sh_mul_inv' (G : HTGroup p) (e : G.Cˣ) : sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul', Units.inv_mul, sh_one']

/- English proof (translation)
Establish `hs : sh G γ = ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C c * β₁)`. Rewrite using `[← h₁]`. Simplify using `[mul_assoc]`. Rewrite `h` using `[hs, ← Algebra.smul_def, ← Algebra.smul_def]`. Simplify using `only [mul_smul_comm] at h`.

Establish `h2 : (γ : G.C) * β * (((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * β₁) = β` using `smul_right_injective G.C hc h`. Establish `h3 : (γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) = β * ((β₁⁻¹ : G.Cˣ) : G.C)` using `by conv_rhs => rw [← h2]`. Simplify using `[mul_assoc]`. Use `show (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem commute_ratio (G : HTGroup p) (β β₁ γ : G.Cˣ) (c : ℚ) (hc : c ≠ 0)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β)
    (h₁ : (γ : G.C) * β₁ * sh G γ = algebraMap ℚ G.C c * β₁) :
    Commute ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  have hs : sh G γ = ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C c * β₁) := by
    rw [← h₁]; simp [mul_assoc]
  rw [hs, ← Algebra.smul_def, ← Algebra.smul_def] at h
  simp only [mul_smul_comm] at h
  have h2 : (γ : G.C) * β * (((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * β₁) = β := smul_right_injective G.C hc h
  have h3 : (γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) = β * ((β₁⁻¹ : G.Cˣ) : G.C) := by
    conv_rhs => rw [← h2]
    simp [mul_assoc]
  show (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ
      = ((γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * γ := by rw [h3]
    _ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C)) := by simp [mul_assoc]

/- English proof (translation)
Establish `e : (β₁ : G.C) * sh G ((β₁⁻¹ : G.Cˣ) : G.C) = 1` using `by conv_lhs => rw [← h₁]`. Conclude with `sh_mul_inv' G β₁`. Rewrite using `[sh_mul', h, ← mul_assoc, e, one_mul]`.
-/
theorem tau_ratio (G : HTGroup p) (β β₁ : G.Cˣ) (h : sh G β = β) (h₁ : sh G β₁ = β₁) :
    (β₁ : G.C) * sh G ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) * ((β₁⁻¹ : G.Cˣ) : G.C) =
      (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) := by
  have e : (β₁ : G.C) * sh G ((β₁⁻¹ : G.Cˣ) : G.C) = 1 := by
    conv_lhs => rw [← h₁]
    exact sh_mul_inv' G β₁
  rw [sh_mul', h, ← mul_assoc, e, one_mul]

/- English proof (translation)
Use `⟨e' * e⁻¹, (r' : ℚ) / r, ?_, ?_, ?_⟩` and prove the remaining obligations. Break down `lt_or_gt_of_ne r.ne_zero with h | h` into its components or cases. Establish `hn : ¬ (0 < (r' : ℚ))` using `fun h0 => absurd (hr.2 h0) (not_lt.2 h.le)`. Conclude with `div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r'.ne_zero) h`. Conclude with `div_pos (hr.1 h) h`.

Rewrite using `[hQβ, hPβ, ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]`. Simplify using `only [mul_smul_comm, smul_mul_assoc, smul_smul]`. Establish `hrr : (r' : ℚ) / r * r = r'` using `by field_simp`. Rewrite using `[hrr]`. Use `congr 1`.

Rewrite using `[Units.val_mul, sh_mul']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.inv_mul, sh_mul_inv', mul_one, mul_one]`. Use `_ = _ := by simp only [mul_assoc]`. Establish `hc : Commute ((e' * e⁻¹ : G.Cˣ) : G.C) (γ₀ : G.C)`.

Rewrite using `[Units.val_mul]`. Conclude with `he'.mul_left he.units_inv_left`. Use `ext`. Rewrite using `[hP, hQ, Units.val_mul, Units.val_mul, hc.eq, mul_assoc, Units.mul_inv, mul_one]`.
-/
theorem rel_of_same (G : HTGroup p) (β₁ γ₀ : G.Cˣ) (a₀ : G.C) (P Q : Pair G) (hP : P.γ = γ₀) (hQ : Q.γ = γ₀)
    (r r' : ℚˣ) (e e' : G.Cˣ) (he : Commute (e : G.C) γ₀) (he' : Commute (e' : G.C) γ₀)
    (hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)))
    (hPβ : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * β₁ * sh G (e : G.C)))
    (hQβ : (Q.β : G.C) = algebraMap ℚ G.C r' * ((e' : G.C) * a₀ * β₁ * sh G (e' : G.C))) : Pair.Rel P Q := by
  refine ⟨e' * e⁻¹, (r' : ℚ) / r, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne r.ne_zero with h | h
    · have hn : ¬ (0 < (r' : ℚ)) := fun h0 => absurd (hr.2 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r'.ne_zero) h
    · exact div_pos (hr.1 h) h
  · rw [hQβ, hPβ, ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
    have hrr : (r' : ℚ) / r * r = r' := by field_simp
    rw [hrr]
    congr 1
    rw [Units.val_mul, sh_mul']
    calc (e' : G.C) * a₀ * β₁ * sh G (e' : G.C)
        = (e' : G.C) * (((e⁻¹ : G.Cˣ) : G.C) * e) * a₀ * β₁ * (sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C)) * sh G (e' : G.C) := by
          rw [Units.inv_mul, sh_mul_inv', mul_one, mul_one]
      _ = _ := by simp only [mul_assoc]
  · have hc : Commute ((e' * e⁻¹ : G.Cˣ) : G.C) (γ₀ : G.C) := by
      rw [Units.val_mul]; exact he'.mul_left he.units_inv_left
    ext
    rw [hP, hQ, Units.val_mul, Units.val_mul, hc.eq, mul_assoc, Units.mul_inv, mul_one]

/- English proof (translation)
Unfold `Pair.term at h`. Use `split_ifs at h with hd`. Unfold `Pair.termAt pointSum at h`. Take `⟨q, hq⟩` from `not_forall.1 (fun hc => h (finsum_eq_zero_of_forall_eq_zero hc))`. Use `⟨_, _, P.trivAf.choose_spec.choose_spec, (Quotient.out q).1, fun h0 => hq ?_⟩` and prove the remaining obligations.

Rewrite using `[h0, zero_mul, mul_zero]`. Conclude with `absurd rfl h`.
-/
theorem exists_point_of_term_ne_zero' {G : HTGroup p} (P : Pair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (h : P.term Kf f r K φ ≠ 0) :
    ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
      f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 := by
  unfold Pair.term at h
  split_ifs at h with hd
  · unfold Pair.termAt pointSum at h
    obtain ⟨q, hq⟩ := not_forall.1 (fun hc => h (finsum_eq_zero_of_forall_eq_zero hc))
    refine ⟨_, _, P.trivAf.choose_spec.choose_spec, (Quotient.out q).1, fun h0 => hq ?_⟩
    rw [h0, zero_mul, mul_zero]
  · exact absurd rfl h

/- English proof (translation)
Distinguish the cases in `hne : ∃ P₁ : Pair G, P₁.γ = γ₀ ∧ P₁.c = c₀`. Use `swap`. Use `Set.finite_empty.subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨P, -, hγ, hc, -⟩`. Conclude with `hne ⟨P, hγ, hc⟩`.

Take `⟨P₁, rfl, rfl⟩` from `hne`. Take `⟨S, hS⟩` from `GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm p G L f hf hreg P₁`. Take `⟨A, hA⟩` from `GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G P₁.β P₁.sym P₁.γ P₁.c P₁.sim P₁.reg.2 P₁.reg.1 S`. Set `D : G.C × Bool → Pair G → Prop` to `fun ab P => P.γ = P₁.γ ∧ ∃ (r : ℚˣ) (e : G.Cˣ), Commute (e : G.C) P₁.γ ∧ decide (0 < (r : ℚ)) = ab.2 ∧ (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * ab.1 * P₁.β * sh G (e : G.C))`. Set `ρ : G.C × Bool → Cls G` to `fun ab => if h : ∃ P, D ab P then Quot.mk _ h.choose else Quot.mk _ P₁`.

Use `(Finset.finite_toSet ((A ×ˢ (Finset.univ : Finset Bool)).image ρ)).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨P, rfl, hγ, hc, x, t, hx, g, hg⟩`. Establish `hcomm` using `commute_ratio G P.β P₁.β P₁.γ P₁.c P₁.c.ne_zero (by rw [← hγ, ← hc]; exact P.sim) P₁.sim`. Establish `hτ` using `tau_ratio G P.β P₁.β P.sym P₁.sym`. Establish `hu : IsUnit ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C))`.

Simplify using `using (P.β * P₁.β⁻¹).isUnit`. Take `⟨a₀, ha₀, r, e, he, hre⟩` from `hA _ hu hcomm hτ (fun ℓ _ hℓ => hS P hγ hc x t hx g hg ℓ hℓ)`. Establish `hβeq : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * P₁.β * sh G (e : G.C))`. Combine the equalities or inequalities in the displayed calculation. Establish `hex : ∃ P', D (a₀, decide (0 < (r : ℚ))) P'` using `⟨P, hγ, r, e, he, rfl, hβeq⟩`.

Use `Finset.mem_coe.2 (Finset.mem_image.2 ⟨(a₀, decide (0 < (r : ℚ))), Finset.mem_product.2 ⟨ha₀, Finset.mem_univ _⟩, ?_⟩)` and prove the remaining obligations. Establish `hρ : ρ (a₀, decide (0 < (r : ℚ))) = Quot.mk _ hex.choose` using `dif_pos hex`. Rewrite using `[hρ]`. Take `⟨hγ', r', e', he', hb', hβ'⟩` from `hex.choose_spec`. Use `Quot.sound (rel_of_same G P₁.β P₁.γ a₀ _ P hγ' hγ r' r e' e he' he ?_ hβ' hβeq)` and prove the remaining obligations.

Rewrite using `[← decide_eq_decide]`. Conclude with `hb'`.
-/
theorem finite_fixed (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (hreg : ∀ g, f g ≠ 0 → RegAf G g)
    (γ₀ : G.Cˣ) (c₀ : ℚˣ) :
    {q : Cls G | ∃ P : Pair G, (Quot.mk Pair.Rel P : Cls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
        f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0}.Finite := by
  by_cases hne : ∃ P₁ : Pair G, P₁.γ = γ₀ ∧ P₁.c = c₀
  swap
  · refine Set.finite_empty.subset ?_
    rintro q ⟨P, -, hγ, hc, -⟩
    exact hne ⟨P, hγ, hc⟩
  obtain ⟨P₁, rfl, rfl⟩ := hne
  obtain ⟨S, hS⟩ := GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm p G L f hf hreg P₁
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G P₁.β P₁.sym P₁.γ P₁.c P₁.sim P₁.reg.2 P₁.reg.1 S
  let D : G.C × Bool → Pair G → Prop := fun ab P => P.γ = P₁.γ ∧ ∃ (r : ℚˣ) (e : G.Cˣ),
    Commute (e : G.C) P₁.γ ∧ decide (0 < (r : ℚ)) = ab.2 ∧
    (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * ab.1 * P₁.β * sh G (e : G.C))
  let ρ : G.C × Bool → Cls G := fun ab => if h : ∃ P, D ab P then Quot.mk _ h.choose else Quot.mk _ P₁
  refine (Finset.finite_toSet ((A ×ˢ (Finset.univ : Finset Bool)).image ρ)).subset ?_
  rintro q ⟨P, rfl, hγ, hc, x, t, hx, g, hg⟩
  have hcomm := commute_ratio G P.β P₁.β P₁.γ P₁.c P₁.c.ne_zero (by rw [← hγ, ← hc]; exact P.sim) P₁.sim
  have hτ := tau_ratio G P.β P₁.β P.sym P₁.sym
  have hu : IsUnit ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
    simpa using (P.β * P₁.β⁻¹).isUnit
  obtain ⟨a₀, ha₀, r, e, he, hre⟩ := hA _ hu hcomm hτ (fun ℓ _ hℓ => hS P hγ hc x t hx g hg ℓ hℓ)
  have hβeq : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * P₁.β * sh G (e : G.C)) := by
    calc (P.β : G.C) = ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) * P₁.β := by simp [mul_assoc]
      _ = _ := by rw [hre]; simp [mul_assoc]
  have hex : ∃ P', D (a₀, decide (0 < (r : ℚ))) P' := ⟨P, hγ, r, e, he, rfl, hβeq⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(a₀, decide (0 < (r : ℚ))),
    Finset.mem_product.2 ⟨ha₀, Finset.mem_univ _⟩, ?_⟩)
  have hρ : ρ (a₀, decide (0 < (r : ℚ))) = Quot.mk _ hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨hγ', r', e', he', hb', hβ'⟩ := hex.choose_spec
  refine Quot.sound (rel_of_same G P₁.β P₁.γ a₀ _ P hγ' hγ r' r e' e he' he ?_ hβ' hβeq)
  rw [← decide_eq_decide]; exact hb'

/- English proof (translation)
Introduce `p _ G _ L f hf hreg K' f' _ P0`. Distinguish the cases in `hne : {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Nonempty`. Take `⟨q₀, hq₀⟩` from `hne`. Use `((finite_fixed G L f hf hreg (Quot.out q₀).γ (Quot.out q₀).c).union (finite_fixed G L f hf hreg (Quot.out q₀).γ (-(Quot.out q₀).c))).subset ?_` and prove the remaining obligations. Introduce `q hq`.

Take `⟨x, t, hx, g, hg⟩` from `exists_point_of_term_ne_zero' _ _ _ _ _ _ hq.2.2`. Take `⟨y, hy⟩` from `GlobalTheory.LKCx.ClsReg.units_conj_of_minpoly_eq_of_separable G (Quot.out q).γ (Quot.out q₀).γ (hq.1.trans hq₀.1.symm) (Quot.out q₀).reg.2 (Quot.out q₀).reg.1`. Take `⟨P', hrel, hγ, -, htr⟩` from `GlobalTheory.LKMid.Pair.exists_conj p G (Quot.out q) y⁻¹`. Take `⟨x', hx', he⟩` from `htr x t hx`. Establish `hq' : (Quot.mk Pair.Rel P' : Cls G) = q`.

Rewrite using `[← Quot.sound hrel]`. Conclude with `Quot.out_eq q`. Establish `hγ' : P'.γ = (Quot.out q₀).γ`. Rewrite using `[hγ]`. Use `ext`.

Rewrite using `[Units.val_mul, Units.val_mul, hy]`. Simplify using `[mul_assoc]`. Establish `hg' : f (g⁻¹ * P'.toAf x' t hx' P'.self * g) ≠ 0` using `by rw [he]; exact hg`. Break down `GlobalTheory.LKMid.Pair.c_eq_or_eq_neg p G (Quot.out q₀) P' hγ' with hc | hc` into its components or cases. Conclude with `Or.inl ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩`.

Conclude with `Or.inr ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩`. Rewrite `hne` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite using `[hne]`. Conclude with `Set.finite_empty`.
-/
theorem finite_classes_of_pol_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ P0 : Polynomial G.F, {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf hreg K' f' _ P0
  by_cases hne : {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧
      (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hne
    refine ((finite_fixed G L f hf hreg (Quot.out q₀).γ (Quot.out q₀).c).union
      (finite_fixed G L f hf hreg (Quot.out q₀).γ (-(Quot.out q₀).c))).subset ?_
    intro q hq
    obtain ⟨x, t, hx, g, hg⟩ := exists_point_of_term_ne_zero' _ _ _ _ _ _ hq.2.2
    obtain ⟨y, hy⟩ := GlobalTheory.LKCx.ClsReg.units_conj_of_minpoly_eq_of_separable G (Quot.out q).γ (Quot.out q₀).γ
      (hq.1.trans hq₀.1.symm) (Quot.out q₀).reg.2 (Quot.out q₀).reg.1
    obtain ⟨P', hrel, hγ, -, htr⟩ := GlobalTheory.LKMid.Pair.exists_conj p G (Quot.out q) y⁻¹
    obtain ⟨x', hx', he⟩ := htr x t hx
    have hq' : (Quot.mk Pair.Rel P' : Cls G) = q := by
      rw [← Quot.sound hrel]; exact Quot.out_eq q
    have hγ' : P'.γ = (Quot.out q₀).γ := by
      rw [hγ]; ext
      rw [Units.val_mul, Units.val_mul, hy]
      simp [mul_assoc]
    have hg' : f (g⁻¹ * P'.toAf x' t hx' P'.self * g) ≠ 0 := by rw [he]; exact hg
    rcases GlobalTheory.LKMid.Pair.c_eq_or_eq_neg p G (Quot.out q₀) P' hγ' with hc | hc
    · exact Or.inl ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
    · exact Or.inr ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Set.finite_empty

end GlobalTheory.LKCx.PeriodicClassFixedPoints
