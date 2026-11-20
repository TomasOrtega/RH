import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LabSelf

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem conj_conj (τ : E →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use the polynomial consequences of the given equalities and inequalities. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem rt_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : (starRingEnd ℂ) H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have h1 : H.rt0.re * H.rt0.im = 0 := by linarith
    have h2 : H.rt0.im = 0 := (mul_eq_zero.1 h1).resolve_left hne
    rw [h2] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨Complex.ext (by simp [h0]) (by simp), fun hz => ?_⟩
  rw [hz] at hre
  simp at hre
  exact H.d_prime.ne_zero hre

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem inPsi_or_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have h : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE]
    simp
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact Or.inl h
  · right
    rw [h, map_neg, (rt_conj H).1, neg_neg]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem not_inPsi_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {τ : E →+* ℂ} (h1 : InPsi H τ) :
    ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h2
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1, (rt_conj H).1] at h2
  exact (rt_conj H).2 (by linear_combination (-1 / 2 : ℂ) * h2)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem embK_conj {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {lv : Level H} (c : Coeff lv) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (H.bar x) := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

/- English proof (translation)
Evaluate the decidable proposition. A detailed English derivation is pending.
-/
theorem zmod_two (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s; decide

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Simplify by unfolding definitions. Apply the first step, then apply the next step to every resulting obligation. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify by unfolding definitions. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify by unfolding definitions. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Split into cases according to the possible forms of the given data. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem arithS_tauC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → PhiC N V.l → ∀ n j j' : ℕ, ArithS V io ι (⟨tauC N pl, n, j, j'⟩ : LabS E (RPl N.R)) ∧ Function.Surjective (fun x : RPl N.R × ZMod 2 => tauC N pl x.1 x.2) := by
  intro E _ _ _ H lv c N pl hP la T io C _ _ V ι _ hl hla hC n j j'
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have h10 : ¬ (1 : ZMod 2) = 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have t0 : ∀ z, tauC N pl z 0 = pl z := fun z => if_pos rfl
  have t1 : ∀ z, tauC N pl z 1 = ComplexEmbedding.conjugate (pl z) := fun z => if_neg h10
  have hpos : ∀ z, N.pos (resCharOf la) z 1 = z := by
    intro z
    unfold NumDatum.pos
    rw [← hl, hC.1, hC.2]
    simp
  have hfr : ∀ z x, V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl z)) x - emA3 io ι (pl z) x ^ V.l) := by
    intro z x
    obtain ⟨y, hy, he⟩ := hP.frob la (Or.inl (hl ▸ hC.1)) z x
    have h1 := hla y hy
    rw [he, hpos, ← hl, map_sub, map_sub, map_pow, map_pow] at h1
    exact h1
  have hem : ∀ τ x, emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (H.bar x) := by
    intro τ x
    show ι (io (embK c _ x)) = ι (io (embK c τ (H.bar x)))
    rw [embK_conj]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨z, s⟩ ⟨z', s'⟩ h
    dsimp only at h
    rcases zmod_two s with rfl | rfl <;> rcases zmod_two s' with rfl | rfl
    · rw [t0, t0] at h
      rw [hP.inj h]
    · rw [t0, t1] at h
      exact absurd (h ▸ hpsi z) (not_inPsi_conj H (hpsi z'))
    · rw [t1, t0] at h
      exact absurd (h ▸ hpsi z') (not_inPsi_conj H (hpsi z))
    · rw [t1, t1] at h
      have h' := congrArg ComplexEmbedding.conjugate h
      rw [conj_conj, conj_conj] at h'
      rw [hP.inj h']
  · intro z s
    dsimp only
    rcases zmod_two s with rfl | rfl
    · rw [zero_add, t0, t1]
    · rw [h11, t0, t1, conj_conj]
  · intro z s x
    dsimp only
    rcases zmod_two s with rfl | rfl
    · rw [zero_add, t0, t1]
      exact hfr z x
    · rw [h11, t0, t1]
      have h1 := hfr z (H.bar x)
      rwa [← hem, ← hem, conj_conj] at h1
  · have h := hC.1
    unfold NumDatum.cls primeClass at h
    refine hP.unr _ V.l_prime (fun h2 => ?_) (fun hq => ?_) (fun hd => ?_)
    · rw [if_pos h2] at h
      cases h
    · rw [if_pos hq] at h
      split_ifs at h
    · rw [if_pos hd] at h
      split_ifs at h
  · intro τ
    rcases inPsi_or_conj H τ with h | h
    · obtain ⟨z, hz⟩ := (hP.psi _).1 h
      exact ⟨(z, 0), (t0 z).trans hz⟩
    · obtain ⟨z, hz⟩ := (hP.psi _).1 h
      exact ⟨(z, 1), (t1 z).trans (by rw [hz, conj_conj])⟩

end GlobalTheory.LabSelf
