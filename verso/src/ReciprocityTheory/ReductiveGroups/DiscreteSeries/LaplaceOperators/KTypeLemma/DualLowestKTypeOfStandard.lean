import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensVdApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K2V

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

def phiR : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexRingEquiv (R := ℂ) (e := (Fin.revPerm : Fin n ≃ Fin n))).toRingHom.comp
    (starRingEnd ℂ).mapMatrix

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem phiR_apply (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    phiR g i j = star (g (Fin.rev i) (Fin.rev j)) := by
  simp [phiR, Matrix.reindexRingEquiv, Fin.revPerm_symm]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem phiR_phiR (g : Matrix (Fin n) (Fin n) ℂ) : phiR (phiR g) = g := by
  ext i j; simp [phiR_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem phiR_conjT (g : Matrix (Fin n) (Fin n) ℂ) : phiR gᴴ = (phiR g)ᴴ := by
  ext i j; simp [phiR_apply, conjTranspose_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem phiR_J (ε : Fin n → Bool) : phiR (Jm (ε ∘ Fin.rev)) = Jm ε := by
  ext i j
  by_cases h : i = j
  · subst h; simp [phiR_apply, Jm]; split_ifs <;> simp
  · simp [phiR_apply, Jm, h]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem phiR_smul_real (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    phiR ((t : ℂ) • X) = (t : ℂ) • phiR X := by
  ext i j; simp [phiR_apply]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem phiR_cont : Continuous (phiR : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  have : (phiR : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) =
      fun g => (g.submatrix Fin.rev Fin.rev).map star := by
    funext g; ext i j; simp [phiR_apply]
  rw [this]
  exact (continuous_id.matrix_submatrix _ _).matrix_map continuous_star

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem phiR_exp (A : Matrix (Fin n) (Fin n) ℂ) : phiR (NormedSpace.exp A) = NormedSpace.exp (phiR A) := by
  simp only [NormedSpace.exp_eq_tsum_rat]
  rw [Function.LeftInverse.map_tsum (g := (phiR : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ))
    _ phiR_cont phiR_cont phiR_phiR]
  simp only [map_rat_smul, map_pow]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem phiR_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset (ε ∘ Fin.rev)) :
    phiR g ∈ UJset ε := by
  have hg' : gᴴ * Jm (ε ∘ Fin.rev) * g = Jm (ε ∘ Fin.rev) := hg
  show (phiR g)ᴴ * Jm ε * phiR g = Jm ε
  rw [← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, hg']

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem phiR_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset (ε ∘ Fin.rev)) :
    phiR k ∈ Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← phiR_conjT, ← map_mul, hu, map_one]
  · rw [← phiR_J, ← map_mul, hc, map_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem phiR_G {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    inG ε (phiR X) := by
  have h : Xᴴ * Jm (ε ∘ Fin.rev) + Jm (ε ∘ Fin.rev) * X = 0 := hX
  show (phiR X)ᴴ * Jm ε + Jm ε * phiR X = 0
  rw [← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, ← map_add, h, map_zero]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Take a linear combination of the given relations to obtain the conclusion. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem actM_tw {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ M) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    actM E (phiR X) = actM (twE ε E) X := by
  have h : Xᴴ * Jm (ε ∘ Fin.rev) + Jm (ε ∘ Fin.rev) * X = 0 := hX
  have key : ∀ a b, star (X b a) = -(sg ε (Fin.rev a) * sg ε (Fin.rev b)) * X a b := by
    intro a b
    have e := congrFun (congrFun h a) b
    simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.conjTranspose_apply, Matrix.zero_apply] at e
    change star (X b a) * sg ε (Fin.rev b) + sg ε (Fin.rev a) * X a b = 0 at e
    linear_combination (sg ε (Fin.rev b)) * e - star (X b a) * sg_sq ε (Fin.rev b)
  show ∑ a, ∑ b, (phiR X) a b • E a b = ∑ a, ∑ b, X a b • twE ε E a b
  calc ∑ a, ∑ b, (phiR X) a b • E a b
      = ∑ a, ∑ b, (phiR X) (Fin.rev a) (Fin.rev b) • E (Fin.rev a) (Fin.rev b) := by
        rw [← sum_rev (fun a => ∑ b, (phiR X) a b • E a b)]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (sum_rev (fun b => (phiR X) (Fin.rev a) b • E (Fin.rev a) b)).symm
    _ = ∑ b, ∑ a, (phiR X) (Fin.rev a) (Fin.rev b) • E (Fin.rev a) (Fin.rev b) := Finset.sum_comm
    _ = ∑ a, ∑ b, X a b • twE ε E a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [phiR_apply, Fin.rev_rev, Fin.rev_rev, key]
        simp only [twE, smul_smul]
        congr 1; ring

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem urep_tw {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) : IsURepOn (UJset (ε ∘ Fin.rev)) (fun g => σ (phiR g)) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hσ
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => h3 _ (phiR_UJ hg) v, fun v => ?_⟩
  · simp only [map_one, h1]
  · simp only [map_mul]; exact h2 _ (phiR_UJ ha) _ (phiR_UJ hb)
  · exact (h4 v).comp phiR_cont.continuousOn (fun g hg => phiR_UJ hg)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem derived_tw {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E) :
    IsDerivedOn (ε ∘ Fin.rev) (fun g => σ (phiR g)) D (twE ε E) where
  glRep := twE_gl hD.glRep
  kStable := fun k hk v hv => hD.kStable _ (phiR_K hk) v hv
  deriv := fun X hX v => by
    have := hD.deriv (phiR X) (phiR_G hX) v
    rw [actM_tw E hX] at this
    have hf : (fun t : ℝ => σ (phiR (NormedSpace.exp ((t : ℂ) • X))) (v : H)) =
        fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • phiR X)) (v : H) := by
      funext t; rw [phiR_exp, phiR_smul_real]
    show HasDerivAt (fun t : ℝ => σ (phiR (NormedSpace.exp ((t : ℂ) • X))) (v : H)) _ 0
    rw [hf]; exact this

end Rep

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dualLowestKType_of_standard (hK : EigenspaceWeightConeStandard n) : EigenspaceWeightConeDual n := by
  intro ε lam h H _ _ _ σ D E V s hσ hD hV hc hVK hint hanti hgap hp hq
  have hV' : IsKIrrHW (ε ∘ Fin.rev) (twE ε E) (lowK (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a))) V := by
    rw [lowK_tw]; exact kirr_tw hV
  have hc' : ∀ v ∈ V, casimir (twE ε E) v = (casVal (fun a => -lam (Fin.rev a)) : ℂ) • v := by
    intro v hv; rw [casimir_twE, casVal_tw]; exact hc v hv
  have hint' : ∀ a, ∃ m : ℤ, (fun a => -lam (Fin.rev a)) a - ((n : ℝ) - 1) / 2 = (m : ℝ) := by
    intro a
    obtain ⟨m, hm⟩ := hint (Fin.rev a)
    refine ⟨-m - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  have hgap' := gapLap_tw hgap
  obtain ⟨K1, K2⟩ := hK (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a)) h H (fun g => σ (phiR g)) D (twE ε E) V
    (Fin.rev s) (urep_tw hσ) (derived_tw hD) hV' hc' (fun k hk v hv => hVK _ (phiR_K hk) v hv) hint'
    hgap'.1 hgap' (by rwa [pOf_tw]) (by rwa [qOf_tw])
  have hθ : thV (fun a => -lam (Fin.rev a)) (Fin.rev s) = thVd lam s := by simp [thV, thVd]
  have hG : genSub (twE ε E) V = genSub E V := genSub_tw ε E V
  have hW : lowK (ε ∘ Fin.rev) ((fun a => -lam (Fin.rev a)) + Pi.single (Fin.rev s) 1) =
      fun a => -lowK ε (lam - Pi.single s 1) (Fin.rev a) := by
    rw [← lowK_tw]
    congr 1
    funext a
    have e : (a = Fin.rev s ↔ Fin.rev a = s) :=
      ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, e]
    ring
  refine ⟨fun μ f hf hf0 hμ => ?_, fun f₁ f₂ h1 h2 hw1 hw2 => ?_⟩
  · have hf' := xs_tw (ε := ε) hf
    rw [← hθ, ← hG] at hf'
    have := K1 (fun a => -μ (Fin.rev a)) (twT ε f) hf' (fun h0 => hf0 (twT_eq_zero h0)) (khwT_tw hμ)
    rw [hW] at this
    apply cone_rev
    convert this using 1
    funext a
    simp only [Pi.sub_apply]
    ring
  · have h1' := xs_tw (ε := ε) h1
    rw [← hθ, ← hG] at h1'
    have h2' := xs_tw (ε := ε) h2
    rw [← hθ, ← hG] at h2'
    have k1 := khwT_tw hw1
    rw [← hW] at k1
    have k2 := khwT_tw hw2
    rw [← hW] at k2
    obtain ⟨c₁, c₂, hne, heq⟩ := K2 _ _ h1' h2' k1 k2
    refine ⟨c₁, c₂, hne, twT_eq_zero (ε := ε) ?_⟩
    rw [map_add, map_smul, map_smul]
    exact heq

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
