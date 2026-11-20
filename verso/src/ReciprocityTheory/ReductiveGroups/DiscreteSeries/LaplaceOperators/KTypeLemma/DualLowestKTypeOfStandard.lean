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
Simplify using `[phiR, Matrix.reindexRingEquiv, Fin.revPerm_symm]`.
-/
theorem phiR_apply (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    phiR g i j = star (g (Fin.rev i) (Fin.rev j)) := by
  simp [phiR, Matrix.reindexRingEquiv, Fin.revPerm_symm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[phiR_apply]`.
-/
theorem phiR_phiR (g : Matrix (Fin n) (Fin n) ℂ) : phiR (phiR g) = g := by
  ext i j; simp [phiR_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[phiR_apply, conjTranspose_apply]`.
-/
theorem phiR_conjT (g : Matrix (Fin n) (Fin n) ℂ) : phiR gᴴ = (phiR g)ᴴ := by
  ext i j; simp [phiR_apply, conjTranspose_apply]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Apply the tactic sequence `subst h; simp [phiR_apply, Jm]; split_ifs <;> simp`. Simplify using `[phiR_apply, Jm, h]`.
-/
theorem phiR_J (ε : Fin n → Bool) : phiR (Jm (ε ∘ Fin.rev)) = Jm ε := by
  ext i j
  by_cases h : i = j
  · subst h; simp [phiR_apply, Jm]; split_ifs <;> simp
  · simp [phiR_apply, Jm, h]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[phiR_apply]`.
-/
theorem phiR_smul_real (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    phiR ((t : ℂ) • X) = (t : ℂ) • phiR X := by
  ext i j; simp [phiR_apply]

/- English proof (translation)
Establish `: (phiR : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) = fun g => (g.submatrix Fin.rev Fin.rev).map star`. Use function extensionality and compare the values at `g`. Use extensionality with `i j`. Simplify using `[phiR_apply]`. Rewrite using `[this]`.

Conclude with `(continuous_id.matrix_submatrix _ _).matrix_map continuous_star`.
-/
theorem phiR_cont : Continuous (phiR : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  have : (phiR : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) =
      fun g => (g.submatrix Fin.rev Fin.rev).map star := by
    funext g; ext i j; simp [phiR_apply]
  rw [this]
  exact (continuous_id.matrix_submatrix _ _).matrix_map continuous_star

/- English proof (translation)
Simplify using `only [NormedSpace.exp_eq_tsum_rat]`. Rewrite using `[Function.LeftInverse.map_tsum (g := (phiR : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ)) _ phiR_cont phiR_cont phiR_phiR]`. Simplify using `only [map_rat_smul, map_pow]`.
-/
theorem phiR_exp (A : Matrix (Fin n) (Fin n) ℂ) : phiR (NormedSpace.exp A) = NormedSpace.exp (phiR A) := by
  simp only [NormedSpace.exp_eq_tsum_rat]
  rw [Function.LeftInverse.map_tsum (g := (phiR : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ))
    _ phiR_cont phiR_cont phiR_phiR]
  simp only [map_rat_smul, map_pow]

/- English proof (translation)
Establish `hg' : gᴴ * Jm (ε ∘ Fin.rev) * g = Jm (ε ∘ Fin.rev)` using `hg`. Use `show (phiR g)ᴴ * Jm ε * phiR g = Jm ε`. Rewrite using `[← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, hg']`.
-/
theorem phiR_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset (ε ∘ Fin.rev)) :
    phiR g ∈ UJset ε := by
  have hg' : gᴴ * Jm (ε ∘ Fin.rev) * g = Jm (ε ∘ Fin.rev) := hg
  show (phiR g)ᴴ * Jm ε * phiR g = Jm ε
  rw [← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, hg']

/- English proof (translation)
Take `⟨hu, hc⟩` from `hk`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hu`, the goal using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]`. Rewrite using `[← phiR_conjT, ← map_mul, hu, map_one]`. Rewrite using `[← phiR_J, ← map_mul, hc, map_mul]`.
-/
theorem phiR_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset (ε ∘ Fin.rev)) :
    phiR k ∈ Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← phiR_conjT, ← map_mul, hu, map_one]
  · rw [← phiR_J, ← map_mul, hc, map_mul]

/- English proof (translation)
Establish `h : Xᴴ * Jm (ε ∘ Fin.rev) + Jm (ε ∘ Fin.rev) * X = 0` using `hX`. Use `show (phiR X)ᴴ * Jm ε + Jm ε * phiR X = 0`. Rewrite using `[← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, ← map_add, h, map_zero]`.
-/
theorem phiR_G {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    inG ε (phiR X) := by
  have h : Xᴴ * Jm (ε ∘ Fin.rev) + Jm (ε ∘ Fin.rev) * X = 0 := hX
  show (phiR X)ᴴ * Jm ε + Jm ε * phiR X = 0
  rw [← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, ← map_add, h, map_zero]

/- English proof (translation)
Establish `h : Xᴴ * Jm (ε ∘ Fin.rev) + Jm (ε ∘ Fin.rev) * X = 0` using `hX`. Establish `key : ∀ a b, star (X b a) = -(sg ε (Fin.rev a) * sg ε (Fin.rev b)) * X a b`. Introduce `a b`. Establish `e` using `congrFun (congrFun h a) b`. Simplify using `only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.zero_apply] at e`.

Express the relevant statement in the definitionally equal form `star (X b a) * sg ε (Fin.rev b) + sg ε (Fin.rev a) * X a b = 0 at e`. Take the linear combination `(sg ε (Fin.rev b)) * e - star (X b a) * sg_sq ε (Fin.rev b)`. Use `show ∑ a, ∑ b, (phiR X) a b • E a b = ∑ a, ∑ b, X a b • twE ε E a b`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← sum_rev (fun a => ∑ b, (phiR X) a b • E a b)]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `(sum_rev (fun b => (phiR X) (Fin.rev a) b • E (Fin.rev a) b)).symm`. Use `_ = ∑ b, ∑ a, (phiR X) (Fin.rev a) (Fin.rev b) • E (Fin.rev a) (Fin.rev b) := Finset.sum_comm`. Use `_ = ∑ a, ∑ b, X a b • twE ε E a b := by`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[phiR_apply, Fin.rev_rev, Fin.rev_rev, key]`. Simplify using `only [twE, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
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
Take `⟨⟨h1, h2⟩, h3, h4⟩` from `hσ`. Use `⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => h3 _ (phiR_UJ hg) v, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [map_one, h1]`. Simplify using `only [map_mul]`. Conclude with `h2 _ (phiR_UJ ha) _ (phiR_UJ hb)`.

Conclude with `(h4 v).comp phiR_cont.continuousOn (fun g hg => phiR_UJ hg)`.
-/
theorem urep_tw {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) : IsURepOn (UJset (ε ∘ Fin.rev)) (fun g => σ (phiR g)) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hσ
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => h3 _ (phiR_UJ hg) v, fun v => ?_⟩
  · simp only [map_one, h1]
  · simp only [map_mul]; exact h2 _ (phiR_UJ ha) _ (phiR_UJ hb)
  · exact (h4 v).comp phiR_cont.continuousOn (fun g hg => phiR_UJ hg)

/- English proof (translation)
The claim follows from `twE_gl hD.glRep kStable := fun k hk v hv => hD.kStable _ (phiR_K hk) v hv deriv := fun X hX v => by have := hD.deriv (phiR X) (phiR_G hX) v rw [actM_tw E hX] at this have hf : (fun t : ℝ => σ (phiR (NormedSpace.exp ((t : ℂ) • X))) (v : H)) = fun t : ℝ => σ (NormedSpace.exp ((t : …`.
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
Introduce `ε lam h H _ _ _ σ D E V s hσ hD hV hc hVK hint hanti hgap hp hq`. Establish `hV' : IsKIrrHW (ε ∘ Fin.rev) (twE ε E) (lowK (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a))) V`. Rewrite using `[lowK_tw]`. Conclude with `kirr_tw hV`. Establish `hc' : ∀ v ∈ V, casimir (twE ε E) v = (casVal (fun a => -lam (Fin.rev a)) : ℂ) • v`.

Introduce `v hv`. Rewrite using `[casimir_twE, casVal_tw]`. Conclude with `hc v hv`. Establish `hint' : ∀ a, ∃ m : ℤ, (fun a => -lam (Fin.rev a)) a - ((n : ℝ) - 1) / 2 = (m : ℝ)`. Introduce `a`.

Take `⟨m, hm⟩` from `hint (Fin.rev a)`. Use `⟨-m - ((n : ℤ) - 1), ?_⟩` and prove the remaining obligations. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgap'` using `gapLap_tw hgap`.

Take `⟨K1, K2⟩` from `hK (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a)) h H (fun g => σ (phiR g)) D (twE ε E) V (Fin.rev s) (urep_tw hσ) (derived_tw hD) hV' hc' (fun k hk v hv => hVK _ (phiR_K hk) v hv) hint' hgap'.1 hgap' (by rwa [pOf_tw]) (by rwa [qOf_tw])`. Establish `hθ : thV (fun a => -lam (Fin.rev a)) (Fin.rev s) = thVd lam s` using `by simp [thV, thVd]`. Establish `hG : genSub (twE ε E) V = genSub E V` using `genSub_tw ε E V`. Establish `hW : lowK (ε ∘ Fin.rev) ((fun a => -lam (Fin.rev a)) + Pi.single (Fin.rev s) 1) = fun a => -lowK ε (lam - Pi.single s 1) (Fin.rev a)`. Rewrite using `[← lowK_tw]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Establish `e : (a = Fin.rev s ↔ Fin.rev a = s)` using `⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, e]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨fun μ f hf hf0 hμ => ?_, fun f₁ f₂ h1 h2 hw1 hw2 => ?_⟩` and prove the remaining obligations. Establish `hf'` using `xs_tw (ε := ε) hf`. Rewrite `hf'` using `[← hθ, ← hG]`. Use `K1 (fun a => -μ (Fin.rev a)) (twT ε f) hf' (fun h0 => hf0 (twT_eq_zero h0)) (khwT_tw hμ)` as an intermediate fact. Rewrite `this` using `[hW]`.

Apply `cone_rev` to reduce the goal to its premises. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1'` using `xs_tw (ε := ε) h1`. Rewrite `h1'` using `[← hθ, ← hG]`. Establish `h2'` using `xs_tw (ε := ε) h2`. Rewrite `h2'` using `[← hθ, ← hG]`. Establish `k1` using `khwT_tw hw1`.

Rewrite `k1` using `[← hW]`. Establish `k2` using `khwT_tw hw2`. Rewrite `k2` using `[← hW]`. Take `⟨c₁, c₂, hne, heq⟩` from `K2 _ _ h1' h2' k1 k2`. Use `⟨c₁, c₂, hne, twT_eq_zero (ε := ε) ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_smul, map_smul]`. Conclude with `heq`.
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
