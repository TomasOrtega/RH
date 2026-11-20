import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PartialTrace
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DataGenSubIrred

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Helpers
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.
-/
theorem tpsc_single_mem {S : Submodule ℂ M} {x : M} (hx : x ∈ S) (c : Fin n) :
    (Pi.single c x : Fin n → M) ∈ tensSub S := by
  refine Submodule.mem_pi.2 fun d _ => ?_
  by_cases h : d = c
  · subst h; simpa using hx
  · simp [h]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tpsc_coord_mem {S : Submodule ℂ M} {f : Fin n → M} (hf : f ∈ tensSub S) (c : Fin n) : f c ∈ S :=
  Submodule.mem_pi.1 hf c (Set.mem_univ _)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tpsc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensV E a b (Pi.single c x) = Pi.single c (E a b x) + if b = c then Pi.single a x else 0 := by
  funext d
  rw [tensV_coord]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp [Pi.single_apply, hdc, hda, hbc] <;> split_ifs <;> simp_all

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tpsc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensVd E a b (Pi.single c x) = Pi.single c (E a b x) - if a = c then Pi.single b x else 0 := by
  funext d
  rw [tensVd_coord]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp [Pi.single_apply, hdc, hdb, hac] <;> split_ifs <;> simp_all

end Helpers

def tpscK (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual (star (k c d)) (k c d)

/- English proof (translation)
Establish an intermediate fact. Split into cases according to the possible forms of the given data. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem tpscK_rows {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (c c' : Fin n) : ∑ d, tpscK dual k c' d * star (tpscK dual k c d) = if c' = c then 1 else 0 := by
  have hu : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  cases dual
  · have := congrFun (congrFun hu c') c
    simpa [tpscK, Matrix.mul_apply, Matrix.one_apply] using this
  · have := congrFun (congrFun hu c) c'
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_true, star_star]
    rw [show (∑ d, star (k c' d) * k c d) = ∑ d, k c d * star (k c' d) from
      Finset.sum_congr rfl fun d _ => mul_comm _ _, this]
    by_cases h : c' = c
    · subst h; simp
    · simp [h, Ne.symm h]

/- English proof (translation)
Establish an intermediate fact. Split into cases according to the possible forms of the given data. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem tpscK_cols {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (e d : Fin n) : ∑ c, tpscK dual k c d * star (tpscK dual k c e) = if e = d then 1 else 0 := by
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  cases dual
  · have := congrFun (congrFun hu e) d
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_false]
    rw [show (∑ c, k c d * star (k c e)) = ∑ c, star (k c e) * k c d from
      Finset.sum_congr rfl fun c _ => mul_comm _ _, this]
  · have := congrFun (congrFun hu d) e
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_true, star_star]
    rw [this]
    by_cases h : e = d
    · subst h; simp
    · simp [h, Ne.symm h]

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {A : Module.End ℂ (Fin n → D)}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ptr_mem {dual : Bool} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ x ∈ genSub E V, ptr A x ∈ genSub E V := by
  intro x hx
  rw [ptr_apply]
  exact Submodule.sum_mem _ fun c _ => tpsc_coord_mem (hA.1 _ (tpsc_single_mem hx c)) c

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem ptr_comm {dual : Bool} (hE : IsGlRep E) (hA : IsGKEndo dual ε σ E (genSub E V) A) (a b : Fin n) :
    ∀ x ∈ genSub E V, ptr A (E a b x) = E a b (ptr A x) := by
  intro x hx
  have hs : ∀ c, (Pi.single c x : Fin n → D) ∈ tensSub (genSub E V) := fun c => tpsc_single_mem hx c
  rw [ptr_apply, ptr_apply, map_sum]
  cases dual
  · have key : ∀ c, A (Pi.single c (E a b x)) c = E a b (A (Pi.single c x) c) +
        (if c = a then A (Pi.single c x) b else 0) - (if b = c then A (Pi.single a x) c else 0) := by
      intro c
      have h1 : (Pi.single c (E a b x) : Fin n → D) =
          tensV E a b (Pi.single c x) - (if b = c then Pi.single a x else 0) := by
        rw [tpsc_tensV_single]; abel
      have h2 := hA.2.1 a b _ (hs c)
      simp only [tensF, cond_false] at h2
      rw [h1, map_sub, h2, Pi.sub_apply, tensV_coord]
      split_ifs <;> simp
    simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, add_sub_cancel_right]
  · have key : ∀ c, A (Pi.single c (E a b x)) c = E a b (A (Pi.single c x) c) -
        (if c = b then A (Pi.single c x) a else 0) + (if a = c then A (Pi.single b x) c else 0) := by
      intro c
      have h1 : (Pi.single c (E a b x) : Fin n → D) =
          tensVd E a b (Pi.single c x) + (if a = c then Pi.single b x else 0) := by
        rw [tpsc_tensVd_single]; abel
      have h2 := hA.2.1 a b _ (hs c)
      simp only [tensF, cond_true] at h2
      rw [h1, map_add, h2, Pi.add_apply, tensVd_coord]
      split_ifs <;> simp
    simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_add_cancel]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tpsc_kDiag (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    kDiag dual σ k f c = ∑ d, tpscK dual k c d • σ k (f d) := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem ptr_kcomm {dual : Bool} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, (y : H) = σ k (x : H) →
      ((ptr A y : D) : H) = σ k ((ptr A x : D) : H) := by
  intro k hk x hx y hy hxy
  have hku := hk.1
  let g : Fin n → Fin n → D := fun c d => star (tpscK dual k c d) • x
  have hg : ∀ c, g c ∈ tensSub (genSub E V) := fun c =>
    Submodule.mem_pi.2 fun d _ => Submodule.smul_mem _ _ hx
  have hgs : ∀ c, g c = ∑ e, star (tpscK dual k c e) • (Pi.single e x : Fin n → D) := by
    intro c; funext d
    simp [g, Finset.sum_apply, Pi.single_apply]
  have hf' : ∀ c, (fun c' => (((Pi.single c y : Fin n → D) c' : D) : H)) =
      kDiag dual σ k (fun d => ((g c d : D) : H)) := by
    intro c; funext c'
    rw [tpsc_kDiag]
    simp only [g, Submodule.coe_smul, map_smul, smul_smul]
    rw [← Finset.sum_smul, tpscK_rows hku dual c c', ← hxy]
    by_cases h : c' = c
    · subst h; simp
    · simp [h]
  have hAf : ∀ c c', ((A (Pi.single c y) c' : D) : H) = ∑ d, tpscK dual k c' d •
      σ k (∑ e, star (tpscK dual k c e) • ((A (Pi.single e x) d : D) : H)) := by
    intro c c'
    have := congrFun (hA.2.2 k hk _ (hg c) _ (tpsc_single_mem hy c) (hf' c)) c'
    rw [this, tpsc_kDiag, hgs c]
    simp [map_sum, map_smul, Finset.sum_apply]
  rw [ptr_apply, ptr_apply, Submodule.coe_sum, Submodule.coe_sum, map_sum]
  simp only [hAf, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, tpscK_cols hku dual]
  simp [ite_smul]

end

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptr_scalar (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, ptr A x = c • x :=
  data_end_scalar hgap hσ hD hV hc hVK (ptr A) (ptr_mem hA) (fun a b => ptr_comm hD.glRep hA a b)
    (ptr_kcomm hσ hD hA)

end ReciprocityTheory.ChartRestriction.DS
