import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qe31.Statement :
    Prop :=
    ∀ (T : Type) [inst : CommRing T] [IsNoetherianRing T] (P : Ideal T) [inst_2 : P.IsPrime] (h : ℕ) (f : Fin h → T),
      (∀ (i : Fin h), f i ∈ P) →
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
            Ideal.span
                (Set.range fun (i : Fin h) ↦
                  (Algebra.algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) ⊔
              IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ (2 : ℕ) →
          ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Qe31.proof :
    UpperTheory.Reformulated.B.Qe31.Statement := by
  intro T _ _ P _ h f _ hle
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
      Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    rwa [smul_eq_mul, ← pow_two]
  have hI : Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) =
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have key : ∀ x ∈ P, ∃ s ∉ P, s * x ∈ Ideal.span (Set.range f) := by
    intro x hx
    have h1 : algebraMap T (Localization.AtPrime P) x ∈
        (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
      rw [← hI]
      apply hm
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩ :=
      (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).1 h1
    rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hab
    obtain ⟨⟨c, hc⟩, hcab⟩ := hab
    refine ⟨c * b, P.primeCompl.mul_mem hc hb, ?_⟩
    have : c * b * x = c * a := by
      simp only at hcab
      rw [← hcab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian P
  have hSP : ∀ x ∈ S, x ∈ P := fun x hx ↦ hS ▸ Submodule.subset_span hx
  choose! g hg1 hg2 using key
  refine ⟨∏ y ∈ S, g y, P.primeCompl.prod_mem (fun y hy ↦ hg1 y (hSP y hy)), ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g hy
    rw [hc, mul_comm (g y) c, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hg2 y (hSP y hy))
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact Ideal.add_mem _ ha hb
  | smul c a _ ha =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ ha
