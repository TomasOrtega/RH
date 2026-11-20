import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorMembership

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
The claim follows from `| [], _, x, hx => by simpa using hx | f :: l, h, x, hx => by rw [List.prod_cons, Module.End.mul_apply] exact h f List.mem_cons_self _ (list_prod_mem_of_forall l (fun g hg => h g (List.mem_cons_of_mem _ hg)) x hx)`.
-/
theorem list_prod_mem_of_forall {S : Submodule ℂ M} :
    ∀ (l : List (Module.End ℂ M)), (∀ f ∈ l, ∀ x ∈ S, f x ∈ S) → ∀ x ∈ S, l.prod x ∈ S
  | [], _, x, hx => by simpa using hx
  | f :: l, h, x, hx => by
    rw [List.prod_cons, Module.End.mul_apply]
    exact h f List.mem_cons_self _
      (list_prod_mem_of_forall l (fun g hg => h g (List.mem_cons_of_mem _ hg)) x hx)

/- English proof (translation)
Introduce `x hx`. Unfold `Capelli.capEntry`. Rewrite using `[LinearMap.add_apply]`. Use `S.add_mem (hS a b x hx) ?_` and prove the remaining obligations. Use `split_ifs`.

Simplify using `using S.smul_mem t hx`. Simplify using the standard rewrite rules.
-/
theorem capEntry_mem {n : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (t : ℂ) (a b : Fin n) :
    ∀ x ∈ S, Capelli.capEntry E t a b x ∈ S := by
  intro x hx
  unfold Capelli.capEntry
  rw [LinearMap.add_apply]
  refine S.add_mem (hS a b x hx) ?_
  split_ifs
  · simpa using S.smul_mem t hx
  · simp

/- English proof (translation)
Introduce `x hx`. Unfold `Capelli.cminor`. Rewrite using `[LinearMap.sum_apply]`. Use `S.sum_mem fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply]`.

Use `S.smul_of_tower_mem _ ?_` and prove the remaining obligations. Use `list_prod_mem_of_forall _ ?_ x hx` and prove the remaining obligations. Introduce `f hf`. Take `⟨j, rfl⟩` from `List.mem_ofFn.mp hf`. Conclude with `capEntry_mem hS _ _ _`.
-/
theorem cminor_mem {n p : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (R C : Fin p → Fin n) (t : ℂ) :
    ∀ x ∈ S, Capelli.cminor E R C t x ∈ S := by
  intro x hx
  unfold Capelli.cminor
  rw [LinearMap.sum_apply]
  refine S.sum_mem fun σ _ => ?_
  rw [LinearMap.smul_apply]
  refine S.smul_of_tower_mem _ ?_
  refine list_prod_mem_of_forall _ ?_ x hx
  intro f hf
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
  exact capEntry_mem hS _ _ _

end CapelliMinorMembership

open CapelliMinorMembership

/- English proof (translation)
Introduce `M _ _ m E S ω y β v hE hS hC hv`. Establish `h0 : Capelli.capelliC E (ω : ℂ) v = 0` using `hC v hv`. Establish `eV : Capelli.eeV E = LemK.eeV E`. Use extensionality with `f d`. Simplify using `[Capelli.eeV, LemK.eeV, LemK.prj]`.

Establish `eVd : Capelli.eeVd E = LemK.eeVd E`. Use extensionality with `f d`. Simplify using `[Capelli.eeVd, LemK.eeVd, LemK.prj]`. Prove the components needed by the constructor for the conclusion. Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mem_pi]`. Introduce `d _`. Unfold `Capelli.nnPlus`. Conclude with `S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eV, Capelli.capelliAPlus M m E y (ω : ℂ) v hE h0]`.

Simplify using the standard rewrite rules. Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_pi]`. Introduce `d _`. Unfold `Capelli.nnMinus`.

Conclude with `S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eVd, Capelli.capelliAMinus M m E β (ω : ℂ) v hE h0]`. Simplify using the standard rewrite rules.
-/
theorem eig : EigStatement := by
  intro M _ _ m E S ω y β v hE hS hC hv
  have h0 : Capelli.capelliC E (ω : ℂ) v = 0 := hC v hv
  have eV : Capelli.eeV E = LemK.eeV E := by
    ext f d; simp [Capelli.eeV, LemK.eeV, LemK.prj]
  have eVd : Capelli.eeVd E = LemK.eeVd E := by
    ext f d; simp [Capelli.eeVd, LemK.eeVd, LemK.prj]
  constructor
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnPlus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eV,
        Capelli.capelliAPlus M m E y (ω : ℂ) v hE h0]
      simp
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnMinus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eVd,
        Capelli.capelliAMinus M m E β (ω : ℂ) v hE h0]
      simp

end ReciprocityTheory.ChartRestriction.DS.Lap
