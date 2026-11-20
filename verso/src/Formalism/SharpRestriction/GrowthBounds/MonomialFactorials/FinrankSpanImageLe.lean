import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankEqSpanGen

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Dim

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Rewrite using `[g.as_sum]`. Use `Submodule.sum_mem _ fun μ hμ => ?_` and prove the remaining obligations. Establish `hsupp` using `((mem_restrictSupport_iff _).1 hg.1) (Finset.mem_coe.2 hμ)`. Establish `h1 : monomial μ (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r t b`. Use `⟨?_, ⟨monomial μ 1, by simp⟩⟩` and prove the remaining obligations.

Use `show monomial μ (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] _`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m hm`. Establish `: m = μ`. Use `support_monomial_subset hm` as an intermediate fact.

Simplify using `using this`. Rewrite using `[this]`. Conclude with `hsupp`. Establish `h2 : monomial μ (g.coeff μ) = g.coeff μ • map ι (monomial μ (1 : ℚ_[p]))`. Rewrite using `[map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h1, rfl⟩)`.
-/
theorem xi_span (ι : ℚ_[p] →+* KK O) {N r t b : ℕ} (g : MvPolynomial (BVar N r t) (KK O))
    (hg : g ∈ XiPolZ O N r t b) :
    g ∈ Submodule.span (KK O) (map ι '' (Formalism.GM.M.XiPolZ p N r t b : Set (MvPolynomial (Formalism.GM.M.BVar N r t) ℚ_[p]))) := by
  classical
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hsupp := ((mem_restrictSupport_iff _).1 hg.1) (Finset.mem_coe.2 hμ)
  have h1 : monomial μ (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r t b := by
    refine ⟨?_, ⟨monomial μ 1, by simp⟩⟩
    show monomial μ (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] _
    rw [mem_restrictSupport_iff]
    intro m hm
    have : m = μ := by
      have := support_monomial_subset hm
      simpa using this
    rw [this]
    exact hsupp
  have h2 : monomial μ (g.coeff μ) = g.coeff μ • map ι (monomial μ (1 : ℚ_[p])) := by
    rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h1, rfl⟩)

def PG {N r : ℕ} (D : BlockData N) (j : Fin (gmB D).T.t → ℕ) (jp : ℕ) :
    MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p] :=
  (∏ i, (gmB D).Ehat p (r := r) i ^ j i) * (gmB D).Eplus p (r := r) ^ jp *
    (∏ i, X (Formalism.GM.M.scalZ N r (gmB D).T.t (Fin.castSucc i)) ^ (gmB D).T.z i) *
    X (Formalism.GM.M.scalZ N r (gmB D).T.t (Fin.last (gmB D).T.t)) ^ (gmB D).zPlus

/- English proof (translation)
Use `set bW := Module.finBasis ℚ_[p] W`. Establish `h0 : f 0 = 0`. Use `hsm 0 0` as an intermediate fact. Rewrite `this` using `[zero_smul, map_zero, zero_smul]`. Then use the resulting hypothesis. Establish `hsum : ∀ (s : Finset (Fin (Module.finrank ℚ_[p] W))) (c : Fin (Module.finrank ℚ_[p] W) → ℚ_[p]), f (∑ i ∈ s, c i • (bW i : V₁)) = ∑ i ∈ s, ι (c i) • f (bW i)`.

Introduce `s c`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [h0]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsm, ih]`. Establish `hle : Submodule.span (KK O) (f '' (W : Set V₁)) ≤ Submodule.span (KK O) (Set.range fun i => f (bW i))`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Establish `hw' : (⟨w, hw⟩ : W) = ∑ i, (bW.repr ⟨w, hw⟩ i) • bW i` using `(bW.sum_repr _).symm`. Establish `hw'' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V₁)`. Establish `h3` using `congrArg (Submodule.subtype W) hw'`.

Rewrite `h3` using `[map_sum]`. Simplify `h3` using `only [Submodule.subtype_apply, map_smul]`. Rewrite using `[hw'', hsum]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `haveI : FiniteDimensional (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) := FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem finrank_span_image_le (ι : ℚ_[p] →+* KK O) {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℚ_[p] V₁]
    [AddCommGroup V₂] [Module (KK O) V₂] (f : V₁ → V₂) (hadd : ∀ u v, f (u + v) = f u + f v)
    (hsm : ∀ (c : ℚ_[p]) u, f (c • u) = ι c • f u) (W : Submodule ℚ_[p] V₁) [FiniteDimensional ℚ_[p] W] :
    Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁))) ≤ Module.finrank ℚ_[p] W := by
  classical
  set bW := Module.finBasis ℚ_[p] W
  have h0 : f 0 = 0 := by
    have := hsm 0 0
    rwa [zero_smul, map_zero, zero_smul] at this
  have hsum : ∀ (s : Finset (Fin (Module.finrank ℚ_[p] W))) (c : Fin (Module.finrank ℚ_[p] W) → ℚ_[p]),
      f (∑ i ∈ s, c i • (bW i : V₁)) = ∑ i ∈ s, ι (c i) • f (bW i) := by
    intro s c
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsm, ih]
  have hle : Submodule.span (KK O) (f '' (W : Set V₁)) ≤
      Submodule.span (KK O) (Set.range fun i => f (bW i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (⟨w, hw⟩ : W) = ∑ i, (bW.repr ⟨w, hw⟩ i) • bW i := (bW.sum_repr _).symm
    have hw'' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V₁) := by
      have h3 := congrArg (Submodule.subtype W) hw'
      rw [map_sum] at h3
      simpa only [Submodule.subtype_apply, map_smul] using h3
    rw [hw'', hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) :=
    FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)
  calc Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁)))
      ≤ Module.finrank (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank ℚ_[p] W)) := finrank_range_le_card _
    _ = Module.finrank ℚ_[p] W := Fintype.card_fin _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[show (⨆ i ∈ (∅ : Finset ι), U i) = (⊥ : Submodule K V) by simp]`. Conclude with `⟨inferInstance, by simp⟩`. Consider the case `insert a s ha ih`.

Take `⟨h1, h2⟩` from `ih fun i hi => hU i (Finset.mem_insert_of_mem hi)`. Establish `ha'` using `hU a (Finset.mem_insert_self a s)`. Rewrite using `[Finset.iSup_insert, Finset.sum_insert ha]`. Use `⟨Submodule.finiteDimensional_sup _ _, ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left h2 _)`.
-/
theorem finrank_biSup_le {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (U : ι → Submodule K V)
    (s : Finset ι) (hU : ∀ i ∈ s, FiniteDimensional K (U i)) :
    FiniteDimensional K (⨆ i ∈ s, U i : Submodule K V) ∧
      Module.finrank K (⨆ i ∈ s, U i : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), U i) = (⊥ : Submodule K V) by simp]
    exact ⟨inferInstance, by simp⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hU i (Finset.mem_insert_of_mem hi)
    have ha' := hU a (Finset.mem_insert_self a s)
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left h2 _)

end Dim

end Formalism.MainNotions.G.SymmetricFormBlocks

end
