import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open Cardinal IntermediateField.algebraAdjoinAdjoin

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem kaehler_adjoin_subsingleton (k K : Type) [Field k] [Field K] [Algebra k K] (s : Set K)
    (hs : Submodule.span K (KaehlerDifferential.D k K '' s) = ⊤) :
    Subsingleton Ω[K⁄(IntermediateField.adjoin k s)] := by
  set L := IntermediateField.adjoin k s
  have hD : ∀ x : K, KaehlerDifferential.D L K x = 0 := by
    intro x
    have hx : KaehlerDifferential.D k K x ∈ Submodule.span K (KaehlerDifferential.D k K '' s) := by
      rw [hs]; trivial
    have h2 := Submodule.mem_map_of_mem (f := KaehlerDifferential.map k L K K) hx
    rw [Submodule.map_span, KaehlerDifferential.map_D] at h2
    have h3 : (KaehlerDifferential.map k L K K) '' (KaehlerDifferential.D k K '' s) ⊆ {0} := by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [KaehlerDifferential.map_D]
      have : y = algebraMap L K ⟨y, IntermediateField.subset_adjoin k s hy⟩ := rfl
      simp only [Algebra.algebraMap_self, RingHom.id_apply, Set.mem_singleton_iff]
      rw [this, Derivation.map_algebraMap]
    have h4 := Submodule.span_mono h3 h2
    simpa using h4
  have htop := KaehlerDifferential.span_range_derivation L K
  have hbot : Submodule.span K (Set.range (KaehlerDifferential.D L K)) = ⊥ := by
    rw [Submodule.span_eq_bot]; rintro _ ⟨x, rfl⟩; exact hD x
  rw [hbot] at htop
  constructor; intro a b
  have ha : a ∈ (⊥ : Submodule K Ω[K⁄L]) := by rw [htop]; trivial
  have hb : b ∈ (⊥ : Submodule K Ω[K⁄L]) := by rw [htop]; trivial
  rw [Submodule.mem_bot] at ha hb; rw [ha, hb]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem TrdegLe_of : TrdegLe := by
  intro k K _ _ _ _
  obtain ⟨b, hbs, hbsp, hbli⟩ := exists_linearIndependent K (Set.range (KaehlerDifferential.D k K))
  rw [KaehlerDifferential.span_range_derivation] at hbsp
  have hpre : ∀ ω : b, ∃ y : K, KaehlerDifferential.D k K y = ω := fun ω => hbs ω.2
  choose t ht using hpre
  set s : Set K := Set.range t
  have himg : KaehlerDifferential.D k K '' s = b := by
    ext ω; constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; rw [ht]; exact i.2
    · intro hω; exact ⟨t ⟨ω, hω⟩, ⟨_, rfl⟩, ht _⟩
  have hsub := kaehler_adjoin_subsingleton k K s (by rw [himg, hbsp])
  set L := IntermediateField.adjoin k s
  have : Algebra.FormallyUnramified L K := ⟨hsub⟩
  have : Algebra.EssFiniteType L K := Algebra.EssFiniteType.of_comp k L K
  have : Algebra.IsSeparable L K := (Algebra.FormallyUnramified.iff_isSeparable L K).mp inferInstance
  have : Algebra.IsAlgebraic (Algebra.adjoin k s) K := Algebra.IsAlgebraic.trans _ L K
  have h1 := Algebra.IsAlgebraic.trdeg_le_cardinalMk k s (A := K)
  have h2 : #s ≤ #b := Cardinal.mk_range_le
  have h3 : #b = (Module.finrank K Ω[K⁄k] : Cardinal) := by
    rw [Module.finrank_eq_rank, ← (Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbsp]))).mk_eq_rank'']
  exact h1.trans (h2.trans h3.le)

end LateralTheory.EtaleTrace.Cov
