import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open Cardinal IntermediateField.algebraAdjoinAdjoin

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Use `set L := IntermediateField.adjoin k s`. Establish `hD : ∀ x : K, KaehlerDifferential.D L K x = 0`. Introduce `x`. Establish `hx : KaehlerDifferential.D k K x ∈ Submodule.span K (KaehlerDifferential.D k K '' s)`. Rewrite using `[hs]`.

Discharge the goal by the elementary cases of `trivial`. Establish `h2` using `Submodule.mem_map_of_mem (f := KaehlerDifferential.map k L K K) hx`. Rewrite `h2` using `[Submodule.map_span, KaehlerDifferential.map_D]`. Establish `h3 : (KaehlerDifferential.map k L K K) '' (KaehlerDifferential.D k K '' s) ⊆ {0}`. Introduce and unpack `_ ⟨_, ⟨y, hy, rfl⟩, rfl⟩`.

Rewrite using `[KaehlerDifferential.map_D]`. Establish `: y = algebraMap L K ⟨y, IntermediateField.subset_adjoin k s hy⟩` using `rfl`. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply, Set.mem_singleton_iff]`. Rewrite using `[this, Derivation.map_algebraMap]`. Establish `h4` using `Submodule.span_mono h3 h2`.

Simplify using `using h4`. Establish `htop` using `KaehlerDifferential.span_range_derivation L K`. Establish `hbot : Submodule.span K (Set.range (KaehlerDifferential.D L K)) = ⊥`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `hD x`. Rewrite `htop` using `[hbot]`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Establish `ha : a ∈ (⊥ : Submodule K Ω[K⁄L])` using `by rw [htop]; trivial`.

Establish `hb : b ∈ (⊥ : Submodule K Ω[K⁄L])` using `by rw [htop]; trivial`. Rewrite `ha`, `hb` using `[Submodule.mem_bot]`. Rewrite using `[ha, hb]`.
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
Introduce `k K _ _ _ _`. Take `⟨b, hbs, hbsp, hbli⟩` from `exists_linearIndependent K (Set.range (KaehlerDifferential.D k K))`. Rewrite `hbsp` using `[KaehlerDifferential.span_range_derivation]`. Establish `hpre : ∀ ω : b, ∃ y : K, KaehlerDifferential.D k K y = ω` using `fun ω => hbs ω.2`. Use `choose t ht using hpre`.

Use `set s : Set K := Set.range t`. Establish `himg : KaehlerDifferential.D k K '' s = b`. Use extensionality with `ω`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨i, rfl⟩, rfl⟩`.

Rewrite using `[ht]`. Conclude with `i.2`. Introduce `hω`. Conclude with `⟨t ⟨ω, hω⟩, ⟨_, rfl⟩, ht _⟩`. Establish `hsub` using `kaehler_adjoin_subsingleton k K s (by rw [himg, hbsp])`.

Use `set L := IntermediateField.adjoin k s`. Establish `: Algebra.FormallyUnramified L K` using `⟨hsub⟩`. Establish `: Algebra.EssFiniteType L K` using `Algebra.EssFiniteType.of_comp k L K`. Establish `: Algebra.IsSeparable L K` using `(Algebra.FormallyUnramified.iff_isSeparable L K).mp inferInstance`. Establish `: Algebra.IsAlgebraic (Algebra.adjoin k s) K` using `Algebra.IsAlgebraic.trans _ L K`.

Establish `h1` using `Algebra.IsAlgebraic.trdeg_le_cardinalMk k s (A := K)`. Establish `h2 : #s ≤ #b` using `Cardinal.mk_range_le`. Establish `h3 : #b = (Module.finrank K Ω[K⁄k] : Cardinal)`. Rewrite using `[Module.finrank_eq_rank, ← (Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbsp]))).mk_eq_rank'']`. Conclude with `h1.trans (h2.trans h3.le)`.
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
