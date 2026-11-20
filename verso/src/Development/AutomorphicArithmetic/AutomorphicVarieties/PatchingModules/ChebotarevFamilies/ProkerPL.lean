import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ Γ _ _ _ _ _ I _ _ _ f H hf hfH g hg`. Unfold `PL`. Simplify using `only [Subgroup.mem_iInf]`. Introduce `U hU`. Set `φ : I →* Γ ⧸ U.toSubgroup` to `(QuotientGroup.mk' U.toSubgroup).comp f`.

Use `haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen`. Establish `hp : IsPGroup l φ.range`. Introduce and unpack `⟨y, x, rfl⟩`. Take `⟨e, he⟩` from `hU (f x) (hfH x)`. Use `⟨e, Subtype.ext ?_⟩` and prove the remaining obligations.

Use `show φ x ^ l ^ e = 1`. Rewrite using `[← map_pow]`. Use `show (QuotientGroup.mk (f (x ^ l ^ e)) : Γ ⧸ U.toSubgroup) = 1`. Rewrite using `[QuotientGroup.eq_one_iff, map_pow]`. Conclude with `he`.

Take `⟨n, hn⟩` from `IsPGroup.iff_card.1 hp`. Establish `hker : φ.ker = U.toSubgroup.comap f`. Use extensionality with `x`. Simplify using `[φ, QuotientGroup.eq_one_iff]`. Establish `hopen : IsOpen (φ.ker : Set I)`.

Rewrite using `[hker]`. Conclude with `U.isOpen.preimage hf`. Establish `h2` using `GlobalTheory.TameQuot.mem_proKer.1 hg φ.ker inferInstance hopen ⟨n, by rw [Subgroup.index_ker, hn]⟩`. Rewrite `h2` using `[hker]`. Conclude with `h2`.
-/
theorem UpperTheory.V.Pa.prokerPL :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (I : Type) [Group I] [TopologicalSpace I] [IsTopologicalGroup I] (f : I →* Γ) (H : Subgroup Γ), Continuous f → (∀ g, f g ∈ H) → ∀ g ∈ GlobalTheory.TameQuot.proKer l I, f g ∈ PL l H := by
  intro l _ Γ _ _ _ _ _ I _ _ _ f H hf hfH g hg
  unfold PL
  simp only [Subgroup.mem_iInf]
  intro U hU
  let φ : I →* Γ ⧸ U.toSubgroup := (QuotientGroup.mk' U.toSubgroup).comp f
  haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  have hp : IsPGroup l φ.range := by
    rintro ⟨y, x, rfl⟩
    obtain ⟨e, he⟩ := hU (f x) (hfH x)
    refine ⟨e, Subtype.ext ?_⟩
    show φ x ^ l ^ e = 1
    rw [← map_pow]
    show (QuotientGroup.mk (f (x ^ l ^ e)) : Γ ⧸ U.toSubgroup) = 1
    rw [QuotientGroup.eq_one_iff, map_pow]
    exact he
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  have hker : φ.ker = U.toSubgroup.comap f := by
    ext x
    simp [φ, QuotientGroup.eq_one_iff]
  have hopen : IsOpen (φ.ker : Set I) := by
    rw [hker]
    exact U.isOpen.preimage hf
  have h2 := GlobalTheory.TameQuot.mem_proKer.1 hg φ.ker inferInstance hopen
    ⟨n, by rw [Subgroup.index_ker, hn]⟩
  rw [hker] at h2
  exact h2
