import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.HomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.Kum.xe_closed {U : Subgroup (G F Ω)} (hU : IsClosed (U : Set (G F Ω))) (n : ℕ) :
    IsClosed (levU l U n : Set (G F Ω)) := by
  have hs : (KStar.TotallyRealRoots.princ l n : Set ℤ_[l]ˣ) =
      Units.val ⁻¹' {x : ℤ_[l] | ‖x - 1‖ ≤ (l : ℝ) ^ (-(n : ℤ))} := by
    ext u
    simp only [SetLike.mem_coe, KStar.TotallyRealRoots.mem_princ, Set.mem_preimage, Set.mem_setOf_eq]
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  have hc : IsClosed (KStar.TotallyRealRoots.princ l n : Set ℤ_[l]ˣ) := by
    rw [hs]
    exact (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).preimage
      Units.continuous_val
  show IsClosed ((U : Set (G F Ω)) ∩ (cycZ F Ω l) ⁻¹' (KStar.TotallyRealRoots.princ l n : Set ℤ_[l]ˣ))
  exact hU.inter (hc.preimage (continuous_cycZ F Ω l))

omit [IsAlgClosure F Ω] in
/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem UpperTheory.V.Kum.xe_anti (U : Subgroup (G F Ω)) {a b : ℕ} (h : a ≤ b) : levU l U b ≤ levU l U a := inf_le_inf_left _ (Subgroup.comap_mono (KStar.TotallyRealRoots.princ_anti h))

omit [IsAlgClosure F Ω] in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem UpperTheory.V.Kum.xe_inter (U : Subgroup (G F Ω)) (g : G F Ω) (h : ∀ m, g ∈ levU l U m) : g ∈ cycU l U := by
  refine ⟨(h 0).1, ?_⟩
  change g ∈ (cycZ F Ω l).ker
  rw [MonoidHom.mem_ker]
  have hd : ∀ m : ℕ, (l : ℤ_[l]) ^ m ∣ ((cycZ F Ω l g : ℤ_[l]) - 1) := fun m => KStar.TotallyRealRoots.mem_princ.mp (h m).2
  by_contra hne
  have hx : ((cycZ F Ω l g : ℤ_[l]) - 1) ≠ 0 := by
    intro h0
    apply hne
    ext
    rw [sub_eq_zero] at h0
    simpa using h0
  have hv := (PadicInt.mem_span_pow_iff_le_valuation _ hx
    (PadicInt.valuation ((cycZ F Ω l g : ℤ_[l]) - 1) + 1)).mp (Ideal.mem_span_singleton.mpr (hd _))
  omega

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.Kum.xe_spread {U : Subgroup (G F Ω)} (hU : IsClosed (U : Set (G F Ω))) (n : ℕ) {M : Type} [Zero M]
    (ψ : levU l U n → M) (hψ : IsLocallyConstant ψ) {C : Set (G F Ω)} (hC : IsCompact C)
    (h : ∀ u : levU l U n, u.1 ∈ C → u.1 ∈ cycU l U → ψ u = 0) :
    ∃ m, n ≤ m ∧ ∀ u : levU l U n, u.1 ∈ C → u.1 ∈ levU l U m → ψ u = 0 := by
  have hZ : IsClosed ({u : levU l U n | ψ u = 0}ᶜ) := (hψ.isOpen_fiber 0).isClosed_compl
  have hB : IsClosed (Subtype.val '' ({u : levU l U n | ψ u = 0}ᶜ) : Set (G F Ω)) :=
    (xe_closed l hU n).isClosedMap_subtype_val _ hZ
  have hBc : IsCompact (C ∩ Subtype.val '' ({u : levU l U n | ψ u = 0}ᶜ)) := hC.inter_right hB
  obtain ⟨i, hi⟩ := hBc.elim_directed_family_closed (fun m => (levU l U (n + m) : Set (G F Ω)))
    (fun m => xe_closed l hU (n + m))
    (by
      ext g
      constructor
      · rintro ⟨⟨hgC, u, hu, rfl⟩, hall⟩
        rw [Set.mem_iInter] at hall
        exfalso
        apply hu
        apply h u hgC
        apply xe_inter l U
        intro m
        exact xe_anti l U (Nat.le_add_left m n) (hall m)
      · intro hg
        exact hg.elim)
    (fun a b => ⟨max a b, xe_anti l U (Nat.add_le_add_left (le_max_left a b) n),
      xe_anti l U (Nat.add_le_add_left (le_max_right a b) n)⟩)
  refine ⟨n + i, Nat.le_add_right n i, ?_⟩
  intro u huC hum
  by_contra hne
  have hmem : u.1 ∈ C ∩ Subtype.val '' ({u : levU l U n | ψ u = 0}ᶜ) ∩ (levU l U (n + i) : Set (G F Ω)) :=
    ⟨⟨huC, u, hne, rfl⟩, hum⟩
  rw [hi] at hmem
  exact hmem

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Kum.xdualExt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], N ≠ 0 → IsClosed (U : Set (G F Ω)) → ∀ φ ∈ XDual N (cycU l U) R M, ∃ n, ∃ ψ ∈ XDual N (levU l U n) R M, restr R M (cycU_le_levU l U n) ψ = φ := by
  intro F Ω _ _ _ _ _ l _ N U R M _ _ _ hN hU φ hφ
  obtain ⟨hφc, hφa, hφI, hφD⟩ := hφ
  obtain ⟨n, ψ, hψc, hψa, hψφ⟩ := homExt F Ω l U M φ hU hφc hφa
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hext : ∀ (g : G F Ω) (hg : g ∈ cycU l U) (hg' : g ∈ levU l U n), ψ ⟨g, hg'⟩ = φ ⟨g, hg⟩ :=
    fun g hg _ => hψφ ⟨g, hg⟩
  have hC : IsCompact ({g | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ Dec A} ∪
      {g | ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := F) A}) :=
    (decCompact F Ω N hN).1.union (decCompact F Ω l hl0).2
  obtain ⟨m, hnm, hm⟩ := xe_spread l hU n ψ hψc hC (by
    intro u huC hucyc
    rw [hext u.1 hucyc u.2]
    rcases huC with ⟨A, hA, hD⟩ | ⟨A, hA, hI⟩
    · exact hφD A hA _ hD
    · exact hφI A _ hI)
  refine ⟨m, restr R M (xe_anti l U hnm) ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hψc.comp_continuous (continuous_subtype_val.subtype_mk _)
  · intro a b
    simp only [restr, LinearMap.funLeft_apply, map_mul]
    exact hψa _ _
  · intro A u hu
    simp only [restr, LinearMap.funLeft_apply]
    by_cases hA : A.valuation (l : Ω) < 1
    · exact hm _ (Or.inr ⟨A, hA, hu⟩) u.2
    · have hker := (places F Ω l A).2.2.2 hA hu
      have hcu : (u : G F Ω) ∈ cycU l U := ⟨(inf_le_left : levU l U m ≤ U) u.2, hker⟩
      rw [show Subgroup.inclusion (xe_anti l U hnm) u = ⟨u.1, (xe_anti l U hnm) u.2⟩ from rfl, hext _ hcu]
      exact hφI A _ hu
  · intro A hA u hu
    simp only [restr, LinearMap.funLeft_apply]
    exact hm _ (Or.inl ⟨A, hA, hu⟩) u.2
  · funext u
    simp only [restr, LinearMap.funLeft_apply]
    exact hψφ u
