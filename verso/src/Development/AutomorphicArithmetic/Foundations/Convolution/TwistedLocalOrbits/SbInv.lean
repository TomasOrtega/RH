import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open GlobalTheory.SplitWeil

/- English proof (translation)
Introduce `G _ _ _ φ hφ K hKo hKc hG`. Take `⟨hl, hc⟩` from `hφ`. Establish `key : ∀ ψ : G × G → G, Continuous ψ → (∀ g, ψ (1, g) = g) → ∀ᶠ u in nhds (1 : G), ∀ g ∈ tsupport φ, φ (ψ (u, g)) = φ g`. Introduce `ψ hψ h1`. Apply `IsCompact.eventually_forall_of_forall_eventually hc` to reduce the goal to its premises.

Introduce `g _`. Establish `a` using `(hl.comp_continuous hψ).eventually_eq (1, g)`. Establish `b` using `(hl.comp_continuous continuous_snd).eventually_eq ((1 : G), g)`. Use `filter_upwards [a, b] with z ha hb`. Simplify using `only [Function.comp, h1] at ha hb`.

Rewrite using `[ha, hb]`. Establish `a` using `key (fun p => p.1 * p.2) (by fun_prop) (by simp)`. Establish `b` using `key (fun p => p.2 * p.1) (by fun_prop) (by simp)`. Take `⟨W, hW, hWo, hW1⟩` from `mem_nhds_iff.1 (a.and b)`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc`.

Take `⟨N, hN⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := K) (U := Subtype.val ⁻¹' W) (hWo.preimage continuous_subtype_val) hW1`. Establish `hU : ∀ u ∈ N.toSubgroup.map K.subtype, u ∈ W`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hN hx`. Use `⟨N.toSubgroup.map K.subtype, ?_, Subgroup.map_subtype_le _, fun u hu g => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `hKo.isOpenMap_subtype_val _ N.isOpen`. Distinguish the cases in `h : g ∈ tsupport φ`. Conclude with `(hW (hU u hu)).1 g h`. Distinguish the cases in `h' : u * g ∈ tsupport φ`. Use `(hW (hU _ (inv_mem hu))).1 _ h'` as an intermediate fact.

Simplify using `using this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']`. Distinguish the cases in `h : g ∈ tsupport φ`. Conclude with `(hW (hU u hu)).2 g h`. Distinguish the cases in `h' : g * u ∈ tsupport φ`.

Use `(hW (hU _ (inv_mem hu))).2 _ h'` as an intermediate fact. Simplify using `using this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']`.
-/
theorem UpperTheory.ConvolutionTheory.Loc.sbInv :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], ∀ φ ∈ SB G, ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → TotallyDisconnectedSpace G →
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ U ≤ K ∧ ∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g := by
  intro G _ _ _ φ hφ K hKo hKc hG
  obtain ⟨hl, hc⟩ := hφ
  have key : ∀ ψ : G × G → G, Continuous ψ → (∀ g, ψ (1, g) = g) → ∀ᶠ u in nhds (1 : G), ∀ g ∈ tsupport φ, φ (ψ (u, g)) = φ g := by
    intro ψ hψ h1
    apply IsCompact.eventually_forall_of_forall_eventually hc
    intro g _
    have a := (hl.comp_continuous hψ).eventually_eq (1, g)
    have b := (hl.comp_continuous continuous_snd).eventually_eq ((1 : G), g)
    filter_upwards [a, b] with z ha hb
    simp only [Function.comp, h1] at ha hb
    rw [ha, hb]
  have a := key (fun p => p.1 * p.2) (by fun_prop) (by simp)
  have b := key (fun p => p.2 * p.1) (by fun_prop) (by simp)
  obtain ⟨W, hW, hWo, hW1⟩ := mem_nhds_iff.1 (a.and b)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := K) (U := Subtype.val ⁻¹' W) (hWo.preimage continuous_subtype_val) hW1
  have hU : ∀ u ∈ N.toSubgroup.map K.subtype, u ∈ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hN hx
  refine ⟨N.toSubgroup.map K.subtype, ?_, Subgroup.map_subtype_le _, fun u hu g => ⟨?_, ?_⟩⟩
  · exact hKo.isOpenMap_subtype_val _ N.isOpen
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).1 g h
    · by_cases h' : u * g ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).1 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).2 g h
    · by_cases h' : g * u ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).2 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
