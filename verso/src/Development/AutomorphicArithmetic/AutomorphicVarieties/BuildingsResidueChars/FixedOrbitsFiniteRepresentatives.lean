import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

/- English proof (translation)
Break down `W.eq_empty_or_nonempty with hW | ⟨w, hw⟩` into its components or cases. Conclude with `⟨∅, by simp, Set.finite_empty, by simp [hW]⟩`. Use `haveI : Nonempty Z := ⟨w⟩`. Use `⟨Function.invFunOn f W '' (f '' W), ?_, h.image _, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨z, hz, rfl⟩, rfl⟩`.

Conclude with `Function.invFunOn_mem ⟨z, hz, rfl⟩`. Introduce `z hz`. Conclude with `⟨Function.invFunOn f W (f z), ⟨f z, ⟨z, hz, rfl⟩, rfl⟩, Function.invFunOn_eq ⟨z, hz, rfl⟩⟩`.
-/
private theorem fixOrb_reps {Z T : Type} (f : Z → T) (W : Set Z) (h : (f '' W).Finite) :
    ∃ B : Set Z, B ⊆ W ∧ B.Finite ∧ ∀ z ∈ W, ∃ z' ∈ B, f z' = f z := by
  classical
  rcases W.eq_empty_or_nonempty with hW | ⟨w, hw⟩
  · exact ⟨∅, by simp, Set.finite_empty, by simp [hW]⟩
  · haveI : Nonempty Z := ⟨w⟩
    refine ⟨Function.invFunOn f W '' (f '' W), ?_, h.image _, ?_⟩
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact Function.invFunOn_mem ⟨z, hz, rfl⟩
    · intro z hz
      exact ⟨Function.invFunOn f W (f z), ⟨f z, ⟨z, hz, rfl⟩, rfl⟩,
        Function.invFunOn_eq ⟨z, hz, rfl⟩⟩

/- English proof (translation)
Introduce `G Z _ _ σ s hs W hfix hstab ⟨R, hR, hRW⟩`. Establish `himg : ((fun z => MulAction.orbit G z) '' W).Finite`. Use `(hR.image (fun z => MulAction.orbit G z)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨g, hg⟩` from `hRW z hz`.

Conclude with `⟨g • z, hg, MulAction.orbit_smul g z⟩`. Take `⟨B1, hB1W, hB1, hB1r⟩` from `fixOrb_reps _ W himg`. Establish `hb : ∀ z ∈ W, ∃ b ∈ B1, ∃ h : G, h • b = z`. Introduce `z hz`. Take `⟨b, hbB, hbo⟩` from `hB1r z hz`.

Establish `hbo' : MulAction.orbit G b = MulAction.orbit G z` using `hbo`. Establish `hm : z ∈ MulAction.orbit G b`. Rewrite using `[hbo']`. Conclude with `MulAction.mem_orbit_self z`. Take `⟨h, hh⟩` from `hm`.

Conclude with `⟨b, hbB, h, hh⟩`. Set `bb : Z → Z` to `fun z => if hz : z ∈ W then (hb z hz).choose else z`. Set `hh : Z → G` to `fun z => if hz : z ∈ W then (hb z hz).choose_spec.2.choose else 1`. Establish `bbB : ∀ z ∈ W, bb z ∈ B1` using `fun z hz => by`. Simplify using `only [bb, dif_pos hz]`.

Conclude with `(hb z hz).choose_spec.1`. Establish `hhb : ∀ z ∈ W, hh z • bb z = z` using `fun z hz => by`. Simplify using `only [bb, hh, dif_pos hz]`. Conclude with `(hb z hz).choose_spec.2.choose_spec`. Establish `hcoc : ∀ z ∈ W, (hh z)⁻¹ * σ (hh z) ∈ MulAction.stabilizer G (bb z)`.

Introduce `z hz`. Establish `hbW : bb z ∈ W` using `hB1W (bbB z hz)`. Rewrite using `[MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]`. Combine the equalities or inequalities in the displayed calculation. Set `key : Z → Z × G` to `fun z => (bb z, (hh z)⁻¹ * σ (hh z))`.

Establish `hkey : (key '' W).Finite`. Use `(hB1.prod (hB1.biUnion (fun b hbB => (haveI := hstab b (hB1W hbB); Set.toFinite (MulAction.stabilizer G b : Set G))))).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `⟨bbB z hz, Set.mem_biUnion (bbB z hz) (hcoc z hz)⟩`. Take `⟨B, hBW, hB, hBr⟩` from `fixOrb_reps key W hkey`.

Use `⟨B, hB, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨z', hz'B, hk⟩` from `hBr z hz`. Establish `hz'W` using `hBW hz'B`. Simplify using `only [key, Prod.mk.injEq] at hk`. Take `⟨h1, h2⟩` from `hk`.

Use `⟨hh z' * (hh z)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `: σ (hh z') = hh z' * ((hh z)⁻¹ * σ (hh z))`. Rewrite using `[← h2, mul_inv_cancel_left]`. Rewrite using `[map_mul, map_inv, this]`. Use `group`.

Rewrite using `[mul_smul, inv_smul_eq_iff.mpr (hhb z hz).symm, ← h1, hhb z' hz'W]`. Conclude with `hz'B`.
-/
theorem UpperTheory.fixedOrbits_finite_representatives :
    UpperTheory.V.Af.BA.FixOrb := by
  classical
  intro G Z _ _ σ s hs W hfix hstab ⟨R, hR, hRW⟩
  have himg : ((fun z => MulAction.orbit G z) '' W).Finite := by
    refine (hR.image (fun z => MulAction.orbit G z)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨g, hg⟩ := hRW z hz
    exact ⟨g • z, hg, MulAction.orbit_smul g z⟩
  obtain ⟨B1, hB1W, hB1, hB1r⟩ := fixOrb_reps _ W himg
  have hb : ∀ z ∈ W, ∃ b ∈ B1, ∃ h : G, h • b = z := by
    intro z hz
    obtain ⟨b, hbB, hbo⟩ := hB1r z hz
    have hbo' : MulAction.orbit G b = MulAction.orbit G z := hbo
    have hm : z ∈ MulAction.orbit G b := by
      rw [hbo']
      exact MulAction.mem_orbit_self z
    obtain ⟨h, hh⟩ := hm
    exact ⟨b, hbB, h, hh⟩
  let bb : Z → Z := fun z => if hz : z ∈ W then (hb z hz).choose else z
  let hh : Z → G := fun z => if hz : z ∈ W then (hb z hz).choose_spec.2.choose else 1
  have bbB : ∀ z ∈ W, bb z ∈ B1 := fun z hz => by
    simp only [bb, dif_pos hz]
    exact (hb z hz).choose_spec.1
  have hhb : ∀ z ∈ W, hh z • bb z = z := fun z hz => by
    simp only [bb, hh, dif_pos hz]
    exact (hb z hz).choose_spec.2.choose_spec
  have hcoc : ∀ z ∈ W, (hh z)⁻¹ * σ (hh z) ∈ MulAction.stabilizer G (bb z) := by
    intro z hz
    have hbW : bb z ∈ W := hB1W (bbB z hz)
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    calc σ (hh z) • bb z = σ (hh z) • s (bb z) := by rw [hfix _ hbW]
      _ = s (hh z • bb z) := (hs _ _).symm
      _ = hh z • bb z := by rw [hhb z hz, hfix z hz]
  let key : Z → Z × G := fun z => (bb z, (hh z)⁻¹ * σ (hh z))
  have hkey : (key '' W).Finite := by
    refine (hB1.prod (hB1.biUnion (fun b hbB =>
      (haveI := hstab b (hB1W hbB); Set.toFinite (MulAction.stabilizer G b : Set G))))).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨bbB z hz, Set.mem_biUnion (bbB z hz) (hcoc z hz)⟩
  obtain ⟨B, hBW, hB, hBr⟩ := fixOrb_reps key W hkey
  refine ⟨B, hB, fun z hz => ?_⟩
  obtain ⟨z', hz'B, hk⟩ := hBr z hz
  have hz'W := hBW hz'B
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨h1, h2⟩ := hk
  refine ⟨hh z' * (hh z)⁻¹, ?_, ?_⟩
  · have : σ (hh z') = hh z' * ((hh z)⁻¹ * σ (hh z)) := by
      rw [← h2, mul_inv_cancel_left]
    rw [map_mul, map_inv, this]
    group
  · rw [mul_smul, inv_smul_eq_iff.mpr (hhb z hz).symm, ← h1, hhb z' hz'W]
    exact hz'B
