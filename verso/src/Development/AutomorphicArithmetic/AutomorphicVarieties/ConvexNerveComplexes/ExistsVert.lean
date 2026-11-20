import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Sublevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Perturb

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `E Y _ _ _ q T hG x hx`. Take `⟨h0, hh0⟩` from `hG.nonempty`. Establish `hK` using `sublevel hG x hx (x h0)`. Take `⟨hm, hmK, hmin⟩` from `hK.exists_isMinOn ⟨h0, hh0, le_rfl⟩ x.continuous.continuousOn`. Establish `hglob : ∀ h' ∈ poly q, x hm ≤ x h'`.

Introduce `h' hh'`. Distinguish the cases in `hle : x h' ≤ x h0`. Conclude with `hmin ⟨hh', hle⟩`. Establish `: x hm ≤ x h0` using `hmK.2`. Combine the linear relations using `[not_le.mp hle]`.

Establish `hF` using `sublevel hG x hx (x hm)`. Take `⟨e, he⟩` from `hF.extremePoints_nonempty ⟨hm, hmK.1, le_rfl⟩`. Rewrite `he` using `[mem_extremePoints]`. Take `⟨⟨hep, hex⟩, hext⟩` from `he`. Use `⟨⟨e, hep, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `k hk`. Take `⟨ε, hε, hs⟩` from `perturb hG.locFin e hep k hk`. Establish `ha` using `hs ε (by rw [abs_of_pos hε])`. Establish `hb` using `hs (-ε) (by rw [abs_neg, abs_of_pos hε])`. Establish `hxa` using `hglob _ ha`.

Establish `hxb` using `hglob _ hb`. Simplify using `only [map_add, map_smul, smul_eq_mul] at hxa hxb`. Establish `hmem1 : e + ε • k ∈ {h | h ∈ poly q ∧ x h ≤ x hm}` using `⟨ha, by simp only [map_add, map_smul, smul_eq_mul]; linarith⟩`. Establish `hmem2 : e + (-ε) • k ∈ {h | h ∈ poly q ∧ x h ≤ x hm}` using `⟨hb, by simp only [map_add, map_smul, smul_eq_mul]; linarith⟩`. Establish `hseg : e ∈ openSegment ℝ (e + ε • k) (e + (-ε) • k)`.

Use `⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩` and prove the remaining obligations. Use `module`. Establish `heq` using `(hext _ hmem1 _ hmem2 hseg).1`. Establish `hzero : ε • k = 0`. Use `congrArg (fun w => w - e) heq` as an intermediate fact.

Simplify using `using this`. Conclude with `(smul_eq_zero.mp hzero).resolve_left hε.ne'`. Simplify using `only [normalCone, Set.mem_setOf_eq]`. Introduce `h' hh'`. Conclude with `le_trans hex (hglob h' hh')`.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.exists_vert :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → ∀ x ∈ posDual T, ∃ v : Vert q, x ∈ normalCone q v.1 := by
  intro E Y _ _ _ q T hG x hx
  obtain ⟨h0, hh0⟩ := hG.nonempty
  have hK := sublevel hG x hx (x h0)
  obtain ⟨hm, hmK, hmin⟩ := hK.exists_isMinOn ⟨h0, hh0, le_rfl⟩ x.continuous.continuousOn
  have hglob : ∀ h' ∈ poly q, x hm ≤ x h' := by
    intro h' hh'
    by_cases hle : x h' ≤ x h0
    · exact hmin ⟨hh', hle⟩
    · have : x hm ≤ x h0 := hmK.2
      linarith [not_le.mp hle]
  have hF := sublevel hG x hx (x hm)
  obtain ⟨e, he⟩ := hF.extremePoints_nonempty ⟨hm, hmK.1, le_rfl⟩
  rw [mem_extremePoints] at he
  obtain ⟨⟨hep, hex⟩, hext⟩ := he
  refine ⟨⟨e, hep, ?_⟩, ?_⟩
  · intro k hk
    obtain ⟨ε, hε, hs⟩ := perturb hG.locFin e hep k hk
    have ha := hs ε (by rw [abs_of_pos hε])
    have hb := hs (-ε) (by rw [abs_neg, abs_of_pos hε])
    have hxa := hglob _ ha
    have hxb := hglob _ hb
    simp only [map_add, map_smul, smul_eq_mul] at hxa hxb
    have hmem1 : e + ε • k ∈ {h | h ∈ poly q ∧ x h ≤ x hm} :=
      ⟨ha, by simp only [map_add, map_smul, smul_eq_mul]; linarith⟩
    have hmem2 : e + (-ε) • k ∈ {h | h ∈ poly q ∧ x h ≤ x hm} :=
      ⟨hb, by simp only [map_add, map_smul, smul_eq_mul]; linarith⟩
    have hseg : e ∈ openSegment ℝ (e + ε • k) (e + (-ε) • k) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      module
    have heq := (hext _ hmem1 _ hmem2 hseg).1
    have hzero : ε • k = 0 := by
      have := congrArg (fun w => w - e) heq
      simpa using this
    exact (smul_eq_zero.mp hzero).resolve_left hε.ne'
  · simp only [normalCone, Set.mem_setOf_eq]
    intro h' hh'
    exact le_trans hex (hglob h' hh')
