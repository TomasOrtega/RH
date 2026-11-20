import ReciprocityTheory.SemistableReduction.SemiDegSt

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

def cutProjK (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[K] (Fin r → K) where
  toFun x i := if e ≤ (i : ℕ) then x i else 0
  map_add' x y := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]

variable {K : Type} [Field K] [NumberField K] {r e : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sdd_cutProjK_eq (x : Fin r → K) : cutProjK K r e x = projGe K r e x := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i hi`. Use `congrFun h i` as an intermediate fact. Simplify `this` using `[projGe, hi]`. Introduce `h`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : e ≤ (i : ℕ)`. Simplify using `[projGe, hi, h i hi]`. Simplify using `[projGe, hi]`.
-/
theorem sdd_proj_eq_zero_iff (x : Fin r → K) : projGe K r e x = 0 ↔ x ∈ cutSub K r e := by
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [projGe, hi] using this
  · intro h
    funext i
    by_cases hi : e ≤ (i : ℕ)
    · simp [projGe, hi, h i hi]
    · simp [projGe, hi]

/- English proof (translation)
Establish `hle : Submodule.span K (Set.range b₀) ≤ LinearMap.ker (cutProjK K r e)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(sdd_proj_eq_zero_iff _).mpr (hb₀.1 i).2`. Use extensionality with `x`.

Simplify using `only [satSub, Submodule.mem_inf, Submodule.restrictScalars_mem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hs⟩`. Conclude with `⟨hx, (sdd_proj_eq_zero_iff x).mp (hle hs)⟩`. Introduce and unpack `⟨hx, hc⟩`.

Conclude with `⟨hx, hb₀.2.2 x ⟨hx, hc⟩⟩`.
-/
theorem sdd_satSub_eq {k₀ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (hb₀ : IsKBasisIn (B ⊓ cutSub K r e) b₀) : satSub B b₀ = B ⊓ cutSub K r e := by
  have hle : Submodule.span K (Set.range b₀) ≤ LinearMap.ker (cutProjK K r e) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (sdd_proj_eq_zero_iff _).mpr (hb₀.1 i).2
  ext x
  simp only [satSub, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨hx, hs⟩
    exact ⟨hx, (sdd_proj_eq_zero_iff x).mp (hle hs)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hx, hb₀.2.2 x ⟨hx, hc⟩⟩

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right] at hg`. Establish `hc' : ∀ j, cutProjK K r e (c j) = b₁ j` using `hcb`.

Establish `hb' : ∀ i, cutProjK K r e (b₀ i) = 0` using `fun i => (sdd_proj_eq_zero_iff _).mpr (hb₀cut i)`. Establish `h1 : ∑ j, g (Fin.natAdd k₀ j) • b₁ j = 0`. Use `congrArg (cutProjK K r e) hg` as an intermediate fact. Simplify `this` using `[map_add, map_sum, map_smul, hb', hc']`. Establish `h1'` using `Fintype.linearIndependent_iff.mp hb₁li _ h1`.

Establish `h0 : ∑ i, g (Fin.castAdd k₁ i) • b₀ i = 0` using `by simpa [h1'] using hg`. Establish `h0'` using `Fintype.linearIndependent_iff.mp hb₀li _ h0`. Introduce `i`. Conclude with `Fin.addCases (fun i => h0' i) (fun j => h1' j) i`.
-/
theorem sdd_append_li {k₀ k₁ : ℕ} (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    LinearIndependent K (Fin.append b₀ c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  have hc' : ∀ j, cutProjK K r e (c j) = b₁ j := hcb
  have hb' : ∀ i, cutProjK K r e (b₀ i) = 0 := fun i => (sdd_proj_eq_zero_iff _).mpr (hb₀cut i)
  have h1 : ∑ j, g (Fin.natAdd k₀ j) • b₁ j = 0 := by
    have := congrArg (cutProjK K r e) hg
    simpa [map_add, map_sum, map_smul, hb', hc'] using this
  have h1' := Fintype.linearIndependent_iff.mp hb₁li _ h1
  have h0 : ∑ i, g (Fin.castAdd k₁ i) • b₀ i = 0 := by simpa [h1'] using hg
  have h0' := Fintype.linearIndependent_iff.mp hb₀li _ h0
  intro i
  exact Fin.addCases (fun i => h0' i) (fun j => h1' j) i

/- English proof (translation)
Introduce `x hx`. Establish `hfx : projGe K r e x ∈ Submodule.span K (Set.range b₁)` using `hb₁.2.2 _ (Submodule.mem_map_of_mem hx)`. Take `⟨β, hβ⟩` from `(Submodule.mem_span_range_iff_exists_fun K).mp hfx`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) β`. Simplify using `only [IsLocalization.IsInteger, RingHom.mem_rangeS] at hd`.

Use `choose β' hβ' using hd`. Use `set dK : K := algebraMap (𝓞 K) K d with hdK`. Establish `hd0 : dK ≠ 0`. Rewrite using `[hdK]`. Conclude with `(IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)`.

Use `set y : Fin r → K := dK • x - ∑ j, (algebraMap (𝓞 K) K (β' j)) • c j with hy`. Establish `hyB : y ∈ B`. Use `B.sub_mem ?_ (B.sum_mem fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hdK, algebraMap_smul]`. Conclude with `B.smul_mem _ hx`.

Rewrite using `[algebraMap_smul]`. Conclude with `B.smul_mem _ (hcB j)`. Establish `hycut : y ∈ cutSub K r e`. Rewrite using `[← sdd_proj_eq_zero_iff, ← sdd_cutProjK_eq, hy, map_sub, map_smul, map_sum]`. Simplify using `only [map_smul, sdd_cutProjK_eq, hcb, ← hβ, Finset.smul_sum, smul_smul, hβ']`.

Rewrite using `[sub_eq_zero]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def (d : 𝓞 K) (β j)]`. Establish `hys : y ∈ Submodule.span K (Set.range (Fin.append b₀ c))`. Use `Submodule.span_mono ?_ (hb₀.2.2 y ⟨hyB, hycut⟩)` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨Fin.castAdd k₁ i, Fin.append_left b₀ c i⟩`. Establish `hcs : ∀ j, c j ∈ Submodule.span K (Set.range (Fin.append b₀ c))` using `fun j => Submodule.subset_span ⟨Fin.natAdd k₀ j, Fin.append_right b₀ c j⟩`. Establish `hx' : x = dK⁻¹ • (y + ∑ j, (algebraMap (𝓞 K) K (β' j)) • c j)`. Rewrite using `[hy, sub_add_cancel, smul_smul, inv_mul_cancel₀ hd0, one_smul]`.

Rewrite using `[hx']`. Conclude with `Submodule.smul_mem _ _ (Submodule.add_mem _ hys (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcs j)))`.
-/
theorem sdd_append_span {k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (c b₁ : Fin k₁ → Fin r → K) (hb₀ : IsKBasisIn (B ⊓ cutSub K r e) b₀) (hcB : ∀ j, c j ∈ B)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁ : IsKBasisIn (B.map (projGe K r e)) b₁) :
    ∀ x ∈ B, x ∈ Submodule.span K (Set.range (Fin.append b₀ c)) := by
  intro x hx
  have hfx : projGe K r e x ∈ Submodule.span K (Set.range b₁) :=
    hb₁.2.2 _ (Submodule.mem_map_of_mem hx)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hfx
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) β
  simp only [IsLocalization.IsInteger, RingHom.mem_rangeS] at hd
  choose β' hβ' using hd
  set dK : K := algebraMap (𝓞 K) K d with hdK
  have hd0 : dK ≠ 0 := by
    rw [hdK]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)
  set y : Fin r → K := dK • x - ∑ j, (algebraMap (𝓞 K) K (β' j)) • c j with hy
  have hyB : y ∈ B := by
    refine B.sub_mem ?_ (B.sum_mem fun j _ => ?_)
    · rw [hdK, algebraMap_smul]
      exact B.smul_mem _ hx
    · rw [algebraMap_smul]
      exact B.smul_mem _ (hcB j)
  have hycut : y ∈ cutSub K r e := by
    rw [← sdd_proj_eq_zero_iff, ← sdd_cutProjK_eq, hy, map_sub, map_smul, map_sum]
    simp only [map_smul, sdd_cutProjK_eq, hcb, ← hβ, Finset.smul_sum, smul_smul, hβ']
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def (d : 𝓞 K) (β j)]
  have hys : y ∈ Submodule.span K (Set.range (Fin.append b₀ c)) := by
    refine Submodule.span_mono ?_ (hb₀.2.2 y ⟨hyB, hycut⟩)
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd k₁ i, Fin.append_left b₀ c i⟩
  have hcs : ∀ j, c j ∈ Submodule.span K (Set.range (Fin.append b₀ c)) := fun j =>
    Submodule.subset_span ⟨Fin.natAdd k₀ j, Fin.append_right b₀ c j⟩
  have hx' : x = dK⁻¹ • (y + ∑ j, (algebraMap (𝓞 K) K (β' j)) • c j) := by
    rw [hy, sub_add_cancel, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hys
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcs j)))

/- English proof (translation)
Establish `hsp : Submodule.span K (Set.range b) = Submodule.span K (Set.range a)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `has _ (hb.1 i)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hb.2.2 _ (haB i)`. Establish `h1` using `finrank_span_eq_card hb.2.1`. Establish `h2` using `finrank_span_eq_card hali`.

Rewrite `h1` using `[hsp, h2]`. Simplify using `using h1.symm`.
-/
theorem sdd_card_eq {k k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K)
    (a : Fin (k₀ + k₁) → Fin r → K) (hb : IsKBasisIn B b) (haB : ∀ i, a i ∈ B)
    (hali : LinearIndependent K a) (has : ∀ x ∈ B, x ∈ Submodule.span K (Set.range a)) :
    k = k₀ + k₁ := by
  have hsp : Submodule.span K (Set.range b) = Submodule.span K (Set.range a) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact has _ (hb.1 i)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb.2.2 _ (haB i)
  have h1 := finrank_span_eq_card hb.2.1
  have h2 := finrank_span_eq_card hali
  rw [hsp, h2] at h1
  simpa using h1.symm

/- English proof (translation)
Establish `hspan : Submodule.span (𝓞 K) (Set.range b₁) = (Submodule.span (𝓞 K) (Set.range c)).map (projGe K r e)`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Conclude with `(hcb j).symm`.

Establish `hcle : Submodule.span (𝓞 K) (Set.range c) ≤ B`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hcB j`. Rewrite using `[Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right, eq_comm, ← AddSubgroup.inf_relIndex_right]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, hsat, hspan]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨y, hy, hxy⟩, hx⟩`.

Establish `hxy' : projGe K r e y = projGe K r e x` using `hxy`. Establish `hyB` using `hcle hy`. Use `⟨?_, hx⟩` and prove the remaining obligations. Establish `hs : x - y ∈ B ⊓ cutSub K r e` using `⟨B.sub_mem hx hyB, (sdd_proj_eq_zero_iff _).mp (by rw [map_sub, hxy', sub_self])⟩`. Use `Submodule.add_mem_sup hs hy` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce and unpack `⟨hsup, hx⟩`. Take `⟨s, hs, t, ht, rfl⟩` from `Submodule.mem_sup.mp hsup`. Use `⟨⟨t, ht, ?_⟩, hx⟩` and prove the remaining obligations. Use `show projGe K r e t = projGe K r e (s + t)`.

Rewrite using `[map_add, (sdd_proj_eq_zero_iff s).mpr hs.2, zero_add]`.
-/
theorem sdd_index {k₀ k₁ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (c b₁ : Fin k₁ → Fin r → K) (hsat : satSub B b₀ = B ⊓ cutSub K r e) (hcB : ∀ j, c j ∈ B)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) :
    (satSub B b₀ ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex B.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b₁)).toAddSubgroup.relIndex
        (B.map (projGe K r e)).toAddSubgroup := by
  have hspan : Submodule.span (𝓞 K) (Set.range b₁) =
      (Submodule.span (𝓞 K) (Set.range c)).map (projGe K r e) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (hcb j).symm
  have hcle : Submodule.span (𝓞 K) (Set.range c) ≤ B := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hcB j
  rw [Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.inf_relIndex_right, eq_comm, ← AddSubgroup.inf_relIndex_right]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, hsat,
    hspan]
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    have hxy' : projGe K r e y = projGe K r e x := hxy
    have hyB := hcle hy
    refine ⟨?_, hx⟩
    have hs : x - y ∈ B ⊓ cutSub K r e :=
      ⟨B.sub_mem hx hyB, (sdd_proj_eq_zero_iff _).mp (by rw [map_sub, hxy', sub_self])⟩
    have := Submodule.add_mem_sup hs hy
    rwa [sub_add_cancel] at this
  · rintro ⟨hsup, hx⟩
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hsup
    refine ⟨⟨t, ht, ?_⟩, hx⟩
    show projGe K r e t = projGe K r e (s + t)
    rw [map_add, (sdd_proj_eq_zero_iff s).mpr hs.2, zero_add]

end ReciprocityTheory.MultiplicativeHeights
