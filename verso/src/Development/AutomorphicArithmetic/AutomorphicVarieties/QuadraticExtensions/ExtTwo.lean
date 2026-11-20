import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Introduce `Γ _ _ _ U V S h σ hσ h2 hopen hidx hσU hS φ hφ hinv hσσ`. Take `⟨hlc, hadd, hoff⟩` from `hφ`. Establish `key : ∀ a b : Γ, a ∈ V → b ∈ V → (a * b ∈ U ↔ (a ∈ U ↔ b ∈ U))`. Introduce `a b ha hb`. Use `Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf V) hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)` as an intermediate fact.

Simplify `this` using `only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]`. Establish `hσi : σ⁻¹ ∉ U` using `fun hh => hσU (by simpa using U.inv_mem hh)`. Set `Φ : Γ → ZMod 2` to `fun g => if hg : g ∈ U then φ ⟨g, hg⟩ else 0`. Establish `hΦ : ∀ g (hg : g ∈ U), Φ g = φ ⟨g, hg⟩` using `fun g hg => dif_pos hg`. Establish `hΦadd : ∀ a b, a ∈ U → b ∈ U → Φ (a * b) = Φ a + Φ b`.

Introduce `a b ha hb`. Rewrite using `[hΦ a ha, hΦ b hb, hΦ _ (U.mul_mem ha hb), ← hadd]`. Both sides reduce to the same expression. Establish `hR : ∀ a, a ∈ V → a ∉ U → a * σ ∈ U` using `fun a ha haU => (key a σ ha hσ).2 (by simp [haU, hσU])`. Establish `hL : ∀ a, a ∈ V → a ∉ U → σ⁻¹ * a ∈ U` using `fun a ha haU => (key σ⁻¹ a (V.inv_mem hσ) ha).2 (by simp [haU, hσi])`.

Establish `hconj : ∀ a, a ∈ U → σ⁻¹ * a * σ ∈ U`. Introduce `a ha`. Use `hR _ (V.mul_mem (V.inv_mem hσ) (h ha)) ?_` and prove the remaining obligations. Rewrite using `[key _ _ (V.inv_mem hσ) (h ha)]`. Simplify using `[ha, hσi]`.

Establish `hΦconj : ∀ a, a ∈ U → Φ (σ⁻¹ * a * σ) = Φ a`. Introduce `a ha`. Rewrite using `[hΦ a ha, hΦ _ (hconj a ha)]`. Conclude with `hinv _ _ rfl`. Establish `hΦσ : Φ (σ * σ) = 0` using `by rw [hΦ _ h2, hσσ]`.

Set `ψ : V → ZMod 2` to `fun v => if v.1 ∈ U then Φ v.1 else Φ (v.1 * σ)`. Establish `hψU : ∀ v : V, v.1 ∈ U → ψ v = Φ v.1` using `fun v hv => if_pos hv`. Establish `hψN : ∀ v : V, v.1 ∉ U → ψ v = Φ (v.1 * σ)` using `fun v hv => if_neg hv`. Establish `hψadd : ∀ a b : V, ψ (a * b) = ψ a + ψ b`. Introduce `a b`.

Establish `hk` using `key a.1 b.1 a.2 b.2`. Apply the tactic sequence `by_cases ha : a.1 ∈ U <;> by_cases hb : b.1 ∈ U`. Rewrite using `[hψU a ha, hψU b hb, hψU (a * b) (U.mul_mem ha hb)]`. Conclude with `hΦadd _ _ ha hb`. Establish `hab : (a * b).1 ∉ U` using `fun hh => hb ((hk.1 hh).1 ha)`.

Rewrite using `[hψU a ha, hψN b hb, hψN _ hab, ← hΦadd _ _ ha (hR _ b.2 hb), Subgroup.coe_mul, mul_assoc]`. Establish `hab : (a * b).1 ∉ U` using `fun hh => ha ((hk.1 hh).2 hb)`. Rewrite using `[hψN a ha, hψU b hb, hψN _ hab, ← hΦconj _ hb, ← hΦadd _ _ (hR _ a.2 ha) (hconj _ hb), Subgroup.coe_mul]`. Use `congr 1`. Use `group`.

Establish `hab : (a * b).1 ∈ U` using `hk.2 (by simp [ha, hb])`. Establish `e1 : Φ (b.1 * σ) = Φ (σ⁻¹ * b.1)`. Rewrite using `[← hΦconj _ (hR _ b.2 hb), show σ⁻¹ * (b.1 * σ) * σ = (σ⁻¹ * b.1) * (σ * σ) by group, hΦadd _ _ (hL _ b.2 hb) h2, hΦσ, add_zero]`. Rewrite using `[hψN a ha, hψN b hb, hψU _ hab, e1, ← hΦadd _ _ (hR _ a.2 ha) (hL _ b.2 hb), Subgroup.coe_mul]`. Use `congr 1`.

Use `group`. Establish `hφ1 : φ 1 = 0`. Use `hadd 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `left_eq_add.1 this`.

Use `⟨ψ, ⟨?_, hψadd, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Take `⟨O, hO, hOe⟩` from `isOpen_induced_iff.1 (hlc {0})`. Establish `hW : IsOpen ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O)` using `hopen.inter (hO.preimage continuous_subtype_val)`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`.

Use `⟨(fun y => x⁻¹ * y) ⁻¹' ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O), hW.preimage (continuous_const.mul continuous_id), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : U) ∈ Subtype.val ⁻¹' O` using `by rw [hOe]; exact hφ1`. Simplify using `only [Set.mem_preimage, inv_mul_cancel]`. Conclude with `⟨(U.subgroupOf V).one_mem, h1⟩`. Introduce and unpack `y ⟨hy1, hy2⟩`.

Establish `hy1' : (x⁻¹ * y).1 ∈ U` using `hy1`. Establish `h0 : (⟨_, hy1'⟩ : U) ∈ Subtype.val ⁻¹' O` using `hy2`. Rewrite `h0` using `[hOe]`. Establish `h0' : ψ (x⁻¹ * y) = 0`. Rewrite using `[hψU _ hy1', hΦ _ hy1']`.

Conclude with `h0`. Use `hψadd x (x⁻¹ * y)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left, h0', add_zero]`. Then use the resulting hypothesis. Introduce `v hv`. Establish `hvU` using `hS _ hv v.2`.

Rewrite using `[hψU v hvU, hΦ _ hvU]`. Conclude with `hoff _ hv`. Rewrite using `[hψN _ hσU]`. Conclude with `hΦσ`. Introduce `u`.

Rewrite using `[hψU _ u.2]`. Conclude with `hΦ _ u.2`.
-/
theorem UpperTheory.V.Two.extTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (h : U ≤ V) (σ : Γ) (hσ : σ ∈ V) (h2 : σ * σ ∈ U), IsOpen (U.subgroupOf V : Set V) → U.relIndex V = 2 → σ ∉ U → (∀ s ∈ S, s ∈ V → s ∈ U) →
      ∀ φ ∈ CharOff U S 2, (∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ u' = φ u) → φ ⟨σ * σ, h2⟩ = 0 →
      ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u.1, h u.2⟩ = φ u := by
  intro Γ _ _ _ U V S h σ hσ h2 hopen hidx hσU hS φ hφ hinv hσσ
  classical
  obtain ⟨hlc, hadd, hoff⟩ := hφ
  have key : ∀ a b : Γ, a ∈ V → b ∈ V → (a * b ∈ U ↔ (a ∈ U ↔ b ∈ U)) := by
    intro a b ha hb
    have := Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf V) hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using this
  have hσi : σ⁻¹ ∉ U := fun hh => hσU (by simpa using U.inv_mem hh)
  let Φ : Γ → ZMod 2 := fun g => if hg : g ∈ U then φ ⟨g, hg⟩ else 0
  have hΦ : ∀ g (hg : g ∈ U), Φ g = φ ⟨g, hg⟩ := fun g hg => dif_pos hg
  have hΦadd : ∀ a b, a ∈ U → b ∈ U → Φ (a * b) = Φ a + Φ b := by
    intro a b ha hb
    rw [hΦ a ha, hΦ b hb, hΦ _ (U.mul_mem ha hb), ← hadd]
    rfl
  have hR : ∀ a, a ∈ V → a ∉ U → a * σ ∈ U := fun a ha haU =>
    (key a σ ha hσ).2 (by simp [haU, hσU])
  have hL : ∀ a, a ∈ V → a ∉ U → σ⁻¹ * a ∈ U := fun a ha haU =>
    (key σ⁻¹ a (V.inv_mem hσ) ha).2 (by simp [haU, hσi])
  have hconj : ∀ a, a ∈ U → σ⁻¹ * a * σ ∈ U := by
    intro a ha
    refine hR _ (V.mul_mem (V.inv_mem hσ) (h ha)) ?_
    rw [key _ _ (V.inv_mem hσ) (h ha)]
    simp [ha, hσi]
  have hΦconj : ∀ a, a ∈ U → Φ (σ⁻¹ * a * σ) = Φ a := by
    intro a ha
    rw [hΦ a ha, hΦ _ (hconj a ha)]
    exact hinv _ _ rfl
  have hΦσ : Φ (σ * σ) = 0 := by rw [hΦ _ h2, hσσ]
  let ψ : V → ZMod 2 := fun v => if v.1 ∈ U then Φ v.1 else Φ (v.1 * σ)
  have hψU : ∀ v : V, v.1 ∈ U → ψ v = Φ v.1 := fun v hv => if_pos hv
  have hψN : ∀ v : V, v.1 ∉ U → ψ v = Φ (v.1 * σ) := fun v hv => if_neg hv
  have hψadd : ∀ a b : V, ψ (a * b) = ψ a + ψ b := by
    intro a b
    have hk := key a.1 b.1 a.2 b.2
    by_cases ha : a.1 ∈ U <;> by_cases hb : b.1 ∈ U
    · rw [hψU a ha, hψU b hb, hψU (a * b) (U.mul_mem ha hb)]
      exact hΦadd _ _ ha hb
    · have hab : (a * b).1 ∉ U := fun hh => hb ((hk.1 hh).1 ha)
      rw [hψU a ha, hψN b hb, hψN _ hab, ← hΦadd _ _ ha (hR _ b.2 hb), Subgroup.coe_mul, mul_assoc]
    · have hab : (a * b).1 ∉ U := fun hh => ha ((hk.1 hh).2 hb)
      rw [hψN a ha, hψU b hb, hψN _ hab, ← hΦconj _ hb, ← hΦadd _ _ (hR _ a.2 ha) (hconj _ hb), Subgroup.coe_mul]
      congr 1
      group
    · have hab : (a * b).1 ∈ U := hk.2 (by simp [ha, hb])
      have e1 : Φ (b.1 * σ) = Φ (σ⁻¹ * b.1) := by
        rw [← hΦconj _ (hR _ b.2 hb), show σ⁻¹ * (b.1 * σ) * σ = (σ⁻¹ * b.1) * (σ * σ) by group,
          hΦadd _ _ (hL _ b.2 hb) h2, hΦσ, add_zero]
      rw [hψN a ha, hψN b hb, hψU _ hab, e1, ← hΦadd _ _ (hR _ a.2 ha) (hL _ b.2 hb), Subgroup.coe_mul]
      congr 1
      group
  have hφ1 : φ 1 = 0 := by
    have := hadd 1 1
    rw [mul_one] at this
    exact left_eq_add.1 this
  refine ⟨ψ, ⟨?_, hψadd, ?_⟩, ?_, ?_⟩
  · obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (hlc {0})
    have hW : IsOpen ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O) :=
      hopen.inter (hO.preimage continuous_subtype_val)
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O),
      hW.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · have h1 : (1 : U) ∈ Subtype.val ⁻¹' O := by rw [hOe]; exact hφ1
      simp only [Set.mem_preimage, inv_mul_cancel]
      exact ⟨(U.subgroupOf V).one_mem, h1⟩
    · rintro y ⟨hy1, hy2⟩
      have hy1' : (x⁻¹ * y).1 ∈ U := hy1
      have h0 : (⟨_, hy1'⟩ : U) ∈ Subtype.val ⁻¹' O := hy2
      rw [hOe] at h0
      have h0' : ψ (x⁻¹ * y) = 0 := by
        rw [hψU _ hy1', hΦ _ hy1']
        exact h0
      have := hψadd x (x⁻¹ * y)
      rwa [mul_inv_cancel_left, h0', add_zero] at this
  · intro v hv
    have hvU := hS _ hv v.2
    rw [hψU v hvU, hΦ _ hvU]
    exact hoff _ hv
  · rw [hψN _ hσU]
    exact hΦσ
  · intro u
    rw [hψU _ u.2]
    exact hΦ _ u.2
