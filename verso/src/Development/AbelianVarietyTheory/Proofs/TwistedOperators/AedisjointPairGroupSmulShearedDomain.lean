import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NullMeasurableSetShearImage
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

/- English proof (translation)
Introduce `H _ _ _ _ _ _ _ _ ν _ Γ N _ hNc hN κ 𝓝 _ h𝓝 hconj 𝓕 h𝓕`. Establish `key : ∀ (g : pairGroup Γ N hN) (x : N × H), shear N x ∈ g • (shear N '' (𝓝 ×ˢ 𝓕)) → ∃ n ∈ 𝓝, ∃ h ∈ 𝓕, (x.1 : H) * x.2 = g.1.1 * n * h ∧ x.2 = g.1.2 * h`. Introduce and unpack `g ⟨a, b⟩ hx`. Take `⟨_, ⟨⟨n, h⟩, ⟨hn, hh⟩, rfl⟩, he⟩` from `Set.mem_smul_set.1 hx`. Use `⟨n, hn, h, hh, ?_⟩` and prove the remaining obligations.

Use `Prod.ext_iff.1 he` as an intermediate fact. Simplify using `only [Subgroup.smul_def, shear, smul_eq_mul, Prod.fst_mul, Prod.snd_mul] at this`. Conclude with `⟨by rw [← this.1, mul_assoc], this.2.symm⟩`. Introduce and unpack `⟨⟨u, v⟩, hg⟩ ⟨⟨u', v'⟩, hg'⟩ hne`. Take `⟨hu, hv, huv⟩` from `hg`.

Take `⟨hu', hv', huv'⟩` from `hg'`. Express the relevant statement in the definitionally equal form `((κ.prod ν).map (shear N)) (_ ∩ _) = 0`. Rewrite using `[(measurableEmbedding_shear hNc).map_apply]`. Distinguish the cases in `hvv : v = v'`. Substitute `hvv` using the available equality.

Establish `huu : u ≠ u'`. Introduce and unpack `rfl`. Conclude with `hne rfl`. Establish `memN : ∀ w, w ∈ Γ → w * v⁻¹ ∈ N → v⁻¹ * w ∈ N`. Introduce `w _ hw`.

Use `hN v⁻¹ (Γ.inv_mem hv) (w * v⁻¹) hw` as an intermediate fact. Establish `e : v⁻¹ * (w * v⁻¹) * v⁻¹⁻¹ = v⁻¹ * w` using `by group`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Set `δ : Γ.subgroupOf N` to `⟨⟨v⁻¹ * u, memN u hu huv⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.inv_mem hv) hu)⟩`. Set `δ' : Γ.subgroupOf N` to `⟨⟨v⁻¹ * u', memN u' hu' huv'⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.inv_mem hv) hu')⟩`.

Establish `hδ : δ ≠ δ'`. Introduce `h`. Use `congrArg (fun d : Γ.subgroupOf N => ((d : N) : H)) h` as an intermediate fact. Simplify using `only [δ, δ', mul_right_inj] at this`. Conclude with `huu this`.

Establish `hW : κ (δ • 𝓝 ∩ δ' • 𝓝) = 0` using `h𝓝.aedisjoint hδ`. Set `c : N → N` to `fun n : N => (⟨v⁻¹ * n * v⁻¹⁻¹, hN v⁻¹ (Γ.inv_mem hv) n n.2⟩ : N)`. Establish `hc : Continuous c` using `((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _`. Establish `hcW : κ (c ⁻¹' (δ • 𝓝 ∩ δ' • 𝓝)) = 0`. Establish `h1` using `Measure.le_map_apply hc.measurable.aemeasurable (μ := κ) (δ • 𝓝 ∩ δ' • 𝓝)`.

Establish `h2 : κ.map c = κ` using `hconj v⁻¹ (Γ.inv_mem hv)`. Rewrite `h1` using `[h2, hW]`. Conclude with `le_antisymm h1 bot_le`. Use `measure_mono_null (t := (c ⁻¹' (δ • 𝓝 ∩ δ' • 𝓝)) ×ˢ Set.univ) ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨a, b⟩ ⟨h1, h2⟩`.

Take `⟨n, hn, h, hh, e1, e2⟩` from `key _ _ h1`. Take `⟨n', hn', h', hh', e1', e2'⟩` from `key _ _ h2`. Establish `av : ∀ (w : H) (m : N) (k : H), (a : H) * b = w * m * k → b = v * k → (a : H) * v = w * m`. Introduce `w m k e e'`. Rewrite `e` using `[e']`.

Use `congrArg (· * k⁻¹) e` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Use `⟨⟨Set.mem_smul_set.2 ⟨n, hn, ?_⟩, Set.mem_smul_set.2 ⟨n', hn', ?_⟩⟩, Set.mem_univ _⟩` and prove the remaining obligations. Apply `Subtype.ext show v⁻¹ * u * (n : H) = v⁻¹ * a * v⁻¹⁻¹` to reduce the goal to its premises. Rewrite using `[inv_inv, mul_assoc v⁻¹ (a : H), av _ _ _ e1 e2, mul_assoc]`.

Apply `Subtype.ext show v⁻¹ * u' * (n' : H) = v⁻¹ * a * v⁻¹⁻¹` to reduce the goal to its premises. Rewrite using `[inv_inv, mul_assoc v⁻¹ (a : H), av _ _ _ e1' e2', mul_assoc]`. Conclude with `le_antisymm ((Measure.prod_prod_le _ _).trans (by rw [hcW, zero_mul])) bot_le`. Establish `hZ : ν ((⟨v, hv⟩ : Γ) • 𝓕 ∩ (⟨v', hv'⟩ : Γ) • 𝓕) = 0` using `h𝓕.aedisjoint (fun h => hvv (congrArg Subtype.val h))`. Use `measure_mono_null (t := Set.univ ×ˢ ((⟨v, hv⟩ : Γ) • 𝓕 ∩ (⟨v', hv'⟩ : Γ) • 𝓕)) ?_ ?_` and prove the remaining obligations.

Introduce and unpack `⟨a, b⟩ ⟨h1, h2⟩`. Take `⟨n, hn, h, hh, e1, e2⟩` from `key _ _ h1`. Take `⟨n', hn', h', hh', e1', e2'⟩` from `key _ _ h2`. Conclude with `⟨Set.mem_univ _, Set.mem_smul_set.2 ⟨h, hh, by rw [e2]; rfl⟩, Set.mem_smul_set.2 ⟨h', hh', by rw [e2']; rfl⟩⟩`. Conclude with `le_antisymm ((Measure.prod_prod_le _ _).trans (by rw [hZ, mul_zero])) bot_le`.
-/
theorem aedisjoint_pairGroup_smul_shear_image : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → Pairwise (AEDisjoint ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)) on fun g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN => g • (GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕))) := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N _ hNc hN κ 𝓝 _ h𝓝 hconj 𝓕 h𝓕
  have key : ∀ (g : pairGroup Γ N hN) (x : N × H), shear N x ∈ g • (shear N '' (𝓝 ×ˢ 𝓕)) →
      ∃ n ∈ 𝓝, ∃ h ∈ 𝓕, (x.1 : H) * x.2 = g.1.1 * n * h ∧ x.2 = g.1.2 * h := by
    rintro g ⟨a, b⟩ hx
    obtain ⟨_, ⟨⟨n, h⟩, ⟨hn, hh⟩, rfl⟩, he⟩ := Set.mem_smul_set.1 hx
    refine ⟨n, hn, h, hh, ?_⟩
    have := Prod.ext_iff.1 he
    simp only [Subgroup.smul_def, shear, smul_eq_mul, Prod.fst_mul, Prod.snd_mul] at this
    exact ⟨by rw [← this.1, mul_assoc], this.2.symm⟩
  rintro ⟨⟨u, v⟩, hg⟩ ⟨⟨u', v'⟩, hg'⟩ hne
  obtain ⟨hu, hv, huv⟩ := hg
  obtain ⟨hu', hv', huv'⟩ := hg'
  change ((κ.prod ν).map (shear N)) (_ ∩ _) = 0
  rw [(measurableEmbedding_shear hNc).map_apply]
  by_cases hvv : v = v'
  · subst hvv
    have huu : u ≠ u' := by
      rintro rfl
      exact hne rfl
    have memN : ∀ w, w ∈ Γ → w * v⁻¹ ∈ N → v⁻¹ * w ∈ N := by
      intro w _ hw
      have := hN v⁻¹ (Γ.inv_mem hv) (w * v⁻¹) hw
      have e : v⁻¹ * (w * v⁻¹) * v⁻¹⁻¹ = v⁻¹ * w := by group
      rwa [e] at this
    let δ : Γ.subgroupOf N := ⟨⟨v⁻¹ * u, memN u hu huv⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.inv_mem hv) hu)⟩
    let δ' : Γ.subgroupOf N := ⟨⟨v⁻¹ * u', memN u' hu' huv'⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.inv_mem hv) hu')⟩
    have hδ : δ ≠ δ' := by
      intro h
      have := congrArg (fun d : Γ.subgroupOf N => ((d : N) : H)) h
      simp only [δ, δ', mul_right_inj] at this
      exact huu this
    have hW : κ (δ • 𝓝 ∩ δ' • 𝓝) = 0 := h𝓝.aedisjoint hδ
    let c : N → N := fun n : N => (⟨v⁻¹ * n * v⁻¹⁻¹, hN v⁻¹ (Γ.inv_mem hv) n n.2⟩ : N)
    have hc : Continuous c :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    have hcW : κ (c ⁻¹' (δ • 𝓝 ∩ δ' • 𝓝)) = 0 := by
      have h1 := Measure.le_map_apply hc.measurable.aemeasurable (μ := κ) (δ • 𝓝 ∩ δ' • 𝓝)
      have h2 : κ.map c = κ := hconj v⁻¹ (Γ.inv_mem hv)
      rw [h2, hW] at h1
      exact le_antisymm h1 bot_le
    refine measure_mono_null (t := (c ⁻¹' (δ • 𝓝 ∩ δ' • 𝓝)) ×ˢ Set.univ) ?_ ?_
    · rintro ⟨a, b⟩ ⟨h1, h2⟩
      obtain ⟨n, hn, h, hh, e1, e2⟩ := key _ _ h1
      obtain ⟨n', hn', h', hh', e1', e2'⟩ := key _ _ h2
      have av : ∀ (w : H) (m : N) (k : H), (a : H) * b = w * m * k → b = v * k → (a : H) * v = w * m := by
        intro w m k e e'
        rw [e'] at e
        have := congrArg (· * k⁻¹) e
        simpa [mul_assoc] using this
      refine ⟨⟨Set.mem_smul_set.2 ⟨n, hn, ?_⟩, Set.mem_smul_set.2 ⟨n', hn', ?_⟩⟩, Set.mem_univ _⟩
      · apply Subtype.ext
        show v⁻¹ * u * (n : H) = v⁻¹ * a * v⁻¹⁻¹
        rw [inv_inv, mul_assoc v⁻¹ (a : H), av _ _ _ e1 e2, mul_assoc]
      · apply Subtype.ext
        show v⁻¹ * u' * (n' : H) = v⁻¹ * a * v⁻¹⁻¹
        rw [inv_inv, mul_assoc v⁻¹ (a : H), av _ _ _ e1' e2', mul_assoc]
    · exact le_antisymm ((Measure.prod_prod_le _ _).trans (by rw [hcW, zero_mul])) bot_le
  · have hZ : ν ((⟨v, hv⟩ : Γ) • 𝓕 ∩ (⟨v', hv'⟩ : Γ) • 𝓕) = 0 :=
      h𝓕.aedisjoint (fun h => hvv (congrArg Subtype.val h))
    refine measure_mono_null (t := Set.univ ×ˢ ((⟨v, hv⟩ : Γ) • 𝓕 ∩ (⟨v', hv'⟩ : Γ) • 𝓕)) ?_ ?_
    · rintro ⟨a, b⟩ ⟨h1, h2⟩
      obtain ⟨n, hn, h, hh, e1, e2⟩ := key _ _ h1
      obtain ⟨n', hn', h', hh', e1', e2'⟩ := key _ _ h2
      exact ⟨Set.mem_univ _, Set.mem_smul_set.2 ⟨h, hh, by rw [e2]; rfl⟩,
        Set.mem_smul_set.2 ⟨h', hh', by rw [e2']; rfl⟩⟩
    · exact le_antisymm ((Measure.prod_prod_le _ _).trans (by rw [hZ, mul_zero])) bot_le

end GlobalTheory.UnfoldNormal
