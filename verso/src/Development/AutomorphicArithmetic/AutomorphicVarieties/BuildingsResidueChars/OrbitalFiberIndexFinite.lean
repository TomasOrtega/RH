import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs

namespace UpperTheory

/- English proof (translation)
Establish `hA : (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = A`. Rewrite using `[Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hN]`. Establish `key : ∀ K : Subgroup Γ, A.relIndex K = (A.map (QuotientGroup.mk' N)).relIndex (K.map (QuotientGroup.mk' N))`. Introduce `K`. Rewrite using `[← Subgroup.relIndex_comap, hA]`.

Establish `hm : (N ⊔ C).map (QuotientGroup.mk' N) = C.map (QuotientGroup.mk' N)`. Rewrite using `[Subgroup.map_sup]`. Establish `: N.map (QuotientGroup.mk' N) = ⊥`. Rewrite using `[Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']`. Rewrite using `[this, bot_sup_eq]`.

Rewrite using `[key, hm, ← key]`. Conclude with `h`.
-/
private lemma relIndex_normal_sup {Γ : Type} [Group Γ] (N A C : Subgroup Γ) [N.Normal] (hN : N ≤ A)
    (h : A.relIndex C ≠ 0) : A.relIndex (N ⊔ C) ≠ 0 := by
  have hA : (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = A := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hN]
  have key : ∀ K : Subgroup Γ, A.relIndex K = (A.map (QuotientGroup.mk' N)).relIndex (K.map (QuotientGroup.mk' N)) := by
    intro K
    rw [← Subgroup.relIndex_comap, hA]
  have hm : (N ⊔ C).map (QuotientGroup.mk' N) = C.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup]
    have : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, bot_sup_eq]
  rw [key, hm, ← key]
  exact h

/- English proof (translation)
Introduce `Γ G _ _ ι S U' Γ₁ Γ₀ hS hΓ₁ hT h0`. Take `⟨T, hT⟩` from `hT`. Establish `hAC : (Γ₁ ⊔ Γ₀).relIndex (U'.comap ι) ≠ 0`. Introduce `h`. Apply `h0` to reduce the goal to its premises.

Use `Subgroup.relIndex_dvd_of_le_left (U'.comap ι) (le_sup_right : Γ₀ ≤ Γ₁ ⊔ Γ₀)` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `Nat.eq_zero_of_zero_dvd this`. Establish `h1 : (Γ₁ ⊔ Γ₀).relIndex (Γ₁ ⊔ U'.comap ι) ≠ 0` using `relIndex_normal_sup Γ₁ _ _ le_sup_left hAC`. Establish `pick : ∀ b : ((S ⊔ U').comap ι : Subgroup Γ), ∃ t, t ∈ T ∧ ∃ h ∈ Γ₁, ∃ u ∈ U', ι (b : Γ) = ι h * t * u`.

Introduce `b`. Establish `hb : ι (b : Γ) ∈ S ⊔ U'` using `b.2`. Rewrite `hb` using `[← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul]`. Take `⟨s, hs, u, hu, e⟩` from `hb`. Take `⟨h, hh, t, ht, u₂, hu₂, rfl⟩` from `hT s hs`.

Conclude with `⟨t, ht, h, hh, u₂ * u, U'.mul_mem hu₂ hu, by rw [← e]; group⟩`. Use `choose f hfT hf using pick`. Establish `h2 : (Γ₁ ⊔ U'.comap ι).relIndex ((S ⊔ U').comap ι) ≠ 0`. Establish `inj : Function.Injective (fun q : ((S ⊔ U').comap ι : Subgroup Γ) ⧸ (Γ₁ ⊔ U'.comap ι).subgroupOf ((S ⊔ U').comap ι) => (⟨f q.out, hfT _⟩ : T))`. Introduce `q q' hq`.

Establish `hq' : f q.out = f q'.out` using `congrArg Subtype.val hq`. Rewrite using `[← q.out_eq', ← q'.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Generalize the expression as in `q.out = a at hq'`. Generalize the expression as in `q'.out = b at hq'`. Take `⟨h, hh, u, hu, ha⟩` from `hf a`.

Take `⟨h', hh', u', hu', hb⟩` from `hf b`. Rewrite `hb` using `[← hq']`. Establish `hx : (a : Γ)⁻¹ * (h' * h⁻¹) * a ∈ Γ₁`. Simplify using `using hΓ₁.conj_mem (h' * h⁻¹) (Γ₁.mul_mem hh' (Γ₁.inv_mem hh)) (a : Γ)⁻¹`. Establish `hc : (a : Γ)⁻¹ * h * h'⁻¹ * b ∈ U'.comap ι`.

Establish `: ι ((a : Γ)⁻¹ * h * h'⁻¹ * b) = u⁻¹ * u'`. Simplify using `only [map_mul, map_inv, ha, hb]`. Use `group`. Rewrite using `[Subgroup.mem_comap, this]`. Conclude with `U'.mul_mem (U'.inv_mem hu) hu'`.

Establish `e : (((a⁻¹ * b : ((S ⊔ U').comap ι : Subgroup Γ))) : Γ) = ((a : Γ)⁻¹ * (h' * h⁻¹) * a) * ((a : Γ)⁻¹ * h * h'⁻¹ * b)`. Use `push_cast`. Use `group`. Rewrite using `[e]`. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hc)`.

Use `haveI := Finite.of_injective _ inj`. Conclude with `Subgroup.index_ne_zero_of_finite`. Conclude with `Subgroup.relIndex_ne_zero_trans h1 h2`.
-/
theorem orbitalFiber_index_finite : V.Z.Sym.Glob.Fib.IndexFin := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ hS hΓ₁ hT h0
  obtain ⟨T, hT⟩ := hT
  have hAC : (Γ₁ ⊔ Γ₀).relIndex (U'.comap ι) ≠ 0 := by
    intro h
    apply h0
    have := Subgroup.relIndex_dvd_of_le_left (U'.comap ι) (le_sup_right : Γ₀ ≤ Γ₁ ⊔ Γ₀)
    rw [h] at this
    exact Nat.eq_zero_of_zero_dvd this
  have h1 : (Γ₁ ⊔ Γ₀).relIndex (Γ₁ ⊔ U'.comap ι) ≠ 0 :=
    relIndex_normal_sup Γ₁ _ _ le_sup_left hAC
  have pick : ∀ b : ((S ⊔ U').comap ι : Subgroup Γ), ∃ t, t ∈ T ∧ ∃ h ∈ Γ₁, ∃ u ∈ U',
      ι (b : Γ) = ι h * t * u := by
    intro b
    have hb : ι (b : Γ) ∈ S ⊔ U' := b.2
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hb
    obtain ⟨s, hs, u, hu, e⟩ := hb
    obtain ⟨h, hh, t, ht, u₂, hu₂, rfl⟩ := hT s hs
    exact ⟨t, ht, h, hh, u₂ * u, U'.mul_mem hu₂ hu, by rw [← e]; group⟩
  choose f hfT hf using pick
  have h2 : (Γ₁ ⊔ U'.comap ι).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    have inj : Function.Injective
        (fun q : ((S ⊔ U').comap ι : Subgroup Γ) ⧸ (Γ₁ ⊔ U'.comap ι).subgroupOf ((S ⊔ U').comap ι) =>
          (⟨f q.out, hfT _⟩ : T)) := by
      intro q q' hq
      have hq' : f q.out = f q'.out := congrArg Subtype.val hq
      rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]
      generalize q.out = a at hq'
      generalize q'.out = b at hq'
      obtain ⟨h, hh, u, hu, ha⟩ := hf a
      obtain ⟨h', hh', u', hu', hb⟩ := hf b
      rw [← hq'] at hb
      have hx : (a : Γ)⁻¹ * (h' * h⁻¹) * a ∈ Γ₁ := by
        simpa using hΓ₁.conj_mem (h' * h⁻¹) (Γ₁.mul_mem hh' (Γ₁.inv_mem hh)) (a : Γ)⁻¹
      have hc : (a : Γ)⁻¹ * h * h'⁻¹ * b ∈ U'.comap ι := by
        have : ι ((a : Γ)⁻¹ * h * h'⁻¹ * b) = u⁻¹ * u' := by
          simp only [map_mul, map_inv, ha, hb]
          group
        rw [Subgroup.mem_comap, this]
        exact U'.mul_mem (U'.inv_mem hu) hu'
      have e : (((a⁻¹ * b : ((S ⊔ U').comap ι : Subgroup Γ))) : Γ)
          = ((a : Γ)⁻¹ * (h' * h⁻¹) * a) * ((a : Γ)⁻¹ * h * h'⁻¹ * b) := by
        push_cast
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hc)
    haveI := Finite.of_injective _ inj
    exact Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_ne_zero_trans h1 h2

end UpperTheory
