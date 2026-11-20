import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace CharacterConductorBound

def Lv (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cond_eq (ψ : 𝒪[k]ˣ →* ℂˣ) : cond ψ = sInf (Lv ψ) := rfl

/- English proof (translation)
Introduce `u hu` and use `hc u (Ideal.pow_le_pow_right h hu)`.
-/
theorem Lv_mono (ψ : 𝒪[k]ˣ →* ℂˣ) {c c' : ℕ} (h : c ≤ c') (hc : c ∈ Lv ψ) : c' ∈ Lv ψ :=
  fun u hu => hc u (Ideal.pow_le_pow_right h hu)

/- English proof (translation)
Establish `hopen : IsOpen (μ.ker : Set kˣ)` using `hμ`. Take `⟨V, hVo, hV⟩` from `(Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.mp hopen`. Establish `h1 : (1 : k) ∈ V`. Establish `: (1 : kˣ) ∈ (Units.val ⁻¹' V)` using `by rw [hV]; exact μ.ker.one_mem`. Simplify using `using this`.

Take `⟨γ, hγ⟩` from `(IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hVo.mem_nhds h1)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[k]`. Establish `hlt : valuation k (algebraMap 𝒪[k] k ϖ) < 1` using `(Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hϖ`. Establish `: MulArchimedean (ValueGroupWithZero k)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Take `⟨c, hc⟩` from `exists_pow_lt₀ hlt γ`.

Use `⟨c, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hm : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Rewrite `hu` using `[hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨t, ht⟩` from `hu`. Establish `e : ((u : 𝒪[k]) : k) - 1 = (algebraMap 𝒪[k] k ϖ) ^ c * algebraMap 𝒪[k] k t`.

Use `congrArg (algebraMap 𝒪[k] k) ht` as an intermediate fact. Simplify using `only [map_sub, map_mul, map_pow, map_one] at this`. Conclude with `this`. Establish `ht1 : valuation k (algebraMap 𝒪[k] k t) ≤ 1` using `t.2`. Establish `hv : valuation k (((u : 𝒪[k]) : k) - 1) < γ`.

Rewrite using `[e, map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hmem : unitIncl k u ∈ (Units.val ⁻¹' V : Set kˣ)` using `hγ hv`. Rewrite `hmem` using `[hV]`. Conclude with `(MonoidHom.mem_ker).mp hmem`.
-/
theorem exists_level (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) : (Lv (res μ)).Nonempty := by
  have hopen : IsOpen (μ.ker : Set kˣ) := hμ
  obtain ⟨V, hVo, hV⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.mp hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' V) := by rw [hV]; exact μ.ker.one_mem
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hVo.mem_nhds h1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hlt : valuation k (algebraMap 𝒪[k] k ϖ) < 1 :=
    (Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hϖ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hlt γ
  refine ⟨c, fun u hu => ?_⟩
  have hm : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨t, ht⟩ := hu
  have e : ((u : 𝒪[k]) : k) - 1 = (algebraMap 𝒪[k] k ϖ) ^ c * algebraMap 𝒪[k] k t := by
    have := congrArg (algebraMap 𝒪[k] k) ht
    simp only [map_sub, map_mul, map_pow, map_one] at this
    exact this
  have ht1 : valuation k (algebraMap 𝒪[k] k t) ≤ 1 := t.2
  have hv : valuation k (((u : 𝒪[k]) : k) - 1) < γ := by
    rw [e, map_mul, map_pow]
    calc valuation k (algebraMap 𝒪[k] k ϖ) ^ c * valuation k (algebraMap 𝒪[k] k t)
        ≤ valuation k (algebraMap 𝒪[k] k ϖ) ^ c * 1 := by gcongr
      _ < γ := by rw [mul_one]; exact hc
  have hmem : unitIncl k u ∈ (Units.val ⁻¹' V : Set kˣ) := hγ hv
  rw [hV] at hmem
  exact (MonoidHom.mem_ker).mp hmem

/- English proof (translation)
Introduce `u hu`. Establish `h1` using `hc u (Ideal.pow_le_pow_right (le_max_left c c') hu)`. Establish `h2` using `hc' u (Ideal.pow_le_pow_right (le_max_right c c') hu)`. Simplify using `only [MonoidHom.comp_apply, MonoidHom.div_apply] at h1 h2 ⊢`. Rewrite using `[h1, h2, div_one]`.
-/
theorem max_mem (μ ν : kˣ →* ℂˣ) {c c' : ℕ} (hc : c ∈ Lv (res μ)) (hc' : c' ∈ Lv (res ν)) :
    max c c' ∈ Lv (res (μ / ν)) := by
  intro u hu
  have h1 := hc u (Ideal.pow_le_pow_right (le_max_left c c') hu)
  have h2 := hc' u (Ideal.pow_le_pow_right (le_max_right c c') hu)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply] at h1 h2 ⊢
  rw [h1, h2, div_one]

/- English proof (translation)
The claim follows from `Nat.sInf_mem h`.
-/
theorem cond_mem (ψ : 𝒪[k]ˣ →* ℂˣ) (h : (Lv ψ).Nonempty) : cond ψ ∈ Lv ψ := Nat.sInf_mem h

variable {n : ℕ} (G : Grp k n)

/- English proof (translation)
The claim follows from `cond_mem _ (exists_level _ (G.smooth a))`.
-/
theorem lv_a (a : Fin G.s) : cond (res (G.μ a)) ∈ Lv (res (G.μ a)) :=
  cond_mem _ (exists_level _ (G.smooth a))

/- English proof (translation)
The claim follows from `max_mem _ _ (lv_a G a) (lv_a G b)`.
-/
theorem lv_ab (a b : Fin G.s) :
    max (cond (res (G.μ a))) (cond (res (G.μ b))) ∈ Lv (res (G.μ a / G.μ b)) :=
  max_mem _ _ (lv_a G a) (lv_a G b)

/- English proof (translation)
The claim follows from `Nat.sInf_le (lv_ab G a b)`.
-/
theorem cc_le (a b : Fin G.s) : cc G.μ a b ≤ max (cond (res (G.μ a))) (cond (res (G.μ b))) :=
  Nat.sInf_le (lv_ab G a b)

/- English proof (translation)
The claim follows from `Nat.sInf_mem ⟨_, lv_ab G a b⟩`.
-/
theorem cc_mem (a b : Fin G.s) : cc G.μ a b ∈ Lv (res (G.μ a / G.μ b)) :=
  Nat.sInf_mem ⟨_, lv_ab G a b⟩

/- English proof (translation)
The claim follows from `Finset.single_le_sum (f := fun b => cond (res (G.μ b))) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)`.
-/
theorem cond_le_sum (a : Fin G.s) : cond (res (G.μ a)) ≤ ∑ b, cond (res (G.μ b)) :=
  Finset.single_le_sum (f := fun b => cond (res (G.μ b))) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `h0' : cc G.μ a b = 0` using `by omega`. Establish `hm` using `cc_mem G a b`. Rewrite `hm` using `[h0']`. Apply `G.dist a b hab` to reduce the goal to its premises.

Use extensionality with `u`. Use `hm u (by simp)` as an intermediate fact. Simplify using `only [MonoidHom.comp_apply, MonoidHom.div_apply, div_eq_one] at this`. Simplify using `only [MonoidHom.comp_apply, this]`.
-/
theorem one_le_cc (a b : Fin G.s) (hab : a ≠ b) : 1 ≤ cc G.μ a b := by
  by_contra h0
  have h0' : cc G.μ a b = 0 := by omega
  have hm := cc_mem G a b
  rw [h0'] at hm
  apply G.dist a b hab
  ext u
  have := hm u (by simp)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply, div_eq_one] at this
  simp only [MonoidHom.comp_apply, this]

end CharacterConductorBound

/- English proof (translation)
Establish `hlev : G.lev = 1 + ∑ b, cond (res (G.μ b))` using `rfl`. Use `⟨fun a b hab => CharacterConductorBound.one_le_cc G a b hab, fun a b => ?_, fun a => ?_, fun a b u hu => CharacterConductorBound.cc_mem G a b u hu⟩` and prove the remaining obligations. Establish `h1` using `CharacterConductorBound.cc_le G a b`. Establish `h2` using `CharacterConductorBound.cond_le_sum G a`. Establish `h3` using `CharacterConductorBound.cond_le_sum G b`.

Rewrite using `[hlev]`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `CharacterConductorBound.cond_le_sum G a`. Rewrite using `[hlev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem step_ccBound {n : ℕ} (G : Grp k n) : CompactConductorBoundProp G := by
  have hlev : G.lev = 1 + ∑ b, cond (res (G.μ b)) := rfl
  refine ⟨fun a b hab => CharacterConductorBound.one_le_cc G a b hab, fun a b => ?_, fun a => ?_,
    fun a b u hu => CharacterConductorBound.cc_mem G a b u hu⟩
  · have h1 := CharacterConductorBound.cc_le G a b
    have h2 := CharacterConductorBound.cond_le_sum G a
    have h3 := CharacterConductorBound.cond_le_sum G b
    rw [hlev]
    omega
  · have h2 := CharacterConductorBound.cond_le_sum G a
    rw [hlev]
    omega

end Grp

end UpperTheory.TNZ
