import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
open NumberField Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.DgenNe

/- English proof (translation)
Introduce `g g' h`. Establish `h1 : H.sigmaOf g = H.sigmaOf g'` using `AlgEquiv.ext fun x => H.φ₀.injective (RingHom.congr_fun h x)`. Conclude with `(H.gal).symm.injective h1`.
-/
theorem emb_injective {R : Ranks} (H : Host R) : Function.Injective H.emb := by
  intro g g' h
  have h1 : H.sigmaOf g = H.sigmaOf g' :=
    AlgEquiv.ext fun x => H.φ₀.injective (RingHom.congr_fun h x)
  exact (H.gal).symm.injective h1

/- English proof (translation)
Introduce `τ τ' h` and use `Subtype.ext (emb_injective H h)`.
-/
theorem embT_injective {R : Ranks} (H : Host R) : Function.Injective (embT H) := fun τ τ' h =>
  Subtype.ext (emb_injective H h)

/- English proof (translation)
Introduce `h`. Establish `h1` using `H.𝔟_spec.1`. Rewrite `h1` using `[h, Ideal.bot_mul]`. Conclude with `differentIdeal_ne_bot h1`.
-/
theorem bb_ne_bot {R : Ranks} (H : Host R) : H.𝔟 ≠ ⊥ := by
  intro h
  have h1 := H.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

/- English proof (translation)
Establish `h0 : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 (bb_ne_bot H)`. Establish `h1 : (1 : H.E) ∈ H.AA0`. Unfold `Host.AA0`. Rewrite using `[FractionalIdeal.mem_inv_iff h0]`. Introduce `y hy`.

Take `⟨x, -, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hy`. Rewrite using `[one_mul]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩`. Establish `h2 : t • (1 : H.E) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E)` using `Submodule.smul_mem _ t h1`. Simplify `h2` using `[Algebra.smul_def]`.
-/
theorem int_mem_inverse_half_different {R : Ranks} (H : Host R) (t : 𝓞 H.E) :
    ((t : H.E)) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := by
  have h0 : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (bb_ne_bot H)
  have h1 : (1 : H.E) ∈ H.AA0 := by
    unfold Host.AA0
    rw [FractionalIdeal.mem_inv_iff h0]
    intro y hy
    obtain ⟨x, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [one_mul]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩
  have h2 : t • (1 : H.E) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := Submodule.smul_mem _ t h1
  simpa [Algebra.smul_def] using h2

end GlobalTheory.Mem.Col2.DgenNe

namespace GlobalTheory.Mem.Col2.DgenNe

/- English proof (translation)
Introduce `R H cD hD τ hτ`. Take `⟨M, hM, hemb, hgen⟩` from `hD`. Take `⟨s, hs, hell⟩` from `hgen τ`. Establish `hs0 : s = 0` using `Subtype.ext (hs.trans hτ)`. Rewrite `hell` using `[hs0, Submodule.span_zero_singleton]`.

Set `e : Tau R → H.E →+* M` to `fun σ => (embT H σ).codRestrict M (hemb σ)`. Establish `hlift : ∀ σ (x : H.E), Formalism.MainNotions.TaylorLogMetric.liftM M (embT H σ x) = e σ x`. Introduce `σ x`. Simplify using `only [Formalism.MainNotions.TaylorLogMetric.liftM, dif_pos (hemb σ x)]`. Both sides reduce to the same expression.

Set `f : Tau R → (𝓞 H.E →* M)` to `fun σ => ((e σ).comp (algebraMap (𝓞 H.E) H.E)).toMonoidHom`. Establish `hf : Function.Injective f`. Introduce `σ σ' h`. Apply `embT_injective H` to reduce the goal to its premises. Establish `h2 : e σ = e σ'` using `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 H.E)) (RingHom.ext fun x => DFunLike.congr_fun h x)`.

Use extensionality with `x`. Conclude with `congrArg Subtype.val (RingHom.congr_fun h2 x)`. Establish `hli` using `(linearIndependent_monoidHom (𝓞 H.E) M).comp f hf`. Establish `hspan` using `span_flip_eq_top_iff_linearIndependent.2 hli`. Set `N` to `Th.mmM H (embT H) M`.

Set `P : Submodule M (Tau R → M)` to `{ carrier := {v | ∃ b : 𝓞 M, b ≠ 0 ∧ b • v ∈ N} add_mem' := by`. Introduce and unpack `v w ⟨b, hb, hv⟩ ⟨b', hb', hw⟩`. Use `⟨b * b', mul_ne_zero hb hb', ?_⟩` and prove the remaining obligations. Establish `: (b * b') • (v + w) = b' • (b • v) + b • (b' • w)`. Rewrite using `[smul_add, mul_smul, mul_smul, smul_comm b b' v]`.

Rewrite using `[this]`. Conclude with `N.add_mem (N.smul_mem _ hv) (N.smul_mem _ hw)`. Use the proof step `zero_mem' := ⟨1, one_ne_zero, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `m v ⟨b, hb, hv⟩`.

Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 M) m`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hy1 : algebraMap (𝓞 M) M y ≠ 0`. Introduce `h0`. Conclude with `hy0 (IsFractionRing.injective (𝓞 M) M (by rw [h0, map_zero]))`.

Use `⟨y * b, mul_ne_zero hy0 hb, ?_⟩` and prove the remaining obligations. Establish `: (y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) • v) = x • (b • v)`. Use function extensionality and compare the values at `σ`. Express the relevant statement in the definitionally equal form `(y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) * v σ) = x • (b • v σ)`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `N.smul_mem _ hv }`. Establish `hP : ∀ t : 𝓞 H.E, (fun σ => e σ t) ∈ P` using `fun t => ⟨1, one_ne_zero, by`. Rewrite using `[one_smul]`.

Conclude with `Submodule.subset_span ⟨(t : H.E), int_mem_inverse_half_different H t, funext fun σ => (hlift σ t).symm⟩⟩`. Establish `hsingle : (Pi.single τ 1 : Tau R → M) ∈ P`. Establish `hle : Submodule.span M (Set.range (flip ((fun g : 𝓞 H.E →* M => (g : 𝓞 H.E → M)) ∘ f))) ≤ P`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`.

Conclude with `hP t`. Conclude with `hle (hspan ▸ Submodule.mem_top)`. Take `⟨b, hb, hbN⟩` from `hsingle`. Establish `hmem : algebraMap (𝓞 M) M b ∈ Th.ellT H (embT H) M τ`. Rewrite using `[Th.ellT, Submodule.mem_comap]`.

Use `hbN using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `σ`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using `[Algebra.smul_def]`.

Simplify using `[h]`. Rewrite `hmem` using `[hell, Submodule.mem_bot]`. Conclude with `hb (IsFractionRing.injective (𝓞 M) M (by rw [hmem, map_zero]))`.
-/
theorem dgen_ne_zero : ∀ {R : Ranks} (H : Host R) (cD : Tau R → ℂ), Th.IsDgen H (embT H) cD → ∀ τ, cD τ ≠ 0 := by
  intro R H cD hD τ hτ
  classical
  obtain ⟨M, hM, hemb, hgen⟩ := hD
  obtain ⟨s, hs, hell⟩ := hgen τ
  have hs0 : s = 0 := Subtype.ext (hs.trans hτ)
  rw [hs0, Submodule.span_zero_singleton] at hell
  let e : Tau R → H.E →+* M := fun σ => (embT H σ).codRestrict M (hemb σ)
  have hlift : ∀ σ (x : H.E), Formalism.MainNotions.TaylorLogMetric.liftM M (embT H σ x) = e σ x := by
    intro σ x
    simp only [Formalism.MainNotions.TaylorLogMetric.liftM, dif_pos (hemb σ x)]
    rfl
  let f : Tau R → (𝓞 H.E →* M) := fun σ => ((e σ).comp (algebraMap (𝓞 H.E) H.E)).toMonoidHom
  have hf : Function.Injective f := by
    intro σ σ' h
    apply embT_injective H
    have h2 : e σ = e σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 H.E))
      (RingHom.ext fun x => DFunLike.congr_fun h x)
    ext x
    exact congrArg Subtype.val (RingHom.congr_fun h2 x)
  have hli := (linearIndependent_monoidHom (𝓞 H.E) M).comp f hf
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  let N := Th.mmM H (embT H) M
  let P : Submodule M (Tau R → M) :=
    { carrier := {v | ∃ b : 𝓞 M, b ≠ 0 ∧ b • v ∈ N}
      add_mem' := by
        rintro v w ⟨b, hb, hv⟩ ⟨b', hb', hw⟩
        refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
        have : (b * b') • (v + w) = b' • (b • v) + b • (b' • w) := by
          rw [smul_add, mul_smul, mul_smul, smul_comm b b' v]
        rw [this]
        exact N.add_mem (N.smul_mem _ hv) (N.smul_mem _ hw)
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro m v ⟨b, hb, hv⟩
        obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) m
        have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
        have hy1 : algebraMap (𝓞 M) M y ≠ 0 := by
          intro h0
          exact hy0 (IsFractionRing.injective (𝓞 M) M (by rw [h0, map_zero]))
        refine ⟨y * b, mul_ne_zero hy0 hb, ?_⟩
        have : (y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) • v) = x • (b • v) := by
          funext σ
          change (y * b) • ((algebraMap (𝓞 M) M x / algebraMap (𝓞 M) M y) * v σ) = x • (b • v σ)
          rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
          field_simp
        rw [this]
        exact N.smul_mem _ hv }
  have hP : ∀ t : 𝓞 H.E, (fun σ => e σ t) ∈ P := fun t =>
    ⟨1, one_ne_zero, by
      rw [one_smul]
      exact Submodule.subset_span ⟨(t : H.E), int_mem_inverse_half_different H t, funext fun σ => (hlift σ t).symm⟩⟩
  have hsingle : (Pi.single τ 1 : Tau R → M) ∈ P := by
    have hle : Submodule.span M (Set.range (flip ((fun g : 𝓞 H.E →* M => (g : 𝓞 H.E → M)) ∘ f))) ≤ P := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact hP t
    exact hle (hspan ▸ Submodule.mem_top)
  obtain ⟨b, hb, hbN⟩ := hsingle
  have hmem : algebraMap (𝓞 M) M b ∈ Th.ellT H (embT H) M τ := by
    rw [Th.ellT, Submodule.mem_comap]
    convert hbN using 1
    funext σ
    by_cases h : σ = τ
    · subst h
      simp [Algebra.smul_def]
    · simp [h]
  rw [hell, Submodule.mem_bot] at hmem
  exact hb (IsFractionRing.injective (𝓞 M) M (by rw [hmem, map_zero]))

end GlobalTheory.Mem.Col2.DgenNe

end
