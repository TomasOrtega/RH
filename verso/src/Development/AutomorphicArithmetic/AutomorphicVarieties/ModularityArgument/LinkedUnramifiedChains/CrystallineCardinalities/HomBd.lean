import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.DualCard

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ D _ ε k N _ ρ e χ s₀ hl hρ hc`. Take `⟨hfinOk, hfinQ, hkill, -, -, hsm, -⟩` from `okFin l O hl`. Use `haveI : Finite (Ok l O k) := hfinOk k`. Use `haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Use `set c := χ s₀ - algebraMap ℤ_[l] O (ε s₀) with hcdef`.

Use `haveI : Finite (O ⧸ Ideal.span {c}) := hfinQ c hc`. Set `I' : Ideal (Ok l O k)` to `Ideal.span {algebraMap O (Ok l O k) c}`. Set `π` to `Ideal.Quotient.mk I'`. Establish `hπ : Function.Surjective π` using `Ideal.Quotient.mk_surjective`. Establish `kill : ∀ f ∈ HomMu l k ε ρ, ∀ a : Ok l O k, f (e (c • a)) = 0`.

Introduce `f hf a`. Establish `hf' : ∀ s x, f (ρ s x) = PadicInt.toZModPow k (ε s : ℤ_[l]) * f x` using `hf`. Rewrite using `[hcdef, sub_smul, map_sub, map_sub, ← hρ, hf', hsm, map_nsmul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, sub_self]`. Establish `wd : ∀ f ∈ HomMu l k ε ρ, ∀ y y' : Ok l O k, π y = π y' → f (e y) = f (e y')`. Introduce `f hf y y' h`.

Establish `h' : y - y' ∈ I'` using `Ideal.Quotient.eq.mp h`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp h'`. Establish `h2 : y - y' = c • a` using `by rw [← ha, Algebra.smul_def, mul_comm]`. Establish `h3` using `kill f hf a`. Rewrite `h3` using `[← h2, map_sub, map_sub]`.

Conclude with `sub_eq_zero.mp h3`. Set `Φ : HomMu l k ε ρ → (Ok l O k ⧸ I' →+ ZMod (l ^ k))` to `fun f => { toFun := fun q => f.1 (e (Function.surjInv hπ q)) map_zero' := by`. Rewrite using `[wd f.1 f.2 _ 0 (by rw [Function.surjInv_eq hπ, map_zero]), map_zero, map_zero]`. Use the proof step `map_add' := by`. Introduce `q q'`.

Rewrite using `[← map_add f.1, ← map_add e]`. Apply `wd f.1 f.2` to reduce the goal to its premises. Rewrite using `[map_add, Function.surjInv_eq hπ, Function.surjInv_eq hπ, Function.surjInv_eq hπ] }`. Establish `hΦ : Function.Injective Φ`. Introduce `f g hfg`.

Establish `h1 : ∀ y, f.1 (e y) = g.1 (e y)`. Introduce `y`. Use `congrArg (fun φ : Ok l O k ⧸ I' →+ ZMod (l ^ k) => φ (π y)) hfg` as an intermediate fact. Express the relevant statement in the definitionally equal form `f.1 (e (Function.surjInv hπ (π y))) = g.1 (e (Function.surjInv hπ (π y))) at this`. Rewrite using `[wd f.1 f.2 y _ (Function.surjInv_eq hπ _).symm, this, ← wd g.1 g.2 y _ (Function.surjInv_eq hπ _).symm]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `x`. Use `h1 (e.symm x)` as an intermediate fact. Rewrite `this` using `[AddEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Use `haveI : Finite (Ok l O k ⧸ I') := Finite.of_surjective π hπ`.

Establish `hQk : ∀ q : Ok l O k ⧸ I', l ^ k • q = 0`. Introduce `q`. Take `⟨y, rfl⟩` from `hπ q`. Rewrite using `[← map_nsmul, hkill, map_zero]`. Take `⟨hfin2, hcard2⟩` from `dualCard l k (Ok l O k ⧸ I') hQk`.

Set `ψ : O ⧸ Ideal.span {c} →+* Ok l O k ⧸ I'` to `Ideal.Quotient.lift (Ideal.span {c}) (π.comp (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}))) (by`. Introduce `a ha`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Rewrite using `[RingHom.comp_apply, map_mul, map_mul]`. Establish `: π (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) c) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by rw [Set.mem_singleton_iff]; rfl))`.

Rewrite using `[this, mul_zero])`. Establish `hψ : Function.Surjective ψ`. Introduce `q`. Take `⟨y, rfl⟩` from `hπ q`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Conclude with `⟨Ideal.Quotient.mk _ x, rfl⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Z.J.homBd :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] (ε : D →* ℤ_[l]ˣ) (k : ℕ) (N : Type) [AddCommGroup N] (ρ : Representation ℤ D N) (e : Ok l O k ≃+ N) (χ : D → O) (s₀ : D), (l : O) ≠ 0 → (∀ s x, ρ s (e x) = e (χ s • x)) → χ s₀ - algebraMap ℤ_[l] O (ε s₀) ≠ 0 → (HomMu l k ε ρ).ncard ≤ Nat.card (O ⧸ Ideal.span {χ s₀ - algebraMap ℤ_[l] O (ε s₀)}) := by
  intro l _ O _ _ _ _ _ D _ ε k N _ ρ e χ s₀ hl hρ hc
  classical
  obtain ⟨hfinOk, hfinQ, hkill, -, -, hsm, -⟩ := okFin l O hl
  haveI : Finite (Ok l O k) := hfinOk k
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set c := χ s₀ - algebraMap ℤ_[l] O (ε s₀) with hcdef
  haveI : Finite (O ⧸ Ideal.span {c}) := hfinQ c hc
  let I' : Ideal (Ok l O k) := Ideal.span {algebraMap O (Ok l O k) c}
  let π := Ideal.Quotient.mk I'
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have kill : ∀ f ∈ HomMu l k ε ρ, ∀ a : Ok l O k, f (e (c • a)) = 0 := by
    intro f hf a
    have hf' : ∀ s x, f (ρ s x) = PadicInt.toZModPow k (ε s : ℤ_[l]) * f x := hf
    rw [hcdef, sub_smul, map_sub, map_sub, ← hρ, hf', hsm, map_nsmul, map_nsmul, nsmul_eq_mul,
      ZMod.natCast_zmod_val, sub_self]
  have wd : ∀ f ∈ HomMu l k ε ρ, ∀ y y' : Ok l O k, π y = π y' → f (e y) = f (e y') := by
    intro f hf y y' h
    have h' : y - y' ∈ I' := Ideal.Quotient.eq.mp h
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h'
    have h2 : y - y' = c • a := by rw [← ha, Algebra.smul_def, mul_comm]
    have h3 := kill f hf a
    rw [← h2, map_sub, map_sub] at h3
    exact sub_eq_zero.mp h3
  let Φ : HomMu l k ε ρ → (Ok l O k ⧸ I' →+ ZMod (l ^ k)) := fun f =>
    { toFun := fun q => f.1 (e (Function.surjInv hπ q))
      map_zero' := by
        rw [wd f.1 f.2 _ 0 (by rw [Function.surjInv_eq hπ, map_zero]), map_zero, map_zero]
      map_add' := by
        intro q q'
        rw [← map_add f.1, ← map_add e]
        apply wd f.1 f.2
        rw [map_add, Function.surjInv_eq hπ, Function.surjInv_eq hπ, Function.surjInv_eq hπ] }
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have h1 : ∀ y, f.1 (e y) = g.1 (e y) := by
      intro y
      have := congrArg (fun φ : Ok l O k ⧸ I' →+ ZMod (l ^ k) => φ (π y)) hfg
      change f.1 (e (Function.surjInv hπ (π y))) = g.1 (e (Function.surjInv hπ (π y))) at this
      rw [wd f.1 f.2 y _ (Function.surjInv_eq hπ _).symm, this,
        ← wd g.1 g.2 y _ (Function.surjInv_eq hπ _).symm]
    apply Subtype.ext
    ext x
    have := h1 (e.symm x)
    rwa [AddEquiv.apply_symm_apply] at this
  haveI : Finite (Ok l O k ⧸ I') := Finite.of_surjective π hπ
  have hQk : ∀ q : Ok l O k ⧸ I', l ^ k • q = 0 := by
    intro q
    obtain ⟨y, rfl⟩ := hπ q
    rw [← map_nsmul, hkill, map_zero]
  obtain ⟨hfin2, hcard2⟩ := dualCard l k (Ok l O k ⧸ I') hQk
  let ψ : O ⧸ Ideal.span {c} →+* Ok l O k ⧸ I' :=
    Ideal.Quotient.lift (Ideal.span {c}) (π.comp (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}))) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [RingHom.comp_apply, map_mul, map_mul]
      have : π (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) c) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by rw [Set.mem_singleton_iff]; rfl))
      rw [this, mul_zero])
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := hπ q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  calc (HomMu l k ε ρ).ncard = Nat.card (HomMu l k ε ρ) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (Ok l O k ⧸ I' →+ ZMod (l ^ k)) := Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card (Ok l O k ⧸ I') := hcard2
    _ ≤ Nat.card (O ⧸ Ideal.span {c}) := Nat.card_le_card_of_surjective ψ hψ
