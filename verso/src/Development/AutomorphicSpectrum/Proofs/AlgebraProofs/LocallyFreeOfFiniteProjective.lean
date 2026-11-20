import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

/- English proof (translation)
Set `Rp` to `Localization.AtPrime p`. Set `Lp` to `LocalizedModule p.primeCompl L`. Set `f : L →ₗ[R] Lp` to `LocalizedModule.mkLinearMap p.primeCompl L`. Use `haveI : Module.Free Rp Lp := Module.free_of_flat_of_isLocalRing`. Set `β` to `Module.finBasis Rp Lp`.

Use `choose ms hms using fun i => IsLocalizedModule.mk'_surjective p.primeCompl f (β i)`. Set `m : Fin (Module.finrank Rp Lp) → L` to `fun i => (ms i).1`. Set `u : Fin (Module.finrank Rp Lp) → Rpˣ` to `fun i => (IsLocalization.map_units Rp (ms i).2).unit`. Establish `hβ : ∀ i, β.unitsSMul u i = f (m i)`. Introduce `i`.

Rewrite using `[Module.Basis.unitsSMul_apply, ← hms i, Units.smul_def]`. Simplify using `only [u, IsUnit.unit_spec, algebraMap_smul, Function.uncurry]`. Conclude with `IsLocalizedModule.mk'_cancel' f _ _`. Establish `hfun : (β.unitsSMul u : _ → Lp) = f ∘ m` using `funext hβ`. Establish `hli : LinearIndependent R m`.

Establish `h1 : LinearIndependent Rp (f ∘ m)` using `hfun ▸ (β.unitsSMul u).linearIndependent`. Establish `h2 : LinearIndependent R (f ∘ m)` using `h1.restrict_scalars' R`. Conclude with `h2.of_comp f`. Establish `hsp : ∀ x : L, ∃ s : R, s ∉ p ∧ s • x ∈ Submodule.span R (Set.range m)`. Introduce `x`.

Establish `h1 : f x ∈ (Submodule.span R (Set.range m)).localized' Rp p.primeCompl f`. Rewrite using `[Submodule.localized'_span, ← Set.range_comp, ← hfun, (β.unitsSMul u).span_eq]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨y, hy, s, hs⟩` from `(Submodule.mem_localized' _ _ _ _ _).1 h1`. Rewrite `hs` using `[IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul]`.

Take `⟨c, hc⟩` from `IsLocalizedModule.exists_of_eq (S := p.primeCompl) hs`. Use `⟨(c * s : p.primeCompl), (c * s).2, ?_⟩` and prove the remaining obligations. Rewrite using `[Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← hc]`. Conclude with `Submodule.smul_mem _ _ hy`. Use `choose s hs hs' using hsp`.

Take `⟨T, hT⟩` from `Module.Finite.fg_top (R := R) (M := L)`. Use `⟨_, m, ∏ t ∈ T, s t, ?_, hli, ?_⟩` and prove the remaining obligations. Conclude with `Submonoid.prod_mem p.primeCompl (fun t _ => hs t)`. Introduce `x`. Establish `hx : x ∈ Submodule.span R (T : Set L)` using `hT ▸ Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem t ht`. Rewrite using `[← Finset.prod_erase_mul T s ht, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (hs' t)`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul a b _ hb => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hb`.
-/
theorem exists_local_basis {R L : Type} [CommRing R] [IsDomain R] [AddCommGroup L] [Module R L]
    [Module.Finite R L] [Module.Projective R L] (p : Ideal R) [p.IsPrime] :
    ∃ (n : ℕ) (m : Fin n → L) (s : R), s ∉ p ∧ LinearIndependent R m ∧
      ∀ x : L, s • x ∈ Submodule.span R (Set.range m) := by
  classical
  let Rp := Localization.AtPrime p
  let Lp := LocalizedModule p.primeCompl L
  let f : L →ₗ[R] Lp := LocalizedModule.mkLinearMap p.primeCompl L
  haveI : Module.Free Rp Lp := Module.free_of_flat_of_isLocalRing
  let β := Module.finBasis Rp Lp
  choose ms hms using fun i => IsLocalizedModule.mk'_surjective p.primeCompl f (β i)
  let m : Fin (Module.finrank Rp Lp) → L := fun i => (ms i).1
  let u : Fin (Module.finrank Rp Lp) → Rpˣ := fun i => (IsLocalization.map_units Rp (ms i).2).unit
  have hβ : ∀ i, β.unitsSMul u i = f (m i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply, ← hms i, Units.smul_def]
    simp only [u, IsUnit.unit_spec, algebraMap_smul, Function.uncurry]
    exact IsLocalizedModule.mk'_cancel' f _ _
  have hfun : (β.unitsSMul u : _ → Lp) = f ∘ m := funext hβ
  have hli : LinearIndependent R m := by
    have h1 : LinearIndependent Rp (f ∘ m) := hfun ▸ (β.unitsSMul u).linearIndependent
    have h2 : LinearIndependent R (f ∘ m) := h1.restrict_scalars' R
    exact h2.of_comp f
  have hsp : ∀ x : L, ∃ s : R, s ∉ p ∧ s • x ∈ Submodule.span R (Set.range m) := by
    intro x
    have h1 : f x ∈ (Submodule.span R (Set.range m)).localized' Rp p.primeCompl f := by
      rw [Submodule.localized'_span, ← Set.range_comp, ← hfun, (β.unitsSMul u).span_eq]
      trivial
    obtain ⟨y, hy, s, hs⟩ := (Submodule.mem_localized' _ _ _ _ _).1 h1
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hs
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p.primeCompl) hs
    refine ⟨(c * s : p.primeCompl), (c * s).2, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← hc]
    exact Submodule.smul_mem _ _ hy
  choose s hs hs' using hsp
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := L)
  refine ⟨_, m, ∏ t ∈ T, s t, ?_, hli, ?_⟩
  · exact Submonoid.prod_mem p.primeCompl (fun t _ => hs t)
  · intro x
    have hx : x ∈ Submodule.span R (T : Set L) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem t ht =>
      rw [← Finset.prod_erase_mul T s ht, mul_smul]
      exact Submodule.smul_mem _ _ (hs' t)
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [smul_comm]; exact Submodule.smul_mem _ _ hb

/- English proof (translation)
Use `letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω`. Use `haveI : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)`. Use `haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ _`. Use `haveI : Module.Flat (FractionRing R) Ω := Module.Flat.of_free`. Conclude with `Module.Flat.trans R (FractionRing R) Ω`.
-/
theorem flat_field {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) :
    Module.Flat R Ω := by
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
  haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ _
  haveI : Module.Flat (FractionRing R) Ω := Module.Flat.of_free
  exact Module.Flat.trans R (FractionRing R) Ω

/- English proof (translation)
Take `⟨n, m, s, hs, hli, hsp⟩` from `exists_local_basis (L := L) p`. Use `haveI := flat_field R`. Establish `hs0 : (s : Ω) ≠ 0` using `fun h => hs (by`. Establish `: s = 0` using `Subtype.ext h`. Rewrite using `[this]`.

Conclude with `p.zero_mem)`. Set `b : Fin n → E` to `fun i => (m i : E)`. Establish `hli' : LinearIndependent Ω b`. Establish `h1` using `(Module.Flat.linearIndependent_one_tmul (S := Ω) hli).map' hb.equiv.toLinearMap (LinearEquiv.ker _)`. Establish `hfun : b = (⇑hb.equiv.toLinearMap ∘ fun x => (1 : Ω) ⊗ₜ[R] m x)`.

Use function extensionality and compare the values at `i`. Simplify using `[b, IsBaseChange.equiv_tmul]`. Rewrite using `[hfun]`. Conclude with `h1`. Establish `key : ∀ x : L, ∃ a : Fin n → R, (s : Ω) • (x : E) = ∑ q, (a q : Ω) • b q`.

Introduce `x`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 (hsp x)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use `congrArg (fun z : L => (z : E)) ha` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at this`.

Conclude with `this.symm`. Establish `hspan : Submodule.span Ω (Set.range b) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `e _`. Proceed by induction on `e using hb.inductionOn with`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `tmul x`. Take `⟨a, ha⟩` from `key x`. Rewrite using `[← Submodule.smul_mem_iff _ hs0]`. Simplify using `only [Submodule.subtype_apply]`.

Rewrite using `[ha]`. Conclude with `Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)`. Consider the case `smul c x hx => exact Submodule.smul_mem _ _ (hx trivial)`. Consider the case `add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)`. Establish `hn : n = r`.

Rewrite using `[← hr, Module.finrank_eq_card_basis (Module.Basis.mk hli' hspan.ge), Fintype.card_fin]`. Substitute `hn` using the available equality. Use `⟨s, hs, b, hli', hspan, fun e => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨k, hk⟩`. Take `⟨a, ha⟩` from `key ⟨_, hk⟩`.

Use `⟨fun q => ((s : Ω) ^ (k + 1))⁻¹ * a q, fun q => ⟨k + 1, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_cancel_left₀ (pow_ne_zero _ hs0)]`. Conclude with `(a q).2`. Simplify using `only [mul_smul]`. Rewrite using `[← Finset.smul_sum, ← ha, smul_smul, smul_smul, mul_assoc, ← pow_succ', inv_mul_cancel₀ (pow_ne_zero _ hs0), one_smul]`.

Introduce and unpack `⟨a, ha, rfl⟩ choose k hk using ha`. Use `⟨∑ q, k q, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `L.toAddSubgroup.sum_mem fun q _ => ?_` and prove the remaining obligations. Establish `h1 : (s : Ω) ^ (∑ q, k q) * a q ∈ R`.

Rewrite using `[← Finset.sum_erase_add _ _ (Finset.mem_univ q), pow_add, mul_assoc]`. Conclude with `R.mul_mem (R.pow_mem s.2 _) (hk q)`. Rewrite using `[smul_smul]`. Conclude with `L.smul_mem (⟨_, h1⟩ : R) (m q).2`.
-/
theorem exists_chart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type}
    [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E) [Module.Finite R L] [Module.Projective R L]
    (hr : Module.finrank Ω E = r) (hb : IsBaseChange Ω L.subtype) (p : Ideal R) [p.IsPrime] :
    ∃ s : R, s ∉ p ∧ ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, (s : Ω) ^ n • e ∈ L.toAddSubgroup) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, (s : Ω) ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q := by
  classical
  obtain ⟨n, m, s, hs, hli, hsp⟩ := exists_local_basis (L := L) p
  haveI := flat_field R
  have hs0 : (s : Ω) ≠ 0 := fun h => hs (by
    have : s = 0 := Subtype.ext h
    rw [this]; exact p.zero_mem)
  let b : Fin n → E := fun i => (m i : E)
  have hli' : LinearIndependent Ω b := by
    have h1 := (Module.Flat.linearIndependent_one_tmul (S := Ω) hli).map' hb.equiv.toLinearMap
      (LinearEquiv.ker _)
    have hfun : b = (⇑hb.equiv.toLinearMap ∘ fun x => (1 : Ω) ⊗ₜ[R] m x) := by
      funext i
      simp [b, IsBaseChange.equiv_tmul]
    rw [hfun]
    exact h1
  have key : ∀ x : L, ∃ a : Fin n → R, (s : Ω) • (x : E) = ∑ q, (a q : Ω) • b q := by
    intro x
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hsp x)
    refine ⟨a, ?_⟩
    have := congrArg (fun z : L => (z : E)) ha
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hspan : Submodule.span Ω (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    induction e using hb.inductionOn with
    | zero => exact Submodule.zero_mem _
    | tmul x =>
      obtain ⟨a, ha⟩ := key x
      rw [← Submodule.smul_mem_iff _ hs0]
      simp only [Submodule.subtype_apply]
      rw [ha]
      exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    | smul c x hx => exact Submodule.smul_mem _ _ (hx trivial)
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hn : n = r := by
    rw [← hr, Module.finrank_eq_card_basis (Module.Basis.mk hli' hspan.ge), Fintype.card_fin]
  subst hn
  refine ⟨s, hs, b, hli', hspan, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := key ⟨_, hk⟩
    refine ⟨fun q => ((s : Ω) ^ (k + 1))⁻¹ * a q, fun q => ⟨k + 1, ?_⟩, ?_⟩
    · rw [mul_inv_cancel_left₀ (pow_ne_zero _ hs0)]; exact (a q).2
    · simp only [mul_smul]
      rw [← Finset.smul_sum, ← ha, smul_smul, smul_smul, mul_assoc, ← pow_succ',
        inv_mul_cancel₀ (pow_ne_zero _ hs0), one_smul]
  · rintro ⟨a, ha, rfl⟩
    choose k hk using ha
    refine ⟨∑ q, k q, ?_⟩
    rw [Finset.smul_sum]
    refine L.toAddSubgroup.sum_mem fun q _ => ?_
    have h1 : (s : Ω) ^ (∑ q, k q) * a q ∈ R := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q), pow_add, mul_assoc]
      exact R.mul_mem (R.pow_mem s.2 _) (hk q)
    rw [smul_smul]
    exact L.smul_mem (⟨_, h1⟩ : R) (m q).2

/- English proof (translation)
Introduce `o Ω _ _ _ R E _ _ r L _ _ hr hb`. Use `⟨fun a ha e he => L.smul_mem (⟨a, ha⟩ : R) he, ?_⟩` and prove the remaining obligations. Set `P : R → Prop` to `fun s => ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e, (∃ n : ℕ, (s : Ω) ^ n • e ∈ L.toAddSubgroup) ↔ ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, (s : Ω) ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q`. Establish `htop : Ideal.span {s | P s} = ⊤`. Assume the negation of the conclusion as `h`.

Take `⟨p, hp, hle⟩` from `Ideal.exists_le_maximal _ h`. Take `⟨s, hs, hP⟩` from `exists_chart R r L hr hb p`. Conclude with `hs (hle (Ideal.subset_span hP))`. Establish `h1 : (1 : R) ∈ Submodule.span R {s | P s}`. Express the relevant statement in the definitionally equal form `(1 : R) ∈ Ideal.span {s | P s}`.

Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨k, c, g, hg⟩` from `Submodule.mem_span_set'.1 h1`. Use `⟨k, fun l => ((g l : R) : Ω), fun l => (c l : Ω), fun l => (g l : R).2, fun l => (c l).2, ?_, fun l => (g l).2⟩` and prove the remaining obligations. Use `congrArg (fun z : R => (z : Ω)) hg` as an intermediate fact.

Simplify using `using this`.
-/
theorem locFree_of_projective : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), Module.Finite R L → Module.Projective R L → Module.finrank Ω E = r → IsBaseChange Ω L.subtype → LocFree R r L.toAddSubgroup := by
  intro o Ω _ _ _ R E _ _ r L _ _ hr hb
  classical
  refine ⟨fun a ha e he => L.smul_mem (⟨a, ha⟩ : R) he, ?_⟩
  let P : R → Prop := fun s => ∃ b : Fin r → E, LinearIndependent Ω b ∧
      Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, (s : Ω) ^ n • e ∈ L.toAddSubgroup) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, (s : Ω) ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q
  have htop : Ideal.span {s | P s} = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨s, hs, hP⟩ := exists_chart R r L hr hb p
    exact hs (hle (Ideal.subset_span hP))
  have h1 : (1 : R) ∈ Submodule.span R {s | P s} := by
    change (1 : R) ∈ Ideal.span {s | P s}
    rw [htop]; trivial
  obtain ⟨k, c, g, hg⟩ := Submodule.mem_span_set'.1 h1
  refine ⟨k, fun l => ((g l : R) : Ω), fun l => (c l : Ω), fun l => (g l : R).2, fun l => (c l).2, ?_,
    fun l => (g l).2⟩
  have := congrArg (fun z : R => (z : Ω)) hg
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj
