import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory.UnifSpan

open GlobalTheory.TateTop

/- English proof (translation)
Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Rewrite using `[quotRep_mk, twist_apply, Submodule.Quotient.mk_smul]`.
-/
private theorem quotRep_twist_apply {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) (n : ℕ) (g : G) (q : O ⧸ powSub (M := O) ϖ n) :
    quotRep (twist ε O) ϖ n g q = ((ε g : Oˣ) : O) • q := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [quotRep_mk, twist_apply, Submodule.Quotient.mk_smul]

/- English proof (translation)
Rewrite using `[quotRep_twist_apply, quotRep_twist_apply]`. Conclude with `map_smul _ _ _`.
-/
private theorem factor_quotRep_of_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type} [Group G] (ε : G →* Oˣ) (ϖ : O) {m n : ℕ} (hmn : m ≤ n) (g : G)
    (q : O ⧸ powSub (M := O) ϖ n) :
    Submodule.factor (powSub_anti (M := O) ϖ hmn) (quotRep (twist ε O) ϖ n g q) =
      quotRep (twist ε O) ϖ m g (Submodule.factor (powSub_anti (M := O) ϖ hmn) q) := by
  rw [quotRep_twist_apply, quotRep_twist_apply]
  exact map_smul _ _ _

/- English proof (translation)
Establish `hwZ` using `(mem_cocycles2 (twist ε O) w).mp hw`. Establish `hp'` using `hp`. Rewrite `hp'` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton]`. Take `⟨t, ht⟩` from `hp'`. Establish `hdisc : ∀ n : ℕ, DiscreteTopology (O ⧸ powSub (M` using `O) ϖ n) := fun n => QuotientAddGroup.discreteTopology (N := (powSub (M := O) ϖ n).toAddSubgroup) (hopen n)`.

Set `S : ℕ → Set O` to `fun n => {a | ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h)))}`. Establish `hne : ∀ n, (S n).Nonempty`. Introduce `n`. Use `hdisc n` as an intermediate fact. Use `letI : Module ℤ_[p] (O ⧸ powSub (M := O) ϖ n) := Module.compHom _ φ`.

Establish `hsm : ∀ (s : ℤ_[p]) (q : O ⧸ powSub (M` using `O) ϖ n), s • q = φ s • q := fun _ _ => rfl`. Establish `: CompactSpace (O ⧸ powSub (M` using `O) ϖ n) := by`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[← (Submodule.mkQ_surjective (powSub (M := O) ϖ n)).range_eq]`. Conclude with `isCompact_range (Submodule.continuous_mkQ _)`.

Establish `: Finite (O ⧸ powSub (M` using `O) ϖ n) := finite_of_compact_of_discrete`. Establish `hkill : ∀ m : O ⧸ powSub (M` using `O) ϖ n, ((p : ℤ_[p]) ^ n) • m = 0 := by`. Introduce `m`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Rewrite using `[hsm, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_powSub]`.

Use `⟨t ^ n * x, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, map_natCast, ht, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨-, hex, -⟩` from `hgen n (O ⧸ powSub (M := O) ϖ n) hkill`. Establish `hz : IsCoc χ (fun q : G × G => (Submodule.Quotient.mk (w q) : O ⧸ powSub (M` using `O) ϖ n)) := by`.

Use `⟨(IsLocallyConstant.iff_continuous _).mpr ((Submodule.continuous_mkQ _).comp hwZ.1), fun g h k => ?_⟩` and prove the remaining obligations. Establish `e` using `hwZ.2 g h k`. Rewrite `e` using `[twist_apply, hε g]`. Rewrite using `[hsm, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_sub, e, Submodule.Quotient.mk_zero]`. Take `⟨x, b, hb, hzb⟩` from `hex _ hz`.

Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `⟨a, b, hb.continuous, fun g h => ?_⟩` and prove the remaining obligations. Establish `e` using `hzb (g, h)`. Simplify using `only [cob, hsm] at e`. Rewrite using `[d1_apply, quotRep_twist_apply, hε g, Submodule.Quotient.mk_sub, e, show a * φ (c (g, h)) = φ (c (g, h)) • a from mul_comm _ _, Submodule.Quotient.mk_smul]`.

Normalize the expressions using the abelian group laws. Establish `hanti : ∀ n, S (n + 1) ⊆ S n`. Introduce `n a ha`. Take `⟨b, hb, hd⟩` from `ha`. Use `⟨fun g => Submodule.factor (powSub_anti (M := O) ϖ (Nat.le_succ n)) (b g), (continuous_factor ϖ (Nat.le_succ n)).comp hb, fun g h => ?_⟩` and prove the remaining obligations.

Establish `e` using `hd g h`. Rewrite `e` using `[d1_apply]`. Rewrite using `[d1_apply, ← factor_quotRep_of_le ε ϖ (Nat.le_succ n), ← map_sub, ← map_add, e]`. Conclude with `Submodule.factor_mk _ _`. Establish `hclosed : ∀ n, IsClosed (S n)`.

Introduce `n`. Use `hdisc n` as an intermediate fact. Establish `hpre : S n = (powSub (M` using `O) ϖ n).mkQ ⁻¹' ((powSub (M := O) ϖ n).mkQ '' S n) := by`. Use `(Set.subset_preimage_image _ _).antisymm ?_` and prove the remaining obligations. Introduce and unpack `a' ⟨a, ⟨b, hb, hd⟩, hmk⟩`.

Use `⟨b, hb, fun g h => ?_⟩` and prove the remaining obligations. Rewrite using `[hd g h, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub]`. Use `congr 1`. Rewrite using `[Submodule.Quotient.eq]`. Establish `hmk' : Submodule.Quotient.mk (p` using `powSub (M := O) ϖ n) a = Submodule.Quotient.mk a' := hmk`.

Establish `hd'` using `Submodule.smul_mem _ (φ (c (g, h))) ((Submodule.Quotient.eq _).mp hmk')`. Rewrite `hd'` using `[smul_eq_mul]`. Use `hd' using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hpre]`.

Conclude with `(isClosed_discrete _).preimage (Submodule.continuous_mkQ _)`. Take `⟨a, ha⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne (hclosed 0).isCompact hclosed`. Conclude with `⟨a, fun n => Set.mem_iInter.mp ha n⟩`.
-/
theorem span_mod_pow {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O]
    {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p])
    (hgen : ∀ r, GlobalTheory.TateTop.Gen χ r c) (φ : ℤ_[p] →+* O) (ε : G →* Oˣ)
    (hε : ∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) (ϖ : O) (hϖ : Irreducible ϖ)
    (hp : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hopen : ∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O))
    (w : G × G → O) (hw : w ∈ Z2 (twist ε O)) :
    ∃ a : O, ∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧
      ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) =
        Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h))) := by
  classical
  have hwZ := (mem_cocycles2 (twist ε O) w).mp hw

  have hp' := hp
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton] at hp'
  obtain ⟨t, ht⟩ := hp'

  have hdisc : ∀ n : ℕ, DiscreteTopology (O ⧸ powSub (M := O) ϖ n) := fun n =>
    QuotientAddGroup.discreteTopology (N := (powSub (M := O) ϖ n).toAddSubgroup) (hopen n)

  let S : ℕ → Set O := fun n => {a | ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧
      ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) =
        Submodule.Quotient.mk (w (g, h) - a * φ (c (g, h)))}

  have hne : ∀ n, (S n).Nonempty := by
    intro n
    have := hdisc n
    letI : Module ℤ_[p] (O ⧸ powSub (M := O) ϖ n) := Module.compHom _ φ
    have hsm : ∀ (s : ℤ_[p]) (q : O ⧸ powSub (M := O) ϖ n), s • q = φ s • q := fun _ _ => rfl
    have : CompactSpace (O ⧸ powSub (M := O) ϖ n) := by
      refine ⟨?_⟩
      rw [← (Submodule.mkQ_surjective (powSub (M := O) ϖ n)).range_eq]
      exact isCompact_range (Submodule.continuous_mkQ _)
    have : Finite (O ⧸ powSub (M := O) ϖ n) := finite_of_compact_of_discrete
    have hkill : ∀ m : O ⧸ powSub (M := O) ϖ n, ((p : ℤ_[p]) ^ n) • m = 0 := by
      intro m
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [hsm, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_powSub]
      refine ⟨t ^ n * x, ?_⟩
      rw [map_pow, map_natCast, ht, smul_eq_mul, smul_eq_mul]
      ring
    obtain ⟨-, hex, -⟩ := hgen n (O ⧸ powSub (M := O) ϖ n) hkill
    have hz : IsCoc χ (fun q : G × G => (Submodule.Quotient.mk (w q) : O ⧸ powSub (M := O) ϖ n)) := by
      refine ⟨(IsLocallyConstant.iff_continuous _).mpr ((Submodule.continuous_mkQ _).comp hwZ.1),
        fun g h k => ?_⟩
      have e := hwZ.2 g h k
      rw [twist_apply, hε g] at e
      rw [hsm, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub,
        ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_sub, e, Submodule.Quotient.mk_zero]
    obtain ⟨x, b, hb, hzb⟩ := hex _ hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨a, b, hb.continuous, fun g h => ?_⟩
    have e := hzb (g, h)
    simp only [cob, hsm] at e
    rw [d1_apply, quotRep_twist_apply, hε g, Submodule.Quotient.mk_sub, e,
      show a * φ (c (g, h)) = φ (c (g, h)) • a from mul_comm _ _, Submodule.Quotient.mk_smul]
    abel

  have hanti : ∀ n, S (n + 1) ⊆ S n := by
    intro n a ha
    obtain ⟨b, hb, hd⟩ := ha
    refine ⟨fun g => Submodule.factor (powSub_anti (M := O) ϖ (Nat.le_succ n)) (b g),
      (continuous_factor ϖ (Nat.le_succ n)).comp hb, fun g h => ?_⟩
    have e := hd g h
    rw [d1_apply] at e
    rw [d1_apply, ← factor_quotRep_of_le ε ϖ (Nat.le_succ n), ← map_sub, ← map_add, e]
    exact Submodule.factor_mk _ _

  have hclosed : ∀ n, IsClosed (S n) := by
    intro n
    have := hdisc n
    have hpre : S n = (powSub (M := O) ϖ n).mkQ ⁻¹' ((powSub (M := O) ϖ n).mkQ '' S n) := by
      refine (Set.subset_preimage_image _ _).antisymm ?_
      rintro a' ⟨a, ⟨b, hb, hd⟩, hmk⟩
      refine ⟨b, hb, fun g h => ?_⟩
      rw [hd g h, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub]
      congr 1
      rw [Submodule.Quotient.eq]
      have hmk' : Submodule.Quotient.mk (p := powSub (M := O) ϖ n) a =
          Submodule.Quotient.mk a' := hmk
      have hd' := Submodule.smul_mem _ (φ (c (g, h))) ((Submodule.Quotient.eq _).mp hmk')
      rw [smul_eq_mul] at hd'
      convert hd' using 1
      ring
    rw [hpre]
    exact (isClosed_discrete _).preimage (Submodule.continuous_mkQ _)

  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne
    (hclosed 0).isCompact hclosed
  exact ⟨a, fun n => Set.mem_iInter.mp ha n⟩

end GlobalTheory.UnifSpan
