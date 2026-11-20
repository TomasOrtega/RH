import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS.SumFiber

/- English proof (translation)
Establish `outL : ∀ x : Γ, ∃ u ∈ L, (QuotientGroup.mk x : Γ ⧸ L).out = x * u`. Introduce `x`. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul L x`. Conclude with `⟨u, u.2, hu⟩`. Establish `outV : ∀ x : H, ∃ u ∈ V, (QuotientGroup.mk x : H ⧸ V).out = x * u`.

Introduce `x`. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul V x`. Conclude with `⟨u, u.2, hu⟩`. Establish `hφout : ∀ x : Γ, φ (QuotientGroup.mk x : Γ ⧸ L).out = φ x`. Introduce `x`.

Take `⟨u, hu, h⟩` from `outL x`. Rewrite using `[h, hφ u hu]`. Set `S : Set (Γ ⧸ L)` to `{q | p q.out ∈ V}`. Establish `hS : ∀ x : Γ, p x ∈ V → (QuotientGroup.mk x : Γ ⧸ L) ∈ S`. Introduce `x hx`.

Take `⟨u, hu, h⟩` from `outL x`. Express the relevant statement in the definitionally equal form `p (QuotientGroup.mk x : Γ ⧸ L).out ∈ V`. Rewrite using `[h, map_mul]`. Conclude with `V.mul_mem hx (hLV u hu)`. Set `T : (H ⧸ V) × S → Γ ⧸ L` to `fun a => QuotientGroup.mk (e a.1.out * a.2.1.out)`.

Establish `hinj : Function.Injective T`. Introduce and unpack `⟨m, q, hq⟩ ⟨m', q', hq'⟩ h`. Establish `hq1 : p q.out ∈ V` using `hq`. Establish `hq2 : p q'.out ∈ V` using `hq'`. Establish `h1 : (e m.out * q.out)⁻¹ * (e m'.out * q'.out) ∈ L` using `QuotientGroup.eq.1 h`.

Establish `h2` using `hLV _ h1`. Simplify using `only [map_mul, map_inv, hpe] at h2`. Establish `hm : m = m'`. Rewrite using `[← QuotientGroup.out_eq' m, ← QuotientGroup.out_eq' m']`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations.

Establish `h3 : m.out⁻¹ * m'.out = p q.out * ((p q.out)⁻¹ * m.out⁻¹ * (m'.out * p q'.out)) * (p q'.out)⁻¹` using `by group`. Rewrite using `[h3]`. Use `V.mul_mem (V.mul_mem hq1 ?_) (V.inv_mem hq2)` and prove the remaining obligations. Simplify `h2` using `[_root_.mul_inv_rev]`. Substitute `hm` using the available equality.

Establish `hqq : q = q'`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Establish `h3 : q.out⁻¹ * q'.out = (e m.out * q.out)⁻¹ * (e m.out * q'.out)` using `by group`. Rewrite using `[h3]`.

Conclude with `h1`. Substitute `hqq` using the available equality. Both sides reduce to the same expression. Establish `hsurj : Function.Surjective T`. Introduce `q`.

Take `⟨v, hv, hm⟩` from `outV (p q.out)`. Set `m : H ⧸ V` to `QuotientGroup.mk (p q.out)`. Establish `hmem : p ((e m.out)⁻¹ * q.out) ∈ V`. Establish `: p ((e m.out)⁻¹ * q.out) = v⁻¹`. Simplify using `only [map_mul, map_inv, hpe, m]`.

Rewrite using `[hm]`. Use `group`. Rewrite using `[this]`. Conclude with `V.inv_mem hv`. Use `⟨(m, ⟨QuotientGroup.mk ((e m.out)⁻¹ * q.out), hS _ hmem⟩), ?_⟩` and prove the remaining obligations.

Take `⟨u, hu, h⟩` from `outL ((e m.out)⁻¹ * q.out)`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk (e m.out * (QuotientGroup.mk ((e m.out)⁻¹ * q.out) : Γ ⧸ L).out) : Γ ⧸ L) = q`. Rewrite using `[h]`. Use `Eq.trans (QuotientGroup.eq.2 ?_) (QuotientGroup.out_eq' q)` and prove the remaining obligations. Establish `h3 : (e m.out * ((e m.out)⁻¹ * q.out * u))⁻¹ * q.out = u⁻¹` using `by group`.

Rewrite using `[h3]`. Conclude with `L.inv_mem hu`. Set `E : (H ⧸ V) × S ≃ Γ ⧸ L` to `Equiv.ofBijective T ⟨hinj, hsurj⟩`. Establish `hsupp : (Function.support (fun a : (H ⧸ V) × S => φ (e a.1.out * a.2.1.out))).Finite`. Use `(hfin.preimage (f := T) hinj.injOn).subset ?_` and prove the remaining obligations.

Introduce `a ha`. Express the relevant statement in the definitionally equal form `φ (QuotientGroup.mk (e a.1.out * a.2.1.out) : Γ ⧸ L).out ≠ 0`. Rewrite using `[hφout]`. Conclude with `ha`. Combine the equalities or inequalities in the displayed calculation.

Use `finsum_congr fun m => ?_` and prove the remaining obligations. Rewrite using `[finsum_set_coe_eq_finsum_mem S (f := fun q : Γ ⧸ L => φ (e m.out * q.out)), finsum_mem_def]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Distinguish the cases in `hq : p q.out ∈ V`. Establish `hq' : q ∈ S` using `hq`.

Rewrite using `[Set.indicator_of_mem hq', Set.indicator_of_mem (show p q.out ∈ (V : Set H) from hq)]`. Simplify using the standard rewrite rules. Establish `hq' : q ∉ S` using `hq`. Rewrite using `[Set.indicator_of_notMem hq', Set.indicator_of_notMem (show p q.out ∉ (V : Set H) from hq)]`. Simplify using the standard rewrite rules.
-/
theorem finsum_cosets_retraction {Γ H : Type} [Group Γ] [Group H] (p : Γ →* H) (e : H →* Γ)
    (hpe : ∀ m, p (e m) = m)
    (L : Subgroup Γ) (V : Subgroup H) (hLV : ∀ u ∈ L, p u ∈ V) (φ : Γ → ℂ)
    (hφ : ∀ u ∈ L, ∀ x, φ (x * u) = φ x) (hfin : {q : Γ ⧸ L | φ q.out ≠ 0}.Finite) :
    ∑ᶠ q : Γ ⧸ L, φ q.out =
      ∑ᶠ m : H ⧸ V, ∑ᶠ q : Γ ⧸ L,
        (V : Set H).indicator (1 : H → ℂ) (p q.out) * φ (e m.out * q.out) := by
  have outL : ∀ x : Γ, ∃ u ∈ L, (QuotientGroup.mk x : Γ ⧸ L).out = x * u := by
    intro x
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul L x
    exact ⟨u, u.2, hu⟩
  have outV : ∀ x : H, ∃ u ∈ V, (QuotientGroup.mk x : H ⧸ V).out = x * u := by
    intro x
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul V x
    exact ⟨u, u.2, hu⟩
  have hφout : ∀ x : Γ, φ (QuotientGroup.mk x : Γ ⧸ L).out = φ x := by
    intro x
    obtain ⟨u, hu, h⟩ := outL x
    rw [h, hφ u hu]
  let S : Set (Γ ⧸ L) := {q | p q.out ∈ V}
  have hS : ∀ x : Γ, p x ∈ V → (QuotientGroup.mk x : Γ ⧸ L) ∈ S := by
    intro x hx
    obtain ⟨u, hu, h⟩ := outL x
    change p (QuotientGroup.mk x : Γ ⧸ L).out ∈ V
    rw [h, map_mul]
    exact V.mul_mem hx (hLV u hu)
  let T : (H ⧸ V) × S → Γ ⧸ L := fun a => QuotientGroup.mk (e a.1.out * a.2.1.out)
  have hinj : Function.Injective T := by
    rintro ⟨m, q, hq⟩ ⟨m', q', hq'⟩ h
    have hq1 : p q.out ∈ V := hq
    have hq2 : p q'.out ∈ V := hq'
    have h1 : (e m.out * q.out)⁻¹ * (e m'.out * q'.out) ∈ L := QuotientGroup.eq.1 h
    have h2 := hLV _ h1
    simp only [map_mul, map_inv, hpe] at h2
    have hm : m = m' := by
      rw [← QuotientGroup.out_eq' m, ← QuotientGroup.out_eq' m']
      refine QuotientGroup.eq.2 ?_
      have h3 : m.out⁻¹ * m'.out
          = p q.out * ((p q.out)⁻¹ * m.out⁻¹ * (m'.out * p q'.out)) * (p q'.out)⁻¹ := by
        group
      rw [h3]
      refine V.mul_mem (V.mul_mem hq1 ?_) (V.inv_mem hq2)
      simpa [_root_.mul_inv_rev] using h2
    subst hm
    have hqq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      refine QuotientGroup.eq.2 ?_
      have h3 : q.out⁻¹ * q'.out = (e m.out * q.out)⁻¹ * (e m.out * q'.out) := by group
      rw [h3]
      exact h1
    subst hqq
    rfl
  have hsurj : Function.Surjective T := by
    intro q
    obtain ⟨v, hv, hm⟩ := outV (p q.out)
    let m : H ⧸ V := QuotientGroup.mk (p q.out)
    have hmem : p ((e m.out)⁻¹ * q.out) ∈ V := by
      have : p ((e m.out)⁻¹ * q.out) = v⁻¹ := by
        simp only [map_mul, map_inv, hpe, m]
        rw [hm]
        group
      rw [this]
      exact V.inv_mem hv
    refine ⟨(m, ⟨QuotientGroup.mk ((e m.out)⁻¹ * q.out), hS _ hmem⟩), ?_⟩
    obtain ⟨u, hu, h⟩ := outL ((e m.out)⁻¹ * q.out)
    change (QuotientGroup.mk (e m.out * (QuotientGroup.mk ((e m.out)⁻¹ * q.out) : Γ ⧸ L).out) :
      Γ ⧸ L) = q
    rw [h]
    refine Eq.trans (QuotientGroup.eq.2 ?_) (QuotientGroup.out_eq' q)
    have h3 : (e m.out * ((e m.out)⁻¹ * q.out * u))⁻¹ * q.out = u⁻¹ := by group
    rw [h3]
    exact L.inv_mem hu
  let E : (H ⧸ V) × S ≃ Γ ⧸ L := Equiv.ofBijective T ⟨hinj, hsurj⟩
  have hsupp : (Function.support
      (fun a : (H ⧸ V) × S => φ (e a.1.out * a.2.1.out))).Finite := by
    refine (hfin.preimage (f := T) hinj.injOn).subset ?_
    intro a ha
    change φ (QuotientGroup.mk (e a.1.out * a.2.1.out) : Γ ⧸ L).out ≠ 0
    rw [hφout]
    exact ha
  calc ∑ᶠ q : Γ ⧸ L, φ q.out
      = ∑ᶠ a : (H ⧸ V) × S, φ (E a).out :=
        (finsum_comp_equiv E (f := fun q : Γ ⧸ L => φ q.out)).symm
    _ = ∑ᶠ a : (H ⧸ V) × S, φ (e a.1.out * a.2.1.out) :=
        finsum_congr fun a => hφout _
    _ = ∑ᶠ m : H ⧸ V, ∑ᶠ q : S, φ (e m.out * q.1.out) :=
        finsum_curry (fun a : (H ⧸ V) × S => φ (e a.1.out * a.2.1.out)) hsupp
    _ = _ := by
        refine finsum_congr fun m => ?_
        rw [finsum_set_coe_eq_finsum_mem S (f := fun q : Γ ⧸ L => φ (e m.out * q.out)),
          finsum_mem_def]
        refine finsum_congr fun q => ?_
        by_cases hq : p q.out ∈ V
        · have hq' : q ∈ S := hq
          rw [Set.indicator_of_mem hq', Set.indicator_of_mem (show p q.out ∈ (V : Set H) from hq)]
          simp
        · have hq' : q ∉ S := hq
          rw [Set.indicator_of_notMem hq',
            Set.indicator_of_notMem (show p q.out ∉ (V : Set H) from hq)]
          simp

end GlobalTheory.CompanionTheory.FinActS.SumFiber
