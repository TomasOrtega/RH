import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.Cyc

/- English proof (translation)
Introduce `g m ζ hζ`. Use `haveI : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Om l) := fun i => ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Use `⟨_, ?_, cyclotomicCharacter.spec l (n := m) (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ hζ⟩` and prove the remaining obligations. Use `set z : ℤ_[l] := ((cycZ (F := ℚ_[l]) (Ω := Om l) l g : ℤ_[l]ˣ) : ℤ_[l]) with hz`. Express the relevant statement in the definitionally equal form `‖(z : ℚ_[l]) - (((PadicInt.toZModPow m z).val : ℕ) : ℚ_[l])‖ ≤ _`.

Establish `h : z - (((PadicInt.toZModPow m z).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m}` using `by haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Rewrite using `[← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]`. Use `(PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 h` as an intermediate fact. Rewrite `this` using `[PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast]`. Then use the resulting hypothesis.
-/
theorem isCyc_map_cycZ (l : ℕ) [Fact l.Prime] :
    IsCyc ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l)) := by
  intro g m ζ hζ
  haveI : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Om l) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨_, ?_, cyclotomicCharacter.spec l (n := m)
    (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ hζ⟩
  set z : ℤ_[l] := ((cycZ (F := ℚ_[l]) (Ω := Om l) l g : ℤ_[l]ˣ) : ℤ_[l]) with hz
  change ‖(z : ℚ_[l]) - (((PadicInt.toZModPow m z).val : ℕ) : ℚ_[l])‖ ≤ _
  have h : z - (((PadicInt.toZModPow m z).val : ℕ) : ℤ_[l]) ∈
      Ideal.span {(l : ℤ_[l]) ^ m} := by
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
      sub_self]
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 h
  rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this

/- English proof (translation)
Introduce `l _ u`. Establish `hχ` using `isCyc_map_cycZ l`. Use `set χ := (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp (cycZ (F := ℚ_[l]) (Ω := Om l) l) with hχdef`. Establish `hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1` using `PadicInt.norm_units u`. Establish `hs : IsClosed {g : GQ l | (χ g : ℚ_[l]) = ((u : ℤ_[l]) : ℚ_[l])}` using `isClosed_eq hχ.continuous continuous_const`.

Establish `key` using `hs.isCompact.inter_iInter_nonempty (fun x : MaximalUnramifiedExtension l => ((IntermediateField.adjoin ℚ_[l] {(x : Om l)}).fixingSubgroup : Set (GQ l))) (fun x => by haveI := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (x : Om l))`. Conclude with `IntermediateField.fixingSubgroup_isClosed _)`. Use the proof step `(fun t => by`. Set `S : Set (Om l)` to `(fun x : MaximalUnramifiedExtension l => (x : Om l)) '' (t : Set (MaximalUnramifiedExtension l))`. Use `haveI : Finite S := (t.finite_toSet.image _).to_subtype`.

Set `K : FinExt l` to `⟨IntermediateField.adjoin ℚ_[l] S, IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)⟩`. Take `⟨g, hg, hgu⟩` from `exists_chi_eq K χ hχ _ hu1`. Use `⟨g, hgu, Set.mem_iInter₂.2 fun x hx => ?_⟩` and prove the remaining obligations. Use `(mem_fixingSubgroup_adjoin_iff _ g).2 ?_` and prove the remaining obligations. Introduce and unpack `y rfl`.

Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩, x.2⟩)`. Take `⟨g, hgu, hg⟩` from `key`. Use `⟨g, fun x hx => ?_, Units.ext (Subtype.ext hgu)⟩` and prove the remaining obligations. Conclude with `(mem_fixingSubgroup_adjoin_iff _ g).1 (Set.mem_iInter.1 hg ⟨x, hx⟩) x rfl`.
-/
theorem exists_inertia_cycZ_eq : ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ), ∃ σ : GQ l, (∀ x ∈ MaximalUnramifiedExtension l, σ x = x) ∧ cycZ (F := ℚ_[l]) (Ω := Om l) l σ = u := by
  intro l _ u
  have hχ := isCyc_map_cycZ l
  set χ := (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
      (cycZ (F := ℚ_[l]) (Ω := Om l) l) with hχdef
  have hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u
  have hs : IsClosed {g : GQ l | (χ g : ℚ_[l]) = ((u : ℤ_[l]) : ℚ_[l])} :=
    isClosed_eq hχ.continuous continuous_const
  have key := hs.isCompact.inter_iInter_nonempty
    (fun x : MaximalUnramifiedExtension l => ((IntermediateField.adjoin ℚ_[l] {(x : Om l)}).fixingSubgroup : Set (GQ l)))
    (fun x => by
      haveI := IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (x : Om l))
      exact IntermediateField.fixingSubgroup_isClosed _)
    (fun t => by
      let S : Set (Om l) := (fun x : MaximalUnramifiedExtension l => (x : Om l)) '' (t : Set (MaximalUnramifiedExtension l))
      haveI : Finite S := (t.finite_toSet.image _).to_subtype
      let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S,
        IntermediateField.finiteDimensional_adjoin
          (fun x _ => Algebra.IsIntegral.isIntegral x)⟩
      obtain ⟨g, hg, hgu⟩ := exists_chi_eq K χ hχ _ hu1
      refine ⟨g, hgu, Set.mem_iInter₂.2 fun x hx => ?_⟩
      refine (mem_fixingSubgroup_adjoin_iff _ g).2 ?_
      rintro y rfl
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        ⟨IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩, x.2⟩)
  obtain ⟨g, hgu, hg⟩ := key
  refine ⟨g, fun x hx => ?_, Units.ext (Subtype.ext hgu)⟩
  exact (mem_fixingSubgroup_adjoin_iff _ g).1 (Set.mem_iInter.1 hg ⟨x, hx⟩) x rfl

end GlobalTheory.Cyc
