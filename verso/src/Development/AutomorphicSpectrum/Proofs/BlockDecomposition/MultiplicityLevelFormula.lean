import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.SelfDualMeasureSFinite
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegLoc.NuIndex

open MeasureTheory

section Abstract

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Establish `hKm : MeasurableSet (K : Set V)` using `(AddSubgroup.isOpen_mono hle ho).measurableSet`. Establish `hemb : MeasurableEmbedding (K.subtype : K → V)` using `MeasurableEmbedding.subtype_coe hKm`. Establish `: (μ.comap (K.subtype : K → V)).IsAddLeftInvariant` using `Measure.IsAddLeftInvariant.comap μ hemb`. Establish `: (H.addSubgroupOf K).FiniteIndex` using `⟨hi⟩`. Establish `hHm : MeasurableSet ((H.addSubgroupOf K : AddSubgroup K) : Set K)` using `(ho.preimage continuous_subtype_val).measurableSet`.

Establish `key` using `AddSubgroup.index_mul_measure (H.addSubgroupOf K) hHm (μ.comap (K.subtype : K → V))`. Rewrite `key` using `[hemb.comap_apply, hemb.comap_apply]`. Establish `h1 : (K.subtype : K → V) '' Set.univ = (K : Set V)` using `by simp`. Establish `h2 : (K.subtype : K → V) '' ((H.addSubgroupOf K : AddSubgroup K) : Set K) = (H : Set V)`. Use extensionality with `x`.

Simplify using `only [AddSubgroup.coe_subtype, Set.mem_image, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `hx`.

Conclude with `⟨⟨x, hle hx⟩, hx, rfl⟩`. Rewrite `key` using `[h1, h2]`. Rewrite using `[← key]`. Both sides reduce to the same expression.
-/
theorem measure_eq_relIndex_mul (μ : Measure V) [μ.IsAddLeftInvariant] (K H : AddSubgroup V)
    (hle : H ≤ K) (ho : IsOpen (H : Set V)) (hi : H.relIndex K ≠ 0) :
    μ K = (H.relIndex K : ENNReal) * μ H := by
  have hKm : MeasurableSet (K : Set V) := (AddSubgroup.isOpen_mono hle ho).measurableSet
  have hemb : MeasurableEmbedding (K.subtype : K → V) := MeasurableEmbedding.subtype_coe hKm
  have : (μ.comap (K.subtype : K → V)).IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ hemb
  have : (H.addSubgroupOf K).FiniteIndex := ⟨hi⟩
  have hHm : MeasurableSet ((H.addSubgroupOf K : AddSubgroup K) : Set K) :=
    (ho.preimage continuous_subtype_val).measurableSet
  have key := AddSubgroup.index_mul_measure (H.addSubgroupOf K) hHm (μ.comap (K.subtype : K → V))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have h1 : (K.subtype : K → V) '' Set.univ = (K : Set V) := by simp
  have h2 : (K.subtype : K → V) '' ((H.addSubgroupOf K : AddSubgroup K) : Set K) = (H : Set V) := by
    ext x
    simp only [AddSubgroup.coe_subtype, Set.mem_image, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [h1, h2] at key
  rw [← key]
  rfl

/- English proof (translation)
Establish `hfN : ∀ p, f p ∈ N` using `fun p => by`. Rewrite using `[hN]`. Conclude with `AddSubgroup.mem_sup_right ⟨p, rfl⟩`. Set `h : P →+ N ⧸ L.addSubgroupOf N` to `(QuotientAddGroup.mk' _).comp (f.codRestrict N hfN)`. Establish `hs : Function.Surjective h`.

Introduce `c`. Proceed by induction on `c using QuotientAddGroup.induction_on with`. Consider the case `H x`. Take `⟨x, hx⟩` from `x`. Establish `hx'` using `hx`.

Rewrite `hx'` using `[hN, AddSubgroup.mem_sup]`. Take `⟨l, hl, _, ⟨p, rfl⟩, rfl⟩` from `hx'`. Use `⟨p, ?_⟩` and prove the remaining obligations. Use `show (QuotientAddGroup.mk _ : N ⧸ L.addSubgroupOf N) = _`. Rewrite using `[QuotientAddGroup.eq]`.

Simplify using `[AddSubgroup.mem_addSubgroupOf, hl]`. Establish `hk : h.ker = g.ker`. Use extensionality with `p`. Rewrite using `[AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hfg]`. Use `show (QuotientAddGroup.mk _ : N ⧸ L.addSubgroupOf N) = 0 ↔ _`.

Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Both sides reduce to the same expression. Establish `e1` using `(QuotientAddGroup.quotientKerEquivOfSurjective h hs).toEquiv`. Establish `e2` using `(QuotientAddGroup.quotientKerEquivRange g).toEquiv`. Establish `e3 : (P ⧸ h.ker) ≃ (P ⧸ g.ker)` using `by rw [hk]`.

Establish `hr : Set.range g = (g.range : Set Q)` using `(AddMonoidHom.coe_range g).symm`. Rewrite using `[hr]`. Conclude with `Nat.card_congr (e1.symm.trans (e3.trans e2))`.
-/
theorem relIndex_eq_card_range {W P Q : Type} [AddCommGroup W] [AddCommGroup P] [AddCommGroup Q] (L N : AddSubgroup W)
    (f : P →+ W) (g : P →+ Q) (hN : N = L ⊔ f.range) (hfg : ∀ p, g p = 0 ↔ f p ∈ L) :
    L.relIndex N = Nat.card (Set.range g) := by
  have hfN : ∀ p, f p ∈ N := fun p => by
    rw [hN]; exact AddSubgroup.mem_sup_right ⟨p, rfl⟩
  let h : P →+ N ⧸ L.addSubgroupOf N := (QuotientAddGroup.mk' _).comp (f.codRestrict N hfN)
  have hs : Function.Surjective h := by
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      have hx' := hx
      rw [hN, AddSubgroup.mem_sup] at hx'
      obtain ⟨l, hl, _, ⟨p, rfl⟩, rfl⟩ := hx'
      refine ⟨p, ?_⟩
      show (QuotientAddGroup.mk _ : N ⧸ L.addSubgroupOf N) = _
      rw [QuotientAddGroup.eq]
      simp [AddSubgroup.mem_addSubgroupOf, hl]
  have hk : h.ker = g.ker := by
    ext p
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hfg]
    show (QuotientAddGroup.mk _ : N ⧸ L.addSubgroupOf N) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  have e1 := (QuotientAddGroup.quotientKerEquivOfSurjective h hs).toEquiv
  have e2 := (QuotientAddGroup.quotientKerEquivRange g).toEquiv
  have e3 : (P ⧸ h.ker) ≃ (P ⧸ g.ker) := by rw [hk]
  have hr : Set.range g = (g.range : Set Q) := (AddMonoidHom.coe_range g).symm
  rw [hr]
  exact Nat.card_congr (e1.symm.trans (e3.trans e2))

/- English proof (translation)
Use `set N : AddSubgroup V := L ⊔ L.map φ with hNdef`. Establish `hset : {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + φ y'} = (N : Set V)`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, SetLike.mem_coe, hNdef, AddSubgroup.mem_sup, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, y', hy', rfl⟩`. Conclude with `⟨y, hy, _, ⟨y', hy', rfl⟩, rfl⟩`. Introduce and unpack `⟨y, hy, _, ⟨y', hy', rfl⟩, rfl⟩`. Conclude with `⟨y, hy, y', hy', rfl⟩`. Establish `hle : L ≤ N` using `le_sup_left`.

Establish `hNc : IsCompact (N : Set V)`. Establish `: (N : Set V) = (fun p : V × V => p.1 + φ p.2) '' ((L : Set V) ×ˢ (L : Set V))`. Rewrite using `[← hset]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, y', hy', rfl⟩`. Conclude with `⟨(y, y'), ⟨hy, hy'⟩, rfl⟩`. Introduce and unpack `⟨⟨y, y'⟩, ⟨hy, hy'⟩, rfl⟩`. Conclude with `⟨y, hy, y', hy', rfl⟩`. Rewrite using `[this]`.

Conclude with `(hLc.prod hLc).image (continuous_fst.add (hφ.comp continuous_snd))`. Establish `hidx : L.relIndex N ≠ 0` using `by haveI : CompactSpace N := isCompact_iff_compactSpace.mp hNc`. Establish `ho : IsOpen ((L.addSubgroupOf N : AddSubgroup N) : Set N)` using `hLo.preimage continuous_subtype_val`. Use `haveI : Finite (N ⧸ L.addSubgroupOf N) := AddSubgroup.quotient_finite_of_isOpen _ ho`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.

Establish `h0 : lam (L : Set V) ≠ 0` using `(hLo.measure_pos lam ⟨0, L.zero_mem⟩).ne'`. Establish `htop : lam (L : Set V) ≠ ⊤` using `hLc.measure_lt_top.ne`. Rewrite using `[hset, measure_eq_relIndex_mul lam N L hle hLo hidx, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel h0 htop, mul_one, ENNReal.toReal_natCast, relIndex_eq_card_range L N f g (by rw [hr]) hfg]`.
-/
theorem vol_ratio (lam : Measure V) [lam.IsAddHaarMeasure] (L : AddSubgroup V) (hLo : IsOpen (L : Set V))
    (hLc : IsCompact (L : Set V)) (φ : V →+ V) (hφ : Continuous φ) {P Q : Type} [AddCommGroup P] [AddCommGroup Q]
    (f : P →+ V) (g : P →+ Q) (hr : f.range = L.map φ) (hfg : ∀ p, g p = 0 ↔ f p ∈ L) :
    (lam {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + φ y'} / lam L).toReal = Nat.card (Set.range g) := by
  set N : AddSubgroup V := L ⊔ L.map φ with hNdef
  have hset : {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + φ y'} = (N : Set V) := by
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, hNdef, AddSubgroup.mem_sup, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩
      exact ⟨y, hy, _, ⟨y', hy', rfl⟩, rfl⟩
    · rintro ⟨y, hy, _, ⟨y', hy', rfl⟩, rfl⟩
      exact ⟨y, hy, y', hy', rfl⟩
  have hle : L ≤ N := le_sup_left
  have hNc : IsCompact (N : Set V) := by
    have : (N : Set V) = (fun p : V × V => p.1 + φ p.2) '' ((L : Set V) ×ˢ (L : Set V)) := by
      rw [← hset]
      ext x
      constructor
      · rintro ⟨y, hy, y', hy', rfl⟩
        exact ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
      · rintro ⟨⟨y, y'⟩, ⟨hy, hy'⟩, rfl⟩
        exact ⟨y, hy, y', hy', rfl⟩
    rw [this]
    exact (hLc.prod hLc).image (continuous_fst.add (hφ.comp continuous_snd))
  have hidx : L.relIndex N ≠ 0 := by
    haveI : CompactSpace N := isCompact_iff_compactSpace.mp hNc
    have ho : IsOpen ((L.addSubgroupOf N : AddSubgroup N) : Set N) := hLo.preimage continuous_subtype_val
    haveI : Finite (N ⧸ L.addSubgroupOf N) := AddSubgroup.quotient_finite_of_isOpen _ ho
    exact AddSubgroup.index_ne_zero_of_finite
  have h0 : lam (L : Set V) ≠ 0 := (hLo.measure_pos lam ⟨0, L.zero_mem⟩).ne'
  have htop : lam (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  rw [hset, measure_eq_relIndex_mul lam N L hle hLo hidx, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel h0 htop, mul_one,
    ENNReal.toReal_natCast, relIndex_eq_card_range L N f g (by rw [hr]) hfg]

end Abstract

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis (Fv F v) bs)`. Use `haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) (Fv F v ⊗[F] E)`. Set `e` to `(Algebra.TensorProduct.basis (Fv F v) bs).equivFun`. Conclude with `⟨{ toEquiv := e.toEquiv continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }, fun x k => rfl⟩`.
-/
theorem exists_coord_homeo : ∃ h : (Fv F v ⊗[F] E) ≃ₜ (Fin d → Fv F v),
    ∀ x k, h x k = (Algebra.TensorProduct.basis (Fv F v) bs).repr x k := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis (Fv F v) bs)
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) (Fv F v ⊗[F] E)
  let e := (Algebra.TensorProduct.basis (Fv F v) bs).equivFun
  exact ⟨{ toEquiv := e.toEquiv
           continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
           continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap },
    fun x k => rfl⟩

/- English proof (translation)
Take `⟨h, hh⟩` from `exists_coord_homeo bs v`. Establish `: Rv bs v = h ⁻¹' (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))`. Use extensionality with `x`. Simplify using `[Rv, Set.mem_pi, hh]`. Rewrite using `[this]`.

Conclude with `(isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _).preimage h.continuous`.
-/
theorem isOpen_Rv : IsOpen (Rv bs v) := by
  obtain ⟨h, hh⟩ := exists_coord_homeo bs v
  have : Rv bs v = h ⁻¹' (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    simp [Rv, Set.mem_pi, hh]
  rw [this]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _).preimage h.continuous

/- English proof (translation)
Take `⟨h, hh⟩` from `exists_coord_homeo bs v`. Establish `: Rv bs v = h ⁻¹' (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))`. Use extensionality with `x`. Simplify using `[Rv, Set.mem_pi, hh]`. Rewrite using `[this, h.isCompact_preimage]`.

Conclude with `isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v`.
-/
theorem isCompact_Rv : IsCompact (Rv bs v) := by
  obtain ⟨h, hh⟩ := exists_coord_homeo bs v
  have : Rv bs v = h ⁻¹' (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    simp [Rv, Set.mem_pi, hh]
  rw [this, h.isCompact_preimage]
  exact isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v

include bs in
/- English proof (translation)
Take `⟨h, -⟩` from `exists_coord_homeo bs v`. Use `haveI : SecondCountableTopology (Fv F v) := LocMassOrdSF.secondCountable_Fv v`. Conclude with `h.isInducing.secondCountableTopology`.
-/
theorem secondCountable_tens : SecondCountableTopology (Fv F v ⊗[F] E) := by
  obtain ⟨h, -⟩ := exists_coord_homeo bs v
  haveI : SecondCountableTopology (Fv F v) := LocMassOrdSF.secondCountable_Fv v
  exact h.isInducing.secondCountableTopology

include bs in
/- English proof (translation)
Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis (Fv F v) bs)`. Conclude with `IsModuleTopology.isTopologicalRing (Fv F v) (Fv F v ⊗[F] E)`.
-/
theorem topRing_tens : IsTopologicalRing (Fv F v ⊗[F] E) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.Finite.of_basis (Algebra.TensorProduct.basis (Fv F v) bs)
  exact IsModuleTopology.isTopologicalRing (Fv F v) (Fv F v ⊗[F] E)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latO_iff {n : ℕ} (y : Fin n → Fv F v ⊗[F] E) : y ∈ latO bs v ↔ ∀ a, y a ∈ Rv bs v := Iff.rfl

end Lattice

section Good

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

/- English proof (translation)
Rewrite using `[Subring.coe_mul, Subring.coe_pow, Algebra.smul_def, map_pow, mul_comm]`. Both sides reduce to the same expression.
-/
theorem coe_mul_pow (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (c : S) :
    ((c * hG.pS ^ k : S) : Fv F v ⊗[F] E) = (ϖ ^ k) • (c : Fv F v ⊗[F] E) := by
  rw [Subring.coe_mul, Subring.coe_pow, Algebra.smul_def, map_pow, mul_comm]
  rfl

/- English proof (translation)
Establish `hne : ϖ ^ k ≠ 0` using `pow_ne_zero _ hG.unif_ne`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `Ideal.mem_span_singleton'.2 ⟨⟨_, h⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[coe_mul_pow, smul_smul, mul_inv_cancel₀ hne, one_smul]`.

Introduce `h`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 h`. Rewrite using `[coe_mul_pow, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Conclude with `c.2`.
-/
theorem inv_smul_mem_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (s : S) :
    (ϖ ^ k)⁻¹ • (s : Fv F v ⊗[F] E) ∈ S ↔ s ∈ lev hG.pS k := by
  have hne : ϖ ^ k ≠ 0 := pow_ne_zero _ hG.unif_ne
  constructor
  · intro h
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [coe_mul_pow, smul_smul, mul_inv_cancel₀ hne, one_smul]
  · intro h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
    rw [coe_mul_pow, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact c.2

/- English proof (translation)
Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hs`. Establish `hp : σS hG.pS = hG.pS` using `hG.quad.fix_ϖ`. Conclude with `Ideal.mem_span_singleton'.2 ⟨σS c, by rw [map_mul, map_pow, hp]⟩`.
-/
theorem sig_mem_lev (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) {s : S} (hs : s ∈ lev hG.pS k) :
    σS s ∈ lev hG.pS k := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
  have hp : σS hG.pS = hG.pS := hG.quad.fix_ϖ
  exact Ideal.mem_span_singleton'.2 ⟨σS c, by rw [map_mul, map_pow, hp]⟩

/- English proof (translation)
Use `⟨fun h => ?_, sig_mem_lev hG k⟩` and prove the remaining obligations. Use `sig_mem_lev hG k h` as an intermediate fact. Rewrite `this` using `[hG.quad.inv]`. Then use the resulting hypothesis.
-/
theorem sig_mem_lev_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (s : S) :
    σS s ∈ lev hG.pS k ↔ s ∈ lev hG.pS k := by
  refine ⟨fun h => ?_, sig_mem_lev hG k⟩
  have := sig_mem_lev hG k h
  rwa [hG.quad.inv] at this

/- English proof (translation)
Rewrite using `[← sig_mem_lev_iff hG k (∑ c, X a c * σS (p c))]`. Establish `: σS (∑ c, X a c * σS (p c)) = ∑ c, p c * X c a`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `h` using `congrFun (congrFun hX c) a`.

Establish `h' : σS (X a c) = X c a` using `by simpa [PositivityTheory.PfSWUS.Loc.cT] using h`. Rewrite using `[map_mul, hG.quad.inv, h', mul_comm]`. Rewrite using `[this]`.
-/
theorem sum_mem_lev_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (X : Matrix (Fin n) (Fin n) S)
    (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) (p : Fin n → S) (a : Fin n) :
    (∑ c, X a c * σS (p c)) ∈ lev hG.pS k ↔ (∑ c, p c * X c a) ∈ lev hG.pS k := by
  rw [← sig_mem_lev_iff hG k (∑ c, X a c * σS (p c))]
  have : σS (∑ c, X a c * σS (p c)) = ∑ c, p c * X c a := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h := congrFun (congrFun hX c) a
    have h' : σS (X a c) = X c a := by simpa [PositivityTheory.PfSWUS.Loc.cT] using h
    rw [map_mul, hG.quad.inv, h', mul_comm]
  rw [this]

/- English proof (translation)
Use `haveI := topRing_tens (E := E) bs v`. Use `haveI := secondCountable_tens (E := E) bs v`. Use `haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩`. Establish `hmem : ∀ y : Fin n → Fv F v ⊗[F] E, y ∈ L ↔ ∀ a, y a ∈ S`. Introduce `y`.

Establish `h1 : y ∈ L ↔ y ∈ latO bs v` using `by rw [← hL]; rfl`. Rewrite using `[h1, mem_latO_iff]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[← hG.carrier]`. Both sides reduce to the same expression.

Establish `hSo : IsOpen (S : Set (Fv F v ⊗[F] E))` using `by rw [hG.carrier]; exact isOpen_Rv bs v`. Establish `hSc : IsCompact (S : Set (Fv F v ⊗[F] E))` using `by rw [hG.carrier]; exact isCompact_Rv bs v`. Establish `hLset : (L : Set (Fin n → Fv F v ⊗[F] E)) = Set.pi Set.univ fun _ => (S : Set (Fv F v ⊗[F] E))`. Use extensionality with `y`. Simplify using `[Set.mem_pi, hmem]`.

Establish `hLo : IsOpen (L : Set (Fin n → Fv F v ⊗[F] E))`. Rewrite using `[hLset]`. Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => hSo`. Establish `hLc : IsCompact (L : Set (Fin n → Fv F v ⊗[F] E))`. Rewrite using `[hLset]`.

Conclude with `isCompact_univ_pi fun _ => hSc`. Use `set b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (hG.hermLev k X hX).1 with hb`. Set `φ : (Fin n → Fv F v ⊗[F] E) →+ (Fin n → Fv F v ⊗[F] E)` to `AddMonoidHom.mk' (fun y => b.mulVec y) (Matrix.mulVec_add b)`. Establish `hφ : Continuous φ` using `continuous_const.matrix_mulVec continuous_id`. Set `f : (Fin n → S) →+ (Fin n → Fv F v ⊗[F] E)` to `AddMonoidHom.mk' (fun p => b.mulVec fun c => ((σS (p c) : S) : Fv F v ⊗[F] E)) (by`.

Introduce `p q`. Rewrite using `[← Matrix.mulVec_add]`. Use `congr 1`. Use extensionality with `c`. Use the proof step `simp)`.

Set `g : (Fin n → S) →+ (Fin n → S ⧸ lev hG.pS k)` to `AddMonoidHom.mk' (fun p => Matrix.vecMul (fun c => Ideal.Quotient.mk (lev hG.pS k) (p c)) (red hG.pS k X)) (by`. Introduce `p q`. Rewrite using `[← Matrix.add_vecMul]`. Use `congr 1)`. Establish `hgdef : ∀ p, g p = Matrix.vecMul (fun c => Ideal.Quotient.mk (lev hG.pS k) (p c)) (red hG.pS k X)` using `fun _ => rfl`.

Establish `hr : f.range = L.map φ`. Use extensionality with `x`. Simplify using `only [AddMonoidHom.mem_range, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, rfl⟩`.

Conclude with `⟨fun c => ((σS (p c) : S) : Fv F v ⊗[F] E), (hmem _).2 fun c => (σS (p c)).2, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `hy'` using `(hmem y).1 hy`. Use `⟨fun c => σS ⟨y c, hy' c⟩, ?_⟩` and prove the remaining obligations. Use `show b.mulVec _ = b.mulVec _`.

Use `congr 1`. Use extensionality with `c`. Rewrite using `[hG.quad.inv]`. Establish `hfg : ∀ p, g p = 0 ↔ f p ∈ L`. Introduce `p`.

Rewrite using `[hmem]`. Establish `hfa : ∀ a, f p a = (ϖ ^ k)⁻¹ • (((∑ c, X a c * σS (p c) : S)) : Fv F v ⊗[F] E)`. Introduce `a`. Use `show (b.mulVec fun c => ((σS (p c) : S) : Fv F v ⊗[F] E)) a = _`. Use `show ∑ c, b a c * ((σS (p c) : S) : Fv F v ⊗[F] E) = _`.

Rewrite using `[AddSubmonoidClass.coe_finset_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Subring.coe_mul]`. Conclude with `smul_mul_assoc _ _ _`. Establish `hga : ∀ a, g p a = Ideal.Quotient.mk (lev hG.pS k) (∑ c, p c * X c a)`.

Introduce `a`. Rewrite using `[hgdef, map_sum]`. Simplify using `[Matrix.vecMul, dotProduct, red, map_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `h a`.

Rewrite using `[hfa, inv_smul_mem_iff hG, sum_mem_lev_iff hG k X hX, ← Ideal.Quotient.eq_zero_iff_mem, ← hga, h]`. Both sides reduce to the same expression. Introduce `h`. Use extensionality with `a`. Use `h a` as an intermediate fact.

Rewrite `this` using `[hfa, inv_smul_mem_iff hG, sum_mem_lev_iff hG k X hX, ← Ideal.Quotient.eq_zero_iff_mem, ← hga]`. Conclude with `this`. Establish `hrange : Set.range g = Set.range fun x : Fin n → S ⧸ lev hG.pS k => Matrix.vecMul x (red hG.pS k X)`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨p, rfl⟩`. Conclude with `⟨_, rfl⟩`. Introduce and unpack `⟨x, rfl⟩ choose p hp using fun c => Ideal.Quotient.mk_surjective (x c)`. Conclude with `⟨p, by rw [hgdef]; congr 1; ext c; exact hp c⟩`. Use `vol_ratio lam L hLo hLc φ hφ f g hr hfg` as an intermediate fact.

Rewrite `this` using `[hrange]`. Conclude with `this`.
-/
theorem multiplicity_hermitian_level (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (lam : Measure (Fin n → Fv F v ⊗[F] E))
    (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (hlam : lam.IsAddHaarMeasure)
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (k : ℕ) (X : Matrix (Fin n) (Fin n) S)
    (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) :
    nu2 lam L L (hG.hermLev k X hX).1 = (nuAt hG.pS (red hG.pS k X) : ℝ) := by
  haveI := topRing_tens (E := E) bs v
  haveI := secondCountable_tens (E := E) bs v
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hmem : ∀ y : Fin n → Fv F v ⊗[F] E, y ∈ L ↔ ∀ a, y a ∈ S := by
    intro y
    have h1 : y ∈ L ↔ y ∈ latO bs v := by rw [← hL]; rfl
    rw [h1, mem_latO_iff]
    refine forall_congr' fun a => ?_
    rw [← hG.carrier]; rfl
  have hSo : IsOpen (S : Set (Fv F v ⊗[F] E)) := by rw [hG.carrier]; exact isOpen_Rv bs v
  have hSc : IsCompact (S : Set (Fv F v ⊗[F] E)) := by rw [hG.carrier]; exact isCompact_Rv bs v
  have hLset : (L : Set (Fin n → Fv F v ⊗[F] E)) = Set.pi Set.univ fun _ => (S : Set (Fv F v ⊗[F] E)) := by
    ext y
    simp [Set.mem_pi, hmem]
  have hLo : IsOpen (L : Set (Fin n → Fv F v ⊗[F] E)) := by
    rw [hLset]; exact isOpen_set_pi Set.finite_univ fun _ _ => hSo
  have hLc : IsCompact (L : Set (Fin n → Fv F v ⊗[F] E)) := by
    rw [hLset]; exact isCompact_univ_pi fun _ => hSc
  set b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (hG.hermLev k X hX).1 with hb
  let φ : (Fin n → Fv F v ⊗[F] E) →+ (Fin n → Fv F v ⊗[F] E) :=
    AddMonoidHom.mk' (fun y => b.mulVec y) (Matrix.mulVec_add b)
  have hφ : Continuous φ := continuous_const.matrix_mulVec continuous_id
  let f : (Fin n → S) →+ (Fin n → Fv F v ⊗[F] E) :=
    AddMonoidHom.mk' (fun p => b.mulVec fun c => ((σS (p c) : S) : Fv F v ⊗[F] E)) (by
      intro p q
      rw [← Matrix.mulVec_add]
      congr 1
      ext c
      simp)
  let g : (Fin n → S) →+ (Fin n → S ⧸ lev hG.pS k) :=
    AddMonoidHom.mk' (fun p => Matrix.vecMul (fun c => Ideal.Quotient.mk (lev hG.pS k) (p c)) (red hG.pS k X)) (by
      intro p q
      rw [← Matrix.add_vecMul]
      congr 1)
  have hgdef : ∀ p, g p = Matrix.vecMul (fun c => Ideal.Quotient.mk (lev hG.pS k) (p c)) (red hG.pS k X) := fun _ => rfl
  have hr : f.range = L.map φ := by
    ext x
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_map]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨fun c => ((σS (p c) : S) : Fv F v ⊗[F] E), (hmem _).2 fun c => (σS (p c)).2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hy' := (hmem y).1 hy
      refine ⟨fun c => σS ⟨y c, hy' c⟩, ?_⟩
      show b.mulVec _ = b.mulVec _
      congr 1
      ext c
      rw [hG.quad.inv]
  have hfg : ∀ p, g p = 0 ↔ f p ∈ L := by
    intro p
    rw [hmem]
    have hfa : ∀ a, f p a = (ϖ ^ k)⁻¹ • (((∑ c, X a c * σS (p c) : S)) : Fv F v ⊗[F] E) := by
      intro a
      show (b.mulVec fun c => ((σS (p c) : S) : Fv F v ⊗[F] E)) a = _
      show ∑ c, b a c * ((σS (p c) : S) : Fv F v ⊗[F] E) = _
      rw [AddSubmonoidClass.coe_finset_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Subring.coe_mul]
      exact smul_mul_assoc _ _ _
    have hga : ∀ a, g p a = Ideal.Quotient.mk (lev hG.pS k) (∑ c, p c * X c a) := by
      intro a
      rw [hgdef, map_sum]
      simp [Matrix.vecMul, dotProduct, red, map_mul]
    constructor
    · intro h a
      rw [hfa, inv_smul_mem_iff hG, sum_mem_lev_iff hG k X hX, ← Ideal.Quotient.eq_zero_iff_mem, ← hga, h]
      rfl
    · intro h
      ext a
      have := h a
      rw [hfa, inv_smul_mem_iff hG, sum_mem_lev_iff hG k X hX, ← Ideal.Quotient.eq_zero_iff_mem, ← hga] at this
      exact this
  have hrange : Set.range g = Set.range fun x : Fin n → S ⧸ lev hG.pS k => Matrix.vecMul x (red hG.pS k X) := by
    ext w
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      choose p hp using fun c => Ideal.Quotient.mk_surjective (x c)
      exact ⟨p, by rw [hgdef]; congr 1; ext c; exact hp c⟩
  have := vol_ratio lam L hLo hLc φ hφ f g hr hfg
  rw [hrange] at this
  exact this

end Good

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG lam L hlam hL k X hX`. Conclude with `multiplicity_hermitian_level hG lam L hlam hL k X hX`.
-/
theorem nuLev : PositivityTheory.SiegelWeilFormula.Gunr.NuLev := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG lam L hlam hL k X hX
  exact multiplicity_hermitian_level hG lam L hlam hL k X hX

end GlobalTheory.CompanionTheory.SiegLoc.NuIndex

end
