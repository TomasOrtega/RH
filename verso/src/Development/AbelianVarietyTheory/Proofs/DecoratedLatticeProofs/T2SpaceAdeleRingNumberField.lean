import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

open IsDedekindDomain NumberField Matrix Topology
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompactOpenIntegers

section Local
variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Set `f : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F)` to `(IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))`. Establish `hval : ∀ a : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) : v.adicCompletion F) = v.valuation F (algebraMap (𝓞 F) F a)` using `fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F a)`. Establish `hmax : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) < 1 → IsLocalRing.residue _ x = 0` using `fun x hx => by`. Rewrite using `[IsLocalRing.residue_eq_zero_iff]`. Conclude with `(Valuation.mem_maximalIdeal_iff _ _).2 hx`.

Establish `hk : ∀ a ∈ v.asIdeal, f a = 0` using `fun a ha => by`. Use `hmax _ ?_` and prove the remaining obligations. Rewrite using `[hval]`. Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem v a).2 ha`. Establish `hs : Function.Surjective f`.

Introduce `y`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`. Establish `ho : {z : v.adicCompletion F | Valued.v (z - x) < 1} ∈ nhds (x : v.adicCompletion F)`. Establish `h1 : {z : v.adicCompletion F | Valued.v z < 1} ∈ nhds (0 : v.adicCompletion F)`. Rewrite using `[Valued.mem_nhds_zero]`.

Conclude with `⟨1, fun z hz => by simpa using hz⟩`. Establish `h2 : Filter.Tendsto (fun z : v.adicCompletion F => z - x) (nhds (x : v.adicCompletion F)) (nhds 0)`. Establish `: IsTopologicalAddGroup (v.adicCompletion F)` using `IsUniformAddGroup.to_topologicalAddGroup`. Establish `: Continuous fun z : v.adicCompletion F => z - x` using `continuous_id.sub continuous_const`. Simplify using `using this.tendsto (x : v.adicCompletion F)`.

Conclude with `h2 h1`. Take `⟨k, hk⟩` from `(HeightOneSpectrum.denseRange_algebraMap F v).mem_nhds ho`. Establish `hk' : Valued.v (algebraMap F (v.adicCompletion F) k - x) < 1` using `hk`. Establish `hv : ∀ k : F, Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k` using `fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k`. Establish `hk1 : v.valuation F k ≤ 1`.

Rewrite using `[← hv]`. Establish `: algebraMap F (v.adicCompletion F) k = (algebraMap F (v.adicCompletion F) k - x) + x` using `(sub_add_cancel _ _).symm`. Rewrite using `[this]`. Conclude with `Valuation.map_add_le _ hk'.le x.2`. Take `⟨a, ha⟩` from `v.exists_valuation_sub_lt_of_integer hk1 1`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Use `Ideal.Quotient.eq.2 ((IsLocalRing.residue_eq_zero_iff _).1 (hmax _ ?_))` and prove the remaining obligations. Establish `: ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a - x : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a - k) + (algebraMap F (v.adicCompletion F) k - x)`. Rewrite using `[RingHom.map_sub]`. Establish `: ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)` using `rfl`.

Rewrite using `[← this]`. Conclude with `(sub_add_sub_cancel _ _ _).symm`. Rewrite using `[this]`. Use `Valuation.map_add_lt _ ?_ hk'` and prove the remaining obligations. Rewrite using `[hv]`.

Conclude with `ha`. Establish `: Finite (𝓞 F ⧸ v.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot`. Conclude with `Finite.of_surjective (Ideal.Quotient.lift v.asIdeal f hk) (Ideal.Quotient.lift_surjective_of_surjective _ hk hs)`.
-/
theorem finite_res (v : HeightOneSpectrum (𝓞 F)) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  let f : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hval : ∀ a : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) :
      v.adicCompletion F) = v.valuation F (algebraMap (𝓞 F) F a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F a)
  have hmax : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) < 1 →
      IsLocalRing.residue _ x = 0 := fun x hx => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff _ _).2 hx
  have hk : ∀ a ∈ v.asIdeal, f a = 0 := fun a ha => by
    refine hmax _ ?_
    rw [hval]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem v a).2 ha
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have ho : {z : v.adicCompletion F | Valued.v (z - x) < 1} ∈ nhds (x : v.adicCompletion F) := by
      have h1 : {z : v.adicCompletion F | Valued.v z < 1} ∈ nhds (0 : v.adicCompletion F) := by
        rw [Valued.mem_nhds_zero]
        exact ⟨1, fun z hz => by simpa using hz⟩
      have h2 : Filter.Tendsto (fun z : v.adicCompletion F => z - x) (nhds (x : v.adicCompletion F)) (nhds 0) := by
        have : IsTopologicalAddGroup (v.adicCompletion F) := IsUniformAddGroup.to_topologicalAddGroup
        have : Continuous fun z : v.adicCompletion F => z - x := continuous_id.sub continuous_const
        simpa using this.tendsto (x : v.adicCompletion F)
      exact h2 h1
    obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap F v).mem_nhds ho
    have hk' : Valued.v (algebraMap F (v.adicCompletion F) k - x) < 1 := hk
    have hv : ∀ k : F, Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k := fun k =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    have hk1 : v.valuation F k ≤ 1 := by
      rw [← hv]
      have : algebraMap F (v.adicCompletion F) k = (algebraMap F (v.adicCompletion F) k - x) + x :=
        (sub_add_cancel _ _).symm
      rw [this]
      exact Valuation.map_add_le _ hk'.le x.2
    obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hk1 1
    refine ⟨a, ?_⟩
    refine Ideal.Quotient.eq.2 ((IsLocalRing.residue_eq_zero_iff _).1 (hmax _ ?_))
    have : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a - x : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a - k) +
          (algebraMap F (v.adicCompletion F) k - x) := by
      rw [RingHom.map_sub]
      have : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl
      rw [← this]
      exact (sub_add_sub_cancel _ _ _).symm
    rw [this]
    refine Valuation.map_add_lt _ ?_ hk'
    rw [hv]
    exact ha
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  exact Finite.of_surjective (Ideal.Quotient.lift v.asIdeal f hk) (Ideal.Quotient.lift_surjective_of_surjective _ hk hs)

/- English proof (translation)
Establish `h : CompactSpace (Valued.integer (v.adicCompletion F))`. Rewrite using `[Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]`. Use `⟨?_, (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F)), finite_res F v⟩` and prove the remaining obligations. Conclude with `(Valued.isClosed_integer (v.adicCompletion F)).completeSpace_coe`. Conclude with `isCompact_iff_compactSpace.2 h`.
-/
theorem compact_int (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have h : CompactSpace (Valued.integer (v.adicCompletion F)) := by
    rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
    refine ⟨?_, (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F)), finite_res F v⟩
    exact (Valued.isClosed_integer (v.adicCompletion F)).completeSpace_coe
  exact isCompact_iff_compactSpace.2 h

/- English proof (translation)
The claim follows from `Valued.isOpen_valuationSubring _`.
-/
theorem open_int (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := Valued.isOpen_valuationSubring _

/- English proof (translation)
The claim follows from `RestrictedProduct.continuous_eval v`.
-/
theorem cont_eval (v : HeightOneSpectrum (𝓞 F)) : Continuous fun a : FiniteAdeleRing (𝓞 F) F => a v :=
  RestrictedProduct.continuous_eval v

/- English proof (translation)
Establish `h` using `RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (open_int F)`. Establish `hc : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F))` using `fun v => isCompact_iff_compactSpace.1 (compact_int F v)`. Establish `h1` using `h.isOpen_range`. Establish `h2` using `isCompact_range h.continuous`. Rewrite `h1`, `h2` using `[RestrictedProduct.range_structureMap]`.

Conclude with `⟨h1, h2⟩`.
-/
theorem open_compact_hat :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} ∧
    IsCompact {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  have h := RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (open_int F)
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => isCompact_iff_compactSpace.1 (compact_int F v)
  have h1 := h.isOpen_range
  have h2 := isCompact_range h.continuous
  rw [RestrictedProduct.range_structureMap] at h1 h2
  exact ⟨h1, h2⟩

/- English proof (translation)
Establish `h1 : T2Space (InfiniteAdeleRing F)` using `(inferInstance : T2Space ((v : InfinitePlace F) → v.Completion))`. Establish `h2 : T2Space (FiniteAdeleRing (𝓞 F) F)` using `T2Space.of_injective_continuous (f := fun (a : FiniteAdeleRing (𝓞 F) F) v => a v) (fun a b h => DFunLike.coe_injective h) (continuous_pi (cont_eval F))`. Conclude with `(inferInstance : T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))`.
-/
theorem t2Space_adeleRing_numberField : T2Space (AdeleRing (𝓞 F) F) := by
  have h1 : T2Space (InfiniteAdeleRing F) := (inferInstance : T2Space ((v : InfinitePlace F) → v.Completion))
  have h2 : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous (f := fun (a : FiniteAdeleRing (𝓞 F) F) v => a v)
      (fun a b h => DFunLike.coe_injective h) (continuous_pi (cont_eval F))
  exact (inferInstance : T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Local

section Grp
variable {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
The claim follows from `hJ.preimage (f := fun g => (⟨π g, hH g⟩ : H)) (hπ.subtype_mk hH)`.
-/
theorem open_comap {π : G →* G} (hπ : Continuous π) {H J : Subgroup G} (hH : ∀ g, π g ∈ H)
    (hJ : IsOpen (J.subgroupOf H : Set H)) : IsOpen (J.comap π : Set G) :=
  hJ.preimage (f := fun g => (⟨π g, hH g⟩ : H)) (hπ.subtype_mk hH)

/- English proof (translation)
Set `U : Subgroup G` to `K.comap p ⊓ J.comap q ⊓ L.comap r`. Establish `oU : IsOpen (U : Set G)` using `((open_comap hp mp oK).inter (open_comap hq mq oJ)).inter (open_comap hr mr oL)`. Set `c : G →* G` to `(MulAut.conj b).toMonoidHom`. Establish `hc : Continuous c` using `(continuous_const.mul continuous_id).mul continuous_const`. Establish `key : ∀ k, k ∈ Γ ⊓ U.comap c ↔ ∃ κ x y, κ ∈ K ∧ x ∈ J ∧ y ∈ L ∧ k = b⁻¹ * (κ * x * y) * b`.

Introduce `k`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, ⟨h1, h2⟩, h3⟩`. Use `⟨_, _, _, h1, h2, h3, ?_⟩` and prove the remaining obligations. Rewrite using `[dec (c k) (hΓ.conj_mem k h0 b)]`.

Express the relevant statement in the definitionally equal form `k = b⁻¹ * (b * k * b⁻¹) * b`. Use `group`. Introduce and unpack `⟨κ, x, y, h1, h2, h3, rfl⟩`. Establish `e : c (b⁻¹ * (κ * x * y) * b) = κ * x * y`. Express the relevant statement in the definitionally equal form `b * _ * b⁻¹ = _`.

Use `group`. Take `⟨a1, a2, a3⟩` from `eP κ (lK h1)`. Take `⟨b1, b2, b3⟩` from `eQ x (lJ h2)`. Take `⟨c1, c2, c3⟩` from `eR y (lL h3)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `hΓ.conj_mem' _ (Γ.mul_mem (Γ.mul_mem (hP (lK h1)) (hQ (lJ h2))) (hR (lL h3))) b`. Express the relevant statement in the definitionally equal form `c _ ∈ U`. Rewrite using `[e]`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p _ ∈ K`.

Simplify `h1` using `[a1, b1, c1]`. Express the relevant statement in the definitionally equal form `q _ ∈ J`. Simplify `h2` using `[a2, b2, c2]`. Express the relevant statement in the definitionally equal form `r _ ∈ L`. Simplify `h3` using `[a3, b3, c3]`.

Use `⟨Γ ⊓ U.comap c, inf_le_left, ?_, ?_, key⟩` and prove the remaining obligations. Establish `: ((Γ ⊓ U.comap c : Subgroup G) : Set G) = (fun z : G × G × G => b⁻¹ * (z.1 * z.2.1 * z.2.2) * b) '' ((K : Set G) ×ˢ (J : Set G) ×ˢ (L : Set G))`. Use extensionality with `k`. Rewrite using `[SetLike.mem_coe, key]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨κ, x, y, h1, h2, h3, rfl⟩`. Conclude with `⟨(κ, x, y), ⟨h1, h2, h3⟩, rfl⟩`. Introduce and unpack `⟨⟨κ, x, y⟩, ⟨h1, h2, h3⟩, rfl⟩`. Conclude with `⟨κ, x, y, h1, h2, h3, rfl⟩`. Rewrite using `[this]`.

Conclude with `(cK.prod (cJ.prod cL)).image (by fun_prop)`. Establish `: (((Γ ⊓ U.comap c).subgroupOf Γ : Subgroup Γ) : Set Γ) = (fun g : Γ => c g) ⁻¹' U`. Use extensionality with `g`. Conclude with `⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩`. Rewrite using `[this]`.

Conclude with `oU.preimage (hc.comp continuous_subtype_val)`.
-/
theorem glue [IsTopologicalGroup G] {p q r : G →* G} (hp : Continuous p) (hq : Continuous q) (hr : Continuous r)
    {Γ P Q R K J L : Subgroup G} (hΓ : Γ.Normal) (hP : P ≤ Γ) (hQ : Q ≤ Γ) (hR : R ≤ Γ)
    (mp : ∀ g, p g ∈ P) (mq : ∀ g, q g ∈ Q) (mr : ∀ g, r g ∈ R)
    (eP : ∀ g ∈ P, p g = g ∧ q g = 1 ∧ r g = 1) (eQ : ∀ g ∈ Q, p g = 1 ∧ q g = g ∧ r g = 1)
    (eR : ∀ g ∈ R, p g = 1 ∧ q g = 1 ∧ r g = g) (dec : ∀ g ∈ Γ, p g * q g * r g = g)
    (lK : K ≤ P) (cK : IsCompact (K : Set G)) (oK : IsOpen (K.subgroupOf P : Set P))
    (lJ : J ≤ Q) (cJ : IsCompact (J : Set G)) (oJ : IsOpen (J.subgroupOf Q : Set Q))
    (lL : L ≤ R) (cL : IsCompact (L : Set G)) (oL : IsOpen (L.subgroupOf R : Set R)) (b : G) :
    ∃ M ≤ Γ, IsCompact (M : Set G) ∧ IsOpen (M.subgroupOf Γ : Set Γ) ∧
      ∀ k, k ∈ M ↔ ∃ κ x y, κ ∈ K ∧ x ∈ J ∧ y ∈ L ∧ k = b⁻¹ * (κ * x * y) * b := by
  let U : Subgroup G := K.comap p ⊓ J.comap q ⊓ L.comap r
  have oU : IsOpen (U : Set G) := ((open_comap hp mp oK).inter (open_comap hq mq oJ)).inter (open_comap hr mr oL)
  let c : G →* G := (MulAut.conj b).toMonoidHom
  have hc : Continuous c := (continuous_const.mul continuous_id).mul continuous_const
  have key : ∀ k, k ∈ Γ ⊓ U.comap c ↔ ∃ κ x y, κ ∈ K ∧ x ∈ J ∧ y ∈ L ∧ k = b⁻¹ * (κ * x * y) * b := by
    intro k
    constructor
    · rintro ⟨h0, ⟨h1, h2⟩, h3⟩
      refine ⟨_, _, _, h1, h2, h3, ?_⟩
      rw [dec (c k) (hΓ.conj_mem k h0 b)]
      change k = b⁻¹ * (b * k * b⁻¹) * b
      group
    · rintro ⟨κ, x, y, h1, h2, h3, rfl⟩
      have e : c (b⁻¹ * (κ * x * y) * b) = κ * x * y := by
        change b * _ * b⁻¹ = _
        group
      obtain ⟨a1, a2, a3⟩ := eP κ (lK h1)
      obtain ⟨b1, b2, b3⟩ := eQ x (lJ h2)
      obtain ⟨c1, c2, c3⟩ := eR y (lL h3)
      refine ⟨?_, ?_⟩
      · exact hΓ.conj_mem' _ (Γ.mul_mem (Γ.mul_mem (hP (lK h1)) (hQ (lJ h2))) (hR (lL h3))) b
      · change c _ ∈ U
        rw [e]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · change p _ ∈ K
          simpa [a1, b1, c1] using h1
        · change q _ ∈ J
          simpa [a2, b2, c2] using h2
        · change r _ ∈ L
          simpa [a3, b3, c3] using h3
  refine ⟨Γ ⊓ U.comap c, inf_le_left, ?_, ?_, key⟩
  · have : ((Γ ⊓ U.comap c : Subgroup G) : Set G) =
        (fun z : G × G × G => b⁻¹ * (z.1 * z.2.1 * z.2.2) * b) '' ((K : Set G) ×ˢ (J : Set G) ×ˢ (L : Set G)) := by
      ext k
      rw [SetLike.mem_coe, key]
      constructor
      · rintro ⟨κ, x, y, h1, h2, h3, rfl⟩
        exact ⟨(κ, x, y), ⟨h1, h2, h3⟩, rfl⟩
      · rintro ⟨⟨κ, x, y⟩, ⟨h1, h2, h3⟩, rfl⟩
        exact ⟨κ, x, y, h1, h2, h3, rfl⟩
    rw [this]
    exact (cK.prod (cJ.prod cL)).image (by fun_prop)
  · have : (((Γ ⊓ U.comap c).subgroupOf Γ : Subgroup Γ) : Set Γ) = (fun g : Γ => c g) ⁻¹' U := by
      ext g
      exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
    rw [this]
    exact oU.preimage (hc.comp continuous_subtype_val)

end Grp

section Cut
variable {S : Type} [CommRing S] {n : Type} [Fintype n] [DecidableEq n]

def cut (e : S) (M : Matrix n n S) : Matrix n n S := 1 + e • (M - 1)

/- English proof (translation)
Simplify using `only [cut, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, mul_comm f e]`. Normalize the expressions using the abelian group laws.
-/
theorem cut_mul_cut (e f : S) (M N : Matrix n n S) :
    cut e M * cut f N = 1 + e • (M - 1) + f • (N - 1) + (e * f) • ((M - 1) * (N - 1)) := by
  simp only [cut, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, mul_comm f e]
  abel

/- English proof (translation)
Rewrite using `[cut_mul_cut, he, cut, add_assoc, add_assoc, ← smul_add, ← smul_add]`. Use `congr 2`. Use `noncomm_ring`.
-/
theorem cut_mul {e : S} (he : e * e = e) (M N : Matrix n n S) : cut e (M * N) = cut e M * cut e N := by
  rw [cut_mul_cut, he, cut, add_assoc, add_assoc, ← smul_add, ← smul_add]
  congr 2
  noncomm_ring

/- English proof (translation)
Simplify using `[cut, smul_smul]`.
-/
theorem cut_cut (e f : S) (M : Matrix n n S) : cut e (cut f M) = cut (e * f) M := by
  simp [cut, smul_smul]

/- English proof (translation)
Rewrite using `[cut_mul_cut, h, zero_smul, add_zero, cut, add_smul, add_assoc]`.
-/
theorem cut_add {e f : S} (h : e * f = 0) (M : Matrix n n S) : cut e M * cut f M = cut (e + f) M := by
  rw [cut_mul_cut, h, zero_smul, add_zero, cut, add_smul, add_assoc]

/- English proof (translation)
Simplify using `[cut]`.
-/
theorem cut_zero (M : Matrix n n S) : cut 0 M = 1 := by simp [cut]

/- English proof (translation)
Rewrite using `[cut, add_comm, ← eq_sub_iff_add_eq, ← Matrix.ext_iff]`. Both sides reduce to the same expression.
-/
theorem cut_eq_iff (e : S) (M : Matrix n n S) : cut e M = M ↔ ∀ i j, e * (M - 1) i j = (M - 1) i j := by
  rw [cut, add_comm, ← eq_sub_iff_add_eq, ← Matrix.ext_iff]
  rfl

def cutHom {e : S} (he : e * e = e) : Matrix n n S →* Matrix n n S where
  toFun := cut e
  map_one' := by simp [cut]
  map_mul' := cut_mul he

variable [TopologicalSpace S] [IsTopologicalRing S] {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
Use `choose π hπ using hst`. Establish `hc : Continuous (cutHom (n` using `n) he) := by`. Express the relevant statement in the definitionally equal form `Continuous fun M : Matrix n n S => 1 + e • (M - 1)`. Use `fun_prop`. Use `⟨MonoidHom.mk' π fun a b => hφ.injective (by simp only [hπ, map_mul]), ?_, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[hφ.continuous_iff]`. Establish `: φ ∘ π = Units.map (cutHom he) ∘ φ` using `funext hπ`. Express the relevant statement in the definitionally equal form `Continuous (φ ∘ π)`. Rewrite using `[this]`. Conclude with `(hc.units_map _).comp hφ.continuous`.

Express the relevant statement in the definitionally equal form `(φ (π g)).val = _`. Rewrite using `[hπ]`. Both sides reduce to the same expression.
-/
theorem exists_proj {φ : G →* GL n S} (hφ : IsEmbedding φ) {e : S} (he : e * e = e)
    (hst : ∀ g, ∃ g', φ g' = Units.map (cutHom he) (φ g)) :
    ∃ π : G →* G, Continuous π ∧ ∀ g, (φ (π g)).val = cut e (φ g).val := by
  choose π hπ using hst
  have hc : Continuous (cutHom (n := n) he) := by
    change Continuous fun M : Matrix n n S => 1 + e • (M - 1)
    fun_prop
  refine ⟨MonoidHom.mk' π fun a b => hφ.injective (by simp only [hπ, map_mul]), ?_, fun g => ?_⟩
  · rw [hφ.continuous_iff]
    have : φ ∘ π = Units.map (cutHom he) ∘ φ := funext hπ
    change Continuous (φ ∘ π)
    rw [this]
    exact (hc.units_map _).comp hφ.continuous
  · change (φ (π g)).val = _
    rw [hπ]; rfl

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨Λ, hΛ, fun M hM => hM x hx⟩`. Consider the case `zero => exact ⟨{0}, isCompact_singleton, fun M _ => by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨C, hC, h⟩` from `hx`.

Take `⟨C', hC', h'⟩` from `hy`. Conclude with `⟨C + C', hC.add hC', fun M hM => by rw [mulVec_add]; exact Set.add_mem_add (h M hM) (h' M hM)⟩`. Consider the case `smul a x _ hx`. Take `⟨C, hC, h⟩` from `hx`. Conclude with `⟨a • C, hC.smul a, fun M hM => by rw [mulVec_smul]; exact Set.smul_mem_smul_set (h M hM)⟩`.
-/
theorem exists_compact_of_span {Λ : Set (n → S)} (hΛ : IsCompact Λ) {y : n → S} (hy : y ∈ Submodule.span S Λ) :
    ∃ C : Set (n → S), IsCompact C ∧ ∀ M : Matrix n n S, (∀ z ∈ Λ, M *ᵥ z ∈ Λ) → M *ᵥ y ∈ C := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨Λ, hΛ, fun M hM => hM x hx⟩
  | zero => exact ⟨{0}, isCompact_singleton, fun M _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC, h⟩ := hx
    obtain ⟨C', hC', h'⟩ := hy
    exact ⟨C + C', hC.add hC', fun M hM => by rw [mulVec_add]; exact Set.add_mem_add (h M hM) (h' M hM)⟩
  | smul a x _ hx =>
    obtain ⟨C, hC, h⟩ := hx
    exact ⟨a • C, hC.smul a, fun M hM => by rw [mulVec_smul]; exact Set.smul_mem_smul_set (h M hM)⟩

/- English proof (translation)
Use `choose C hC h using fun j => exists_compact_of_span hΛ (hy j)`. Use `⟨(fun X : n → n → S => (1 - e) • (1 : Matrix n n S) + (Matrix.of X)ᵀ) '' Set.pi Set.univ C, (isCompact_univ_pi hC).image ?_, fun M hM hz => ⟨_, fun j _ => h j M hz, ?_⟩⟩` and prove the remaining obligations. Conclude with `continuous_const.add (Continuous.matrix_transpose continuous_id)`. Use `conv_rhs => rw [← hM]`. Use extensionality with `i j`.

Simplify using `[cut, mulVec_smul, mul_sub, sub_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_compact_mat {Λ : Set (n → S)} (hΛ : IsCompact Λ) {e : S}
    (hy : ∀ j, e • Pi.single j (1 : S) ∈ Submodule.span S Λ) :
    ∃ C : Set (Matrix n n S), IsCompact C ∧ ∀ M : Matrix n n S, cut e M = M → (∀ z ∈ Λ, M *ᵥ z ∈ Λ) → M ∈ C := by
  choose C hC h using fun j => exists_compact_of_span hΛ (hy j)
  refine ⟨(fun X : n → n → S => (1 - e) • (1 : Matrix n n S) + (Matrix.of X)ᵀ) '' Set.pi Set.univ C,
    (isCompact_univ_pi hC).image ?_, fun M hM hz => ⟨_, fun j _ => h j M hz, ?_⟩⟩
  · exact continuous_const.add (Continuous.matrix_transpose continuous_id)
  · conv_rhs => rw [← hM]
    ext i j
    simp [cut, mulVec_smul, mul_sub, sub_mul]
    ring

/- English proof (translation)
Establish `tg : IsTopologicalGroup G` using `hφ.isInducing.topologicalGroup φ`. Establish `cm : Continuous fun g => (φ g).val` using `Units.continuous_val.comp hφ.continuous`. Set `T : Subgroup G` to `{ carrier := {g | (∀ z ∈ Λ, (φ g).val *ᵥ z ∈ Λ) ∧ ∀ z ∈ Λ, (φ g⁻¹).val *ᵥ z ∈ Λ} one_mem' := by simp mul_mem' := fun {a b} ha hb => ⟨fun z hz => by`. Rewrite using `[map_mul, Units.val_mul, ← mulVec_mulVec]`. Conclude with `ha.1 _ (hb.1 z hz),`.

Use `fun z hz => by`. Rewrite using `[_root_.mul_inv_rev, map_mul, Units.val_mul, ← mulVec_mulVec]`. Conclude with `hb.2 _ (ha.2 z hz)⟩`. Use the proof step `inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }`. Establish `oW : IsOpen {g : G | ∀ z ∈ Λ, (φ g).val *ᵥ z ∈ Λ}`.

Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `g hg`. Establish `h1 : ∀ᶠ x in nhds g, ∀ z ∈ Λ, e • ((φ x).val *ᵥ z) ∈ Λ`. Use `hΛ.eventually_forall_of_forall_eventually fun z hz => ?_` and prove the remaining obligations. Establish `hc : Continuous fun w : G × (n → S) => (φ w.1).val *ᵥ w.2` using `(cm.comp continuous_fst).matrix_mulVec continuous_snd`.

Use `hc.continuousAt.preimage_mem_nhds (ho.mem_nhds ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e • _ ∈ Λ`. Rewrite using `[he _ (hg z hz)]`. Conclude with `hg z hz`. Use `filter_upwards [h1] with x hx z hz`.

Use `hx z hz` as an intermediate fact. Rewrite `this` using `[← mulVec_smul, he z hz]`. Then use the resulting hypothesis. Establish `oT : IsOpen (T : Set G)` using `oW.inter (oW.preimage continuous_inv)`. Establish `cP : IsClosed (P : Set G)`. Establish `: (P : Set G) = {g | cut e (φ g).val = (φ g).val}` using `Set.ext hP`.

Rewrite using `[this]`. Use `isClosed_eq ?_ cm` and prove the remaining obligations. Unfold `cut`. Use `fun_prop`. Use `⟨P ⊓ T, inf_le_left, ?_, ?_, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨C, hC, h⟩` from `exists_compact_mat hΛ hy`. Establish `hE` using `Units.isClosedEmbedding_embedProduct.comp hφ`. Establish `h2` using `hE.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))`. Use `h2.of_isClosed_subset (cP.inter (T.isClosed_of_isOpen oT)) fun g hg => ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `h _ ((hP g).1 hg.1) hg.2.1`.

Use `⟨_, h _ ((hP _).1 (P.inv_mem hg.1)) hg.2.2, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `: (((P ⊓ T).subgroupOf P : Subgroup P) : Set P) = Subtype.val ⁻¹' T`. Use extensionality with `g`. Conclude with `⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩`.

Rewrite using `[this]`. Conclude with `oT.preimage continuous_subtype_val`. Use `and_congr_right fun _ => ⟨fun h y _ => ⟨h.1 y, fun hy => ?_⟩, fun h => ⟨fun z hz => (h z (he z hz)).1 hz, fun z hz => (h _ ?_).2 ?_⟩⟩` and prove the remaining obligations. Use `h.2 _ hy` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]`. Then use the resulting hypothesis.

Rewrite using `[← mulVec_smul, he z hz]`. Rewrite using `[mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]` and apply the resulting hypothesis.
-/
theorem stab_compact_open [T2Space S] {φ : G →* GL n S} (hφ : IsClosedEmbedding φ) {e : S}
    {Λ : Set (n → S)} (hΛ : IsCompact Λ) (ho : IsOpen {y : n → S | e • y ∈ Λ}) (he : ∀ y ∈ Λ, e • y = y)
    (hy : ∀ j, e • Pi.single j (1 : S) ∈ Submodule.span S Λ) {P : Subgroup G}
    (hP : ∀ g, g ∈ P ↔ cut e (φ g).val = (φ g).val) :
    ∃ K ≤ P, IsCompact (K : Set G) ∧ IsOpen (K.subgroupOf P : Set P) ∧
      ∀ g, g ∈ K ↔ g ∈ P ∧ ∀ y : n → S, e • y = y → (y ∈ Λ ↔ (φ g).val *ᵥ y ∈ Λ) := by
  have tg : IsTopologicalGroup G := hφ.isInducing.topologicalGroup φ
  have cm : Continuous fun g => (φ g).val := Units.continuous_val.comp hφ.continuous
  let T : Subgroup G :=
    { carrier := {g | (∀ z ∈ Λ, (φ g).val *ᵥ z ∈ Λ) ∧ ∀ z ∈ Λ, (φ g⁻¹).val *ᵥ z ∈ Λ}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => ⟨fun z hz => by
          rw [map_mul, Units.val_mul, ← mulVec_mulVec]; exact ha.1 _ (hb.1 z hz),
        fun z hz => by
          rw [_root_.mul_inv_rev, map_mul, Units.val_mul, ← mulVec_mulVec]; exact hb.2 _ (ha.2 z hz)⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  have oW : IsOpen {g : G | ∀ z ∈ Λ, (φ g).val *ᵥ z ∈ Λ} := by
    rw [isOpen_iff_mem_nhds]
    intro g hg
    have h1 : ∀ᶠ x in nhds g, ∀ z ∈ Λ, e • ((φ x).val *ᵥ z) ∈ Λ := by
      refine hΛ.eventually_forall_of_forall_eventually fun z hz => ?_
      have hc : Continuous fun w : G × (n → S) => (φ w.1).val *ᵥ w.2 :=
        (cm.comp continuous_fst).matrix_mulVec continuous_snd
      refine hc.continuousAt.preimage_mem_nhds (ho.mem_nhds ?_)
      change e • _ ∈ Λ
      rw [he _ (hg z hz)]
      exact hg z hz
    filter_upwards [h1] with x hx z hz
    have := hx z hz
    rwa [← mulVec_smul, he z hz] at this
  have oT : IsOpen (T : Set G) := oW.inter (oW.preimage continuous_inv)
  have cP : IsClosed (P : Set G) := by
    have : (P : Set G) = {g | cut e (φ g).val = (φ g).val} := Set.ext hP
    rw [this]
    refine isClosed_eq ?_ cm
    unfold cut
    fun_prop
  refine ⟨P ⊓ T, inf_le_left, ?_, ?_, fun g => ?_⟩
  · obtain ⟨C, hC, h⟩ := exists_compact_mat hΛ hy
    have hE := Units.isClosedEmbedding_embedProduct.comp hφ
    have h2 := hE.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
    refine h2.of_isClosed_subset (cP.inter (T.isClosed_of_isOpen oT)) fun g hg => ⟨?_, ?_⟩
    · exact h _ ((hP g).1 hg.1) hg.2.1
    · refine ⟨_, h _ ((hP _).1 (P.inv_mem hg.1)) hg.2.2, ?_⟩
      simp
  · have : (((P ⊓ T).subgroupOf P : Subgroup P) : Set P) = Subtype.val ⁻¹' T := by
      ext g
      exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
    rw [this]
    exact oT.preimage continuous_subtype_val
  · refine and_congr_right fun _ => ⟨fun h y _ => ⟨h.1 y, fun hy => ?_⟩, fun h => ⟨fun z hz => (h z (he z hz)).1 hz,
      fun z hz => (h _ ?_).2 ?_⟩⟩
    · have := h.2 _ hy
      rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this
    · rw [← mulVec_smul, he z hz]
    · rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec]

end Cut

section Main
variable {S : Type} [CommRing S] {n : Type} [Fintype n] [DecidableEq n]
variable [TopologicalSpace S] [IsTopologicalRing S] {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
Establish `tg : IsTopologicalGroup G` using `hφ.isInducing.topologicalGroup φ`. Take `⟨K, lK, cK, oK, iK⟩` from `stab_compact_open hφ hΛ ho hs hy iP`. Take `⟨p, hp, ep⟩` from `exists_proj hφ.isEmbedding he se`. Take `⟨q, hq, eq⟩` from `exists_proj hφ.isEmbedding hf sf`. Take `⟨r, hr, er⟩` from `exists_proj hφ.isEmbedding hg sg`.

Establish `inj : ∀ x y, (φ x).val = (φ y).val → x = y` using `fun x y h => hφ.injective (Units.ext h)`. Establish `hfe : f * e = 0` using `by rw [mul_comm, hef]`. Establish `hge : g * e = 0` using `by rw [mul_comm, heg]`. Establish `hgf : g * f = 0` using `by rw [mul_comm, hfg]`. Establish `sub : ∀ (a c : S) (M : Matrix n n S), a * c = c → cut c M = M → cut a M = M` using `fun a c M h hM => by`.

Rewrite using `[← hM, cut_cut, h]`. Establish `kill : ∀ (a c : S) (x y : G), a * c = 0 → cut c (φ x).val = (φ x).val → (φ y).val = cut a (φ x).val → y = 1` using `fun a c x y h hx hy => inj _ _ (by rw [hy, ← hx, cut_cut, h, cut_zero, map_one, Units.val_one])`. Simplify using `only [← iK]`. Use `glue hp hq hr hΓ (fun x hx => (iΓ x).2 (sub _ _ _ ?_ ((iP x).1 hx))) (fun x hx => (iΓ x).2 (sub _ _ _ ?_ ((iQ x).1 hx))) (fun x hx => (iΓ x).2 (sub _ _ _ ?_ ((iR x).1 hx))) (fun x => (iP _).2 (by rw [ep, cut_cut, he])) (fun x => (iQ _).2 (by rw [eq, cut_cut, hf])) (fun x => (iR _ …` and prove the remaining obligations. Rewrite using `[add_mul, add_mul, he, hfe, hge, add_zero, add_zero]`.

Rewrite using `[add_mul, add_mul, hef, hf, hgf, add_zero, zero_add]`. Rewrite using `[add_mul, add_mul, heg, hfg, hg, add_zero, zero_add]`. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, ep, eq, er, cut_add hef, cut_add (by rw [add_mul, heg, hfg, add_zero]), (iΓ x).1 hx]`.
-/
theorem level [T2Space S] {φ : G →* GL n S} (hφ : IsClosedEmbedding φ) {e f g : S}
    (he : e * e = e) (hf : f * f = f) (hg : g * g = g) (hef : e * f = 0) (heg : e * g = 0) (hfg : f * g = 0)
    (se : ∀ x, ∃ x', φ x' = Units.map (cutHom he) (φ x)) (sf : ∀ x, ∃ x', φ x' = Units.map (cutHom hf) (φ x))
    (sg : ∀ x, ∃ x', φ x' = Units.map (cutHom hg) (φ x))
    {Λ : Set (n → S)} (hΛ : IsCompact Λ) (ho : IsOpen {y : n → S | e • y ∈ Λ}) (hs : ∀ y ∈ Λ, e • y = y)
    (hy : ∀ j, e • Pi.single j (1 : S) ∈ Submodule.span S Λ) {Γ P Q R J L : Subgroup G} (hΓ : Γ.Normal)
    (iΓ : ∀ x, x ∈ Γ ↔ cut (e + f + g) (φ x).val = (φ x).val)
    (iP : ∀ x, x ∈ P ↔ cut e (φ x).val = (φ x).val) (iQ : ∀ x, x ∈ Q ↔ cut f (φ x).val = (φ x).val)
    (iR : ∀ x, x ∈ R ↔ cut g (φ x).val = (φ x).val)
    (lJ : J ≤ Q) (cJ : IsCompact (J : Set G)) (oJ : IsOpen (J.subgroupOf Q : Set Q))
    (lL : L ≤ R) (cL : IsCompact (L : Set G)) (oL : IsOpen (L.subgroupOf R : Set R)) (b : G) :
    ∃ M ≤ Γ, IsCompact (M : Set G) ∧ IsOpen (M.subgroupOf Γ : Set Γ) ∧
      ∀ k, k ∈ M ↔ ∃ κ x y, (κ ∈ P ∧ ∀ y : n → S, e • y = y → (y ∈ Λ ↔ (φ κ).val *ᵥ y ∈ Λ)) ∧
        x ∈ J ∧ y ∈ L ∧ k = b⁻¹ * (κ * x * y) * b := by
  have tg : IsTopologicalGroup G := hφ.isInducing.topologicalGroup φ
  obtain ⟨K, lK, cK, oK, iK⟩ := stab_compact_open hφ hΛ ho hs hy iP
  obtain ⟨p, hp, ep⟩ := exists_proj hφ.isEmbedding he se
  obtain ⟨q, hq, eq⟩ := exists_proj hφ.isEmbedding hf sf
  obtain ⟨r, hr, er⟩ := exists_proj hφ.isEmbedding hg sg
  have inj : ∀ x y, (φ x).val = (φ y).val → x = y := fun x y h => hφ.injective (Units.ext h)
  have hfe : f * e = 0 := by rw [mul_comm, hef]
  have hge : g * e = 0 := by rw [mul_comm, heg]
  have hgf : g * f = 0 := by rw [mul_comm, hfg]
  have sub : ∀ (a c : S) (M : Matrix n n S), a * c = c → cut c M = M → cut a M = M := fun a c M h hM => by
    rw [← hM, cut_cut, h]
  have kill : ∀ (a c : S) (x y : G), a * c = 0 → cut c (φ x).val = (φ x).val → (φ y).val = cut a (φ x).val → y = 1 :=
    fun a c x y h hx hy => inj _ _ (by rw [hy, ← hx, cut_cut, h, cut_zero, map_one, Units.val_one])
  simp only [← iK]
  refine glue hp hq hr hΓ (fun x hx => (iΓ x).2 (sub _ _ _ ?_ ((iP x).1 hx)))
    (fun x hx => (iΓ x).2 (sub _ _ _ ?_ ((iQ x).1 hx))) (fun x hx => (iΓ x).2 (sub _ _ _ ?_ ((iR x).1 hx)))
    (fun x => (iP _).2 (by rw [ep, cut_cut, he])) (fun x => (iQ _).2 (by rw [eq, cut_cut, hf]))
    (fun x => (iR _).2 (by rw [er, cut_cut, hg]))
    (fun x hx => ⟨inj _ _ ((ep x).trans ((iP x).1 hx)), kill _ _ x _ hfe ((iP x).1 hx) (eq x),
      kill _ _ x _ hge ((iP x).1 hx) (er x)⟩)
    (fun x hx => ⟨kill _ _ x _ hef ((iQ x).1 hx) (ep x), inj _ _ ((eq x).trans ((iQ x).1 hx)),
      kill _ _ x _ hgf ((iQ x).1 hx) (er x)⟩)
    (fun x hx => ⟨kill _ _ x _ heg ((iR x).1 hx) (ep x), kill _ _ x _ hfg ((iR x).1 hx) (eq x),
      inj _ _ ((er x).trans ((iR x).1 hx))⟩)
    (fun x hx => inj _ _ ?_) lK cK oK lJ cJ oJ lL cL oL b
  · rw [add_mul, add_mul, he, hfe, hge, add_zero, add_zero]
  · rw [add_mul, add_mul, hef, hf, hgf, add_zero, zero_add]
  · rw [add_mul, add_mul, heg, hfg, hg, add_zero, zero_add]
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ep, eq, er, cut_add hef,
      cut_add (by rw [add_mul, heg, hfg, add_zero]), (iΓ x).1 hx]

end Main

section Tens
variable {F E R : Type} [Field F] [Field E] [NumberField E] [Algebra F E] [CommRing R] [Algebra F R]

/- English proof (translation)
Establish `h1 : Module.Finite (𝓞 E) N` using `Module.Finite.iff_fg.2 hN.fg`. Establish `h2 : Module.Finite ℤ N` using `Module.Finite.trans (𝓞 E) N`. Establish `h3 : (N.restrictScalars ℤ).FG` using `Module.Finite.iff_fg.1 h2`. Take `⟨m, x, hx⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 h3`. Establish `hz : ∀ y ∈ N, y ∈ Submodule.span ℤ (Set.range x)` using `fun y hy => by rw [hx]; exact hy`.

Establish `hF : ∀ y ∈ N, y ∈ Submodule.span F (Set.range x)` using `fun y hy => Submodule.span_le_restrictScalars ℤ F _ (hz y hy)`. Use `⟨m, x, fun k => ?_, hz, ?_⟩` and prove the remaining obligations. Establish `: x k ∈ Submodule.span ℤ (Set.range x)` using `Submodule.subset_span ⟨k, rfl⟩`. Rewrite `this` using `[hx]`. Conclude with `this`.

Establish `key : ∀ y ∈ Submodule.span E (N : Set (Fin n → E)), ∀ a : E, a • y ∈ Submodule.span F (Set.range x)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Introduce `a`.

Establish `ha : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨d, hd, hi⟩` from `ha.exists_integral_multiple`. Establish `h4` using `hF _ (N.smul_mem (⟨d • a, hi⟩ : 𝓞 E) hy)`. Establish `hdE : (d : E) ≠ 0` using `Int.cast_ne_zero.2 hd`. Establish `: a • y = (d : F)⁻¹ • ((⟨d • a, hi⟩ : 𝓞 E) • y)`.

Use extensionality with `i`. Express the relevant statement in the definitionally equal form `a * y i = (d : F)⁻¹ • ((d • a) * y i)`. Rewrite using `[Algebra.smul_def, map_inv₀, map_intCast, zsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ h4`. Consider the case `zero => intro a`. Simplify using the standard rewrite rules. Consider the case `add y z _ _ hy hz => intro a`. Rewrite using `[smul_add]`.

Conclude with `Submodule.add_mem _ (hy a) (hz a)`. Consider the case `smul c y _ hy => intro a`. Rewrite using `[smul_smul]`. Conclude with `hy _`. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Simplify using `using key y (by rw [hN.span_eq_top]; trivial) 1`.
-/
theorem span_lattice {n : ℕ} {N : Submodule (𝓞 E) (Fin n → E)} (hN : Submodule.IsLattice E N) :
    ∃ (m : ℕ) (x : Fin m → Fin n → E), (∀ k, x k ∈ N) ∧ (∀ y ∈ N, y ∈ Submodule.span ℤ (Set.range x)) ∧
      Submodule.span F (Set.range x) = ⊤ := by
  have h1 : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN.fg
  have h2 : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  have h3 : (N.restrictScalars ℤ).FG := Module.Finite.iff_fg.1 h2
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 h3
  have hz : ∀ y ∈ N, y ∈ Submodule.span ℤ (Set.range x) := fun y hy => by rw [hx]; exact hy
  have hF : ∀ y ∈ N, y ∈ Submodule.span F (Set.range x) := fun y hy =>
    Submodule.span_le_restrictScalars ℤ F _ (hz y hy)
  refine ⟨m, x, fun k => ?_, hz, ?_⟩
  · have : x k ∈ Submodule.span ℤ (Set.range x) := Submodule.subset_span ⟨k, rfl⟩
    rw [hx] at this
    exact this
  · have key : ∀ y ∈ Submodule.span E (N : Set (Fin n → E)), ∀ a : E, a • y ∈ Submodule.span F (Set.range x) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        intro a
        have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
        obtain ⟨d, hd, hi⟩ := ha.exists_integral_multiple
        have h4 := hF _ (N.smul_mem (⟨d • a, hi⟩ : 𝓞 E) hy)
        have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.2 hd
        have : a • y = (d : F)⁻¹ • ((⟨d • a, hi⟩ : 𝓞 E) • y) := by
          ext i
          change a * y i = (d : F)⁻¹ • ((d • a) * y i)
          rw [Algebra.smul_def, map_inv₀, map_intCast, zsmul_eq_mul]
          field_simp
        rw [this]
        exact Submodule.smul_mem _ _ h4
      | zero => intro a; simp
      | add y z _ _ hy hz => intro a; rw [smul_add]; exact Submodule.add_mem _ (hy a) (hz a)
      | smul c y _ hy => intro a; rw [smul_smul]; exact hy _
    rw [eq_top_iff]
    intro y _
    simpa using key y (by rw [hN.span_eq_top]; trivial) 1

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff]`. Use `set W := Submodule.span R (Set.range fun k i => ((1 : R) ⊗ₜ[F] x k i : R ⊗[F] E))`. Establish `h1 : ∀ y ∈ Submodule.span F (Set.range x), (fun i => ((1 : R) ⊗ₜ[F] y i : R ⊗[F] E)) ∈ W`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy => obtain ⟨k, rfl⟩ := hy`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Consider the case `zero => simp only [Pi.zero_apply, TensorProduct.tmul_zero]`. Conclude with `W.zero_mem`. Consider the case `add y z _ _ hy hz => simp only [Pi.add_apply, TensorProduct.tmul_add]`.

Conclude with `W.add_mem hy hz`. Consider the case `smul c y _ hy => simp only [Pi.smul_apply, TensorProduct.tmul_smul]`. Conclude with `W.smul_of_tower_mem c hy`. Introduce `z _`. Rewrite using `[← Finset.univ_sum_single z]`.

Use `W.sum_mem fun i _ => ?_` and prove the remaining obligations. Proceed by induction on `z i using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r a`. Use `W.smul_mem r (h1 (Pi.single i a) (by rw [hx]; trivial))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[TensorProduct.smul_tmul']`.

Simplify using `[h]`. Consider the case `add a b ha hb => rw [Pi.single_add]`. Conclude with `W.add_mem ha hb`.
-/
theorem comb_surjective {n m : ℕ} {x : Fin m → Fin n → E} (hx : Submodule.span F (Set.range x) = ⊤) :
    Function.Surjective (Fintype.linearCombination R fun k i => ((1 : R) ⊗ₜ[F] x k i : R ⊗[F] E)) := by
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff]
  set W := Submodule.span R (Set.range fun k i => ((1 : R) ⊗ₜ[F] x k i : R ⊗[F] E))
  have h1 : ∀ y ∈ Submodule.span F (Set.range x), (fun i => ((1 : R) ⊗ₜ[F] y i : R ⊗[F] E)) ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp only [Pi.zero_apply, TensorProduct.tmul_zero]; exact W.zero_mem
    | add y z _ _ hy hz => simp only [Pi.add_apply, TensorProduct.tmul_add]; exact W.add_mem hy hz
    | smul c y _ hy => simp only [Pi.smul_apply, TensorProduct.tmul_smul]; exact W.smul_of_tower_mem c hy
  intro z _
  rw [← Finset.univ_sum_single z]
  refine W.sum_mem fun i _ => ?_
  induction z i using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    have := W.smul_mem r (h1 (Pi.single i a) (by rw [hx]; trivial))
    convert this using 1
    ext j
    by_cases h : j = i
    · subst h; simp [TensorProduct.smul_tmul']
    · simp [h]
  | add a b ha hb => rw [Pi.single_add]; exact W.add_mem ha hb

variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace (R ⊗[F] E)] [IsModuleTopology R (R ⊗[F] E)]

omit [NumberField E] in
/- English proof (translation)
Set `b` to `Algebra.TensorProduct.basis R (Module.Basis.ofVectorSpace F E)`. Use `T2Space.of_injective_continuous (f := fun a i => b.repr a i) (fun a c h => b.repr.injective (Finsupp.ext (congrFun h))) (continuous_pi fun i => ?_)` and prove the remaining obligations. Conclude with `IsModuleTopology.continuous_of_linearMap (b.coord i)`.
-/
theorem t2_tensor_product [T2Space R] : T2Space (R ⊗[F] E) := by
  let b := Algebra.TensorProduct.basis R (Module.Basis.ofVectorSpace F E)
  refine T2Space.of_injective_continuous (f := fun a i => b.repr a i)
    (fun a c h => b.repr.injective (Finsupp.ext (congrFun h))) (continuous_pi fun i => ?_)
  exact IsModuleTopology.continuous_of_linearMap (b.coord i)

/- English proof (translation)
Use `IsModuleTopology.toContinuousAdd R (R ⊗[F] E)` as an intermediate fact. Use `IsModuleTopology.topologicalAddGroup R (R ⊗[F] E)` as an intermediate fact. Take `⟨m, x, hxN, hz, hF⟩` from `span_lattice (F := F) hN`. Use `set ψ := Fintype.linearCombination R fun k i => ((1 : R) ⊗ₜ[F] x k i : R ⊗[F] E) with hψ`. Establish `hq` using `IsModuleTopology.isOpenQuotientMap_of_surjective (comb_surjective (R := R) hF)`.

Rewrite `hq` using `[← hψ]`. Establish `hsm : ∀ y : Fin n → R ⊗[F] E, (e ⊗ₜ[F] (1 : E) : R ⊗[F] E) • y = e • y` using `fun y => by`. Use extensionality with `i`. Simplify using `[Algebra.smul_def]`. Establish `gen : ∀ a ∈ O, ∀ y ∈ N, (fun i => a ⊗ₜ[F] y i) ∈ Λ` using `fun a ha y hy => by`.

Rewrite using `[hΛ]`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩`. Establish `hin : ∀ r : Fin m → R, (∀ k, r k ∈ O) → ψ r ∈ Λ` using `fun r hr => by`. Rewrite using `[hψ, Fintype.linearCombination_apply]`. Use `Λ.sum_mem fun k _ => ?_` and prove the remaining obligations.

Use `gen _ (hr k) _ (hxN k) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using `[TensorProduct.smul_tmul']`. Establish `hout : Λ ≤ (AddSubgroup.pi Set.univ fun _ => O).map ψ.toAddMonoidHom`. Rewrite using `[hΛ, AddSubgroup.closure_le]`.

Introduce and unpack `_ ⟨a, ha, y, hy, rfl⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 (hz y hy)`. Use `⟨fun k => c k • a, fun k _ => O.zsmul_mem ha _, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `only [LinearMap.toAddMonoidHom_coe, hψ, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Conclude with `Finset.sum_congr rfl fun k _ => TensorProduct.smul_tmul _ _ _`. Use `⟨?_, ?_, fun y hy => ?_, fun j => ?_⟩` and prove the remaining obligations. Establish `: (Λ : Set (Fin n → R ⊗[F] E)) = ψ '' Set.pi Set.univ fun _ => (O : Set R)` using `Set.Subset.antisymm hout (by rintro _ ⟨r, hr, rfl⟩; exact hin r fun k => hr k trivial)`. Rewrite using `[this]`. Conclude with `(isCompact_univ_pi fun _ => hO).image hq.continuous`.

Simplify using `only [hsm]`. Use `AddSubgroup.isOpen_of_mem_nhds (Λ.comap (DistribSMul.toAddMonoidHom _ e)) (g := 0) ?_` and prove the remaining obligations. Establish `h1` using `hq.isOpenMap.image_mem_nhds (x := 0) (set_pi_mem_nhds Set.finite_univ fun (k : Fin m) _ => hU)`. Rewrite `h1` using `[map_zero]`. Use `Filter.mem_of_superset h1 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨r, hr, rfl⟩`. Express the relevant statement in the definitionally equal form `e • ψ r ∈ Λ`. Rewrite using `[← map_smul]`. Conclude with `hin _ fun k => hUe _ (hr k trivial)`. Take `⟨r, hr, rfl⟩` from `hout hy`.

Express the relevant statement in the definitionally equal form `_ • ψ r = ψ r`. Rewrite using `[hsm, ← map_smul]`. Use `congr 1`. Use extensionality with `k`. Conclude with `he _ (hr k trivial)`.

Take `⟨r, hr⟩` from `hq.surjective (Pi.single j 1)`. Rewrite using `[← hr, hψ, Fintype.linearCombination_apply, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`. Use `Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations.

Establish `: ((e ⊗ₜ[F] (1 : E) : R ⊗[F] E) • fun i => ((1 : R) ⊗ₜ[F] x k i : R ⊗[F] E)) = fun i => e ⊗ₜ[F] x k i`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `gen _ heO _ (hxN k)`.
-/
theorem lattice {n : ℕ} {N : Submodule (𝓞 E) (Fin n → E)} (hN : Submodule.IsLattice E N) (O : AddSubgroup R)
    (hO : IsCompact (O : Set R)) {e : R} (heO : e ∈ O) (he : ∀ a ∈ O, e * a = a) {U : Set R} (hU : U ∈ nhds 0)
    (hUe : ∀ a ∈ U, e * a ∈ O) (Λ : AddSubgroup (Fin n → R ⊗[F] E))
    (hΛ : Λ = AddSubgroup.closure {y | ∃ a ∈ O, ∃ x ∈ N, y = fun i => a ⊗ₜ[F] x i}) :
    IsCompact (Λ : Set (Fin n → R ⊗[F] E)) ∧ IsOpen {y : Fin n → R ⊗[F] E | (e ⊗ₜ[F] (1 : E) : R ⊗[F] E) • y ∈ Λ} ∧
      (∀ y ∈ Λ, (e ⊗ₜ[F] (1 : E) : R ⊗[F] E) • y = y) ∧
      ∀ j, (e ⊗ₜ[F] (1 : E) : R ⊗[F] E) • Pi.single j (1 : R ⊗[F] E) ∈
        Submodule.span (R ⊗[F] E) (Λ : Set (Fin n → R ⊗[F] E)) := by
  have := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have := IsModuleTopology.topologicalAddGroup R (R ⊗[F] E)
  obtain ⟨m, x, hxN, hz, hF⟩ := span_lattice (F := F) hN
  set ψ := Fintype.linearCombination R fun k i => ((1 : R) ⊗ₜ[F] x k i : R ⊗[F] E) with hψ
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective (comb_surjective (R := R) hF)
  rw [← hψ] at hq
  have hsm : ∀ y : Fin n → R ⊗[F] E, (e ⊗ₜ[F] (1 : E) : R ⊗[F] E) • y = e • y := fun y => by
    ext i
    simp [Algebra.smul_def]
  have gen : ∀ a ∈ O, ∀ y ∈ N, (fun i => a ⊗ₜ[F] y i) ∈ Λ := fun a ha y hy => by
    rw [hΛ]; exact AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩
  have hin : ∀ r : Fin m → R, (∀ k, r k ∈ O) → ψ r ∈ Λ := fun r hr => by
    rw [hψ, Fintype.linearCombination_apply]
    refine Λ.sum_mem fun k _ => ?_
    convert gen _ (hr k) _ (hxN k) using 1
    ext i
    simp [TensorProduct.smul_tmul']
  have hout : Λ ≤ (AddSubgroup.pi Set.univ fun _ => O).map ψ.toAddMonoidHom := by
    rw [hΛ, AddSubgroup.closure_le]
    rintro _ ⟨a, ha, y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hz y hy)
    refine ⟨fun k => c k • a, fun k _ => O.zsmul_mem ha _, ?_⟩
    ext i
    simp only [LinearMap.toAddMonoidHom_coe, hψ, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
      TensorProduct.tmul_sum, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact Finset.sum_congr rfl fun k _ => TensorProduct.smul_tmul _ _ _
  refine ⟨?_, ?_, fun y hy => ?_, fun j => ?_⟩
  · have : (Λ : Set (Fin n → R ⊗[F] E)) = ψ '' Set.pi Set.univ fun _ => (O : Set R) :=
      Set.Subset.antisymm hout (by rintro _ ⟨r, hr, rfl⟩; exact hin r fun k => hr k trivial)
    rw [this]
    exact (isCompact_univ_pi fun _ => hO).image hq.continuous
  · simp only [hsm]
    refine AddSubgroup.isOpen_of_mem_nhds (Λ.comap (DistribSMul.toAddMonoidHom _ e)) (g := 0) ?_
    have h1 := hq.isOpenMap.image_mem_nhds (x := 0) (set_pi_mem_nhds Set.finite_univ fun (k : Fin m) _ => hU)
    rw [map_zero] at h1
    refine Filter.mem_of_superset h1 ?_
    rintro _ ⟨r, hr, rfl⟩
    change e • ψ r ∈ Λ
    rw [← map_smul]
    exact hin _ fun k => hUe _ (hr k trivial)
  · obtain ⟨r, hr, rfl⟩ := hout hy
    change _ • ψ r = ψ r
    rw [hsm, ← map_smul]
    congr 1
    ext k
    exact he _ (hr k trivial)
  · obtain ⟨r, hr⟩ := hq.surjective (Pi.single j 1)
    rw [← hr, hψ, Fintype.linearCombination_apply, Finset.smul_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [smul_comm]
    refine Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ?_)
    have : ((e ⊗ₜ[F] (1 : E) : R ⊗[F] E) • fun i => ((1 : R) ⊗ₜ[F] x k i : R ⊗[F] E)) = fun i => e ⊗ₜ[F] x k i := by
      ext i
      simp
    rw [this]
    exact gen _ heO _ (hxN k)

end Tens

section Unitary
variable {S : Type} [CommRing S] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `h : Formalism.UG.cT σ g.val * J * g.val = J` using `hg`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT σ (cut e g.val) * J * cut e g.val = J`. Establish `h1 : Formalism.UG.cT σ (cut e g.val) = cut e (Formalism.UG.cT σ g.val)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[Formalism.UG.cT, cut, hσ]`. Simplify using `[Formalism.UG.cT, cut, hσ, hij, Ne.symm hij]`. Rewrite using `[h1]`. Generalize the expression as in `Formalism.UG.cT σ g.val = N at h`.

Establish `h2 : cut e N * J * cut e g.val = J + e • (N * J * g.val - J)`. Establish `h3 : N * J * g.val - J = (N - 1) * J + (J * (g.val - 1) + (N - 1) * J * (g.val - 1))` using `by noncomm_ring`. Simplify using `only [h3, cut, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, he, add_assoc]`. Rewrite using `[h2, h, sub_self, smul_zero, add_zero]`.
-/
theorem cut_mem {σ : S →+* S} {J : Matrix n n S} {e : S} (he : e * e = e) (hσ : σ e = e) {g : GL n S}
    (hg : g ∈ Formalism.UG.UJ σ J) : Units.map (cutHom he) g ∈ Formalism.UG.UJ σ J := by
  have h : Formalism.UG.cT σ g.val * J * g.val = J := hg
  change Formalism.UG.cT σ (cut e g.val) * J * cut e g.val = J
  have h1 : Formalism.UG.cT σ (cut e g.val) = cut e (Formalism.UG.cT σ g.val) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Formalism.UG.cT, cut, hσ]
    · simp [Formalism.UG.cT, cut, hσ, hij, Ne.symm hij]
  rw [h1]
  generalize Formalism.UG.cT σ g.val = N at h
  have h2 : cut e N * J * cut e g.val = J + e • (N * J * g.val - J) := by
    have h3 : N * J * g.val - J = (N - 1) * J + (J * (g.val - 1) + (N - 1) * J * (g.val - 1)) := by noncomm_ring
    simp only [h3, cut, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, he,
      add_assoc]
  rw [h2, h, sub_self, smul_zero, add_zero]

/- English proof (translation)
Use `isClosed_eq (f := fun g : GL n S => (g.val.map σ)ᵀ * J * g.val) (g := fun _ => J) ?_ continuous_const` and prove the remaining obligations. Conclude with `(((Units.continuous_val.matrix_map hσ).matrix_transpose).mul continuous_const).mul Units.continuous_val`.
-/
theorem closed_unitary [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] {σ : S →+* S} (hσ : Continuous σ)
    (J : Matrix n n S) : IsClosed (Formalism.UG.UJ σ J : Set (GL n S)) := by
  refine isClosed_eq (f := fun g : GL n S => (g.val.map σ)ᵀ * J * g.val) (g := fun _ => J) ?_ continuous_const
  exact (((Units.continuous_val.matrix_map hσ).matrix_transpose).mul continuous_const).mul Units.continuous_val

/- English proof (translation)
Rewrite using `[Units.ext_iff, ← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero, Units.val_one, Matrix.one_apply, Matrix.one_apply, apply_ite f, map_one, map_zero]`. Both sides reduce to the same expression.
-/
theorem map_eq_one_iff_ker {T : Type} [CommRing T] (f : S →+* T) (g : GL n S) :
    Units.map (RingHom.mapMatrix f).toMonoidHom g = 1 ↔ ∀ i j, (g.val - 1) i j ∈ RingHom.ker f := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero, Units.val_one, Matrix.one_apply, Matrix.one_apply,
    apply_ite f, map_one, map_zero]
  rfl

end Unitary

section Adelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.FinPl

/- English proof (translation)
Establish `h : ∀ i, (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) a) i = f ((Algebra.TensorProduct.basis R b).repr a i)` using `fun i => by`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r x => simp [Algebra.TensorProduct.basis_repr_tmul]`. Consider the case `add x y hx hy => simp [hx, hy]`.

Simplify using `only [← h]`. Rewrite using `[← (Algebra.TensorProduct.basis R' b).repr.map_eq_zero_iff, Finsupp.ext_iff]`. Both sides reduce to the same expression.
-/
theorem map_eq_zero_iff_repr {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (b : Module.Basis ι F E) (f : R →ₐ[F] R') (a : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) a = 0 ↔
      ∀ i, f ((Algebra.TensorProduct.basis R b).repr a i) = 0 := by
  have h : ∀ i, (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) a) i =
      f ((Algebra.TensorProduct.basis R b).repr a i) := fun i => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp [hx, hy]
  simp only [← h]
  rw [← (Algebra.TensorProduct.basis R' b).repr.map_eq_zero_iff, Finsupp.ext_iff]
  rfl

variable {F : Type} [Field F] [NumberField F]

open Classical in

def idemF (P : HeightOneSpectrum (𝓞 F) → Prop) : Af F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [if_pos h]; exact (v.adicCompletionIntegers F).one_mem
    · simp only [if_neg h]; exact (v.adicCompletionIntegers F).zero_mem⟩

/- English proof (translation)
The claim follows from `if_pos h`.
-/
theorem idemF_pos {P : HeightOneSpectrum (𝓞 F) → Prop} {v} (h : P v) : evalV F v (idemF P) = 1 := if_pos h
/- English proof (translation)
The claim follows from `if_neg h`.
-/
theorem idemF_neg {P : HeightOneSpectrum (𝓞 F) → Prop} {v} (h : ¬ P v) : evalV F v (idemF P) = 0 := if_neg h

def idem (P : HeightOneSpectrum (𝓞 F) → Prop) : AF F := pairA F 0 (idemF P)

/- English proof (translation)
The claim follows from `Prod.ext h1 (FiniteAdeleRing.ext F h2)`.
-/
theorem adele_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : ∀ v, evalV F v (sndA F a) = evalV F v (sndA F b)) :
    a = b := Prod.ext h1 (FiniteAdeleRing.ext F h2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_idem (P : HeightOneSpectrum (𝓞 F) → Prop) : fstA F (idem P) = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem snd_idem (P : HeightOneSpectrum (𝓞 F) → Prop) : sndA F (idem P) = idemF P := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨by rw [← h, map_mul, fst_idem, zero_mul], fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[← h, map_mul, map_mul, snd_idem, idemF_neg hv, zero_mul]`. Introduce and unpack `⟨h1, h2⟩`.

Use `adele_ext (by rw [map_mul, h1, mul_zero]) fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, snd_idem]`. Distinguish the cases in `hv : P v`. Rewrite using `[idemF_pos hv, one_mul]`. Rewrite using `[h2 v hv, mul_zero]`.
-/
theorem idem_mul_eq_iff (P : HeightOneSpectrum (𝓞 F) → Prop) (a : AF F) :
    idem P * a = a ↔ fstA F a = 0 ∧ ∀ v, ¬ P v → evalV F v (sndA F a) = 0 := by
  constructor
  · intro h
    refine ⟨by rw [← h, map_mul, fst_idem, zero_mul], fun v hv => ?_⟩
    rw [← h, map_mul, map_mul, snd_idem, idemF_neg hv, zero_mul]
  · rintro ⟨h1, h2⟩
    refine adele_ext (by rw [map_mul, h1, mul_zero]) fun v => ?_
    rw [map_mul, map_mul, snd_idem]
    by_cases hv : P v
    · rw [idemF_pos hv, one_mul]
    · rw [h2 v hv, mul_zero]

/- English proof (translation)
The claim follows from `(idem_mul_eq_iff P _).2 ⟨rfl, fun _ hv => idemF_neg hv⟩`.
-/
theorem idem_sq (P : HeightOneSpectrum (𝓞 F) → Prop) : idem P * idem P = idem P :=
  (idem_mul_eq_iff P _).2 ⟨rfl, fun _ hv => idemF_neg hv⟩

/- English proof (translation)
Use `adele_ext (by rw [map_mul, fst_idem, zero_mul, map_zero]) fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, snd_idem, snd_idem, map_zero, map_zero]`. Distinguish the cases in `hv : P v`. Rewrite using `[idemF_neg (h v hv), mul_zero]`. Rewrite using `[idemF_neg hv, zero_mul]`.
-/
theorem idem_orth {P Q : HeightOneSpectrum (𝓞 F) → Prop} (h : ∀ v, P v → ¬ Q v) : idem P * idem Q = 0 := by
  refine adele_ext (by rw [map_mul, fst_idem, zero_mul, map_zero]) fun v => ?_
  rw [map_mul, map_mul, snd_idem, snd_idem, map_zero, map_zero]
  by_cases hv : P v
  · rw [idemF_neg (h v hv), mul_zero]
  · rw [idemF_neg hv, zero_mul]

/- English proof (translation)
Use `adele_ext (by simp only [map_add, fst_idem, add_zero]) fun v => ?_` and prove the remaining obligations. Simplify using `only [map_add, snd_idem]`. Rewrite using `[idemF_pos (P := fun _ => True) trivial]`. Distinguish the cases in `hv : P v`. Rewrite using `[idemF_neg (h v hv), idemF_pos hv, idemF_neg (by simp [hv]), add_zero, zero_add]`.

Distinguish the cases in `hq : Q v`. Rewrite using `[idemF_neg hv, idemF_pos hq, idemF_neg (by simp [hq]), add_zero, zero_add]`. Rewrite using `[idemF_neg hv, idemF_neg hq, idemF_pos (P := fun v => ¬ P v ∧ ¬ Q v) ⟨hv, hq⟩, add_zero, add_zero]`.
-/
theorem idem_sum {P Q : HeightOneSpectrum (𝓞 F) → Prop} (h : ∀ v, P v → ¬ Q v) :
    idem (fun v => ¬ P v ∧ ¬ Q v) + idem P + idem Q = idem fun _ => True := by
  refine adele_ext (by simp only [map_add, fst_idem, add_zero]) fun v => ?_
  simp only [map_add, snd_idem]
  rw [idemF_pos (P := fun _ => True) trivial]
  by_cases hv : P v
  · rw [idemF_neg (h v hv), idemF_pos hv, idemF_neg (by simp [hv]), add_zero, zero_add]
  · by_cases hq : Q v
    · rw [idemF_neg hv, idemF_pos hq, idemF_neg (by simp [hq]), add_zero, zero_add]
    · rw [idemF_neg hv, idemF_neg hq, idemF_pos (P := fun v => ¬ P v ∧ ¬ Q v) ⟨hv, hq⟩, add_zero, add_zero]

def intOn (P : HeightOneSpectrum (𝓞 F) → Prop) : AddSubgroup (AF F) where
  carrier := {a | fstA F a = 0 ∧ sndA F a ∈ intAf F ∧ ∀ v, ¬ P v → evalV F v (sndA F a) = 0}
  zero_mem' := ⟨map_zero _, fun v => by rw [map_zero, map_zero]; exact zero_mem _, fun v _ => by rw [map_zero, map_zero]⟩
  add_mem' := fun {a b} ha hb => ⟨by rw [map_add, ha.1, hb.1, add_zero],
    fun v => by rw [map_add, map_add]; exact add_mem (ha.2.1 v) (hb.2.1 v),
    fun v hv => by rw [map_add, map_add, ha.2.2 v hv, hb.2.2 v hv, add_zero]⟩
  neg_mem' := fun {a} ha => ⟨by rw [map_neg, ha.1, neg_zero],
    fun v => by rw [map_neg, map_neg]; exact neg_mem (ha.2.1 v),
    fun v hv => by rw [map_neg, map_neg, ha.2.2 v hv, neg_zero]⟩

/- English proof (translation)
Establish `h1 : IsClosed {a : Af F | ∀ v, ¬ P v → evalV F v a = 0}`. Simplify using `only [Set.ofPred_forall]`. Conclude with `isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_eq (cont_eval F v) continuous_const`. Conclude with `(isCompact_singleton (x := (0 : Ainf F))).prod ((open_compact_hat F).2.inter_right h1)`.
-/
theorem compact_intOn (P : HeightOneSpectrum (𝓞 F) → Prop) : IsCompact (intOn P : Set (AF F)) := by
  have h1 : IsClosed {a : Af F | ∀ v, ¬ P v → evalV F v a = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_eq (cont_eval F v) continuous_const
  exact (isCompact_singleton (x := (0 : Ainf F))).prod ((open_compact_hat F).2.inter_right h1)

/- English proof (translation)
Introduce `v` and use `by by_cases h : P v · rw [idemF_pos h]; exact one_mem _ · rw [idemF_neg h]; exact zero_mem _`.
-/
theorem idemF_int (P : HeightOneSpectrum (𝓞 F) → Prop) : idemF P ∈ intAf F := fun v => by
  by_cases h : P v
  · rw [idemF_pos h]; exact one_mem _
  · rw [idemF_neg h]; exact zero_mem _

variable {D : D7}

def eps (D : D7) (P : Pl D → Prop) : AE D := idem P ⊗ₜ[D.host.F] (1 : D.host.E)

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace D.host.F D.host.E`. Establish `h1 : eps D P * a = idem P • a`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Establish `h2 : ∀ w, compAt D w a = Algebra.TensorProduct.map ((evalV D.host.F w).comp (sndA D.host.F)) (AlgHom.id D.host.F D.host.E) a` using `fun w => by`.

Conclude with `(DFunLike.congr_fun (Algebra.TensorProduct.map_comp (evalV D.host.F w) (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (AlgHom.id D.host.F D.host.E)) a).symm`. Rewrite using `[h1, ← (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective.eq_iff, map_smul, Finsupp.ext_iff]`. Simplify using `only [Finsupp.smul_apply, smul_eq_mul, idem_mul_eq_iff, idAt, Ideal.mem_inf, Ideal.mem_iInf, RingHom.mem_ker, h2, map_eq_zero_iff_repr b, forall_and]`. Conclude with `and_congr (map_eq_zero_iff_repr b (fstA D.host.F) a) ⟨fun h i v hv => h ⟨v, hv⟩ i, fun h v i => h i v.1 v.2⟩`.
-/
theorem mem_idAt (P : Pl D → Prop) (a : AE D) : a ∈ idAt D P ↔ eps D P * a = a := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  have h1 : eps D P * a = idem P • a := by
    rw [Algebra.smul_def]; rfl
  have h2 : ∀ w, compAt D w a = Algebra.TensorProduct.map ((evalV D.host.F w).comp (sndA D.host.F))
      (AlgHom.id D.host.F D.host.E) a := fun w => by
    exact (DFunLike.congr_fun (Algebra.TensorProduct.map_comp (evalV D.host.F w) (sndA D.host.F)
      (AlgHom.id D.host.F D.host.E) (AlgHom.id D.host.F D.host.E)) a).symm
  rw [h1, ← (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective.eq_iff, map_smul, Finsupp.ext_iff]
  simp only [Finsupp.smul_apply, smul_eq_mul, idem_mul_eq_iff, idAt, Ideal.mem_inf, Ideal.mem_iInf, RingHom.mem_ker, h2,
    map_eq_zero_iff_repr b, forall_and]
  exact and_congr (map_eq_zero_iff_repr b (fstA D.host.F) a) ⟨fun h i v hv => h ⟨v, hv⟩ i, fun h v i => h i v.1 v.2⟩

/- English proof (translation)
Rewrite using `[cut_eq_iff]`. Simplify using `only [← mem_idAt]`. Use `(map_eq_one_iff_ker (Ideal.Quotient.mk (idAt D P)) (matHom V g)).trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.mk_ker]`.
-/
theorem mem_grpAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) :
    g ∈ grpAt V P ↔ cut (eps D P) (matHom V g).val = (matHom V g).val := by
  rw [cut_eq_iff]
  simp only [← mem_idAt]
  refine (map_eq_one_iff_ker (Ideal.Quotient.mk (idAt D P)) (matHom V g)).trans ?_
  rw [Ideal.mk_ker]

/- English proof (translation)
Rewrite using `[cut_eq_iff]`. Simplify using `only [← mem_idAt]`. Use `(map_eq_one_iff_ker (infPart D) (matHom V g)).trans ?_` and prove the remaining obligations. Establish `: idAt D (fun _ => True) = RingHom.ker (infPart D)` using `inf_eq_left.2 (le_iInf fun w => (w.2 trivial).elim)`. Rewrite using `[this]`.
-/
theorem mem_fin (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ cut (eps D fun _ => True) (matHom V g).val = (matHom V g).val := by
  rw [cut_eq_iff]
  simp only [← mem_idAt]
  refine (map_eq_one_iff_ker (infPart D) (matHom V g)).trans ?_
  have : idAt D (fun _ => True) = RingHom.ker (infPart D) :=
    inf_eq_left.2 (le_iInf fun w => (w.2 trivial).elim)
  rw [this]

/- English proof (translation)
Unfold `GlobalTheory.FinPl.latV latMul`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨α, h1, h2, a, rfl, x, hx, rfl⟩`.

Conclude with `⟨pairA _ 0 α, ⟨rfl, h1, h2⟩, x, hx, by simp only [one_mul]⟩`. Introduce and unpack `⟨⟨a, α⟩, ⟨h0, h1, h2⟩, x, hx, rfl⟩`. Take `rfl : a = 0` from `h0`. Conclude with `⟨α, h1, h2, 1, rfl, x, hx, by simp only [one_mul]; rfl⟩`.
-/
theorem latV_eq (V : HSp D) (N : Lat V) (P : Pl D → Prop) :
    GlobalTheory.FinPl.latV V N P = AddSubgroup.closure {y | ∃ a ∈ intOn P, ∃ x ∈ N, y = fun i => a ⊗ₜ[D.host.F] x i} := by
  unfold GlobalTheory.FinPl.latV latMul
  congr 1
  ext y
  constructor
  · rintro ⟨α, h1, h2, a, rfl, x, hx, rfl⟩
    exact ⟨pairA _ 0 α, ⟨rfl, h1, h2⟩, x, hx, by simp only [one_mul]⟩
  · rintro ⟨⟨a, α⟩, ⟨h0, h1, h2⟩, x, hx, rfl⟩
    obtain rfl : a = 0 := h0
    exact ⟨α, h1, h2, 1, rfl, x, hx, by simp only [one_mul]; rfl⟩

/- English proof (translation)
Rewrite using `[eps, eps, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem eps_mul (P Q : Pl D → Prop) : eps D P * eps D Q = (idem P * idem Q) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [eps, eps, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Rewrite using `[eps_mul, idem_sq, eps]`.
-/
theorem eps_sq (P : Pl D → Prop) : eps D P * eps D P = eps D P := by rw [eps_mul, idem_sq, eps]

/- English proof (translation)
Rewrite using `[eps_mul, idem_orth h, TensorProduct.zero_tmul]`.
-/
theorem eps_orth {P Q : Pl D → Prop} (h : ∀ v, P v → ¬ Q v) : eps D P * eps D Q = 0 := by
  rw [eps_mul, idem_orth h, TensorProduct.zero_tmul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨_, cut_mem (eps_sq P) (by simp [sigR, eps]) x.2⟩, rfl⟩`.
-/
theorem eps_stable (V : HSp D) (P : Pl D → Prop) (x : GA D V) :
    ∃ x', matHom V x' = Units.map (cutHom (eps_sq P)) (matHom V x) :=
  ⟨⟨_, cut_mem (eps_sq P) (by simp [sigR, eps]) x.2⟩, rfl⟩

/- English proof (translation)
Establish `i1 : IsModuleTopology (AF D.host.F) (AE D)` using `⟨rfl⟩`. Establish `i2 : T2Space (AF D.host.F)` using `t2Space_adeleRing_numberField _`. Establish `i3 : T2Space (AE D)` using `t2_tensor_product`. Establish `i4 : IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Establish `hσ : Continuous (sigR (AF D.host.F) D.sp.cm.sig)` using `IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap`.

Establish `hφ : IsClosedEmbedding (matHom V)` using `(closed_unitary hσ _).isClosedEmbedding_subtypeVal`. Establish `hd : ∀ v, v ∈ A → ¬ v ∈ B` using `fun v hv h => Finset.disjoint_left.1 hAB h hv`. Establish `hU : {a : AF D.host.F | sndA _ a ∈ intAf _} ∈ nhds 0` using `((open_compact_hat D.host.F).1.preimage continuous_snd).mem_nhds fun v => zero_mem _`. Take `⟨l1, l2, l3, l4⟩` from `lattice hN.1 (intOn fun p => p ∉ A ∧ p ∉ B) (compact_intOn _) (e := idem fun p => p ∉ A ∧ p ∉ B) ⟨rfl, idemF_int _, fun _ hv => idemF_neg hv⟩ (fun a ha => (idem_mul_eq_iff _ a).2 ⟨ha.1, ha.2.2⟩) hU (fun a ha => ⟨by rw [map_mul, fst_idem, zero_mul], fun v => by rw [map_mul, map_mu …`. Establish `hsum : eps D (fun p => p ∉ A ∧ p ∉ B) + eps D (fun p => p ∈ A) + eps D (fun p => p ∈ B) = eps D fun _ => True`.

Simplify using `only [eps, ← TensorProduct.add_tmul]`. Rewrite using `[idem_sum hd]`. Take `⟨K, k1, k2, k3, k4⟩` from `level hφ (eps_sq fun p => p ∉ A ∧ p ∉ B) (eps_sq fun p => p ∈ A) (eps_sq fun p => p ∈ B) (eps_orth fun _ h => h.1) (eps_orth fun _ h => h.2) (eps_orth hd) (eps_stable V _) (eps_stable V _) (eps_stable V _) l1 l2 l3 l4 (Γ := GfC V) (MonoidHom.normal_ker _) (fun x => by rw [hsum]; …`. Use `⟨K, k1, k2, k3, fun k => (k4 k).trans ?_⟩` and prove the remaining obligations. Use `exists_congr fun κ => exists_congr fun x => exists_congr fun y => and_congr_left' ?_` and prove the remaining obligations.

Use `and_congr_right' (forall_congr' fun y => imp_congr_left ?_)` and prove the remaining obligations. Simplify using `only [mem_idAt]`. Conclude with `funext_iff`.
-/
theorem exists_level (D : D7) (V : HSp D) (N : Lat V) (A B : Finset (Pl D)) (JA JB : Subgroup (GA D V)) (b : GA D V)
    (hAB : Disjoint B A) (hN : Formalism.IndefR.Datum.IsSelfDualC V N) (_ : b ∈ GfC V)
    (lA : JA ≤ grpAt V fun x => x ∈ A) (cA : IsCompact (JA : Set (GA D V)))
    (oA : IsOpen (JA.subgroupOf (grpAt V fun x => x ∈ A) : Set (grpAt V fun x => x ∈ A)))
    (lB : JB ≤ grpAt V fun x => x ∈ B) (cB : IsCompact (JB : Set (GA D V)))
    (oB : IsOpen (JB.subgroupOf (grpAt V fun x => x ∈ B) : Set (grpAt V fun x => x ∈ B))) :
    ∃ K ≤ GfC V, IsCompact (K : Set (GA D V)) ∧ IsOpen (K.subgroupOf (GfC V) : Set (GfC V)) ∧
      ∀ k, k ∈ K ↔ ∃ κ x y, InK V N (fun p => p ∉ A ∧ p ∉ B) κ ∧ x ∈ JA ∧ y ∈ JB ∧ k = b⁻¹ * (κ * x * y) * b := by
  have i1 : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have i2 : T2Space (AF D.host.F) := t2Space_adeleRing_numberField _
  have i3 : T2Space (AE D) := t2_tensor_product
  have i4 : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hσ : Continuous (sigR (AF D.host.F) D.sp.cm.sig) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  have hφ : IsClosedEmbedding (matHom V) := (closed_unitary hσ _).isClosedEmbedding_subtypeVal
  have hd : ∀ v, v ∈ A → ¬ v ∈ B := fun v hv h => Finset.disjoint_left.1 hAB h hv
  have hU : {a : AF D.host.F | sndA _ a ∈ intAf _} ∈ nhds 0 :=
    ((open_compact_hat D.host.F).1.preimage continuous_snd).mem_nhds fun v => zero_mem _
  obtain ⟨l1, l2, l3, l4⟩ := lattice hN.1 (intOn fun p => p ∉ A ∧ p ∉ B) (compact_intOn _)
    (e := idem fun p => p ∉ A ∧ p ∉ B) ⟨rfl, idemF_int _, fun _ hv => idemF_neg hv⟩
    (fun a ha => (idem_mul_eq_iff _ a).2 ⟨ha.1, ha.2.2⟩) hU
    (fun a ha => ⟨by rw [map_mul, fst_idem, zero_mul],
      fun v => by rw [map_mul, map_mul]; exact mul_mem (idemF_int _ v) (ha v),
      fun v hv => by rw [map_mul, map_mul, snd_idem, idemF_neg hv, zero_mul]⟩) _ (latV_eq V N _)
  have hsum : eps D (fun p => p ∉ A ∧ p ∉ B) + eps D (fun p => p ∈ A) + eps D (fun p => p ∈ B) =
      eps D fun _ => True := by
    simp only [eps, ← TensorProduct.add_tmul]
    rw [idem_sum hd]
  obtain ⟨K, k1, k2, k3, k4⟩ := level hφ (eps_sq fun p => p ∉ A ∧ p ∉ B) (eps_sq fun p => p ∈ A)
    (eps_sq fun p => p ∈ B) (eps_orth fun _ h => h.1) (eps_orth fun _ h => h.2) (eps_orth hd)
    (eps_stable V _) (eps_stable V _) (eps_stable V _) l1 l2 l3 l4 (Γ := GfC V) (MonoidHom.normal_ker _)
    (fun x => by rw [hsum]; exact mem_fin V x) (mem_grpAt V _) (mem_grpAt V _) (mem_grpAt V _)
    lA cA oA lB cB oB b
  refine ⟨K, k1, k2, k3, fun k => (k4 k).trans ?_⟩
  refine exists_congr fun κ => exists_congr fun x => exists_congr fun y => and_congr_left' ?_
  refine and_congr_right' (forall_congr' fun y => imp_congr_left ?_)
  simp only [mem_idAt]
  exact funext_iff

end Adelic

end GlobalTheory.CompactOpenIntegers

end
