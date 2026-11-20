import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfNormOneValuationSubOneSmallStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmIdeleConjMemCongruenceUnitIdelesConjPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOneStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj) in
open GlobalTheory.HeckeUnrExt in

/- English proof (translation)
Introduce `E _ _ _ ψ a hψ hns w₀ _`. Take `⟨M, hM, hlev⟩` from `GlobalTheory.Mem.HeckeLevel.exists_level_nat _ ψ`. Take `⟨w₁, hw₁s, hw₁⟩` from `GlobalTheory.T.exists_other_split_place_with_distinct_real_place E w₀`. Use `set K : ℕ := Module.finrank ℚ E + 1 with hK`. Use `set Q : ℕ := Ideal.absNorm w₁.asIdeal ^ K with hQ`.

Establish `hQ0 : 0 < Q` using `pow_pos (Nat.pos_of_ne_zero fun h => w₁.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) _`. Use `set N : ℕ := 3 * M * Q with hN`. Establish `hN0 : 0 < N` using `by positivity`. Set `T : Set (HeightOneSpectrum (𝓞 E))` to `{w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀}`. Set `T' : Set (HeightOneSpectrum (𝓞 E))` to `{w | ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T}`.

Establish `hw₁T : w₁ ∈ T'` using `fun w' e => by`. Use `⟨?_, fun h => hw₁ (h ▸ e).symm⟩` and prove the remaining obligations. Distinguish the cases in `h : w' = w₁`. Conclude with `h ▸ hw₁s`. Conclude with `⟨w₁, fun h' => h h'.symm, e.symm⟩`.

Establish `hT'T : T' ⊆ T` using `fun w hw => hw w rfl`. Establish `hF : ∀ b : Ideles (maximalRealSubfield E), ideleMap _ E b ∈ levT E T N → ψ.1 b = kap E a (ideleMap _ E b)`. Introduce `b hb`. Set `z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ` to `Units.map (MonoidHom.fst _ _) b`. Establish `e : b = Units.map (MonoidHom.inl _ _) z * GlobalTheory.Mem.Chr.finPartI _ b` using `Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)`.

Establish `h1 : ψ.1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1` using `GlobalTheory.T.realSubfield_heckeChar_finitePart_eq_one E ψ M hlev (fun w hw => (hns w hw).2) w₀ N ⟨3 * Q, by rw [hN]; ring⟩ b hb`. Establish `h2 : kap E a (ideleMap _ E b) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z))`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_kap, coe_kap]`. Both sides reduce to the same expression.

Rewrite using `[h2, ← psi_eq_kap E ψ a hψ z]`. Use `conv_lhs => rw [e, map_mul, h1, mul_one]`. Establish `hprin : ∀ ε : Eˣ, diagUnits E ε ∈ levT E T' N → (∀ φ : E →+* ℂ, ‖φ ε‖ = 1) → ε = 1`. Introduce `ε hε hn`. Use `Units.ext (GlobalTheory.T.eq_one_of_norm_one_valuation_sub_one_small E (ε : E) w₁ K (by omega) (fun v => ?_) hn ?_)` and prove the remaining obligations.

Establish `e : Valued.v (algebraMap E (v.adicCompletion E) (ε : E)) = 1` using `hε.1 v`. Rewrite `e` using `[GlobalTheory.UpIdeleMod.valued_algebraMap]`. Conclude with `e.le`. Establish `e : Valued.v (algebraMap E (w₁.adicCompletion E) (ε : E) - 1) ≤ Valued.v (N : w₁.adicCompletion E)` using `hε.2 w₁ hw₁T`. Rewrite `e` using `[← map_one (algebraMap E (w₁.adicCompletion E)), ← map_sub, ← map_natCast (algebraMap E (w₁.adicCompletion E)), GlobalTheory.UpIdeleMod.valued_algebraMap, GlobalTheory.UpIdeleMod.valued_algebraMap]`.

Use `e.trans ?_` and prove the remaining obligations. Establish `eN : ((N : ℕ) : E) = algebraMap (𝓞 E) E ((3 * M : ℕ) : 𝓞 E) * algebraMap (𝓞 E) E ((Q : ℕ) : 𝓞 E)`. Rewrite using `[← map_mul, ← Nat.cast_mul, map_natCast]`. Rewrite using `[eN, map_mul]`. Use `(mul_le_of_le_one_left' (HeightOneSpectrum.valuation_le_one _ _)).trans ?_` and prove the remaining obligations.

Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]`. Rewrite using `[hQ, Nat.cast_pow]`. Conclude with `Ideal.pow_mem_pow (Ideal.absNorm_mem w₁.asIdeal) K`. Take `⟨ξ, hξ⟩` from `glue (((ideleMap (maximalRealSubfield E) E).coprod (levT E T N).subtype).coprod (diagUnits E)) ((MonoidHom.coprod ψ.1 ((kap E a).comp (levT E T N).subtype)).coprod 1) (by`. Introduce and unpack `⟨⟨b, u, hu⟩, k⟩ h`.

Express the relevant statement in the definitionally equal form `ideleMap (maximalRealSubfield E) E b * u * diagUnits E k = 1 at h`. Express the relevant statement in the definitionally equal form `ψ.1 b * kap E a u * 1 = 1`. Set `c` to `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E`. Establish `h'` using `congrArg (ideleConj (maximalRealSubfield E) E) h`. Establish `c1 : ideleConj (maximalRealSubfield E) E (ideleMap _ E b) = ideleMap _ E b` using `Units.ext (GlobalTheory.UnitaryHeckeBaseChange.adeleConj_adeleMap _)`.

Establish `c2 : ideleConj (maximalRealSubfield E) E (diagUnits E k) = diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k)` using `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele _ E k`. Establish `c3 : ideleConj (maximalRealSubfield E) E u ∈ levT E T' N` using `GlobalTheory.T.cmIdeleConj_mem_congruenceUnitIdeles_conj_places E T N u hu`. Rewrite `h'` using `[map_mul, map_mul, map_one, c1, c2, ← h, mul_assoc, mul_assoc, mul_right_inj]`. Establish `h3 : diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k / k) = u / ideleConj (maximalRealSubfield E) E u`. Rewrite using `[_root_.map_div, div_eq_div_iff_mul_eq_mul, mul_comm, h']`.

Establish `h4` using `hprin _ (h3 ▸ div_mem (levT_anti E hT'T N hu) c3) fun φ => by`. Rewrite using `[Units.val_div_eq_div_val, map_div₀, norm_div]`. Establish `: φ (Units.map c.toRingEquiv.toRingHom.toMonoidHom k : Eˣ) = starRingEnd ℂ (φ k)` using `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k`. Rewrite using `[this, Complex.norm_conj, div_self (by simp)]`. Establish `h5 : IsCMField.complexConj E k = k` using `congrArg Units.val (div_eq_one.1 h4)`.

Establish `h6 : (k : E) ∈ maximalRealSubfield E` using `(IsCMField.complexConj_eq_self_iff E (k : E)).1 h5`. Set `k0 : (maximalRealSubfield E)ˣ` to `Units.mk0 ⟨k, h6⟩ fun h0 => k.ne_zero (congrArg Subtype.val h0)`. Establish `h7 : ideleMap _ E (diagUnits _ k0) = diagUnits E k` using `(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k0).trans (congrArg (diagUnits E) (Units.ext rfl))`. Establish `h8 : ideleMap _ E (b * diagUnits _ k0) = u⁻¹`. Rewrite using `[map_mul, h7, eq_inv_iff_mul_eq_one, mul_right_comm, h]`.

Establish `h9` using `hF _ (h8 ▸ inv_mem hu)`. Rewrite `h9` using `[h8, map_mul, ψ.2.2, mul_one, map_inv]`. Rewrite using `[h9, inv_mul_cancel, one_mul])`. Establish `hu : ∀ u ∈ levT E T N, ξ u = kap E a u` using `fun u hu => by`. Simplify using `using hξ ((1, ⟨u, hu⟩), 1)`.

Set `κ : HChar E` to `⟨ξ, ?_, fun k => by simpa using hξ ((1, 1), k)⟩`. Use `swap`. Use `continuous_of_continuousAt_one ξ ((continuous_kap E a).continuousAt.congr ?_) filter_upwards [levT_mem_nhds E T (N := N) (by omega)] with x hx` and prove the remaining obligations. Conclude with `(hu x hx).symm`. Establish `hloc : ∀ w, w ∉ T → κ.UnrAt w`.

Introduce `w hw x hx`. Establish `hmem : localIdele E w x ∈ levT E T N`. Use `⟨fun v => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hvw : v = w`. Substitute `hvw` using the available equality.

Rewrite using `[GlobalTheory.HeckeProduct.localIdele_snd_self]`. Conclude with `hx`. Rewrite using `[GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]`. Conclude with `map_one _`. Establish `hvw : v ≠ w` using `fun e => hw (e ▸ hv)`.

Rewrite using `[GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]`. Use `show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _`. Rewrite using `[sub_self, map_zero]`. Conclude with `zero_le`. Use `show ξ (localIdele E w x) = 1`.

Rewrite using `[hu _ hmem]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[kap_of_fst a _ (1 : E) (by rw [GlobalTheory.HeckeProduct.localIdele_fst, map_one])]`. Simplify using the standard rewrite rules. Use `⟨κ, fun φ => if (InfinitePlace.mk φ).embedding = φ then a else 0, fun k => ?_, Subtype.ext (MonoidHom.ext fun b => ?_), hloc w₀ fun h => h.2 rfl, fun w hw => hloc w fun h => hw h.1⟩` and prove the remaining obligations.

Establish `h1 : infDiag k ∈ levT E T N`. Use `lev_le_levT E T N ⟨fun v => ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_infDiag']`. Conclude with `map_one _`. Rewrite using `[coe_infDiag'] show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _`.

Rewrite using `[sub_self, map_zero]`. Conclude with `zero_le`. Express the relevant statement in the definitionally equal form `((ξ (infDiag k) : ℂˣ) : ℂ) = _`. Rewrite using `[hu _ h1, kap_of_fst a _ (k : E) (by rw [coe_infDiag']), prod_type]`. Express the relevant statement in the definitionally equal form `ξ (ideleMap _ E b) = ψ.1 b`.

Simplify using `using hξ ((b, 1), 1)`.
-/
theorem GlobalTheory.HeckeUnrExt.exists_ext_unr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (b : ℤ), χ.IsAlg (fun _ => b) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧ χ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ w₀ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ GlobalTheory.HeightCounting.Blocks.resReal κ = χ ∧ κ.UnrAt w₀ ∧ ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → κ.UnrAt w := by
  intro E _ _ _ ψ a hψ hns w₀ _
  classical
  obtain ⟨M, hM, hlev⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat _ ψ
  obtain ⟨w₁, hw₁s, hw₁⟩ := GlobalTheory.T.exists_other_split_place_with_distinct_real_place E w₀
  set K : ℕ := Module.finrank ℚ E + 1 with hK
  set Q : ℕ := Ideal.absNorm w₁.asIdeal ^ K with hQ
  have hQ0 : 0 < Q := pow_pos (Nat.pos_of_ne_zero fun h => w₁.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) _
  set N : ℕ := 3 * M * Q with hN
  have hN0 : 0 < N := by positivity
  let T : Set (HeightOneSpectrum (𝓞 E)) := {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀}
  let T' : Set (HeightOneSpectrum (𝓞 E)) := {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T}
  have hw₁T : w₁ ∈ T' := fun w' e => by
    refine ⟨?_, fun h => hw₁ (h ▸ e).symm⟩
    by_cases h : w' = w₁
    · exact h ▸ hw₁s
    · exact ⟨w₁, fun h' => h h'.symm, e.symm⟩
  have hT'T : T' ⊆ T := fun w hw => hw w rfl
  have hF : ∀ b : Ideles (maximalRealSubfield E), ideleMap _ E b ∈ levT E T N → ψ.1 b = kap E a (ideleMap _ E b) := by
    intro b hb
    let z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ := Units.map (MonoidHom.fst _ _) b
    have e : b = Units.map (MonoidHom.inl _ _) z * GlobalTheory.Mem.Chr.finPartI _ b :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have h1 : ψ.1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 :=
      GlobalTheory.T.realSubfield_heckeChar_finitePart_eq_one E ψ M hlev (fun w hw => (hns w hw).2) w₀ N ⟨3 * Q, by rw [hN]; ring⟩ b hb
    have h2 : kap E a (ideleMap _ E b) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z)) := by
      apply Units.ext
      rw [coe_kap, coe_kap]
      rfl
    rw [h2, ← psi_eq_kap E ψ a hψ z]
    conv_lhs => rw [e, map_mul, h1, mul_one]
  have hprin : ∀ ε : Eˣ, diagUnits E ε ∈ levT E T' N → (∀ φ : E →+* ℂ, ‖φ ε‖ = 1) → ε = 1 := by
    intro ε hε hn
    refine Units.ext (GlobalTheory.T.eq_one_of_norm_one_valuation_sub_one_small E (ε : E) w₁ K (by omega) (fun v => ?_) hn ?_)
    · have e : Valued.v (algebraMap E (v.adicCompletion E) (ε : E)) = 1 := hε.1 v
      rw [GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      exact e.le
    · have e : Valued.v (algebraMap E (w₁.adicCompletion E) (ε : E) - 1) ≤ Valued.v (N : w₁.adicCompletion E) := hε.2 w₁ hw₁T
      rw [← map_one (algebraMap E (w₁.adicCompletion E)), ← map_sub,
        ← map_natCast (algebraMap E (w₁.adicCompletion E)), GlobalTheory.UpIdeleMod.valued_algebraMap,
        GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      refine e.trans ?_
      have eN : ((N : ℕ) : E) = algebraMap (𝓞 E) E ((3 * M : ℕ) : 𝓞 E) * algebraMap (𝓞 E) E ((Q : ℕ) : 𝓞 E) := by
        rw [← map_mul, ← Nat.cast_mul, map_natCast]
      rw [eN, map_mul]
      refine (mul_le_of_le_one_left' (HeightOneSpectrum.valuation_le_one _ _)).trans ?_
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
      rw [hQ, Nat.cast_pow]
      exact Ideal.pow_mem_pow (Ideal.absNorm_mem w₁.asIdeal) K
  obtain ⟨ξ, hξ⟩ := glue
    (((ideleMap (maximalRealSubfield E) E).coprod (levT E T N).subtype).coprod (diagUnits E))
    ((MonoidHom.coprod ψ.1 ((kap E a).comp (levT E T N).subtype)).coprod 1) (by
      rintro ⟨⟨b, u, hu⟩, k⟩ h
      change ideleMap (maximalRealSubfield E) E b * u * diagUnits E k = 1 at h
      change ψ.1 b * kap E a u * 1 = 1
      let c := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E
      have h' := congrArg (ideleConj (maximalRealSubfield E) E) h
      have c1 : ideleConj (maximalRealSubfield E) E (ideleMap _ E b) = ideleMap _ E b :=
        Units.ext (GlobalTheory.UnitaryHeckeBaseChange.adeleConj_adeleMap _)
      have c2 : ideleConj (maximalRealSubfield E) E (diagUnits E k) =
          diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k) :=
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele _ E k
      have c3 : ideleConj (maximalRealSubfield E) E u ∈ levT E T' N := GlobalTheory.T.cmIdeleConj_mem_congruenceUnitIdeles_conj_places E T N u hu
      rw [map_mul, map_mul, map_one, c1, c2, ← h, mul_assoc, mul_assoc, mul_right_inj] at h'
      have h3 : diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k / k) =
          u / ideleConj (maximalRealSubfield E) E u := by
        rw [_root_.map_div, div_eq_div_iff_mul_eq_mul, mul_comm, h']
      have h4 := hprin _ (h3 ▸ div_mem (levT_anti E hT'T N hu) c3) fun φ => by
        rw [Units.val_div_eq_div_val, map_div₀, norm_div]
        have : φ (Units.map c.toRingEquiv.toRingHom.toMonoidHom k : Eˣ) = starRingEnd ℂ (φ k) :=
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k
        rw [this, Complex.norm_conj, div_self (by simp)]
      have h5 : IsCMField.complexConj E k = k := congrArg Units.val (div_eq_one.1 h4)
      have h6 : (k : E) ∈ maximalRealSubfield E := (IsCMField.complexConj_eq_self_iff E (k : E)).1 h5
      let k0 : (maximalRealSubfield E)ˣ := Units.mk0 ⟨k, h6⟩ fun h0 => k.ne_zero (congrArg Subtype.val h0)
      have h7 : ideleMap _ E (diagUnits _ k0) = diagUnits E k :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k0).trans (congrArg (diagUnits E) (Units.ext rfl))
      have h8 : ideleMap _ E (b * diagUnits _ k0) = u⁻¹ := by
        rw [map_mul, h7, eq_inv_iff_mul_eq_one, mul_right_comm, h]
      have h9 := hF _ (h8 ▸ inv_mem hu)
      rw [h8, map_mul, ψ.2.2, mul_one, map_inv] at h9
      rw [h9, inv_mul_cancel, one_mul])
  have hu : ∀ u ∈ levT E T N, ξ u = kap E a u := fun u hu => by
    simpa using hξ ((1, ⟨u, hu⟩), 1)
  let κ : HChar E := ⟨ξ, ?_, fun k => by simpa using hξ ((1, 1), k)⟩
  swap
  · refine continuous_of_continuousAt_one ξ ((continuous_kap E a).continuousAt.congr ?_)
    filter_upwards [levT_mem_nhds E T (N := N) (by omega)] with x hx
    exact (hu x hx).symm
  have hloc : ∀ w, w ∉ T → κ.UnrAt w := by
    intro w hw x hx
    have hmem : localIdele E w x ∈ levT E T N := by
      refine ⟨fun v => ?_, fun v hv => ?_⟩
      · by_cases hvw : v = w
        · subst hvw
          rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
          exact hx
        · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]
          exact map_one _
      · have hvw : v ≠ w := fun e => hw (e ▸ hv)
        rw [GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]
        show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _
        rw [sub_self, map_zero]
        exact zero_le
    show ξ (localIdele E w x) = 1
    rw [hu _ hmem]
    apply Units.ext
    rw [kap_of_fst a _ (1 : E) (by rw [GlobalTheory.HeckeProduct.localIdele_fst, map_one])]
    simp
  refine ⟨κ, fun φ => if (InfinitePlace.mk φ).embedding = φ then a else 0, fun k => ?_,
    Subtype.ext (MonoidHom.ext fun b => ?_), hloc w₀ fun h => h.2 rfl, fun w hw => hloc w fun h => hw h.1⟩
  · have h1 : infDiag k ∈ levT E T N := by
      refine lev_le_levT E T N ⟨fun v => ?_, fun v => ?_⟩
      · rw [coe_infDiag']
        exact map_one _
      · rw [coe_infDiag']
        show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _
        rw [sub_self, map_zero]
        exact zero_le
    change ((ξ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hu _ h1, kap_of_fst a _ (k : E) (by rw [coe_infDiag']), prod_type]
  · change ξ (ideleMap _ E b) = ψ.1 b
    simpa using hξ ((b, 1), 1)
