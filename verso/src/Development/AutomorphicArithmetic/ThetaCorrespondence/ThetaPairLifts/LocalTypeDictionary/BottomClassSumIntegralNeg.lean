import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped ComplexOrder
open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal
open GlobalTheory.Grid (neg sgn ofSgn)
namespace GlobalTheory.RowTest.BottomClassSumNeg
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}
end GlobalTheory.RowTest.BottomClassSumNeg
namespace GlobalTheory.RowTest.BottomClassSumNeg
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}
/- English proof (translation)
Introduce `D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX`. Establish `hV : ∀ φ : D.host.E →+* ℂ, (A.gram.map φ).PosDef` using `fun φ => by`. Rewrite using `[hX.std.1, Matrix.map_one φ (map_zero φ) (map_one φ)]`. Conclude with `Matrix.PosDef.one`. Set `V' : HSp D` to `{ A with sig := fun _ => (A.rank, 0) }`.

Establish `hS' : V'.SigOK` using `fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)`. Establish `hD' : V'.IsDefinite` using `fun τ => Or.inl rfl`. Establish `hGc : IsCompact (GinfC A : Set (GA D A))` using `Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'`. Use `haveI : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 hGc`. Establish `hT` using `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A`.

Establish `hLC` using `hT.1`. Establish `hSC` using `hT.2.1`. Establish `hB` using `hT.2.2.2.1`. Establish `hG` using `hT.2.2.2.2.1`. Establish `hC` using `hT.2.2.2.2.2.2`.

Take `⟨K'', hK'', hr⟩` from `level_all μ₀ hX`. Establish `hfin0 : Finite (FinCl A K'')` using `(finite_finCl_and_gamOrd A K'' hV hK'').1`. Set `μ` to `X.m`. Use `haveI : μ.IsHaarMeasure := hX.is.meas.1`. Establish `hfd : IsFundamentalDomain (GQ A) X.fd μ` using `hX.is.meas.2`.

Set `J : Subgroup (GA D A)` to `K''.comap (Lev.finE A)`. Establish `hJo : IsOpen (J : Set (GA D A))` using `hK''.1`. Establish `hJc : IsCompact (J : Set (GA D A))`. Use `(hK''.2.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hK''.1) ?_` and prove the remaining obligations. Introduce `k hk`.

Conclude with `⟨finPart A k, finPart_mem_levA A hk, realPart A k, realPart_mem A k, finPart_mul_realPart A k⟩`. Establish `hJtop : μ J ≠ ⊤` using `hJc.measure_lt_top.ne`. Establish `hJ0 : μ J ≠ 0` using `(hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'`. Establish `hinfJ : GinfC A ≤ J` using `by show GinfC A ≤ K''.comap (Lev.finE A)`. Rewrite using `[GlobalTheory.Mass.Levels.comap_finE]`.

Conclude with `le_sup_right`. Set `κ : Measure (GinfC A)` to `Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC A))`. Use `haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _`. Establish `hκ1 : κ Set.univ = 1`. Use `Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC A)))` as an intermediate fact.

Simplify using `using this`. Use `haveI : IsProbabilityMeasure κ := ⟨hκ1⟩`. Set `e` to `finEquiv A`. Establish `he : ∀ γ, e (((finPt A).comp (GQ A).subtype) γ) = Bridge.ratF A γ` using `fun γ => e.apply_symm_apply _`. Establish `hJe : ∀ a, e a ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'' ↔ a ∈ K''.comap (finG A)` using `fun a => Iff.rfl`.

Establish `hy` using `isReps_transfer _ _ e he _ _ hJe _ (isReps_out A K'')`. Set `N` to `Nat.card (FinCl A K'')`. Set `eq : FinCl A K'' ≃ Fin N` to `Finite.equivFin _`. Set `y : FinCl A K'' → Bridge.Gf A` to `fun c => e (Quotient.out c)`. Set `zc : FinCl A K'' → GA D A` to `fun c => ((Quotient.out c : GfC A) : GA D A)`.

Establish `hz : ∀ c, (finHom A).rangeRestrict (zc c) = y c` using `fun c => rfl`. Establish `hu0 : ∀ x : GA D A, ∃! c, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k` using `existsUnique_doubleCoset (finHom A).rangeRestrict (GQ A) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'') y hy zc hz`. Set `z : Fin N → GA D A` to `fun l => zc (eq.symm l)`. Establish `hu : ∀ x : GA D A, ∃! l, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * z l * k` using `fun x => (eq.existsUnique_congr_left (p := fun c => ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k)).1 (hu0 x)`. Establish `hfinΓ : ∀ l, {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J}.Finite` using `fun l => GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ A) J hfd hJ0 hJtop (z l)`.

Establish `him : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J} = Subtype.val '' {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J}`. Introduce `l`. Use extensionality with `γ`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]`. Conclude with `⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩`.

Establish `hfin : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite` using `fun l => him l ▸ (hfinΓ l).image _`. Establish `hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA A K'', ∃ w : GinfC A, k = k' * (GinfC A).subtype w` using `fun k hk => ⟨finPart A k, finPart_mem_levA A hk, ⟨realPart A k, realPart_mem A k⟩, (finPart_mul_realPart A k).symm⟩`. Establish `hcomm : ∀ k ∈ Lev.levA A K'', ∀ w : GinfC A, k * (GinfC A).subtype w = (GinfC A).subtype w * k` using `fun k hk w => (Formalism.IndefR.Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm`. Establish `hrt : ∀ w : GinfC A, MeasurePreserving (· * (GinfC A).subtype w) μ μ` using `fun w => measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)`. Use `⟨(μ J).toReal, N, z, fun l => {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.ncard, κ, ENNReal.toReal_pos hJ0 hJtop, fun l => (Quotient.out (eq.symm l)).2, fun l => ?_, inferInstance, inferInstance, fun t P h _ => ?_⟩` and prove the remaining obligations.

Conclude with `(Set.ncard_pos (hfin l)).2 ⟨1, (GQ A).one_mem, by simp [J.one_mem]⟩`. Establish `hcont : Continuous (X.ker W.ψ W.θ t P h)` using `continuous_of_level A K'' hK''.1 _ (fun k hk g => hr t P h k hk g) (ker_cont hX t P h)`. Take `⟨-, heq⟩` from `integral_eq_sum_avg (GA D A) μ (GQ A) J (Lev.levA A K'') X.fd hfd hJo hJtop (GinfC A) κ (GinfC A).subtype continuous_subtype_val hrt hdec hcomm (Fin N) z hu hfin (X.ker W.ψ W.θ t P h) hcont (ker_left hX t P h) (fun k hk g => hr t P h k hk g)`. Conclude with `heq`.
-/
theorem integral_eq_bottom_classSum : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A) (w : Fin N → ℕ) (κ : Measure (GinfC A)), 0 < v ∧ (∀ l, z l ∈ GfC A) ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank), ∀ h ∈ GfC WW,
        X.I W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker W.ψ W.θ t P h (z l * (g : GA D A)) ∂κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hV : ∀ φ : D.host.E →+* ℂ, (A.gram.map φ).PosDef := fun φ => by
    rw [hX.std.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A with sig := fun _ => (A.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A : Set (GA D A)) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  obtain ⟨K'', hK'', hr⟩ := level_all μ₀ hX
  have hfin0 : Finite (FinCl A K'') := (finite_finCl_and_gamOrd A K'' hV hK'').1
  let μ := X.m
  haveI : μ.IsHaarMeasure := hX.is.meas.1
  have hfd : IsFundamentalDomain (GQ A) X.fd μ := hX.is.meas.2
  let J : Subgroup (GA D A) := K''.comap (Lev.finE A)
  have hJo : IsOpen (J : Set (GA D A)) := hK''.1
  have hJc : IsCompact (J : Set (GA D A)) := by
    refine (hK''.2.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hK''.1) ?_
    intro k hk
    exact ⟨finPart A k, finPart_mem_levA A hk, realPart A k, realPart_mem A k, finPart_mul_realPart A k⟩
  have hJtop : μ J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC A ≤ J := by
    show GinfC A ≤ K''.comap (Lev.finE A)
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  let κ : Measure (GinfC A) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC A))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC A)))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  let e := finEquiv A
  have he : ∀ γ, e (((finPt A).comp (GQ A).subtype) γ) = Bridge.ratF A γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'' ↔ a ∈ K''.comap (finG A) := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out A K'')
  let N := Nat.card (FinCl A K'')
  let eq : FinCl A K'' ≃ Fin N := Finite.equivFin _
  let y : FinCl A K'' → Bridge.Gf A := fun c => e (Quotient.out c)
  let zc : FinCl A K'' → GA D A := fun c => ((Quotient.out c : GfC A) : GA D A)
  have hz : ∀ c, (finHom A).rangeRestrict (zc c) = y c := fun c => rfl
  have hu0 : ∀ x : GA D A, ∃! c, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k :=
    existsUnique_doubleCoset (finHom A).rangeRestrict (GQ A) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A K'') y hy zc hz
  let z : Fin N → GA D A := fun l => zc (eq.symm l)
  have hu : ∀ x : GA D A, ∃! l, ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * z l * k := fun x =>
    (eq.existsUnique_congr_left (p := fun c => ∃ γ ∈ GQ A, ∃ k ∈ J, x = γ * zc c * k)).1 (hu0 x)
  have hfinΓ : ∀ l, {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J}.Finite := fun l =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ A) J hfd hJ0 hJtop (z l)
  have him : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J} =
      Subtype.val '' {γ : GQ A | (z l)⁻¹ * (γ : GA D A) * z l ∈ J} := by
    intro l
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ l, {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l =>
    him l ▸ (hfinΓ l).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA A K'', ∃ w : GinfC A, k = k' * (GinfC A).subtype w := fun k hk =>
    ⟨finPart A k, finPart_mem_levA A hk, ⟨realPart A k, realPart_mem A k⟩, (finPart_mul_realPart A k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA A K'', ∀ w : GinfC A, k * (GinfC A).subtype w = (GinfC A).subtype w * k :=
    fun k hk w => (Formalism.IndefR.Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC A, MeasurePreserving (· * (GinfC A).subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  refine ⟨(μ J).toReal, N, z, fun l => {γ : GA D A | γ ∈ GQ A ∧ (z l)⁻¹ * γ * z l ∈ J}.ncard, κ,
    ENNReal.toReal_pos hJ0 hJtop, fun l => (Quotient.out (eq.symm l)).2, fun l => ?_, inferInstance, inferInstance,
    fun t P h _ => ?_⟩
  · exact (Set.ncard_pos (hfin l)).2 ⟨1, (GQ A).one_mem, by simp [J.one_mem]⟩
  · have hcont : Continuous (X.ker W.ψ W.θ t P h) :=
      continuous_of_level A K'' hK''.1 _ (fun k hk g => hr t P h k hk g) (ker_cont hX t P h)
    obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D A) μ (GQ A) J (Lev.levA A K'') X.fd hfd hJo hJtop (GinfC A) κ
      (GinfC A).subtype continuous_subtype_val hrt hdec hcomm (Fin N) z hu hfin (X.ker W.ψ W.θ t P h) hcont
      (ker_left hX t P h) (fun k hk g => hr t P h k hk g)
    exact heq
end GlobalTheory.RowTest.BottomClassSumNeg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum | exact _root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum | (intros; apply _root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.bottom_class_sum_integral_neg : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A) (w : Fin N → ℕ) (κ : Measure (GinfC A)), 0 < v ∧ (∀ l, z l ∈ GfC A) ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank), ∀ h ∈ GfC WW,
        X.I W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker W.ψ W.θ t P h (z l * (g : GA D A)) ∂κ := by
  first | exact @_root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum | exact _root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum | (intros; apply _root_.GlobalTheory.RowTest.BottomClassSumNeg.integral_eq_bottom_classSum <;> assumption)
end
