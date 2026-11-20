import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSectionSplitPlaceComponentMapStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPartStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormaliserGLintEqScalarMulGLintStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameConjGLintLeSelfDualLatticeStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldUniformizerAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformizerBlockEqDiagonalPowMulIntegralGLStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.StdEltLabel

set_option maxHeartbeats 4000000 in
/- English proof (translation)
Introduce `D hF V n Ps hS hn sp ϖ hϖ k hk`. Substitute `hn` using the available equality. Take `⟨⟨β, β', h1, h2, hm⟩, hK⟩` from `id hS`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h0`.

Use `hϖ` as an intermediate fact. Rewrite `this` using `[Formalism.AUTREP.IsUnif, h0, map_zero]`. Conclude with `WithZero.zero_ne_coe this`. Set `g0 : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E))` to `⟨Formalism.UG.diagJ V.rank ϖ k, Matrix.diagonal (fun i => if (i : ℕ) < k then ϖ⁻¹ else 1), by`. Rewrite using `[Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Apply the tactic sequence `congr 1; funext i; split_ifs <;> simp [hϖ0],`. Use `by`. Rewrite using `[Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Apply the tactic sequence `congr 1; funext i; split_ifs <;> simp [hϖ0]⟩`. Take `⟨emb, hembT, hembL⟩` from `GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp`.

Establish `hx₀ : emb g0 ∈ Formalism.AUTREP.tSet D.host.E V.rank sp ϖ k` using `⟨hembT g0, 1, one_mem _, 1, one_mem _, by rw [hembL]; simp [g0]⟩`. Take `⟨p, c, hpl, -, -, hπ⟩` from `GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D sp hF`. Establish `hidem : Formalism.L2.NTheta.IsIdemAt p.e sp.w` using `⟨p.split, hpl.2.2⟩`. Establish `hprime : Formalism.IndefR.Mult.IsPrimeIdem sp.w p.e (p.e + Formalism.L2.Theta.cA D p.e)` using `Or.inl ⟨hidem, rfl⟩`. Take `⟨y, hy1, hy2, hyu⟩` from `GlobalTheory.T.exists_realSubfield_uniformizer_at_splitPlace sp`.

Use `⟨emb g0, hx₀, p.e, p.e + Formalism.L2.Theta.cA D p.e, y, hprime, hy1, hy2, (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V V.rank Ps hS _ _ hprime (emb g0)).2 (hembT g0), ?_⟩` and prove the remaining obligations. Take `⟨sec, hs, hO', hO, hinc⟩` from `GlobalTheory.T.exists_integralSection_splitPlace_componentMap D sp hF`. Take `⟨hε, hker⟩` from `GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part D sp hF p c hπ`. Set `φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* sp.v.adicCompletion (maximalRealSubfield D.host.E)` to `sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom`. Establish `hφ : ∀ x, φ x = sp.proj (GlobalTheory.NJoin.tensCast hF x)` using `fun x => rfl`.

Establish `he : p.e * p.e = p.e` using `p.split.1`. Take `⟨B, b1, b2⟩` from `GlobalTheory.SphLabelOps.exists_basis (P := sp.w) V he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hprime)`. Establish `hee : Formalism.L2.Theta.finPart D p.e * Formalism.L2.Theta.finPart D p.e = Formalism.L2.Theta.finPart D p.e`. Rewrite using `[← map_mul, he]`. Take `⟨C, c1, c2⟩` from `(GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2`.

Establish `mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), Formalism.L2.Theta.finPart D p.e • (X * Y) = Formalism.L2.Theta.finPart D p.e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ …`. Introduce `X Y hXY`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `congrArg φ (congrFun (congrFun hXY i) j)` as an intermediate fact.

Rewrite `this` using `[Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hφ, hε, one_mul, one_mul]`. Then use the resulting hypothesis. Establish `hBC` using `mp _ _ c1`. Establish `hCB` using `mp _ _ c2`. Establish `hββ' : β.map φ * β'.map φ = 1`. Rewrite using `[← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]`.

Establish `hβ'β : β'.map φ * β.map φ = 1`. Rewrite using `[← Matrix.map_mul, h2, Matrix.map_one φ (map_zero φ) (map_one φ)]`. Take `⟨N, hNdef⟩ : ∃ N : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E)), (N : Matrix (Fin V.rank) (Fin V.rank) _) = β'.map φ * B.map φ` from `⟨⟨β'.map φ * B.map φ, C.map φ * β.map φ, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.map φ), hBC, Matrix.one_mul, hβ'β], by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β.map φ), hββ', Matrix.one_mul, hCB]⟩, rfl⟩`. Establish `hlat` using `GlobalTheory.T.standardFrame_conj_GLint_le_selfDualLattice_stabilizer hF Ps sp β β' h1 h2 hm hK (Formalism.L2.Theta.finPart D p.e) sec B hs hO' hO hε b1 b2`. Take `⟨k₁, hk₁, k₂, hk₂, hkk⟩` from `GlobalTheory.T.normaliser_GLint_conj_eq_two_sided_GLint_mul _ sp.v V.rank N (by rw [hNdef]; exact hlat) (Formalism.UG.diagJ V.rank ϖ k)`.

Take `⟨T, hT, hTe⟩` from `GlobalTheory.T.diagUniformizerBlock_eq_diagonal_pow_mul_integralGL _ sp.v V.rank k ϖ (sp.i (y : D.host.E)) hϖ hyu`. Rewrite using `[GlobalTheory.DivDual.divAt_iff]`. Use `⟨by simp [hk], ?_⟩` and prove the remaining obligations. Establish `hk₂' : T * k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v)` using `mul_mem hT hk₂`. Use `GlobalTheory.SphLabelOps.dv_of_cartan (OK := Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) φ sec hs hε hker (fun x hx => hO x hx) (fun t ht => hO' t ht) b1 b2 (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁)) (Formalism …` and prove the remaining obligations.

Establish `hdiag : (Matrix.diagonal fun i : Fin V.rank => φ (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D ((y : D.host.E) ^ ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0))))) = Matrix.diagonal (fun i : Fin V.rank => sp.i (y : D.host.E) ^ ((List.replicate …`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[hφ, hinc, map_zpow₀]`. Establish `hA : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g0))).map φ = β.map φ * Formalism.UG.diagJ V.rank ϖ k * β'.map φ`.

Rewrite using `[hm, Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`. Establish `e2 : ((emb g0).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map sp.proj = Formalism.UG.diagJ V.rank ϖ k` using `congrArg Units.val (hembL g0)`. Rewrite using `[← e2, Matrix.map_map]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `[φ]`. Establish `hBN : B.map φ = β.map φ * (N : Matrix (Fin V.rank) (Fin V.rank) _)`. Rewrite using `[hNdef, ← Matrix.mul_assoc, hββ', Matrix.one_mul]`. Establish `hNN : (N : Matrix (Fin V.rank) (Fin V.rank) _) * (N⁻¹).val = 1`.

Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Rewrite using `[hdiag, hA, hBN]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (β'.map φ), hβ'β, Matrix.one_mul]`. Use `_ = β.map φ * ((N : Matrix (Fin V.rank) (Fin V.rank) _) * ((N⁻¹).val * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _))) := by`.

Establish `e3 : (N : Matrix (Fin V.rank) (Fin V.rank) _) * ((N⁻¹).val * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _)) = Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _)`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hNN, Matrix.one_mul]`. Rewrite using `[e3, Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[hkk, hTe]`.

Simplify using `only [Units.val_mul, Matrix.mul_assoc]`.
-/
theorem std_elt_label : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ} (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E) (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ → ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E), Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧ Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧ Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := by
  intro D hF V n Ps hS hn sp ϖ hϖ k hk
  subst hn
  classical
  obtain ⟨⟨β, β', h1, h2, hm⟩, hK⟩ := id hS
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have := hϖ
    rw [Formalism.AUTREP.IsUnif, h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let g0 : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E)) :=
    ⟨Formalism.UG.diagJ V.rank ϖ k, Matrix.diagonal (fun i => if (i : ℕ) < k then ϖ⁻¹ else 1),
      by
        rw [Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; split_ifs <;> simp [hϖ0],
      by
        rw [Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; split_ifs <;> simp [hϖ0]⟩
  obtain ⟨emb, hembT, hembL⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp
  have hx₀ : emb g0 ∈ Formalism.AUTREP.tSet D.host.E V.rank sp ϖ k :=
    ⟨hembT g0, 1, one_mem _, 1, one_mem _, by rw [hembL]; simp [g0]⟩
  obtain ⟨p, c, hpl, -, -, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D sp hF
  have hidem : Formalism.L2.NTheta.IsIdemAt p.e sp.w := ⟨p.split, hpl.2.2⟩
  have hprime : Formalism.IndefR.Mult.IsPrimeIdem sp.w p.e (p.e + Formalism.L2.Theta.cA D p.e) := Or.inl ⟨hidem, rfl⟩
  obtain ⟨y, hy1, hy2, hyu⟩ := GlobalTheory.T.exists_realSubfield_uniformizer_at_splitPlace sp
  refine ⟨emb g0, hx₀, p.e, p.e + Formalism.L2.Theta.cA D p.e, y, hprime, hy1, hy2,
    (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V V.rank Ps hS _ _ hprime (emb g0)).2 (hembT g0), ?_⟩
  obtain ⟨sec, hs, hO', hO, hinc⟩ := GlobalTheory.T.exists_integralSection_splitPlace_componentMap D sp hF
  obtain ⟨hε, hker⟩ := GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part D sp hF p c hπ
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* sp.v.adicCompletion (maximalRealSubfield D.host.E) :=
    sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom
  have hφ : ∀ x, φ x = sp.proj (GlobalTheory.NJoin.tensCast hF x) := fun x => rfl
  have he : p.e * p.e = p.e := p.split.1
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis (P := sp.w) V he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hprime)
  have hee : Formalism.L2.Theta.finPart D p.e * Formalism.L2.Theta.finPart D p.e = Formalism.L2.Theta.finPart D p.e := by
    rw [← map_mul, he]
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      Formalism.L2.Theta.finPart D p.e • (X * Y) = Formalism.L2.Theta.finPart D p.e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) →
        X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hφ, hε, one_mul,
      one_mul] at this
  have hBC := mp _ _ c1
  have hCB := mp _ _ c2
  have hββ' : β.map φ * β'.map φ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hβ'β : β'.map φ * β.map φ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one φ (map_zero φ) (map_one φ)]
  obtain ⟨N, hNdef⟩ : ∃ N : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E)),
      (N : Matrix (Fin V.rank) (Fin V.rank) _) = β'.map φ * B.map φ :=
    ⟨⟨β'.map φ * B.map φ, C.map φ * β.map φ,
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.map φ), hBC, Matrix.one_mul, hβ'β],
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β.map φ), hββ', Matrix.one_mul, hCB]⟩, rfl⟩
  have hlat := GlobalTheory.T.standardFrame_conj_GLint_le_selfDualLattice_stabilizer hF Ps sp β β' h1 h2 hm hK (Formalism.L2.Theta.finPart D p.e) sec B hs hO' hO hε b1 b2
  obtain ⟨k₁, hk₁, k₂, hk₂, hkk⟩ := GlobalTheory.T.normaliser_GLint_conj_eq_two_sided_GLint_mul _ sp.v V.rank N (by rw [hNdef]; exact hlat) (Formalism.UG.diagJ V.rank ϖ k)
  obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.diagUniformizerBlock_eq_diagonal_pow_mul_integralGL _ sp.v V.rank k ϖ (sp.i (y : D.host.E)) hϖ hyu
  rw [GlobalTheory.DivDual.divAt_iff]
  refine ⟨by simp [hk], ?_⟩
  have hk₂' : T * k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) := mul_mem hT hk₂
  refine GlobalTheory.SphLabelOps.dv_of_cartan (OK := Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) φ sec hs hε hker
    (fun x hx => hO x hx) (fun t ht => hO' t ht) b1 b2
    (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁))
    (Formalism.UG.P.cartan_entries_of_mem _ _ hk₂') (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂')) ?_
  have hdiag : (Matrix.diagonal fun i : Fin V.rank => φ (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D
      ((y : D.host.E) ^ ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0))))) =
      Matrix.diagonal (fun i : Fin V.rank => sp.i (y : D.host.E) ^
        ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0)) := by
    congr 1; funext i; rw [hφ, hinc, map_zpow₀]
  have hA : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g0))).map φ =
      β.map φ * Formalism.UG.diagJ V.rank ϖ k * β'.map φ := by
    rw [hm, Matrix.map_mul, Matrix.map_mul]
    congr 2
    have e2 : ((emb g0).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map sp.proj =
        Formalism.UG.diagJ V.rank ϖ k := congrArg Units.val (hembL g0)
    rw [← e2, Matrix.map_map]
    congr 1
    funext x
    simp [φ]
  have hBN : B.map φ = β.map φ * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
    rw [hNdef, ← Matrix.mul_assoc, hββ', Matrix.one_mul]
  have hNN : (N : Matrix (Fin V.rank) (Fin V.rank) _) *
      (N⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hdiag, hA, hBN]
  calc β.map φ * Formalism.UG.diagJ V.rank ϖ k * β'.map φ * (β.map φ * (N : Matrix (Fin V.rank) (Fin V.rank) _))
      = β.map φ * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β'.map φ), hβ'β, Matrix.one_mul]
    _ = β.map φ * ((N : Matrix (Fin V.rank) (Fin V.rank) _) *
          ((N⁻¹).val *
            Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _))) := by
        have e3 : (N : Matrix (Fin V.rank) (Fin V.rank) _) * ((N⁻¹).val * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _)) =
            Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hNN, Matrix.one_mul]
        rw [e3, Matrix.mul_assoc]
    _ = _ := by
        rw [hkk, hTe]
        simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.StdEltLabel
