import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HeckeCharacterFamilyConductor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PeterssonSquareIntegrableDefiniteOfLawsStatement

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D Q hQ hpq pb hpb hMb chiW hchi`. Establish `hM : Q.l.M = D.host.g 0 * D.host.g 1` using `hQ.2.1.1`. Use `choose iota hiota using exists_iotaAll Q hQ`. Use `choose Kf hKf using fun j => (GlobalTheory.T.exists_principalLevel_subgroup_open D (D.sp.W j) Q.l.M).1`. Use `choose U dict mu x₀ hS using fun j σ => exists_pkgAll Q hQ hpq j σ (iota j) (hiota j) (Kf j) (hKf j) (chiW j σ) (fun hj hσ => ⟨(hchi j hj σ hσ).1, (hchi j hj σ hσ).2.1⟩)`.

Establish `hgood` using `(GlobalTheory.T.level_good_and_half_eq_prime_product D Q.H Q.l hQ.1.2.1 hM).1`. Establish `hB` using `fun j => GlobalTheory.T.algebraic_laws_moduli_scheme_good_level D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c (hpq j) hgood`. Establish `hF` using `fun j (hj : InR D j) => ((hB j).2.2.2.2.2 D.R.r (U j)).2.2 fun σ hσ => (hS j σ hj hσ).2.unf`. Establish `hL` using `fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) => GlobalTheory.T.finVol_and_exists_L2DefiniteCuspForms_of_pkgLaws D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c D.R.r (U j) σ (D.sp.W j) _ _ _ _ (dict j σ) (mu j σ) (x₀ j σ) (D.sp.W_sig j) hσ (hF j hj).2 (hS j σ hj hσ).2`. Set `T : CoreJ D` to `{ Q := Q, U := U, V := fun j _ => D.sp.W j, dict := dict, mu := mu, Kf := fun j _ => Kf j, pb := pb, cE := fun _ _ _ => 1, chiW := chiW, x₀ := x₀, iota := iota }`.

Establish `h0 : GoodEmb Q.c T.toCore.σ₀` using `T.toCore.good_σ₀`. Establish `hLM : LawsM T.toCore` using `{ pins := hQ half := ⟨hpb, hMb⟩ evalWD := fun j _ => (hB j).1 unf := fun j hj σ hσ => (hS j σ hj hσ).2.unf unTest := fun j hj σ hσ => (hS j σ hj hσ).2.unTest chiTriv := fun j hj σ hσ _ _ _ k γ _ => (hS j σ hj hσ).2.chi1 k _ γ dictU := fun j hj σ hσ => by`. Take `⟨g, e, F, ik, φ, th, h1, h2, -⟩` from `(hS j σ hj hσ).2.dictLaws`. Conclude with `⟨th, _, h1, h2⟩`. Use `spaceW := fun _ _ _ _ => rfl`.

Use `levelK := fun j _ _ _ => hM ▸ hKf j`. Use `xiAbs := fun j hj σ hσ => (hL j hj σ hσ).2.1`. Use `muUnit := fun j hj σ hσ => (hS j σ hj hσ).2.muUnit`. Use `muCont := fun j hj σ hσ => (hS j σ hj hσ).2.muCont`. Use `finVol := fun j hj σ hσ => (hL j hj σ hσ).1`.

Use `cuspFD := fun j hj => (hF j hj).1`. Use `supDef := fun j hj => (hF j hj).2`. Use `cuspidalL2Subspace := fun j hj σ hσ => (hL j hj σ hσ).2.2.choose`. Use `l2Def := fun j hj σ hσ => (hL j hj σ hσ).2.2.choose_spec`. Use `unitIndep := fun j _ => (hB j).2.1`.

Use `ptNe := fun j _ => (hB j).2.2.1 }`. Use `⟨T, ?_, ?_, rfl, rfl, HEq.rfl⟩` and prove the remaining obligations. Conclude with `{ toLawsM := hLM cUnit := fun _ _ _ _ _ => norm_one muVal := fun j hj σ hσ => (hS j σ hj hσ).2.muVal muConj := fun j hj σ hσ => (hchi j hj σ hσ).2.2 intAll := fun j _ => (hB j).2.2.2.1 modelW := fun j hj σ hσ => ⟨_, (hS j σ hj hσ).2.modelW⟩ familyUniformisationBasePointOrthogonal …`. Take `⟨g, e, F, ik, φ, th, h1, -, h3⟩` from `(hS j σ hj hσ).2.dictLaws`. Establish `hi` using `hiota j hj (D.sp.W_rank j hj.1 hj.2)`.

Use `⟨D.sp.W_rank j hj.1 hj.2, g, e, F, ik, φ, th, hi.emb, ⟨1, fun x y => ?_⟩, h1, h3⟩` and prove the remaining obligations. Rewrite using `[Units.val_one, Int.cast_one, one_mul]`. Conclude with `hi.isom x y }`. Conclude with `{ toLawsM := hLM cuspMul := fun j _ => ((hB j).2.2.2.2.2 D.R.r (U j)).2.1 latZ := fun j hj => ((hS j _ hj h0).2.expo _).1 cuNe := fun j hj k => by`. Take `⟨-, h1, h2, h3⟩` from `GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace D Q hQ j hj`.

Establish `hp : (T.toCore.X₀ j k).p0 = (Q.Dw j).q` using `(hS j _ hj h0).1 k`. Conclude with `GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt _ _ _ _ (by omega) (by omega) (by omega)`. Use `expo := fun j hj => hM ▸ ((hS j _ hj h0).2.expo _).2 }`.
-/
theorem exists_coreJ_noVol : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) → ∀ chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, (∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)) → ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.pb = pb ∧ T.Q = Q ∧ HEq T.chiW chiW := by
  intro D Q hQ hpq pb hpb hMb chiW hchi
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hQ.2.1.1
  choose iota hiota using exists_iotaAll Q hQ
  choose Kf hKf using fun j => (GlobalTheory.T.exists_principalLevel_subgroup_open D (D.sp.W j) Q.l.M).1
  choose U dict mu x₀ hS using fun j σ => exists_pkgAll Q hQ hpq j σ (iota j) (hiota j) (Kf j) (hKf j) (chiW j σ)
    (fun hj hσ => ⟨(hchi j hj σ hσ).1, (hchi j hj σ hσ).2.1⟩)
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D Q.H Q.l hQ.1.2.1 hM).1
  have hB := fun j => GlobalTheory.T.algebraic_laws_moduli_scheme_good_level D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c (hpq j) hgood
  have hF := fun j (hj : InR D j) => ((hB j).2.2.2.2.2 D.R.r (U j)).2.2 fun σ hσ => (hS j σ hj hσ).2.unf
  have hL := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.T.finVol_and_exists_L2DefiniteCuspForms_of_pkgLaws D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c D.R.r (U j) σ (D.sp.W j) _ _ _ _ (dict j σ) (mu j σ) (x₀ j σ)
      (D.sp.W_sig j) hσ (hF j hj).2 (hS j σ hj hσ).2
  let T : CoreJ D :=
    { Q := Q, U := U, V := fun j _ => D.sp.W j, dict := dict, mu := mu, Kf := fun j _ => Kf j, pb := pb,
      cE := fun _ _ _ => 1, chiW := chiW, x₀ := x₀, iota := iota }
  have h0 : GoodEmb Q.c T.toCore.σ₀ := T.toCore.good_σ₀
  have hLM : LawsM T.toCore :=
    { pins := hQ
      half := ⟨hpb, hMb⟩
      evalWD := fun j _ => (hB j).1
      unf := fun j hj σ hσ => (hS j σ hj hσ).2.unf
      unTest := fun j hj σ hσ => (hS j σ hj hσ).2.unTest
      chiTriv := fun j hj σ hσ _ _ _ k γ _ => (hS j σ hj hσ).2.chi1 k _ γ
      dictU := fun j hj σ hσ => by
        obtain ⟨g, e, F, ik, φ, th, h1, h2, -⟩ := (hS j σ hj hσ).2.dictLaws
        exact ⟨th, _, h1, h2⟩
      spaceW := fun _ _ _ _ => rfl
      levelK := fun j _ _ _ => hM ▸ hKf j
      xiAbs := fun j hj σ hσ => (hL j hj σ hσ).2.1
      muUnit := fun j hj σ hσ => (hS j σ hj hσ).2.muUnit
      muCont := fun j hj σ hσ => (hS j σ hj hσ).2.muCont
      finVol := fun j hj σ hσ => (hL j hj σ hσ).1
      cuspFD := fun j hj => (hF j hj).1
      supDef := fun j hj => (hF j hj).2
      cuspidalL2Subspace := fun j hj σ hσ => (hL j hj σ hσ).2.2.choose
      l2Def := fun j hj σ hσ => (hL j hj σ hσ).2.2.choose_spec
      unitIndep := fun j _ => (hB j).2.1
      ptNe := fun j _ => (hB j).2.2.1 }
  refine ⟨T, ?_, ?_, rfl, rfl, HEq.rfl⟩
  · exact
      { toLawsM := hLM
        cUnit := fun _ _ _ _ _ => norm_one
        muVal := fun j hj σ hσ => (hS j σ hj hσ).2.muVal
        muConj := fun j hj σ hσ => (hchi j hj σ hσ).2.2
        intAll := fun j _ => (hB j).2.2.2.1
        modelW := fun j hj σ hσ => ⟨_, (hS j σ hj hσ).2.modelW⟩
        familyUniformisationBasePointOrthogonal := fun j hj σ hσ => (hS j σ hj hσ).2.familyUniformisationBasePointOrthogonal
        kfHalf := fun j _ _ _ => (GlobalTheory.T.principalLevel_eq_halfMarking_stabilizer D Q.H Q.l (D.sp.W j)).2 (Kf j) (hKf j)
        adPin := fun j hj σ hσ => by
          obtain ⟨g, e, F, ik, φ, th, h1, -, h3⟩ := (hS j σ hj hσ).2.dictLaws
          have hi := hiota j hj (D.sp.W_rank j hj.1 hj.2)
          refine ⟨D.sp.W_rank j hj.1 hj.2, g, e, F, ik, φ, th, hi.emb, ⟨1, fun x y => ?_⟩, h1, h3⟩
          rw [Units.val_one, Int.cast_one, one_mul]
          exact hi.isom x y }
  · exact
      { toLawsM := hLM
        cuspMul := fun j _ => ((hB j).2.2.2.2.2 D.R.r (U j)).2.1
        latZ := fun j hj => ((hS j _ hj h0).2.expo _).1
        cuNe := fun j hj k => by
          obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace D Q hQ j hj
          have hp : (T.toCore.X₀ j k).p0 = (Q.Dw j).q := (hS j _ hj h0).1 k
          exact GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt _ _ _ _ (by omega) (by omega) (by omega)
        expo := fun j hj => hM ▸ ((hS j _ hj h0).2.expo _).2 }

end GlobalTheory.FinalJoin2
