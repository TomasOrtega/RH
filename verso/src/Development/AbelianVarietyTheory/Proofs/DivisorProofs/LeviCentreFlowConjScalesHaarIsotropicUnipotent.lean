import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharSkewHermitianNormScaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousChartIsotropicUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviConjScalarIdeleUnipotentCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSmulOfCentralParabolicLeviStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section
namespace GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y h hJ hW b hb ν hν t f hf`. Take `⟨m, Z, J₀, hF⟩` from `GlobalTheory.SphEis.exists_fr_of_isotropic F E σ h n J hJ (r + 1) X Y hW.xx hW.yy hW.xy`. Take `⟨lv, hlv⟩` from `GlobalTheory.SphEis.exists_isLv F E σ n J (r + 1) m X Y Z J₀ hF`. Establish `hlaw` using `GlobalTheory.SphEis.crd_law F E σ n J (r + 1) m X Y Z J₀ hF lv hlv`. Establish `hmem` using `hb.mem t`.

Take `⟨l, hl⟩` from `GlobalTheory.T.exists_unit_smul_of_central_parabolicLevi F E σ n J r m X Y Z J₀ hF (b t) hmem (fun k hk => hb.comm t k hk)`. Choose the witnesses or unpack the hypotheses as in `⟨γ, hγ⟩ : ∃ γ : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J (b t)).1 * adMat F Y = adMat F Y * γ := by`. Establish `h1` using `hmem`. Simplify using `only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf] at h1`. Take `⟨B, -, e⟩` from `(h1 (Fin.last r) (Finset.mem_singleton_self _)).2`.

Conclude with `⟨B.1, e⟩`. Take `⟨δ, hδdet, hδJ, hconj⟩` from `GlobalTheory.T.leviConj_scalarIdele_unipotentCoordinates F E σ n J (r + 1) m X Y Z J₀ hF (b t) l γ hl hγ`. Establish `habs : ((absE F E l : ℝ≥0) : ℝ) ^ (r + 1) = Real.exp t`. Take `⟨β, hβ, hβt⟩` from `hb.onX t`. Establish `hL : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1`.

Rewrite using `[← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `e1 : adMat F X * β.1 = (l : AF F ⊗[F] E) • adMat F X` using `hβ.symm.trans hl`. Establish `hβ' : β.1 = (l : AF F ⊗[F] E) • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E))`. Establish `e2` using `congrArg (adMat F (cT (σ : E →+* E) Y * J) * ·) e1`. Simplify using `only [← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_smul] at e2`.

Rewrite using `[e2]`. Establish `hdet : Matrix.GeneralLinearGroup.det β = l ^ (r + 1)`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hβ', Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, Units.val_pow_eq_pow_val]`. Rewrite using `[← hβt, hdet, map_pow, NNReal.coe_pow]`.

Establish `hFD : FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Take `⟨eE⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`. Use `haveI : SecondCountableTopology (AF F ⊗[F] E) := eE.secondCountableTopology`. Use `haveI : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin m → AF F ⊗[F] E))`.

Use `haveI : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin m → AF F ⊗[F] E))`. Use `haveI : T2Space (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := inferInstanceAs (T2Space (Fin (r + 1) → Fin m → AF F ⊗[F] E))`. Use `letI : MeasurableSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := borel _`. Use `haveI : BorelSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → AF F ⊗[F] E))`.

Use `haveI : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → AF F ⊗[F] E))`. Use `letI : MeasurableSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := borel _`. Use `haveI : BorelSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := ⟨rfl⟩`. Establish `hsc : Continuous (sigR (AF F) σ)`. Establish `h0` using `IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)`.

Use `h0.congr fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y => simp [LinearMap.baseChange_tmul, sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Establish `hcT : ∀ {p q : ℕ}, Continuous fun M : Matrix (Fin p) (Fin q) (AF F ⊗[F] E) => cT (sigR (AF F) σ) M` using `fun {p q} => (continuous_id.matrix_map hsc).matrix_transpose`. Establish `hSk : IsClosed (skewA σ (r + 1) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)))` using `isClosed_eq (continuous_id.add hcT) continuous_const`. Use `haveI : LocallyCompactSpace (skewA σ (r + 1)) := hSk.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `hff` using `GlobalTheory.SphEis.frame_facts F E σ n J (r + 1) m X Y Z J₀ hF`. Use `haveI : LocallyCompactSpace (unipRad σ J X) := GlobalTheory.UAut.locallyCompact_unipRad h hJ hff.1`.

Use `haveI i1 : SecondCountableTopology (skewA σ (r + 1)) := TopologicalSpace.Subtype.secondCountableTopology (skewA σ (r + 1) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)))`. Establish `i2 : BorelSpace (skewA σ (r + 1))` using `inferInstance`. Establish `i3 : T2Space (skewA σ (r + 1))` using `inferInstance`. Establish `i4 : SecondCountableTopology (unipRad σ J X)` using `inferInstance`. Establish `i5 : BorelSpace (unipRad σ J X)` using `inferInstance`.

Establish `i6 : T2Space (unipRad σ J X)` using `inferInstance`. Establish `cTadd : ∀ {p q : ℕ} (M N : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)), cT (sigR (AF F) σ) (M + N) = cT (sigR (AF F) σ) M + cT (sigR (AF F) σ) N` using `fun M N => Matrix.ext fun i k => by simp [cT]`. Establish `cTsub : ∀ {p q : ℕ} (M N : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)), cT (sigR (AF F) σ) (M - N) = cT (sigR (AF F) σ) M - cT (sigR (AF F) σ) N` using `fun M N => Matrix.ext fun i k => by simp [cT]`. Establish `cTsmul : ∀ {p q : ℕ} (a : AF F ⊗[F] E) (M : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)), cT (sigR (AF F) σ) (a • M) = sigR (AF F) σ a • cT (sigR (AF F) σ) M` using `fun a M => Matrix.ext fun i k => by simp [cT]`. Establish `hJ0 : cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹` using `GlobalTheory.SphEis.UnipCrd.cT_inv_herm σ J₀ hF.herm₀`.

Establish `hpx : ∀ x y : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E), cT (sigR (AF F) σ) (x * GlobalTheory.SphEis.plus σ J₀ y) = y * GlobalTheory.SphEis.plus σ J₀ x` using `fun x y => by`. Simplify using `only [GlobalTheory.SphEis.plus, GlobalTheory.SphEis.crdLaw_cT_mul, GlobalTheory.SphEis.UnipCrd.cT_cT σ h, GlobalTheory.SphEis.UnipCrd.cT_adMat, hJ0, Matrix.mul_assoc]`. Use `set hf2 : AF F ⊗[F] E := inclR (F := F) (AF F) (2⁻¹ : E) with hhf2`. Establish `hh : hf2 + hf2 = 1`. Rewrite using `[hhf2, ← map_add, ← map_one (inclR (F := F) (AF F))]`.

Use `congr 1`. Evaluate the numerical expressions. Establish `hsh : sigR (AF F) σ hf2 = hf2`. Rewrite using `[hhf2]`. Simplify using `[sigR, inclR, map_ofNat]`.

Establish `hcond : ∀ (x : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) (s : skewA σ (r + 1)), ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) + cT (sigR (AF F) σ) ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * Globa …` using `fun x s => by`. Establish `hs : (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + cT (sigR (AF F) σ) s = 0` using `s.2`. Rewrite using `[cTsub, cTsmul, hsh, hpx]`. Rewrite using `[show (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x) + (cT (sigR (AF F) σ) s - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) + x * GlobalTheory.SphEis.plus σ J₀ x = ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + cT ( …`. Take `⟨φ, hφc, hφ⟩` from `GlobalTheory.T.exists_continuous_chart_isotropicUnipotentRadical F E σ n J (r + 1) m X Y Z J₀ hF`.

Establish `hφmem : ∀ p, φ p ∈ unipRad σ J X`. Introduce and unpack `⟨x, s⟩`. Take `⟨u, hu, hcu⟩` from `GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd F E σ n J (r + 1) m X Y Z J₀ hF x _ (hcond x s)`. Establish `e` using `(hlaw (φ (x, s)) u x _ 0 0 (hφ x s)).2.1 hcu`. Rewrite using `[e]`.

Conclude with `hu`. Set `βc : GAd σ J → Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)` to `fun u => adMat F (cT (σ : E →+* E) Y * J) * ((matHom _ σ J u).1 * adMat F Z)`. Set `κc : GAd σ J → Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)` to `fun u => adMat F (cT (σ : E →+* E) Y * J) * ((matHom _ σ J u).1 * adMat F Y)`. Establish `hβc : ∀ u x c, GlobalTheory.SphEis.Crd σ J X Y Z J₀ u x c → βc u = x` using `fun u x c hu => by`. Simplify using `only [βc]`.

Rewrite using `[hu.onZ, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hF.dz, hF.dc]`. Simplify using the standard rewrite rules. Establish `hκc : ∀ u x c, GlobalTheory.SphEis.Crd σ J X Y Z J₀ u x c → κc u = c` using `fun u x c hu => by`. Simplify using `only [κc]`. Rewrite using `[hu.onD]`.

Simplify using `only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc]`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hF.dd, hF.dz, hF.dc]`. Simplify using the standard rewrite rules. Establish `hβcont : Continuous βc` using `continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)`. Establish `hκcont : Continuous κc` using `continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)`.

Establish `hPcont : Continuous fun x : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) => x * GlobalTheory.SphEis.plus σ J₀ x` using `continuous_id.matrix_mul (continuous_const.matrix_mul hcT)`. Establish `hinvmem : ∀ u : unipRad σ J X, κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) ∈ skewA σ (r + 1)` using `fun u => by`. Take `⟨x, c, hc, hcc⟩` from `GlobalTheory.SphEis.exists_crd_of_mem_unipRad F E σ n J (r + 1) m X Y Z J₀ hF u u.2`. Rewrite using `[hβc _ _ _ hc, hκc _ _ _ hc, mem_skewA, cTadd, cTsmul, hsh, hpx]`. Rewrite using `[show c + hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x) + (cT (sigR (AF F) σ) c + hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) = (c + cT (sigR (AF F) σ) c + x * GlobalTheory.SphEis.plus σ J₀ x) + ((hf2 + hf2) - 1) • (x * GlobalTheory.SphEis.plus σ J₀ x) by rw [sub_smul, one_smul, a …`.

Establish `hinvc : Continuous fun u : unipRad σ J X => κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u))` using `(hκcont.comp continuous_subtype_val).add ((hPcont.comp (hβcont.comp continuous_subtype_val)).const_smul hf2)`. Set `Φ : Unit × (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) × skewA σ (r + 1)) ≃ₜ unipRad σ J X` to `{ toFun := fun p => ⟨φ p.2, hφmem p.2⟩ invFun := fun u => ((), (βc u, ⟨κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)), hinvmem u⟩)) left_inv := fun p => by`. Take `⟨⟨⟩, x, s⟩` from `p`. Establish `e1` using `hβc _ _ _ (hφ x s)`. Establish `e2` using `hκc _ _ _ (hφ x s)`.

Use `Prod.ext rfl (Prod.ext e1 (Subtype.ext ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `κc (φ (x, s)) + hf2 • (βc (φ (x, s)) * GlobalTheory.SphEis.plus σ J₀ (βc (φ (x, s)))) = s`. Rewrite using `[e1, e2, sub_add_cancel]`. Use `right_inv := fun u => by`. Take `⟨x, c, hc, -⟩` from `GlobalTheory.SphEis.exists_crd_of_mem_unipRad F E σ n J (r + 1) m X Y Z J₀ hF u u.2`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `hφ (βc u) ⟨_, hinvmem u⟩`. Establish `e3 : ((⟨_, hinvmem u⟩ : skewA σ (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - inclR (F` using `F) (AF F) (2⁻¹ : E) • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) = κc u := add_sub_cancel_right _ _`. Rewrite `h1` using `[e3]`. Establish `hu' : GlobalTheory.SphEis.Crd σ J X Y Z J₀ u (βc u) (κc u)`.

Rewrite using `[hβc _ _ _ hc, hκc _ _ _ hc]`. Conclude with `hc`. Express the relevant statement in the definitionally equal form `φ (βc u, ⟨_, hinvmem u⟩) = u`. Conclude with `(hlaw _ u _ _ 0 0 h1).2.1 hu'`. Use `continuous_toFun := Continuous.subtype_mk (hφc.comp continuous_snd) _`.

Use `continuous_invFun := continuous_const.prodMk ((hβcont.comp continuous_subtype_val).prodMk (hinvc.subtype_mk hinvmem)) }`. Establish `hplusc : Continuous (GlobalTheory.SphEis.plus σ J₀ : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) → _)` using `continuous_const.matrix_mul hcT`. Establish `hT : ∀ q' : unipRad σ J X, ∃ (l' : Unit) (f₁ : Unit → Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) (g₁ : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) → skewA σ (r + 1)), Continuous f₁ ∧ Continuous g₁ ∧ ∀ l a c, Φ (l, a, c) * q' = Φ (l * l', a + f₁ l, c + g₁ (l, a))`. Introduce `q'`. Take `⟨⟨⟨⟩, x', s'⟩, rfl⟩` from `Φ.surjective q'`.

Establish `hgmem : ∀ a : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E), hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ a - a * GlobalTheory.SphEis.plus σ J₀ x') ∈ skewA σ (r + 1)` using `fun a => by`. Rewrite using `[mem_skewA, cTsmul, hsh, cTsub, hpx, hpx, ← smul_add]`. Simplify using the standard rewrite rules. Establish `hgc : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) => hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ p.2 - p.2 * GlobalTheory.SphEis.plus σ J₀ x')` using `((continuous_const.matrix_mul (hplusc.comp continuous_snd)).sub (continuous_snd.matrix_mul continuous_const)).const_smul hf2`. Establish `hgc' : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) => (⟨_, hgmem p.2⟩ : skewA σ (r + 1))` using `hgc.subtype_mk _`.

Establish `hgc'' : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) => s' + (⟨_, hgmem p.2⟩ : skewA σ (r + 1))` using `continuous_const.add hgc'`. Use `⟨(), fun _ => x', fun p => s' + ⟨_, hgmem p.2⟩, continuous_const, hgc'', fun l a c => ?_⟩` and prove the remaining obligations. Take `⟨⟩` from `l`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `φ (a, c) * φ (x', s') = φ (a + x', c + (s' + ⟨_, hgmem a⟩))`.

Establish `h1` using `(hlaw _ _ a _ x' _ (hφ a c)).1 (hφ x' s')`. Establish `h2` using `hφ (a + x') (c + (s' + ⟨_, hgmem a⟩))`. Simplify using `only [← hhf2] at h1 h2`. Establish `hQ : a * GlobalTheory.SphEis.plus σ J₀ x' = hf2 • (a * GlobalTheory.SphEis.plus σ J₀ x') + hf2 • (a * GlobalTheory.SphEis.plus σ J₀ x')`. Rewrite using `[← add_smul, hh, one_smul]`.

Establish `hLR : ((c : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (a * GlobalTheory.SphEis.plus σ J₀ a)) + ((s' : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ x')) - a * GlobalTheory.SphEis.plus σ J₀ x' = (((c + (s' + ⟨_, hgmem …`. Rewrite using `[show (((c + (s' + ⟨_, hgmem a⟩) : skewA σ (r + 1))) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) =`. Use the proof step `(c : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + ((s' : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ a - a * GlobalTheory.SphEis.plus σ J₀ x')) from rfl]`. Rewrite using `[GlobalTheory.SphEis.crdLaw_plus_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]`. Use `conv_lhs => rw [hQ]`.

Simplify using `only [smul_add, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite `h2` using `[← hLR]`. Conclude with `(hlaw _ _ _ _ 0 0 h1).2.1 h2`. Establish `hconjmem : ∀ u ∈ unipRad σ J X, b t * u * (b t)⁻¹ ∈ unipRad σ J X` using `(GlobalTheory.ResidueEisenstein.frame_levi_facts F E σ n J r X Y h hJ hW).1 (b t) hmem`.

Set `α : unipRad σ J X →* unipRad σ J X` to `{ toFun := fun u => ⟨b t * u * (b t)⁻¹, hconjmem u u.2⟩ map_one' := Subtype.ext (by simp) map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }`. Establish `hαc : Continuous α` using `Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _`. Set `lI : GL (Fin (r + 1)) (AF F ⊗[F] E)` to `Units.map (Matrix.scalar (Fin (r + 1)) : AF F ⊗[F] E →+* Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)).toMonoidHom l`. Establish `hlI : (lI : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) = (l : AF F ⊗[F] E) • 1`. Simplify using `[lI, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]`.

Establish `hdetlI : Matrix.GeneralLinearGroup.det lI = l ^ (r + 1)`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hlI, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, Units.val_pow_eq_pow_val]`. Set `sA : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) →+ Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)` to `(GlobalTheory.ModuLR.lrCE lI δ).toAddEquiv.toAddMonoidHom`. Establish `hsA : ∀ a, sA a = (l : AF F ⊗[F] E) • (a * δ.1)` using `fun a => by`.

Express the relevant statement in the definitionally equal form `lI.1 * a * δ.1 = _`. Rewrite using `[hlI, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]`. Set `u2 : (AF F ⊗[F] E)ˣ` to `l * Units.map (sigR (AF F) σ).toMonoidHom l`. Establish `hu2 : (u2 : AF F ⊗[F] E) = (l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)` using `rfl`. Establish `hsu2 : sigR (AF F) σ (u2 : AF F ⊗[F] E) = u2`.

Rewrite using `[hu2, map_mul, GlobalTheory.SphEis.UnipCrd.sigR_invol σ h, mul_comm]`. Establish `hsu2' : sigR (AF F) σ ((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (u2⁻¹ : (AF F ⊗[F] E)ˣ)`. Use `Units.eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Use `conv_lhs => rw [← hsu2]`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.

Establish `hsk : ∀ a : AF F ⊗[F] E, sigR (AF F) σ a = a → ∀ s ∈ skewA σ (r + 1), a • s ∈ skewA σ (r + 1)` using `fun a ha s hs => by`. Rewrite using `[mem_skewA, cTsmul, ha, ← smul_add, (mem_skewA.1 hs), smul_zero]`. Set `Lc : skewA σ (r + 1) ≃ₜ+ skewA σ (r + 1)` to `{ toFun := fun s => ⟨(u2 : AF F ⊗[F] E) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)), hsk _ hsu2 _ s.2⟩ invFun := fun s => ⟨((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)), hsk _ hsu2' _ s.2⟩ left_inv := fun s => Subtyp …`. Set `sC : skewA σ (r + 1) →+ skewA σ (r + 1)` to `Lc.toAddEquiv.toAddMonoidHom`. Establish `hsC : ∀ s, (sC s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) = ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E))` using `fun s => rfl`.

Establish `hδJ' : ∀ M : Matrix (Fin m) (Fin (r + 1)) (AF F ⊗[F] E), δ.1 * (adMat F J₀⁻¹ * (cT (sigR (AF F) σ) δ.1 * M)) = adMat F J₀⁻¹ * M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hδJ]`. Establish `hαΦ : ∀ (l' : Unit) a c, α (Φ (l', a, c)) = Φ (l', sA a, sC c)`. Introduce `l' a c`. Take `⟨⟩` from `l'`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `b t * φ (a, c) * (b t)⁻¹ = φ (sA a, sC c)`. Establish `h1` using `hconj _ _ _ (hφ a c)`. Establish `h2` using `hφ (sA a) (sC c)`. Simplify using `only [← hhf2] at h1 h2`.

Establish `e3 : sA a * GlobalTheory.SphEis.plus σ J₀ (sA a) = ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (a * GlobalTheory.SphEis.plus σ J₀ a)`. Rewrite using `[hsA]`. Simplify using `only [GlobalTheory.SphEis.plus, cTsmul, GlobalTheory.SphEis.crdLaw_cT_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hδJ']`. Rewrite using `[mul_comm (sigR (AF F) σ (l : AF F ⊗[F] E))]`. Rewrite `h2` using `[e3, hsC]`.

Rewrite `h1` using `[← hsA]`. Rewrite `h1` using `[smul_sub, smul_comm ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) hf2]`. Conclude with `(hlaw _ _ _ _ 0 0 h1).2.1 h2`. Use `set kA : ℝ≥0 := (absE F E l ^ ((r + 1) * m))⁻¹ with hkA`. Use `set kC : ℝ≥0 := (absE F E l ^ ((r + 1) * (r + 1)))⁻¹ with hkC`.

Establish `hl0 : absE F E l ≠ 0` using `fun h0 => by`. Establish `e` using `map_mul (absE F E) l l⁻¹`. Rewrite `e` using `[mul_inv_cancel, map_one, h0, zero_mul]`. Conclude with `zero_ne_one e.symm`. Establish `hsA' : ∀ ν' : Measure (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)), ν'.IsAddHaarMeasure → ν'.map sA = kA • ν'`.

Introduce `ν' hν'`. Establish `e` using `addEquivAddHaarChar_smul_map ν' (GlobalTheory.ModuLR.lrCE lI δ)`. Rewrite `e` using `[GlobalTheory.T.addHaarChar_leftRight_matrixMul_adeleTensor F E σ h (r + 1) m lI δ, hdetlI, hδdet, one_pow, mul_one, map_pow, ← pow_mul]`. Express the relevant statement in the definitionally equal form `ν'.map (GlobalTheory.ModuLR.lrCE lI δ) = kA • ν'`. Use `conv_rhs => rw [← e]`.

Rewrite using `[smul_smul, hkA, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]`. Establish `hsC' : ∀ ν' : Measure (skewA σ (r + 1)), ν'.IsAddHaarMeasure → ν'.map sC = kC • ν'`. Introduce `ν' hν'`. Establish `e` using `addEquivAddHaarChar_smul_map ν' Lc`. Rewrite `e` using `[GlobalTheory.T.addHaarChar_skewHermitian_normScale F E σ h (r + 1) l Lc (fun s => rfl)]`.

Express the relevant statement in the definitionally equal form `ν'.map Lc = kC • ν'`. Use `conv_rhs => rw [← e]`. Rewrite using `[smul_smul, hkC, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]`. Establish `hmap` using `GlobalTheory.ModulusCoord.map_haar_eq_smul_of_coords (unipRad σ J X) Unit (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) (skewA σ (r + 1)) Φ hT α sA sC kA kC hαc (GlobalTheory.ModuLR.lrCE lI δ).continuous Lc.continuous hαΦ hsA' hsC' ν hν`. Establish `hfm : Measurable fun u : unipRad σ J X => f u` using `hf.comp measurable_subtype_coe`.

Establish `hk : ((kA * kC : ℝ≥0) : ℝ) = Real.exp (-(((n : ℝ) - (r + 1)) * t))`. Establish `hn : (n : ℝ) = m + 2 * (r + 1)` using `by exact_mod_cast hF.dim.symm`. Rewrite using `[hkA, hkC, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_pow, pow_mul, pow_mul, habs, hn, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem modulus_conj_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ b, IsFlowJ σ J X Y b → ∀ ν : Measure (unipRad σ J X), ν.IsHaarMeasure → ∀ (t : ℝ) (f : GAd σ J → ℝ≥0∞), Measurable f → ∫⁻ u : unipRad σ J X, f (b t * u * (b t)⁻¹) ∂ν = ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * t))) * ∫⁻ u : unipRad σ J X, f u ∂ν := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW b hb ν hν t f hf
  classical
  obtain ⟨m, Z, J₀, hF⟩ := GlobalTheory.SphEis.exists_fr_of_isotropic F E σ h n J hJ (r + 1) X Y hW.xx hW.yy hW.xy
  obtain ⟨lv, hlv⟩ := GlobalTheory.SphEis.exists_isLv F E σ n J (r + 1) m X Y Z J₀ hF
  have hlaw := GlobalTheory.SphEis.crd_law F E σ n J (r + 1) m X Y Z J₀ hF lv hlv
  have hmem := hb.mem t
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_unit_smul_of_central_parabolicLevi F E σ n J r m X Y Z J₀ hF (b t) hmem (fun k hk => hb.comm t k hk)
  obtain ⟨γ, hγ⟩ : ∃ γ : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E),
      (matHom _ σ J (b t)).1 * adMat F Y = adMat F Y * γ := by
    have h1 := hmem
    simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf] at h1
    obtain ⟨B, -, e⟩ := (h1 (Fin.last r) (Finset.mem_singleton_self _)).2
    exact ⟨B.1, e⟩
  obtain ⟨δ, hδdet, hδJ, hconj⟩ := GlobalTheory.T.leviConj_scalarIdele_unipotentCoordinates F E σ n J (r + 1) m X Y Z J₀ hF (b t) l γ hl hγ
  have habs : ((absE F E l : ℝ≥0) : ℝ) ^ (r + 1) = Real.exp t := by
    obtain ⟨β, hβ, hβt⟩ := hb.onX t
    have hL : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
      rw [← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
    have e1 : adMat F X * β.1 = (l : AF F ⊗[F] E) • adMat F X := hβ.symm.trans hl
    have hβ' : β.1 = (l : AF F ⊗[F] E) • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := by
      have e2 := congrArg (adMat F (cT (σ : E →+* E) Y * J) * ·) e1
      simp only [← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_smul] at e2
      rw [e2]
    have hdet : Matrix.GeneralLinearGroup.det β = l ^ (r + 1) := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hβ', Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
        Units.val_pow_eq_pow_val]
    rw [← hβt, hdet, map_pow, NNReal.coe_pow]

  have hFD : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨eE⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AF F ⊗[F] E) := eE.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin m → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin m → AF F ⊗[F] E))
  haveI : T2Space (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin (r + 1) → Fin m → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := ⟨rfl⟩
  have hsc : Continuous (sigR (AF F) σ) := by
    have h0 := IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)
    refine h0.congr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcT : ∀ {p q : ℕ}, Continuous fun M : Matrix (Fin p) (Fin q) (AF F ⊗[F] E) => cT (sigR (AF F) σ) M :=
    fun {p q} => (continuous_id.matrix_map hsc).matrix_transpose
  have hSk : IsClosed (skewA σ (r + 1) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E))) :=
    isClosed_eq (continuous_id.add hcT) continuous_const
  haveI : LocallyCompactSpace (skewA σ (r + 1)) := hSk.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hff := GlobalTheory.SphEis.frame_facts F E σ n J (r + 1) m X Y Z J₀ hF
  haveI : LocallyCompactSpace (unipRad σ J X) := GlobalTheory.UAut.locallyCompact_unipRad h hJ hff.1
  haveI i1 : SecondCountableTopology (skewA σ (r + 1)) :=
    TopologicalSpace.Subtype.secondCountableTopology (skewA σ (r + 1) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)))
  have i2 : BorelSpace (skewA σ (r + 1)) := inferInstance
  have i3 : T2Space (skewA σ (r + 1)) := inferInstance
  have i4 : SecondCountableTopology (unipRad σ J X) := inferInstance
  have i5 : BorelSpace (unipRad σ J X) := inferInstance
  have i6 : T2Space (unipRad σ J X) := inferInstance

  have cTadd : ∀ {p q : ℕ} (M N : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) (M + N) = cT (sigR (AF F) σ) M + cT (sigR (AF F) σ) N := fun M N => Matrix.ext fun i k => by simp [cT]
  have cTsub : ∀ {p q : ℕ} (M N : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) (M - N) = cT (sigR (AF F) σ) M - cT (sigR (AF F) σ) N := fun M N => Matrix.ext fun i k => by simp [cT]
  have cTsmul : ∀ {p q : ℕ} (a : AF F ⊗[F] E) (M : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) (a • M) = sigR (AF F) σ a • cT (sigR (AF F) σ) M := fun a M => Matrix.ext fun i k => by simp [cT]
  have hJ0 : cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := GlobalTheory.SphEis.UnipCrd.cT_inv_herm σ J₀ hF.herm₀
  have hpx : ∀ x y : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E),
      cT (sigR (AF F) σ) (x * GlobalTheory.SphEis.plus σ J₀ y) = y * GlobalTheory.SphEis.plus σ J₀ x := fun x y => by
    simp only [GlobalTheory.SphEis.plus, GlobalTheory.SphEis.crdLaw_cT_mul, GlobalTheory.SphEis.UnipCrd.cT_cT σ h, GlobalTheory.SphEis.UnipCrd.cT_adMat, hJ0,
      Matrix.mul_assoc]
  set hf2 : AF F ⊗[F] E := inclR (F := F) (AF F) (2⁻¹ : E) with hhf2
  have hh : hf2 + hf2 = 1 := by
    rw [hhf2, ← map_add, ← map_one (inclR (F := F) (AF F))]; congr 1; norm_num
  have hsh : sigR (AF F) σ hf2 = hf2 := by
    rw [hhf2]; simp [sigR, inclR, map_ofNat]
  have hcond : ∀ (x : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) (s : skewA σ (r + 1)),
      ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) +
        cT (sigR (AF F) σ) ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) +
        x * GlobalTheory.SphEis.plus σ J₀ x = 0 := fun x s => by
    have hs : (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + cT (sigR (AF F) σ) s = 0 := s.2
    rw [cTsub, cTsmul, hsh, hpx]
    rw [show (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x) +
        (cT (sigR (AF F) σ) s - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) + x * GlobalTheory.SphEis.plus σ J₀ x =
        ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + cT (sigR (AF F) σ) s) +
          (1 - (hf2 + hf2)) • (x * GlobalTheory.SphEis.plus σ J₀ x) by rw [sub_smul, one_smul, add_smul]; abel, hs, hh, sub_self, zero_smul, add_zero]

  obtain ⟨φ, hφc, hφ⟩ := GlobalTheory.T.exists_continuous_chart_isotropicUnipotentRadical F E σ n J (r + 1) m X Y Z J₀ hF
  have hφmem : ∀ p, φ p ∈ unipRad σ J X := by
    rintro ⟨x, s⟩
    obtain ⟨u, hu, hcu⟩ := GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd F E σ n J (r + 1) m X Y Z J₀ hF x _ (hcond x s)
    have e := (hlaw (φ (x, s)) u x _ 0 0 (hφ x s)).2.1 hcu
    rw [e]
    exact hu
  let βc : GAd σ J → Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) := fun u =>
    adMat F (cT (σ : E →+* E) Y * J) * ((matHom _ σ J u).1 * adMat F Z)
  let κc : GAd σ J → Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E) := fun u =>
    adMat F (cT (σ : E →+* E) Y * J) * ((matHom _ σ J u).1 * adMat F Y)
  have hβc : ∀ u x c, GlobalTheory.SphEis.Crd σ J X Y Z J₀ u x c → βc u = x := fun u x c hu => by
    simp only [βc]
    rw [hu.onZ, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hF.dz, hF.dc]
    simp
  have hκc : ∀ u x c, GlobalTheory.SphEis.Crd σ J X Y Z J₀ u x c → κc u = c := fun u x c hu => by
    simp only [κc]
    rw [hu.onD]
    simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hF.dd, hF.dz, hF.dc]
    simp
  have hβcont : Continuous βc := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  have hκcont : Continuous κc := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  have hPcont : Continuous fun x : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) => x * GlobalTheory.SphEis.plus σ J₀ x :=
    continuous_id.matrix_mul (continuous_const.matrix_mul hcT)
  have hinvmem : ∀ u : unipRad σ J X, κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) ∈ skewA σ (r + 1) := fun u => by
    obtain ⟨x, c, hc, hcc⟩ := GlobalTheory.SphEis.exists_crd_of_mem_unipRad F E σ n J (r + 1) m X Y Z J₀ hF u u.2
    rw [hβc _ _ _ hc, hκc _ _ _ hc, mem_skewA, cTadd, cTsmul, hsh, hpx]
    rw [show c + hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x) + (cT (sigR (AF F) σ) c + hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) =
        (c + cT (sigR (AF F) σ) c + x * GlobalTheory.SphEis.plus σ J₀ x) + ((hf2 + hf2) - 1) • (x * GlobalTheory.SphEis.plus σ J₀ x) by rw [sub_smul, one_smul, add_smul]; abel,
      hcc, hh, sub_self, zero_smul, add_zero]
  have hinvc : Continuous fun u : unipRad σ J X => κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) :=
    (hκcont.comp continuous_subtype_val).add ((hPcont.comp (hβcont.comp continuous_subtype_val)).const_smul hf2)
  let Φ : Unit × (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) × skewA σ (r + 1)) ≃ₜ unipRad σ J X :=
    { toFun := fun p => ⟨φ p.2, hφmem p.2⟩
      invFun := fun u => ((), (βc u, ⟨κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)), hinvmem u⟩))
      left_inv := fun p => by
        obtain ⟨⟨⟩, x, s⟩ := p
        have e1 := hβc _ _ _ (hφ x s)
        have e2 := hκc _ _ _ (hφ x s)
        refine Prod.ext rfl (Prod.ext e1 (Subtype.ext ?_))
        change κc (φ (x, s)) + hf2 • (βc (φ (x, s)) * GlobalTheory.SphEis.plus σ J₀ (βc (φ (x, s)))) = s
        rw [e1, e2, sub_add_cancel]
      right_inv := fun u => by
        obtain ⟨x, c, hc, -⟩ := GlobalTheory.SphEis.exists_crd_of_mem_unipRad F E σ n J (r + 1) m X Y Z J₀ hF u u.2
        apply Subtype.ext
        have h1 := hφ (βc u) ⟨_, hinvmem u⟩
        have e3 : ((⟨_, hinvmem u⟩ : skewA σ (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) -
            inclR (F := F) (AF F) (2⁻¹ : E) • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) = κc u := add_sub_cancel_right _ _
        rw [e3] at h1
        have hu' : GlobalTheory.SphEis.Crd σ J X Y Z J₀ u (βc u) (κc u) := by
          rw [hβc _ _ _ hc, hκc _ _ _ hc]; exact hc
        change φ (βc u, ⟨_, hinvmem u⟩) = u
        exact (hlaw _ u _ _ 0 0 h1).2.1 hu'
      continuous_toFun := Continuous.subtype_mk (hφc.comp continuous_snd) _
      continuous_invFun := continuous_const.prodMk ((hβcont.comp continuous_subtype_val).prodMk
        (hinvc.subtype_mk hinvmem)) }

  have hplusc : Continuous (GlobalTheory.SphEis.plus σ J₀ : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) → _) :=
    continuous_const.matrix_mul hcT

  have hT : ∀ q' : unipRad σ J X, ∃ (l' : Unit) (f₁ : Unit → Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E))
      (g₁ : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) → skewA σ (r + 1)), Continuous f₁ ∧ Continuous g₁ ∧
      ∀ l a c, Φ (l, a, c) * q' = Φ (l * l', a + f₁ l, c + g₁ (l, a)) := by
    intro q'
    obtain ⟨⟨⟨⟩, x', s'⟩, rfl⟩ := Φ.surjective q'
    have hgmem : ∀ a : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E),
        hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ a - a * GlobalTheory.SphEis.plus σ J₀ x') ∈ skewA σ (r + 1) := fun a => by
      rw [mem_skewA, cTsmul, hsh, cTsub, hpx, hpx, ← smul_add]
      simp
    have hgc : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) =>
        hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ p.2 - p.2 * GlobalTheory.SphEis.plus σ J₀ x') :=
      ((continuous_const.matrix_mul (hplusc.comp continuous_snd)).sub (continuous_snd.matrix_mul continuous_const)).const_smul hf2
    have hgc' : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) =>
        (⟨_, hgmem p.2⟩ : skewA σ (r + 1)) := hgc.subtype_mk _
    have hgc'' : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) =>
        s' + (⟨_, hgmem p.2⟩ : skewA σ (r + 1)) := continuous_const.add hgc'
    refine ⟨(), fun _ => x', fun p => s' + ⟨_, hgmem p.2⟩, continuous_const, hgc'', fun l a c => ?_⟩
    obtain ⟨⟩ := l
    apply Subtype.ext
    change φ (a, c) * φ (x', s') = φ (a + x', c + (s' + ⟨_, hgmem a⟩))
    have h1 := (hlaw _ _ a _ x' _ (hφ a c)).1 (hφ x' s')
    have h2 := hφ (a + x') (c + (s' + ⟨_, hgmem a⟩))
    simp only [← hhf2] at h1 h2
    have hQ : a * GlobalTheory.SphEis.plus σ J₀ x' = hf2 • (a * GlobalTheory.SphEis.plus σ J₀ x') + hf2 • (a * GlobalTheory.SphEis.plus σ J₀ x') := by
      rw [← add_smul, hh, one_smul]
    have hLR : ((c : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (a * GlobalTheory.SphEis.plus σ J₀ a)) +
        ((s' : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ x')) - a * GlobalTheory.SphEis.plus σ J₀ x' =
        (((c + (s' + ⟨_, hgmem a⟩) : skewA σ (r + 1))) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) -
          hf2 • ((a + x') * GlobalTheory.SphEis.plus σ J₀ (a + x')) := by
      rw [show (((c + (s' + ⟨_, hgmem a⟩) : skewA σ (r + 1))) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) =
      (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + ((s' : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) +
        hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ a - a * GlobalTheory.SphEis.plus σ J₀ x')) from rfl]
      rw [GlobalTheory.SphEis.crdLaw_plus_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      conv_lhs => rw [hQ]
      simp only [smul_add, smul_sub]
      abel
    rw [← hLR] at h2
    exact (hlaw _ _ _ _ 0 0 h1).2.1 h2

  have hconjmem : ∀ u ∈ unipRad σ J X, b t * u * (b t)⁻¹ ∈ unipRad σ J X :=
    (GlobalTheory.ResidueEisenstein.frame_levi_facts F E σ n J r X Y h hJ hW).1 (b t) hmem
  let α : unipRad σ J X →* unipRad σ J X :=
    { toFun := fun u => ⟨b t * u * (b t)⁻¹, hconjmem u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hαc : Continuous α :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

  let lI : GL (Fin (r + 1)) (AF F ⊗[F] E) :=
    Units.map (Matrix.scalar (Fin (r + 1)) : AF F ⊗[F] E →+* Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)).toMonoidHom l
  have hlI : (lI : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) = (l : AF F ⊗[F] E) • 1 := by
    simp [lI, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hdetlI : Matrix.GeneralLinearGroup.det lI = l ^ (r + 1) := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hlI, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
      Units.val_pow_eq_pow_val]
  let sA : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) →+ Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) :=
    (GlobalTheory.ModuLR.lrCE lI δ).toAddEquiv.toAddMonoidHom
  have hsA : ∀ a, sA a = (l : AF F ⊗[F] E) • (a * δ.1) := fun a => by
    change lI.1 * a * δ.1 = _
    rw [hlI, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  let u2 : (AF F ⊗[F] E)ˣ := l * Units.map (sigR (AF F) σ).toMonoidHom l
  have hu2 : (u2 : AF F ⊗[F] E) = (l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E) := rfl
  have hsu2 : sigR (AF F) σ (u2 : AF F ⊗[F] E) = u2 := by
    rw [hu2, map_mul, GlobalTheory.SphEis.UnipCrd.sigR_invol σ h, mul_comm]
  have hsu2' : sigR (AF F) σ ((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (u2⁻¹ : (AF F ⊗[F] E)ˣ) := by
    refine Units.eq_inv_of_mul_eq_one_left ?_
    conv_lhs => rw [← hsu2]
    rw [← map_mul, Units.mul_inv, map_one]
  have hsk : ∀ a : AF F ⊗[F] E, sigR (AF F) σ a = a → ∀ s ∈ skewA σ (r + 1), a • s ∈ skewA σ (r + 1) := fun a ha s hs => by
    rw [mem_skewA, cTsmul, ha, ← smul_add, (mem_skewA.1 hs), smul_zero]
  let Lc : skewA σ (r + 1) ≃ₜ+ skewA σ (r + 1) :=
    { toFun := fun s => ⟨(u2 : AF F ⊗[F] E) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)), hsk _ hsu2 _ s.2⟩
      invFun := fun s => ⟨((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)),
        hsk _ hsu2' _ s.2⟩
      left_inv := fun s => Subtype.ext (by simp [smul_smul])
      right_inv := fun s => Subtype.ext (by simp [smul_smul])
      map_add' := fun s s' => Subtype.ext (by simp [smul_add])
      continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.const_smul (u2 : AF F ⊗[F] E)) _
      continuous_invFun := Continuous.subtype_mk
        (continuous_subtype_val.const_smul (((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E))) _ }
  let sC : skewA σ (r + 1) →+ skewA σ (r + 1) := Lc.toAddEquiv.toAddMonoidHom
  have hsC : ∀ s, (sC s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) =
      ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) :=
    fun s => rfl
  have hδJ' : ∀ M : Matrix (Fin m) (Fin (r + 1)) (AF F ⊗[F] E),
      δ.1 * (adMat F J₀⁻¹ * (cT (sigR (AF F) σ) δ.1 * M)) = adMat F J₀⁻¹ * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hδJ]
  have hαΦ : ∀ (l' : Unit) a c, α (Φ (l', a, c)) = Φ (l', sA a, sC c) := by
    intro l' a c
    obtain ⟨⟩ := l'
    apply Subtype.ext
    change b t * φ (a, c) * (b t)⁻¹ = φ (sA a, sC c)
    have h1 := hconj _ _ _ (hφ a c)
    have h2 := hφ (sA a) (sC c)
    simp only [← hhf2] at h1 h2
    have e3 : sA a * GlobalTheory.SphEis.plus σ J₀ (sA a) =
        ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (a * GlobalTheory.SphEis.plus σ J₀ a) := by
      rw [hsA]
      simp only [GlobalTheory.SphEis.plus, cTsmul, GlobalTheory.SphEis.crdLaw_cT_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_assoc, hδJ']
      rw [mul_comm (sigR (AF F) σ (l : AF F ⊗[F] E))]
    rw [e3, hsC] at h2
    rw [← hsA] at h1
    rw [smul_sub, smul_comm ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) hf2] at h1
    exact (hlaw _ _ _ _ 0 0 h1).2.1 h2

  set kA : ℝ≥0 := (absE F E l ^ ((r + 1) * m))⁻¹ with hkA
  set kC : ℝ≥0 := (absE F E l ^ ((r + 1) * (r + 1)))⁻¹ with hkC
  have hl0 : absE F E l ≠ 0 := fun h0 => by
    have e := map_mul (absE F E) l l⁻¹
    rw [mul_inv_cancel, map_one, h0, zero_mul] at e
    exact zero_ne_one e.symm
  have hsA' : ∀ ν' : Measure (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)), ν'.IsAddHaarMeasure → ν'.map sA = kA • ν' := by
    intro ν' hν'
    have e := addEquivAddHaarChar_smul_map ν' (GlobalTheory.ModuLR.lrCE lI δ)
    rw [GlobalTheory.T.addHaarChar_leftRight_matrixMul_adeleTensor F E σ h (r + 1) m lI δ, hdetlI, hδdet, one_pow, mul_one, map_pow, ← pow_mul] at e
    change ν'.map (GlobalTheory.ModuLR.lrCE lI δ) = kA • ν'
    conv_rhs => rw [← e]
    rw [smul_smul, hkA, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  have hsC' : ∀ ν' : Measure (skewA σ (r + 1)), ν'.IsAddHaarMeasure → ν'.map sC = kC • ν' := by
    intro ν' hν'
    have e := addEquivAddHaarChar_smul_map ν' Lc
    rw [GlobalTheory.T.addHaarChar_skewHermitian_normScale F E σ h (r + 1) l Lc (fun s => rfl)] at e
    change ν'.map Lc = kC • ν'
    conv_rhs => rw [← e]
    rw [smul_smul, hkC, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  have hmap := GlobalTheory.ModulusCoord.map_haar_eq_smul_of_coords (unipRad σ J X) Unit
    (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) (skewA σ (r + 1)) Φ hT α sA sC kA kC hαc
    (GlobalTheory.ModuLR.lrCE lI δ).continuous Lc.continuous hαΦ hsA' hsC' ν hν
  have hfm : Measurable fun u : unipRad σ J X => f u := hf.comp measurable_subtype_coe
  have hk : ((kA * kC : ℝ≥0) : ℝ) = Real.exp (-(((n : ℝ) - (r + 1)) * t)) := by
    have hn : (n : ℝ) = m + 2 * (r + 1) := by exact_mod_cast hF.dim.symm
    rw [hkA, hkC, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_pow, pow_mul, pow_mul, habs, hn,
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc ∫⁻ u, f (b t * u * (b t)⁻¹) ∂ν = ∫⁻ u, (fun v : unipRad σ J X => f v) (α u) ∂ν := rfl
    _ = ∫⁻ v, f v ∂(ν.map α) := (lintegral_map hfm hαc.measurable).symm
    _ = ∫⁻ v, f v ∂((kA * kC) • ν) := by rw [hmap]
    _ = ((kA * kC : ℝ≥0) : ℝ≥0∞) * ∫⁻ v, f v ∂ν := by rw [lintegral_smul_measure]; rfl
    _ = _ := by rw [← hk, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.ResidueEisenstein.ModConj
