import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseAdeleExtInfiniteFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryDenseClosureLocal

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.TailFix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `baseAdele_ext_infinite_finite ?_ fun w => ?_` and prove the remaining obligations. Conclude with `(idem_fst S).trans (GlobalTheory.FinPlaceDense.idemS_fst S).symm`. Conclude with `(evFin_idem S w).trans (GlobalTheory.FinPlaceDense.evFin_idemS S w).symm`.
-/
theorem idem_eq_idemS (S : Finset (Pl F)) : idem S = GlobalTheory.FinPlaceDense.idemS S := by
  classical
  refine baseAdele_ext_infinite_finite ?_ fun w => ?_
  · exact (idem_fst S).trans (GlobalTheory.FinPlaceDense.idemS_fst S).symm
  · exact (evFin_idem S w).trans (GlobalTheory.FinPlaceDense.evFin_idemS S w).symm

/- English proof (translation)
Establish `h` using `hz (1 - GlobalTheory.FinPlaceDense.idemFin F) (by show (1 : Af F) - (GlobalTheory.FinPlaceDense.idemFin F).2 = 0`. Simplify using `[GlobalTheory.FinPlaceDense.idemFin])`. Rewrite `h` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h.symm`.
-/
theorem idemFin_smul {z : AE F E} (hz : At (fun u : AF F => u.2) z) : GlobalTheory.FinPlaceDense.idemFin F • z = z := by
  have h := hz (1 - GlobalTheory.FinPlaceDense.idemFin F) (by
    show (1 : Af F) - (GlobalTheory.FinPlaceDense.idemFin F).2 = 0
    simp [GlobalTheory.FinPlaceDense.idemFin])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

/- English proof (translation)
Establish `h` using `GlobalTheory.FinPlaceDense.tendsto_idemS_smul (F := F) (E := E) z`. Rewrite `h` using `[idemFin_smul hz]`. Conclude with `h.congr fun S => by rw [idem_eq_idemS]`.
-/
theorem tendsto_idem_smul {z : AE F E} (hz : At (fun u : AF F => u.2) z) :
    Tendsto (fun S : Finset (Pl F) => idem S • z) atTop (𝓝 z) := by
  have h := GlobalTheory.FinPlaceDense.tendsto_idemS_smul (F := F) (E := E) z
  rw [idemFin_smul hz] at h
  exact h.congr fun S => by rw [idem_eq_idemS]

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Rewrite using `[spl, smul_sub, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem spl_eq (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) : spl e A = e • (A - 1) + 1 := by
  rw [spl, smul_sub, sub_smul, one_smul]; abel

/- English proof (translation)
Use `haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _`. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Establish `hz : At (fun u : AF F => u.2) ((A - 1) i j)` using `fun u hu => by`. Use `congrFun (congrFun (hA u hu) i) j` as an intermediate fact. Rewrite `this` using `[Matrix.smul_apply]`. Then use the resulting hypothesis.

Establish `h` using `(tendsto_idem_smul hz).add_const ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j)`. Rewrite `h` using `[Matrix.sub_apply, sub_add_cancel]`. Use `h.congr fun S => ?_` and prove the remaining obligations. Rewrite using `[spl_eq, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]`.
-/
theorem tendsto_spl {A : Matrix (Fin n) (Fin n) (AE F E)} (hA : At (fun u : AF F => u.2) (A - 1)) :
    Tendsto (fun S : Finset (Pl F) => spl (idem S) A) atTop (𝓝 A) := by
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hz : At (fun u : AF F => u.2) ((A - 1) i j) := fun u hu => by
    have := congrFun (congrFun (hA u hu) i) j
    rwa [Matrix.smul_apply] at this
  have h := (tendsto_idem_smul hz).add_const ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  rw [spl_eq, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]

/- English proof (translation)
Introduce `u hu`. Establish `e : mat g⁻¹ - 1 = -((mat g - 1) * mat g⁻¹)`. Rewrite using `[Matrix.sub_mul, mat_mul_inv', Matrix.one_mul, neg_sub]`. Rewrite using `[e, smul_neg, ← Matrix.smul_mul, hg u hu, Matrix.zero_mul, neg_zero]`.
-/
theorem at_inv {g : UA σ J} (hg : At (fun u : AF F => u.2) (mat g - 1)) : At (fun u : AF F => u.2) (mat g⁻¹ - 1) := by
  intro u hu
  have e : mat g⁻¹ - 1 = -((mat g - 1) * mat g⁻¹) := by
    rw [Matrix.sub_mul, mat_mul_inv', Matrix.one_mul, neg_sub]
  rw [e, smul_neg, ← Matrix.smul_mul, hg u hu, Matrix.zero_mul, neg_zero]

/- English proof (translation)
Rewrite using `[tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Use `Tendsto.prodMk_nhds ?_ ?_` and prove the remaining obligations. Conclude with `tendsto_spl hg`. Establish `h2` using `tendsto_spl (at_inv hg)`. Use `((MulOpposite.continuous_op.tendsto _).comp h2).congr fun S => ?_` and prove the remaining obligations.

Use `show MulOpposite.op (spl (idem S) (mat g⁻¹)) = MulOpposite.op (mat (splU (idem S) (idem_mul_self S) g)⁻¹)`. Rewrite using `[← map_inv, mat_splU]`.
-/
theorem tendsto_splU (g : UA σ J) (hg : At (fun u : AF F => u.2) (mat g - 1)) :
    Filter.Tendsto (fun S : Finset (Pl F) => splU (idem S) (idem_mul_self S) g) Filter.atTop (𝓝 g) := by
  rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine Tendsto.prodMk_nhds ?_ ?_
  · exact tendsto_spl hg
  · have h2 := tendsto_spl (at_inv hg)
    refine ((MulOpposite.continuous_op.tendsto _).comp h2).congr fun S => ?_
    show MulOpposite.op (spl (idem S) (mat g⁻¹)) = MulOpposite.op (mat (splU (idem S) (idem_mul_self S) g)⁻¹)
    rw [← map_inv, mat_splU]

end GlobalTheory.TailFix
