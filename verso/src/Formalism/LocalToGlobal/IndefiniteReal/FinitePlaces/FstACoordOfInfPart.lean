import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TendstoCut

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Filter Topology Classical
open scoped TensorProduct
open Formalism.IndefR.Datum

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adeles

variable {F : Type} [Field F] [NumberField F]

def sglS (A : Finset (HeightOneSpectrum (𝓞 F))) : Af F := ∑ v ∈ A, sglV v 1

/- English proof (translation)
Unfold `sglS`. Rewrite using `[map_sum]`. Establish `: ∀ v ∈ A, evalV F w (sglV v (1 : v.adicCompletion F)) = if w = v then 1 else 0`. Introduce `v _`. Distinguish the cases in `h : w = v`.

Substitute `h` using the available equality. Rewrite using `[sglV_same, if_pos rfl]`. Rewrite using `[sglV_ne v _ h, if_neg h]`. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_ite_eq]`.
-/
theorem evalV_sglS (A : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    evalV F w (sglS A) = if w ∈ A then 1 else 0 := by
  classical
  unfold sglS
  rw [map_sum]
  have : ∀ v ∈ A, evalV F w (sglV v (1 : v.adicCompletion F)) = if w = v then 1 else 0 := by
    intro v _
    by_cases h : w = v
    · subst h; rw [sglV_same, if_pos rfl]
    · rw [sglV_ne v _ h, if_neg h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]

def idemS (A : Finset (HeightOneSpectrum (𝓞 F))) : AF F := pairA F 0 (sglS A)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fstA_idemS (A : Finset (HeightOneSpectrum (𝓞 F))) : fstA F (idemS A) = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sndA_idemS (A : Finset (HeightOneSpectrum (𝓞 F))) : sndA F (idemS A) = sglS A := rfl

/- English proof (translation)
Apply `af_ext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[map_mul, evalV_sglS]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sglS_mul_self (A : Finset (HeightOneSpectrum (𝓞 F))) : sglS A * sglS A = sglS A := by
  apply af_ext; intro w
  rw [map_mul, evalV_sglS]
  split_ifs <;> simp

/- English proof (translation)
The claim follows from `Prod.ext (by show (0 : InfiniteAdeleRing F) * 0 = 0; rw [mul_zero]) (sglS_mul_self A)`.
-/
theorem idemS_idem (A : Finset (HeightOneSpectrum (𝓞 F))) : IsIdempotentElem (idemS A) :=
  Prod.ext (by show (0 : InfiniteAdeleRing F) * 0 = 0; rw [mul_zero]) (sglS_mul_self A)

/- English proof (translation)
The claim follows from `Prod.ext rfl (by show sglS ∅ = 0; simp [sglS])`.
-/
theorem idemS_empty : idemS (∅ : Finset (HeightOneSpectrum (𝓞 F))) = 0 :=
  Prod.ext rfl (by show sglS ∅ = 0; simp [sglS])

/- English proof (translation)
Use `Prod.ext (by show (0 : InfiniteAdeleRing F) = 0 + 0; rw [add_zero]) ?_` and prove the remaining obligations. Use `show sglS (insert v A) = sglS A + sglV v 1`. Unfold `sglS`. Rewrite using `[Finset.sum_insert hv, add_comm]`.
-/
theorem idemS_insert {A : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ A) :
    idemS (insert v A) = idemS A + sA v 1 := by
  refine Prod.ext (by show (0 : InfiniteAdeleRing F) = 0 + 0; rw [add_zero]) ?_
  show sglS (insert v A) = sglS A + sglV v 1
  unfold sglS
  rw [Finset.sum_insert hv, add_comm]

/- English proof (translation)
Use `Prod.ext (by show (0 : InfiniteAdeleRing F) * 0 = 0; rw [mul_zero]) ?_` and prove the remaining obligations. Use `show sglS A * sglV v 1 = 0`. Apply `af_ext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[map_mul, evalV_sglS, map_zero]`.

Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Rewrite using `[if_neg hv, zero_mul]`. Rewrite using `[sglV_ne v _ h, mul_zero]`.
-/
theorem idemS_mul_sA {A : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ A) :
    idemS A * sA v 1 = 0 := by
  refine Prod.ext (by show (0 : InfiniteAdeleRing F) * 0 = 0; rw [mul_zero]) ?_
  show sglS A * sglV v 1 = 0
  apply af_ext; intro w
  rw [map_mul, evalV_sglS, map_zero]
  by_cases h : w = v
  · subst h; rw [if_neg hv, zero_mul]
  · rw [sglV_ne v _ h, mul_zero]

/- English proof (translation)
Use `show sA v 1 * sA v 1 = sA v 1`. Rewrite using `[← map_mul, mul_one]`.
-/
theorem sA_idem (v : HeightOneSpectrum (𝓞 F)) : IsIdempotentElem (sA v (1 : v.adicCompletion F)) := by
  show sA v 1 * sA v 1 = sA v 1
  rw [← map_mul, mul_one]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qi11.tendsto_fin y`.
-/
theorem tendsto_fin (y : Af F) : Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 F)) => (1 - sglS A) * y) atTop (𝓝 0) :=
  _root_.UpperTheory.Reformulated.B.Qi11.tendsto_fin y

/- English proof (translation)
Establish `heq : ∀ A : Finset (HeightOneSpectrum (𝓞 F)), (1 - idemS A) * a = ((0 : InfiniteAdeleRing F), (1 - sglS A) * a.2)`. Introduce `A`. Use `Prod.ext ?_ rfl` and prove the remaining obligations. Establish `: a.1 = 0` using `ha`. Use `show (1 - 0) * a.1 = 0`.

Rewrite using `[this, mul_zero]`. Simplify using `only [heq]`. Conclude with `tendsto_const_nhds.prodMk_nhds (tendsto_fin a.2)`.
-/
theorem tendsto_AF (a : AF F) (ha : fstA F a = 0) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 F)) => (1 - idemS A) * a) atTop (𝓝 0) := by
  have heq : ∀ A : Finset (HeightOneSpectrum (𝓞 F)), (1 - idemS A) * a = ((0 : InfiniteAdeleRing F), (1 - sglS A) * a.2) := by
    intro A
    refine Prod.ext ?_ rfl
    have : a.1 = 0 := ha
    show (1 - 0) * a.1 = 0
    rw [this, mul_zero]
  simp only [heq]
  exact tendsto_const_nhds.prodMk_nhds (tendsto_fin a.2)

end Adeles

variable {D : D7}

/- English proof (translation)
Use `set c := fun i => (Algebra.TensorProduct.basis (AF D.host.F) b).repr z i`. Use `set bI := Algebra.TensorProduct.basis (Ainf D.host.F) b`. Establish `hz' : z = ∑ i, c i • ((1 : AF D.host.F) ⊗ₜ[D.host.F] b i)` using `by conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) b).sum_repr z]`. Simplify using `only [Algebra.TensorProduct.basis_apply, c]`. Establish `hinf : infPart D z = ∑ i, fstA D.host.F (c i) • bI i`.

Rewrite using `[hz', map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Use `show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (c i ⊗ₜ[D.host.F] b i) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul]`.

Both sides reduce to the same expression. Establish `h` using `bI.repr_sum_self (fun i => fstA D.host.F (c i))`. Rewrite `h` using `[← hinf, hz, map_zero]`. Conclude with `(congrFun h i).symm`.
-/
theorem fstA_coord_of_infPart {z : AE D} (hz : infPart D z = 0) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι D.host.F D.host.E) (i : ι) :
    fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) b).repr z i) = 0 := by
  set c := fun i => (Algebra.TensorProduct.basis (AF D.host.F) b).repr z i
  set bI := Algebra.TensorProduct.basis (Ainf D.host.F) b
  have hz' : z = ∑ i, c i • ((1 : AF D.host.F) ⊗ₜ[D.host.F] b i) := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply, c]
  have hinf : infPart D z = ∑ i, fstA D.host.F (c i) • bI i := by
    rw [hz', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (c i ⊗ₜ[D.host.F] b i) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have h := bI.repr_sum_self (fun i => fstA D.host.F (c i))
  rw [← hinf, hz, map_zero] at h
  exact (congrFun h i).symm

instance instIsModTopAE : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩

/- English proof (translation)
Set `b` to `Module.finBasis D.host.F D.host.E`. Set `bA` to `Algebra.TensorProduct.basis (AF D.host.F) b`. Establish `hz' : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)), algebraMap (AF D.host.F) (AE D) (1 - idemS A) * z = ∑ i, ((1 - idemS A) * bA.repr z i) • bA i`. Introduce `A`. Use `conv_lhs => rw [← bA.sum_repr z]`.

Rewrite using `[← Algebra.smul_def, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Establish `: ContinuousAdd (AE D)` using `IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)`. Establish `: ContinuousSMul (AF D.host.F) (AE D)` using `IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)`. Simplify using `only [hz']`.

Establish `: (0 : AE D) = ∑ i, (0 : AF D.host.F) • bA i` using `by simp`. Rewrite using `[this]`. Use `tendsto_finsetSum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(tendsto_AF _ (fstA_coord_of_infPart hz b i)).smul_const _`.
-/
theorem tendsto_AE (z : AE D) (hz : infPart D z = 0) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (1 - idemS A) * z) atTop (𝓝 0) := by
  classical
  let b := Module.finBasis D.host.F D.host.E
  let bA := Algebra.TensorProduct.basis (AF D.host.F) b
  have hz' : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)), algebraMap (AF D.host.F) (AE D) (1 - idemS A) * z =
      ∑ i, ((1 - idemS A) * bA.repr z i) • bA i := by
    intro A
    conv_lhs => rw [← bA.sum_repr z]
    rw [← Algebra.smul_def, Finset.smul_sum]
    simp only [smul_smul]
  have : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  simp only [hz']
  have : (0 : AE D) = ∑ i, (0 : AF D.host.F) • bA i := by simp
  rw [this]
  refine tendsto_finsetSum _ fun i _ => ?_
  exact (tendsto_AF _ (fstA_coord_of_infPart hz b i)).smul_const _

/- English proof (translation)
Establish `hemb : Topology.IsEmbedding (fun x : GA D V => (matHom V x : GL (Fin V.rank) (AE D)))` using `Topology.IsEmbedding.subtypeVal`. Use `hemb.tendsto_nhds_iff.2 ?_` and prove the remaining obligations. Use `Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_` and prove the remaining obligations. Simplify using `only [Function.comp_def, Units.embedProduct_apply]`. Use `Tendsto.prodMk_nhds ?_ ?_` and prove the remaining obligations.

Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Conclude with `h1 i j`. Use `(MulOpposite.continuous_op.tendsto _).comp ?_` and prove the remaining obligations. Establish `hinv : ∀ x : GA D V, ((matHom V x)⁻¹ : GL (Fin V.rank) (AE D)) = matHom V x⁻¹` using `fun x => (map_inv _ x).symm`. Simplify using `only [hinv]`.

Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Conclude with `h2 i j`.
-/
theorem tendsto_GA {V : HSp D} {ι : Type*} {l : Filter ι} (k : ι → GA D V) (g : GA D V)
    (h1 : ∀ i j, Tendsto (fun a => Formalism.L2.Theta.mt V (k a) i j) l (𝓝 (Formalism.L2.Theta.mt V g i j)))
    (h2 : ∀ i j, Tendsto (fun a => Formalism.L2.Theta.mt V (k a)⁻¹ i j) l (𝓝 (Formalism.L2.Theta.mt V g⁻¹ i j))) :
    Tendsto k l (𝓝 g) := by
  have hemb : Topology.IsEmbedding (fun x : GA D V => (matHom V x : GL (Fin V.rank) (AE D))) :=
    Topology.IsEmbedding.subtypeVal
  refine hemb.tendsto_nhds_iff.2 ?_
  refine Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_
  simp only [Function.comp_def, Units.embedProduct_apply]
  refine Tendsto.prodMk_nhds ?_ ?_
  · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    exact h1 i j
  · refine (MulOpposite.continuous_op.tendsto _).comp ?_
    have hinv : ∀ x : GA D V, ((matHom V x)⁻¹ : GL (Fin V.rank) (AE D)) = matHom V x⁻¹ := fun x => (map_inv _ x).symm
    simp only [hinv]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    exact h2 i j

/- English proof (translation)
Use function extensionality and compare the values at `w`. Establish `hc` using `hW.om_cont f₀ hf₀ w`. Establish `h` using `(hc.tendsto p).comp hk`. Establish `h' : Tendsto (fun _ : ι => f₀ w) l (𝓝 ((om p) f₀ w))`. Use `h.congr fun a => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, hfix a]`. Conclude with `(tendsto_nhds_unique tendsto_const_nhds h').symm`.
-/
theorem om_fix_of_tendsto {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {f₀ : WO S T → ℂ}
    (hf₀ : IsThetaFunO ψ S T f₀) {ι : Type*} {l : Filter ι} [l.NeBot] (k : ι → GA D S × GA D T)
    (p : GA D S × GA D T) (hk : Tendsto k l (𝓝 p)) (hfix : ∀ a, om (k a) f₀ = f₀) : om p f₀ = f₀ := by
  funext w
  have hc := hW.om_cont f₀ hf₀ w
  have h := (hc.tendsto p).comp hk
  have h' : Tendsto (fun _ : ι => f₀ w) l (𝓝 ((om p) f₀ w)) := by
    refine h.congr fun a => ?_
    simp only [Function.comp_apply, hfix a]
  exact (tendsto_nhds_unique tendsto_const_nhds h').symm

/- English proof (translation)
Establish `h1 : infHom V g = 1` using `hg`. Establish `h2` using `congrArg (fun x : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) h1`. Simplify using `only [Units.val_one] at h2`. Establish `h3 : infPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j` using `h2`. Rewrite using `[map_sub, h3]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`.
-/
theorem infPart_mt_sub_one {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    infPart D (Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = 0 := by
  have h1 : infHom V g = 1 := hg
  have h2 := congrArg (fun x : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) h1
  simp only [Units.val_one] at h2
  have h3 : infPart D (Formalism.L2.Theta.mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := h2
  rw [map_sub, h3]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

/- English proof (translation)
Establish `heq : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)), ((1 : Matrix (Fin n) (Fin n) (AE D)) + algebraMap (AF D.host.F) (AE D) (idemS A) • (M - 1)) i j = M i j + algebraMap (AF D.host.F) (AE D) (1 - idemS A) * ((1 : Matrix (Fin n) (Fin n) (AE D)) i j - M i j)`. Introduce `A`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : infPart D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j - M i j) = 0`.

Rewrite using `[← neg_sub, map_neg, hM i j, neg_zero]`. Establish `: ContinuousAdd (AE D)` using `IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)`. Simplify using `only [heq]`. Establish `h` using `(tendsto_const_nhds (x := M i j)).add (tendsto_AE _ hz)`. Simplify using `using h`.
-/
theorem tendsto_trunc_entry {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D))
    (hM : ∀ i j, infPart D (M i j - (1 : Matrix (Fin n) (Fin n) (AE D)) i j) = 0) (i j : Fin n) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      ((1 : Matrix (Fin n) (Fin n) (AE D)) + algebraMap (AF D.host.F) (AE D) (idemS A) • (M - 1)) i j) atTop
      (𝓝 (M i j)) := by
  have heq : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      ((1 : Matrix (Fin n) (Fin n) (AE D)) + algebraMap (AF D.host.F) (AE D) (idemS A) • (M - 1)) i j =
        M i j + algebraMap (AF D.host.F) (AE D) (1 - idemS A) * ((1 : Matrix (Fin n) (Fin n) (AE D)) i j - M i j) := by
    intro A
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_sub, map_one]
    ring
  have hz : infPart D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j - M i j) = 0 := by
    rw [← neg_sub, map_neg, hM i j, neg_zero]
  have : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  simp only [heq]
  have h := (tendsto_const_nhds (x := M i j)).add (tendsto_AE _ hz)
  simpa using h

/- English proof (translation)
Apply `tendsto_GA` to reduce the goal to its premises. Introduce `i j`. Simplify using `only [hk]`. Apply the tactic sequence `exact tendsto_trunc_entry _ (infPart_mt_sub_one hg) i j`. Introduce `i j`.

Simplify using `only [hk']`. Apply the tactic sequence `exact tendsto_trunc_entry _ (infPart_mt_sub_one (Subgroup.inv_mem _ hg)) i j`.
-/
theorem tendsto_trunc {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) (k : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V)
    (hk : ∀ A, Formalism.L2.Theta.mt V (k A) = 1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt V g - 1))
    (hk' : ∀ A, Formalism.L2.Theta.mt V (k A)⁻¹ =
      1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt V g⁻¹ - 1)) :
    Tendsto k atTop (𝓝 g) := by
  apply tendsto_GA
  · intro i j
    simp only [hk]
    exact tendsto_trunc_entry _ (infPart_mt_sub_one hg) i j
  · intro i j
    simp only [hk']
    exact tendsto_trunc_entry _ (infPart_mt_sub_one (Subgroup.inv_mem _ hg)) i j

/- English proof (translation)
The claim follows from `om_fix_of_tendsto hW hf₀ (fun A => (k A, k' A)) (g, h) ((tendsto_trunc hg k hk hki).prodMk_nhds (tendsto_trunc hh k' hk' hki')) hfix`.
-/
theorem om_fix_of_trunc {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {f₀ : WO S T → ℂ}
    (hf₀ : IsThetaFunO ψ S T f₀) {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T)
    (k : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D S) (k' : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D T)
    (hk : ∀ A, Formalism.L2.Theta.mt S (k A) = 1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt S g - 1))
    (hki : ∀ A, Formalism.L2.Theta.mt S (k A)⁻¹ =
      1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt S g⁻¹ - 1))
    (hk' : ∀ A, Formalism.L2.Theta.mt T (k' A) = 1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt T h - 1))
    (hki' : ∀ A, Formalism.L2.Theta.mt T (k' A)⁻¹ =
      1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt T h⁻¹ - 1))
    (hfix : ∀ A, om (k A, k' A) f₀ = f₀) : om (g, h) f₀ = f₀ :=
  om_fix_of_tendsto hW hf₀ (fun A => (k A, k' A)) (g, h)
    ((tendsto_trunc hg k hk hki).prodMk_nhds (tendsto_trunc hh k' hk' hki')) hfix

end Formalism.IndefR.Fin.LevelGroupLemmas

end
