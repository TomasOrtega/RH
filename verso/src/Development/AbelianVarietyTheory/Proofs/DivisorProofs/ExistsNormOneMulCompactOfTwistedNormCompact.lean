import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import GroundTheory.GlobalFields.LocalAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedArtinianInvolutionIdempotentSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinMatrixReducedOfCharpolySeparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPreimageQuadraticMapNoNullVectorsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.Tw.NormOneCore

/- English proof (translation)
Introduce `K _ _ _ hK n δ hδ C hC`. Establish `hu` using `hδ.1`. Use `set N := GlobalTheory.Tw.nrm δ with hNdef`. Use `set A := Algebra.adjoin K {N} with hAdef`. Use `letI : CommRing A := Algebra.adjoinCommRingOfComm K (by`.

Introduce `a ha b hb`. Rewrite using `[Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb])`. Establish `hA` using `GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hu`. Establish `hmul` using `GlobalTheory.Tw.CentralizerAdjoin.adj_mul' hu`. Establish `hsemi` using `GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ`.

Establish `hone` using `GlobalTheory.Tw.CentralizerAdjoin.adj_one' hu`. Establish `hadd : ∀ x y : Matrix (Fin n) (Fin n) K, GlobalTheory.Tw.adj δ (x + y) = GlobalTheory.Tw.adj δ x + GlobalTheory.Tw.adj δ y` using `fun x y => by simpa using hsemi 1 x y`. Establish `hzero : GlobalTheory.Tw.adj δ 0 = 0` using `by simp [GlobalTheory.Tw.adj]`. Set `σ : A →+* A` to `{ toFun := fun x => ⟨GlobalTheory.Tw.adj δ x, (hA x x.2).1⟩ map_one' := Subtype.ext hone map_mul' := fun x y => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `GlobalTheory.Tw.adj δ (x.1 * y.1) = _`. Rewrite using `[hmul]`. Conclude with `congrArg Subtype.val (mul_comm (⟨_, (hA y y.2).1⟩ : A) ⟨_, (hA x x.2).1⟩)`. Use the proof step `map_zero' := Subtype.ext hzero`. Use the proof step `map_add' := fun x y => Subtype.ext (hadd x.1 y.1) }`.

Establish `hσv : ∀ x : A, (σ x : Matrix (Fin n) (Fin n) K) = GlobalTheory.Tw.adj δ x` using `fun x => rfl`. Establish `hσσ : ∀ x : A, σ (σ x) = x` using `fun x => Subtype.ext (hA x x.2).2`. Use `haveI : IsReduced A := ⟨fun x ⟨m, hm⟩ => Subtype.ext (GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable K n N hδ.2 x x.2 m (by simpa using congrArg Subtype.val hm))⟩`. Use `haveI : IsArtinianRing A := IsArtinianRing.of_finite K A`. Take `⟨e, f, he, hf, hes, hsum, hnull⟩` from `GlobalTheory.T.reduced_artinian_involution_idempotent_split A σ hσσ`.

Establish `hse : σ e * f = 0`. Establish `h1 : σ e * σ e = σ e` using `by rw [← map_mul, he.eq]`. Establish `: f = 1 - e - σ e` using `by rw [← hsum]; ring`. Rewrite using `[this]`. Take the linear combination `(-1 : A) * h1 + (-1 : A) * hes`.

Establish `hef : e * f = 0`. Establish `: f = 1 - e - σ e` using `by rw [← hsum]; ring`. Rewrite using `[this]`. Take the linear combination `-he.eq - hes`. Establish `hσf : σ f = f`.

Establish `h` using `congrArg σ hsum`. Rewrite `h` using `[map_add, map_add, hσσ, map_one]`. Take the linear combination `h - hsum`. Use `letI : ContinuousStar K := ⟨(Isometry.of_dist_eq fun x y => by`. Rewrite using `[dist_eq_norm, dist_eq_norm, ← star_sub, hK]).continuous⟩`.

Establish `hqc : Continuous fun w : Matrix (Fin n) (Fin n) K => w * GlobalTheory.Tw.adj δ w`. Unfold `GlobalTheory.Tw.adj`. Use `fun_prop`. Establish `hss : σ e * σ e = σ e` using `by rw [← map_mul, he.eq]`. Set `S : Submodule K (Matrix (Fin n) (Fin n) K)` to `Submodule.map (LinearMap.mulRight K (f : Matrix (Fin n) (Fin n) K)) (Subalgebra.toSubmodule A)`.

Establish `hhom : ∀ (c : K) (w : Matrix (Fin n) (Fin n) K), (c • w) * GlobalTheory.Tw.adj δ (c • w) = (c * star c) • (w * GlobalTheory.Tw.adj δ w)`. Introduce `c w`. Establish `: GlobalTheory.Tw.adj δ (c • w) = star c • GlobalTheory.Tw.adj δ w` using `by simpa [hzero] using hsemi c w 0`. Rewrite using `[this, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Establish `hnullS : ∀ w ∈ S, w * GlobalTheory.Tw.adj δ w = 0 → w = 0`.

Introduce `w hw h0`. Take `⟨a, ha, rfl⟩` from `Submodule.mem_map.mp hw`. Establish `hx : (⟨a, ha⟩ * f : A) * σ (⟨a, ha⟩ * f) = 0` using `Subtype.ext h0`. Establish `h1` using `hnull _ hx`. Rewrite `h1` using `[mul_assoc, hf.eq]`.

Conclude with `congrArg Subtype.val h1`. Take `⟨B1, hB1, hB1m⟩` from `GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * u) '' C) (hC.image (continuous_const.mul Units.continuous_val))`. Take `⟨B2, hB2, hB2m⟩` from `GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) '' C) (hC.image (continuous_const.mul (Uni …`. Set `φ : GL (Fin n) K × Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K × (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ` to `fun p => ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * p.1 + p.2.1, MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + p.2.2))`. Establish `hφ : Continuous φ` using `((continuous_const.add (continuous_const.mul (Units.continuous_val.comp continuous_fst))).add (continuous_fst.comp continuous_snd)).prodMk (MulOpposite.continuous_op.comp ((continuous_const.add (continuous_const.mul ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K)).comp …`.

Use `⟨Units.embedProduct _ ⁻¹' (φ '' (C ×ˢ (B1 ×ˢ B2))), Units.isClosedEmbedding_embedProduct.isCompact_preimage ((hC.prod (hB1.prod hB2)).image hφ), ?_⟩` and prove the remaining obligations. Introduce `z hz u hu' huz`. Establish `hzi : ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ A`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Algebra.adjoin_le (Set.singleton_subset_iff.mpr hz) (GlobalTheory.Tw.CentralizerAdjoin.inv_mem_adjoin_of_isUnit z.isUnit)`.

Use `set z' : A := ⟨z, hz⟩ with hz'`. Use `set zi : A := ⟨_, hzi⟩ with hzi'`. Establish `hz1 : z' * zi = 1` using `Subtype.ext (Units.mul_inv z)`. Establish `hsz1 : σ z' * σ zi = 1` using `by rw [← map_mul, hz1, map_one]`. Use `set tA : A := e * z' + σ e * σ zi + f with htA`.

Use `set tiA : A := e * zi + σ e * σ z' + f with htiA`. Establish `hprod : tA * tiA = 1`. Rewrite using `[htA, htiA]`. Take the linear combination `(z' * zi) * he.eq + e * hz1 + (z' * σ z' + σ zi * zi) * hes + (z' + zi) * hef + (σ zi * σ z') * hss + σ e * hsz1 + (σ zi + σ z') * hse + hf.eq + hsum`. Establish `hprod' : tiA * tA = 1` using `by rw [mul_comm]; exact hprod`.

Establish `hσt : σ tA = tiA`. Rewrite using `[htA, htiA]`. Simplify using `only [map_add, map_mul, hσσ, hσf]`. Expand and normalize the polynomial expressions, which then agree. Set `t : GL (Fin n) K` to `⟨tA, tiA, congrArg Subtype.val hprod, congrArg Subtype.val hprod'⟩`.

Establish `hinvu : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * σ zi : A) : Matrix (Fin n) (Fin n) K)`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[huz]`. Conclude with `congrArg Subtype.val (show (z' * σ z') * (zi * σ zi) = 1 by`. Take the linear combination `(σ z' * σ zi) * hz1 + hsz1)`.

Use `⟨t, tA.2, ?_, t⁻¹ * z, ?_, by simp⟩` and prove the remaining obligations. Use `show (tA : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ tA = 1`. Rewrite using `[← hσv, hσt]`. Conclude with `congrArg Subtype.val hprod`. Use `⟨(u, (z : Matrix (Fin n) (Fin n) K) * f, ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f), ⟨hu', hB1m _ (Submodule.mem_map.mpr ⟨z, hz, rfl⟩) ⟨u, hu', ?_⟩, hB2m _ (Submodule.mem_map.mpr ⟨_, hzi, rfl⟩) ⟨u, hu', ?_⟩⟩, ?_⟩` and prove the remaining obligations.

Use `show (f : Matrix (Fin n) (Fin n) K) * u = ((z' * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (z' * f) : A) : Matrix (Fin n) (Fin n) K)`. Rewrite using `[huz]`. Conclude with `congrArg Subtype.val (show f * (z' * σ z') = (z' * f) * σ (z' * f) by`. Rewrite using `[map_mul, hσf]`. Take the linear combination `(-(z' * σ z')) * hf.eq)`.

Use `show (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (zi * f) : A) : Matrix (Fin n) (Fin n) K)`. Rewrite using `[hinvu]`. Conclude with `congrArg Subtype.val (show f * (zi * σ zi) = (zi * f) * σ (zi * f) by`. Rewrite using `[map_mul, hσf]`. Take the linear combination `(-(zi * σ zi)) * hf.eq)`.

Apply `Prod.ext` to reduce the goal to its premises. Use `show (e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K) + (z : Matrix (Fin n) (Fin n) K) * f = ((t⁻¹ * z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`. Rewrite using `[huz]`. Conclude with `congrArg Subtype.val (show e + σ e * (z' * σ z') + z' * f = tiA * z' by`. Rewrite using `[htiA]`.

Take the linear combination `(-e) * hz1)`. Use `show MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f) = MulOpposite.op (((t⁻¹ * z)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`. Rewrite using `[hinvu, _root_.mul_inv_rev, inv_inv, Units.val_mul]`. Conclude with `congrArg MulOpposite.op (congrArg Subtype.val (show e + σ e * (zi * σ zi) + zi * f = zi * tA by`. Rewrite using `[htA]`.

Take the linear combination `(-e) * hz1))`.
-/
theorem exists_normOne_mul_compact : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) K), GlobalTheory.Tw.Reg δ → ∀ C : Set (GL (Fin n) K), IsCompact C → ∃ D : Set (GL (Fin n) K), IsCompact D ∧ ∀ z : GL (Fin n) K, (z : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} → ∀ u ∈ C, (u : Matrix (Fin n) (Fin n) K) = (z : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (z : Matrix (Fin n) (Fin n) K) → ∃ t : GL (Fin n) K, (t : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} ∧ (t : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (t : Matrix (Fin n) (Fin n) K) = 1 ∧ ∃ d ∈ D, z = t * d := by
  intro K _ _ _ hK n δ hδ C hC
  have hu := hδ.1
  set N := GlobalTheory.Tw.nrm δ with hNdef
  set A := Algebra.adjoin K {N} with hAdef
  letI : CommRing A := Algebra.adjoinCommRingOfComm K (by
    intro a ha b hb; rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb])
  have hA := GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hu
  have hmul := GlobalTheory.Tw.CentralizerAdjoin.adj_mul' hu
  have hsemi := GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ
  have hone := GlobalTheory.Tw.CentralizerAdjoin.adj_one' hu
  have hadd : ∀ x y : Matrix (Fin n) (Fin n) K, GlobalTheory.Tw.adj δ (x + y) = GlobalTheory.Tw.adj δ x + GlobalTheory.Tw.adj δ y :=
    fun x y => by simpa using hsemi 1 x y
  have hzero : GlobalTheory.Tw.adj δ 0 = 0 := by simp [GlobalTheory.Tw.adj]
  let σ : A →+* A :=
    { toFun := fun x => ⟨GlobalTheory.Tw.adj δ x, (hA x x.2).1⟩
      map_one' := Subtype.ext hone
      map_mul' := fun x y => by
        apply Subtype.ext
        change GlobalTheory.Tw.adj δ (x.1 * y.1) = _
        rw [hmul]
        exact congrArg Subtype.val (mul_comm (⟨_, (hA y y.2).1⟩ : A) ⟨_, (hA x x.2).1⟩)
      map_zero' := Subtype.ext hzero
      map_add' := fun x y => Subtype.ext (hadd x.1 y.1) }
  have hσv : ∀ x : A, (σ x : Matrix (Fin n) (Fin n) K) = GlobalTheory.Tw.adj δ x := fun x => rfl
  have hσσ : ∀ x : A, σ (σ x) = x := fun x => Subtype.ext (hA x x.2).2
  haveI : IsReduced A := ⟨fun x ⟨m, hm⟩ => Subtype.ext
    (GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable K n N hδ.2 x x.2 m (by simpa using congrArg Subtype.val hm))⟩
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨e, f, he, hf, hes, hsum, hnull⟩ := GlobalTheory.T.reduced_artinian_involution_idempotent_split A σ hσσ

  have hse : σ e * f = 0 := by
    have h1 : σ e * σ e = σ e := by rw [← map_mul, he.eq]
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination (-1 : A) * h1 + (-1 : A) * hes
  have hef : e * f = 0 := by
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination -he.eq - hes
  have hσf : σ f = f := by
    have h := congrArg σ hsum
    rw [map_add, map_add, hσσ, map_one] at h
    linear_combination h - hsum
  letI : ContinuousStar K := ⟨(Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, hK]).continuous⟩
  have hqc : Continuous fun w : Matrix (Fin n) (Fin n) K => w * GlobalTheory.Tw.adj δ w := by
    unfold GlobalTheory.Tw.adj
    fun_prop
  have hss : σ e * σ e = σ e := by rw [← map_mul, he.eq]
  let S : Submodule K (Matrix (Fin n) (Fin n) K) :=
    Submodule.map (LinearMap.mulRight K (f : Matrix (Fin n) (Fin n) K)) (Subalgebra.toSubmodule A)
  have hhom : ∀ (c : K) (w : Matrix (Fin n) (Fin n) K),
      (c • w) * GlobalTheory.Tw.adj δ (c • w) = (c * star c) • (w * GlobalTheory.Tw.adj δ w) := by
    intro c w
    have : GlobalTheory.Tw.adj δ (c • w) = star c • GlobalTheory.Tw.adj δ w := by simpa [hzero] using hsemi c w 0
    rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hnullS : ∀ w ∈ S, w * GlobalTheory.Tw.adj δ w = 0 → w = 0 := by
    intro w hw h0
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hw
    have hx : (⟨a, ha⟩ * f : A) * σ (⟨a, ha⟩ * f) = 0 := Subtype.ext h0
    have h1 := hnull _ hx
    rw [mul_assoc, hf.eq] at h1
    exact congrArg Subtype.val h1
  obtain ⟨B1, hB1, hB1m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * u) '' C)
    (hC.image (continuous_const.mul Units.continuous_val))
  obtain ⟨B2, hB2, hB2m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) '' C)
    (hC.image (continuous_const.mul (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K))))
  let φ : GL (Fin n) K × Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K →
      Matrix (Fin n) (Fin n) K × (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ := fun p =>
    ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * p.1 + p.2.1,
      MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + p.2.2))
  have hφ : Continuous φ :=
    ((continuous_const.add (continuous_const.mul (Units.continuous_val.comp continuous_fst))).add
      (continuous_fst.comp continuous_snd)).prodMk
      (MulOpposite.continuous_op.comp ((continuous_const.add
        (continuous_const.mul ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K)).comp continuous_fst))).add
          (continuous_snd.comp continuous_snd)))
  refine ⟨Units.embedProduct _ ⁻¹' (φ '' (C ×ˢ (B1 ×ˢ B2))),
    Units.isClosedEmbedding_embedProduct.isCompact_preimage ((hC.prod (hB1.prod hB2)).image hφ), ?_⟩
  intro z hz u hu' huz
  have hzi : ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ A := by
    rw [Matrix.coe_units_inv]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hz) (GlobalTheory.Tw.CentralizerAdjoin.inv_mem_adjoin_of_isUnit z.isUnit)
  set z' : A := ⟨z, hz⟩ with hz'
  set zi : A := ⟨_, hzi⟩ with hzi'
  have hz1 : z' * zi = 1 := Subtype.ext (Units.mul_inv z)
  have hsz1 : σ z' * σ zi = 1 := by rw [← map_mul, hz1, map_one]
  set tA : A := e * z' + σ e * σ zi + f with htA
  set tiA : A := e * zi + σ e * σ z' + f with htiA
  have hprod : tA * tiA = 1 := by
    rw [htA, htiA]
    linear_combination (z' * zi) * he.eq + e * hz1 + (z' * σ z' + σ zi * zi) * hes + (z' + zi) * hef +
      (σ zi * σ z') * hss + σ e * hsz1 + (σ zi + σ z') * hse + hf.eq + hsum
  have hprod' : tiA * tA = 1 := by rw [mul_comm]; exact hprod
  have hσt : σ tA = tiA := by
    rw [htA, htiA]; simp only [map_add, map_mul, hσσ, hσf]; ring
  let t : GL (Fin n) K := ⟨tA, tiA, congrArg Subtype.val hprod, congrArg Subtype.val hprod'⟩
  have hinvu : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * σ zi : A) : Matrix (Fin n) (Fin n) K) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [huz]
    exact congrArg Subtype.val (show (z' * σ z') * (zi * σ zi) = 1 by
      linear_combination (σ z' * σ zi) * hz1 + hsz1)
  refine ⟨t, tA.2, ?_, t⁻¹ * z, ?_, by simp⟩
  · show (tA : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ tA = 1
    rw [← hσv, hσt]; exact congrArg Subtype.val hprod
  refine ⟨(u, (z : Matrix (Fin n) (Fin n) K) * f, ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f),
    ⟨hu', hB1m _ (Submodule.mem_map.mpr ⟨z, hz, rfl⟩) ⟨u, hu', ?_⟩,
      hB2m _ (Submodule.mem_map.mpr ⟨_, hzi, rfl⟩) ⟨u, hu', ?_⟩⟩, ?_⟩
  · show (f : Matrix (Fin n) (Fin n) K) * u = ((z' * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (z' * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [huz]
    exact congrArg Subtype.val (show f * (z' * σ z') = (z' * f) * σ (z' * f) by
      rw [map_mul, hσf]; linear_combination (-(z' * σ z')) * hf.eq)
  · show (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (zi * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [hinvu]
    exact congrArg Subtype.val (show f * (zi * σ zi) = (zi * f) * σ (zi * f) by
      rw [map_mul, hσf]; linear_combination (-(zi * σ zi)) * hf.eq)
  · apply Prod.ext
    · show (e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K) + (z : Matrix (Fin n) (Fin n) K) * f = ((t⁻¹ * z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [huz]
      exact congrArg Subtype.val (show e + σ e * (z' * σ z') + z' * f = tiA * z' by
        rw [htiA]; linear_combination (-e) * hz1)
    · show MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f) = MulOpposite.op (((t⁻¹ * z)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [hinvu, _root_.mul_inv_rev, inv_inv, Units.val_mul]
      exact congrArg MulOpposite.op (congrArg Subtype.val (show e + σ e * (zi * σ zi) + zi * f = zi * tA by
        rw [htA]; linear_combination (-e) * hz1))
end GlobalTheory.Tw.NormOneCore
