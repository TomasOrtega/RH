import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.LevelHalf

open scoped Matrix nonZeroDivisors

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def conjEquiv (cm : CMData F E) : E ≃ₐ[F] E :=
  AlgEquiv.ofAlgHom cm.sig cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjEquiv_apply (cm : CMData F E) (x : E) : conjEquiv cm x = star x := rfl

def frameLat (V : HSpace E) : Submodule (𝓞 E) (Fin V.rank → E) :=
  V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 E))

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_frameLat (V : HSpace E) (v : Fin V.rank → E) :
    v ∈ frameLat V ↔ ∃ x ∈ V.L0, (fun i => V.frame.repr x i) = v := Iff.rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hT_eq (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ a, ∑ b, V.frame.repr y a * V.gram b a * star (V.frame.repr x b) := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, starRingEnd_apply,
    HSpace.gram]
  ring

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frameLat_fg (V : HSpace E) : (frameLat V).FG := V.standardTuple_isLattice.fg.map _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem frameLat_span (V : HSpace E) : Submodule.span E (frameLat V : Set (Fin V.rank → E)) = ⊤ := by
  have h : (frameLat V : Set (Fin V.rank → E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
  rw [h, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gram_herm (V : HSpace E) (a b : Fin V.rank) : star (V.gram b a) = V.gram a b :=
  LinearMap.isSymm_def.1 V.herm _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gram_det_ne (V : HSpace E) : V.gramᵀ.det ≠ 0 := by
  rw [Matrix.det_transpose]
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    rw [hT_eq, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul]
    have hb := congrFun h0 b
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hb
    have e : ∑ a, V.frame.repr (V.frame.equivFun.symm v) a * V.gram b a = 0 := by
      rw [← hb]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← V.frame.equivFun_apply, LinearEquiv.apply_symm_apply, mul_comm]
    rw [e, zero_mul]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 this

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem frameLat_dual (cm : CMData F E) (V : HSpace E) (v : Fin V.rank → E) :
    (∀ y ∈ frameLat V, (∑ a, ∑ b, v a * V.gramᵀ a b * conjEquiv cm (y b)) ∈
      (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔ v ∈ frameLat V := by
  obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
  have h1 : V.frame.equivFun x ∈ frameLat V ↔ x ∈ V.L0 := by
    constructor
    · rintro ⟨x', hx', e⟩
      have : x' = x := V.frame.equivFun.injective e
      exact this ▸ hx'
    · intro hx
      exact ⟨x, hx, rfl⟩
  have h2 : x ∈ V.L0 ↔ ∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 E) E) := by
    conv_lhs => rw [← V.baseLattice_isUnimodular]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
    rfl
  rw [h1, h2]
  constructor
  · intro h y hy
    have := h _ ⟨y, hy, rfl⟩
    rw [hT_eq]
    exact Submodule.mem_one.2 ((FractionalIdeal.mem_one_iff _).1 this)
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    rw [hT_eq] at this
    exact (FractionalIdeal.mem_one_iff _).2 (Submodule.mem_one.1 this)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermA_eq (cm : CMData F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA (conjEquiv cm) Jᵀ x y = (sigR (Af F) cm.sig ∘ y) ⬝ᵥ (JR (Af F) J *ᵥ x) := by
  unfold GlobalTheory.AdLat.hermA
  rw [Finset.sum_comm]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  change x a * ((1 : Af F) ⊗ₜ J b a) * sigR (Af F) cm.sig (y b) = sigR (Af F) cm.sig (y b) * (((1 : Af F) ⊗ₜ J b a) * x a)
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hermA_unitary (cm : CMData F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (GlobalTheory.AdLat.RA F E)) (hg : g ∈ HR (Af F) cm.sig J) (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA (conjEquiv cm) Jᵀ ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ y) = GlobalTheory.AdLat.hermA (conjEquiv cm) Jᵀ x y := by
  have h : Formalism.UG.cT (sigR (Af F) cm.sig) (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) * JR (Af F) J *
    (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) = JR (Af F) J := hg
  rw [hermA_eq, hermA_eq]
  have e : sigR (Af F) cm.sig ∘ ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ y) =
      ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)).map (sigR (Af F) cm.sig)) *ᵥ (sigR (Af F) cm.sig ∘ y) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  rw [e]
  conv_rhs => rw [← h]
  rw [Formalism.UG.cT, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose,
    dotProduct_comm, dotProduct_comm (_ ∘ y), Matrix.dotProduct_mulVec]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem bc_mem_HR (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') (g : GL (Fin n) (R ⊗[F] E)) (hg : g ∈ HR R σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom g ∈ HR R' σ J := by
  set ψ : R ⊗[F] E →+* R' ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom with hψ
  have h : Formalism.UG.cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * JR R J *
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = JR R J := hg
  have h1 : ∀ t, ψ (sigR R σ t) = sigR R' σ (ψ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [hψ, sigR]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : (JR R J).map ψ = JR R' J := by
    ext i j
    simp [hψ, JR, inclR]
  have h3 : (Formalism.UG.cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))).map ψ =
      Formalism.UG.cT (sigR R' σ) ((g : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map ψ) := by
    ext i j
    simp [Formalism.UG.cT, h1]
  have h4 := congrArg (fun m => m.map ψ) h
  simp only [Matrix.map_mul, h2, h3] at h4
  exact h4

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem latHat_eq (V : HSp D) :
    Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (frameLat V : Set (Fin V.rank → D.host.E)) := by
  unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, x, hx, rfl⟩

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem halfVec_mem (V : HSp D) (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : z ∈ Formalism.L2.Pj.latHat V) : halfVec V b z ∈ Formalism.L2.Pj.latHat V := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, V.L0.smul_mem b hx, ?_⟩
    funext i
    rw [← algebraMap_smul D.host.E b x, map_smul]
    simp [halfVec, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero =>
    have : halfVec V b 0 = 0 := by funext i; simp [halfVec]
    rw [this]; exact zero_mem _
  | add w w' _ _ h h' =>
    have : halfVec V b (w + w') = halfVec V b w + halfVec V b w' := by funext i; simp [halfVec, mul_add]
    rw [this]; exact add_mem h h'
  | neg w _ h =>
    have : halfVec V b (-w) = - halfVec V b w := by funext i; simp [halfVec]
    rw [this]; exact neg_mem h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finHom_mem (V : HSp D) (k : GA D V) : finHom V k ∈ HR (Af D.host.F) D.sp.cm.sig V.gram :=
  bc_mem_HR _ _ (sndA D.host.F) _ (show HR (AF D.host.F) D.sp.cm.sig V.gram from k).2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.
-/
theorem kfHalf_of_level (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H)
    (Kf : Subgroup (GA D V)) (hK : IsLevelK V l.M Kf) :
    KfHalf V Kf l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) := by
  intro k
  rw [hK k]
  refine and_congr_right fun _ => ⟨fun h b _ z hz => h _ (halfVec_mem V b z hz), fun h => ?_⟩
  rw [latHat_eq] at h ⊢
  refine GlobalTheory.AdLat.trivial_level_of_half D.host.F D.host.E V.rank (frameLat V) (conjEquiv D.sp.cm) V.gramᵀ 1
    (finHom V k) l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) l.Mb (frameLat_fg V) (frameLat_span V)
    (fun x => star_star x) (fun a b => gram_herm V a b) (gram_det_ne V) one_ne_zero (frameLat_dual D.sp.cm V)
    (hermA_unitary D.sp.cm V.gram _ (finHom_mem V k)) (lt_of_lt_of_le (by norm_num) l.three_le)
    (by rw [sup_comm]; exact l.coprime) (by rw [mul_comm]; exact l.prod)
    (fun b hb => ⟨H.bar b, Ideal.mem_map_of_mem _ hb, H.bar_eq b⟩) h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem kfHalf_record : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → KfHalf (D.sp.W j) Kf Q.l.M (Q.l.Mb.map (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) := by
  intro D Q hQ j Kf hK
  refine kfHalf_of_level _ Q.l Kf ?_
  rw [hQ.2.1.1]
  exact hK

end GlobalTheory.LevelHalf
