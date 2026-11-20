import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CoreExists
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet

noncomputable section

namespace GlobalTheory.LevelSubgroup

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def latCo (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem latHat_eq (V : HSp D) :
    latHat V = GlobalTheory.AdLat.hat D.host.F (latCo V : Set (Fin V.rank → D.host.E)) := by
  unfold latHat GlobalTheory.AdLat.hat
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, x, hx, rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latCo_fg (V : HSp D) : (latCo V).FG := V.standardTuple_isLattice.fg.map _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem latCo_span (V : HSp D) :
    Submodule.span D.host.E (latCo V : Set (Fin V.rank → D.host.E)) = ⊤ := by
  have h := V.standardTuple_isLattice.span_eq_top
  have : (latCo V : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
  rw [this, Submodule.span_image, h, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem gram_det_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have h0 : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    have : V.hT.flip (V.frame.equivFun.symm v) = 0 := by
      refine V.frame.ext fun i => ?_
      have := congrFun hm i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
      simp only [LinearMap.flip_apply, Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul,
        LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
      exact mul_comm (v j) _
    exact congrArg (fun f => f x) this
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

def conjEquiv (D : D7) : D.host.E ≃ₐ[D.host.F] D.host.E :=
  AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.
-/
theorem det_norm_one_gen {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (τ : B → B) (φ : A →+* B)
    (hφ : ∀ x, τ (φ x) = φ (σ x)) (J g : Matrix (Fin n) (Fin n) A) (hJ : IsUnit J.det)
    (h : Formalism.UG.cT σ g * J * g = J) : (g.map φ).det * τ (g.map φ).det = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose] at h1
  have h2 : (g.map σ).det = σ g.det := (RingHom.map_det _ _).symm
  have h5 : (g.map φ).det = φ g.det := (RingHom.map_det _ _).symm
  rw [h2] at h1
  have h4 : g.det * σ g.det = 1 := by
    apply hJ.mul_left_cancel
    linear_combination h1
  rw [h5, hφ, ← map_mul, h4, map_one]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem sg_fin {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (x : AF F ⊗[F] E) :
    GlobalTheory.AdLat.sg (Af F) c ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x) =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (sigR (AF F) (c : E →ₐ[F] E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isUnit_det_JR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (h : J.det ≠ 0) : IsUnit (JR (F := F) (AF F) J).det := by
  have h3 : (JR (F := F) (AF F) J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ _).symm
  rw [h3]
  exact (Ne.isUnit h).map _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem det_norm_one (V : HSp D) (k : GA D V) :
    (finHom V k).1.det * GlobalTheory.AdLat.sg (Af D.host.F) (conjEquiv D) (finHom V k).1.det = 1 :=
  det_norm_one_gen (sigR (AF D.host.F) D.sp.cm.sig) (GlobalTheory.AdLat.sg (Af D.host.F) (conjEquiv D)) _
    (sg_fin (conjEquiv D)) (JR (AF D.host.F) V.gram) (matHom V k).1 (isUnit_det_JR _ (gram_det_ne_zero V)) k.2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mulVec_mem {V : HSp D} {N : ℕ} {k : GA D V} (hk : k ∈ levSet V N) :
    ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V := by
  intro z hz
  obtain ⟨y, hy, h⟩ := hk.2 z hz
  rw [eq_add_of_sub_eq h]
  exact add_mem (nsmul_mem hy N) hz

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem inv_mulVec_mem {V : HSp D} {k : GA D V} (hk : ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V) :
    ∀ z ∈ latHat V, (finHom V k⁻¹).1 *ᵥ z ∈ latHat V := by
  rw [map_inv]
  rw [latHat_eq] at hk ⊢
  exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latCo V) (finHom V k) (conjEquiv D)
    (latCo_fg V) (latCo_span V) hk (det_norm_one V k)

def levSub (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := levSet V N
  one_mem' := ⟨one_mem _, fun z _ => ⟨0, zero_mem _, by simp⟩⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨mul_mem ha.1 hb.1, fun z hz => ?_⟩
    obtain ⟨y, hy, h⟩ := hb.2 z hz
    obtain ⟨y', hy', h'⟩ := ha.2 _ (mulVec_mem hb z hz)
    refine ⟨y' + y, add_mem hy' hy, ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← h, ← h']
    abel
  inv_mem' := by
    intro a ha
    refine ⟨inv_mem ha.1, fun z hz => ?_⟩
    obtain ⟨y, hy, h⟩ := ha.2 _ (inv_mulVec_mem (mulVec_mem ha) z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h
    rw [neg_nsmul, ← h]
    abel

def finSign (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : AF F ⊗[F] E :=
  pairA F 1 (-1) ⊗ₜ 1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem finSign_sq (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    finSign F E * finSign F E = 1 := by
  rw [finSign, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def, mul_one]
  congr 1
  exact Prod.ext (mul_one (1 : Ainf F)) (neg_mul_neg (1 : Af F) 1 |>.trans (mul_one _))

def finSignGL (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n : ℕ) : GL (Fin n) (AF F ⊗[F] E) :=
  ⟨finSign F E • 1, finSign F E • 1, by rw [smul_mul_smul_comm, finSign_sq, mul_one, one_smul],
    by rw [smul_mul_smul_comm, finSign_sq, mul_one, one_smul]⟩

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem finSignGL_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E)
    (J : Matrix (Fin n) (Fin n) E) : finSignGL F E n ∈ HR (AF F) σ J := by
  have h : sigR (AF F) σ (finSign F E) = finSign F E := by
    change pairA F 1 (-1) ⊗ₜ σ 1 = _
    rw [map_one]; rfl
  have h2 : Formalism.UG.cT (sigR (AF F) σ) (finSign F E • (1 : Matrix (Fin n) (Fin n) _)) = finSign F E • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Formalism.UG.cT, h]
    · simp [Formalism.UG.cT, hij, Ne.symm hij]
  change Formalism.UG.cT (sigR (AF F) σ) (finSign F E • 1) * JR (AF F) J * (finSign F E • 1) = JR (AF F) J
  rw [h2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, finSign_sq, one_smul]

def negFin (V : HSp D) : GA D V := ⟨finSignGL _ _ _, finSignGL_mem _ _⟩

end GlobalTheory.LevelSubgroup
