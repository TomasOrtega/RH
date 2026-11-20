import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.RationalPointsDense
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.LatticeClassesFiniteRefinement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.PosDefOfDefiniteSignatureHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictInter

noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem incl_mem_Oh {e : E} (he : IsIntegral ℤ e) : inclR (Af F) e ∈ Oh F E :=
  tmul_mem_Oh intAf_one he

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem one_mem_Oh : (1 : Af F ⊗[F] E) ∈ Oh F E := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_Oh intAf_one isIntegral_one

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem oh_inter {e : E} (he : inclR (Af F) e ∈ Oh F E) : IsIntegral ℤ e := by
  let ψ : Af F ⊗[F] E →+* E ⊗[F] Af F := (Algebra.TensorProduct.comm F (Af F) E).toRingHom
  have hψ : ∀ z ∈ Oh F E, ψ z ∈ Formalism.MainNotions.S.IntAf F E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, e', he', rfl⟩ := hz
      have e1 : ψ (a ⊗ₜ[F] e') = (e' ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [e1]
      refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨e', ⟨⟨e', he'⟩, rfl⟩⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact Subring.zero_mem _
    | add x y _ _ h1 h2 => rw [map_add]; exact Subring.add_mem _ h1 h2
    | neg x _ h1 => rw [map_neg]; exact Subring.neg_mem _ h1
  have e2 : ψ (inclR (Af F) e) = Formalism.UG.inclE (F := F) (Af F) e := rfl
  have := PIW.AdelClassFin.dual_intersection F E e (e2 ▸ hψ _ he)
  obtain ⟨b, hb⟩ := this
  rw [← hb]
  exact b.isIntegral_coe

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem up_nat {M : ℕ} (L : Set (Fin M → E))
    (h4 : ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) :
    ∃ u : ℕ, 0 < u ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i) := by
  obtain ⟨c, hc, hL⟩ := h4
  obtain ⟨u, hu, c', huc⟩ := nat_mult c hc
  refine ⟨u, hu, fun x hx i => ?_⟩
  have : (u : F) • x i = (c' : F) • ((c : F) • x i) := by
    rw [smul_smul]
    congr 1
    have := congrArg (algebraMap (𝓞 F) F) huc
    rw [map_natCast, map_mul] at this
    rw [this, mul_comm]
  rw [this, Algebra.smul_def]
  exact (IsIntegral.algebraMap (c'.isIntegral_coe)).mul (hL x hx i)

variable {M : ℕ}

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem up_Oh (L : Set (Fin M → E)) {u : ℕ} (hu : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i))
    {w : Fin M → Af F ⊗[F] E} (hw : w ∈ latHat F E L) (i : Fin M) : u • w i ∈ Oh F E := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    show u • (a ⊗ₜ[F] x i) ∈ Oh F E
    rw [nsmul_tmul_F]
    exact tmul_mem_Oh ha (hu x hx i)
  | zero => show u • (0 : Af F ⊗[F] E) ∈ Oh F E; rw [smul_zero]; exact zero_mem _
  | add w w' _ _ h1 h2 => show u • (w i + w' i) ∈ Oh F E; rw [smul_add]; exact add_mem h1 h2
  | neg w _ h1 => show u • (-w i) ∈ Oh F E; rw [smul_neg]; exact neg_mem h1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem low_vec (L : Set (Fin M → E)) {k : ℕ}
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    {w : Fin M → Af F ⊗[F] E} (hw : ∀ i, w i ∈ Oh F E) : k • w ∈ latHat F E L := by
  rw [← Finset.univ_sum_single (k • w)]
  exact AddSubgroup.sum_mem _ fun i _ => single_mem L hk (hw i) i

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem den_mat (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) :
    ∃ m : ℕ, 0 < m ∧ ∀ l j, m • g l j ∈ Oh F E := by
  classical
  choose mf hmf hmO using fun p : Fin M × Fin M => den (g p.1 p.2)
  refine ⟨∏ p, mf p, Finset.prod_pos (fun p _ => hmf p), fun l j => ?_⟩
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ (l, j))
  rw [hq, mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (hmO (l, j)) _

variable (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem sigR_Oh {z : Af F ⊗[F] E} (hz : z ∈ Oh F E) : sigR (Af F) σ z ∈ Oh F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, e, he, rfl⟩ := hz
    have e1 : sigR (Af F) σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [sigR]
    rw [e1]
    exact tmul_mem_Oh ha (by simpa using int_sigma (σ : E →+* E) he)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [map_neg]; exact neg_mem h1

def hermA (X Y : Fin M → Af F ⊗[F] E) : Af F ⊗[F] E :=
  dotProduct (fun i => sigR (Af F) σ (X i)) ((JR (Af F) J).mulVec Y)

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermA_vinc (x y : Fin M → E) :
    hermA σ J (vinc (F := F) x) (vinc y) = inclR (Af F) (PI.HermLatFin.herm (σ : E →+* E) J x y) := by
  simp only [hermA, dotProduct, Matrix.mulVec, vinc, JR, Matrix.map_apply, sigR_inclR, PI.HermLatFin.herm,
    map_sum, map_mul, Finset.mul_sum, AlgHom.coe_toRingHom]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hermA_add_left (X X' Y : Fin M → Af F ⊗[F] E) :
    hermA σ J (X + X') Y = hermA σ J X Y + hermA σ J X' Y := by
  simp only [hermA, dotProduct, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hermA_neg_left (X Y : Fin M → Af F ⊗[F] E) : hermA σ J (-X) Y = -hermA σ J X Y := by
  simp only [hermA, dotProduct, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hermA_zero_left (Y : Fin M → Af F ⊗[F] E) : hermA σ J 0 Y = 0 := by
  simp [hermA, dotProduct]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hermA_smul_left (c : Af F ⊗[F] E) (X Y : Fin M → Af F ⊗[F] E) :
    hermA σ J (c • X) Y = sigR (Af F) σ c * hermA σ J X Y := by
  simp only [hermA, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem hermA_single_left (i : Fin M) (p : Af F ⊗[F] E) (Y : Fin M → Af F ⊗[F] E) :
    hermA σ J (Pi.single i p) Y = sigR (Af F) σ p * ((JR (Af F) J).mulVec Y) i := by
  rw [hermA, dotProduct, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hermA_unitary (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (hg : cT (sigR (Af F) σ) g * JR (Af F) J * g = JR (Af F) J) (X Y : Fin M → Af F ⊗[F] E) :
    hermA σ J (g.mulVec X) (g.mulVec Y) = hermA σ J X Y := by
  have h1 : (fun i => sigR (Af F) σ ((g.mulVec X) i)) =
      (g.map (sigR (Af F) σ)).mulVec (fun i => sigR (Af F) σ (X i)) := by
    funext i
    exact RingHom.map_mulVec _ g X i
  have e : (g.map (sigR (Af F) σ))ᵀ * (JR (Af F) J * g) = JR (Af F) J := by
    rw [← Matrix.mul_assoc]; exact hg
  unfold hermA
  rw [h1, ← Matrix.vecMul_transpose (g.map (sigR (Af F) σ)), ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, e]

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem finMat_unitary (h : HA (AF F) σ J) :
    cT (sigR (Af F) σ) (finMat σ J h) * JR (Af F) J * finMat σ J h = JR (Af F) J := by
  have hm : cT (sigR (AF F) σ) ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      JR (AF F) J * ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      JR (AF F) J := (show HR (AF F) σ J from h).2
  let φ := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
  have hφs : ∀ z, φ (sigR (AF F) σ z) = sigR (Af F) σ (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [φ, sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hφJ : (JR (AF F) J).map φ = JR (Af F) J := by
    ext i j
    simp [φ, JR, inclR, Algebra.TensorProduct.map_tmul]
  have hcT : ∀ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      (cT (sigR (AF F) σ) X).map φ = cT (sigR (Af F) σ) (X.map φ) := by
    intro X
    ext i j
    simp [cT, hφs]
  have := congrArg (fun X => X.map φ) hm
  simp only [mapAlg_mul, hcT, hφJ] at this
  exact this

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hermA_Oh {u dJ : ℕ} (hJ : ∀ i j, IsIntegral ℤ ((dJ : E) * J i j)) {X Y : Fin M → Af F ⊗[F] E}
    (hX : ∀ i, u • X i ∈ Oh F E) (hY : ∀ i, u • Y i ∈ Oh F E) :
    (u * u * dJ) • hermA σ J X Y ∈ Oh F E := by
  have : (u * u * dJ) • hermA σ J X Y = ∑ i, ∑ j,
      sigR (Af F) σ (u • X i) * (inclR (Af F) ((dJ : E) * J i j) * (u • Y j)) := by
    simp only [hermA, dotProduct, Matrix.mulVec, JR, Matrix.map_apply, Finset.mul_sum, Finset.smul_sum,
      map_nsmul, map_mul, map_natCast, nsmul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [this]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ =>
    Oh_mul (sigR_Oh σ (hX i)) (Oh_mul (incl_mem_Oh (hJ i j)) (hY j))

end PI.UnitaryGroupMassFormula.UJClassFin
