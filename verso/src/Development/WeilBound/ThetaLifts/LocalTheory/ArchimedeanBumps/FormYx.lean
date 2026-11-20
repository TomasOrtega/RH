import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.HeisenbergActionAddOfOrthogonal
import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr PositivityTheory.ThKF
open scoped ComplexConjugate

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}
  {lift : (InfinitePlace F → ℂ) → AE F E}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem IsLift.ext (h : IsLift σ B lift) {a b : AE F E} (hab : At (evI F) (a - b)) (e : ∀ w, piInf (B.emb w) a = piInf (B.emb w) b) :
    a = b := by
  have h0 : lift (fun w => piInf (B.emb w) 0) = 0 := h.inv 0 fun u _ => smul_zero u
  rw [← sub_eq_zero, ← h.inv _ hab, ← h0]
  congr 1; funext w; rw [map_sub, e, sub_self, map_zero]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem at_sub {N : Type} [AddCommGroup N] [Module (AF F) N] {a b : N} (ha : At (evI F) a) (hb : At (evI F) b) : At (evI F) (a - b) :=
  fun u hu => by rw [smul_sub, ha u hu, hb u hu, sub_zero]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem at_add {N : Type} [AddCommGroup N] [Module (AF F) N] {a b : N} (ha : At (evI F) a) (hb : At (evI F) b) : At (evI F) (a + b) :=
  fun u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem at_mul {a : AE F E} (ha : At (evI F) a) (b : AE F E) : At (evI F) (a * b) := at_smul2 ha b

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsLift.eq (h : IsLift σ B lift) {a : AE F E} (ha : At (evI F) a) {c} (e : ∀ w, piInf (B.emb w) a = c w) : a = lift c :=
  h.ext (at_sub ha (h.supp c)) fun w => by rw [e, h.pi]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsLift.ch (h : IsLift σ B lift) {a b : AE F E} (ha : At (evI F) a) {x y : InfinitePlace F → ℂ} (hx : ∀ w, (piInf (B.emb w) (a * b)).re = (x w * y w).re) :
    B.ψ (Algebra.trace (AF F) (AE F E) (a * b)) = ch (-pr x y) := by
  rw [h.psi _ (at_mul ha b), Bump.ch, pr]
  simp only [hx]
  congr 1; push_cast; ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem pi_bA (h : IsLift σ B lift) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → AE F E) (w) : piInf (B.emb w) (bA σ J x y) =
    (fun i => piInf (B.emb w) (x i)) ⬝ᵥ J.map (B.emb w).1 *ᵥ fun i => conj (piInf (B.emb w) (y i)) := by
  simp only [bA, dotProduct, Matrix.mulVec, map_sum, map_mul, h.conj, incM, Matrix.map_apply, h.incl]

variable (B) in

def xi (x : Fin n → E) {S : Subgroup (UA σ X.J)} (k : S) : InfinitePlace F → Fin n → ℂ :=
  fun w i => piInf (B.emb w) ((mat k.1⁻¹ *ᵥ incV F x) i)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem cont_xi (h : IsLift σ B lift) (x : Fin n → E) (S : Subgroup (UA σ X.J)) : Continuous (xi B x (S := S)) := by
  refine continuous_pi fun w => continuous_pi fun i => ?_
  simp only [xi, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine continuous_finsetSum _ fun j _ => ((h.cont w).comp ?_).mul continuous_const
  have : Continuous fun k : S => (((k.1.1)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
    Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (continuous_apply j).comp ((continuous_apply i).comp this)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem xi_ne (h : IsLift σ B lift) {x y : Fin n → E} (hxy : form σ X.J x y = 1) {S : Subgroup (UA σ X.J)} (k : S) (w) : xi B x k w ≠ 0 := by
  intro h0
  have := pi_bA h X.J (mat k.1⁻¹ *ᵥ incV F x) (mat k.1⁻¹ *ᵥ incV F y) w
  rw [bA_mat, bA_inc, hxy, map_one, map_one] at this
  change _ = xi B x k w ⬝ᵥ _ at this
  rw [h0, zero_dotProduct] at this
  exact one_ne_zero this

variable (B X) in

def Yv (lift : (InfinitePlace F → ℂ) → AE F E) (η : XS (InfinitePlace F × Fin n)) : Fin n → AE F E :=
  fun i => lift fun w => conj (((X.J.map (B.emb w).1)⁻¹ *ᵥ fun j => conj (η (w, j))) i)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem at_Yv (h : IsLift σ B lift) (η) : At (evI F) (Yv X B lift η) := fun u hu => funext fun _ => h.supp _ u hu

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem pi_beta (h : IsLift σ B lift) {r s} (hX : X.IsHerm σ B r s) (x : Fin n → E) {S : Subgroup (UA σ X.J)} (k : S) (η) (w) :
    piInf (B.emb w) (bA σ X.J (incV F x) (mat k.1 *ᵥ Yv X B lift η)) = bet (xi B x) (k, η) w := by
  rw [← mat_cancel' k.1 (incV F x), bA_mat, pi_bA h]
  simp only [Yv, h.pi, Complex.conj_conj]
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (cartan_det (hX.cartan w)).isUnit, Matrix.one_mulVec]
  rfl

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem sig_pt (h : IsLift σ B lift) {x y : Fin n → E} (hxy : form σ X.J x y = 1) {S : Subgroup (UA σ X.J)}
    (hS : ∀ k ∈ S, k ∈ UAt σ X (evI F)) (p : S × (InfinitePlace F → ℂ)) (hp : pim (xi B x) p = pim (xi B x) ((1 : S), 1)) :
    (∀ w, p.2 w ≠ 0) ∧ ∃ t : (AE F E)ˣ, At (evI F) ((t : AE F E) - 1) ∧ (∀ w, piInf (B.emb w) (t : AE F E) = p.2 w) ∧
      mat p.1.1 *ᵥ incV F x = t.1 • incV F x := by
  have e : ∀ w i, p.2 w * xi B x p.1 w i = xi B x (1 : S) w i := fun w i => by
    simpa [pim] using congrArg (fun z : XS _ => z (w, i)) hp
  have hne : ∀ w, p.2 w ≠ 0 := fun w h0 => xi_ne h hxy (1 : S) w (funext fun i => by rw [← e, h0, zero_mul]; rfl)
  obtain ⟨t, ht, ht'⟩ := h.unit p.2 hne
  refine ⟨hne, t, ht, ht', ?_⟩
  have k1 : t.1 • (mat p.1.1⁻¹ *ᵥ incV F x) = incV F x := funext fun i => by
    refine h.ext ?_ fun w => ?_
    · have a1 : At (evI F) ((mat p.1.1⁻¹ - 1) *ᵥ incV F x) := fun u hu => by
        rw [← Matrix.smul_mulVec, hS _ (inv_mem p.1.2) u hu, Matrix.zero_mulVec]
      have a2 := at_add (at_smul2 ht (mat p.1.1⁻¹ *ᵥ incV F x)) a1
      rw [sub_smul, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_sub_cancel] at a2
      exact fun u hu => congrFun (a2 u hu) i
    · rw [Pi.smul_apply, smul_eq_mul, map_mul, ht']
      refine (e w i).trans ?_
      simp [xi, mat_one]
  conv_lhs => rw [← k1, Matrix.mulVec_smul, mat_cancel']

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem nu_eq (h : IsLift σ B lift) {ν : Chr F E} {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w) {t : (AE F E)ˣ}
    (ht : At (evI F) ((t : AE F E) - 1)) : (ν t : ℂ) = r0 κ 0 (fun w => piInf (B.emb w) t) ∧
      (absE F E t : ℝ) = nm fun w => piInf (B.emb w) t := ⟨by rw [hν t ht]; simp [r0], h.abs t ht⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conv (h : IsLift σ B lift) {ν : Chr F E} {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w)
    (x : @Measure (idAt E (evI F)) (borel _)) (hx : @Measure.IsHaarMeasure _ _ _ (borel _) x) : ∃ c : ℂ, c ≠ 0 ∧
    ∀ (e : ℕ) (g : (InfinitePlace F → ℂ) → ℂ) (G : (AE F E)ˣ → ℂ), (∀ t : (AE F E)ˣ, G t = g fun w => piInf (B.emb w) t) →
      @integral _ _ _ _ (borel _) x (fun t => G t.1 * (ν t.1 : ℂ) * ((absE F E t.1 : ℝ) : ℂ) ^ (e + 1)) = c * ∫ y, g y * r0 κ e y := by
  obtain ⟨c, hc, H⟩ := h.haar x hx
  refine ⟨c, by exact_mod_cast hc.ne', fun e g G hG => ?_⟩
  have := H fun y => g y * r0 κ (e + 1) y
  rw [← show _ = ∫ y, g y * r0 κ e y from integral_congr_ae (by
    filter_upwards [ae_unit] with y hy
    exact (mul_assoc _ _ _).trans (congrArg _ (rationalWeight_succ_mul_inv_norm κ e hy))), ← this]
  congr 1; funext t
  obtain ⟨e1, e2⟩ := nu_eq h hν ((h.idAt t.1).1 t.2)
  rw [hG, rationalWeight_eq_mul_norm_pow κ (e + 1), e1, e2, mul_assoc]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem form_yx (hB : B.IsGood σ) {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ} (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j)
    {x y : Fin n → E} (h : form σ J x y = 1) : form σ J y x = ((ε : ℤ) : E) := by
  have hs := PositivityTheory.ThKG.Tow.Levi.sig_sig hB.cm
  rw [← hs (form σ J y x), form_eps hs hJ, h, mul_one, map_intCast]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem decomp (hB : B.IsGood σ) {r s} (hX : X.IsHerm σ B r s) {H : Plane E n n₁} {i j} (hH : H.IsAdapted σ B X X₁ i j)
    (z : Fin n → AE F E) : ∃ (U : Fin n₁ → AE F E) (a : AE F E),
      z = incM F H.ι *ᵥ U + a • incV F H.x + cA σ (bA σ X.J (incV F H.x) z) • incV F H.y := by
  obtain ⟨ε, A', hF⟩ := isFr hB (Or.inl hX) hH
  obtain ⟨U, a, b, rfl⟩ := (IsFr.ad hF).span z
  refine ⟨U, a, ?_⟩
  congr 2
  have g := (IsFr.ad hF).gram
  have e : (fun i => cA σ ((fr (incM F H.ι) (incV F H.x) (incV F H.y) *ᵥ Sum.elim U ![a, b]) i)) =
      (fr (incM F H.ι) (incV F H.x) (incV F H.y)).map (cA σ) *ᵥ fun i => cA σ (Sum.elim U ![a, b] i) :=
    funext fun i => RingHom.map_mulVec (cA σ : AE F E →+* AE F E) _ _ i
  have g2 := congrFun (congrArg (· *ᵥ fun i => cA σ (Sum.elim U ![a, b] i)) g) (Sum.inr 0)
  rw [← fr_mulVec, bA, e]
  have g3 : incV F H.x ⬝ᵥ incM F X.J *ᵥ (fr (incM F H.ι) (incV F H.x) (incV F H.y)).map (cA σ) *ᵥ
      (fun i => cA σ (Sum.elim U ![a, b] i)) = cA σ b := by
    simp only [← Matrix.mulVec_mulVec] at g2
    refine Eq.trans ?_ (g2.trans ?_)
    · rfl
    · simp [gr, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [g3, PositivityTheory.ThKG.Tow.Levi.cA_cA hB.cm]

end PositivityTheory.ThKG.Loc.Bump

end
