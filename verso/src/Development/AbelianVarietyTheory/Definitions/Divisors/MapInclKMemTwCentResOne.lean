import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycFieldA
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

noncomputable section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped TensorProduct Classical
namespace GlobalTheory.LKRes.Model
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem sigKQ_inclK (r : ℕ) (a : K) : sigKQ p K r (inclK p K r a) = inclK p K r a := by
  change Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) = a ⊗ₜ[ℚ_[p]] (1 : Qr p r)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem sigKQ_inclQ (r : ℕ) (b : Qr p r) : sigKQ p K r (inclQ p K r b) = inclQ p K r (frobQ p r b) := by
  change Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) ((1 : K) ⊗ₜ[ℚ_[p]] b) = (1 : K) ⊗ₜ[ℚ_[p]] frobQ p r b
  rw [Algebra.TensorProduct.map_tmul, map_one]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobQ_norm (r : ℕ) (b : Qr p r) : ‖((frobQ p r b : Qr p r) : PadicAlgCl p)‖ = ‖(b : PadicAlgCl p)‖ :=
  norm_map_GK p (Q0 p) (frobK p (Q0 p)) b

/- English proof (translation)
Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem frobQ_intR (r : ℕ) (b : Qr p r) (hb : b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r) :
    frobQ p r b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
  simp only [GlobalTheory.LKLoc.intR, Subring.mem_comap] at *
  have := (mem_Obar_iff (p := p)).1 hb
  exact (mem_Obar_iff (p := p)).2 (by
    show ‖((frobQ p r b : Qr p r) : PadicAlgCl p)‖ ≤ 1
    rw [frobQ_norm]; exact this)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sigKQ_intKQ (r : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) : sigKQ p K r x ∈ intKQ p K r := by
  have : intKQ p K r ≤ (intKQ p K r).comap (sigKQ p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [sigKQ_inclK]; exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [sigKQ_inclQ]; exact Subring.subset_closure (Or.inr ⟨⟨_, frobQ_intR p r b.1 b.2⟩, rfl⟩)
  exact this hx

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem sigRes_Kres (n r : ℕ) (g : GL (Fin n) (KQ p K r)) (hg : g ∈ Kres p K n r) :
    sigRes p K n r g ∈ Kres p K n r := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨GeneralLinearGroup.map ((sigKQ p K r).toRingHom.restrict (intKQ p K r) (intKQ p K r)
    (fun x hx => sigKQ_intKQ p K r x hx)) h, ?_⟩
  ext i j
  simp [sigRes, GeneralLinearGroup.map]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem nrmRes_one (n : ℕ) (δ : GL (Fin n) (KQ p K 1)) : nrmRes p K n 1 δ = δ := by
  simp [nrmRes]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
example (n r : ℕ) : Nontrivial (KQ p K r) := by
  unfold KQ; infer_instance

def mulMap (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] PadicAlgCl p :=
  Algebra.TensorProduct.productMap K.val (Qr p r).val

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mulMap_intKQ (r : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) : ‖mulMap p K r x‖ ≤ 1 := by
  have : intKQ p K r ≤ (Obar p).toSubring.comap (mulMap p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (mulMap p K r (a.1 ⊗ₜ[ℚ_[p]] (1 : Qr p r))) ∈ Obar p
      show (a.1 : PadicAlgCl p) * 1 ∈ Obar p
      rw [mul_one]; exact a.2
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (mulMap p K r ((1 : K) ⊗ₜ[ℚ_[p]] b.1)) ∈ Obar p
      show 1 * (b.1 : PadicAlgCl p) ∈ Obar p
      rw [one_mul]; exact b.2
  exact (mem_Obar_iff (p := p)).1 (this hx)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inv_p_not_mem_intKQ (r : ℕ) : inclK p K r (p : K)⁻¹ ∉ intKQ p K r := by
  intro h
  have h1 := mulMap_intKQ p K r _ h
  have h2 : mulMap p K r (inclK p K r (p : K)⁻¹) = (p : PadicAlgCl p)⁻¹ := by
    show (((p : K)⁻¹ : K) : PadicAlgCl p) * 1 = _
    simp
  rw [h2, norm_inv] at h1
  have hp : ‖(p : PadicAlgCl p)‖ < 1 := by
    have h := Padic.norm_p_lt_one (p := p)
    rw [← PadicAlgCl.norm_extends] at h
    simpa using h
  have hp0 : 0 < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have := (one_lt_inv₀ hp0).2 hp
  linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Kres_ne_top (r : ℕ) : Kres p K 1 r ≠ ⊤ := by
  intro h
  have hp : (p : K)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let g0 : GL (Fin 1) K := GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun _ => (p : K)⁻¹) (by simp [hp])
  let g : GL (Fin 1) (KQ p K r) := GeneralLinearGroup.map (inclK p K r).toRingHom g0
  have hg : g ∈ Kres p K 1 r := by rw [h]; trivial
  obtain ⟨k, hk⟩ := hg
  have e := congrArg (fun x : GL (Fin 1) (KQ p K r) => (x : Matrix (Fin 1) (Fin 1) (KQ p K r)) 0 0) hk
  simp only [g, g0, GeneralLinearGroup.map] at e
  apply inv_p_not_mem_intKQ p K r
  have : ((k : Matrix (Fin 1) (Fin 1) (intKQ p K r)) 0 0 : KQ p K r) ∈ intKQ p K r := SetLike.coe_mem _
  convert this using 1
  simp at e ⊢
  exact e.symm

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem frobQ_congr (r : ℕ) (b : Qr p r) (hb : ‖(b : PadicAlgCl p)‖ ≤ 1) :
    ‖((frobQ p r b : Qr p r) : PadicAlgCl p) - (b : PadicAlgCl p) ^ p‖ < 1 := by
  have h := (isFrob_frobK (p := p) (K := Q0 p) inferInstance).isFrobOn r b b.2 hb
  rw [show qK p (Q0 p) = p from residue_cardinality_base_field] at h
  exact h

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
-/
theorem exists_frobQ_ne {r : ℕ} (hr : 2 ≤ r) : ∃ b : Qr p r, b ≠ 0 ∧ frobQ p r b ≠ b := by
  by_contra hc
  push Not at hc
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  have h := (IsFrobOn.pow_fixes_iff p (Q0 p) hK (by omega : 0 < r) ((isFrob_frobK hK).isFrobOn r) 1).1 (by
    intro x hx
    rw [pow_one]
    by_cases h0 : (⟨x, hx⟩ : Qr p r) = 0
    · have : x = 0 := congrArg Subtype.val h0
      rw [this, map_zero]
    · exact congrArg Subtype.val (hc ⟨x, hx⟩ h0))
  have := Nat.le_of_dvd one_pos h
  omega

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inclQ_injective (r : ℕ) : Function.Injective (inclQ p K r) :=
  haveI : Nontrivial (KQ p K r) := by unfold KQ; infer_instance
  (inclQ p K r).toRingHom.injective

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem twCentRes_one_ne_top {r : ℕ} (hr : 2 ≤ r) : twCentRes p K 1 r 1 ≠ ⊤ := by
  intro h
  obtain ⟨b, hb0, hb⟩ := exists_frobQ_ne p hr
  let g0 : GL (Fin 1) (Qr p r) := GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun _ => b) (by simp [hb0])
  let g : GL (Fin 1) (KQ p K r) := GeneralLinearGroup.map (inclQ p K r).toRingHom g0
  have hg : g ∈ twCentRes p K 1 r 1 := by rw [h]; trivial
  have e : g * 1 = 1 * sigRes p K 1 r g := hg
  rw [mul_one, one_mul] at e
  have e' := congrArg (fun x : GL (Fin 1) (KQ p K r) => (x : Matrix (Fin 1) (Fin 1) (KQ p K r)) 0 0) e
  have e'' : inclQ p K r b = sigKQ p K r (inclQ p K r b) := by
    simpa [g, g0, sigRes, GeneralLinearGroup.map] using e'
  rw [sigKQ_apply_inclQ] at e''
  exact hb (inclQ_injective p K r e'').symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem map_inclK_mem_twCentRes_one (n r : ℕ) (g : GL (Fin n) K) :
    GeneralLinearGroup.map (inclK p K r).toRingHom g ∈ twCentRes p K n r 1 := by
  show _ * 1 = 1 * sigRes p K n r _
  rw [mul_one, one_mul]
  ext i j
  simp [sigRes, GeneralLinearGroup.map, sigKQ_apply_inclK]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem finrank_KQ {r : ℕ} (hr : 0 < r) : Module.finrank ℚ_[p] (KQ p K r) = Module.finrank ℚ_[p] K * r := by
  have h : Module.finrank ℚ_[p] (Qr p r) = r := by
    have := finrank_Kn p (Q0 p) inferInstance hr
    simpa using this
  have e : Module.finrank ℚ_[p] (K ⊗[ℚ_[p]] Qr p r) = Module.finrank ℚ_[p] K * Module.finrank ℚ_[p] (Qr p r) :=
    Module.finrank_tensorProduct
  rw [h] at e
  exact e

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem TOResU_gl_one_of_le (γ : GL (Fin 1) (KQ p K 1)) (U : Subgroup (GL (Fin 1) (KQ p K 1)))
    (hU : U ≤ Kres p K 1 1) (φ : GL (Fin 1) (KQ p K 1) → ℂ) :
    TOResU p K 1 1 γ U φ = φ γ / (U.relIndex (Kres p K 1 1) : ℂ) := by
  haveI := normal_of_gl_one (Kres p K 1 1)
  have hT : GlobalTheory.BCT.twCent (sigRes p K 1 1) γ = ⊤ := by
    rw [sigRes_degree_one]
    refine eq_top_iff.2 fun g _ => ?_
    show g * γ = γ * g
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  obtain ⟨x, hx⟩ := orbSum_of_twCent_eq_top (sigRes p K 1 1) (Kres p K 1 1) γ hT
  rw [TOResU, GlobalTheory.LKLoc.twOrbU, hx, locPart_of_normal, hT, top_inf_eq, GlobalTheory.LKLoc.volRat,
    Subgroup.relIndex_eq_one.2 hU]
  push_cast
  ring

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem TOHT_torus_degree_one (m : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p))
    (γ : GHT p m 1 1 Kw) (φ : GHT p m 1 1 Kw → ℂ) : TOHT p m 1 1 Kw γ φ = φ γ := by
  have hc : ∀ {R : Type} [CommRing R] (a b : GL (Fin 1) R), a * b = b * a := fun a b => by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have hT : GlobalTheory.BCT.twCent (sigHT p m 1 1 Kw) γ = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    have hs : sigHT p m 1 1 Kw g = g := by
      refine Prod.ext ?_ (funext fun i => ?_)
      · show GlobalTheory.LKLoc.sig p (Q0 p) 1 1 g.1 = g.1
        refine Units.ext (Matrix.ext fun i j => ?_)
        exact DFunLike.congr_fun (frobQ_degree_one p) ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)) i j)
      · show sigRes p (Kw i) 1 1 (g.2 i) = g.2 i
        rw [sigRes_degree_one]; rfl
    show g * γ = γ * sigHT p m 1 1 Kw g
    rw [hs]
    exact Prod.ext (hc _ _) (funext fun i => hc _ _)
  rw [TOHT_gl_one, TOHTU, GlobalTheory.LKLoc.twOrbU]
  haveI : (KHT p m 1 1 Kw).Normal := ⟨fun k hk x =>
    ⟨(normal_of_gl_one _).conj_mem k.1 hk.1 x.1,
      fun i hi => (normal_of_gl_one (Kres p (Kw i) 1 1)).conj_mem (k.2 i) (hk.2 i hi) (x.2 i)⟩⟩
  obtain ⟨x, hx⟩ := orbSum_of_twCent_eq_top (sigHT p m 1 1 Kw) (KHT p m 1 1 Kw) γ hT
  rw [hx, locPart_of_normal, twCentHT, GlobalTheory.LKLoc.volRat_self]
  simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem sigHT_KHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) (g : GHT p m n r Kw)
    (hg : g ∈ KHT p m n r Kw) : sigHT p m n r Kw g ∈ KHT p m n r Kw := by
  refine ⟨?_, fun i hi => sigRes_Kres p (Kw i) n r _ (hg.2 i hi)⟩
  obtain ⟨h, e⟩ := hg.1
  refine ⟨GeneralLinearGroup.map ((frobQ p r).toRingHom.restrict (GlobalTheory.LKLoc.intR p (Q0 p) r)
    (GlobalTheory.LKLoc.intR p (Q0 p) r) (fun x hx => frobQ_intR p r x hx)) h, ?_⟩
  show _ = GlobalTheory.LKLoc.sig p (Q0 p) 1 r g.1
  rw [← e]
  ext i j
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
example (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : TopologicalSpace (GHT p m n r Kw) :=
  inferInstance

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isTopologicalRing_KQ (hK : FiniteDimensional ℚ_[p] K) {r : ℕ} (hr : 0 < r) :
    IsTopologicalRing (KQ p K r) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI : FiniteDimensional ℚ_[p] (KQ p K r) := inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing ℚ_[p] (KQ p K r)

/- English proof (translation)
Both sides reduce to the same expression.
-/
example : Q0 p = ReciprocityTheory.DiscreteGroups.LocalClassField.Q0 p := rfl

end GlobalTheory.LKRes.Model
