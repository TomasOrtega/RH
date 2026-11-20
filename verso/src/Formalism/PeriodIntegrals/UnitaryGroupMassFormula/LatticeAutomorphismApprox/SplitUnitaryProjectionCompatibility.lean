import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SecondCoordinateVectorNsmul

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB

open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `I g r k e f z Rf _hH v _hv _hsum p1 hp1 T hT`. Establish `hε : ∀ w ∈ LL I v, PI.FinKW.psiV I v Rf.ew • w ∈ LL I v` using `fun w hw => PI.FinKW.LocTo.intAf_le_mulSet I v Rf.ew_int w hw`. Establish `: Module.Finite I.F I.E` using `Module.finite_of_finrank_eq_succ I.cm.deg2`. Establish `hdim : Module.finrank (KV I v) (RV I v) = 2`. Rewrite using `[Module.finrank_baseChange]`.

Conclude with `I.cm.deg2`. Establish `hb` using `piHom_bijective hdim (sigV I v) p1 (sigV_alg I v) (sigV_sigV I v) hp1.1 (PI.FinKW.psiV I v Rf.ew) hp1.2.1 hp1.2.2.1`. Use `set π := piEquiv (sigV I v) p1 hb with hπdef`. Establish `hπ : ∀ r, π (sigV I v r) = (π r).swap` using `piEquiv_sig _ _ (sigV_sigV I v) hb`. Establish `hchar` using `mem_LL_iff I v _ p1 hp1 hb.1 hε`.

Take `⟨y, hy⟩` from `(SplitGL.proj_bijective (sigV I v) π hπ _ (spl_herm_v I v) (spl_det_v I v)).2 T`. Substitute `hy` using the available equality. Establish `hPm : (I.J.map (inclV I v)).map (SplitGL.p1 π) = Pm I v p1` using `by ext i j; rfl`. Establish `v1 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (X : Fin I.n → RV I v), vec1 p1 (((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) = ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y' : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) …`. Introduce `y' X`.

Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec p1 _ _ i`. Establish `v2 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (X : Fin I.n → RV I v), vec2 p1 (((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) = ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)).map (SplitGL.p2 π) *ᵥ vec2 p1 X`. Introduce `y' X`. Use function extensionality and compare the values at `i`.

Conclude with `RingHom.map_mulVec (p1.comp (sigV I v)) _ _ i`. Establish `vp2 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (β β' : Fin I.n → KV I v), β' ᵥ* Pm I v p1 = (β ᵥ* Pm I v p1) ᵥ* (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y')⁻¹ : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) → ((y' : GL (Fin I.n) (RV I v) …`. Introduce `y' β β' h`. Rewrite `h` using `[← hPm]`. Conclude with `second_projection_mulVec_eq (sigV I v) π hπ _ (spl_det_v I v) y' β β' h`.

Establish `extv : ∀ X X' : Fin I.n → RV I v, vec1 p1 X = vec1 p1 X' → vec2 p1 X = vec2 p1 X' → X = X'`. Introduce `X X' h1 h2`. Use function extensionality and compare the values at `i`. Apply `hb.1` to reduce the goal to its premises. Conclude with `Prod.ext (congrFun h1 i) (congrFun h2 i)`.

Establish `fwd : ∀ y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v)), (∀ x ∈ Lam1 I v p1, ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y' : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ x ∈ Lam1 I v p1) → (∀ β ∈ Lam2 I v p1, ∃ β' ∈ Lam2 I v p1, β' ᵥ* Pm I v p1 = …`. Introduce `y' h1 h2 w hw`. Rewrite `hw`, the goal using `[hchar]`. Take `⟨hw1, hw2⟩` from `hw`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[v1]`. Conclude with `h1 _ hw1`. Rewrite using `[v2]`. Take `⟨β', hβ', eβ⟩` from `h2 _ hw2`. Rewrite using `[vp2 y' _ β' eβ]`.

Conclude with `hβ'`. Establish `hinvproj : SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y⁻¹ = (SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹` using `map_inv _ y`. Establish `fwdY` using `fwd y (fun x hx => (hT.1 x hx).1) (fun β hβ => (hT.2.1 β hβ).2)`. Establish `fwdYi` using `fwd y⁻¹ (fun x hx => by rw [hinvproj]; exact (hT.1 x hx).2) (fun β hβ => by rw [hinvproj, inv_inv]; exact (hT.2.1 β hβ).1)`. Establish `hYiY : ∀ X : Fin I.n → RV I v, (((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ (((y : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) = X`.

Introduce `X`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul]`. Establish `: ((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) * (y : GL (Fin I.n) (RV I v)) = 1`. Rewrite using `[← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]`. Rewrite using `[this, Units.val_one, Matrix.one_mulVec]`.

Establish `fixv : ∀ X : Fin I.n → RV I v, ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ vec1 p1 X = vec1 p1 X → (vec2 p1 X ᵥ* Pm I v p1) ᵥ* ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y : GL (Fin I.n) (KV I v)) : …`. Introduce `X h1 h2`. Apply `extv` to reduce the goal to its premises. Rewrite using `[v1, h1]`. Rewrite using `[v2]`.

Apply `vp2` to reduce the goal to its premises. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`. Use `⟨(y : GL (Fin I.n) (RV I v)), y.2, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x`. Use `⟨fun hx => fwdY x hx, fun hx => ?_⟩` and prove the remaining obligations. Use `fwdYi _ hx` as an intermediate fact. Rewrite `this` using `[hYiY]`. Then use the resulting hypothesis. Introduce `a`.

Take `⟨h1, h2, h3, h4⟩` from `hT.2.2.1 a`. Conclude with `⟨fixv _ h1 h3, fixv _ h2 h4⟩`. Take `⟨w1, hw1, hw1e⟩` from `hT.2.2.2.1`. Take `⟨β, hβ, hβe⟩` from `hT.2.2.2.2`. Use `set w : Fin I.n → RV I v := fun i => π.symm (w1 i, β i) with hwdef`.

Establish `hw1' : vec1 p1 w = w1`. Use function extensionality and compare the values at `i`. Use `show SplitGL.p1 π (π.symm (w1 i, β i)) = w1 i`. Simplify using `[SplitGL.p1]`. Establish `hw2' : vec2 p1 w = β`.

Use function extensionality and compare the values at `i`. Use `show SplitGL.p2 π (π.symm (w1 i, β i)) = β i`. Simplify using `[SplitGL.p2]`. Establish `hwL : w ∈ LL I v` using `(hchar w).2 ⟨hw1' ▸ hw1, hw2' ▸ hβ⟩`. Use `⟨w, hwL, ?_⟩` and prove the remaining obligations.

Establish `hyi : ((y : GL (Fin I.n) (RV I v))⁻¹ : GL (Fin I.n) (RV I v)) = ((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v))` using `rfl`. Rewrite using `[hyi]`. Apply `extv` to reduce the goal to its premises. Rewrite using `[first_coordinate_vector_sub, v1, first_coordinate_vector_nsmul, hw1', hinvproj]`. Conclude with `hw1e`.

Rewrite using `[second_coordinate_vector_sub, v2, second_coordinate_vector_nsmul, hw2']`. Rewrite using `[vp2 y⁻¹ _ (vec2 p1 (PI.FinKW.vecV I v Rf.z0) + (g : KV I v) • β)]`. Normalize the expressions using the abelian group laws. Rewrite using `[hinvproj, inv_inv, Matrix.add_vecMul, Matrix.smul_vecMul, ← hβe]`. Normalize the expressions using the abelian group laws.
-/
theorem split_unitary_projection_compatibility : BridgeB := by
  intro I g r k e f z Rf _hH v _hv _hsum p1 hp1 T hT
  have hε : ∀ w ∈ LL I v, PI.FinKW.psiV I v Rf.ew • w ∈ LL I v := fun w hw =>
    PI.FinKW.LocTo.intAf_le_mulSet I v Rf.ew_int w hw
  have : Module.Finite I.F I.E := Module.finite_of_finrank_eq_succ I.cm.deg2
  have hdim : Module.finrank (KV I v) (RV I v) = 2 := by
    rw [Module.finrank_baseChange]; exact I.cm.deg2
  have hb := piHom_bijective hdim (sigV I v) p1 (sigV_alg I v) (sigV_sigV I v) hp1.1
    (PI.FinKW.psiV I v Rf.ew) hp1.2.1 hp1.2.2.1
  set π := piEquiv (sigV I v) p1 hb with hπdef
  have hπ : ∀ r, π (sigV I v r) = (π r).swap := piEquiv_sig _ _ (sigV_sigV I v) hb
  have hchar := mem_LL_iff I v _ p1 hp1 hb.1 hε
  obtain ⟨y, hy⟩ := (SplitGL.proj_bijective (sigV I v) π hπ _ (spl_herm_v I v) (spl_det_v I v)).2 T
  subst hy
  have hPm : (I.J.map (inclV I v)).map (SplitGL.p1 π) = Pm I v p1 := by ext i j; rfl

  have v1 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (X : Fin I.n → RV I v),
      vec1 p1 (((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) =
        ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y' : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ
          vec1 p1 X := by
    intro y' X; funext i; exact RingHom.map_mulVec p1 _ _ i
  have v2 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (X : Fin I.n → RV I v),
      vec2 p1 (((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) =
        ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)).map (SplitGL.p2 π) *ᵥ
          vec2 p1 X := by
    intro y' X; funext i; exact RingHom.map_mulVec (p1.comp (sigV I v)) _ _ i
  have vp2 : ∀ (y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) (β β' : Fin I.n → KV I v),
      β' ᵥ* Pm I v p1 = (β ᵥ* Pm I v p1) ᵥ*
        (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y')⁻¹ : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) →
      ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)).map (SplitGL.p2 π) *ᵥ β = β' := by
    intro y' β β' h
    rw [← hPm] at h
    exact second_projection_mulVec_eq (sigV I v) π hπ _ (spl_det_v I v) y' β β' h
  have extv : ∀ X X' : Fin I.n → RV I v, vec1 p1 X = vec1 p1 X' → vec2 p1 X = vec2 p1 X' → X = X' := by
    intro X X' h1 h2
    funext i
    apply hb.1
    exact Prod.ext (congrFun h1 i) (congrFun h2 i)

  have fwd : ∀ y' : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v)),
      (∀ x ∈ Lam1 I v p1, ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y' : GL (Fin I.n) (KV I v)) :
        Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ x ∈ Lam1 I v p1) →
      (∀ β ∈ Lam2 I v p1, ∃ β' ∈ Lam2 I v p1, β' ᵥ* Pm I v p1 = (β ᵥ* Pm I v p1) ᵥ*
        (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y')⁻¹ : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v))) →
      ∀ w ∈ LL I v, ((y' : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ w ∈ LL I v := by
    intro y' h1 h2 w hw
    rw [hchar] at hw ⊢
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨?_, ?_⟩
    · rw [v1]; exact h1 _ hw1
    · rw [v2]
      obtain ⟨β', hβ', eβ⟩ := h2 _ hw2
      rw [vp2 y' _ β' eβ]
      exact hβ'
  have hinvproj : SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y⁻¹ = (SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹ := map_inv _ y
  have fwdY := fwd y (fun x hx => (hT.1 x hx).1) (fun β hβ => (hT.2.1 β hβ).2)
  have fwdYi := fwd y⁻¹ (fun x hx => by rw [hinvproj]; exact (hT.1 x hx).2)
    (fun β hβ => by rw [hinvproj, inv_inv]; exact (hT.2.1 β hβ).1)
  have hYiY : ∀ X : Fin I.n → RV I v,
      (((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) :
        Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ
        (((y : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X) = X := by
    intro X
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]
    have : ((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) *
        (y : GL (Fin I.n) (RV I v)) = 1 := by
      rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
    rw [this, Units.val_one, Matrix.one_mulVec]
  have fixv : ∀ X : Fin I.n → RV I v,
      ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y : GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v)) *ᵥ
        vec1 p1 X = vec1 p1 X →
      (vec2 p1 X ᵥ* Pm I v p1) ᵥ* ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y : GL (Fin I.n) (KV I v)) :
        Matrix (Fin I.n) (Fin I.n) (KV I v)) = vec2 p1 X ᵥ* Pm I v p1 →
      ((y : GL (Fin I.n) (RV I v)) : Matrix (Fin I.n) (Fin I.n) (RV I v)) *ᵥ X = X := by
    intro X h1 h2
    apply extv
    · rw [v1, h1]
    · rw [v2]
      apply vp2
      symm
      calc (vec2 p1 X ᵥ* Pm I v p1) ᵥ*
            (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹ : GL (Fin I.n) (KV I v)) :
              Matrix (Fin I.n) (Fin I.n) (KV I v))
          = ((vec2 p1 X ᵥ* Pm I v p1) ᵥ* ((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y :
              GL (Fin I.n) (KV I v)) : Matrix (Fin I.n) (Fin I.n) (KV I v))) ᵥ*
            (((SplitGL.proj (sigV I v) π (I.J.map (inclV I v)) y)⁻¹ : GL (Fin I.n) (KV I v)) :
              Matrix (Fin I.n) (Fin I.n) (KV I v)) := by rw [h2]
        _ = vec2 p1 X ᵥ* Pm I v p1 := by
          rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  refine ⟨(y : GL (Fin I.n) (RV I v)), y.2, ?_, ?_, ?_⟩
  ·
    intro x
    refine ⟨fun hx => fwdY x hx, fun hx => ?_⟩
    have := fwdYi _ hx
    rwa [hYiY] at this
  ·
    intro a
    obtain ⟨h1, h2, h3, h4⟩ := hT.2.2.1 a
    exact ⟨fixv _ h1 h3, fixv _ h2 h4⟩
  ·
    obtain ⟨w1, hw1, hw1e⟩ := hT.2.2.2.1
    obtain ⟨β, hβ, hβe⟩ := hT.2.2.2.2
    set w : Fin I.n → RV I v := fun i => π.symm (w1 i, β i) with hwdef
    have hw1' : vec1 p1 w = w1 := by
      funext i
      show SplitGL.p1 π (π.symm (w1 i, β i)) = w1 i
      simp [SplitGL.p1]
    have hw2' : vec2 p1 w = β := by
      funext i
      show SplitGL.p2 π (π.symm (w1 i, β i)) = β i
      simp [SplitGL.p2]
    have hwL : w ∈ LL I v := (hchar w).2 ⟨hw1' ▸ hw1, hw2' ▸ hβ⟩
    refine ⟨w, hwL, ?_⟩
    have hyi : ((y : GL (Fin I.n) (RV I v))⁻¹ : GL (Fin I.n) (RV I v)) =
        ((y⁻¹ : Formalism.UG.UJ (sigV I v) (I.J.map (inclV I v))) : GL (Fin I.n) (RV I v)) := rfl
    rw [hyi]
    apply extv
    · rw [first_coordinate_vector_sub, v1, first_coordinate_vector_nsmul, hw1', hinvproj]
      exact hw1e
    · rw [second_coordinate_vector_sub, v2, second_coordinate_vector_nsmul, hw2']
      rw [vp2 y⁻¹ _ (vec2 p1 (PI.FinKW.vecV I v Rf.z0) + (g : KV I v) • β)]
      · abel
      · rw [hinvproj, inv_inv, Matrix.add_vecMul, Matrix.smul_vecMul, ← hβe]
        abel

end PI.UnitaryGroupMassFormula.ScXuExists.BrB
