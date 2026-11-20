import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LinearIndependentOfCommSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ A _ _ E _ _ _ e Φ hcard hdim hmul hcomm hnd T lam hlam Wt hWt χ U hU hstab`. Distinguish the cases in `hbot : U = ⊥`. Conclude with `Or.inl hbot`. Use `right`. Take `⟨u, huU, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`.

Use `haveI : Nontrivial E := ⟨⟨u, 0, hu0⟩⟩`. Establish `hel : ∀ a b c, e (a * b) c = e a c * e b c`. Introduce `a b c`. Take `⟨k, hk⟩` from `hmul a b`. Establish `h1` using `hcomm (a * b) c u`.

Rewrite `h1` using `[hk, hk, hcomm b c u, map_smul, hcomm a c, map_smul, smul_smul, smul_smul, smul_smul]`. Establish `h2 : Φ c (Φ a (Φ b u)) ≠ 0` using `fun h => hu0 (by simpa using h)`. Establish `h3` using `smul_left_injective F h2 h1`. Apply `Units.ext` to reduce the goal to its premises. Establish `hk0 : (k : F) ≠ 0` using `k.ne_zero`.

Apply `mul_left_cancel₀ hk0` to reduce the goal to its premises. Rewrite using `[Units.val_mul]`. Take the linear combination `-h3`. Establish `he1 : ∀ c, e 1 c = 1`. Introduce `c`.

Use `hel 1 1 c` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `(mul_eq_left.mp this.symm)`. Establish `hinj : Function.Injective fun a b => (e a b : F)`. Introduce `a a' h`.

Establish `: a * a'⁻¹ = 1`. Apply `hnd` to reduce the goal to its premises. Introduce `b`. Establish `hb : e a b = e a' b` using `Units.ext (congrFun h b)`. Rewrite using `[hel, hb, ← hel, mul_inv_cancel, he1]`.

Conclude with `mul_inv_eq_one.mp this`. Establish `hli : LinearIndependent F fun a => (Φ a : E →ₗ[F] E)` using `linearIndependent_of_comm_smul _ _ (fun a => (Φ a).injective) (fun a b v => hcomm a b v) hinj`. Use `haveI := Fintype.ofFinite A`. Establish `hspan : Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)) = ⊤`. Apply `hli.span_eq_top_of_card_eq_finrank'` to reduce the goal to its premises.

Rewrite using `[Module.finrank_linearMap, ← sq, hdim, Nat.card_eq_fintype_card]`. Use `le_antisymm hU fun v hv => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : E →ₗ[F] E, f u = v := by`. Take `⟨φ, hφ⟩` from `Module.Projective.exists_dual_eq_one F hu0`. Conclude with `⟨φ.smulRight v, by simp [hφ]⟩`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun F).mp (hspan ▸ Submodule.mem_top : f ∈ Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)))`. Establish `hvs : v = ∑ a, c a • Φ a u`. Rewrite using `[← hf, ← hc]`. Simplify using the standard rewrite rules. Establish `hu` using `(hWt χ u).mp (hU huU)`.

Establish `hv'` using `(hWt χ v).mp hv`. Establish `hlamΦ : ∀ (t : T) a, lam t (Φ a u) = ((χ t : F) * (e t a : F)) • Φ a u`. Introduce `t a`. Take `⟨k, hk⟩` from `hlam t`. Rewrite using `[hk, hcomm, smul_comm, ← map_smul, ← hk, hu, map_smul, smul_smul, mul_comm]`.

Establish `hvt : ∀ t : T, v = ∑ a, (c a * (e t a : F)) • Φ a u`. Introduce `t`. Establish `h1` using `hv' t`. Establish `h0 : (χ t : F) ≠ 0` using `(χ t).ne_zero`. Apply `smul_right_injective E h0` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[← h1]`. Use `conv_lhs => rw [hvs]`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hlamΦ, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hT : (Fintype.card T : F) ≠ 0`. Introduce `h`.

Apply `hcard` to reduce the goal to its premises. Rewrite using `[← Subgroup.card_mul_index T, Nat.cast_mul, Nat.card_eq_fintype_card, h, zero_mul]`. Establish `hsum : (Fintype.card T : F) • v = ∑ a, (c a * ∑ t : T, (e t a : F)) • Φ a u`. Establish `: (Fintype.card T : F) • v = ∑ _t : T, v`. Rewrite using `[Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]`.

Rewrite using `[this, Finset.sum_congr rfl fun t _ => hvt t, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_smul]`. Rewrite using `[← U.smul_mem_iff hT, hsum]`. Use `U.sum_mem fun a _ => ?_` and prove the remaining obligations.

Distinguish the cases in `ha : ∀ t : T, e t a = 1`. Conclude with `U.smul_mem _ (hstab a ha u huU)`. Set `ψ : T →* F` to `{ toFun := fun t => (e t a : F) map_one' := by simp [he1] map_mul' := fun s t => by simp [hel] }`. Establish `hψ : ψ ≠ 1`. Introduce `h`.

Apply `ha` to reduce the goal to its premises. Introduce `t`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `DFunLike.congr_fun h t`. Use `sum_hom_units_eq_zero ψ hψ` as an intermediate fact.

Establish `h2 : ∑ t : T, (e t a : F) = 0` using `this`. Rewrite using `[h2, mul_zero, zero_smul]`. Conclude with `U.zero_mem`.
-/
theorem heisenberg_weightSpace_irreducible : ∀ (F : Type) [Field F] [IsAlgClosed F] (A : Type) [CommGroup A] [Finite A] (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)), (Nat.card A : F) ≠ 0 → Module.finrank F E ^ 2 = Nat.card A → (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) → (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ (T : Subgroup A) (lam : T →* (E ≃ₗ[F] E)), (∀ t : T, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v) → ∀ Wt : (T →* Fˣ) → Submodule F E, (∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v) → ∀ (χ : T →* Fˣ) (U : Submodule F E), U ≤ Wt χ → (∀ h : A, (∀ t : T, e t h = 1) → ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = Wt χ := by
  classical
  intro F _ _ A _ _ E _ _ _ e Φ hcard hdim hmul hcomm hnd T lam hlam Wt hWt χ U hU hstab
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  haveI : Nontrivial E := ⟨⟨u, 0, hu0⟩⟩

  have hel : ∀ a b c, e (a * b) c = e a c * e b c := by
    intro a b c
    obtain ⟨k, hk⟩ := hmul a b
    have h1 := hcomm (a * b) c u
    rw [hk, hk, hcomm b c u, map_smul, hcomm a c, map_smul, smul_smul, smul_smul, smul_smul] at h1
    have h2 : Φ c (Φ a (Φ b u)) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 h1
    apply Units.ext
    have hk0 : (k : F) ≠ 0 := k.ne_zero
    apply mul_left_cancel₀ hk0
    rw [Units.val_mul]
    linear_combination -h3
  have he1 : ∀ c, e 1 c = 1 := by
    intro c
    have := hel 1 1 c
    rw [_root_.mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinj : Function.Injective fun a b => (e a b : F) := by
    intro a a' h
    have : a * a'⁻¹ = 1 := by
      apply hnd
      intro b
      have hb : e a b = e a' b := Units.ext (congrFun h b)
      rw [hel, hb, ← hel, mul_inv_cancel, he1]
    exact mul_inv_eq_one.mp this
  have hli : LinearIndependent F fun a => (Φ a : E →ₗ[F] E) :=
    linearIndependent_of_comm_smul _ _ (fun a => (Φ a).injective) (fun a b v => hcomm a b v) hinj
  haveI := Fintype.ofFinite A
  have hspan : Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, ← sq, hdim, Nat.card_eq_fintype_card]
  refine le_antisymm hU fun v hv => ?_
  obtain ⟨f, hf⟩ : ∃ f : E →ₗ[F] E, f u = v := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hu0
    exact ⟨φ.smulRight v, by simp [hφ]⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)))
  have hvs : v = ∑ a, c a • Φ a u := by
    rw [← hf, ← hc]; simp
  have hu := (hWt χ u).mp (hU huU)
  have hv' := (hWt χ v).mp hv
  have hlamΦ : ∀ (t : T) a, lam t (Φ a u) = ((χ t : F) * (e t a : F)) • Φ a u := by
    intro t a
    obtain ⟨k, hk⟩ := hlam t
    rw [hk, hcomm, smul_comm, ← map_smul, ← hk, hu, map_smul, smul_smul, mul_comm]
  have hvt : ∀ t : T, v = ∑ a, (c a * (e t a : F)) • Φ a u := by
    intro t
    have h1 := hv' t
    have h0 : (χ t : F) ≠ 0 := (χ t).ne_zero
    apply smul_right_injective E h0
    simp only
    rw [← h1]
    conv_lhs => rw [hvs]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hlamΦ, smul_smul, smul_smul]
    congr 1; ring
  have hT : (Fintype.card T : F) ≠ 0 := by
    intro h
    apply hcard
    rw [← Subgroup.card_mul_index T, Nat.cast_mul, Nat.card_eq_fintype_card, h, zero_mul]
  have hsum : (Fintype.card T : F) • v = ∑ a, (c a * ∑ t : T, (e t a : F)) • Φ a u := by
    have : (Fintype.card T : F) • v = ∑ _t : T, v := by
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this, Finset.sum_congr rfl fun t _ => hvt t, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_smul]
  rw [← U.smul_mem_iff hT, hsum]
  refine U.sum_mem fun a _ => ?_
  by_cases ha : ∀ t : T, e t a = 1
  · exact U.smul_mem _ (hstab a ha u huU)
  · let ψ : T →* F :=
      { toFun := fun t => (e t a : F)
        map_one' := by simp [he1]
        map_mul' := fun s t => by simp [hel] }
    have hψ : ψ ≠ 1 := by
      intro h
      apply ha
      intro t
      apply Units.ext
      exact DFunLike.congr_fun h t
    have := sum_hom_units_eq_zero ψ hψ
    have h2 : ∑ t : T, (e t a : F) = 0 := this
    rw [h2, mul_zero, zero_smul]
    exact U.zero_mem

end GlobalTheory
