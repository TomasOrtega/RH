import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FamilyUnifIndexEqOfMarkedLatticeIsometryStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardNonisometricCmTorusDataLeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace PeriodSpaceCount

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_linearIndependent_of_le_finrank (R := R) (M := M) hr.ge`. Establish `h1` using `(Submodule.span R (Set.range v)).finrank_quotient_add_finrank`. Rewrite `h1` using `[finrank_span_eq_card hv, Fintype.card_fin, hr]`. Establish `h2 : Module.IsTorsion R (M ⧸ Submodule.span R (Set.range v))` using `Module.finrank_eq_zero_iff_isTorsion.1 (by omega)`. Take `⟨c, hc, hc0⟩` from `Submodule.annihilator_top_inter_nonZeroDivisors h2`.

Establish `h3 : ∀ m : M, (c • (LinearMap.id : M →ₗ[R] M)) m ∈ Submodule.span R (Set.range v)` using `fun m => by`. Establish `h3` using `Submodule.mem_annihilator.1 hc (Submodule.Quotient.mk m) trivial`. Rewrite `h3` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis. Use `⟨(Module.Basis.span hv).equivFun.toLinearMap ∘ₗ LinearMap.codRestrict _ _ h3, (Module.Basis.span hv).equivFun.injective.comp fun x y h => ?_⟩` and prove the remaining obligations. Conclude with `smul_right_injective M (nonZeroDivisors.ne_zero hc0) (congrArg Subtype.val h)`.
-/
theorem exists_injective_pi {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] {r : ℕ} (hr : Module.finrank R M = r) :
    ∃ φ : M →ₗ[R] (Fin r → R), Function.Injective φ := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) hr.ge
  have h1 := (Submodule.span R (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hv, Fintype.card_fin, hr] at h1
  have h2 : Module.IsTorsion R (M ⧸ Submodule.span R (Set.range v)) :=
    Module.finrank_eq_zero_iff_isTorsion.1 (by omega)
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors h2
  have h3 : ∀ m : M, (c • (LinearMap.id : M →ₗ[R] M)) m ∈ Submodule.span R (Set.range v) := fun m => by
    have h3 := Submodule.mem_annihilator.1 hc (Submodule.Quotient.mk m) trivial
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h3
  refine ⟨(Module.Basis.span hv).equivFun.toLinearMap ∘ₗ LinearMap.codRestrict _ _ h3,
    (Module.Basis.span hv).equivFun.injective.comp fun x y h => ?_⟩
  exact smul_right_injective M (nonZeroDivisors.ne_zero hc0) (congrArg Subtype.val h)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Use `D.fin` as an intermediate fact. Use `D.proj` as an intermediate fact. Take `⟨φ, hφ⟩` from `exists_injective_pi D.rank`. Take `⟨x, hx⟩` from `BoundedBasis.exists_generators_mod_smul (a := (k : 𝓞 E)) (Nat.cast_ne_zero.2 hk.ne') _ D.La φ hφ`. Use `⟨x, fun m => ?_⟩` and prove the remaining obligations.

Take `⟨c, m', h⟩` from `hx m`. Conclude with `⟨c, m', by rw [h, Nat.cast_smul_eq_nsmul]⟩`.
-/
theorem exists_generators (D : Datum H) {k : ℕ} (hk : 0 < k) :
    ∃ x : Fin (D.p + D.q) → D.La, ∀ m : D.La, ∃ (c : Fin (D.p + D.q) → 𝓞 E) (m' : D.La),
      m = ∑ i, c i • x i + k • m' := by
  have := D.fin
  have := D.proj
  obtain ⟨φ, hφ⟩ := exists_injective_pi D.rank
  obtain ⟨x, hx⟩ := BoundedBasis.exists_generators_mod_smul (a := (k : 𝓞 E))
    (Nat.cast_ne_zero.2 hk.ne') _ D.La φ hφ
  refine ⟨x, fun m => ?_⟩
  obtain ⟨c, m', h⟩ := hx m
  exact ⟨c, m', by rw [h, Nat.cast_smul_eq_nsmul]⟩

def Isometric (D D' : Datum H) : Prop :=
  ∃ gam : D.La ≃ₗ[𝓞 E] D'.La, ∀ a b, D'.EF (gam a) (gam b) = D.EF a b

/- English proof (translation)
Assemble the required witnesses or components as `⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩`.
-/
theorem Isometric.refl (D : Datum H) : Isometric D D := ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

/- English proof (translation)
Take `⟨gam, h⟩` from `h`. Conclude with `⟨gam.symm, fun a b => by rw [← h]; simp⟩`.
-/
theorem Isometric.symm {D D' : Datum H} (h : Isometric D D') : Isometric D' D := by
  obtain ⟨gam, h⟩ := h
  exact ⟨gam.symm, fun a b => by rw [← h]; simp⟩

/- English proof (translation)
Take `⟨gam, h⟩` from `h`. Take `⟨gam', h'⟩` from `h'`. Conclude with `⟨gam.trans gam', fun a b => by rw [← h, ← h']; rfl⟩`.
-/
theorem Isometric.trans {D D' D'' : Datum H} (h : Isometric D D') (h' : Isometric D' D'') :
    Isometric D D'' := by
  obtain ⟨gam, h⟩ := h
  obtain ⟨gam', h'⟩ := h'
  exact ⟨gam.trans gam', fun a b => by rw [← h, ← h']; rfl⟩

/- English proof (translation)
Use `D₀.fin` as an intermediate fact. Establish `: Module.Finite ℤ D₀.La` using `Module.Finite.trans (𝓞 E) D₀.La`. Use `datum_free_int D₀` as an intermediate fact. Set `K : AddSubgroup D₀.La` to `(nsmulAddMonoidHom k : D₀.La →+ D₀.La).range`. Establish `hK : Nat.card (D₀.La ⧸ K) = k ^ Module.finrank ℤ D₀.La` using `AddSubgroup.index_range_nsmul D₀.La k`.

Establish `: Finite (D₀.La ⧸ K)` using `Nat.finite_of_card_ne_zero (by rw [hK]; positivity)`. Take `⟨x, hx⟩` from `exists_generators D hk`. Use `choose gam hgam using hs`. Set `F : s → Fin (D.p + D.q) → D₀.La ⧸ K` to `fun i c => QuotientAddGroup.mk (gam i.1 i.2 (t i.1 (x c)))`. Establish `hF : Function.Injective F`.

Introduce `i j hij`. Use `Subtype.ext (hmatch i.1 j.1 ((gam i.1 i.2).trans (gam j.1 j.2).symm) (fun a b => ?_) fun a => ?_)` and prove the remaining obligations. Rewrite using `[← hgam j.1 j.2, ← hgam i.1 i.2]`. Simplify using the standard rewrite rules. Establish `h1 : ∀ c, ∃ e, gam i.1 i.2 (t i.1 (x c)) = gam j.1 j.2 (t j.1 (x c)) + k • e` using `fun c => by`.

Take `⟨e, he⟩` from `QuotientAddGroup.eq.1 (congrFun hij c).symm`. Conclude with `⟨e, by rw [show k • e = _ from he, add_neg_cancel_left]⟩`. Use `choose e he using h1`. Take `⟨c, m', rfl⟩` from `hx a`. Use `⟨(gam j.1 j.2).symm (∑ d, c d • e d + gam i.1 i.2 (t i.1 m') - gam j.1 j.2 (t j.1 m')), ?_⟩` and prove the remaining obligations.

Apply `(gam j.1 j.2).injective` to reduce the goal to its premises. Simplify using `only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_add, map_nsmul, map_sum, map_smul, he, smul_add, smul_sub, Finset.sum_add_distrib, Finset.smul_sum, smul_comm k]`. Normalize the expressions using the abelian group laws. Establish `h2` using `Nat.card_le_card_of_injective F hF`. Rewrite `h2` using `[Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_fun, hK, datum_finrank_int, h₀, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]`.

Use `h2.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Unfold `FD.fdeg`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_isometric_le {D D₀ : Datum H} (h₀ : D₀.p + D₀.q = D.p + D.q) {k : ℕ} (hk : 0 < k)
    {n : ℕ} (Di : Fin n → Datum H) (t : ∀ i, D.La →ₗ[𝓞 E] (Di i).La)
    (hmatch : ∀ (i j : Fin n) (gam : (Di i).La ≃ₗ[𝓞 E] (Di j).La),
      (∀ a b, (Di j).EF (gam a) (gam b) = (Di i).EF a b) →
      (∀ a, ∃ e, gam (t i a) = t j a + k • e) → i = j)
    (s : Finset (Fin n)) (hs : ∀ i ∈ s, Isometric (Di i) D₀) :
    s.card ≤ k ^ (2 * FD.fdeg E * (D.p + D.q) ^ 2) := by
  classical
  have := D₀.fin
  have : Module.Finite ℤ D₀.La := Module.Finite.trans (𝓞 E) D₀.La
  have := datum_free_int D₀
  let K : AddSubgroup D₀.La := (nsmulAddMonoidHom k : D₀.La →+ D₀.La).range
  have hK : Nat.card (D₀.La ⧸ K) = k ^ Module.finrank ℤ D₀.La :=
    AddSubgroup.index_range_nsmul D₀.La k
  have : Finite (D₀.La ⧸ K) := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨x, hx⟩ := exists_generators D hk
  choose gam hgam using hs
  let F : s → Fin (D.p + D.q) → D₀.La ⧸ K := fun i c => QuotientAddGroup.mk (gam i.1 i.2 (t i.1 (x c)))
  have hF : Function.Injective F := by
    intro i j hij
    refine Subtype.ext (hmatch i.1 j.1 ((gam i.1 i.2).trans (gam j.1 j.2).symm) (fun a b => ?_)
      fun a => ?_)
    · rw [← hgam j.1 j.2, ← hgam i.1 i.2]
      simp
    · have h1 : ∀ c, ∃ e, gam i.1 i.2 (t i.1 (x c)) = gam j.1 j.2 (t j.1 (x c)) + k • e := fun c => by
        obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 (congrFun hij c).symm
        exact ⟨e, by rw [show k • e = _ from he, add_neg_cancel_left]⟩
      choose e he using h1
      obtain ⟨c, m', rfl⟩ := hx a
      refine ⟨(gam j.1 j.2).symm (∑ d, c d • e d + gam i.1 i.2 (t i.1 m') - gam j.1 j.2 (t j.1 m')), ?_⟩
      apply (gam j.1 j.2).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_add, map_nsmul, map_sum,
        map_smul, he, smul_add, smul_sub, Finset.sum_add_distrib, Finset.smul_sum, smul_comm k]
      abel
  have h2 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_fun, hK, datum_finrank_int, h₀,
    Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul] at h2
  refine h2.trans (le_of_eq ?_)
  congr 1
  unfold FD.fdeg
  ring

/- English proof (translation)
Set `S : Setoid (Fin n)` to `⟨fun i j => Isometric (Di i) (Di j), fun _ => Isometric.refl _, Isometric.symm, Isometric.trans⟩`. Set `e` to `Finite.equivFin (Quotient S)`. Use `⟨_, fun c => (e.symm c).out, fun c d h => ?_, fun i => ⟨e (Quotient.mk S i), ?_⟩⟩` and prove the remaining obligations. Conclude with `e.symm.injective (Quotient.out_equiv_out.1 h)`. Simplify using `only [Equiv.symm_apply_apply]`.

Conclude with `Isometric.symm (Quotient.mk_out (s := S) i)`.
-/
theorem exists_representatives {n : ℕ} (Di : Fin n → Datum H) :
    ∃ (m : ℕ) (rep : Fin m → Fin n), (∀ c d, Isometric (Di (rep c)) (Di (rep d)) → c = d) ∧
      ∀ i, ∃ c, Isometric (Di i) (Di (rep c)) := by
  let S : Setoid (Fin n) := ⟨fun i j => Isometric (Di i) (Di j),
    fun _ => Isometric.refl _, Isometric.symm, Isometric.trans⟩
  let e := Finite.equivFin (Quotient S)
  refine ⟨_, fun c => (e.symm c).out, fun c d h => ?_, fun i => ⟨e (Quotient.mk S i), ?_⟩⟩
  · exact e.symm.injective (Quotient.out_equiv_out.1 h)
  · simp only [Equiv.symm_apply_apply]
    exact Isometric.symm (Quotient.mk_out (s := S) i)

end PeriodSpaceCount

open PeriodSpaceCount in

/- English proof (translation)
Introduce `hN hT hL E _ _ _ H D l Xo σ g ty h1 hσ hty U r hr ξ AA hξ hξ0 hfg hA0 hAA`. Establish `hk : 0 < l.M'` using `Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos`. Take `⟨m, rep, hrep, hcls⟩` from `exists_representatives U.Di`. Establish `hm` using `GlobalTheory.T.card_nonisometric_cmTorusData_le hN E H D.p D.q r hr ξ AA hξ hξ0 hfg hA0 hAA m (fun c => U.Di (rep c)) (fun c => U.sig _) fun c d gam h => hrep c d ⟨gam, h⟩`. Establish `hn : U.n ≤ m * l.M' ^ (2 * FD.fdeg E * r ^ 2)`.

Establish `h2 : (Finset.univ : Finset (Fin U.n)) ⊆ (Finset.univ : Finset (Fin m)).biUnion fun c => Finset.univ.filter fun i => Isometric (U.Di i) (U.Di (rep c))` using `fun i _ => by`. Take `⟨c, hc⟩` from `hcls i`. Conclude with `Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩`. Establish `h3` using `(Finset.card_le_card h2).trans (Finset.card_biUnion_le_card_mul _ _ (l.M' ^ (2 * FD.fdeg E * r ^ 2)) fun c _ => by`. Rewrite using `[hr]`.

Apply the tactic sequence `exact card_isometric_le (D₀ := U.Di (rep c)) (by rw [(U.sig _).1, (U.sig _).2]) hk U.Di U.t (GlobalTheory.T.familyUnif_index_eq_of_marked_latticeIsometry hT hL E H D l Xo σ g ty h1 hσ hty U) _ fun i hi => (Finset.mem_filter.1 hi).2)`. Simplify using `using h3`. Establish `hmain` using `le_trans (b := (l.M' : ℝ) ^ (2 * FD.fdeg E * r ^ 2) * m) (a := (U.n : ℝ)) (by rw [mul_comm]; exact_mod_cast hn) (mul_le_mul_of_nonneg_left hm (by positivity))`. Use `⟨hmain, fun L hf hL2 hd hrL hfL hM => ?_⟩` and prove the remaining obligations. Establish `h` using `hmain.trans (ClassCount.pow_mul_bound_le_exp (FD.fdeg E) r (d := FD.dE E) hf hL2 (abs_nonneg _) hd hrL hfL (Nat.cast_nonneg _) hM)`.

Establish `h0` using `sq_nonneg (FD.fdeg E * r * L)`. Establish `h' : (0 : ℝ) < U.n` using `by exact_mod_cast U.n_pos`. Combine the linear relations using `[(Real.log_le_iff_le_exp h').2 h]`.
-/
theorem familyUnif_card_le : GlobalTheory.Published.HasseNormSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ U : FamilyUnif Xo σ ty, ∀ (r : ℕ), r = D.p + D.q → ∀ (ξ : E) (AA : Submodule (𝓞 E) E), FD.cc ξ = -ξ → ξ ≠ 0 → AA.FG → AA ≠ ⊥ → (∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x) → (U.n : ℝ) ≤ (l.M' : ℝ) ^ (2 * FD.fdeg E * r ^ 2) * ((1 + 2 * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) * (r * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2)) ∧ ∀ L : ℝ, 16 ≤ FD.fdeg E → 2 ≤ L → Real.log (FD.dE E) ≤ 4 * FD.fdeg E * L → Real.log r ≤ L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log l.M' ≤ 30 * L → Real.log U.n ≤ 41 * (FD.fdeg E * r * L) ^ 2 := by
  intro hN hT hL E _ _ _ H D l Xo σ g ty h1 hσ hty U r hr ξ AA hξ hξ0 hfg hA0 hAA
  classical
  have hk : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  obtain ⟨m, rep, hrep, hcls⟩ := exists_representatives U.Di
  have hm := GlobalTheory.T.card_nonisometric_cmTorusData_le hN E H D.p D.q r hr ξ AA hξ hξ0 hfg hA0 hAA m (fun c => U.Di (rep c))
    (fun c => U.sig _) fun c d gam h => hrep c d ⟨gam, h⟩
  have hn : U.n ≤ m * l.M' ^ (2 * FD.fdeg E * r ^ 2) := by
    have h2 : (Finset.univ : Finset (Fin U.n)) ⊆ (Finset.univ : Finset (Fin m)).biUnion
        fun c => Finset.univ.filter fun i => Isometric (U.Di i) (U.Di (rep c)) := fun i _ => by
      obtain ⟨c, hc⟩ := hcls i
      exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
    have h3 := (Finset.card_le_card h2).trans (Finset.card_biUnion_le_card_mul _ _
      (l.M' ^ (2 * FD.fdeg E * r ^ 2)) fun c _ => by
        rw [hr]
        exact card_isometric_le (D₀ := U.Di (rep c)) (by rw [(U.sig _).1, (U.sig _).2]) hk U.Di U.t
          (GlobalTheory.T.familyUnif_index_eq_of_marked_latticeIsometry hT hL E H D l Xo σ g ty h1 hσ hty U) _ fun i hi => (Finset.mem_filter.1 hi).2)
    simpa using h3
  have hmain := le_trans (b := (l.M' : ℝ) ^ (2 * FD.fdeg E * r ^ 2) * m) (a := (U.n : ℝ))
    (by rw [mul_comm]; exact_mod_cast hn) (mul_le_mul_of_nonneg_left hm (by positivity))
  refine ⟨hmain, fun L hf hL2 hd hrL hfL hM => ?_⟩
  have h := hmain.trans (ClassCount.pow_mul_bound_le_exp (FD.fdeg E) r (d := FD.dE E) hf hL2
    (abs_nonneg _) hd hrL hfL (Nat.cast_nonneg _) hM)
  have h0 := sq_nonneg (FD.fdeg E * r * L)
  have h' : (0 : ℝ) < U.n := by exact_mod_cast U.n_pos
  linarith [(Real.log_le_iff_le_exp h').2 h]

end GlobalTheory
