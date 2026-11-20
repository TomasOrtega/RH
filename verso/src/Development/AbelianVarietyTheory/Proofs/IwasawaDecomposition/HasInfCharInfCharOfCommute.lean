import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep
open Polynomial

namespace GlobalTheory.CuspRep

/- English proof (translation)
Set `Q : Finset (Fin n) → ℂ[X]` to `fun S => ∏ k ∈ Sᶜ, (X - C ((k : ℂ) - s))`. Establish `hQm : ∀ S, (Q S).Monic` using `fun S => monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _`. Establish `hQd : ∀ S, (Q S).natDegree = Sᶜ.card` using `fun S => by`. Simplify using `only [Q]`. Rewrite using `[natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]`.

Simplify using `only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]`. Set `R : ℂ[X]` to `∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)), C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S`. Establish `h0 : (Q ∅).degree = n`. Rewrite using `[degree_eq_natDegree (hQm _).ne_zero, hQd]`. Simplify using the standard rewrite rules.

Establish `hR : R.degree < (Q ∅).degree`. Rewrite using `[h0]`. Use `(degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun S hS => ?_)` and prove the remaining obligations. Use `degree_le_natDegree.trans_lt ?_` and prove the remaining obligations. Establish `h1 : (C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S).natDegree < n`.

Use `(natDegree_C_mul_le _ _).trans_lt ?_` and prove the remaining obligations. Rewrite using `[hQd, Finset.card_compl, Fintype.card_fin]`. Establish `h2` using `Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS))`. Establish `h3 : S.card ≤ n` using `by simpa using Finset.card_le_univ S`. Use linear arithmetic over natural numbers and integers.

Conclude with `h1` after adjusting the coercions. Establish `hm : (Q ∅ + R).Monic` using `(hQm _).add_of_left hR`. Establish `hd : (Q ∅ + R).natDegree = n`. Rewrite using `[natDegree_eq_of_degree_eq_some ((degree_add_eq_left_of_degree_lt hR).trans h0)]`. Establish `hc : Multiset.card (Q ∅ + R).roots = (Q ∅ + R).natDegree` using `IsAlgClosed.card_roots_eq_natDegree`.

Use `⟨(Q ∅ + R).roots.map Neg.neg, by rw [Multiset.card_map, hc, hd], fun u => ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (eval u) (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc)`. Establish `e2 : ((Q ∅ + R).roots.map Neg.neg |>.map (u + ·)).prod = eval u (Q ∅ + R)`. Rewrite using `[← e]`. Simplify using `[eval_multiset_prod, Multiset.map_map, sub_eq_add_neg]`.

Establish `hQe : ∀ S, eval u (Q S) = ∏ k ∈ Sᶜ, (u + s - (k : ℂ))` using `fun S => by`. Simplify using `only [Q, eval_prod, eval_sub, eval_X, eval_C]`. Conclude with `Finset.prod_congr rfl fun k _ => by ring`. Rewrite using `[e2, GlobalTheory.CapelliTop.qdet_expand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin n))), GlobalTheory.CapelliTop.subdet_empty]`. Simplify using `only [R, eval_add, eval_finset_sum, eval_mul, eval_C, hQe, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add, map_sum, map_smul, Module.End.one_apply, hf, smul_eq_mul, mul_one]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun S _ => mul_comm _ _`.
-/
theorem exists_multiset_qdet {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (F : Fin n → Fin n → Module.End ℂ M)
    (s : ℂ) (φ : M) (f : M →ₗ[ℂ] ℂ) (hf : f φ = 1) :
    ∃ m : Multiset ℂ, Multiset.card m = n ∧ ∀ u, f (Formalism.REAL.qdet F (u + s) φ) = (m.map (u + ·)).prod := by
  classical
  let Q : Finset (Fin n) → ℂ[X] := fun S => ∏ k ∈ Sᶜ, (X - C ((k : ℂ) - s))
  have hQm : ∀ S, (Q S).Monic := fun S => monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
  have hQd : ∀ S, (Q S).natDegree = Sᶜ.card := fun S => by
    simp only [Q]
    rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  let R : ℂ[X] := ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)), C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S
  have h0 : (Q ∅).degree = n := by
    rw [degree_eq_natDegree (hQm _).ne_zero, hQd]; simp
  have hR : R.degree < (Q ∅).degree := by
    rw [h0]
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun S hS => ?_)
    refine degree_le_natDegree.trans_lt ?_
    have h1 : (C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S).natDegree < n := by
      refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [hQd, Finset.card_compl, Fintype.card_fin]
      have h2 := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS))
      have h3 : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega
    exact_mod_cast h1
  have hm : (Q ∅ + R).Monic := (hQm _).add_of_left hR
  have hd : (Q ∅ + R).natDegree = n := by
    rw [natDegree_eq_of_degree_eq_some ((degree_add_eq_left_of_degree_lt hR).trans h0)]
  have hc : Multiset.card (Q ∅ + R).roots = (Q ∅ + R).natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨(Q ∅ + R).roots.map Neg.neg, by rw [Multiset.card_map, hc, hd], fun u => ?_⟩
  have e := congrArg (eval u) (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc)
  have e2 : ((Q ∅ + R).roots.map Neg.neg |>.map (u + ·)).prod = eval u (Q ∅ + R) := by
    rw [← e]
    simp [eval_multiset_prod, Multiset.map_map, sub_eq_add_neg]
  have hQe : ∀ S, eval u (Q S) = ∏ k ∈ Sᶜ, (u + s - (k : ℂ)) := fun S => by
    simp only [Q, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_congr rfl fun k _ => by ring
  rw [e2, GlobalTheory.CapelliTop.qdet_expand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin n))),
    GlobalTheory.CapelliTop.subdet_empty]
  simp only [R, eval_add, eval_finset_sum, eval_mul, eval_C, hQe, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_add, map_sum, map_smul, Module.End.one_apply, hf, smul_eq_mul, mul_one]
  congr 1
  exact Finset.sum_congr rfl fun S _ => mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 π.ne_bot`. Use `set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU`. Establish `hfin : FiniteDimensional ℂ U` using `(π.cusp φ hφ).1.zfin`. Establish `hle : U ≤ π.V` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `Zalg_stable (fun X => π.stable (.lie X)) hy φ hφ)`. Establish `hst : ∀ x ∈ U, z x ∈ U` using `fun x hx => by`. Establish `: U ≤ U.comap z` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)`.

Conclude with `this hx`. Establish `hφU : φ ∈ U` using `Submodule.subset_span ⟨1, one_mem _, rfl⟩`. Establish `: Nontrivial U` using `⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩`. Take `⟨c, hc'⟩` from `Module.End.exists_eigenvalue (z.restrict hst)`. Take `⟨v, hv⟩` from `hc'.exists_hasEigenvector`.

Establish `hv1 : z v.1 = c • v.1` using `congrArg Subtype.val hv.apply_eq_smul`. Use `⟨c, fun ψ hψ => ?_⟩` and prove the remaining obligations. Break down `π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by` into its components or cases. Establish `h1 : z x = c • x` using `Module.End.mem_eigenspace_iff.1 hx.2`. Use `Module.End.mem_eigenspace_iff.2 ?_` and prove the remaining obligations.

Rewrite using `[← map_smul, ← h1]`. Conclude with `LinearMap.congr_fun (hc o).eq x⟩) with h | h`. Establish `: v.1 ∈ π.V ⊓ z.eigenspace c` using `⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩`. Rewrite `this` using `[h]`. Conclude with `absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2`.

Rewrite `hψ` using `[← h]`. Conclude with `Module.End.mem_eigenspace_iff.1 hψ.2`.
-/
theorem CuspSub.exists_scalar (π : CuspSub E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (π.cusp φ hφ).1.zfin
  have hle : U ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => π.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ π.V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

/- English proof (translation)
Introduce `E _ _ _ a hc π τ`. It suffices to establish `h : ∃ m, π.HasInfChar τ m by`. Take `⟨m, h⟩` from `h`. Rewrite using `[h.infChar_eq]` and apply the resulting hypothesis. Proceed by induction on `π using Quotient.inductionOn with`.

Consider the case `h π`. Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 π.ne_bot`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one ℂ h0`. Take `⟨m, hm, h⟩` from `exists_multiset_qdet (Eop (a := a) τ) (((a : ℂ) - 1) / 2) φ f hf`. Use `⟨m, hm, fun u ψ hψ => ?_⟩` and prove the remaining obligations.

Take `⟨c, h1⟩` from `π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (hc τ u)`. Establish `h2 : f (cap τ u φ) = _` using `h u`. Rewrite `h2` using `[h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one]`. Rewrite using `[h1 ψ hψ, h2]`.
-/
theorem hasInfChar_infChar_of_commute : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o)) → ∀ (π : CG E a) (τ : E →+* ℂ), π.HasInfChar τ (π.infChar τ) := by
  intro E _ _ _ a hc π τ
  suffices h : ∃ m, π.HasInfChar τ m by
    obtain ⟨m, h⟩ := h
    rwa [h.infChar_eq]
  induction π using Quotient.inductionOn with
  | h π =>
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := a) τ) (((a : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (hc τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CuspRep
