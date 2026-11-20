import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialCommutesWeightOperator
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KTypeCount
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.DoubleSumReduceSecond

open Finset
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.LK

open Car
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq lowK)
open CompanionTheory.D.DSIC (KRel KUnit KStab)

variable {n : ℕ} {ε : Fin n → Bool}

section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.P6.r26a.PositivityTheory.D.LK.casK_comm hE h`.
-/
theorem casK_comm {E : Fin n → Fin n → Module.End ℂ V} (hE : KRel ε E) {c d : Fin n} (h : ε c = ε d) :
    Commute (E c d) (CasK ε E) :=
  _root_.UpperTheory.Reformulated.B.P6.r26a.PositivityTheory.D.LK.casK_comm hE h

/- English proof (translation)
Establish `h : ∀ g : Fin n → Fin n → M, ∑ i : Pos n, g i.1.1 i.1.2 = ∑ a, ∑ b, if a < b then g a b else 0` using `fun g => by`. Rewrite using `[← Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp) fun p => g p.1 p.2, Finset.sum_filter, Fintype.sum_prod_type]`. Rewrite using `[Finset.sum_add_distrib, h f, h fun a b => f b a, Finset.sum_comm (f := fun a b => if a < b then f b a else 0), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib, show f a a = ∑ b, if a = b then f a b else 0 by simp, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `[h, h.ne, h.not_gt]`. Simplify using `[h]`. Simplify using `[h, h.ne', h.not_gt]`.
-/
theorem sum_pos {M : Type} [AddCommMonoid M] (f : Fin n → Fin n → M) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ i : Pos n, (f i.1.1 i.1.2 + f i.1.2 i.1.1) := by
  have h : ∀ g : Fin n → Fin n → M, ∑ i : Pos n, g i.1.1 i.1.2 = ∑ a, ∑ b, if a < b then g a b else 0 := fun g => by
    rw [← Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp) fun p => g p.1 p.2,
      Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_add_distrib, h f, h fun a b => f b a, Finset.sum_comm (f := fun a b => if a < b then f b a else 0),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, show f a a = ∑ b, if a = b then f a b else 0 by simp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.ne, h.not_gt]
  · simp [h]
  · simp [h, h.ne', h.not_gt]

/- English proof (translation)
Simplify using `only [wt, al, Finset.sum_sub_distrib, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]`.
-/
theorem wt_sum (A : Finset (Pos n)) (c : Fin n) : wt A c = ∑ i ∈ A, al i c := by
  simp only [wt, al, Finset.sum_sub_distrib, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/- English proof (translation)
Use `⟨fun i => (2 : ℂ) • E i.1.2 i.1.1 x, ?_⟩` and prove the remaining obligations. Establish `e : ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • E c c x = ∑ i : Pos n, if cpt ε i then E i.1.1 i.1.1 x - E i.1.2 i.1.2 x else 0`. Establish `: ∀ c, 2 * rhoC ε c = ∑ i ∈ om ε, al i c` using `fun c => by rw [← wt_sum, wt_om]; rfl`. Simplify using `only [this, Complex.ofReal_sum, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_filter]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[al, sub_smul, apply_ite ((↑) : ℝ → ℂ), ite_smul]`. Rewrite using `[e, CasK, sum_pos]`. Simplify using `only [if_true, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply]`. Rewrite using `[add_sub_sub_cancel, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : cpt ε i`. Use `LinearMap.congr_fun (hE i.1.1 i.1.2 i.1.2 i.1.1 hi (Eq.symm hi)) x` as an intermediate fact. Simplify using `only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at this`. Rewrite using `[if_pos hi, if_pos hi, if_pos hi, if_pos (Eq.symm hi), ← this, map_smul, two_smul]`.

Simplify using `only [Module.End.mul_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[if_neg hi, if_neg hi, if_neg hi, if_neg fun h => hi h.symm]`. Simplify using the standard rewrite rules.
-/
theorem casK_inN {E : Fin n → Fin n → Module.End ℂ V} (hE : KRel ε E) (x : V) :
    InN ε E (CasK ε E x - (∑ c, E c c (E c c x) - ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • E c c x)) := by
  refine ⟨fun i => (2 : ℂ) • E i.1.2 i.1.1 x, ?_⟩
  have e : ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • E c c x =
      ∑ i : Pos n, if cpt ε i then E i.1.1 i.1.1 x - E i.1.2 i.1.2 x else 0 := by
    have : ∀ c, 2 * rhoC ε c = ∑ i ∈ om ε, al i c := fun c => by rw [← wt_sum, wt_om]; rfl
    simp only [this, Complex.ofReal_sum, Finset.sum_smul]
    rw [Finset.sum_comm, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [al, sub_smul, apply_ite ((↑) : ℝ → ℂ), ite_smul]
  rw [e, CasK, sum_pos]
  simp only [if_true, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply]
  rw [add_sub_sub_cancel, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : cpt ε i
  · have := LinearMap.congr_fun (hE i.1.1 i.1.2 i.1.2 i.1.1 hi (Eq.symm hi)) x
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [if_pos hi, if_pos hi, if_pos hi, if_pos (Eq.symm hi), ← this, map_smul, two_smul]
    simp only [Module.End.mul_apply]
    abel
  · rw [if_neg hi, if_neg hi, if_neg hi, if_neg fun h => hi h.symm]
    simp

/- English proof (translation)
Introduce `n ε V _ _ E hE B j τ x hx hτ hb`. Set `a : FreeAlgebra ℂ (Fin n × Fin n)` to `∑ c, ∑ d, if ε c = ε d then FreeAlgebra.ι ℂ (c, d) * FreeAlgebra.ι ℂ (d, c) else 0`. Set `b : FreeAlgebra ℂ (Fin n)` to `∑ c, FreeAlgebra.ι ℂ c * FreeAlgebra.ι ℂ c - ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • FreeAlgebra.ι ℂ c`. Establish `ha : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), evK ε E a = CasK ε E` using `fun V _ _ E => by`. Simplify using `only [a, CasK, map_sum]`.

Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Simplify using `[evK, h]`. Conclude with `map_zero _`. Take `⟨w, hw, e⟩` from `hG n ε ε a b (fun _ _ h => h) (fun V _ _ E hE => by`.

Rewrite using `[ha]`. Use `⟨fun i hi => casK_comm hE hi, fun x => ?_⟩` and prove the remaining obligations. Simplify `casK_inN hE x) V E hE B j x hx (fun _ _ _ _ h => h) hb` using `[b, evd, LinearMap.sum_apply]`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, ha, evd_eig _ _ _ hτ]`.

Use `congr 2`. Simplify using `only [b, map_sub, map_sum, map_mul, map_smul, FreeAlgebra.lift_ι_apply, smul_eq_mul, nsq, PI.UpqRep.dot, Pi.sub_apply, ← Finset.sum_sub_distrib]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun c _ => by ring`.
-/
theorem cok_of (hG : GenCO) : COK := by
  intro n ε V _ _ E hE B j τ x hx hτ hb
  let a : FreeAlgebra ℂ (Fin n × Fin n) :=
    ∑ c, ∑ d, if ε c = ε d then FreeAlgebra.ι ℂ (c, d) * FreeAlgebra.ι ℂ (d, c) else 0
  let b : FreeAlgebra ℂ (Fin n) :=
    ∑ c, FreeAlgebra.ι ℂ c * FreeAlgebra.ι ℂ c - ∑ c, ((2 * rhoC ε c : ℝ) : ℂ) • FreeAlgebra.ι ℂ c
  have ha : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      evK ε E a = CasK ε E := fun V _ _ E => by
    simp only [a, CasK, map_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · simp [evK, h]
    · exact map_zero _
  obtain ⟨w, hw, e⟩ := hG n ε ε a b (fun _ _ h => h) (fun V _ _ E hE => by
    rw [ha]
    refine ⟨fun i hi => casK_comm hE hi, fun x => ?_⟩
    simpa [b, evd, LinearMap.sum_apply] using casK_inN hE x) V E hE B j x hx (fun _ _ _ _ h => h) hb
  refine ⟨w, hw, ?_⟩
  rw [← e, ha, evd_eig _ _ _ hτ]
  congr 2
  simp only [b, map_sub, map_sum, map_mul, map_smul, FreeAlgebra.lift_ι_apply, smul_eq_mul, nsq, PI.UpqRep.dot,
    Pi.sub_apply, ← Finset.sum_sub_distrib]
  push_cast
  exact Finset.sum_congr rfl fun c _ => by ring

/- English proof (translation)
Rewrite using `[wt_sum, wt_sum, wt_sum, Finset.sum_filter_add_sum_filter_not]`.
-/
theorem wt_split (A : Finset (Pos n)) (c : Fin n) :
    wt A c = wt (A.filter (cpt ε)) c + wt (A.filter fun i => ¬cpt ε i) c := by
  rw [wt_sum, wt_sum, wt_sum, Finset.sum_filter_add_sum_filter_not]

/- English proof (translation)
The claim follows from `filter_true_of_mem fun _ _ => rfl`.
-/
theorem filter_all (A : Finset (Pos n)) : A.filter (cpt (allT n)) = A := filter_true_of_mem fun _ _ => rfl

end

/- English proof (translation)
Establish `hs : (T.restrict hW).IsSymmetric` using `fun x y => hT x y`. Set `ev` to `hs.eigenvalues rfl`. Set `p : Polynomial ℂ` to `Lagrange.basis (insert (s : ℂ) (univ.image fun i => (ev i : ℂ))) id (s : ℂ)`. Establish `hp1 : p.eval (s : ℂ) = 1` using `Lagrange.eval_basis_self (v := id) (Set.injOn_id _) (mem_insert_self _ _)`. Take `⟨q, hq⟩ : Polynomial.X - Polynomial.C (s : ℂ) ∣ p - 1` from `Polynomial.dvd_iff_isRoot.2 (by simp [hp1])`.

Use `⟨q, fun x hx y hy => ?_⟩` and prove the remaining obligations. Establish `e : y = Polynomial.aeval T p x`. Rewrite using `[hy, eq_add_of_sub_eq' hq, mul_comm]`. Simplify using `[Module.algebraMap_end_apply]`. Rewrite using `[e, show x = ∑ i, (hs.eigenvectorBasis rfl).repr ⟨x, hx⟩ i • (hs.eigenvectorBasis rfl i : V) by`.

Simplify using `using (congrArg Subtype.val ((hs.eigenvectorBasis rfl).sum_repr ⟨x, hx⟩)).symm]`. Simplify using `only [map_sum, map_smul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : T (hs.eigenvectorBasis rfl i : V) = (ev i : ℂ) • (hs.eigenvectorBasis rfl i : V)` using `congrArg Subtype.val (hs.apply_eigenvectorBasis rfl i)`. Rewrite using `[Module.End.aeval_apply_of_mem_apply_eq_smul h1, map_smul, h1]`.

Distinguish the cases in `h : (ev i : ℂ) = s`. Rewrite using `[h]`. Use `module`. Establish `: p.eval (ev i : ℂ) = 0` using `Lagrange.eval_basis_of_ne (v := id) (Ne.symm h) (mem_insert_of_mem (mem_image_of_mem _ (mem_univ i)))`. Simplify using `[this]`.
-/
theorem exists_poly {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : Module.End ℂ V)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ x ∈ W, T x ∈ W) (s : ℝ) :
    ∃ q : Polynomial ℂ, ∀ x ∈ W, ∀ y, y = x + Polynomial.aeval T q (T x - (s : ℂ) • x) → T y = (s : ℂ) • y := by
  classical
  have hs : (T.restrict hW).IsSymmetric := fun x y => hT x y
  let ev := hs.eigenvalues rfl
  let p : Polynomial ℂ := Lagrange.basis (insert (s : ℂ) (univ.image fun i => (ev i : ℂ))) id (s : ℂ)
  have hp1 : p.eval (s : ℂ) = 1 := Lagrange.eval_basis_self (v := id) (Set.injOn_id _) (mem_insert_self _ _)
  obtain ⟨q, hq⟩ : Polynomial.X - Polynomial.C (s : ℂ) ∣ p - 1 := Polynomial.dvd_iff_isRoot.2 (by simp [hp1])
  refine ⟨q, fun x hx y hy => ?_⟩
  have e : y = Polynomial.aeval T p x := by
    rw [hy, eq_add_of_sub_eq' hq, mul_comm]
    simp [Module.algebraMap_end_apply]
  rw [e, show x = ∑ i, (hs.eigenvectorBasis rfl).repr ⟨x, hx⟩ i • (hs.eigenvectorBasis rfl i : V) by
    simpa using (congrArg Subtype.val ((hs.eigenvectorBasis rfl).sum_repr ⟨x, hx⟩)).symm]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : T (hs.eigenvectorBasis rfl i : V) = (ev i : ℂ) • (hs.eigenvectorBasis rfl i : V) :=
    congrArg Subtype.val (hs.apply_eigenvectorBasis rfl i)
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul h1, map_smul, h1]
  by_cases h : (ev i : ℂ) = s
  · rw [h]; module
  · have : p.eval (ev i : ℂ) = 0 := Lagrange.eval_basis_of_ne (v := id) (Ne.symm h)
      (mem_insert_of_mem (mem_image_of_mem _ (mem_univ i)))
    simp [this]

/- English proof (translation)
Introduce `n ε lam V _ _ E hl hE hU hF hmin B j z hB hz hwt hb`. Use `set τ := lowK ε lam + (2 : ℝ) • rhoC ε with hτ`. Establish `hzw : ∀ A, IsWeight E (τ - wt A) (z A)` using `fun A c => by`. Use `congrFun (hwt c) A` as an intermediate fact. Rewrite `this` using `[Ft_apply, filter_all, Pi.smul_apply]`.

Rewrite using `[eq_sub_of_add_eq this, Pi.sub_apply, Complex.ofReal_sub, sub_smul]`. Take `⟨w, hw, e⟩` from `hC n ε V E hE B j (τ - wt B) z hz (fun c => funext fun A => by`. Distinguish the cases in `h : z A = 0`. Simplify using `[Ft_apply, h]`. Rewrite using `[Ft_apply, hzw A c, Pi.smul_apply, ← add_smul, Pi.sub_apply, Pi.sub_apply, wt_split (ε := ε) A, (hz A h).1]`.

Use `congr 1`. Use `push_cast`. Use the proof step `ring) hb`. Use `choose S hS hSt hmem using hF`. Set `W : Submodule ℂ V` to `⨆ A, S (z A)`.

Use `haveI : ∀ A, FiniteDimensional ℂ (S (z A)) := fun A => hS _`. Establish `hWs : KStab ε E W` using `fun a b h v hv => (iSup_le fun A y hy => Submodule.mem_iSup_of_mem A (hSt _ a b h y hy) : W ≤ W.comap (E a b)) hv`. Take `⟨q, hq⟩` from `exists_poly (CasK ε E) (fun x y => by`. Simplify using `only [CasK, LinearMap.sum_apply, sum_inner, inner_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, hU a b h, hU b a h.symm]`. Use the proof step `simp) W (fun x hx => by`. Simplify using `only [CasK, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Conclude with `hWs a b h _ (hWs b a h.symm _ hx)`. Use the proof step `simp) (nsq (τ - wt B - rhoC ε) - nsq (rhoC ε))`. Establish `hcq : ∀ c d, ε c = ε d → ∀ x, Polynomial.aeval (CasK ε E) q (E c d x) = E c d (Polynomial.aeval (CasK ε E) q x)` using `fun c d h x => by`. Establish `: Commute (E c d) (Polynomial.aeval (CasK ε E) q)`.

Rewrite using `[Polynomial.aeval_eq_sum_range]`. Conclude with `Commute.sum_right _ _ _ fun k _ => ((casK_comm hE h).pow_right k).smul_right _`. Conclude with `(LinearMap.congr_fun this.eq x).symm`. Establish `h0 : z + lift n (Polynomial.aeval (CasK ε E) q) (bd ε E w) = 0`. Use function extensionality and compare the values at `A`.

Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[← e]`. Establish `hA : z A ≠ 0` using `fun h => hne (by simp [h])`. Take `⟨ν, y, hy0, hy, hs, hd, hc⟩` from `hM n ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (τ - wt A) _ _ hne (fun c => by`. Simplify using `only [Pi.add_apply, lift_apply, Pi.sub_apply, Pi.smul_apply]`.

Rewrite using `[map_add, ← hcq c c rfl, map_sub, map_smul, ← Module.End.mul_apply, (casK_comm hE rfl).eq, Module.End.mul_apply, hzw A c]`. Simplify using `only [map_smul, map_sub, smul_add, smul_sub, Pi.sub_apply, smul_comm ((τ c - wt A c : ℝ) : ℂ)])`. Use the proof step `(hq (z A) (Submodule.mem_iSup_of_mem A (hmem _)) _ rfl)`. Establish `hA1` using `(hz A hA).1`. Use `absurd (hmin ν y hy0 hy) (not_le.2 (K_type_count n ε lam ν B (A.filter (cpt ε)) hl hB (fun i hi => (mem_filter.1 (hA1.symm ▸ hi :)).2) (fun i hi => (mem_filter.1 hi).2) hd (fun w hw' => ?_) ?_))` and prove the remaining obligations.

Use `hc w hw' using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `c`. Simplify using `only [Pi.sub_apply, wt_split (ε := ε) A, hA1, hτ]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : nsq (τ - wt B - rhoC ε) = nsq (ν + rhoC ε)`.

Use `Complex.ofReal_injective hs` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← h1]`. Use `congr 1`. Rewrite using `[hτ, two_smul]`.

Normalize the expressions using the abelian group laws. Establish `h1 : bd ε E (-lift n (Polynomial.aeval (CasK ε E) q) w) = z`. Rewrite using `[map_neg, ← lift_bd _ E E fun i hi x => hcq _ _ hi x]`. Conclude with `(eq_neg_of_add_eq_zero_left h0).symm`. Take `⟨t, ht1, ht2, ht3⟩` from `hP n (allT n) ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (bd ε E) (differential_commutes_weight_operator n _ ε V E (fun _ _ _ => rfl) hE) τ _ (h1.symm ▸ hwt)`.

Conclude with `⟨t, sup_of_supp hw fun A h => ht3 A (by simp [h]), ht1, ht2.trans h1⟩`.
-/
theorem vanK_of (hC : COK) (hP : WtProj) (hM : WtMajor) : VanK := by
  intro n ε lam V _ _ E hl hE hU hF hmin B j z hB hz hwt hb
  set τ := lowK ε lam + (2 : ℝ) • rhoC ε with hτ
  have hzw : ∀ A, IsWeight E (τ - wt A) (z A) := fun A c => by
    have := congrFun (hwt c) A
    rw [Ft_apply, filter_all, Pi.smul_apply] at this
    rw [eq_sub_of_add_eq this, Pi.sub_apply, Complex.ofReal_sub, sub_smul]
  obtain ⟨w, hw, e⟩ := hC n ε V E hE B j (τ - wt B) z hz (fun c => funext fun A => by
    by_cases h : z A = 0
    · simp [Ft_apply, h]
    · rw [Ft_apply, hzw A c, Pi.smul_apply, ← add_smul, Pi.sub_apply, Pi.sub_apply, wt_split (ε := ε) A, (hz A h).1]
      congr 1; push_cast; ring) hb
  choose S hS hSt hmem using hF
  let W : Submodule ℂ V := ⨆ A, S (z A)
  haveI : ∀ A, FiniteDimensional ℂ (S (z A)) := fun A => hS _
  have hWs : KStab ε E W := fun a b h v hv =>
    (iSup_le fun A y hy => Submodule.mem_iSup_of_mem A (hSt _ a b h y hy) : W ≤ W.comap (E a b)) hv
  obtain ⟨q, hq⟩ := exists_poly (CasK ε E) (fun x y => by
      simp only [CasK, LinearMap.sum_apply, sum_inner, inner_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rw [Module.End.mul_apply, Module.End.mul_apply, hU a b h, hU b a h.symm]
      · simp) W (fun x hx => by
      simp only [CasK, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      split_ifs with h
      · exact hWs a b h _ (hWs b a h.symm _ hx)
      · simp) (nsq (τ - wt B - rhoC ε) - nsq (rhoC ε))
  have hcq : ∀ c d, ε c = ε d → ∀ x, Polynomial.aeval (CasK ε E) q (E c d x) = E c d (Polynomial.aeval (CasK ε E) q x) :=
    fun c d h x => by
      have : Commute (E c d) (Polynomial.aeval (CasK ε E) q) := by
        rw [Polynomial.aeval_eq_sum_range]
        exact Commute.sum_right _ _ _ fun k _ => ((casK_comm hE h).pow_right k).smul_right _
      exact (LinearMap.congr_fun this.eq x).symm
  have h0 : z + lift n (Polynomial.aeval (CasK ε E) q) (bd ε E w) = 0 := by
    funext A
    by_contra hne
    rw [← e] at hne
    have hA : z A ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ν, y, hy0, hy, hs, hd, hc⟩ := hM n ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (τ - wt A) _ _ hne
      (fun c => by
        simp only [Pi.add_apply, lift_apply, Pi.sub_apply, Pi.smul_apply]
        rw [map_add, ← hcq c c rfl, map_sub, map_smul, ← Module.End.mul_apply, (casK_comm hE rfl).eq,
          Module.End.mul_apply, hzw A c]
        simp only [map_smul, map_sub, smul_add, smul_sub, Pi.sub_apply, smul_comm ((τ c - wt A c : ℝ) : ℂ)])
      (hq (z A) (Submodule.mem_iSup_of_mem A (hmem _)) _ rfl)
    have hA1 := (hz A hA).1
    refine absurd (hmin ν y hy0 hy) (not_le.2 (K_type_count n ε lam ν B (A.filter (cpt ε)) hl hB
      (fun i hi => (mem_filter.1 (hA1.symm ▸ hi :)).2) (fun i hi => (mem_filter.1 hi).2) hd (fun w hw' => ?_) ?_))
    · convert hc w hw' using 2
      funext c
      simp only [Pi.sub_apply, wt_split (ε := ε) A, hA1, hτ]
      ring
    · have h1 : nsq (τ - wt B - rhoC ε) = nsq (ν + rhoC ε) := by
        have := Complex.ofReal_injective hs
        linarith
      rw [← h1]
      congr 1
      rw [hτ, two_smul]
      abel
  have h1 : bd ε E (-lift n (Polynomial.aeval (CasK ε E) q) w) = z := by
    rw [map_neg, ← lift_bd _ E E fun i hi x => hcq _ _ hi x]
    exact (eq_neg_of_add_eq_zero_left h0).symm
  obtain ⟨t, ht1, ht2, ht3⟩ := hP n (allT n) ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (bd ε E)
    (differential_commutes_weight_operator n _ ε V E (fun _ _ _ => rfl) hE) τ _ (h1.symm ▸ hwt)
  exact ⟨t, sup_of_supp hw fun A h => ht3 A (by simp [h]), ht1, ht2.trans h1⟩

/- English proof (translation)
Introduce `n ε lam V _ _ E hl hgl hU hF hmin u y hu hy hb`. Establish `hE : KRel ε E` using `fun a b c d _ _ => hgl a b c d`. Establish `hA : KRel (allT n) E` using `fun a b c d _ _ => hgl a b c d`. Use `set τ := lowK ε lam + (2 : ℝ) • rhoC ε with hτ`. Establish `hc` using `differential_commutes_weight_operator n _ (allT n) V E (fun _ _ h => h) hA`.

Take `⟨-, -, -, s4⟩` from `differential_bounded_support n ε V E`. Establish `main : ∀ N (y : Cn n V), (∀ A, y A ≠ 0 → A.card = (om ε).card + 1 ∧ pot (A.filter fun i => ¬cpt ε i) < N) → Wt (allT n) E τ y → bd (allT n) E y = Pi.single (om ε) u → u = 0`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`.

Introduce `y h _ hb`. Take `rfl : y = 0` from `funext fun A => by by_contra h'; exact Nat.not_lt_zero _ (h A h').2`. Simplify using `using (congrFun hb (om ε)).symm`. Consider the case `succ N ih`. Introduce `y h hw hb`.

Set `r : Finset (Pos n) → Cn n V` to `fun B A => if (A.filter fun i => ¬cpt ε i) = B then y A else 0`. Establish `hr : ∀ B, Sup ε B ((om ε).card + 1 - B.card) (r B)` using `fun B A hA => by`. Choose the witnesses or unpack the hypotheses as in `⟨h1, h2⟩ : (A.filter fun i => ¬cpt ε i) = B ∧ y A ≠ 0 := by`. Simplify using `only [r] at hA`. Use `split_ifs at hA with h1`.

Conclude with `⟨h1, hA⟩`. Conclude with `absurd rfl hA`. Use `card_filter_add_card_filter_not (s := A) (cpt ε)` as an intermediate fact. Use `(h A h2).1` as an intermediate fact. Conclude with `⟨h1, by rw [← h1]; omega⟩`.

Establish `hsum : y = ∑ B, r B` using `funext fun A => by simp [r, Finset.sum_apply]`. Establish `hrne : ∀ B A, r B A ≠ 0 → pot B < N + 1 ∧ B.Nonempty ∧ B.card ≤ (om ε).card + 1` using `fun B A hA => by`. Establish `h2 : y A ≠ 0` using `fun h' => hA (by simp [r, h'])`. Establish `h3` using `(hr B A hA).1`. Establish `h4` using `h A h2`.

Use `⟨h3 ▸ h4.2, nonempty_iff_ne_empty.2 fun hB => ?_, h4.1 ▸ h3 ▸ card_filter_le _ _⟩` and prove the remaining obligations. Establish `: A ⊆ om ε` using `fun i hi => mem_filter.2 ⟨mem_univ _, by`. Assume the negation of the conclusion as `hc`. Conclude with `notMem_empty i (hB ▸ h3 ▸ mem_filter.2 ⟨hi, hc⟩)⟩`. Use `card_le_card this` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hex : ∀ B, ∃ t : Cn n V, Wt (allT n) E τ t ∧ (pot B = N → bd ε E t = r B) ∧ (pot B ≠ N → t = 0) ∧ (t = 0 ∨ (B.card ≤ (om ε).card + 1 ∧ Sup ε B ((om ε).card + 1 - B.card + 1) t))`. Introduce `B`. Distinguish the cases in `h0 : pot B = N ∧ r B ≠ 0`. Take `⟨A₀, hA₀⟩` from `Function.ne_iff.1 h0.2`.

Take `⟨-, hBn, hBc⟩` from `hrne B A₀ hA₀`. Take `⟨t, t1, t2, t3⟩` from `hV n ε lam V E hl hE hU hF hmin B _ (r B) hBn (hr B) (fun c => funext fun A => by`. Use `congrFun (hw c) A` as an intermediate fact. Simplify using `only [Ft_apply, Pi.smul_apply, r] at this ⊢`. Use `split_ifs`.

Conclude with `this`. Use the proof step `simp) (funext fun A => by`. Assume the negation of the conclusion as `hne`. Establish `hAB` using `(sup_bd E (hr B) hne).1`. Establish `e` using `congrFun hb A`.

Establish `hAo : A ≠ om ε`. Introduce and unpack `rfl`. Take `⟨i, hi⟩` from `hBn`. Rewrite `hi` using `[← hAB]`. Conclude with `(mem_filter.1 hi).2 (mem_filter.1 (mem_filter.1 hi).1).2`.

Rewrite `e` using `[Pi.single_eq_of_ne hAo, hsum, map_sum, Finset.sum_apply, Finset.sum_eq_single B]`. Apply `hne` to reduce the goal to its premises. Assume the negation of the conclusion as `h'`. Use `(s4 B _ _ (hr B) A (by rw [Pi.sub_apply, e, zero_sub]; exact neg_ne_zero.2 hne)).1` as an intermediate fact. Rewrite `this` using `[hAB]`.

Conclude with `lt_irrefl _ this`. Introduce `B' _ hB'`. Distinguish the cases in `h1 : r B' = 0`. Simplify using `[h1]`. Take `⟨A₁, hA₁⟩` from `Function.ne_iff.1 h1`.

Establish `h2` using `(hrne B' A₁ hA₁).1`. Establish `h3 : bd ε E (r B') A = 0`. Assume the negation of the conclusion as `h3`. Conclude with `hB' ((sup_bd E (hr B') h3).1.symm.trans hAB)`. Assume the negation of the conclusion as `h4`.

Use `(s4 B' _ _ (hr B') A (by rw [Pi.sub_apply, h3, sub_zero]; exact h4)).1` as an intermediate fact. Rewrite `this` using `[hAB]`. Use linear arithmetic over natural numbers and integers. Use the proof step `simp)`. Conclude with `⟨t, t2, fun _ => t3, fun h => absurd h0.1 h, Or.inr ⟨hBc, t1⟩⟩`.

Use `⟨0, fun c => by simp, fun h => ?_, fun _ => rfl, Or.inl rfl⟩` and prove the remaining obligations. Rewrite using `[map_zero]`. Assume the negation of the conclusion as `h'`. Conclude with `h0 ⟨h, Ne.symm h'⟩`. Use `choose t t1 t2 t3 t4 using hex`.

Use `ih (y - ∑ B, bd (allT n) E (t B)) (fun A hA => ?_) (fun c => ?_) ?_` and prove the remaining obligations. Establish `e : (y - ∑ B, bd (allT n) E (t B)) A = ∑ B, ((if pot B = N then 0 else r B A) - (bd (allT n) E (t B) - bd ε E (t B)) A)`. Rewrite using `[Pi.sub_apply, congrFun hsum A, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun B _ => ?_` and prove the remaining obligations. Use `split_ifs with h1`.

Rewrite using `[Pi.sub_apply, t2 B h1]`. Normalize the expressions using the abelian group laws. Simplify using `[t3 B h1]`. Rewrite `hA` using `[e]`. Take `⟨B, -, hB⟩` from `exists_ne_zero_of_sum_ne_zero hA`.

Distinguish the cases in `h1 : pot B = N`. Rewrite `hB` using `[if_pos h1, zero_sub, neg_ne_zero]`. Break down `t4 B with h2 | h2` into its components or cases. Simplify using `[h2] at hB`. Use `s4 B _ _ h2.2 A hB` as an intermediate fact.

Use `h2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `hB` using `[if_neg h1, t3 B h1]`. Establish `hB' : r B A ≠ 0` using `by simpa using hB`. Establish `h2` using `(hrne B A hB').1`.

Establish `h3` using `(hr B A hB').1`. Conclude with `⟨(h A fun h' => hB' (by simp [r, h'])).1, by rw [h3]; omega⟩`. Rewrite using `[map_sub, map_sum, hw c, smul_sub, Finset.smul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun B _ => ?_` and prove the remaining obligations.

Rewrite using `[← Module.End.mul_apply, (hc c).eq, Module.End.mul_apply, t1 B c, map_smul]`. Rewrite using `[map_sub, map_sum, hb, Finset.sum_eq_zero, sub_zero]`. Conclude with `fun B _ => LinearMap.congr_fun (hS n _ V E hA) _`. Take `⟨y', y1, y2, y3⟩` from `hP n (allT n) ε V E hE hU hF _ hc τ y (fun c => funext fun A => by`. Rewrite using `[hb, Ft_apply, filter_all]`.

Distinguish the cases in `e : A = om ε`. Substitute `e` using the available equality. Rewrite using `[Pi.smul_apply, Pi.single_eq_same, hu c, wt_om, ← add_smul, hτ]`. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne e])`.

Use `main ((univ.sup fun A : Finset (Pos n) => pot A) + 1) y' (fun A hA => ⟨?_, ?_⟩) y1 (y2.trans hb)` and prove the remaining obligations. Use `(hy A fun h => hA (y3 A h)).2` as an intermediate fact. Rewrite `this` using `[filter_all]`. Then use the resulting hypothesis. Conclude with `Nat.lt_succ_of_le (Finset.le_sup (f := fun A : Finset (Pos n) => pot A) (mem_univ _))`.
-/
theorem inj_of (hV : VanK) (hP : WtProj) (hS : BdSq) : Inj := by
  intro n ε lam V _ _ E hl hgl hU hF hmin u y hu hy hb
  have hE : KRel ε E := fun a b c d _ _ => hgl a b c d
  have hA : KRel (allT n) E := fun a b c d _ _ => hgl a b c d
  set τ := lowK ε lam + (2 : ℝ) • rhoC ε with hτ
  have hc := differential_commutes_weight_operator n _ (allT n) V E (fun _ _ h => h) hA
  obtain ⟨-, -, -, s4⟩ := differential_bounded_support n ε V E
  have main : ∀ N (y : Cn n V), (∀ A, y A ≠ 0 → A.card = (om ε).card + 1 ∧ pot (A.filter fun i => ¬cpt ε i) < N) →
      Wt (allT n) E τ y → bd (allT n) E y = Pi.single (om ε) u → u = 0 := by
    intro N
    induction N with
    | zero =>
      intro y h _ hb
      obtain rfl : y = 0 := funext fun A => by by_contra h'; exact Nat.not_lt_zero _ (h A h').2
      simpa using (congrFun hb (om ε)).symm
    | succ N ih =>
      intro y h hw hb
      let r : Finset (Pos n) → Cn n V := fun B A => if (A.filter fun i => ¬cpt ε i) = B then y A else 0
      have hr : ∀ B, Sup ε B ((om ε).card + 1 - B.card) (r B) := fun B A hA => by
        obtain ⟨h1, h2⟩ : (A.filter fun i => ¬cpt ε i) = B ∧ y A ≠ 0 := by
          simp only [r] at hA
          split_ifs at hA with h1
          · exact ⟨h1, hA⟩
          · exact absurd rfl hA
        have := card_filter_add_card_filter_not (s := A) (cpt ε)
        have := (h A h2).1
        exact ⟨h1, by rw [← h1]; omega⟩
      have hsum : y = ∑ B, r B := funext fun A => by simp [r, Finset.sum_apply]
      have hrne : ∀ B A, r B A ≠ 0 → pot B < N + 1 ∧ B.Nonempty ∧ B.card ≤ (om ε).card + 1 := fun B A hA => by
        have h2 : y A ≠ 0 := fun h' => hA (by simp [r, h'])
        have h3 := (hr B A hA).1
        have h4 := h A h2
        refine ⟨h3 ▸ h4.2, nonempty_iff_ne_empty.2 fun hB => ?_, h4.1 ▸ h3 ▸ card_filter_le _ _⟩
        have : A ⊆ om ε := fun i hi => mem_filter.2 ⟨mem_univ _, by
          by_contra hc; exact notMem_empty i (hB ▸ h3 ▸ mem_filter.2 ⟨hi, hc⟩)⟩
        have := card_le_card this
        omega
      have hex : ∀ B, ∃ t : Cn n V, Wt (allT n) E τ t ∧ (pot B = N → bd ε E t = r B) ∧ (pot B ≠ N → t = 0) ∧
          (t = 0 ∨ (B.card ≤ (om ε).card + 1 ∧ Sup ε B ((om ε).card + 1 - B.card + 1) t)) := by
        intro B
        by_cases h0 : pot B = N ∧ r B ≠ 0
        · obtain ⟨A₀, hA₀⟩ := Function.ne_iff.1 h0.2
          obtain ⟨-, hBn, hBc⟩ := hrne B A₀ hA₀
          obtain ⟨t, t1, t2, t3⟩ := hV n ε lam V E hl hE hU hF hmin B _ (r B) hBn (hr B) (fun c => funext fun A => by
              have := congrFun (hw c) A
              simp only [Ft_apply, Pi.smul_apply, r] at this ⊢
              split_ifs
              · exact this
              · simp) (funext fun A => by
              by_contra hne
              have hAB := (sup_bd E (hr B) hne).1
              have e := congrFun hb A
              have hAo : A ≠ om ε := by
                rintro rfl
                obtain ⟨i, hi⟩ := hBn
                rw [← hAB] at hi
                exact (mem_filter.1 hi).2 (mem_filter.1 (mem_filter.1 hi).1).2
              rw [Pi.single_eq_of_ne hAo, hsum, map_sum, Finset.sum_apply, Finset.sum_eq_single B] at e
              · apply hne
                by_contra h'
                have := (s4 B _ _ (hr B) A (by rw [Pi.sub_apply, e, zero_sub]; exact neg_ne_zero.2 hne)).1
                rw [hAB] at this
                exact lt_irrefl _ this
              · intro B' _ hB'
                by_cases h1 : r B' = 0
                · simp [h1]
                obtain ⟨A₁, hA₁⟩ := Function.ne_iff.1 h1
                have h2 := (hrne B' A₁ hA₁).1
                have h3 : bd ε E (r B') A = 0 := by
                  by_contra h3; exact hB' ((sup_bd E (hr B') h3).1.symm.trans hAB)
                by_contra h4
                have := (s4 B' _ _ (hr B') A (by rw [Pi.sub_apply, h3, sub_zero]; exact h4)).1
                rw [hAB] at this
                omega
              · simp)
          exact ⟨t, t2, fun _ => t3, fun h => absurd h0.1 h, Or.inr ⟨hBc, t1⟩⟩
        · refine ⟨0, fun c => by simp, fun h => ?_, fun _ => rfl, Or.inl rfl⟩
          rw [map_zero]
          by_contra h'
          exact h0 ⟨h, Ne.symm h'⟩
      choose t t1 t2 t3 t4 using hex
      refine ih (y - ∑ B, bd (allT n) E (t B)) (fun A hA => ?_) (fun c => ?_) ?_
      · have e : (y - ∑ B, bd (allT n) E (t B)) A =
            ∑ B, ((if pot B = N then 0 else r B A) - (bd (allT n) E (t B) - bd ε E (t B)) A) := by
          rw [Pi.sub_apply, congrFun hsum A, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun B _ => ?_
          split_ifs with h1
          · rw [Pi.sub_apply, t2 B h1]; abel
          · simp [t3 B h1]
        rw [e] at hA
        obtain ⟨B, -, hB⟩ := exists_ne_zero_of_sum_ne_zero hA
        by_cases h1 : pot B = N
        · rw [if_pos h1, zero_sub, neg_ne_zero] at hB
          rcases t4 B with h2 | h2
          · simp [h2] at hB
          · have := s4 B _ _ h2.2 A hB
            have := h2.1
            omega
        · rw [if_neg h1, t3 B h1] at hB
          have hB' : r B A ≠ 0 := by simpa using hB
          have h2 := (hrne B A hB').1
          have h3 := (hr B A hB').1
          exact ⟨(h A fun h' => hB' (by simp [r, h'])).1, by rw [h3]; omega⟩
      · rw [map_sub, map_sum, hw c, smul_sub, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [← Module.End.mul_apply, (hc c).eq, Module.End.mul_apply, t1 B c, map_smul]
      · rw [map_sub, map_sum, hb, Finset.sum_eq_zero, sub_zero]
        exact fun B _ => LinearMap.congr_fun (hS n _ V E hA) _
  obtain ⟨y', y1, y2, y3⟩ := hP n (allT n) ε V E hE hU hF _ hc τ y (fun c => funext fun A => by
    rw [hb, Ft_apply, filter_all]
    by_cases e : A = om ε
    · subst e
      rw [Pi.smul_apply, Pi.single_eq_same, hu c, wt_om, ← add_smul, hτ]
      simp
    · simp [Pi.single_eq_of_ne e])
  refine main ((univ.sup fun A : Finset (Pos n) => pot A) + 1) y' (fun A hA => ⟨?_, ?_⟩) y1 (y2.trans hb)
  · have := (hy A fun h => hA (y3 A h)).2
    rwa [filter_all] at this
  · exact Nat.lt_succ_of_le (Finset.le_sup (f := fun A : Finset (Pos n) => pot A) (mem_univ _))

end CompanionTheory.D.LK
