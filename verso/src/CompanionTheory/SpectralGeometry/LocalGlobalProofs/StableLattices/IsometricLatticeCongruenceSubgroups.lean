import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.CartanU

section Form

variable {L : Type} [NontriviallyNormedField L] {n : ℕ}

def form (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) : L :=
  dotProduct (s ∘ x) (J.mulVec y)

/- English proof (translation)
Use `⟨fun x y z => ?_, fun a x y => ?_, fun x y => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `[form, Matrix.mulVec_add, dotProduct_add]`. Simplify using `[form, Matrix.mulVec_smul, dotProduct_smul]`. Establish `hJ' : ∀ i j, s (J i j) = J j i` using `fun i j => by`. Use `congrFun (congrFun hJ j) i` as an intermediate fact.

Simplify `this` using `[Matrix.transpose_apply, Matrix.map_apply]`. Simplify using `only [form, dotProduct, Matrix.mulVec, Function.comp, map_sum, map_mul, hs, Finset.mul_sum, hJ']`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : Matrix.vecMul (s ∘ x) J = 0`. Use function extensionality and compare the values at `j`. Use `hx (Pi.single j 1)` as an intermediate fact. Simplify `this` using `[form, Matrix.vecMul, dotProduct, Matrix.mulVec, Pi.single_apply]`. Establish `h2 : s ∘ x = 0` using `Matrix.eq_zero_of_vecMul_eq_zero hd h1`.

Use function extensionality and compare the values at `i`. Establish `h3` using `congrFun h2 i`. Establish `h4 : s (x i) = 0` using `h3`. Simplify using `using h4`.
-/
theorem form_isHerm (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (hs : ∀ x, s (s x) = x)
    (hJ : (J.map s).transpose = J) (hd : J.det ≠ 0) : IsHerm s (form s J) := by
  refine ⟨fun x y z => ?_, fun a x y => ?_, fun x y => ?_, fun x hx => ?_⟩
  · simp [form, Matrix.mulVec_add, dotProduct_add]
  · simp [form, Matrix.mulVec_smul, dotProduct_smul]
  · have hJ' : ∀ i j, s (J i j) = J j i := fun i j => by
      have := congrFun (congrFun hJ j) i
      simpa [Matrix.transpose_apply, Matrix.map_apply] using this
    simp only [form, dotProduct, Matrix.mulVec, Function.comp, map_sum, map_mul, hs, Finset.mul_sum, hJ']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · have h1 : Matrix.vecMul (s ∘ x) J = 0 := by
      funext j
      have := hx (Pi.single j 1)
      simpa [form, Matrix.vecMul, dotProduct, Matrix.mulVec, Pi.single_apply] using this
    have h2 : s ∘ x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hd h1
    funext i
    have h3 := congrFun h2 i
    have h4 : s (x i) = 0 := h3
    simpa using h4

def toE : GL (Fin n) L →* ((Fin n → L) ≃ₗ[L] (Fin n → L)) where
  toFun g := LinearEquiv.ofLinear (Matrix.mulVecLin g.1) (Matrix.mulVecLin (g⁻¹).1)
    (by rw [← Matrix.mulVecLin_mul]; simp) (by rw [← Matrix.mulVecLin_mul]; simp)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [Matrix.mulVec_mulVec]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toE_apply (g : GL (Fin n) L) (x : Fin n → L) : toE g x = g.1.mulVec x := rfl

/- English proof (translation)
Introduce `a b h`. Apply `Units.ext` to reduce the goal to its premises. Apply `Matrix.mulVec_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Conclude with `congrArg (fun t : (Fin n → L) ≃ₗ[L] (Fin n → L) => t x) h`.
-/
theorem toE_injective : Function.Injective (toE : GL (Fin n) L → _) := by
  intro a b h
  apply Units.ext
  apply Matrix.mulVec_injective
  funext x
  exact congrArg (fun t : (Fin n → L) ≃ₗ[L] (Fin n → L) => t x) h

def ofE (t : (Fin n → L) ≃ₗ[L] (Fin n → L)) : GL (Fin n) L :=
  ⟨LinearMap.toMatrix' t.toLinearMap, LinearMap.toMatrix' t.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩

/- English proof (translation)
Use `ext1 x`. Rewrite using `[toE_apply]`. Simplify using `[ofE, LinearMap.toMatrix'_mulVec]`.
-/
theorem toE_ofE (t : (Fin n → L) ≃ₗ[L] (Fin n → L)) : toE (ofE t) = t := by
  ext1 x
  rw [toE_apply]
  simp [ofE, LinearMap.toMatrix'_mulVec]

/- English proof (translation)
Establish `h1 : s ∘ (g.1.mulVec x) = (g.1.map s).mulVec (s ∘ x)`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec s g.1 x i`. Simplify using `only [form, toE_apply, h1]`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (s ∘ x), Matrix.vecMul_transpose]`.
-/
theorem form_toE (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (g : GL (Fin n) L) (x y : Fin n → L) :
    form s J (toE g x) (toE g y) = dotProduct (s ∘ x) (((g.1.map s).transpose * J * g.1).mulVec y) := by
  have h1 : s ∘ (g.1.mulVec x) = (g.1.map s).mulVec (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s g.1 x i
  simp only [form, toE_apply, h1]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (s ∘ x),
    Matrix.vecMul_transpose]

/- English proof (translation)
Establish `hm : g ∈ UG s J ↔ (g.1.map s).transpose * J * g.1 = J` using `Iff.rfl`. Rewrite using `[hm]`. Prove the components needed by the constructor for the conclusion. Introduce `h x y`. Rewrite using `[form_toE, h, form]`.

Introduce `h`. Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[form_toE, form]`. Establish `hsi : s ∘ (Pi.single i 1 : Fin n → L) = Pi.single i 1`.

Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`.

Rewrite `this` using `[hsi]`. Simplify using `using this`.
-/
theorem mem_UG_iff (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (g : GL (Fin n) L) :
    g ∈ UG s J ↔ IsIso (form s J) (toE g) := by
  have hm : g ∈ UG s J ↔ (g.1.map s).transpose * J * g.1 = J := Iff.rfl
  rw [hm]
  constructor
  · intro h x y
    rw [form_toE, h, form]
  · intro h
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [form_toE, form] at this
    have hsi : s ∘ (Pi.single i 1 : Fin n → L) = Pi.single i 1 := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [hsi] at this
    simpa using this

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨ofE t, (mem_UG_iff s J _).2 (by rwa [toE_ofE])⟩, toE_ofE t⟩`.
-/
theorem toE_surj (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (t : (Fin n → L) ≃ₗ[L] (Fin n → L))
    (ht : IsIso (form s J) t) : ∃ g : UG s J, toE g.1 = t :=
  ⟨⟨ofE t, (mem_UG_iff s J _).2 (by rwa [toE_ofE])⟩, toE_ofE t⟩

end Form

section Tor

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i => by simp, fun i => by simp, fun w _ => rfl⟩`.
-/
theorem isTor_one (s : L →+* L) {l : ℕ} (e f : Fin l → V) (W : Submodule L V) :
    IsTor s e f W (fun _ => 1) (1 : V ≃ₗ[L] V) :=
  ⟨fun i => by simp, fun i => by simp, fun w _ => rfl⟩

/- English proof (translation)
Use `⟨fun i => ?_, fun i => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.mul_apply, h'.1, map_smul, h.1, smul_smul, mul_comm]`. Rewrite using `[LinearEquiv.mul_apply, h'.2.1, map_smul, h.2.1, smul_smul, map_mul, mul_inv, mul_comm]`. Rewrite using `[LinearEquiv.mul_apply, h'.2.2 w hw, h.2.2 w hw]`.
-/
theorem isTor_mul {s : L →+* L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V} {u u' : Fin l → L}
    {t t' : V ≃ₗ[L] V} (h : IsTor s e f W u t) (h' : IsTor s e f W u' t') :
    IsTor s e f W (fun i => u i * u' i) (t * t') := by
  refine ⟨fun i => ?_, fun i => ?_, fun w hw => ?_⟩
  · rw [LinearEquiv.mul_apply, h'.1, map_smul, h.1, smul_smul, mul_comm]
  · rw [LinearEquiv.mul_apply, h'.2.1, map_smul, h.2.1, smul_smul, map_mul, mul_inv, mul_comm]
  · rw [LinearEquiv.mul_apply, h'.2.2 w hw, h.2.2 w hw]

end Tor

/- English proof (translation)
Take `⟨x, hx0, hx1⟩` from `NormedField.exists_norm_lt_one L`. Establish `hclosed : IsClosed ({a : L | ‖x‖ ≤ ‖a‖} ∩ Metric.ball 0 1)` using `(isClosed_le continuous_const continuous_norm).inter (IsUltrametricDist.isClopen_ball (0 : L) 1).isClosed`. Establish `hcomp : IsCompact ({a : L | ‖x‖ ≤ ‖a‖} ∩ Metric.ball 0 1)` using `(isCompact_closedBall (0 : L) 1).of_isClosed_subset hclosed (fun a ha => Metric.ball_subset_closedBall ha.2)`. Take `⟨p, hpA, hmax⟩` from `hcomp.exists_isMaxOn ⟨x, le_refl ‖x‖, by simpa using hx1⟩ continuous_norm.continuousOn`. Establish `hp1 : ‖p‖ < 1` using `by simpa using hpA.2`.

Establish `hxp : ‖x‖ ≤ ‖p‖` using `hpA.1`. Use `⟨p, fun h => ?_, hp1, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite `hxp` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h : ‖x‖ ≤ ‖a‖`.

Conclude with `hmax ⟨h, by simpa using ha⟩`. Conclude with `(not_le.1 h).le.trans hxp`.
-/
theorem exists_unif (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] :
    ∃ p : L, p ≠ 0 ∧ ‖p‖ < 1 ∧ ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖ := by
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one L
  have hclosed : IsClosed ({a : L | ‖x‖ ≤ ‖a‖} ∩ Metric.ball 0 1) :=
    (isClosed_le continuous_const continuous_norm).inter (IsUltrametricDist.isClopen_ball (0 : L) 1).isClosed
  have hcomp : IsCompact ({a : L | ‖x‖ ≤ ‖a‖} ∩ Metric.ball 0 1) :=
    (isCompact_closedBall (0 : L) 1).of_isClosed_subset hclosed
      (fun a ha => Metric.ball_subset_closedBall ha.2)
  obtain ⟨p, hpA, hmax⟩ := hcomp.exists_isMaxOn ⟨x, le_refl ‖x‖, by simpa using hx1⟩
    continuous_norm.continuousOn
  have hp1 : ‖p‖ < 1 := by simpa using hpA.2
  have hxp : ‖x‖ ≤ ‖p‖ := hpA.1
  refine ⟨p, fun h => ?_, hp1, fun a ha => ?_⟩
  · rw [h, norm_zero] at hxp; linarith
  · by_cases h : ‖x‖ ≤ ‖a‖
    · exact hmax ⟨h, by simpa using ha⟩
    · exact (not_le.1 h).le.trans hxp

/- English proof (translation)
Take `⟨t, ht⟩` from `hc.elim_finite_subcover (fun c : K₀ => (fun x => (c : G)⁻¹ * x) ⁻¹' (K : Set G)) (fun c => hK.preimage (continuous_const.mul continuous_id)) (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp [one_mem]⟩)`. Use `⟨t.card, fun i => ((t.equivFin.symm i : t) : K₀), fun i => Subtype.coe_prop _, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨c, hct, hgc⟩ : ∃ c ∈ t, (c : G)⁻¹ * g ∈ K` from `by simpa using ht hg`. Use `⟨t.equivFin ⟨c, hct⟩, (c : G)⁻¹ * g, hgc, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem exists_cover {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (K K₀ : Subgroup G)
    (hK : IsOpen (K : Set G)) (hc : IsCompact (K₀ : Set G)) :
    ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ k ∈ K, g = c i * k := by
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun c : K₀ => (fun x => (c : G)⁻¹ * x) ⁻¹' (K : Set G))
    (fun c => hK.preimage (continuous_const.mul continuous_id))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp [one_mem]⟩)
  refine ⟨t.card, fun i => ((t.equivFin.symm i : t) : K₀), fun i => Subtype.coe_prop _, fun g hg => ?_⟩
  obtain ⟨c, hct, hgc⟩ : ∃ c ∈ t, (c : G)⁻¹ * g ∈ K := by simpa using ht hg
  refine ⟨t.equivFin ⟨c, hct⟩, (c : G)⁻¹ * g, hgc, ?_⟩
  simp

def ind {l : ℕ} (i : Fin l) : Fin l → ℕ := fun j => if j ≤ i then 1 else 0

/- English proof (translation)
Introduce `a b hab`. Simplify using `only [ind]`. Apply the tactic sequence `split_ifs <;> first | exact le_rfl | exact Nat.zero_le _ | exact absurd (hab.trans ‹_›) ‹_›`.
-/
theorem ind_antitone {l : ℕ} (i : Fin l) : Antitone (ind i) := by
  intro a b hab
  simp only [ind]
  split_ifs <;> first | exact le_rfl | exact Nat.zero_le _ | exact absurd (hab.trans ‹_›) ‹_›

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Proceed by induction on `hg using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`.

Conclude with `⟨ind i, ind_antitone i, rfl⟩`. Consider the case `one => exact ⟨0, fun _ _ _ => le_rfl, h0.symm⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb, rfl⟩` from `hy`.

Conclude with `⟨a + b, ha.add hb, (hadd a b).symm⟩`. Introduce and unpack `⟨r, hr, rfl⟩`. Establish `key : ∀ m : ℕ, ∀ r : Fin l → ℕ, ∑ j, r j = m → Antitone r → T r ∈ Submonoid.closure (Set.range fun i : Fin l => T (ind i))`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`.

Consider the case `_ m ih`. Introduce `r hm hr`. Distinguish the cases in `h : r = 0`. Rewrite using `[h, h0]`. Conclude with `one_mem _`.

Choose the witnesses or unpack the hypotheses as in `⟨j₀, hj₀⟩ : ∃ j, r j ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (funext hc)`. Establish `hS : (Finset.univ.filter fun j => r j ≠ 0).Nonempty` using `⟨j₀, by simp [hj₀]⟩`.

Take `⟨i, hidef⟩ : ∃ i, i = (Finset.univ.filter fun j => r j ≠ 0).max' hS` from `⟨_, rfl⟩`. Establish `hi : r i ≠ 0`. Use `Finset.max'_mem _ hS` as an intermediate fact. Rewrite `this` using `[← hidef]`. Simplify using `using this`.

Establish `hlt : ∀ j, ¬ j ≤ i → r j = 0` using `fun j hj => by`. Assume the negation of the conclusion as `hc`. Apply `hj` to reduce the goal to its premises. Rewrite using `[hidef]`. Conclude with `Finset.le_max' _ j (by simp [hc])`.

Establish `hpos : ∀ j, j ≤ i → 1 ≤ r j` using `fun j hj => by`. Use `hr hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsplit : r = ind i + (r - ind i)`. Use function extensionality and compare the values at `j`.

Simplify using `only [Pi.add_apply, Pi.sub_apply, ind]`. Use `split_ifs with hj`. Use `hpos j hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Establish `hanti : Antitone (r - ind i)`. Introduce `a b hab`. Simplify using `only [Pi.sub_apply, ind]`. Establish `hab'` using `hr hab`. Use `split_ifs with h1 h2 h2`.

Use linear arithmetic over natural numbers and integers. Conclude with `absurd (hab.trans h1) h2`. Use `hlt b h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Establish `hsum : ∑ j, (r - ind i) j < m`. Establish `h1 : ∑ j, r j = ∑ j, ind i j + ∑ j, (r - ind i) j`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => congrFun hsplit j`. Establish `h2 : ind i i ≤ ∑ j, ind i j` using `Finset.single_le_sum (f := ind i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`.

Establish `h3 : ind i i = 1` using `by simp [ind]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[show T r = T (ind i) * T (r - ind i) by rw [← hadd, ← hsplit]]`. Conclude with `mul_mem (Submonoid.subset_closure ⟨i, rfl⟩) (ih _ hsum _ rfl hanti)`. Conclude with `key _ r rfl hr`.
-/
theorem closure_tor {M : Type} [Monoid M] {l : ℕ} (T : (Fin l → ℕ) → M) (h0 : T 0 = 1)
    (hadd : ∀ a b, T (a + b) = T a * T b) (g : M) :
    g ∈ Submonoid.closure (Set.range fun i : Fin l => T (ind i)) ↔
      ∃ r : Fin l → ℕ, Antitone r ∧ g = T r := by
  constructor
  · intro hg
    induction hg using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨ind i, ind_antitone i, rfl⟩
    | one => exact ⟨0, fun _ _ _ => le_rfl, h0.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, ha.add hb, (hadd a b).symm⟩
  · rintro ⟨r, hr, rfl⟩
    have key : ∀ m : ℕ, ∀ r : Fin l → ℕ, ∑ j, r j = m → Antitone r →
        T r ∈ Submonoid.closure (Set.range fun i : Fin l => T (ind i)) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro r hm hr
        by_cases h : r = 0
        · rw [h, h0]; exact one_mem _
        · obtain ⟨j₀, hj₀⟩ : ∃ j, r j ≠ 0 := by
            by_contra hc
            push_neg at hc
            exact h (funext hc)
          have hS : (Finset.univ.filter fun j => r j ≠ 0).Nonempty := ⟨j₀, by simp [hj₀]⟩
          obtain ⟨i, hidef⟩ : ∃ i, i = (Finset.univ.filter fun j => r j ≠ 0).max' hS := ⟨_, rfl⟩
          have hi : r i ≠ 0 := by
            have := Finset.max'_mem _ hS
            rw [← hidef] at this
            simpa using this
          have hlt : ∀ j, ¬ j ≤ i → r j = 0 := fun j hj => by
            by_contra hc
            apply hj
            rw [hidef]
            exact Finset.le_max' _ j (by simp [hc])
          have hpos : ∀ j, j ≤ i → 1 ≤ r j := fun j hj => by
            have := hr hj
            omega
          have hsplit : r = ind i + (r - ind i) := by
            funext j
            simp only [Pi.add_apply, Pi.sub_apply, ind]
            split_ifs with hj
            · have := hpos j hj
              omega
            · omega
          have hanti : Antitone (r - ind i) := by
            intro a b hab
            simp only [Pi.sub_apply, ind]
            have hab' := hr hab
            split_ifs with h1 h2 h2
            · omega
            · exact absurd (hab.trans h1) h2
            · have := hlt b h1
              omega
            · omega
          have hsum : ∑ j, (r - ind i) j < m := by
            have h1 : ∑ j, r j = ∑ j, ind i j + ∑ j, (r - ind i) j := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun j _ => congrFun hsplit j
            have h2 : ind i i ≤ ∑ j, ind i j :=
              Finset.single_le_sum (f := ind i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            have h3 : ind i i = 1 := by simp [ind]
            omega
          rw [show T r = T (ind i) * T (r - ind i) by rw [← hadd, ← hsplit]]
          exact mul_mem (Submonoid.subset_closure ⟨i, rfl⟩) (ih _ hsum _ rfl hanti)
    exact key _ r rfl hr

/- English proof (translation)
Establish `hcl` using `closure_tor T h0 hadd`. Use `⟨c, fun i => T (ind i), fun i k => hnorm _ (hc i) k, fun i j => ?_, fun g => ?_, ?_⟩` and prove the remaining obligations. Use `show T (ind i) * T (ind j) = T (ind j) * T (ind i)`. Rewrite using `[← hadd, ← hadd, add_comm]`. Take `⟨k, hk, k', hk', r, hr, rfl⟩` from `hdec g`.

Take `⟨i, a, ha, rfl⟩` from `hcov k hk`. Take `⟨j, b, hb, rfl⟩` from `hcov k' hk'`. Use `⟨i, j, T r, (hcl _).2 ⟨r, hr, rfl⟩, c i * a * (c i)⁻¹, (hnorm _ (hc i) _).1 ha, b, hb, ?_⟩` and prove the remaining obligations. Use `group`. Introduce `x hx y hy k hk`.

Take `⟨r, hr, rfl⟩` from `(hcl _).1 hx`. Take `⟨r', hr', rfl⟩` from `(hcl _).1 hy`. Take `⟨a, b, rfl, hab⟩` from `hiw k hk`. Conclude with `⟨_, (hab r hr).1, _, (hab r' hr').2, by group⟩`.
-/
theorem isCartan_of {G : Type} [Group G] (K K₀ : Subgroup G) {d l : ℕ} (T : (Fin l → ℕ) → G)
    (h0 : T 0 = 1) (hadd : ∀ a b, T (a + b) = T a * T b) (c : Fin d → G) (hc : ∀ i, c i ∈ K₀)
    (hcov : ∀ g ∈ K₀, ∃ i, ∃ k ∈ K, g = c i * k)
    (hnorm : ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K)
    (hdec : ∀ g, ∃ k ∈ K₀, ∃ k' ∈ K₀, ∃ r : Fin l → ℕ, Antitone r ∧ g = k * T r * k')
    (hiw : ∀ k ∈ K, ∃ a b : G, k = a * b ∧ ∀ r : Fin l → ℕ, Antitone r →
      T r * a * (T r)⁻¹ ∈ K ∧ (T r)⁻¹ * b * T r ∈ K) :
    IsCartan K d l := by
  have hcl := closure_tor T h0 hadd
  refine ⟨c, fun i => T (ind i), fun i k => hnorm _ (hc i) k, fun i j => ?_, fun g => ?_, ?_⟩
  · show T (ind i) * T (ind j) = T (ind j) * T (ind i)
    rw [← hadd, ← hadd, add_comm]
  · obtain ⟨k, hk, k', hk', r, hr, rfl⟩ := hdec g
    obtain ⟨i, a, ha, rfl⟩ := hcov k hk
    obtain ⟨j, b, hb, rfl⟩ := hcov k' hk'
    refine ⟨i, j, T r, (hcl _).2 ⟨r, hr, rfl⟩, c i * a * (c i)⁻¹, (hnorm _ (hc i) _).1 ha, b, hb, ?_⟩
    group
  · intro x hx y hy k hk
    obtain ⟨r, hr, rfl⟩ := (hcl _).1 hx
    obtain ⟨r', hr', rfl⟩ := (hcl _).1 hy
    obtain ⟨a, b, rfl, hab⟩ := hiw k hk
    exact ⟨_, (hab r hr).1, _, (hab r' hr').2, by group⟩

/- English proof (translation)
Introduce `hΔ hE hF hT hD hI H L _ _ _ _ s hs hn hne n J hJ hdet U hU`. Establish `hinv : IsInv s` using `⟨hs, hn, hne⟩`. Take `⟨δ, hδ⟩` from `hΔ L s hinv`. Establish `hh` using `form_isHerm s J hs hJ hdet`. Take `⟨Λ, hΛ⟩` from `hE L s hinv δ hδ (Fin n → L) (form s J) hh`.

Take `⟨l, e, f, W, u, -, hfr, had, -⟩` from `hF L s hinv δ hδ _ (form s J) hh Λ Λ hΛ hΛ`. Take `⟨p, hp0, hp1, hpm⟩` from `exists_unif L`. Take `⟨hK, hU'⟩` from `H L s hn n J Λ hΛ.1`. Take `⟨π, hπ0, hπ1, hπU⟩` from `hU' U hU`. Take `⟨K, K₀, hKm, hK₀m, hKo, hKc, hK₀c, -, hnorm⟩` from `hK π hπ0 hπ1`.

Use `⟨K, fun g hg => hπU g ((hKm g).1 hg), hKo, hKc, ?_⟩` and prove the remaining obligations. Take `⟨d, c, hcK, hcov⟩` from `exists_cover K K₀ hKo hK₀c`. Establish `hKc' : ∀ g : UG s J, g ∈ K ↔ IsCong Λ π (toE g.1)` using `hKm`. Establish `hK₀' : ∀ g : UG s J, g ∈ K₀ ↔ ∀ x, toE g.1 x ∈ Λ ↔ x ∈ Λ` using `hK₀m`. Establish `hiso : ∀ g : UG s J, IsIso (form s J) (toE g.1)` using `fun g => (mem_UG_iff s J g.1).1 g.2`.

Establish `hinj : ∀ a b : UG s J, toE a.1 = toE b.1 → a = b` using `fun a b h => Subtype.ext (toE_injective h)`. Establish `hex : ∀ r : Fin l → ℕ, ∃ g : UG s J, IsTor s e f W (fun i => p ^ r i) (toE g.1) ∧ ∀ t' : (Fin n → L) ≃ₗ[L] (Fin n → L), IsTor s e f W (fun i => p ^ r i) t' → t' = toE g.1`. Introduce `r`. Take `⟨t, ht, htor, huniq⟩` from `hT L s hinv δ hδ _ (form s J) hh l e f W hfr (fun i => p ^ r i) (fun i => pow_ne_zero _ hp0)`. Take `⟨g, rfl⟩` from `toE_surj s J t ht`.

Conclude with `⟨g, htor, huniq⟩`. Use `choose T hTt hTe using hex`. Establish `hTu : ∀ (r : Fin l → ℕ) (g' : UG s J), IsTor s e f W (fun i => p ^ r i) (toE g'.1) → g' = T r` using `fun r g' h' => hinj _ _ (hTe r _ h')`. Establish `h0 : T 0 = 1`. Use `(hTu 0 1 ?_).symm` and prove the remaining obligations.

Simplify using `using isTor_one s e f W`. Establish `hadd : ∀ a b, T (a + b) = T a * T b`. Introduce `a b`. Use `(hTu (a + b) (T a * T b) ?_).symm` and prove the remaining obligations. Use `isTor_mul (hTt a) (hTt b)` as an intermediate fact.

Simplify `this` using `[pow_add]`. Use `⟨d, l, isCartan_of K K₀ T h0 hadd c hcK hcov hnorm ?_ ?_⟩` and prove the remaining obligations. Introduce `g`. Take `⟨k, t, k', r, hr, hk, hk', hkΛ, hk'Λ, htor, heq⟩` from `hD L s hinv δ hδ _ (form s J) hh l e f W Λ hfr hΛ had p hp0 hp1 hpm (toE g.1) (hiso g)`. Take `⟨k₁, rfl⟩` from `toE_surj s J k hk`.

Take `⟨k₂, rfl⟩` from `toE_surj s J k' hk'`. Take `rfl` from `hTe r t htor`. Use `⟨k₁, (hK₀' _).2 hkΛ, k₂, (hK₀' _).2 hk'Λ, r, hr, ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Simplify using `using heq`.

Introduce `k hk`. Take `⟨a, b, ha, hb, hab, hall⟩` from `hI L s hinv δ hδ _ (form s J) hh l e f W Λ hfr hΛ.1 had π hπ1 (toE k.1) (hiso k) ((hKc' k).1 hk)`. Take `⟨a₀, rfl⟩` from `toE_surj s J a ha`. Take `⟨b₀, rfl⟩` from `toE_surj s J b hb`. Use `⟨a₀, b₀, hinj _ _ (by simpa using hab), fun r hr => ?_⟩` and prove the remaining obligations.

Establish `hmono : Monotone fun i => ‖p ^ r i‖` using `fun i j hij => by`. Simplify using `only [norm_pow]`. Conclude with `pow_le_pow_of_le_one (norm_nonneg _) hp1.le (hr hij)`. Establish `hone : ∀ i, ‖p ^ r i‖ ≤ 1` using `fun i => by`. Simplify using `only [norm_pow]`.

Conclude with `pow_le_one₀ (norm_nonneg _) hp1.le`. Take `⟨h1, h2⟩` from `hall (fun i => p ^ r i) (toE (T r).1) (fun i => pow_ne_zero _ hp0) hmono hone (hTt r)`. Conclude with `⟨(hKc' _).2 (by simpa using h1), (hKc' _).2 (by simpa using h2)⟩`.
-/
theorem final : StDelta → StExists → StFrame → StTor → StDecomp → StIwahori →
    (∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (s : L →+* L),
      (∀ x, ‖s x‖ = ‖x‖) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) L) (Λ : AddSubgroup (Fin n → L)),
      IsLat L Λ →
      (∀ π : L, π ≠ 0 → ‖π‖ < 1 → ∃ K K₀ : Subgroup (UG s J),
        (∀ g, g ∈ K ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) ∧
        (∀ g, g ∈ K₀ ↔ ∀ x, g.1.1.mulVec x ∈ Λ ↔ x ∈ Λ) ∧ IsOpen (K : Set (UG s J)) ∧
        IsCompact (K : Set (UG s J)) ∧ IsCompact (K₀ : Set (UG s J)) ∧ K ≤ K₀ ∧
        ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K) ∧
      ∀ U : Subgroup (UG s J), IsOpen (U : Set (UG s J)) → ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧
        ∀ g : UG s J, (∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) → g ∈ U) → StCartanU := by
  intro hΔ hE hF hT hD hI H L _ _ _ _ s hs hn hne n J hJ hdet U hU
  have hinv : IsInv s := ⟨hs, hn, hne⟩
  obtain ⟨δ, hδ⟩ := hΔ L s hinv
  have hh := form_isHerm s J hs hJ hdet
  obtain ⟨Λ, hΛ⟩ := hE L s hinv δ hδ (Fin n → L) (form s J) hh
  obtain ⟨l, e, f, W, u, -, hfr, had, -⟩ := hF L s hinv δ hδ _ (form s J) hh Λ Λ hΛ hΛ
  obtain ⟨p, hp0, hp1, hpm⟩ := exists_unif L
  obtain ⟨hK, hU'⟩ := H L s hn n J Λ hΛ.1
  obtain ⟨π, hπ0, hπ1, hπU⟩ := hU' U hU
  obtain ⟨K, K₀, hKm, hK₀m, hKo, hKc, hK₀c, -, hnorm⟩ := hK π hπ0 hπ1
  refine ⟨K, fun g hg => hπU g ((hKm g).1 hg), hKo, hKc, ?_⟩
  obtain ⟨d, c, hcK, hcov⟩ := exists_cover K K₀ hKo hK₀c
  have hKc' : ∀ g : UG s J, g ∈ K ↔ IsCong Λ π (toE g.1) := hKm
  have hK₀' : ∀ g : UG s J, g ∈ K₀ ↔ ∀ x, toE g.1 x ∈ Λ ↔ x ∈ Λ := hK₀m
  have hiso : ∀ g : UG s J, IsIso (form s J) (toE g.1) := fun g => (mem_UG_iff s J g.1).1 g.2
  have hinj : ∀ a b : UG s J, toE a.1 = toE b.1 → a = b := fun a b h => Subtype.ext (toE_injective h)
  have hex : ∀ r : Fin l → ℕ, ∃ g : UG s J, IsTor s e f W (fun i => p ^ r i) (toE g.1) ∧
      ∀ t' : (Fin n → L) ≃ₗ[L] (Fin n → L), IsTor s e f W (fun i => p ^ r i) t' → t' = toE g.1 := by
    intro r
    obtain ⟨t, ht, htor, huniq⟩ := hT L s hinv δ hδ _ (form s J) hh l e f W hfr (fun i => p ^ r i)
      (fun i => pow_ne_zero _ hp0)
    obtain ⟨g, rfl⟩ := toE_surj s J t ht
    exact ⟨g, htor, huniq⟩
  choose T hTt hTe using hex
  have hTu : ∀ (r : Fin l → ℕ) (g' : UG s J), IsTor s e f W (fun i => p ^ r i) (toE g'.1) → g' = T r :=
    fun r g' h' => hinj _ _ (hTe r _ h')
  have h0 : T 0 = 1 := by
    refine (hTu 0 1 ?_).symm
    simpa using isTor_one s e f W
  have hadd : ∀ a b, T (a + b) = T a * T b := by
    intro a b
    refine (hTu (a + b) (T a * T b) ?_).symm
    have := isTor_mul (hTt a) (hTt b)
    simpa [pow_add] using this
  refine ⟨d, l, isCartan_of K K₀ T h0 hadd c hcK hcov hnorm ?_ ?_⟩
  · intro g
    obtain ⟨k, t, k', r, hr, hk, hk', hkΛ, hk'Λ, htor, heq⟩ :=
      hD L s hinv δ hδ _ (form s J) hh l e f W Λ hfr hΛ had p hp0 hp1 hpm (toE g.1) (hiso g)
    obtain ⟨k₁, rfl⟩ := toE_surj s J k hk
    obtain ⟨k₂, rfl⟩ := toE_surj s J k' hk'
    obtain rfl := hTe r t htor
    refine ⟨k₁, (hK₀' _).2 hkΛ, k₂, (hK₀' _).2 hk'Λ, r, hr, ?_⟩
    apply hinj
    simpa using heq
  · intro k hk
    obtain ⟨a, b, ha, hb, hab, hall⟩ := hI L s hinv δ hδ _ (form s J) hh l e f W Λ hfr hΛ.1 had π hπ1
      (toE k.1) (hiso k) ((hKc' k).1 hk)
    obtain ⟨a₀, rfl⟩ := toE_surj s J a ha
    obtain ⟨b₀, rfl⟩ := toE_surj s J b hb
    refine ⟨a₀, b₀, hinj _ _ (by simpa using hab), fun r hr => ?_⟩
    have hmono : Monotone fun i => ‖p ^ r i‖ := fun i j hij => by
      simp only [norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) hp1.le (hr hij)
    have hone : ∀ i, ‖p ^ r i‖ ≤ 1 := fun i => by
      simp only [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hp1.le
    obtain ⟨h1, h2⟩ := hall (fun i => p ^ r i) (toE (T r).1) (fun i => pow_ne_zero _ hp0) hmono hone (hTt r)
    exact ⟨(hKc' _).2 (by simpa using h1), (hKc' _).2 (by simpa using h2)⟩

end GlobalTheory.CompanionTheory.CartanU

end
