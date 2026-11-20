import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace QuantumDeterminantProducts

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def sg (σ : Equiv.Perm (Fin n)) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)

/- English proof (translation)
Simplify using `[sg, Equiv.Perm.sign_swap h]`.
-/
theorem sg_swap {i j : Fin n} (h : i ≠ j) : sg (Equiv.swap i j) = -1 := by
  simp [sg, Equiv.Perm.sign_swap h]

def IsAnti (g : TV n M (Fin n)) : Prop := ∀ σ : Equiv.Perm (Fin n), pm σ g = sg σ • g

/- English proof (translation)
Establish `h` using `congrFun (hg σ) I`. Simplify `h` using `[pm]`.
-/
theorem anti_apply {g : TV n M (Fin n)} (hg : IsAnti g) (σ : Equiv.Perm (Fin n)) (I : Fin n → Fin n) :
    g (I ∘ σ) = sg σ • g I := by
  have h := congrFun (hg σ) I
  simpa [pm] using h

/- English proof (translation)
Simplify using `only [Function.Injective] at hI`. Use `push_neg at hI`. Take `⟨i, j, hij, hne⟩` from `hI`. Establish `hIs : I ∘ Equiv.swap i j = I`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp_apply]`. Break down `eq_or_ne k i with rfl | hki` into its components or cases. Simplify using `[Equiv.swap_apply_left, hij]`. Break down `eq_or_ne k j with rfl | hkj` into its components or cases. Simplify using `[Equiv.swap_apply_right, hij]`.

Rewrite using `[Equiv.swap_apply_of_ne_of_ne hki hkj]`. Establish `h` using `anti_apply hg (Equiv.swap i j) I`. Rewrite `h` using `[hIs, sg_swap hne]`. Establish `h2 : (2 : ℂ) • g I = 0`. Rewrite using `[two_smul]`.

Use `nth_rewrite 1 [h]`. Simplify using the standard rewrite rules. Conclude with `(smul_eq_zero.mp h2).resolve_left two_ne_zero`.
-/
theorem anti_zero {g : TV n M (Fin n)} (hg : IsAnti g) {I : Fin n → Fin n} (hI : ¬ Function.Injective I) :
    g I = 0 := by
  simp only [Function.Injective] at hI
  push_neg at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  have hIs : I ∘ Equiv.swap i j = I := by
    funext k
    simp only [Function.comp_apply]
    rcases eq_or_ne k i with rfl | hki
    · simp [Equiv.swap_apply_left, hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [Equiv.swap_apply_right, hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := anti_apply hg (Equiv.swap i j) I
  rw [hIs, sg_swap hne] at h
  have h2 : (2 : ℂ) • g I = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/- English proof (translation)
Use function extensionality and compare the values at `I`. Distinguish the cases in `hI : Function.Injective I`. Establish `hb : Function.Bijective I` using `Finite.injective_iff_bijective.mp hI`. Establish `h` using `anti_apply hg (Equiv.ofBijective I hb) id`. Establish `hc : (id ∘ ⇑(Equiv.ofBijective I hb)) = I`.

Use function extensionality and compare the values at `k`. Both sides reduce to the same expression. Rewrite `h` using `[hc, h0, smul_zero]`. Simplify using `using h`. Simplify using `using anti_zero hg hI`.
-/
theorem anti_ext {g : TV n M (Fin n)} (hg : IsAnti g) (h0 : g id = 0) : g = 0 := by
  funext I
  by_cases hI : Function.Injective I
  · have hb : Function.Bijective I := Finite.injective_iff_bijective.mp hI
    have h := anti_apply hg (Equiv.ofBijective I hb) id
    have hc : (id ∘ ⇑(Equiv.ofBijective I hb)) = I := by
      funext k
      rfl
    rw [hc, h0, smul_zero] at h
    simpa using h
  · simpa using anti_zero hg hI

/- English proof (translation)
Introduce `σ`. Use function extensionality and compare the values at `I`. Establish `key : ∀ J : Fin n → Fin n, alt Finset.univ f J = ∑ τ : Equiv.Perm (Fin n), sg τ • f (J ∘ ⇑τ)`. Introduce `J`. Simplify using `[alt, pm, sg]`.

Establish `hp : pm σ (alt Finset.univ f) I = alt Finset.univ f (I ∘ σ)`. Simplify using `[pm]`. Rewrite using `[hp]`. Use `show alt Finset.univ f (I ∘ σ) = sg σ • alt Finset.univ f I`. Rewrite using `[key (I ∘ σ), key I, Finset.smul_sum]`.

Use `Fintype.sum_equiv (Equiv.mulLeft σ) _ _ ?_` and prove the remaining obligations. Introduce `τ`. Establish `hs : sg σ * sg (σ * τ) = sg τ`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [sg, Equiv.Perm.sign_mul, h]`. Simplify using `only [Equiv.coe_mulLeft]`.

Rewrite using `[smul_smul, hs]`. Both sides reduce to the same expression.
-/
theorem alt_anti (f : TV n M (Fin n)) : IsAnti (alt Finset.univ f) := by
  intro σ
  funext I
  have key : ∀ J : Fin n → Fin n, alt Finset.univ f J = ∑ τ : Equiv.Perm (Fin n), sg τ • f (J ∘ ⇑τ) := by
    intro J
    simp [alt, pm, sg]
  have hp : pm σ (alt Finset.univ f) I = alt Finset.univ f (I ∘ σ) := by
    simp [pm]
  rw [hp]
  show alt Finset.univ f (I ∘ σ) = sg σ • alt Finset.univ f I
  rw [key (I ∘ σ), key I, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ ?_
  intro τ
  have hs : sg σ * sg (σ * τ) = sg τ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [sg, Equiv.Perm.sign_mul, h]
  simp only [Equiv.coe_mulLeft]
  rw [smul_smul, hs]
  rfl

def X (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) : Module.End ℂ (TV n M (Fin n)) :=
  algebraMap ℂ _ u + xJ E j

def T (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) : Module.End ℂ (TV n M (Fin n)) :=
  algebraMap ℂ _ (u - (j : ℂ)) + Om E j

/- English proof (translation)
Establish `hs : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j), pm (Equiv.swap i j)) w = -(((j : ℕ) : ℂ) • w)`. Rewrite using `[LinearMap.sum_apply]`. Rewrite using `[Finset.sum_congr rfl (fun i hi => hw i (Finset.mem_filter.mp hi).2)]`. Rewrite using `[Finset.sum_neg_distrib, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, Nat.cast_smul_eq_nsmul]`. Simplify using `only [X, T, xJ, LinearMap.add_apply]`.

Rewrite using `[hs, Module.algebraMap_end_apply, Module.algebraMap_end_apply, sub_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem X_eq_T_of_antisymm_below (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) (w : TV n M (Fin n))
    (hw : ∀ i, i < j → pm (Equiv.swap i j) w = -w) : X E u j w = T E u j w := by
  have hs : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j), pm (Equiv.swap i j)) w = -(((j : ℕ) : ℂ) • w) := by
    rw [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun i hi => hw i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_neg_distrib, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, Nat.cast_smul_eq_nsmul]
  simp only [X, T, xJ, LinearMap.add_apply]
  rw [hs, Module.algebraMap_end_apply, Module.algebraMap_end_apply, sub_smul]
  abel

/- English proof (translation)
Use `Commute.add_right (Algebra.commutes _ _).symm ?_` and prove the remaining obligations. Use `(hT n M (Fin n) E hE ∅).2.2.2 σ j` as an intermediate fact. Rewrite `this` using `[hj]`. Conclude with `this`.
-/
theorem T_comm (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (u : ℂ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) (hj : σ j = j) : Commute (pm σ) (T E u j) := by
  refine Commute.add_right (Algebra.commutes _ _).symm ?_
  have := (hT n M (Fin n) E hE ∅).2.2.2 σ j
  rw [hj] at this
  exact this

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons k l ih`. Rewrite `hl` using `[List.pairwise_cons]`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply]`.

Rewrite using `[ih hl.2]`. Apply `X_eq_T_of_antisymm_below` to reduce the goal to its premises. Introduce `i hi`. Establish `hc : Commute (pm (Equiv.swap i k)) (l.map (T E u)).prod`. Apply `Commute.list_prod_right` to reduce the goal to its premises.

Introduce `b hb`. Take `⟨j, hj, rfl⟩` from `List.mem_map.mp hb`. Establish `hkj` using `hl.1 j hj`. Apply `T_comm hT E hE u` to reduce the goal to its premises. Apply `Equiv.swap_apply_of_ne_of_ne` to reduce the goal to its premises.

Conclude with `ne_of_gt (lt_trans hi hkj)`. Conclude with `ne_of_gt hkj`. Rewrite using `[← Module.End.mul_apply, hc.eq, Module.End.mul_apply]`. Rewrite using `[hg (Equiv.swap i k), sg_swap (ne_of_lt hi)]`. Simplify using the standard rewrite rules.
-/
theorem step1 (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (u : ℂ) (g : TV n M (Fin n))
    (hg : IsAnti g) (l : List (Fin n)) (hl : l.Pairwise (· < ·)) :
    (l.map (X E u)).prod g = (l.map (T E u)).prod g := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.pairwise_cons] at hl
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih hl.2]
    apply X_eq_T_of_antisymm_below
    intro i hi
    have hc : Commute (pm (Equiv.swap i k)) (l.map (T E u)).prod := by
      apply Commute.list_prod_right
      intro b hb
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hkj := hl.1 j hj
      apply T_comm hT E hE u
      apply Equiv.swap_apply_of_ne_of_ne
      · exact ne_of_gt (lt_trans hi hkj)
      · exact ne_of_gt hkj
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
    rw [hg (Equiv.swap i k), sg_swap (ne_of_lt hi)]
    simp

def ev (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) : List (Fin n) → (Fin n → Fin n) → TV n M (Fin n) → M
  | [], I, h => h I
  | k :: l, I, h => ∑ a, Tm E (u - (k : ℂ)) a (I k) (ev E u l (Function.update I k a) h)

/- English proof (translation)
Simplify using `[T, Om, lift, eAt, Tm, Finset.sum_add_distrib, LinearMap.add_apply]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single (I k)]`. Simplify using `[sub_smul]`. Introduce `b _ hb`.

Simplify using `[hb]`. Simplify using the standard rewrite rules. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (I k)]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem T_apply (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (k : Fin n) (h : TV n M (Fin n)) (I : Fin n → Fin n) :
    T E u k h I = ∑ a, Tm E (u - (k : ℂ)) a (I k) (h (Function.update I k a)) := by
  simp [T, Om, lift, eAt, Tm, Finset.sum_add_distrib, LinearMap.add_apply]
  congr 1
  · rw [Finset.sum_eq_single (I k)]
    · simp [sub_smul]
    · intro b _ hb
      simp [hb]
    · simp
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (I k)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

/- English proof (translation)
Proceed by induction on `l generalizing I with`. Consider the case `nil => rfl`. Consider the case `cons k l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ev, T_apply, ih]`.
-/
theorem evA (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (I : Fin n → Fin n) :
    (l.map (T E u)).prod h I = ev E u l I h := by
  induction l generalizing I with
  | nil => rfl
  | cons k l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ev, T_apply, ih]

/- English proof (translation)
Proceed by induction on `l generalizing I with`. Consider the case `nil`. Rewrite using `[Finset.sum_eq_single I]`. Simplify using `[ev]`. Introduce `c hc hne`.

It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `p`. Conclude with `(Finset.mem_filter.mp hc).2 p (by simp)`. Introduce `hI`.

It suffices to derive a contradiction. Apply `hI` to reduce the goal to its premises. Simplify using the standard rewrite rules. Consider the case `cons k l ih`. Establish `hk : k ∉ l` using `(List.nodup_cons.mp hl).1`.

Establish `hl'` using `(List.nodup_cons.mp hl).2`. Simplify using `only [ev, ih hl']`. Use `conv_rhs => rw [← Finset.sum_fiberwise _ (fun c : Fin n → Fin n => c k)]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`.

Use `Finset.sum_congr ?_ fun c hc => ?_` and prove the remaining obligations. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, not_or]`. Prove the components needed by the constructor for the conclusion. Introduce `H`.

Use `⟨fun p hp => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[H p hp.2, Function.update_of_ne hp.1]`. Rewrite using `[H k hk, Function.update_self]`. Introduce and unpack `⟨H, hca⟩ p hp`. Distinguish the cases in `hpk : p = k`.

Substitute `hpk` using the available equality. Rewrite using `[hca, Function.update_self]`. Rewrite using `[H p ⟨hpk, hp⟩, Function.update_of_ne hpk]`. Simplify using `only [Finset.mem_filter] at hc`. Establish `hca : c k = a` using `hc.2`.

Establish `hm : l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (Function.update I k a k')) = l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (I k'))`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `x hx`. Establish `hxk : x ≠ k`. Introduce and unpack `rfl`.

Conclude with `hk hx`. Rewrite using `[Function.update_of_ne hxk]`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply, hca, hm]`.
-/
theorem evB (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (hl : l.Nodup)
    (I : Fin n → Fin n) :
    ev E u l I h = ∑ c ∈ Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ l → c p = I p),
      (l.map fun k : Fin n => Tm E (u - (k : ℂ)) (c k) (I k)).prod (h c) := by
  induction l generalizing I with
  | nil =>
    rw [Finset.sum_eq_single I]
    · simp [ev]
    · intro c hc hne
      exfalso
      apply hne
      funext p
      exact (Finset.mem_filter.mp hc).2 p (by simp)
    · intro hI
      exfalso
      apply hI
      simp
  | cons k l ih =>
    have hk : k ∉ l := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    simp only [ev, ih hl']
    conv_rhs => rw [← Finset.sum_fiberwise _ (fun c : Fin n → Fin n => c k)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr ?_ fun c hc => ?_
    · ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, not_or]
      constructor
      · intro H
        refine ⟨fun p hp => ?_, ?_⟩
        · rw [H p hp.2, Function.update_of_ne hp.1]
        · rw [H k hk, Function.update_self]
      · rintro ⟨H, hca⟩ p hp
        by_cases hpk : p = k
        · subst hpk
          rw [hca, Function.update_self]
        · rw [H p ⟨hpk, hp⟩, Function.update_of_ne hpk]
    · simp only [Finset.mem_filter] at hc
      have hca : c k = a := hc.2
      have hm : l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (Function.update I k a k'))
          = l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (I k')) := by
        apply List.map_congr_left
        intro x hx
        have hxk : x ≠ k := by
          rintro rfl
          exact hk hx
        rw [Function.update_of_ne hxk]
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hca, hm]

/- English proof (translation)
Rewrite using `[evB E u g _ (List.nodup_finRange n) id]`. Establish `hfilt : Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ List.finRange n → c p = id p) = Finset.univ`. Apply `Finset.filter_true_of_mem` to reduce the goal to its premises. Introduce `c _ p hp`. Conclude with `absurd (List.mem_finRange p) hp`.

Rewrite using `[hfilt]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨fun σ : Equiv.Perm (Fin n) => ⇑σ, DFunLike.coe_injective⟩)), Finset.sum_map]`. Simplify using `only [qdet, qminor, LinearMap.sum_apply, Function.Embedding.coeFn_mk]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `ha` using `anti_apply hg σ id`.

Simplify using `only [Function.id_comp] at ha`. Rewrite using `[ha, map_smul, Module.End.mul_apply, Module.End.intCast_apply, List.ofFn_eq_map, sg, Int.cast_smul_eq_zsmul]`. Both sides reduce to the same expression. Introduce `c _ hc`. Establish `hnc : ¬ Function.Injective c`.

Introduce `hinj`. Apply `hc` to reduce the goal to its premises. Rewrite using `[Finset.mem_map]`. Conclude with `⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩`. Rewrite using `[anti_zero hg hnc, map_zero]`.
-/
theorem evQ (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (g : TV n M (Fin n)) (hg : IsAnti g) :
    ev E u (List.finRange n) id g = qdet E u (g id) := by
  rw [evB E u g _ (List.nodup_finRange n) id]
  have hfilt : Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ List.finRange n → c p = id p) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro c _ p hp
    exact absurd (List.mem_finRange p) hp
  rw [hfilt]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨fun σ : Equiv.Perm (Fin n) => ⇑σ, DFunLike.coe_injective⟩)), Finset.sum_map]
  · simp only [qdet, qminor, LinearMap.sum_apply, Function.Embedding.coeFn_mk]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have ha := anti_apply hg σ id
    simp only [Function.id_comp] at ha
    rw [ha, map_smul, Module.End.mul_apply, Module.End.intCast_apply, List.ofFn_eq_map, sg, Int.cast_smul_eq_zsmul]
    rfl
  · intro c _ hc
    have hnc : ¬ Function.Injective c := by
      intro hinj
      apply hc
      rw [Finset.mem_map]
      exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
    rw [anti_zero hg hnc, map_zero]

end QuantumDeterminantProducts

open QuantumDeterminantProducts in
/- English proof (translation)
Introduce `hT hJ n M _ _ E hE u`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Use `set g := alt Finset.univ f with hgdef`. Establish `hg : IsAnti g` using `alt_anti f`.

Rewrite using `[Module.End.mul_apply, Module.End.mul_apply]`. Establish `hPX : PiJ n E u = ((List.finRange n).map (X E u)).prod`. Unfold `PiJ`. Rewrite using `[List.ofFn_eq_map]`. Both sides reduce to the same expression.

Establish `hA : IsAnti (PiJ n E u g)`. Introduce `σ`. Establish `hc` using `((hJ n M E hE n).2.2 u σ).eq`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : IsAnti (lift (qdet E u) g)`.

Introduce `σ`. Establish `hl : pm σ (lift (qdet E u) g) = lift (qdet E u) (pm σ g)`. Use function extensionality and compare the values at `I`. Simplify using `[pm, lift]`. Rewrite using `[hl, hg σ, map_smul]`.

Establish `hD : IsAnti (PiJ n E u g - lift (qdet E u) g)`. Introduce `σ`. Rewrite using `[map_sub, hA σ, hB σ, smul_sub]`. Establish `h0 : (PiJ n E u g - lift (qdet E u) g) id = 0`. Rewrite using `[Pi.sub_apply, hPX, step1 hT E hE u g hg _ (List.pairwise_lt_finRange n), evA, evQ E u g hg]`.

Simplify using `[lift]`. Conclude with `sub_eq_zero.mp (anti_ext hD h0)`.
-/
theorem piQdet_of : TensorGl → JMComm → PiQdet := by
  intro hT hJ n M _ _ E hE u
  apply LinearMap.ext
  intro f
  set g := alt Finset.univ f with hgdef
  have hg : IsAnti g := alt_anti f
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have hPX : PiJ n E u = ((List.finRange n).map (X E u)).prod := by
    unfold PiJ
    rw [List.ofFn_eq_map]
    rfl
  have hA : IsAnti (PiJ n E u g) := by
    intro σ
    have hc := ((hJ n M E hE n).2.2 u σ).eq
    calc pm σ (PiJ n E u g) = ((pm σ * PiJ n E u : Module.End ℂ (TV n M (Fin n))) g) := rfl
      _ = ((PiJ n E u * pm σ : Module.End ℂ (TV n M (Fin n))) g) := by rw [hc]
      _ = PiJ n E u (pm σ g) := rfl
      _ = sg σ • PiJ n E u g := by rw [hg σ, map_smul]
  have hB : IsAnti (lift (qdet E u) g) := by
    intro σ
    have hl : pm σ (lift (qdet E u) g) = lift (qdet E u) (pm σ g) := by
      funext I
      simp [pm, lift]
    rw [hl, hg σ, map_smul]
  have hD : IsAnti (PiJ n E u g - lift (qdet E u) g) := by
    intro σ
    rw [map_sub, hA σ, hB σ, smul_sub]
  have h0 : (PiJ n E u g - lift (qdet E u) g) id = 0 := by
    rw [Pi.sub_apply, hPX, step1 hT E hE u g hg _ (List.pairwise_lt_finRange n), evA, evQ E u g hg]
    simp [lift]
  exact sub_eq_zero.mp (anti_ext hD h0)

end PositivityTheory.Rg.Cz

end
