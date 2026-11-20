import Formalism.SharpRestriction.GrowthBounds.RootWeights.PieAltApply

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def pie_pr {n : ℕ} (j : Fin n) : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩

def pie_sw {n : ℕ} (mu : Fin n → ℕ) (j : Fin n) : Fin n → ℕ :=
  Function.update (Function.update mu (pie_pr j) (mu j - 1)) j (mu (pie_pr j) + 1)

def pie_B {n : ℕ} (lam mu : Fin n → ℕ) : Finset (Fin n) :=
  univ.filter fun j => 0 < j.val ∧ lam (pie_pr j) < mu j

/- English proof (translation)
Introduce `hc`. Establish `h2 : j.val - 1 = j.val` using `congrArg Fin.val hc`. Use linear arithmetic over natural numbers and integers.
-/
theorem pie_pr_ne {n : ℕ} {j : Fin n} (h : 0 < j.val) : pie_pr j ≠ j := by
  intro hc
  have h2 : j.val - 1 = j.val := congrArg Fin.val hc
  omega

/- English proof (translation)
Unfold `pie_sw`. Use `first`. Consider the case `rw [Function.update_self]`. Consider the case `rw [Function.update_same]`. Consider the case `simp`.
-/
theorem pie_sw_self {n : ℕ} (mu : Fin n → ℕ) (j : Fin n) : pie_sw mu j j = mu (pie_pr j) + 1 := by
  unfold pie_sw
  first
  | rw [Function.update_self]
  | rw [Function.update_same]
  | simp

/- English proof (translation)
Unfold `pie_sw`. Use `first`. Consider the case `rw [Function.update_of_ne (pie_pr_ne h), Function.update_self]`. Consider the case `rw [Function.update_noteq (pie_pr_ne h), Function.update_same]`.
-/
theorem pie_sw_pr {n : ℕ} (mu : Fin n → ℕ) {j : Fin n} (h : 0 < j.val) :
    pie_sw mu j (pie_pr j) = mu j - 1 := by
  unfold pie_sw
  first
  | rw [Function.update_of_ne (pie_pr_ne h), Function.update_self]
  | rw [Function.update_noteq (pie_pr_ne h), Function.update_same]

/- English proof (translation)
Unfold `pie_sw`. Use `first`. Consider the case `rw [Function.update_of_ne hk, Function.update_of_ne hk']`. Consider the case `rw [Function.update_noteq hk, Function.update_noteq hk']`.
-/
theorem pie_sw_other {n : ℕ} (mu : Fin n → ℕ) {j k : Fin n} (hk : k ≠ j) (hk' : k ≠ pie_pr j) :
    pie_sw mu j k = mu k := by
  unfold pie_sw
  first
  | rw [Function.update_of_ne hk, Function.update_of_ne hk']
  | rw [Function.update_noteq hk, Function.update_noteq hk']

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Function.comp_apply, rhoN]`. Establish `hj` using `j.isLt`. Establish `hpr : (pie_pr j).val = j.val - 1` using `rfl`. Distinguish the cases in `hkj : k = j`.

Substitute `hkj` using the available equality. Rewrite using `[Equiv.swap_apply_right, pie_sw_self]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hkp : k = pie_pr j`. Substitute `hkp` using the available equality.

Rewrite using `[Equiv.swap_apply_left, pie_sw_pr mu h]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hkp hkj, pie_sw_other mu hkj hkp]`.
-/
theorem pie_sw_rho {n : ℕ} (mu : Fin n → ℕ) {j : Fin n} (h : 0 < j.val) (h1 : 1 ≤ mu j) :
    pie_sw mu j + rhoN n = (mu + rhoN n) ∘ Equiv.swap (pie_pr j) j := by
  funext k
  simp only [Pi.add_apply, Function.comp_apply, rhoN]
  have hj := j.isLt
  have hpr : (pie_pr j).val = j.val - 1 := rfl
  by_cases hkj : k = j
  · subst hkj
    rw [Equiv.swap_apply_right, pie_sw_self]
    omega
  · by_cases hkp : k = pie_pr j
    · subst hkp
      rw [Equiv.swap_apply_left, pie_sw_pr mu h]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hkp hkj, pie_sw_other mu hkj hkp]

/- English proof (translation)
Unfold `alt`. Establish `e : (Matrix.of fun a b : Fin n => (X a : MvPolynomial (Fin n) ℤ) ^ (ga ∘ Equiv.swap i j) b) = (Matrix.of fun a b : Fin n => (X a : MvPolynomial (Fin n) ℤ) ^ ga b).submatrix id (Equiv.swap i j)`. Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.det_permute', Equiv.Perm.sign_swap hij]`.

Simplify using the standard rewrite rules.
-/
theorem pie_alt_swap (n : ℕ) (ga : Fin n → ℕ) {i j : Fin n} (hij : i ≠ j) :
    alt n (ga ∘ Equiv.swap i j) = - alt n ga := by
  unfold alt
  have e : (Matrix.of fun a b : Fin n => (X a : MvPolynomial (Fin n) ℤ) ^ (ga ∘ Equiv.swap i j) b) =
      (Matrix.of fun a b : Fin n => (X a : MvPolynomial (Fin n) ℤ) ^ ga b).submatrix id (Equiv.swap i j) := by
    ext a b
    rfl
  rw [e, Matrix.det_permute', Equiv.Perm.sign_swap hij]
  simp

/- English proof (translation)
Unfold `alt`. Conclude with `Matrix.det_zero_of_column_eq hij fun k => by simp [h]`.
-/
theorem pie_alt_zero (n : ℕ) (ga : Fin n → ℕ) {i j : Fin n} (hij : i ≠ j) (h : ga i = ga j) :
    alt n ga = 0 := by
  unfold alt
  exact Matrix.det_zero_of_column_eq hij fun k => by simp [h]

open Classical in

def pie_S {n : ℕ} (lam : Fin n → ℕ) (b : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (∑ j, lam j + b + 1)).filter
    fun mu => (∀ j, lam j ≤ mu j) ∧ ∑ j, mu j = ∑ j, lam j + b

/- English proof (translation)
Unfold `pie_S`. Rewrite using `[Finset.mem_filter, Fintype.mem_piFinset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩`. Conclude with `h`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun j => ?_, h1, h2⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_range]`. Use `Finset.single_le_sum (f := mu) (fun i _ => Nat.zero_le (mu i)) (Finset.mem_univ j)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem pie_mem_S {n : ℕ} {lam : Fin n → ℕ} {b : ℕ} {mu : Fin n → ℕ} :
    mu ∈ pie_S lam b ↔ (∀ j, lam j ≤ mu j) ∧ ∑ j, mu j = ∑ j, lam j + b := by
  unfold pie_S
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, h1, h2⟩
    rw [Finset.mem_range]
    have := Finset.single_le_sum (f := mu) (fun i _ => Nat.zero_le (mu i)) (Finset.mem_univ j)
    omega

/- English proof (translation)
Unfold `pie_cnt`. Use `first`. Consider the case `(rw [Multiset.sum_count_eq_card] all_goals first`. Consider the case `exact s.2`. Consider the case `exact fun a _ => Finset.mem_univ a)`.

Consider the case `(rw [← s.2, ← Multiset.toFinset_sum_count_eq]`. Conclude with `(Finset.sum_subset (Finset.subset_univ _) fun x _ hx => Multiset.count_eq_zero.2 (by simpa using hx)).symm)`.
-/
private lemma sum_pie_cnt_eq {n b : ℕ} (s : Sym (Fin n) b) : ∑ j, pie_cnt s j = b := by
  unfold pie_cnt
  first
  | (rw [Multiset.sum_count_eq_card]
     all_goals first
       | exact s.2
       | exact fun a _ => Finset.mem_univ a)
  | (rw [← s.2, ← Multiset.toFinset_sum_count_eq]
     exact (Finset.sum_subset (Finset.subset_univ _)
       fun x _ hx => Multiset.count_eq_zero.2 (by simpa using hx)).symm)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `first`. Consider the case `exact Multiset.ext' fun a => congrFun h a`. Consider the case `exact Multiset.ext.2 fun a => congrFun h a`.
-/
private lemma pie_cnt_injective {n b : ℕ} {s1 s2 : Sym (Fin n) b} (h : pie_cnt s1 = pie_cnt s2) :
    s1 = s2 := by
  apply Subtype.ext
  first
  | exact Multiset.ext' fun a => congrFun h a
  | exact Multiset.ext.2 fun a => congrFun h a

/- English proof (translation)
Use `Finset.sum_bij (fun s _ => lam + pie_cnt s) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `s _ show lam + pie_cnt s ∈ pie_S lam b`. Rewrite using `[pie_mem_S]`. Use `⟨fun j => Nat.le_add_right _ _, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`.

Rewrite using `[Finset.sum_add_distrib, sum_pie_cnt_eq s]`. Introduce `s1 _ s2 _ h12`. Apply `pie_cnt_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Establish `h3` using `congrFun h12 j`.

Simplify using `only [Pi.add_apply] at h3`. Use linear arithmetic over natural numbers and integers. Introduce `mu hmu`. Rewrite `hmu` using `[pie_mem_S]`. Take `⟨hle, hsum⟩` from `hmu`.

Set `M : Multiset (Fin n)` to `∑ j, Multiset.replicate (mu j - lam j) j`. Establish `hcount : ∀ i, Multiset.count i M = mu i - lam i`. Introduce `i`. Simplify using `[M, Multiset.count_sum', Multiset.count_replicate]`. Establish `hcard : Multiset.card M = b`.

Simplify using `only [M, Multiset.card_sum, Multiset.card_replicate]`. Establish `h2 : ∑ j, (mu j - lam j) + ∑ j, lam j = ∑ j, mu j`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hle j)`. Use linear arithmetic over natural numbers and integers.

Use `⟨⟨M, hcard⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show lam i + Multiset.count i M = mu i`. Rewrite using `[hcount i]`. Use `hle i` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce `s _ show alt n (lam + rhoN n + pie_cnt s) = alt n (lam + pie_cnt s + rhoN n)`. Rewrite using `[add_right_comm]`.
-/
theorem pie_step2 (n b : ℕ) (lam : Fin n → ℕ) :
    ∑ s : Sym (Fin n) b, alt n (lam + rhoN n + pie_cnt s) = ∑ mu ∈ pie_S lam b, alt n (mu + rhoN n) := by
  classical
  refine Finset.sum_bij (fun s _ => lam + pie_cnt s) ?_ ?_ ?_ ?_
  · intro s _
    show lam + pie_cnt s ∈ pie_S lam b
    rw [pie_mem_S]
    refine ⟨fun j => Nat.le_add_right _ _, ?_⟩
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, sum_pie_cnt_eq s]
  · intro s1 _ s2 _ h12
    apply pie_cnt_injective
    funext j
    have h3 := congrFun h12 j
    simp only [Pi.add_apply] at h3
    omega
  · intro mu hmu
    rw [pie_mem_S] at hmu
    obtain ⟨hle, hsum⟩ := hmu
    let M : Multiset (Fin n) := ∑ j, Multiset.replicate (mu j - lam j) j
    have hcount : ∀ i, Multiset.count i M = mu i - lam i := by
      intro i
      simp [M, Multiset.count_sum', Multiset.count_replicate]
    have hcard : Multiset.card M = b := by
      simp only [M, Multiset.card_sum, Multiset.card_replicate]
      have h2 : ∑ j, (mu j - lam j) + ∑ j, lam j = ∑ j, mu j := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hle j)
      omega
    refine ⟨⟨M, hcard⟩, Finset.mem_univ _, ?_⟩
    funext i
    show lam i + Multiset.count i M = mu i
    rw [hcount i]
    have := hle i
    omega
  · intro s _
    show alt n (lam + rhoN n + pie_cnt s) = alt n (lam + pie_cnt s + rhoN n)
    rw [add_right_comm]

/- English proof (translation)
Establish `e : ∑ k, (pie_sw mu j + rhoN n) k = ∑ k, (mu + rhoN n) k`. Rewrite using `[pie_sw_rho mu h h1]`. Conclude with `Equiv.sum_comp (Equiv.swap (pie_pr j) j) (mu + rhoN n)`. Simplify using `only [Pi.add_apply, Finset.sum_add_distrib] at e`. Use linear arithmetic over natural numbers and integers.
-/
theorem pie_sw_sum {n : ℕ} (mu : Fin n → ℕ) {j : Fin n} (h : 0 < j.val) (h1 : 1 ≤ mu j) :
    ∑ k, pie_sw mu j k = ∑ k, mu k := by
  have e : ∑ k, (pie_sw mu j + rhoN n) k = ∑ k, (mu + rhoN n) k := by
    rw [pie_sw_rho mu h h1]
    exact Equiv.sum_comp (Equiv.swap (pie_pr j) j) (mu + rhoN n)
  simp only [Pi.add_apply, Finset.sum_add_distrib] at e
  omega

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality. Rewrite using `[pie_sw_self, pie_sw_pr mu h]`. Use linear arithmetic over natural numbers and integers.

Distinguish the cases in `hkp : k = pie_pr j`. Substitute `hkp` using the available equality. Rewrite using `[pie_sw_pr _ h, pie_sw_self]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[pie_sw_other _ hkj hkp, pie_sw_other _ hkj hkp]`.
-/
theorem pie_sw_sw {n : ℕ} (mu : Fin n → ℕ) {j : Fin n} (h : 0 < j.val) (h1 : 1 ≤ mu j) :
    pie_sw (pie_sw mu j) j = mu := by
  funext k
  by_cases hkj : k = j
  · subst hkj
    rw [pie_sw_self, pie_sw_pr mu h]
    omega
  · by_cases hkp : k = pie_pr j
    · subst hkp
      rw [pie_sw_pr _ h, pie_sw_self]
      omega
    · rw [pie_sw_other _ hkj hkp, pie_sw_other _ hkj hkp]

/- English proof (translation)
Unfold `pie_B`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.
-/
theorem pie_mem_B {n : ℕ} {lam mu : Fin n → ℕ} {j : Fin n} :
    j ∈ pie_B lam mu ↔ 0 < j.val ∧ lam (pie_pr j) < mu j := by
  unfold pie_B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/- English proof (translation)
Establish `hj'` using `pie_mem_B.1 hj`. Establish `hjB : j ∈ pie_B lam (pie_sw mu j)`. Rewrite using `[pie_mem_B, pie_sw_self]`. Conclude with `⟨hj'.1, by omega⟩`. Use `⟨⟨j, hjB⟩, ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Apply `Finset.max'_le` to reduce the goal to its premises. Introduce `k hk`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Establish `hkj : k ≠ j` using `hlt.ne'`. Establish `hkp : k ≠ pie_pr j`. Introduce `e`. Establish `h2 : k.val = j.val - 1` using `congrArg Fin.val e`. Establish `h3 : j.val < k.val` using `hlt`.

Use linear arithmetic over natural numbers and integers. Establish `hk'` using `pie_mem_B.1 hk`. Rewrite `hk'` using `[pie_sw_other mu hkj hkp]`. Establish `h4` using `hmax k (pie_mem_B.2 hk')`. Conclude with `absurd h4 (not_le.2 hlt)`.

Conclude with `Finset.le_max' _ j hjB`.
-/
theorem pie_B_sw {n : ℕ} {lam mu : Fin n → ℕ} {j : Fin n} (hj : j ∈ pie_B lam mu)
    (hmax : ∀ k ∈ pie_B lam mu, k ≤ j) (hle : lam (pie_pr j) ≤ mu (pie_pr j)) :
    ∃ h' : (pie_B lam (pie_sw mu j)).Nonempty, (pie_B lam (pie_sw mu j)).max' h' = j := by
  have hj' := pie_mem_B.1 hj
  have hjB : j ∈ pie_B lam (pie_sw mu j) := by
    rw [pie_mem_B, pie_sw_self]
    exact ⟨hj'.1, by omega⟩
  refine ⟨⟨j, hjB⟩, ?_⟩
  apply le_antisymm
  · apply Finset.max'_le
    intro k hk
    by_contra hlt
    push_neg at hlt
    have hkj : k ≠ j := hlt.ne'
    have hkp : k ≠ pie_pr j := by
      intro e
      have h2 : k.val = j.val - 1 := congrArg Fin.val e
      have h3 : j.val < k.val := hlt
      omega
    have hk' := pie_mem_B.1 hk
    rw [pie_sw_other mu hkj hkp] at hk'
    have h4 := hmax k (pie_mem_B.2 hk')
    exact absurd h4 (not_le.2 hlt)
  · exact Finset.le_max' _ j hjB

def pie_g {n : ℕ} (lam mu : Fin n → ℕ) : Fin n → ℕ :=
  if h : (pie_B lam mu).Nonempty then pie_sw mu ((pie_B lam mu).max' h) else mu

open Classical in
/- English proof (translation)
Establish `key : ∀ mu : Fin n → ℕ, (∀ j, lam j ≤ mu j) → (pie_B lam mu).Nonempty → ∃ j : Fin n, 0 < j.val ∧ 1 ≤ mu j ∧ pie_g lam mu = pie_sw mu j ∧ (∀ k, lam k ≤ pie_sw mu j k) ∧ ∃ h' : (pie_B lam (pie_sw mu j)).Nonempty, (pie_B lam (pie_sw mu j)).max' h' = j`. Introduce `mu hle hB`. Take `⟨j, hjdef⟩ : ∃ j, (pie_B lam mu).max' hB = j` from `⟨_, rfl⟩`. Establish `hjB : j ∈ pie_B lam mu`. Rewrite using `[← hjdef]`.

Conclude with `Finset.max'_mem _ _`. Establish `hmax : ∀ k ∈ pie_B lam mu, k ≤ j` using `fun k hk => by`. Rewrite using `[← hjdef]`. Conclude with `Finset.le_max' _ k hk`. Establish `hj` using `pie_mem_B.1 hjB`.

Establish `hj2` using `hj.2`. Establish `hprj : pie_pr j ≤ j` using `by show (pie_pr j).val ≤ j.val`. Conclude with `Nat.sub_le _ _`. Establish `hl : lam j ≤ lam (pie_pr j)` using `hlam hprj`. Establish `hg : pie_g lam mu = pie_sw mu j`.

Unfold `pie_g`. Rewrite using `[dif_pos hB, hjdef]`. Use `⟨j, hj.1, by omega, hg, ?_, pie_B_sw hjB hmax (hle _)⟩` and prove the remaining obligations. Introduce `k`. Distinguish the cases in `hkj : k = j`.

Rewrite using `[hkj, pie_sw_self]`. Use `hle (pie_pr j)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hkp : k = pie_pr j`. Rewrite using `[hkp, pie_sw_pr mu hj.1]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[pie_sw_other mu hkj hkp]`. Conclude with `hle k`. Use `Finset.sum_involution (fun mu _ => pie_g lam mu) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `mu hmu`.

Establish `hmu'` using `hmu`. Rewrite `hmu'` using `[Finset.mem_filter, pie_mem_S]`. Take `⟨⟨hle, -⟩, hB⟩` from `hmu'`. Take `⟨j, hj0, hj1, hg, -, -⟩` from `key mu hle hB`. Use `show alt n (mu + rhoN n) + alt n (pie_g lam mu + rhoN n) = 0`.

Rewrite using `[hg, pie_sw_rho mu hj0 hj1, pie_alt_swap n _ (pie_pr_ne hj0)]`. Use `first`. Consider the case `exact add_neg_cancel _`. Consider the case `exact add_right_neg _`. Consider the case `simp`.

Introduce `mu hmu hne`. Establish `hmu'` using `hmu`. Rewrite `hmu'` using `[Finset.mem_filter, pie_mem_S]`. Take `⟨⟨hle, -⟩, hB⟩` from `hmu'`. Take `⟨j, hj0, hj1, hg, -, -⟩` from `key mu hle hB`.

Use `show pie_g lam mu ≠ mu`. Rewrite using `[hg]`. Introduce `heq`. Apply `hne` to reduce the goal to its premises. Establish `e` using `pie_sw_rho mu hj0 hj1`.

Rewrite `e` using `[heq]`. Establish `e2` using `congrFun e j`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_right] at e2`. Conclude with `pie_alt_zero n _ (pie_pr_ne hj0) e2.symm`. Introduce `mu hmu`.

Establish `hmu'` using `hmu`. Rewrite `hmu'` using `[Finset.mem_filter, pie_mem_S]`. Take `⟨⟨hle, hsum⟩, hB⟩` from `hmu'`. Take `⟨j, hj0, hj1, hg, hle', hne', -⟩` from `key mu hle hB`. Use `show pie_g lam mu ∈ (pie_S lam b).filter (fun mu => (pie_B lam mu).Nonempty)`.

Rewrite using `[hg, Finset.mem_filter, pie_mem_S]`. Conclude with `⟨⟨hle', by rw [pie_sw_sum mu hj0 hj1, hsum]⟩, hne'⟩`. Introduce `mu hmu`. Establish `hmu'` using `hmu`. Rewrite `hmu'` using `[Finset.mem_filter, pie_mem_S]`.

Take `⟨⟨hle, -⟩, hB⟩` from `hmu'`. Take `⟨j, hj0, hj1, hg, -, hne', hmax'⟩` from `key mu hle hB`. Use `show pie_g lam (pie_g lam mu) = mu`. Rewrite using `[hg]`. Unfold `pie_g`.

Rewrite using `[dif_pos hne', hmax', pie_sw_sw mu hj0 hj1]`.
-/
theorem pie_bad_zero (n b : ℕ) (lam : Fin n → ℕ) (hlam : Antitone lam) :
    ∑ mu ∈ (pie_S lam b).filter (fun mu => (pie_B lam mu).Nonempty), alt n (mu + rhoN n) = 0 := by
  have key : ∀ mu : Fin n → ℕ, (∀ j, lam j ≤ mu j) → (pie_B lam mu).Nonempty →
      ∃ j : Fin n, 0 < j.val ∧ 1 ≤ mu j ∧ pie_g lam mu = pie_sw mu j ∧ (∀ k, lam k ≤ pie_sw mu j k) ∧
        ∃ h' : (pie_B lam (pie_sw mu j)).Nonempty, (pie_B lam (pie_sw mu j)).max' h' = j := by
    intro mu hle hB
    obtain ⟨j, hjdef⟩ : ∃ j, (pie_B lam mu).max' hB = j := ⟨_, rfl⟩
    have hjB : j ∈ pie_B lam mu := by
      rw [← hjdef]
      exact Finset.max'_mem _ _
    have hmax : ∀ k ∈ pie_B lam mu, k ≤ j := fun k hk => by
      rw [← hjdef]
      exact Finset.le_max' _ k hk
    have hj := pie_mem_B.1 hjB
    have hj2 := hj.2
    have hprj : pie_pr j ≤ j := by
      show (pie_pr j).val ≤ j.val
      exact Nat.sub_le _ _
    have hl : lam j ≤ lam (pie_pr j) := hlam hprj
    have hg : pie_g lam mu = pie_sw mu j := by
      unfold pie_g
      rw [dif_pos hB, hjdef]
    refine ⟨j, hj.1, by omega, hg, ?_, pie_B_sw hjB hmax (hle _)⟩
    intro k
    by_cases hkj : k = j
    · rw [hkj, pie_sw_self]
      have := hle (pie_pr j)
      omega
    · by_cases hkp : k = pie_pr j
      · rw [hkp, pie_sw_pr mu hj.1]
        omega
      · rw [pie_sw_other mu hkj hkp]
        exact hle k
  refine Finset.sum_involution (fun mu _ => pie_g lam mu) ?_ ?_ ?_ ?_
  · intro mu hmu
    have hmu' := hmu
    rw [Finset.mem_filter, pie_mem_S] at hmu'
    obtain ⟨⟨hle, -⟩, hB⟩ := hmu'
    obtain ⟨j, hj0, hj1, hg, -, -⟩ := key mu hle hB
    show alt n (mu + rhoN n) + alt n (pie_g lam mu + rhoN n) = 0
    rw [hg, pie_sw_rho mu hj0 hj1, pie_alt_swap n _ (pie_pr_ne hj0)]
    first
    | exact add_neg_cancel _
    | exact add_right_neg _
    | simp
  · intro mu hmu hne
    have hmu' := hmu
    rw [Finset.mem_filter, pie_mem_S] at hmu'
    obtain ⟨⟨hle, -⟩, hB⟩ := hmu'
    obtain ⟨j, hj0, hj1, hg, -, -⟩ := key mu hle hB
    show pie_g lam mu ≠ mu
    rw [hg]
    intro heq
    apply hne
    have e := pie_sw_rho mu hj0 hj1
    rw [heq] at e
    have e2 := congrFun e j
    simp only [Function.comp_apply, Equiv.swap_apply_right] at e2
    exact pie_alt_zero n _ (pie_pr_ne hj0) e2.symm
  · intro mu hmu
    have hmu' := hmu
    rw [Finset.mem_filter, pie_mem_S] at hmu'
    obtain ⟨⟨hle, hsum⟩, hB⟩ := hmu'
    obtain ⟨j, hj0, hj1, hg, hle', hne', -⟩ := key mu hle hB
    show pie_g lam mu ∈ (pie_S lam b).filter (fun mu => (pie_B lam mu).Nonempty)
    rw [hg, Finset.mem_filter, pie_mem_S]
    exact ⟨⟨hle', by rw [pie_sw_sum mu hj0 hj1, hsum]⟩, hne'⟩
  · intro mu hmu
    have hmu' := hmu
    rw [Finset.mem_filter, pie_mem_S] at hmu'
    obtain ⟨⟨hle, -⟩, hB⟩ := hmu'
    obtain ⟨j, hj0, hj1, hg, -, hne', hmax'⟩ := key mu hle hB
    show pie_g lam (pie_g lam mu) = mu
    rw [hg]
    unfold pie_g
    rw [dif_pos hne', hmax', pie_sw_sw mu hj0 hj1]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hn i j hij`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hn` to reduce the goal to its premises.

Establish `hpr : pie_pr j = i` using `Fin.ext (by show j.val - 1 = i.val; omega)`. Conclude with `⟨j, pie_mem_B.2 ⟨by omega, by rw [hpr]; exact hc⟩⟩`. Introduce and unpack `h ⟨j, hj⟩`. Take `⟨hj0, hj1⟩` from `pie_mem_B.1 hj`. Establish `h2` using `h (pie_pr j) j (by show j.val - 1 + 1 = j.val; omega)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem pie_good_iff {n : ℕ} (lam mu : Fin n → ℕ) :
    ¬ (pie_B lam mu).Nonempty ↔ ∀ i j : Fin n, i.val + 1 = j.val → mu j ≤ lam i := by
  constructor
  · intro hn i j hij
    by_contra hc
    push_neg at hc
    apply hn
    have hpr : pie_pr j = i := Fin.ext (by show j.val - 1 = i.val; omega)
    exact ⟨j, pie_mem_B.2 ⟨by omega, by rw [hpr]; exact hc⟩⟩
  · rintro h ⟨j, hj⟩
    obtain ⟨hj0, hj1⟩ := pie_mem_B.1 hj
    have h2 := h (pie_pr j) j (by show j.val - 1 + 1 = j.val; omega)
    omega

/- English proof (translation)
Unfold `adm1`. Introduce `n lam hlam b`. Establish `hset : (pie_S lam b).filter (fun mu => ¬ (pie_B lam mu).Nonempty) = (Fintype.piFinset fun _ : Fin n => Finset.range (∑ j, lam j + b + 1)).filter (fun mu => Interlace lam mu ∧ ∑ j, mu j = ∑ j, lam j + b)`. Use extensionality with `mu`. Rewrite using `[Finset.mem_filter, Finset.mem_filter, pie_mem_S, pie_good_iff]`.

Unfold `Interlace`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Establish `hm : mu ∈ pie_S lam b` using `pie_mem_S.2 ⟨h1, h2⟩`. Unfold `pie_S at hm`.

Conclude with `⟨(Finset.mem_filter.1 hm).1, ⟨h1, h3⟩, h2⟩`. Introduce and unpack `⟨-, ⟨h1, h3⟩, h2⟩`. Conclude with `⟨⟨h1, h2⟩, h3⟩`. Rewrite using `[pie_step1, pie_step2, ← Finset.sum_filter_add_sum_filter_not (pie_S lam b) (fun mu => (pie_B lam mu).Nonempty), pie_bad_zero n b lam hlam, zero_add, hset]`.
-/
theorem positivity_condition_holds (D : Formalism.BasicNotions.D7) : adm1 D := by
  classical
  unfold adm1
  intro n lam hlam b
  have hset : (pie_S lam b).filter (fun mu => ¬ (pie_B lam mu).Nonempty) =
      (Fintype.piFinset fun _ : Fin n => Finset.range (∑ j, lam j + b + 1)).filter
        (fun mu => Interlace lam mu ∧ ∑ j, mu j = ∑ j, lam j + b) := by
    ext mu
    rw [Finset.mem_filter, Finset.mem_filter, pie_mem_S, pie_good_iff]
    unfold Interlace
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hm : mu ∈ pie_S lam b := pie_mem_S.2 ⟨h1, h2⟩
      unfold pie_S at hm
      exact ⟨(Finset.mem_filter.1 hm).1, ⟨h1, h3⟩, h2⟩
    · rintro ⟨-, ⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  rw [pie_step1, pie_step2,
    ← Finset.sum_filter_add_sum_filter_not (pie_S lam b) (fun mu => (pie_B lam mu).Nonempty),
    pie_bad_zero n b lam hlam, zero_add, hset]

end Formalism.MainNotions.G.GLWeightTheory
