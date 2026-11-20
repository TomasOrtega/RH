import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section LamAbs

variable {R : Type} [CommRing R] {F : Type} [Field F] {σ τ : Type} {J : ℕ}

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih, monomial_mul]`.
-/
theorem lam_prod_monomial {ι : Type} (s : Finset ι) (f : ι → τ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, monomial (f i) (a i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih, monomial_mul]

abbrev lam_ph (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (j : Fin J) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval fun v => (X (g j v) : MvPolynomial τ R) ^ e j v

/- English proof (translation)
Establish `h : ∀ j, lam_ph g e j (y j) = ∑ m ∈ (y j).support, monomial (imgMon (g j) (e j) m) (coeff m (y j))`. Introduce `j`. Use `conv_lhs => rw [(y j).as_sum]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => aeval_pow_monomial _ _ _ _`.

Rewrite using `[Finset.prod_congr rfl fun j _ => h j, Finset.prod_univ_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => lam_prod_monomial _ _ _`.
-/
theorem lam_expand (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (y : Fin J → MvPolynomial σ R) :
    ∏ j, lam_ph g e j (y j) = ∑ m ∈ Fintype.piFinset (fun j => (y j).support),
      monomial (∑ j, imgMon (g j) (e j) (m j)) (∏ j, coeff (m j) (y j)) := by
  classical
  have h : ∀ j, lam_ph g e j (y j) = ∑ m ∈ (y j).support, monomial (imgMon (g j) (e j) m) (coeff m (y j)) := by
    intro j
    conv_lhs => rw [(y j).as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => aeval_pow_monomial _ _ _ _
  rw [Finset.prod_congr rfl fun j _ => h j, Finset.prod_univ_sum]
  exact Finset.sum_congr rfl fun m _ => lam_prod_monomial _ _ _

/- English proof (translation)
Rewrite using `[coeff_monomial_mul, one_mul, lam_expand, coeff_sum, Finset.sum_eq_single s]`. Rewrite using `[coeff_monomial, if_pos rfl]`. Introduce `m hm hne`. Rewrite using `[coeff_monomial, if_neg]`. Introduce `h`.

Apply `hne` to reduce the goal to its premises. Use `hinj m s (fun j => ?_) hs h` and prove the remaining obligations. Use `Fintype.mem_piFinset.mp hm j` as an intermediate fact. Conclude with `((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hy j)) (Finset.mem_coe.mpr this)`. Introduce `hnot`.

Rewrite using `[coeff_monomial, if_pos rfl]`. Rewrite `hnot` using `[Fintype.mem_piFinset]`. Use `push Not at hnot`. Take `⟨j, hj⟩` from `hnot`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ j) (MvPolynomial.notMem_support_iff.mp hj)`.
-/
theorem lam_coeff (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : τ →₀ ℕ) (S : Fin J → Set (σ →₀ ℕ))
    (hinj : ∀ m m' : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S j) → (∀ j, m' j ∈ S j) →
      ∑ j, imgMon (g j) (e j) (m j) = ∑ j, imgMon (g j) (e j) (m' j) → m = m')
    (y : Fin J → MvPolynomial σ F) (hy : ∀ j, y j ∈ restrictSupport F (S j)) (s : Fin J → σ →₀ ℕ)
    (hs : ∀ j, s j ∈ S j) :
    coeff (l + ∑ j, imgMon (g j) (e j) (s j)) (monomial l (1 : F) * ∏ j, lam_ph g e j (y j)) =
      ∏ j, coeff (s j) (y j) := by
  classical
  rw [coeff_monomial_mul, one_mul, lam_expand, coeff_sum, Finset.sum_eq_single s]
  · rw [coeff_monomial, if_pos rfl]
  · intro m hm hne
    rw [coeff_monomial, if_neg]
    intro h
    apply hne
    refine hinj m s (fun j => ?_) hs h
    have := Fintype.mem_piFinset.mp hm j
    exact ((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hy j)) (Finset.mem_coe.mpr this)
  · intro hnot
    rw [coeff_monomial, if_pos rfl]
    rw [Fintype.mem_piFinset] at hnot
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    exact Finset.prod_eq_zero (Finset.mem_univ j) (MvPolynomial.notMem_support_iff.mp hj)

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination F u) (LinearMap.ker_eq_bot.mpr hu)`. Establish `h1 : ∀ a, ψ (u a) = Finsupp.single a 1`. Introduce `a`. Establish `h2 : Finsupp.linearCombination F u (Finsupp.single a 1) = u a` using `by simp`. Rewrite using `[← h2]`.

Conclude with `congrArg (fun f => f (Finsupp.single a 1)) hψ`. Use `⟨ψ, fun a => by rw [h1]; simp, fun a b hb => by rw [h1, Finsupp.single_apply, if_neg hb.symm]⟩` and prove the remaining obligations.
-/
theorem lam_dual {I : Type} {M : Type} [AddCommGroup M] [Module F M] (u : I → M)
    (hu : LinearIndependent F u) :
    ∃ ψ : M →ₗ[F] (I →₀ F), (∀ a, ψ (u a) a = 1) ∧ ∀ a b, b ≠ a → ψ (u a) b = 0 := by
  classical
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination F u)
    (LinearMap.ker_eq_bot.mpr hu)
  have h1 : ∀ a, ψ (u a) = Finsupp.single a 1 := by
    intro a
    have h2 : Finsupp.linearCombination F u (Finsupp.single a 1) = u a := by simp
    rw [← h2]
    exact congrArg (fun f => f (Finsupp.single a 1)) hψ
  refine ⟨ψ, fun a => by rw [h1]; simp, fun a b hb => by rw [h1, Finsupp.single_apply, if_neg hb.symm]⟩

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc b`. Establish `hstar : ∀ s : Fin J → σ →₀ ℕ, ∑ a, c a * ∏ j, coeff (s j) (u j (a j)) = 0`. Introduce `s`. Distinguish the cases in `hs : ∀ j, s j ∈ S j`.

Establish `h1` using `congrArg (coeff (l + ∑ j, imgMon (g j) (e j) (s j))) hc`. Rewrite `h1` using `[coeff_sum, coeff_zero]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul, lam_coeff g e l S hinj (fun j => u j (a j)) (fun j => hS j (a j)) s hs, smul_eq_mul]`.

Use `push Not at hs`. Take `⟨j0, hj0⟩` from `hs`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ j0) (li_coeff_zero (hS j0 (a j0)) hj0), mul_zero]`. Use `choose ψ hψ using fun j => lam_dual (u j) (hu j)`.

Set `supp : ∀ j, Finset (σ →₀ ℕ)` to `fun j => Finset.univ.biUnion fun a => (u j a).support`. Set `w : ∀ j, (σ →₀ ℕ) → F` to `fun j m => ψ j (monomial m 1) (b j)`. Establish `hexp : ∀ j (a : I j), (ψ j (u j a)) (b j) = ∑ m ∈ supp j, coeff m (u j a) * w j m`. Introduce `j a`. Use `conv_lhs => rw [(u j a).as_sum]`.

Rewrite using `[map_sum, Finsupp.finsetSum_apply]`. Establish `hsub : (u j a).support ⊆ supp j` using `fun m hm => Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hm⟩`. Rewrite using `[← Finset.sum_subset hsub]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `: (monomial m (coeff m (u j a)) : MvPolynomial σ F) = coeff m (u j a) • monomial m (1 : F)`.

Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Introduce `m _ hm`. Rewrite using `[MvPolynomial.notMem_support_iff.mp hm, zero_mul]`. Establish `h1 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = c b`.

Rewrite using `[Finset.sum_eq_single b]`. Rewrite using `[Finset.prod_eq_one fun j _ => (hψ j).1 (b j), mul_one]`. Introduce `a _ hab`. Take `⟨j, hj⟩` from `Function.ne_iff.mp hab`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ j) ((hψ j).2 (a j) (b j) hj.symm), mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `h2 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = 0`. Establish `e1 : ∀ a : ∀ j, I j, c a * ∏ j, (ψ j (u j (a j))) (b j) = ∑ s ∈ Fintype.piFinset supp, (c a * ∏ j, coeff (s j) (u j (a j))) * ∏ j, w j (s j)`. Introduce `a`.

Rewrite using `[Finset.prod_congr rfl fun j _ => hexp j (a j), Finset.prod_univ_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, mul_assoc]`. Rewrite using `[Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_comm]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_mul, hstar s, zero_mul]`. Rewrite using `[← h1, h2]`.
-/
theorem lam_li_fixed (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : τ →₀ ℕ) (S : Fin J → Set (σ →₀ ℕ))
    (hinj : ∀ m m' : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S j) → (∀ j, m' j ∈ S j) →
      ∑ j, imgMon (g j) (e j) (m j) = ∑ j, imgMon (g j) (e j) (m' j) → m = m')
    {I : Fin J → Type} [∀ j, Fintype (I j)] (u : ∀ j, I j → MvPolynomial σ F)
    (hu : ∀ j, LinearIndependent F (u j)) (hS : ∀ j i, u j i ∈ restrictSupport F (S j)) :
    LinearIndependent F fun a : ∀ j, I j => monomial l (1 : F) * ∏ j, lam_ph g e j (u j (a j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have hstar : ∀ s : Fin J → σ →₀ ℕ, ∑ a, c a * ∏ j, coeff (s j) (u j (a j)) = 0 := by
    intro s
    by_cases hs : ∀ j, s j ∈ S j
    · have h1 := congrArg (coeff (l + ∑ j, imgMon (g j) (e j) (s j))) hc
      rw [coeff_sum, coeff_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [coeff_smul, lam_coeff g e l S hinj (fun j => u j (a j)) (fun j => hS j (a j)) s hs, smul_eq_mul]
    · push Not at hs
      obtain ⟨j0, hj0⟩ := hs
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [Finset.prod_eq_zero (Finset.mem_univ j0) (li_coeff_zero (hS j0 (a j0)) hj0), mul_zero]
  choose ψ hψ using fun j => lam_dual (u j) (hu j)
  let supp : ∀ j, Finset (σ →₀ ℕ) := fun j => Finset.univ.biUnion fun a => (u j a).support
  let w : ∀ j, (σ →₀ ℕ) → F := fun j m => ψ j (monomial m 1) (b j)
  have hexp : ∀ j (a : I j), (ψ j (u j a)) (b j) = ∑ m ∈ supp j, coeff m (u j a) * w j m := by
    intro j a
    conv_lhs => rw [(u j a).as_sum]
    rw [map_sum, Finsupp.finsetSum_apply]
    have hsub : (u j a).support ⊆ supp j := fun m hm => Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hm⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m _ => ?_
      have : (monomial m (coeff m (u j a)) : MvPolynomial σ F) = coeff m (u j a) • monomial m (1 : F) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro m _ hm
      rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]
  have h1 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = c b := by
    rw [Finset.sum_eq_single b]
    · rw [Finset.prod_eq_one fun j _ => (hψ j).1 (b j), mul_one]
    · intro a _ hab
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
      rw [Finset.prod_eq_zero (Finset.mem_univ j) ((hψ j).2 (a j) (b j) hj.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = 0 := by
    have e1 : ∀ a : ∀ j, I j, c a * ∏ j, (ψ j (u j (a j))) (b j) =
        ∑ s ∈ Fintype.piFinset supp, (c a * ∏ j, coeff (s j) (u j (a j))) * ∏ j, w j (s j) := by
      intro a
      rw [Finset.prod_congr rfl fun j _ => hexp j (a j), Finset.prod_univ_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.prod_mul_distrib, mul_assoc]
    rw [Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← Finset.sum_mul, hstar s, zero_mul]
  rw [← h1, h2]

/- English proof (translation)
Use `li_graded _ (fun x => x.1) (fun f => {n | ∃ m : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S f j) ∧ n = l f + ∑ j, imgMon (g j) (e j) (m j)}) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `k k' n ⟨m, hm, rfl⟩ ⟨m', hm', h⟩`. Conclude with `(hinj k k' m m' hm hm' h).1`. Introduce `x`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`.

Introduce `n hn`. Establish `hn' : coeff n (monomial (l x.1) (1 : F) * ∏ j, lam_ph g e j (u x.1 j (x.2 j))) ≠ 0` using `MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)`. Rewrite `hn'` using `[coeff_monomial_mul']`. Use `split_ifs at hn' with hle`. Rewrite `hn'` using `[one_mul, lam_expand, coeff_sum]`.

Take `⟨m, hm, hm0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hn'`. Rewrite `hm0` using `[coeff_monomial]`. Use `split_ifs at hm0 with heq`. Use `⟨m, fun j => ?_, ?_⟩` and prove the remaining obligations. Conclude with `((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hS x.1 j (x.2 j))) (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))`.

Rewrite using `[heq]`. Conclude with `(add_tsub_cancel_of_le hle).symm`. Conclude with `absurd rfl hm0`. Conclude with `absurd rfl hn'`. Introduce `k`.

Establish `hfix` using `lam_li_fixed g e (l k) (S k) (fun m m' hm hm' h => (hinj k k m m' hm hm' (by rw [h])).2) (u k) (hu k) (hS k)`. Establish `hι : Function.Injective (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j))`. Introduce and unpack `⟨⟨f, a⟩, h⟩ ⟨⟨f', a'⟩, h'⟩ hxx`. Simplify using `only at h h'`. Substitute `h` using the available equality.

Substitute `h'` using the available equality. Simplify using `only at hxx`. Rewrite using `[hxx]`. Establish `hcomp` using `hfix.comp _ hι`. Establish `heq : (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => monomial (l x.1.1) (1 : F) * ∏ j, lam_ph g e j (u x.1.1 j (x.1.2 j))) = ((fun a : ∀ j, I k j => monomial (l k) (1 : F) * ∏ j, lam_ph g e j (u k j (a j))) ∘ fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j …`.

Use function extensionality and compare the values at `x`. Take `⟨⟨f, a⟩, h⟩` from `x`. Simplify using `only at h`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Rewrite using `[heq]`. Conclude with `hcomp`.
-/
theorem lam_li_all {Φ : Type} (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : Φ → τ →₀ ℕ)
    (S : Φ → Fin J → Set (σ →₀ ℕ)) (I : Φ → Fin J → Type) [∀ f j, Fintype (I f j)]
    (u : ∀ f j, I f j → MvPolynomial σ F) (hu : ∀ f j, LinearIndependent F (u f j))
    (hS : ∀ f j i, u f j i ∈ restrictSupport F (S f j))
    (hinj : ∀ f f' (m m' : Fin J → σ →₀ ℕ), (∀ j, m j ∈ S f j) → (∀ j, m' j ∈ S f' j) →
      l f + ∑ j, imgMon (g j) (e j) (m j) = l f' + ∑ j, imgMon (g j) (e j) (m' j) → f = f' ∧ m = m') :
    LinearIndependent F fun x : (Σ f, ∀ j, I f j) =>
      monomial (l x.1) (1 : F) * ∏ j, lam_ph g e j (u x.1 j (x.2 j)) := by
  classical
  refine li_graded _ (fun x => x.1)
    (fun f => {n | ∃ m : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S f j) ∧ n = l f + ∑ j, imgMon (g j) (e j) (m j)}) ?_ ?_ ?_
  · rintro k k' n ⟨m, hm, rfl⟩ ⟨m', hm', h⟩
    exact (hinj k k' m m' hm hm' h).1
  · intro x
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    have hn' : coeff n (monomial (l x.1) (1 : F) * ∏ j, lam_ph g e j (u x.1 j (x.2 j))) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)
    rw [coeff_monomial_mul'] at hn'
    split_ifs at hn' with hle
    · rw [one_mul, lam_expand, coeff_sum] at hn'
      obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
      rw [coeff_monomial] at hm0
      split_ifs at hm0 with heq
      · refine ⟨m, fun j => ?_, ?_⟩
        · exact ((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hS x.1 j (x.2 j)))
            (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))
        · rw [heq]; exact (add_tsub_cancel_of_le hle).symm
      · exact absurd rfl hm0
    · exact absurd rfl hn'
  · intro k
    have hfix := lam_li_fixed g e (l k) (S k)
      (fun m m' hm hm' h => (hinj k k m m' hm hm' (by rw [h])).2) (u k) (hu k) (hS k)
    have hι : Function.Injective
        (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j)) := by
      rintro ⟨⟨f, a⟩, h⟩ ⟨⟨f', a'⟩, h'⟩ hxx
      simp only at h h'
      subst h
      subst h'
      simp only at hxx
      rw [hxx]
    have hcomp := hfix.comp _ hι
    have heq : (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} =>
        monomial (l x.1.1) (1 : F) * ∏ j, lam_ph g e j (u x.1.1 j (x.1.2 j))) =
        ((fun a : ∀ j, I k j => monomial (l k) (1 : F) * ∏ j, lam_ph g e j (u k j (a j))) ∘
          fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j)) := by
      funext x
      obtain ⟨⟨f, a⟩, h⟩ := x
      simp only at h
      subst h
      rfl
    rw [heq]
    exact hcomp

end LamAbs

end Formalism.MainNotions.SelectionLemmas.Pf
