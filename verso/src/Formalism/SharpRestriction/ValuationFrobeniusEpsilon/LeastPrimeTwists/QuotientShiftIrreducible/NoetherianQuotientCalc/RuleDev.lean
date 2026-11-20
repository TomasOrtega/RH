import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open DirectSum

section Prime

/- English proof (translation)
Take `rfl : dec = LinearOrder.toDecidableEq` from `Subsingleton.elim _ _`. Conclude with `hI.isPrime_of_homogeneous_mem_or_mem hne h`.
-/
theorem isPrime_of_dec {ι B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι] [dec : DecidableEq ι]
    (𝒜 : ι → Submodule B R) [GradedRing 𝒜] {I : Ideal R} (hI : I.IsHomogeneous 𝒜)
    (hne : I ≠ ⊤)
    (h : ∀ {x y : R}, SetLike.IsHomogeneousElem 𝒜 x → SetLike.IsHomogeneousElem 𝒜 y →
      x * y ∈ I → x ∈ I ∨ y ∈ I) : I.IsPrime := by
  obtain rfl : dec = LinearOrder.toDecidableEq := Subsingleton.elim _ _
  exact hI.isPrime_of_homogeneous_mem_or_mem hne h

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

/- English proof (translation)
The claim follows from `@isPrime_of_dec (Lex (Deg k)) B R _ _ _ _ _ _ (inferInstanceAs (DecidableEq (Deg k))) (fun m => 𝒜 (ofLex m)) inst I hI hne h`.
-/
theorem isPrime_of_hom (𝒜 : Deg k → Submodule B R) [inst : GradedAlgebra 𝒜] {I : Ideal R}
    (hI : I.IsHomogeneous 𝒜) (hne : I ≠ ⊤)
    (h : ∀ {x y : R}, SetLike.IsHomogeneousElem 𝒜 x → SetLike.IsHomogeneousElem 𝒜 y →
      x * y ∈ I → x ∈ I ∨ y ∈ I) : I.IsPrime :=
  @isPrime_of_dec (Lex (Deg k)) B R _ _ _ _ _ _ (inferInstanceAs (DecidableEq (Deg k)))
    (fun m => 𝒜 (ofLex m)) inst I hI hne h

end Prime

section Noeth

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

/- English proof (translation)
Use `h.noeth` as an intermediate fact. Use `choose s hs using fun i => h.fg i`. Set `T : Subalgebra B R` to `Algebra.adjoin B (⋃ i, (s i : Set R))`. Establish `h1 : ∀ i, 𝒜 (e i) ≤ Subalgebra.toSubmodule T`. Introduce `i`.

Rewrite using `[← hs i, Submodule.span_le]`. Introduce `x hx`. Conclude with `Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, hx⟩)`. Establish `h2 : ∀ (n : ℕ) (m : Deg k), 0 ≤ m → (∑ i, m i) = (n : ℤ) → 𝒜 m ≤ Subalgebra.toSubmodule T`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `m hm hsum`. Establish `hm0 : m = 0`. Use function extensionality and compare the values at `i`.

Conclude with `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hm i)).1 (by simpa using hsum) i (Finset.mem_univ i)`. Substitute `hm0` using the available equality. Rewrite using `[h.zero]`. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `T.algebraMap_mem b`.

Consider the case `succ n ih`. Introduce `m hm hsum`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, 0 < m i := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `h0 : ∑ i, m i ≤ 0` using `Finset.sum_nonpos (fun i _ => hcon i)`. Rewrite `h0` using `[hsum]`. Move the coercions through the operations in `at h0`. Use linear arithmetic over natural numbers and integers. Establish `hm' : 0 ≤ m - e i`.

Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [e, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_same]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [e, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_of_ne hj, sub_zero]`. Conclude with `hm j`. Establish `hsum' : ∑ j, (m - e i) j = (n : ℤ)`. Simplify using `only [e, Pi.sub_apply, Finset.sum_sub_distrib, hsum, Finset.sum_pi_single', Finset.mem_univ, if_true]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hg` using `h.gen (m - e i) i hm'`. Rewrite `hg` using `[sub_add_cancel]`. Rewrite using `[hg, Submodule.mul_le]`. Introduce `a ha b hb`.

Conclude with `T.mul_mem (ih _ hm' hsum' ha) (h1 i hb)`. Establish `h3 : T = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Rewrite using `[← DirectSum.sum_support_decompose 𝒜 x]`.

Use `T.sum_mem (fun m _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hm : 0 ≤ m`. Conclude with `h2 _ m hm (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hm i)).symm (SetLike.coe_mem _)`. Establish `hb : ((decompose 𝒜 x m : 𝒜 m) : R) ∈ (⊥ : Submodule B R)` using `h.nonneg m hm ▸ SetLike.coe_mem _`. Rewrite using `[(Submodule.mem_bot B).1 hb]`.

Conclude with `T.zero_mem`. Establish `: Algebra.FiniteType B R` using `⟨Subalgebra.fg_def.2 ⟨_, Set.finite_iUnion (fun i => (s i).finite_toSet), h3⟩⟩`. Conclude with `Algebra.FiniteType.isNoetherianRing B R`.
-/
theorem isNoetherianRing_of_std [IsLocalRing B] (𝒜 : Deg k → Submodule B R) [GradedAlgebra 𝒜]
    (h : Std 𝒜) : IsNoetherianRing R := by
  classical
  have := h.noeth
  choose s hs using fun i => h.fg i
  let T : Subalgebra B R := Algebra.adjoin B (⋃ i, (s i : Set R))
  have h1 : ∀ i, 𝒜 (e i) ≤ Subalgebra.toSubmodule T := by
    intro i
    rw [← hs i, Submodule.span_le]
    intro x hx
    exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, hx⟩)
  have h2 : ∀ (n : ℕ) (m : Deg k), 0 ≤ m → (∑ i, m i) = (n : ℤ) →
      𝒜 m ≤ Subalgebra.toSubmodule T := by
    intro n
    induction n with
    | zero =>
      intro m hm hsum
      have hm0 : m = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hm i)).1 (by simpa using hsum) i
          (Finset.mem_univ i)
      subst hm0
      rw [h.zero]
      rintro _ ⟨b, rfl⟩
      exact T.algebraMap_mem b
    | succ n ih =>
      intro m hm hsum
      obtain ⟨i, hi⟩ : ∃ i, 0 < m i := by
        by_contra hcon
        push Not at hcon
        have h0 : ∑ i, m i ≤ 0 := Finset.sum_nonpos (fun i _ => hcon i)
        rw [hsum] at h0
        push_cast at h0
        omega
      have hm' : 0 ≤ m - e i := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp only [e, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_same]
          omega
        · simp only [e, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_of_ne hj, sub_zero]
          exact hm j
      have hsum' : ∑ j, (m - e i) j = (n : ℤ) := by
        simp only [e, Pi.sub_apply, Finset.sum_sub_distrib, hsum, Finset.sum_pi_single',
          Finset.mem_univ, if_true]
        push_cast
        ring
      have hg := h.gen (m - e i) i hm'
      rw [sub_add_cancel] at hg
      rw [hg, Submodule.mul_le]
      intro a ha b hb
      exact T.mul_mem (ih _ hm' hsum' ha) (h1 i hb)
  have h3 : T = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← DirectSum.sum_support_decompose 𝒜 x]
    refine T.sum_mem (fun m _ => ?_)
    by_cases hm : 0 ≤ m
    · exact h2 _ m hm (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hm i)).symm
        (SetLike.coe_mem _)
    · have hb : ((decompose 𝒜 x m : 𝒜 m) : R) ∈ (⊥ : Submodule B R) :=
        h.nonneg m hm ▸ SetLike.coe_mem _
      rw [(Submodule.mem_bot B).1 hb]
      exact T.zero_mem
  have : Algebra.FiniteType B R :=
    ⟨Subalgebra.fg_def.2 ⟨_, Set.finite_iUnion (fun i => (s i).finite_toSet), h3⟩⟩
  exact Algebra.FiniteType.isNoetherianRing B R

end Noeth

section Comp

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
variable (𝒜 : Deg k → Submodule B R) [GradedAlgebra 𝒜]

/- English proof (translation)
Establish `hterm : ∀ j, ((decompose F.gr (((decompose 𝒜 a j : 𝒜 j) : R) • x) m : F.gr m) : F.M) = if j + d = m then ((decompose 𝒜 a j : 𝒜 j) : R) • x else 0`. Introduce `j`. Rewrite using `[decompose_of_mem F.gr (hF.smul_mem (SetLike.coe_mem _) hx), DirectSum.coe_of_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Establish `hsum : a • x = ∑ j ∈ (decompose 𝒜 a).support, ((decompose 𝒜 a j : 𝒜 j) : R) • x`.

Rewrite using `[← Finset.sum_smul, DirectSum.sum_support_decompose 𝒜 a]`. Rewrite using `[hsum, decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]`. Repeatedly rewrite using `[hterm]`. Rewrite using `[Finset.sum_eq_single (m - d)]`. Rewrite using `[if_pos (sub_add_cancel m d)]`.

Introduce `j _ hj`. Rewrite using `[if_neg]`. Introduce `hjd`. Conclude with `hj (eq_sub_of_add_eq hjd)`. Introduce `hns`.

Rewrite `hns` using `[DFinsupp.notMem_support_iff]`. Rewrite using `[hns]`. Simplify using the standard rewrite rules.
-/
theorem devComp_smul {F : GMod B R k} (hF : F.IsGr 𝒜) [Decomposition F.gr] {d : Deg k} {x : F.M}
    (hx : x ∈ F.gr d) (a : R) (m : Deg k) :
    ((decompose F.gr (a • x) m : F.gr m) : F.M) = ((decompose 𝒜 a (m - d) : 𝒜 (m - d)) : R) • x := by
  classical
  have hterm : ∀ j, ((decompose F.gr (((decompose 𝒜 a j : 𝒜 j) : R) • x) m : F.gr m) : F.M) =
      if j + d = m then ((decompose 𝒜 a j : 𝒜 j) : R) • x else 0 := by
    intro j
    rw [decompose_of_mem F.gr (hF.smul_mem (SetLike.coe_mem _) hx), DirectSum.coe_of_apply]
    split_ifs <;> rfl
  have hsum : a • x = ∑ j ∈ (decompose 𝒜 a).support, ((decompose 𝒜 a j : 𝒜 j) : R) • x := by
    rw [← Finset.sum_smul, DirectSum.sum_support_decompose 𝒜 a]
  rw [hsum, decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (m - d)]
  · rw [if_pos (sub_add_cancel m d)]
  · intro j _ hj
    rw [if_neg]
    intro hjd
    exact hj (eq_sub_of_add_eq hjd)
  · intro hns
    rw [DFinsupp.notMem_support_iff] at hns
    rw [hns]
    simp

/- English proof (translation)
Set `` to `hF.internal.chooseDecomposition`. Introduce `j a ha`. Rewrite `ha`, the goal using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Establish `h` using `devComp_smul 𝒜 hF hx a (j + d)`. Rewrite `h` using `[ha, decompose_zero, add_sub_cancel_right]`.

Conclude with `h.symm`.
-/
theorem ker_hom {F : GMod B R k} (hF : F.IsGr 𝒜) {d : Deg k} {x : F.M} (hx : x ∈ F.gr d) :
    Ideal.IsHomogeneous 𝒜 (LinearMap.ker (LinearMap.toSpanSingleton R F.M x)) := by
  let := hF.internal.chooseDecomposition
  intro j a ha
  rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at ha ⊢
  have h := devComp_smul 𝒜 hF hx a (j + d)
  rw [ha, decompose_zero, add_sub_cancel_right] at h
  exact h.symm

/- English proof (translation)
Set `` to `hF.internal.chooseDecomposition`. Use `⟨_, SetLike.coe_mem (decompose 𝒜 a (m - d)), ?_⟩` and prove the remaining obligations. Rewrite using `[← devComp_smul 𝒜 hF hx a m, decompose_of_mem_same F.gr h]`.
-/
theorem smul_strict {F : GMod B R k} (hF : F.IsGr 𝒜) {d : Deg k} {x : F.M} (hx : x ∈ F.gr d)
    (a : R) (m : Deg k) (h : a • x ∈ F.gr m) : ∃ a' ∈ 𝒜 (m - d), a' • x = a • x := by
  let := hF.internal.chooseDecomposition
  refine ⟨_, SetLike.coe_mem (decompose 𝒜 a (m - d)), ?_⟩
  rw [← devComp_smul 𝒜 hF hx a m, decompose_of_mem_same F.gr h]

/- English proof (translation)
Set `` to `hG.internal.chooseDecomposition`. Set `S : Set (Ideal R)` to `{I | ∃ (d : Deg k) (x : G.M), x ∈ G.gr d ∧ x ≠ 0 ∧ I = LinearMap.ker (LinearMap.toSpanSingleton R G.M x)}`. Establish `hS : S.Nonempty`. Assume the negation of the conclusion as `hcon`. Establish `hall : ∀ (d : Deg k) (x : G.M), x ∈ G.gr d → x = 0`.

Introduce `d x hx`. Assume the negation of the conclusion as `hx0`. Conclude with `hcon ⟨_, d, x, hx, hx0, rfl⟩`. Take `⟨y, hy⟩` from `exists_ne (0 : G.M)`. Apply `hy` to reduce the goal to its premises.

Rewrite using `[← DirectSum.sum_support_decompose G.gr y]`. Conclude with `Finset.sum_eq_zero (fun m _ => hall m _ (SetLike.coe_mem _))`. Take `⟨I, ⟨d, x, hx, hx0, rfl⟩, hmax⟩` from `(set_has_maximal_iff_noetherian (R := R) (M := R)).2 inferInstance S hS`. Use `⟨d, x, hx, isPrime_of_hom 𝒜 (ker_hom 𝒜 hG hx) ?_ ?_⟩` and prove the remaining obligations. Introduce `htop`.

Establish `h1 : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R G.M x)`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`. Rewrite `h1` using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul]`. Conclude with `hx0 h1`.

Introduce and unpack `a b ⟨i, ha⟩ _ hab`. Distinguish the cases in `hax : a • x = 0`. Use `left`. Rewrite using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Conclude with `hax`.

Use `right`. Establish `hle : LinearMap.ker (LinearMap.toSpanSingleton R G.M x) ≤ LinearMap.ker (LinearMap.toSpanSingleton R G.M (a • x))`. Introduce `c hc`. Rewrite `hc`, the goal using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Rewrite using `[smul_comm, hc, smul_zero]`.

Establish `heq` using `eq_of_le_of_not_lt hle (hmax _ ⟨i + d, a • x, hG.smul_mem ha hx, hax, rfl⟩)`. Rewrite using `[heq, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_smul, mul_comm]`. Rewrite `hab` using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Conclude with `hab`.
-/
theorem exists_prime_ker [IsNoetherianRing R] {G : GMod B R k} (hG : G.IsGr 𝒜)
    [Nontrivial G.M] :
    ∃ (d : Deg k) (x : G.M), x ∈ G.gr d ∧
      Ideal.IsPrime (LinearMap.ker (LinearMap.toSpanSingleton R G.M x)) := by
  classical
  let := hG.internal.chooseDecomposition
  let S : Set (Ideal R) := {I | ∃ (d : Deg k) (x : G.M), x ∈ G.gr d ∧ x ≠ 0 ∧
    I = LinearMap.ker (LinearMap.toSpanSingleton R G.M x)}
  have hS : S.Nonempty := by
    by_contra hcon
    have hall : ∀ (d : Deg k) (x : G.M), x ∈ G.gr d → x = 0 := by
      intro d x hx
      by_contra hx0
      exact hcon ⟨_, d, x, hx, hx0, rfl⟩
    obtain ⟨y, hy⟩ := exists_ne (0 : G.M)
    apply hy
    rw [← DirectSum.sum_support_decompose G.gr y]
    exact Finset.sum_eq_zero (fun m _ => hall m _ (SetLike.coe_mem _))
  obtain ⟨I, ⟨d, x, hx, hx0, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := R) (M := R)).2 inferInstance S hS
  refine ⟨d, x, hx, isPrime_of_hom 𝒜 (ker_hom 𝒜 hG hx) ?_ ?_⟩
  · intro htop
    have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R G.M x) := by
      rw [htop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hx0 h1
  · rintro a b ⟨i, ha⟩ _ hab
    by_cases hax : a • x = 0
    · left
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hax
    · right
      have hle : LinearMap.ker (LinearMap.toSpanSingleton R G.M x) ≤
          LinearMap.ker (LinearMap.toSpanSingleton R G.M (a • x)) := by
        intro c hc
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hc ⊢
        rw [smul_comm, hc, smul_zero]
      have heq := eq_of_le_of_not_lt hle
        (hmax _ ⟨i + d, a • x, hG.smul_mem ha hx, hax, rfl⟩)
      rw [heq, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_smul, mul_comm]
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hab
      exact hab

end Comp

section Step

variable {k : ℕ}

/- English proof (translation)
Establish `: IsNoetherianRing X.R` using `isNoetherianRing_of_std X.𝒜 X.std`. Establish `hG : (F.quo N).IsGr X.𝒜` using `((hGr k X F hF).1 N hN).2`. Establish `: Nontrivial (F.quo N).M` using `(Submodule.Quotient.nontrivial_iff (p := N)).2 hne`. Take `⟨d, xb, hxb, hprime⟩` from `exists_prime_ker X.𝒜 hG`. Establish `hhom` using `ker_hom X.𝒜 hG hxb`.

Establish `hstrict` using `smul_strict X.𝒜 hG hxb`. Take `⟨x, hx, rfl⟩` from `hxb`. Express the relevant statement in the definitionally equal form `x ∈ F.gr d at hx`. Use `set xb : F.M ⧸ N := N.mkQ x with hxbdef`. Set `φ : X.R →ₗ[X.R] F.M ⧸ N` to `LinearMap.toSpanSingleton X.R (F.M ⧸ N) xb`.

Express the relevant statement in the definitionally equal form `Ideal.IsPrime (LinearMap.ker φ) at hprime`. Express the relevant statement in the definitionally equal form `Ideal.IsHomogeneous X.𝒜 (LinearMap.ker φ) at hhom`. Set `N' : Submodule X.R F.M` to `N ⊔ Submodule.span X.R {x}`. Establish `hxN' : x ∈ N'` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)`. Establish `hNN' : N ≤ N'` using `le_sup_left`.

Establish `hrange : ∀ y : N', (N.mkQ ∘ₗ N'.subtype) y ∈ LinearMap.range φ`. Introduce and unpack `⟨y, hy⟩`. Take `⟨n, hn, z, hz, rfl⟩` from `Submodule.mem_sup.1 hy`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hz`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Use `show a • N.mkQ x = N.mkQ (n + a • x)`. Rewrite using `[map_add, map_smul, (Submodule.Quotient.mk_eq_zero N).2 hn |> (show N.mkQ n = 0 from ·), zero_add]`. Set `g : N' →ₗ[X.R] X.R ⧸ LinearMap.ker φ` to `(φ.quotKerEquivRange.symm : LinearMap.range φ →ₗ[X.R] X.R ⧸ LinearMap.ker φ) ∘ₗ (LinearMap.codRestrict (LinearMap.range φ) (N.mkQ ∘ₗ N'.subtype) hrange)`. Establish `key : ∀ (y : N') (a : X.R), N.mkQ (y : F.M) = a • xb → g y = (LinearMap.ker φ).mkQ a`. Introduce `y a hya`.

Use `show φ.quotKerEquivRange.symm _ = _`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show N.mkQ (y : F.M) = φ a`. Rewrite using `[hya]`.

Conclude with `(LinearMap.toSpanSingleton_apply X.R (F.M ⧸ N) xb a).symm`. Use `⟨N', LinearMap.ker φ, d, ?_, ?_, hprime, hhom, ?_, ⟨?_⟩⟩` and prove the remaining obligations. Use `lt_of_le_of_ne hNN' ?_` and prove the remaining obligations. Introduce `heq`. Establish `hxN : x ∈ N` using `heq ▸ hxN'`.

Apply `hprime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, LinearMap.mem_ker]`. Use `show (1 : X.R) • N.mkQ x = 0`. Rewrite using `[one_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero N).2 hxN`.

Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ ?_` and prove the remaining obligations. Conclude with `(show N = Submodule.span X.R {x | x ∈ N ∧ ∃ m, x ∈ F.gr m} from hN).le.trans (Submodule.span_mono (fun y hy => ⟨hNN' hy.1, hy.2⟩))`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `Submodule.subset_span ⟨hxN', d, hx⟩`.

Conclude with `Submodule.span_le.2 (fun y hy => hy.1)`. Introduce `a ha`. Rewrite using `[LinearMap.mem_ker]`. Use `show a • N.mkQ x = 0`. Rewrite using `[← map_smul, Module.mem_annihilator.1 ha x, map_zero]`.

Use `{ f := Submodule.inclusion hNN' g := g inj := Submodule.inclusion_injective hNN' surj := ?_` and prove the remaining obligations. Conclude with `:= ?_`. Use `f_gr := ?_`. Use `g_gr := ?_ }`. Introduce `q`.

Take `⟨a, rfl⟩` from `(LinearMap.ker φ).mkQ_surjective q`. Conclude with `⟨⟨a • x, N'.smul_mem a hxN'⟩, key _ a (map_smul _ _ _)⟩`. Introduce `(y : N')`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `h0 : LinearMap.codRestrict (LinearMap.range φ) (N.mkQ ∘ₗ N'.subtype) hrange y = 0` using `(LinearEquiv.map_eq_zero_iff φ.quotKerEquivRange.symm).1 hy`. Establish `h1 : N.mkQ (y : F.M) = 0` using `congrArg Subtype.val h0`. Establish `h2 : (y : F.M) ∈ N` using `(Submodule.Quotient.mk_eq_zero N).1 h1`. Conclude with `⟨⟨y, h2⟩, Subtype.ext rfl⟩`. Introduce and unpack `⟨n, rfl⟩`.

Establish `h1 : N.mkQ ((Submodule.inclusion hNN' n : N') : F.M) = (0 : X.R) • xb`. Rewrite using `[zero_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero N).2 n.2`. Establish `h2` using `key _ 0 h1`. Rewrite `h2` using `[map_zero]`.

Conclude with `h2`. Introduce `m`. Use extensionality with `y`. Conclude with `Iff.rfl`. Introduce `m`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨(a : X.R), ha, rfl⟩`. Use `⟨⟨a • x, N'.smul_mem a hxN'⟩, ?_, key _ a (map_smul _ _ _)⟩` and prove the remaining obligations. Use `show a • x ∈ F.gr m`. Establish `h1` using `hF.smul_mem ha hx`.

Rewrite `h1` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce and unpack `_ ⟨(y : N'), hy, rfl⟩`. Take `⟨a, ha⟩` from `hrange y`. Establish `hy' : (y : F.M) ∈ F.gr m` using `hy`. Establish `h1 : a • xb ∈ (F.quo N).gr m` using `⟨(y : F.M), hy', ha.symm⟩`.

Take `⟨a', ha', h2⟩` from `hstrict a m h1`. Conclude with `⟨a', ha', (key y a' (ha.symm.trans h2.symm)).symm⟩`.
-/
theorem step (hGr : RuleGr) (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜)
    (N : Submodule X.R F.M) (hN : F.IsHomSub N) (hne : N ≠ ⊤) :
    ∃ (N' : Submodule X.R F.M) (𝔮 : Ideal X.R) (d : Deg k), N < N' ∧ F.IsHomSub N' ∧
      𝔮.IsPrime ∧ 𝔮.IsHomogeneous X.𝒜 ∧ F.Ann ≤ 𝔮 ∧
      Nonempty (SES (F.sub N) (F.sub N') (((GMod.self X.𝒜).quo 𝔮).shift d)) := by
  have : IsNoetherianRing X.R := isNoetherianRing_of_std X.𝒜 X.std
  have hG : (F.quo N).IsGr X.𝒜 := ((hGr k X F hF).1 N hN).2
  have : Nontrivial (F.quo N).M := (Submodule.Quotient.nontrivial_iff (p := N)).2 hne
  obtain ⟨d, xb, hxb, hprime⟩ := exists_prime_ker X.𝒜 hG
  have hhom := ker_hom X.𝒜 hG hxb
  have hstrict := smul_strict X.𝒜 hG hxb
  obtain ⟨x, hx, rfl⟩ := hxb
  change x ∈ F.gr d at hx
  set xb : F.M ⧸ N := N.mkQ x with hxbdef
  let φ : X.R →ₗ[X.R] F.M ⧸ N := LinearMap.toSpanSingleton X.R (F.M ⧸ N) xb
  change Ideal.IsPrime (LinearMap.ker φ) at hprime
  change Ideal.IsHomogeneous X.𝒜 (LinearMap.ker φ) at hhom
  let N' : Submodule X.R F.M := N ⊔ Submodule.span X.R {x}
  have hxN' : x ∈ N' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hNN' : N ≤ N' := le_sup_left
  have hrange : ∀ y : N', (N.mkQ ∘ₗ N'.subtype) y ∈ LinearMap.range φ := by
    rintro ⟨y, hy⟩
    obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨a, ?_⟩
    show a • N.mkQ x = N.mkQ (n + a • x)
    rw [map_add, map_smul, (Submodule.Quotient.mk_eq_zero N).2 hn |> (show N.mkQ n = 0 from ·),
      zero_add]
  let g : N' →ₗ[X.R] X.R ⧸ LinearMap.ker φ :=
    (φ.quotKerEquivRange.symm : LinearMap.range φ →ₗ[X.R] X.R ⧸ LinearMap.ker φ) ∘ₗ
      (LinearMap.codRestrict (LinearMap.range φ) (N.mkQ ∘ₗ N'.subtype) hrange)
  have key : ∀ (y : N') (a : X.R), N.mkQ (y : F.M) = a • xb →
      g y = (LinearMap.ker φ).mkQ a := by
    intro y a hya
    show φ.quotKerEquivRange.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    show N.mkQ (y : F.M) = φ a
    rw [hya]
    exact (LinearMap.toSpanSingleton_apply X.R (F.M ⧸ N) xb a).symm
  refine ⟨N', LinearMap.ker φ, d, ?_, ?_, hprime, hhom, ?_, ⟨?_⟩⟩
  · refine lt_of_le_of_ne hNN' ?_
    intro heq
    have hxN : x ∈ N := heq ▸ hxN'
    apply hprime.ne_top
    rw [Ideal.eq_top_iff_one, LinearMap.mem_ker]
    show (1 : X.R) • N.mkQ x = 0
    rw [one_smul]
    exact (Submodule.Quotient.mk_eq_zero N).2 hxN
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · exact (show N = Submodule.span X.R {x | x ∈ N ∧ ∃ m, x ∈ F.gr m} from hN).le.trans
          (Submodule.span_mono (fun y hy => ⟨hNN' hy.1, hy.2⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span ⟨hxN', d, hx⟩
    · exact Submodule.span_le.2 (fun y hy => hy.1)
  · intro a ha
    rw [LinearMap.mem_ker]
    show a • N.mkQ x = 0
    rw [← map_smul, Module.mem_annihilator.1 ha x, map_zero]
  · refine
      { f := Submodule.inclusion hNN'
        g := g
        inj := Submodule.inclusion_injective hNN'
        surj := ?_
        exact := ?_
        f_gr := ?_
        g_gr := ?_ }
    · intro q
      obtain ⟨a, rfl⟩ := (LinearMap.ker φ).mkQ_surjective q
      exact ⟨⟨a • x, N'.smul_mem a hxN'⟩, key _ a (map_smul _ _ _)⟩
    · intro (y : N')
      constructor
      · intro hy
        have h0 : LinearMap.codRestrict (LinearMap.range φ) (N.mkQ ∘ₗ N'.subtype) hrange y = 0 :=
          (LinearEquiv.map_eq_zero_iff φ.quotKerEquivRange.symm).1 hy
        have h1 : N.mkQ (y : F.M) = 0 := congrArg Subtype.val h0
        have h2 : (y : F.M) ∈ N := (Submodule.Quotient.mk_eq_zero N).1 h1
        exact ⟨⟨y, h2⟩, Subtype.ext rfl⟩
      · rintro ⟨n, rfl⟩
        have h1 : N.mkQ ((Submodule.inclusion hNN' n : N') : F.M) = (0 : X.R) • xb := by
          rw [zero_smul]
          exact (Submodule.Quotient.mk_eq_zero N).2 n.2
        have h2 := key _ 0 h1
        rw [map_zero] at h2
        exact h2
    · intro m
      ext y
      exact Iff.rfl
    · intro m
      apply le_antisymm
      · rintro _ ⟨(a : X.R), ha, rfl⟩
        refine ⟨⟨a • x, N'.smul_mem a hxN'⟩, ?_, key _ a (map_smul _ _ _)⟩
        show a • x ∈ F.gr m
        have h1 := hF.smul_mem ha hx
        rwa [sub_add_cancel] at h1
      · rintro _ ⟨(y : N'), hy, rfl⟩
        obtain ⟨a, ha⟩ := hrange y
        have hy' : (y : F.M) ∈ F.gr m := hy
        have h1 : a • xb ∈ (F.quo N).gr m := ⟨(y : F.M), hy', ha.symm⟩
        obtain ⟨a', ha', h2⟩ := hstrict a m h1
        exact ⟨a', ha', (key y a' (ha.symm.trans h2.symm)).symm⟩

end Step

section Main

variable {k : ℕ}

def Good (X : HidaSetting k) (F : X.Mod) (N₀ : Submodule X.R F.M) : Prop :=
  ∃ (t : ℕ) (N : ℕ → Submodule X.R F.M) (𝔮 : ℕ → Ideal X.R) (d : ℕ → Deg k),
    N 0 = ⊥ ∧ N t = N₀ ∧ (∀ i, F.IsHomSub (N i)) ∧ (∀ i, N i ≤ N (i + 1)) ∧
    ∀ i < t, (𝔮 i).IsPrime ∧ (𝔮 i).IsHomogeneous X.𝒜 ∧ F.Ann ≤ 𝔮 i ∧
      Nonempty (SES (F.sub (N i)) (F.sub (N (i + 1))) (((GMod.self X.𝒜).quo (𝔮 i)).shift (d i)))

/- English proof (translation)
Use `⟨0, fun _ => ⊥, fun _ => ⊥, fun _ => 0, rfl, rfl, ?_, fun _ => le_rfl, ?_⟩` and prove the remaining obligations. Introduce `_`. Conclude with `(Submodule.span_eq_bot.2 (fun x hx => (Submodule.mem_bot _).1 hx.1)).symm`. Introduce `i hi`. Conclude with `absurd hi (Nat.not_lt_zero i)`.
-/
theorem good_bot (X : HidaSetting k) (F : X.Mod) : Good X F ⊥ := by
  refine ⟨0, fun _ => ⊥, fun _ => ⊥, fun _ => 0, rfl, rfl, ?_, fun _ => le_rfl, ?_⟩
  · intro _
    exact (Submodule.span_eq_bot.2 (fun x hx => (Submodule.mem_bot _).1 hx.1)).symm
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)

/- English proof (translation)
Take `⟨t, N, 𝔮, d, hN0, rfl, hhom, hmono, hstep⟩` from `h`. Use `⟨t + 1, fun i => if i ≤ t then N i else N', Function.update 𝔮 t 𝔮', Function.update d t d', ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Nat.zero_le, if_true]`. Conclude with `hN0`. Simplify using the standard rewrite rules.

Introduce `i`. Distinguish the cases in `hi : i ≤ t`. Simplify using `only [if_pos hi]`. Conclude with `hhom i`. Simplify using `only [if_neg hi]`.

Conclude with `hN'`. Introduce `i`. Distinguish the cases in `hi : i + 1 ≤ t`. Simplify using `only [if_pos hi, if_pos (Nat.le_of_succ_le hi)]`. Conclude with `hmono i`.

Distinguish the cases in `hi' : i ≤ t`. Establish `hit : i = t` using `by omega`. Substitute `hit` using the available equality. Simplify using `only [if_neg hi, if_pos hi']`. Conclude with `hle`.

Simplify using `only [if_neg hi, if_neg hi']`. Conclude with `le_rfl`. Introduce `i hi`. Distinguish the cases in `hit : i = t`. Substitute `hit` using the available equality.

Simplify using `only [le_refl, if_true, Nat.succ_le_iff, lt_irrefl, if_false, Function.update_self]`. Conclude with `⟨h1, h2, h3, h4⟩`. Establish `hlt : i < t` using `by omega`. Simplify using `only [if_pos hlt.le, if_pos (Nat.succ_le_of_lt hlt), Function.update_of_ne hit]`. Conclude with `hstep i hlt`.
-/
theorem good_step (X : HidaSetting k) (F : X.Mod) {N₀ N' : Submodule X.R F.M} (h : Good X F N₀)
    (hle : N₀ ≤ N') (hN' : F.IsHomSub N') {𝔮' : Ideal X.R} {d' : Deg k} (h1 : 𝔮'.IsPrime)
    (h2 : 𝔮'.IsHomogeneous X.𝒜) (h3 : F.Ann ≤ 𝔮')
    (h4 : Nonempty (SES (F.sub N₀) (F.sub N') (((GMod.self X.𝒜).quo 𝔮').shift d'))) :
    Good X F N' := by
  obtain ⟨t, N, 𝔮, d, hN0, rfl, hhom, hmono, hstep⟩ := h
  refine ⟨t + 1, fun i => if i ≤ t then N i else N', Function.update 𝔮 t 𝔮',
    Function.update d t d', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Nat.zero_le, if_true]
    exact hN0
  · simp
  · intro i
    by_cases hi : i ≤ t
    · simp only [if_pos hi]; exact hhom i
    · simp only [if_neg hi]; exact hN'
  · intro i
    by_cases hi : i + 1 ≤ t
    · simp only [if_pos hi, if_pos (Nat.le_of_succ_le hi)]; exact hmono i
    · by_cases hi' : i ≤ t
      · have hit : i = t := by omega
        subst hit
        simp only [if_neg hi, if_pos hi']; exact hle
      · simp only [if_neg hi, if_neg hi']; exact le_rfl
  · intro i hi
    by_cases hit : i = t
    · subst hit
      simp only [le_refl, if_true, Nat.succ_le_iff, lt_irrefl, if_false, Function.update_self]
      exact ⟨h1, h2, h3, h4⟩
    · have hlt : i < t := by omega
      simp only [if_pos hlt.le, if_pos (Nat.succ_le_of_lt hlt), Function.update_of_ne hit]
      exact hstep i hlt

/- English proof (translation)
Introduce `hGr k X F hF`. Establish `: IsNoetherianRing X.R` using `isNoetherianRing_of_std X.𝒜 X.std`. Establish `: Module.Finite X.R F.M` using `hF.fin`. Establish `: IsNoetherian X.R F.M` using `isNoetherian_of_isNoetherianRing_of_finite X.R F.M`. Take `⟨N, hN, hmax⟩` from `(set_has_maximal_iff_noetherian (R := X.R) (M := F.M)).2 inferInstance {N | Good X F N} ⟨⊥, good_bot X F⟩`.

Establish `htop : N = ⊤`. Assume the negation of the conclusion as `hne`. Establish `hNhom : F.IsHomSub N`. Take `⟨t, Ns, _, _, _, rfl, hhom, _⟩` from `hN`. Conclude with `hhom t`.

Take `⟨N', 𝔮, d, hlt, hN', h1, h2, h3, h4⟩` from `step hGr X F hF N hNhom hne`. Conclude with `hmax N' (good_step X F hN hlt.le hN' h1 h2 h3 h4) hlt`. Rewrite `hN` using `[htop]`. Conclude with `hN`.
-/
theorem ruleDev : RuleGr → RuleDev := by
  intro hGr k X F hF
  have : IsNoetherianRing X.R := isNoetherianRing_of_std X.𝒜 X.std
  have : Module.Finite X.R F.M := hF.fin
  have : IsNoetherian X.R F.M := isNoetherian_of_isNoetherianRing_of_finite X.R F.M
  obtain ⟨N, hN, hmax⟩ := (set_has_maximal_iff_noetherian (R := X.R) (M := F.M)).2 inferInstance
    {N | Good X F N} ⟨⊥, good_bot X F⟩
  have htop : N = ⊤ := by
    by_contra hne
    have hNhom : F.IsHomSub N := by
      obtain ⟨t, Ns, _, _, _, rfl, hhom, _⟩ := hN
      exact hhom t
    obtain ⟨N', 𝔮, d, hlt, hN', h1, h2, h3, h4⟩ := step hGr X F hF N hNhom hne
    exact hmax N' (good_step X F hN hlt.le hN' h1 h2 h3 h4) hlt
  rw [htop] at hN
  exact hN

end Main

end Formalism.MainNotions.V.Pf.V2.Calc
