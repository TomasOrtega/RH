import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FTDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentChainDegreeEven

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

/- English proof (translation)
Introduce `d hd`. Apply `h` to reduce the goal to its premises. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[MvPolynomial.coeff_smul, h0, smul_zero]`.
-/
theorem wh_smulO {O : Type} [CommRing O] [IsDomain O] {σ : Type} {ω : σ → ℕ} {x : MvPolynomial σ (KK O)} {n : ℕ} (c : O)
    (h : IsWeightedHomogeneous ω x n) : IsWeightedHomogeneous ω (c • x) n := by
  intro d hd
  apply h
  intro h0
  apply hd
  rw [MvPolynomial.coeff_smul, h0, smul_zero]

/- English proof (translation)
Conclude with `e ▸ h`.
-/
theorem wh_congr {K : Type} [CommRing K] {σ : Type} {ω : σ → ℕ} {x : MvPolynomial σ K} {n n' : ℕ}
    (h : IsWeightedHomogeneous ω x n) (e : n = n') : IsWeightedHomogeneous ω x n' := by
  exact e ▸ h

/- English proof (translation)
Establish `hinj : Function.Injective (chainEmb N r t)`. Introduce `x y h`. Simplify using `only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h`. Conclude with `Prod.ext h.1 h.2`. Introduce `d hd`.

Establish `hd' : d ∈ (rename (chainEmb N r t) y).support` using `MvPolynomial.mem_support_iff.mpr hd`. Rewrite `hd'` using `[MvPolynomial.support_rename_of_injective hinj]`. Take `⟨m1, hm1, rfl⟩` from `Finset.mem_image.mp hd'`. Unfold `Pol at hy`. Rewrite `hy` using `[MvPolynomial.mem_restrictSupport_iff]`.

Establish `hdeg` using `hy hm1`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • ω i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _), Finsupp.sum_fintype m1 (fun a (m : ℕ) => m • ω (chainEmb N r t a)) (fun _ => zero_smul _ _), Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← hdeg a]`. Unfold `multideg`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`. Use `congr 1`. Conclude with `h1 _ _`.
-/
theorem wh_chain {K : Type} [CommRing K] {N r t : ℕ} (ω : BVar N r t → ℕ) (ωL : Fin (N + 1) → ℕ)
    (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a) (deg : Fin N → ℕ) (y : MvPolynomial (Fin N × Fin r) K)
    (hy : y ∈ Pol K r deg) :
    IsWeightedHomogeneous ω (rename (chainEmb N r t) y) (∑ a, deg a * ωL (Fin.castSucc a)) := by
  classical
  have hinj : Function.Injective (chainEmb N r t) := by
    intro x y h
    simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
    exact Prod.ext h.1 h.2
  intro d hd
  have hd' : d ∈ (rename (chainEmb N r t) y).support := MvPolynomial.mem_support_iff.mpr hd
  rw [MvPolynomial.support_rename_of_injective hinj] at hd'
  obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hd'
  unfold Pol at hy
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  have hdeg := hy hm1
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • ω i) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_fintype m1 (fun a (m : ℕ) => m • ω (chainEmb N r t a)) (fun _ => zero_smul _ _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hdeg a]
  unfold multideg
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_eq_mul]
  congr 1
  exact h1 _ _

/- English proof (translation)
Introduce `d hd`. Establish `hg1` using `(Submodule.mem_inf.mp hg).1`. Rewrite `hg1` using `[Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]`. Take `⟨hsupp, hsum⟩` from `hg1 (MvPolynomial.mem_support_iff.mpr hd)`. Establish `hinj : Function.Injective (xiVar N r t)`.

Introduce `a b h`. Simplify using `only [xiVar, Sum.inl.injEq, Prod.mk.injEq] at h`. Conclude with `h.2`. Establish `hsub : d.support ⊆ Finset.univ.image (xiVar N r t)`. Introduce `v hv`.

Take `⟨c, rfl⟩` from `hsupp v hv`. Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ c)`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_of_support_subset d hsub (fun i (c : ℕ) => c • ω i) (fun _ _ => zero_smul _ _), Finset.sum_image (fun a _ b _ h => hinj h), ← hsum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`.

Use `congr 1`. Conclude with `h1 _ _`.
-/
theorem wh_xi {O : Type} [CommRing O] [IsDomain O] {N r t b' : ℕ} (ω : BVar N r t → ℕ) (ωL : Fin (N + 1) → ℕ)
    (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a) (g : MvPolynomial (BVar N r t) (KK O)) (hg : g ∈ XiPolZ O N r t b') :
    IsWeightedHomogeneous ω g (b' * ωL (Fin.last N)) := by
  classical
  intro d hd
  have hg1 := (Submodule.mem_inf.mp hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hg1
  obtain ⟨hsupp, hsum⟩ := hg1 (MvPolynomial.mem_support_iff.mpr hd)
  have hinj : Function.Injective (xiVar N r t) := by
    intro a b h
    simp only [xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
    exact h.2
  have hsub : d.support ⊆ Finset.univ.image (xiVar N r t) := by
    intro v hv
    obtain ⟨c, rfl⟩ := hsupp v hv
    exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
  rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset d hsub (fun i (c : ℕ) => c • ω i) (fun _ _ => zero_smul _ _),
    Finset.sum_image (fun a _ b _ h => hinj h), ← hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_eq_mul]
  congr 1
  exact h1 _ _

variable {s r : ℕ}

def OmB (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (b : SegBlock s r) (ω : BVar (2 * s + 1) r S.t → ℕ)
    (ωL : Fin (2 * s + 1 + 1) → ℕ) : ℕ :=
  (∑ l : Fin S.t, (coarseA p S b (uTop S l) - b.o (uTop S l)) * ω (Sum.inr (Fin.castSucc l, false))) +
    (aPlus - b.oPlus) * ω (Sum.inr (Fin.last S.t, false)) +
    (∑ a : Fin (2 * s + 1), (segChain p S aTop b).deg a * ωL (Fin.castSucc a)) + S.bPlus * ωL (Fin.last _)

/- English proof (translation)
Establish `hb` using `level_bounds p S aTop aPlus m b jl jp h`. Rewrite using `[lev_deg]`. Establish `ha` using `a.2`. Distinguish the cases in `h2 : a.val = 2 * s`. Establish `q : a.val / 2 = s` using `by omega`.

Rewrite using `[if_pos h2, q, jE_top, chain_deg_U p S aTop b a h2]`. Use `hb.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h2]`. Establish `hi : a.val / 2 < s` using `by omega`.

Distinguish the cases in `hs : a.val / 2 < S.sigma`. Rewrite using `[jE_S S jl hs]`. Use linear arithmetic over natural numbers and integers. Establish `hb1 : jE S jl (a.val / 2) ≤ b.o ⟨a.val / 2, hi⟩ ∧ jE S jl (a.val / 2) ≤ coarseC p S aTop b ⟨a.val / 2, hi⟩` using `hb.1 ⟨a.val / 2, hi⟩ (by show S.sigma ≤ a.val / 2; omega)`. Distinguish the cases in `hpar : a.val % 2 = 0`.

Rewrite using `[segment_chain_degree_even p S aTop b a ⟨a.val / 2, hi⟩ (by show a.val = 2 * (a.val / 2); omega), if_neg hs]`. Use `hb1.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[chain_deg_E p S aTop b a ⟨a.val / 2, hi⟩ (by show a.val = 2 * (a.val / 2) + 1; omega), if_neg hs]`. Use `hb1.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem deg_split (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (jl : Fin S.t → ℕ) (jp : ℕ) (h : (blockData p S aTop aPlus m b).LevelOK jl jp) (a : Fin (2 * s + 1)) :
    (segChain p S aTop b).deg a = ((blockData p S aTop aPlus m b).lettersAt jl jp).deg a + jE S jl (a.val / 2) +
      (if a.val = 2 * s then jp else 0) := by
  have hb := level_bounds p S aTop aPlus m b jl jp h
  rw [lev_deg]
  have ha := a.2
  by_cases h2 : a.val = 2 * s
  · have q : a.val / 2 = s := by omega
    rw [if_pos h2, q, jE_top, chain_deg_U p S aTop b a h2]
    have := hb.2
    omega
  · rw [if_neg h2]
    have hi : a.val / 2 < s := by omega
    by_cases hs : a.val / 2 < S.sigma
    · rw [jE_S S jl hs]
      omega
    · have hb1 : jE S jl (a.val / 2) ≤ b.o ⟨a.val / 2, hi⟩ ∧ jE S jl (a.val / 2) ≤ coarseC p S aTop b ⟨a.val / 2, hi⟩ :=
        hb.1 ⟨a.val / 2, hi⟩ (by show S.sigma ≤ a.val / 2; omega)
      by_cases hpar : a.val % 2 = 0
      · rw [segment_chain_degree_even p S aTop b a ⟨a.val / 2, hi⟩ (by show a.val = 2 * (a.val / 2); omega), if_neg hs]
        have := hb1.1
        omega
      · rw [chain_deg_E p S aTop b a ⟨a.val / 2, hi⟩ (by show a.val = 2 * (a.val / 2) + 1; omega), if_neg hs]
        have := hb1.2
        omega

/- English proof (translation)
Set `e : Fin S.t × Fin 2 → Fin (2 * s + 1)` to `fun p => ⟨2 * (S.sigma + p.1.val) + p.2.val, by`. Establish `h1` using `p.1.2`. Establish `h2` using `p.2.2`. Simplify using `only [SegData.t] at h1`. Use the proof step `omega⟩`.

Establish `he : Function.Injective e`. Introduce and unpack `⟨l, b⟩ ⟨l', b'⟩ h`. Establish `hv : 2 * (S.sigma + l.val) + b.val = 2 * (S.sigma + l'.val) + b'.val` using `congrArg Fin.val h`. Use `b.2` as an intermediate fact. Use `b'.2` as an intermediate fact.

Conclude with `Prod.ext (Fin.ext (show l.val = l'.val by omega)) (Fin.ext (show b.val = b'.val by omega))`. Rewrite using `[← Fintype.sum_of_injective e he (fun p => jl p.1 * ωL (finPos (2 * s + 1) (2 * (uTop S p.1 : ℕ) + p.2.val))) _ ?_ ?_]`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two, mul_add]`.

Simplify using the standard rewrite rules. Introduce `a ha`. Unfold `jE`. Rewrite using `[dif_neg]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨h1, h2⟩`. Apply `ha` to reduce the goal to its premises. Use `⟨(⟨a.val / 2 - S.sigma, by simp only [SegData.t]; omega⟩, ⟨a.val % 2, by omega⟩), ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises. Use `show 2 * (S.sigma + (a.val / 2 - S.sigma)) + a.val % 2 = a.val`.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨l, b⟩`. Establish `hb` using `b.2`. Establish `hl` using `l.2`. Simplify using `only [SegData.t] at hl`.

Establish `hdiv : (2 * (S.sigma + l.val) + b.val) / 2 = S.sigma + l.val` using `by omega`. Simplify using `only [e, hdiv]`. Unfold `jE`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Use `congr 1`.

Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use `congr 1`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `[finPos, uTop]`. Use linear arithmetic over natural numbers and integers.
-/
theorem tie_sum (S : SegData s) (jl : Fin S.t → ℕ) (ωL : Fin (2 * s + 1 + 1) → ℕ) :
    ∑ a : Fin (2 * s + 1), jE S jl (a.val / 2) * ωL (Fin.castSucc a) =
      ∑ l : Fin S.t, jl l * (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) +
        ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) := by

  let e : Fin S.t × Fin 2 → Fin (2 * s + 1) := fun p =>
    ⟨2 * (S.sigma + p.1.val) + p.2.val, by
      have h1 := p.1.2
      have h2 := p.2.2
      simp only [SegData.t] at h1
      omega⟩
  have he : Function.Injective e := by
    rintro ⟨l, b⟩ ⟨l', b'⟩ h
    have hv : 2 * (S.sigma + l.val) + b.val = 2 * (S.sigma + l'.val) + b'.val := congrArg Fin.val h
    have := b.2
    have := b'.2
    exact Prod.ext (Fin.ext (show l.val = l'.val by omega)) (Fin.ext (show b.val = b'.val by omega))
  rw [← Fintype.sum_of_injective e he
    (fun p => jl p.1 * ωL (finPos (2 * s + 1) (2 * (uTop S p.1 : ℕ) + p.2.val))) _ ?_ ?_]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Fin.sum_univ_two, mul_add]
    simp
  · intro a ha
    unfold jE
    rw [dif_neg]
    · simp
    · rintro ⟨h1, h2⟩
      apply ha
      refine ⟨(⟨a.val / 2 - S.sigma, by simp only [SegData.t]; omega⟩, ⟨a.val % 2, by omega⟩), ?_⟩
      apply Fin.ext
      show 2 * (S.sigma + (a.val / 2 - S.sigma)) + a.val % 2 = a.val
      omega
  · rintro ⟨l, b⟩
    have hb := b.2
    have hl := l.2
    simp only [SegData.t] at hl
    have hdiv : (2 * (S.sigma + l.val) + b.val) / 2 = S.sigma + l.val := by omega
    simp only [e, hdiv]
    unfold jE
    rw [dif_pos ⟨by omega, by omega⟩]
    congr 1
    · congr 1
      apply Fin.ext
      simp
    · congr 1
      apply Fin.ext
      simp [finPos, uTop]
      omega

/- English proof (translation)
Use `Submodule.span_induction (p := fun x _ => IsWeightedHomogeneous ω x (OmB p S aTop aPlus b ω ωL)) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce `x hx`. Take `⟨jl, hx⟩` from `Set.mem_iUnion.1 hx`. Take `⟨jp, hx⟩` from `Set.mem_iUnion.1 hx`. Take `⟨hlev, hx⟩` from `Set.mem_iUnion.1 hx`.

Take `⟨y, hy, g, hg, rfl⟩` from `hx`. Establish `hE : ∀ l : Fin S.t, IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Ehat O (r` using `r) l) (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) := by`. Introduce `l`. Use `IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[← h2 l]`.

Conclude with `(isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)`. Use `(isWeightedHomogeneous_X (KK O) ω (Sum.inl (finPos (2 * s + 1) (2 * (uTop S l : ℕ)), c))).mul (isWeightedHomogeneous_X (KK O) ω (Sum.inl (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1), c)))` as an intermediate fact. Rewrite `this` using `[h1, h1]`. Conclude with `this`. Establish `hEp : IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Eplus O (r` using `r)) (ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)) := by`.

Use `IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[← h3]`. Conclude with `(isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)`. Use `(isWeightedHomogeneous_X (KK O) ω (Sum.inl (Fin.castSucc (⟨2 * s, by omega⟩ : Fin (2 * s + 1)), c))).mul (isWeightedHomogeneous_X (KK O) ω (Sum.inl (Fin.last (2 * s + 1), c)))` as an intermediate fact. Rewrite `this` using `[h1, h1]`.

Conclude with `this`. Establish `hA` using `IsWeightedHomogeneous.prod Finset.univ (fun l : Fin S.t => (blockData p S aTop aPlus mm b).Ehat O (r := r) l ^ jl l) _ (fun l _ => (hE l).pow (jl l))`. Establish `hB` using `hEp.pow jp`. Establish `hC` using `IsWeightedHomogeneous.prod Finset.univ (fun l : Fin S.t => (X (scalZ (2 * s + 1) r S.t (Fin.castSucc l)) : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) ^ (coarseA p S b (uTop S l) - b.o (uTop S l))) _ (fun l _ => (isWeightedHomogeneous_X (KK O) ω _).pow _)`. Establish `hD` using `(isWeightedHomogeneous_X (KK O) ω (scalZ (2 * s + 1) r S.t (Fin.last S.t))).pow (aPlus - b.oPlus)`.

Establish `hY` using `wh_chain ω ωL h1 _ y hy.1.1`. Establish `hG` using `wh_xi ω ωL h1 g hg`. Establish `hall` using `((((hA.mul hB).mul hC).mul hD).mul hY).mul hG`. Use `wh_congr hall (Eq.symm ?_)` and prove the remaining obligations. Establish `hjpB : jp ≤ S.bPlus` using `le_trans hlev.2 (min_le_right _ _)`.

Establish `hsplit : ∑ a : Fin (2 * s + 1), (segChain p S aTop b).deg a * ωL (Fin.castSucc a) = ∑ a : Fin (2 * s + 1), ((blockData p S aTop aPlus mm b).lettersAt jl jp).deg a * ωL (Fin.castSucc a) + ∑ l : Fin S.t, jl l * (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) …`. Rewrite using `[← tie_sum S jl ωL]`. Establish `e3 : jp * ωL (Fin.castSucc ⟨2 * s, by omega⟩) = ∑ a : Fin (2 * s + 1), (if a.val = 2 * s then jp else 0) * ωL (Fin.castSucc a)`. Rewrite using `[Finset.sum_eq_single (⟨2 * s, by omega⟩ : Fin (2 * s + 1))]`. Rewrite using `[if_pos rfl]`.

Introduce `c _ hc`. Rewrite using `[if_neg (fun h => hc (Fin.ext h)), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[deg_split p S aTop aPlus mm b jl jp hlev a]`. Expand and normalize the polynomial expressions, which then agree. Unfold `OmB`. Rewrite using `[hsplit]`.

Establish `hBj : S.bPlus * ωL (Fin.last _) = (S.bPlus - jp) * ωL (Fin.last _) + jp * ωL (Fin.last _)`. Rewrite using `[← add_mul, Nat.sub_add_cancel hjpB]`. Rewrite using `[hBj]`. Simplify using `only [smul_eq_mul]`. Use `show _ = (∑ l : Fin S.t, jl l * (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1)))) + jp * (ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)) + (∑ l : Fin S.t, (coarseA p S b (uTop S l) - b.o (uTop S l)) * ω (Sum.inr (Fin.castSu …`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `isWeightedHomogeneous_zero _ _ _`. Introduce `x y _ _ hx hy`. Conclude with `hx.add hy`. Introduce `c x _ hx`.

Conclude with `wh_smulO c hx`.
-/
theorem ssz_wh (O : Type) [CommRing O] [IsDomain O] [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ)
    (mm : ℝ) (b : SegBlock s r) (ω : BVar (2 * s + 1) r S.t → ℕ) (ωL : Fin (2 * s + 1 + 1) → ℕ)
    (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a)
    (h2 : ∀ l : Fin S.t, ω (Sum.inr (Fin.castSucc l, false)) + ω (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1)))
    (h3 : ω (Sum.inr (Fin.last S.t, false)) + ω (Sum.inr (Fin.last S.t, true)) =
      ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _))
    (x : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) (hx : x ∈ (blockData p S aTop aPlus mm b).SSZ O (r := r)) :
    IsWeightedHomogeneous ω x (OmB p S aTop aPlus b ω ωL) := by
  refine Submodule.span_induction (p := fun x _ => IsWeightedHomogeneous ω x (OmB p S aTop aPlus b ω ωL))
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    obtain ⟨jl, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨jp, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hlev, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, hy, g, hg, rfl⟩ := hx
    have hE : ∀ l : Fin S.t, IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Ehat O (r := r) l)
        (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) := by
      intro l
      refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)
      · rw [← h2 l]
        exact (isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)
      · have := (isWeightedHomogeneous_X (KK O) ω (Sum.inl (finPos (2 * s + 1) (2 * (uTop S l : ℕ)), c))).mul
          (isWeightedHomogeneous_X (KK O) ω (Sum.inl (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1), c)))
        rw [h1, h1] at this
        exact this
    have hEp : IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Eplus O (r := r))
        (ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)) := by
      refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)
      · rw [← h3]
        exact (isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)
      · have := (isWeightedHomogeneous_X (KK O) ω (Sum.inl (Fin.castSucc (⟨2 * s, by omega⟩ : Fin (2 * s + 1)), c))).mul
          (isWeightedHomogeneous_X (KK O) ω (Sum.inl (Fin.last (2 * s + 1), c)))
        rw [h1, h1] at this
        exact this
    have hA := IsWeightedHomogeneous.prod Finset.univ
      (fun l : Fin S.t => (blockData p S aTop aPlus mm b).Ehat O (r := r) l ^ jl l) _ (fun l _ => (hE l).pow (jl l))
    have hB := hEp.pow jp
    have hC := IsWeightedHomogeneous.prod Finset.univ
      (fun l : Fin S.t => (X (scalZ (2 * s + 1) r S.t (Fin.castSucc l)) : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) ^
        (coarseA p S b (uTop S l) - b.o (uTop S l))) _ (fun l _ => (isWeightedHomogeneous_X (KK O) ω _).pow _)
    have hD := (isWeightedHomogeneous_X (KK O) ω (scalZ (2 * s + 1) r S.t (Fin.last S.t))).pow (aPlus - b.oPlus)
    have hY := wh_chain ω ωL h1 _ y hy.1.1
    have hG := wh_xi ω ωL h1 g hg
    have hall := ((((hA.mul hB).mul hC).mul hD).mul hY).mul hG
    refine wh_congr hall (Eq.symm ?_)
    have hjpB : jp ≤ S.bPlus := le_trans hlev.2 (min_le_right _ _)
    have hsplit : ∑ a : Fin (2 * s + 1), (segChain p S aTop b).deg a * ωL (Fin.castSucc a) =
        ∑ a : Fin (2 * s + 1), ((blockData p S aTop aPlus mm b).lettersAt jl jp).deg a * ωL (Fin.castSucc a) +
        ∑ l : Fin S.t, jl l * (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) +
          ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) + jp * ωL (Fin.castSucc ⟨2 * s, by omega⟩) := by
      rw [← tie_sum S jl ωL]
      have e3 : jp * ωL (Fin.castSucc ⟨2 * s, by omega⟩) =
          ∑ a : Fin (2 * s + 1), (if a.val = 2 * s then jp else 0) * ωL (Fin.castSucc a) := by
        rw [Finset.sum_eq_single (⟨2 * s, by omega⟩ : Fin (2 * s + 1))]
        · rw [if_pos rfl]
        · intro c _ hc
          rw [if_neg (fun h => hc (Fin.ext h)), zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [deg_split p S aTop aPlus mm b jl jp hlev a]
      ring
    unfold OmB
    rw [hsplit]
    have hBj : S.bPlus * ωL (Fin.last _) = (S.bPlus - jp) * ωL (Fin.last _) + jp * ωL (Fin.last _) := by
      rw [← add_mul, Nat.sub_add_cancel hjpB]
    rw [hBj]
    simp only [smul_eq_mul]
    show _ = (∑ l : Fin S.t, jl l * (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) +
          ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1)))) +
        jp * (ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)) +
        (∑ l : Fin S.t, (coarseA p S b (uTop S l) - b.o (uTop S l)) * ω (Sum.inr (Fin.castSucc l, false))) +
        (aPlus - b.oPlus) * ω (Sum.inr (Fin.last S.t, false)) +
        (∑ a : Fin (2 * s + 1), ((blockData p S aTop aPlus mm b).lettersAt jl jp).deg a * ωL (Fin.castSucc a)) +
        (S.bPlus - jp) * ωL (Fin.last _)
    ring
  · exact isWeightedHomogeneous_zero _ _ _
  · intro x y _ _ hx hy
    exact hx.add hy
  · intro c x _ hx
    exact wh_smulO c hx

end Formalism.MainNotions.ColumnSystems.Pf
