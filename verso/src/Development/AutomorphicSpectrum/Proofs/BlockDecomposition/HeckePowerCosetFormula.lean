import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AOpRightInvariant
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow.HeckeTrace

variable {G : Type} [Group G]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant hR hu hφ`.
-/
theorem aOp_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) : ∀ g, ∀ i ∈ I, aOp R t φ (g * i) = aOp R t φ g :=
  _root_.UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant hR hu hφ

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using hφ`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `aOp_rightInvariant hR hu ih`.
-/
theorem aOp_iterate_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) (j : ℕ) :
    ∀ g, ∀ i ∈ I, (aOp R t)^[j] φ (g * i) = (aOp R t)^[j] φ g := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact aOp_rightInvariant hR hu ih

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Use `⟨{1}, by simp, ?_, fun ψ g => by simp⟩` and prove the remaining obligations. Introduce `w hw`. Conclude with `⟨1, one_mem K, by simpa using hw⟩`.

Consider the case `succ j ih`. Take `⟨W, hW0, hWK, hWf⟩` from `ih`. Use `⟨W.bind fun w => R.val.map fun r => w * r * t, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `Multiset.exists_mem_of_ne_zero hW0`. Introduce `h0`.

Establish `hm : w * 1 * t ∈ W.bind fun w => R.val.map fun r => w * r * t` using `Multiset.mem_bind.2 ⟨w, hw, Multiset.mem_map.2 ⟨1, h1, rfl⟩⟩`. Rewrite `hm` using `[h0]`. Conclude with `Multiset.notMem_zero _ hm`. Introduce `x hx`. Take `⟨w, hw, hx⟩` from `Multiset.mem_bind.1 hx`.

Take `⟨r, hr, rfl⟩` from `Multiset.mem_map.1 hx`. Take `⟨k, hk, rfl⟩` from `hWK w hw`. Use `⟨k * (t ^ j * r * (t ^ j)⁻¹), mul_mem hk (hc r hr j), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ]`. Use `group`.

Introduce `ψ g`. Rewrite using `[Function.iterate_succ_apply, hWf, Multiset.map_bind, Multiset.sum_bind]`. Use `congr 1`. Use `Multiset.map_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Multiset.map_map]`.

Use `show ∑ r ∈ R, ψ (g * w * r * t) = _`. Simplify using `only [Function.comp, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem exists_words (K : Subgroup G) (t : G) (R : Finset G) (h1 : (1 : G) ∈ R)
    (hc : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) (j : ℕ) :
    ∃ W : Multiset G, W ≠ 0 ∧ (∀ w ∈ W, ∃ k ∈ K, w = k * t ^ j) ∧
      ∀ (ψ : G → ℂ) (g : G), (aOp R t)^[j] ψ g = (W.map fun w => ψ (g * w)).sum := by
  induction j with
  | zero =>
    refine ⟨{1}, by simp, ?_, fun ψ g => by simp⟩
    intro w hw
    exact ⟨1, one_mem K, by simpa using hw⟩
  | succ j ih =>
    obtain ⟨W, hW0, hWK, hWf⟩ := ih
    refine ⟨W.bind fun w => R.val.map fun r => w * r * t, ?_, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
      intro h0
      have hm : w * 1 * t ∈ W.bind fun w => R.val.map fun r => w * r * t :=
        Multiset.mem_bind.2 ⟨w, hw, Multiset.mem_map.2 ⟨1, h1, rfl⟩⟩
      rw [h0] at hm
      exact Multiset.notMem_zero _ hm
    · intro x hx
      obtain ⟨w, hw, hx⟩ := Multiset.mem_bind.1 hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨k, hk, rfl⟩ := hWK w hw
      refine ⟨k * (t ^ j * r * (t ^ j)⁻¹), mul_mem hk (hc r hr j), ?_⟩
      rw [pow_succ]
      group
    · intro ψ g
      rw [Function.iterate_succ_apply, hWf, Multiset.map_bind, Multiset.sum_bind]
      congr 1
      refine Multiset.map_congr rfl fun w _ => ?_
      rw [Multiset.map_map]
      show ∑ r ∈ R, ψ (g * w * r * t) = _
      simp only [Function.comp, mul_assoc]
      rfl

/- English proof (translation)
Set `kk : K` to `⟨k, hk⟩`. Rewrite using `[← finsum_comp_equiv (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) (f := fun c : K ⧸ I.subgroupOf K => φ ((c.out : K) : G))]`. Use `finsum_congr fun c => ?_` and prove the remaining obligations. Establish `e : (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c = ((kk * c.out : K) : K ⧸ I.subgroupOf K)` using `by show kk • c = _ conv_lhs => rw [← QuotientGroup.out_eq' c]`. Both sides reduce to the same expression.

Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (I.subgroupOf K) (kk * c.out)`. Establish `hi : ((h : K) : G) ∈ I` using `Subgroup.mem_subgroupOf.1 h.2`. Use `show _ = φ ((((MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c).out : K) : G)`. Rewrite using `[e, hh]`. Use `show _ = φ (k * ((c.out : K) : G) * ((h : K) : G))`.

Rewrite using `[hφ _ _ hi]`.
-/
theorem finsum_left_mul {K I : Subgroup G} (hIK : I ≤ K) {φ : G → ℂ} (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g)
    {k : G} (hk : k ∈ K) :
    ∑ᶠ c : K ⧸ I.subgroupOf K, φ (k * ((c.out : K) : G)) = ∑ᶠ c : K ⧸ I.subgroupOf K, φ ((c.out : K) : G) := by
  let kk : K := ⟨k, hk⟩
  rw [← finsum_comp_equiv (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K))
    (f := fun c : K ⧸ I.subgroupOf K => φ ((c.out : K) : G))]
  refine finsum_congr fun c => ?_
  have e : (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c = ((kk * c.out : K) : K ⧸ I.subgroupOf K) := by
    show kk • c = _
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (I.subgroupOf K) (kk * c.out)
  have hi : ((h : K) : G) ∈ I := Subgroup.mem_subgroupOf.1 h.2
  show _ = φ ((((MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c).out : K) : G)
  rw [e, hh]
  show _ = φ (k * ((c.out : K) : G) * ((h : K) : G))
  rw [hφ _ _ hi]

/- English proof (translation)
Use `set M' : Multiset (G ⧸ K) := M.map (QuotientGroup.mk : G → G ⧸ K) with hM'`. Establish `hout : ∀ (ψ : G → ℂ), (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ x : G, ψ ((x : G ⧸ K).out) = ψ x`. Introduce `ψ hψ x`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul K x`. Rewrite using `[hh, hψ _ _ h.2]`.

Establish `key1 : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → (M.map ψ).sum = ∑ y ∈ M'.toFinset, (M'.count y : ℂ) * ψ y.out`. Introduce `ψ hψ`. Establish `e : M.map ψ = M'.map fun y : G ⧸ K => ψ y.out`. Rewrite using `[hM', Multiset.map_map]`. Conclude with `Multiset.map_congr rfl fun x _ => (hout ψ hψ x).symm`.

Rewrite using `[e, Finset.sum_multiset_map_count]`. Simplify using `only [nsmul_eq_mul]`. Set `e : G ⧸ K → G → ℂ` to `fun y x => if (x : G ⧸ K) = y then 1 else 0`. Establish `he : ∀ y g, ∀ k ∈ K, e y (g * k) = e y g`. Introduce `y g k hk`.

Establish `: ((g * k : G) : G ⧸ K) = g`. Rewrite using `[QuotientGroup.eq]`. Simplify using `using inv_mem hk`. Simplify using `only [e, this]`. Establish `key2 : ∀ y, (M.map (e y)).sum = (M'.count y : ℂ)`.

Introduce `y`. Rewrite using `[key1 _ (he y)]`. Establish `: ∀ z : G ⧸ K, (M'.count z : ℂ) * e y z.out = if z = y then (M'.count z : ℂ) else 0`. Introduce `z`. Simplify using `only [e, QuotientGroup.out_eq']`.

Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [this]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression.

Establish `: M'.count y = 0` using `Multiset.count_eq_zero.2 (by simpa using h)`. Simplify using `[this]`. Establish `key3 : ∀ k ∈ K, ∀ g : G, M'.count ((k * g : G) : G ⧸ K) = M'.count (g : G ⧸ K)`. Introduce `k hk g`. Establish `h1` using `hinv (e ((k * g : G) : G ⧸ K)) (he _) k hk`.

Establish `h2 : (fun x => e ((k * g : G) : G ⧸ K) (k * x)) = e (g : G ⧸ K)`. Use function extensionality and compare the values at `x`. Establish `: ((k * x : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) ↔ (x : G ⧸ K) = (g : G ⧸ K)`. Rewrite using `[QuotientGroup.eq, QuotientGroup.eq]`. Establish `: (k * x)⁻¹ * (k * g) = x⁻¹ * g` using `by group`.

Rewrite using `[this]`. Simplify using `only [e, this]`. Rewrite `h1` using `[h2, key2, key2]`. Conclude with `h1.symm` after adjusting the coercions. Take `⟨x0, hx0⟩` from `Multiset.exists_mem_of_ne_zero hM0`.

Establish `hconst : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G), M'.count (g : G ⧸ K) = M'.count (x0 : G ⧸ K)`. Establish `hred : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G), M'.count (g : G ⧸ K) = M'.count (s : G ⧸ K)`. Introduce `g hg`. Take `⟨a, ha, b, hb, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hg`. Establish `: ((a * s * b : G) : G ⧸ K) = ((a * s : G) : G ⧸ K)`.

Rewrite using `[QuotientGroup.eq]`. Simplify `inv_mem hb` using `[mul_assoc]`. Rewrite using `[this, key3 a ha]`. Introduce `g hg`. Rewrite using `[hred g hg, hred x0 (hMs x0 hx0)]`.

Establish `hpos : 0 < M'.count (x0 : G ⧸ K)` using `Multiset.count_pos.2 (Multiset.mem_map_of_mem _ hx0)`. Use `⟨M'.count (x0 : G ⧸ K), hpos, fun ψ hψ => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ y : G ⧸ K, y ∈ M'.toFinset ↔ y.out ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G)`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Take `⟨x, hx, rfl⟩` from `Multiset.mem_map.1 (Multiset.mem_toFinset.1 hy)`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul K x`. Take `⟨a, ha, b, hb, e1⟩` from `DoubleCoset.mem_doubleCoset.1 (hMs x hx)`. Use `DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * h, mul_mem hb h.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[hh, e1]`. Use `group`. Introduce `hy`. Establish `h` using `hconst _ hy`. Rewrite `h` using `[QuotientGroup.out_eq']`.

Use `Multiset.mem_toFinset.2 (Multiset.count_pos.1 ?_)` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `hpos`. Establish `hact : hAct K (dosetInd ℂ K s) ψ 1 = ∑ y ∈ M'.toFinset, ψ y.out`. Unfold `hAct`.

Rewrite using `[finsum_eq_sum_of_support_subset (s := M'.toFinset)]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Establish `h` using `(hmem y).1 hy`. Simplify using `[dosetInd, Set.indicator_of_mem h]`. Introduce `y hy`.

Assume the negation of the conclusion as `hn`. Establish `h : y.out ∉ DoubleCoset.doubleCoset s (K : Set G) (K : Set G)` using `fun h => hn ((hmem y).2 h)`. Apply `hy` to reduce the goal to its premises. Simplify using `[dosetInd, Set.indicator_of_notMem h]`. Rewrite using `[hact, key1 ψ hψ, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Establish `h` using `hconst _ ((hmem y).1 hy)`. Rewrite `h` using `[QuotientGroup.out_eq']`. Rewrite using `[h]`.
-/
theorem multiset_sum_eq_hAct (K : Subgroup G) (s : G) (M : Multiset G) (hM0 : M ≠ 0)
    (hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G))
    (hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum) :
    ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = (m : ℂ) * hAct K (dosetInd ℂ K s) ψ 1 := by
  classical
  set M' : Multiset (G ⧸ K) := M.map (QuotientGroup.mk : G → G ⧸ K) with hM'
  have hout : ∀ (ψ : G → ℂ), (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ x : G,
      ψ ((x : G ⧸ K).out) = ψ x := by
    intro ψ hψ x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
    rw [hh, hψ _ _ h.2]
  have key1 : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = ∑ y ∈ M'.toFinset, (M'.count y : ℂ) * ψ y.out := by
    intro ψ hψ
    have e : M.map ψ = M'.map fun y : G ⧸ K => ψ y.out := by
      rw [hM', Multiset.map_map]
      exact Multiset.map_congr rfl fun x _ => (hout ψ hψ x).symm
    rw [e, Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
  let e : G ⧸ K → G → ℂ := fun y x => if (x : G ⧸ K) = y then 1 else 0
  have he : ∀ y g, ∀ k ∈ K, e y (g * k) = e y g := by
    intro y g k hk
    have : ((g * k : G) : G ⧸ K) = g := by
      rw [QuotientGroup.eq]
      simpa using inv_mem hk
    simp only [e, this]
  have key2 : ∀ y, (M.map (e y)).sum = (M'.count y : ℂ) := by
    intro y
    rw [key1 _ (he y)]
    have : ∀ z : G ⧸ K, (M'.count z : ℂ) * e y z.out = if z = y then (M'.count z : ℂ) else 0 := by
      intro z
      simp only [e, QuotientGroup.out_eq']
      split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · have : M'.count y = 0 := Multiset.count_eq_zero.2 (by simpa using h)
      simp [this]
  have key3 : ∀ k ∈ K, ∀ g : G, M'.count ((k * g : G) : G ⧸ K) = M'.count (g : G ⧸ K) := by
    intro k hk g
    have h1 := hinv (e ((k * g : G) : G ⧸ K)) (he _) k hk
    have h2 : (fun x => e ((k * g : G) : G ⧸ K) (k * x)) = e (g : G ⧸ K) := by
      funext x
      have : ((k * x : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) ↔ (x : G ⧸ K) = (g : G ⧸ K) := by
        rw [QuotientGroup.eq, QuotientGroup.eq]
        have : (k * x)⁻¹ * (k * g) = x⁻¹ * g := by group
        rw [this]
      simp only [e, this]
    rw [h2, key2, key2] at h1
    exact_mod_cast h1.symm
  obtain ⟨x0, hx0⟩ := Multiset.exists_mem_of_ne_zero hM0
  have hconst : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
      M'.count (g : G ⧸ K) = M'.count (x0 : G ⧸ K) := by
    have hred : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
        M'.count (g : G ⧸ K) = M'.count (s : G ⧸ K) := by
      intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      have : ((a * s * b : G) : G ⧸ K) = ((a * s : G) : G ⧸ K) := by
        rw [QuotientGroup.eq]
        simpa [mul_assoc] using inv_mem hb
      rw [this, key3 a ha]
    intro g hg
    rw [hred g hg, hred x0 (hMs x0 hx0)]
  have hpos : 0 < M'.count (x0 : G ⧸ K) :=
    Multiset.count_pos.2 (Multiset.mem_map_of_mem _ hx0)
  refine ⟨M'.count (x0 : G ⧸ K), hpos, fun ψ hψ => ?_⟩
  have hmem : ∀ y : G ⧸ K, y ∈ M'.toFinset ↔ y.out ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hy)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
      obtain ⟨a, ha, b, hb, e1⟩ := DoubleCoset.mem_doubleCoset.1 (hMs x hx)
      refine DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * h, mul_mem hb h.2, ?_⟩
      rw [hh, e1]
      group
    · intro hy
      have h := hconst _ hy
      rw [QuotientGroup.out_eq'] at h
      refine Multiset.mem_toFinset.2 (Multiset.count_pos.1 ?_)
      rw [h]
      exact hpos
  have hact : hAct K (dosetInd ℂ K s) ψ 1 = ∑ y ∈ M'.toFinset, ψ y.out := by
    unfold hAct
    rw [finsum_eq_sum_of_support_subset (s := M'.toFinset)]
    · refine Finset.sum_congr rfl fun y hy => ?_
      have h := (hmem y).1 hy
      simp [dosetInd, Set.indicator_of_mem h]
    · intro y hy
      by_contra hn
      have h : y.out ∉ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := fun h => hn ((hmem y).2 h)
      apply hy
      simp [dosetInd, Set.indicator_of_notMem h]
  rw [hact, key1 ψ hψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h := hconst _ ((hmem y).1 hy)
  rw [QuotientGroup.out_eq'] at h
  rw [h]

/- English proof (translation)
Introduce `G _ K I hIK hfin t R h1 hR hc hu j`. Use `haveI := Fintype.ofFinite (K ⧸ I.subgroupOf K)`. Take `⟨W, hW0, hWK, hWf⟩` from `exists_words K t R h1 hc j`. Use `set M : Multiset G := (Finset.univ : Finset (K ⧸ I.subgroupOf K)).val.bind fun c => W.map fun w => ((c.out : K) : G) * w with hMdef`. Establish `hM : ∀ φ : G → ℂ, (M.map φ).sum = ∑ c : K ⧸ I.subgroupOf K, (W.map fun w => φ (((c.out : K) : G) * w)).sum`.

Introduce `φ`. Rewrite using `[hMdef, Multiset.map_bind, Multiset.sum_bind]`. Simplify using `only [Multiset.map_map, Function.comp_def]`. Both sides reduce to the same expression. Establish `hL : ∀ ψ : G → ℂ, ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (M.map ψ).sum`.

Introduce `ψ`. Rewrite using `[finsum_eq_sum_of_fintype, hM]`. Conclude with `Finset.sum_congr rfl fun c _ => hWf ψ _`. Establish `hIinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ g, ∀ i ∈ I, ψ (g * i) = ψ g` using `fun ψ hψ g i hi => hψ g i (hIK hi)`. Establish `hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K, (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum`.

Introduce `ψ hψ k hk`. Rewrite using `[← hL ψ, ← finsum_left_mul hIK (aOp_iterate_rightInvariant hR hu (hIinv ψ hψ) j) hk, finsum_eq_sum_of_fintype, hM]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hWf ψ]`. Simplify using `only [mul_assoc]`.

Establish `hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset (t ^ j) (K : Set G) (K : Set G)`. Introduce `x hx`. Take `⟨c, -, hx⟩` from `Multiset.mem_bind.1 hx`. Take `⟨w, hw, rfl⟩` from `Multiset.mem_map.1 hx`. Take `⟨k, hk, rfl⟩` from `hWK w hw`.

Conclude with `DoubleCoset.mem_doubleCoset.2 ⟨((c.out : K) : G) * k, mul_mem (c.out : K).2 hk, 1, one_mem K, by simp [mul_assoc]⟩`. Establish `hM0 : M ≠ 0`. Take `⟨w, hw⟩` from `Multiset.exists_mem_of_ne_zero hW0`. Set `c0 : K ⧸ I.subgroupOf K` to `((1 : K) : K ⧸ I.subgroupOf K)`. Introduce `h0`.

Establish `hm : ((c0.out : K) : G) * w ∈ M` using `Multiset.mem_bind.2 ⟨c0, Finset.mem_univ c0, Multiset.mem_map.2 ⟨w, hw, rfl⟩⟩`. Rewrite `hm` using `[h0]`. Conclude with `Multiset.notMem_zero _ hm`. Take `⟨m, hm, hmf⟩` from `multiset_sum_eq_hAct K (t ^ j) M hM0 hMs hinv`. Conclude with `⟨m, hm, fun ψ hψ => by rw [hL, hmf ψ hψ]⟩`.
-/
theorem heckeTrace : ∀ (G : Type) [Group G] (K I : Subgroup G), I ≤ K → Finite (K ⧸ I.subgroupOf K) → ∀ (t : G) (R : Finset G), (1 : G) ∈ R → (∀ r ∈ R, r ∈ I) → (∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) → (∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) → ∀ j : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (m : ℂ) * hAct K (dosetInd ℂ K (t ^ j)) ψ 1 := by
  intro G _ K I hIK hfin t R h1 hR hc hu j
  classical
  haveI := Fintype.ofFinite (K ⧸ I.subgroupOf K)
  obtain ⟨W, hW0, hWK, hWf⟩ := exists_words K t R h1 hc j
  set M : Multiset G := (Finset.univ : Finset (K ⧸ I.subgroupOf K)).val.bind
    fun c => W.map fun w => ((c.out : K) : G) * w with hMdef
  have hM : ∀ φ : G → ℂ, (M.map φ).sum =
      ∑ c : K ⧸ I.subgroupOf K, (W.map fun w => φ (((c.out : K) : G) * w)).sum := by
    intro φ
    rw [hMdef, Multiset.map_bind, Multiset.sum_bind]
    simp only [Multiset.map_map, Function.comp_def]
    rfl
  have hL : ∀ ψ : G → ℂ, ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (M.map ψ).sum := by
    intro ψ
    rw [finsum_eq_sum_of_fintype, hM]
    exact Finset.sum_congr rfl fun c _ => hWf ψ _
  have hIinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ g, ∀ i ∈ I, ψ (g * i) = ψ g :=
    fun ψ hψ g i hi => hψ g i (hIK hi)
  have hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum := by
    intro ψ hψ k hk
    rw [← hL ψ, ← finsum_left_mul hIK (aOp_iterate_rightInvariant hR hu (hIinv ψ hψ) j) hk,
      finsum_eq_sum_of_fintype, hM]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hWf ψ]
    simp only [mul_assoc]
  have hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset (t ^ j) (K : Set G) (K : Set G) := by
    intro x hx
    obtain ⟨c, -, hx⟩ := Multiset.mem_bind.1 hx
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨k, hk, rfl⟩ := hWK w hw
    exact DoubleCoset.mem_doubleCoset.2
      ⟨((c.out : K) : G) * k, mul_mem (c.out : K).2 hk, 1, one_mem K, by simp [mul_assoc]⟩
  have hM0 : M ≠ 0 := by
    obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
    let c0 : K ⧸ I.subgroupOf K := ((1 : K) : K ⧸ I.subgroupOf K)
    intro h0
    have hm : ((c0.out : K) : G) * w ∈ M :=
      Multiset.mem_bind.2 ⟨c0, Finset.mem_univ c0, Multiset.mem_map.2 ⟨w, hw, rfl⟩⟩
    rw [h0] at hm
    exact Multiset.notMem_zero _ hm
  obtain ⟨m, hm, hmf⟩ := multiset_sum_eq_hAct K (t ^ j) M hM0 hMs hinv
  exact ⟨m, hm, fun ψ hψ => by rw [hL, hmf ψ hψ]⟩

end GlobalTheory.CompanionTheory.SatPow.HeckeTrace

end
