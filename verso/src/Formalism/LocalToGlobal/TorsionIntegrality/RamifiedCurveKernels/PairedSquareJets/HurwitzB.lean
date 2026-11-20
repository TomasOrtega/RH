import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementH
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.G

open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)

namespace HurwitzJetIntegrality

/- English proof (translation)
Take `⟨hC, -, -, -, hmul⟩` from `h1 K R ι`. Conclude with `Finset.prod_induction g (JetsIn R) (fun a b ha hb => hmul a b ha hb) (by simpa using hC 1 R.one_mem) hg`.
-/
theorem jetsIn_prod (h1 : JetsRing) {K : Type} [Field K] (R : Subring K) {ι α : Type}
    (s : Finset α) (g : α → MvPowerSeries ι K) (hg : ∀ x ∈ s, JetsIn R (g x)) :
    JetsIn R (∏ x ∈ s, g x) := by
  obtain ⟨hC, -, -, -, hmul⟩ := h1 K R ι
  exact Finset.prod_induction g (JetsIn R) (fun a b ha hb => hmul a b ha hb)
    (by simpa using hC 1 R.one_mem) hg

/- English proof (translation)
Take `⟨hC, -, -, -, hmul⟩` from `h1 K R κ`. Establish `e : MvPowerSeries.C (MvPowerSeries.coeff d f) * d.prod (fun s e => (a s) ^ e) = MvPowerSeries.C (((mfact d : ℕ) : K) * MvPowerSeries.coeff d f) * d.prod (fun s e => MvPowerSeries.C ((e.factorial : K)⁻¹) * (a s) ^ e)`. Simplify using `only [mfact, Finsupp.prod]`. Rewrite using `[Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]`. Use `congr 2`.

Use `push_cast`. Rewrite using `[mul_comm (∏ x ∈ d.support, ((d x).factorial : K)) _, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun x _ => mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))), mul_one]`. Rewrite using `[e]`. Use `hmul _ _ (hC _ (hf d)) ?_` and prove the remaining obligations. Simplify using `only [Finsupp.prod]`.

Conclude with `Finset.prod_induction _ (JetsIn R) (fun x y hx hy => hmul x y hx hy) (by simpa using hC 1 R.one_mem) (fun s _ => h2 K R κ (a s) (ha0 s) (ha s) (d s))`.
-/
theorem jetsIn_term (h1 : JetsRing) (h2 : JetsDivPow) {K : Type} [Field K] [CharZero K]
    (R : Subring K) {ι κ : Type} (f : MvPowerSeries ι K) (a : ι → MvPowerSeries κ K)
    (hf : JetsIn R f) (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, JetsIn R (a i)) (d : ι →₀ ℕ) :
    JetsIn R (MvPowerSeries.C (MvPowerSeries.coeff d f) * d.prod fun s e => (a s) ^ e) := by
  obtain ⟨hC, -, -, -, hmul⟩ := h1 K R κ
  have e : MvPowerSeries.C (MvPowerSeries.coeff d f) * d.prod (fun s e => (a s) ^ e) =
      MvPowerSeries.C (((mfact d : ℕ) : K) * MvPowerSeries.coeff d f) *
        d.prod (fun s e => MvPowerSeries.C ((e.factorial : K)⁻¹) * (a s) ^ e) := by
    simp only [mfact, Finsupp.prod]
    rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]
    congr 2
    push_cast
    rw [mul_comm (∏ x ∈ d.support, ((d x).factorial : K)) _, mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one (fun x _ => mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))),
      mul_one]
  rw [e]
  refine hmul _ _ (hC _ (hf d)) ?_
  simp only [Finsupp.prod]
  exact Finset.prod_induction _ (JetsIn R) (fun x y hx hy => hmul x y hx hy)
    (by simpa using hC 1 R.one_mem) (fun s _ => h2 K R κ (a s) (ha0 s) (ha s) (d s))

end HurwitzJetIntegrality

open HurwitzJetIntegrality

/- English proof (translation)
Introduce `K _ _ R ι κ _ f a hf ha0 ha n`. Establish `hs : MvPowerSeries.HasSubst a` using `by first`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha0`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by simp [ha0 i, IsNilpotent.zero])`. Consider the case `exact ⟨fun i => by simp [ha0 i, IsNilpotent.zero], by simp [Filter.cofinite_eq_bot]⟩`.

Rewrite using `[MvPowerSeries.coeff_subst hs]`. Use `finsum_induction (fun x => ((mfact n : ℕ) : K) * x ∈ R) (by simp) (fun x y hx hy => by rw [mul_add]; exact R.add_mem hx hy) (fun d => ?_)` and prove the remaining obligations. Establish `h` using `jetsIn_term h1 h2 R f a hf ha0 ha d n`. Rewrite `h` using `[MvPowerSeries.coeff_C_mul]`. Simplify `h` using `only [smul_eq_mul]`.
-/
theorem JetsSubst_of (h1 : JetsRing) (h2 : JetsDivPow) : JetsSubst := by
  intro K _ _ R ι κ _ f a hf ha0 ha n
  have hs : MvPowerSeries.HasSubst a := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by simp [ha0 i, IsNilpotent.zero])
      | exact ⟨fun i => by simp [ha0 i, IsNilpotent.zero], by simp [Filter.cofinite_eq_bot]⟩
  rw [MvPowerSeries.coeff_subst hs]
  refine finsum_induction (fun x => ((mfact n : ℕ) : K) * x ∈ R) (by simp)
    (fun x y hx hy => by rw [mul_add]; exact R.add_mem hx hy) (fun d => ?_)
  have h := jetsIn_term h1 h2 R f a hf ha0 ha d n
  rw [MvPowerSeries.coeff_C_mul] at h
  simpa only [smul_eq_mul] using h

namespace HurwitzJetIntegrality

def blockEmb (B ι : Type) (k : B) : ι ↪ B × ι := ⟨fun i => (k, i), fun _ _ h => (Prod.mk.inj h).2⟩

/- English proof (translation)
Unfold `inBlock`. Use `first`. Consider the case `exact (MvPowerSeries.rename_eq_subst (blockEmb B ι k) f).symm`. Consider the case `exact (MvPowerSeries.rename_eq_subst f (blockEmb B ι k)).symm`. Consider the case `(rw [MvPowerSeries.rename_eq_subst]; rfl)`.

Consider the case `rfl`.
-/
theorem inBlock_eq_rename {K : Type} [Field K] {ι B : Type} (k : B) (f : MvPowerSeries ι K) :
    inBlock k f = MvPowerSeries.rename (blockEmb B ι k) f := by
  unfold inBlock
  first
    | exact (MvPowerSeries.rename_eq_subst (blockEmb B ι k) f).symm
    | exact (MvPowerSeries.rename_eq_subst f (blockEmb B ι k)).symm
    | (rw [MvPowerSeries.rename_eq_subst]; rfl)
    | rfl

/- English proof (translation)
Rewrite using `[inBlock_eq_rename, Finsupp.embDomain_eq_mapDomain]`. Simplify using `only [MvPowerSeries.coeff_rename]`. Rewrite using `[Finset.sum_eq_single κ]`. Introduce `b hb hbk`. It suffices to derive a contradiction.

Apply `hbk` to reduce the goal to its premises. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hb`. Conclude with `Finsupp.mapDomain_injective (blockEmb B ι k).injective hb`. Introduce `hκ`. It suffices to derive a contradiction.

Apply `hκ` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem coeff_inBlock_embDomain {K : Type} [Field K] {ι B : Type} (k : B) (f : MvPowerSeries ι K)
    (κ : ι →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain (blockEmb B ι k) κ) (inBlock k f) =
      MvPowerSeries.coeff κ f := by
  rw [inBlock_eq_rename, Finsupp.embDomain_eq_mapDomain]
  simp only [MvPowerSeries.coeff_rename]
  rw [Finset.sum_eq_single κ]
  · intro b hb hbk
    exfalso
    apply hbk
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hb
    exact Finsupp.mapDomain_injective (blockEmb B ι k).injective hb
  · intro hκ
    exfalso
    apply hκ
    simp

/- English proof (translation)
Rewrite `h` using `[inBlock_eq_rename]`. Assume the negation of the conclusion as `hx`. Use `push_neg at hx`. Apply `h` to reduce the goal to its premises. Apply `MvPowerSeries.coeff_rename_eq_zero` to reduce the goal to its premises.

Introduce and unpack `⟨m, rfl⟩`. Conclude with `hx m (Finsupp.embDomain_eq_mapDomain _ _).symm`.
-/
theorem exists_of_coeff_inBlock_ne_zero {K : Type} [Field K] {ι B : Type} (k : B)
    (f : MvPowerSeries ι K) (x : B × ι →₀ ℕ) (h : MvPowerSeries.coeff x (inBlock k f) ≠ 0) :
    ∃ m : ι →₀ ℕ, x = Finsupp.embDomain (blockEmb B ι k) m := by
  rw [inBlock_eq_rename] at h
  by_contra hx
  push_neg at hx
  apply h
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨m, rfl⟩
  exact hx m (Finsupp.embDomain_eq_mapDomain _ _).symm

def rep (B : Type) [Fintype B] {ι : Type} (m : B → ι →₀ ℕ) : B × ι →₀ ℕ :=
  ∑ k : B, Finsupp.embDomain (blockEmb B ι k) (m k)

/- English proof (translation)
Unfold `rep`. Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single k]`. Use `first`. Consider the case `exact Finsupp.embDomain_apply_self (blockEmb B ι k) (m k) i`. Consider the case `exact Finsupp.embDomain_apply_self (f := blockEmb B ι k) (v := m k) (a := i)`.

Consider the case `simp [Finsupp.embDomain_apply, blockEmb]`. Introduce `k' _ hk'`. Rewrite using `[Finsupp.embDomain_notin_range]`. Introduce and unpack `⟨j, hj⟩`. Conclude with `hk' (congrArg Prod.fst hj)`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`.
-/
theorem rep_apply (B : Type) [Fintype B] {ι : Type} (m : B → ι →₀ ℕ) (k : B) (i : ι) :
    rep B m (k, i) = m k i := by
  classical
  unfold rep
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single k]
  · first
      | exact Finsupp.embDomain_apply_self (blockEmb B ι k) (m k) i
      | exact Finsupp.embDomain_apply_self (f := blockEmb B ι k) (v := m k) (a := i)
      | simp [Finsupp.embDomain_apply, blockEmb]
  · intro k' _ hk'
    rw [Finsupp.embDomain_notin_range]
    rintro ⟨j, hj⟩
    exact hk' (congrArg Prod.fst hj)
  · intro h
    exact absurd (Finset.mem_univ k) h

/- English proof (translation)
Establish `hx : ∀ {α : Type} [Fintype α] (x : α →₀ ℕ), mfact x = ∏ p, (x p).factorial` using `fun x => Finsupp.prod_of_support_subset x (Finset.subset_univ _) (fun _ k => k.factorial) (fun _ _ => rfl)`. Rewrite using `[hx, hx, Fintype.prod_prod_type]`. Simplify using `only [rep_apply]`. Rewrite using `[Finset.prod_const, Finset.card_univ]`.
-/
theorem mfact_rep (B : Type) [Fintype B] {ι : Type} [Fintype ι] (κ : ι →₀ ℕ) :
    mfact (rep B fun _ => κ) = (mfact κ) ^ Fintype.card B := by
  classical
  have hx : ∀ {α : Type} [Fintype α] (x : α →₀ ℕ), mfact x = ∏ p, (x p).factorial := fun x =>
    Finsupp.prod_of_support_subset x (Finset.subset_univ _) (fun _ k => k.factorial) (fun _ _ => rfl)
  rw [hx, hx, Fintype.prod_prod_type]
  simp only [rep_apply]
  rw [Finset.prod_const, Finset.card_univ]

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_prod]`. Rewrite using `[Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm fun k => Finsupp.embDomain (blockEmb B ι k) κ)]`. Rewrite using `[Finset.prod_congr rfl (fun k _ => show MvPowerSeries.coeff ((Finsupp.equivFunOnFinite.symm fun k => Finsupp.embDomain (blockEmb B ι k) κ) k) (inBlock k f) = MvPowerSeries.coeff κ f from coeff_inBlock_embDomain k f κ)]`. Rewrite using `[Finset.prod_const, Finset.card_univ]`. Introduce `l hl hne`.

Assume the negation of the conclusion as `hprod`. Apply `hne` to reduce the goal to its premises. Establish `hex : ∀ k, ∃ m : ι →₀ ℕ, l k = Finsupp.embDomain (blockEmb B ι k) m` using `fun k => exists_of_coeff_inBlock_ne_zero k f (l k) (fun h0 => hprod (Finset.prod_eq_zero (Finset.mem_univ k) h0))`. Use `choose m hm using hex`. Rewrite `hl` using `[Finset.mem_finsuppAntidiag]`.

Use extensionality with `k : 1`. Use `show l k = Finsupp.embDomain (blockEmb B ι k) κ`. Rewrite using `[hm k]`. Use `congr 1`. Use extensionality with `i`.

Establish `h1` using `congrArg (fun x : B × ι →₀ ℕ => x (k, i)) hl.1`. Simplify using `only [Finsupp.finset_sum_apply, rep_apply, hm] at h1`. Rewrite `h1` using `[Finset.sum_eq_single k]`. Rewrite using `[← h1]`. Use `symm`.

Use `first`. Consider the case `exact Finsupp.embDomain_apply_self (blockEmb B ι k) (m k) i`. Consider the case `exact Finsupp.embDomain_apply_self (f := blockEmb B ι k) (v := m k) (a := i)`. Consider the case `simp [Finsupp.embDomain_apply, blockEmb]`. Introduce `k' _ hk'`.

Rewrite using `[Finsupp.embDomain_notin_range]`. Introduce and unpack `⟨j, hj⟩`. Conclude with `hk' (congrArg Prod.fst hj)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`.

Introduce `h`. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Rewrite using `[Finset.mem_finsuppAntidiag]`. Use `⟨?_, fun _ _ => Finset.mem_univ _⟩` and prove the remaining obligations.

Use extensionality with `⟨k, i⟩`. Rewrite using `[Finsupp.finset_sum_apply, rep_apply, Finset.sum_eq_single k]`. Use `show (Finsupp.embDomain (blockEmb B ι k) κ) (k, i) = κ i first`. Consider the case `exact Finsupp.embDomain_apply_self (blockEmb B ι k) κ i`. Consider the case `exact Finsupp.embDomain_apply_self (f := blockEmb B ι k) (v := κ) (a := i)`.

Consider the case `simp [Finsupp.embDomain_apply, blockEmb]`. Introduce `k' _ hk' show (Finsupp.embDomain (blockEmb B ι k') κ) (k, i) = 0`. Rewrite using `[Finsupp.embDomain_notin_range]`. Introduce and unpack `⟨j, hj⟩`. Conclude with `hk' (congrArg Prod.fst hj)`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`.
-/
theorem coeff_prod_inBlock {K : Type} [Field K] {ι B : Type} [Fintype B]
    (f : MvPowerSeries ι K) (κ : ι →₀ ℕ) :
    MvPowerSeries.coeff (rep B fun _ => κ) (∏ k : B, inBlock k f) =
      (MvPowerSeries.coeff κ f) ^ Fintype.card B := by
  classical
  rw [MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm fun k => Finsupp.embDomain (blockEmb B ι k) κ)]
  · rw [Finset.prod_congr rfl (fun k _ => show MvPowerSeries.coeff
        ((Finsupp.equivFunOnFinite.symm fun k => Finsupp.embDomain (blockEmb B ι k) κ) k) (inBlock k f) =
        MvPowerSeries.coeff κ f from coeff_inBlock_embDomain k f κ)]
    rw [Finset.prod_const, Finset.card_univ]
  · intro l hl hne
    by_contra hprod
    apply hne
    have hex : ∀ k, ∃ m : ι →₀ ℕ, l k = Finsupp.embDomain (blockEmb B ι k) m := fun k =>
      exists_of_coeff_inBlock_ne_zero k f (l k) (fun h0 => hprod (Finset.prod_eq_zero (Finset.mem_univ k) h0))
    choose m hm using hex
    rw [Finset.mem_finsuppAntidiag] at hl
    ext k : 1
    show l k = Finsupp.embDomain (blockEmb B ι k) κ
    rw [hm k]
    congr 1
    ext i
    have h1 := congrArg (fun x : B × ι →₀ ℕ => x (k, i)) hl.1
    simp only [Finsupp.finset_sum_apply, rep_apply, hm] at h1
    rw [Finset.sum_eq_single k] at h1
    · rw [← h1]
      symm
      first
        | exact Finsupp.embDomain_apply_self (blockEmb B ι k) (m k) i
        | exact Finsupp.embDomain_apply_self (f := blockEmb B ι k) (v := m k) (a := i)
        | simp [Finsupp.embDomain_apply, blockEmb]
    · intro k' _ hk'
      rw [Finsupp.embDomain_notin_range]
      rintro ⟨j, hj⟩
      exact hk' (congrArg Prod.fst hj)
    · intro h
      exact absurd (Finset.mem_univ k) h
  · intro h
    exfalso
    apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, fun _ _ => Finset.mem_univ _⟩
    ext ⟨k, i⟩
    rw [Finsupp.finset_sum_apply, rep_apply, Finset.sum_eq_single k]
    · show (Finsupp.embDomain (blockEmb B ι k) κ) (k, i) = κ i
      first
        | exact Finsupp.embDomain_apply_self (blockEmb B ι k) κ i
        | exact Finsupp.embDomain_apply_self (f := blockEmb B ι k) (v := κ) (a := i)
        | simp [Finsupp.embDomain_apply, blockEmb]
    · intro k' _ hk'
      show (Finsupp.embDomain (blockEmb B ι k') κ) (k, i) = 0
      rw [Finsupp.embDomain_notin_range]
      rintro ⟨j, hj⟩
      exact hk' (congrArg Prod.fst hj)
    · intro h
      exact absurd (Finset.mem_univ k) h

end HurwitzJetIntegrality

/- English proof (translation)
Introduce `K _ R ι _ f h4 hf κ`. Apply `h4` to reduce the goal to its premises. Establish `h` using `hf (HurwitzJetIntegrality.rep (Fin 4) fun _ => κ)`. Unfold `tens4 at h`. Rewrite `h` using `[HurwitzJetIntegrality.coeff_prod_inBlock, HurwitzJetIntegrality.mfact_rep]`.

Simplify `h` using `[mul_pow]`.
-/
theorem jets_fourth_holds : JetsFourth := by
  intro K _ R ι _ f h4 hf κ
  apply h4
  have h := hf (HurwitzJetIntegrality.rep (Fin 4) fun _ => κ)
  unfold tens4 at h
  rw [HurwitzJetIntegrality.coeff_prod_inBlock, HurwitzJetIntegrality.mfact_rep] at h
  simpa [mul_pow] using h

/- English proof (translation)
Introduce `K _ _ R l linv f h`. Unfold `JetsIn1`. Simplify using `only [Formalism.L2.Th1.C.jetAdditive K l linv f h]`.
-/
theorem jets_of_dist_jets_holds : JetsOfDJets := by
  intro K _ _ R l linv f h
  unfold JetsIn1
  simp only [Formalism.L2.Th1.C.jetAdditive K l linv f h]

/- English proof (translation)
Introduce `n`. Rewrite using `[PowerSeries.coeff_mul]`. Conclude with `R.sum_mem fun p _ => R.mul_mem (hf p.1) (hg p.2)`.
-/
private theorem intPS_mul_paired_square_jets {K : Type} [Field K] {R : Subring K} {f g : PowerSeries K}
    (hf : Formalism.L2.Th1.C.IntPS R f) (hg : Formalism.L2.Th1.C.IntPS R g) : Formalism.L2.Th1.C.IntPS R (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact R.sum_mem fun p _ => R.mul_mem (hf p.1) (hg p.2)

/- English proof (translation)
Introduce `n`. Establish `h : PowerSeries.coeff n (PowerSeries.derivative K f) = PowerSeries.coeff (n + 1) f * (n + 1)` using `by first`. Consider the case `exact PowerSeries.coeff_derivativeFun f n`. Consider the case `(rw [PowerSeries.derivative_coe, PowerSeries.coeff_derivativeFun])`. Consider the case `simp [PowerSeries.derivative]`.

Rewrite using `[h]`. Establish `hn : ((n : K) + 1) ∈ R` using `R.add_mem (by simpa using R.natCast_mem n) R.one_mem`. Conclude with `R.mul_mem (hf (n + 1)) hn`.
-/
private theorem intPS_derivative' {K : Type} [Field K] {R : Subring K} {f : PowerSeries K}
    (hf : Formalism.L2.Th1.C.IntPS R f) : Formalism.L2.Th1.C.IntPS R (PowerSeries.derivative K f) := by
  intro n
  have h : PowerSeries.coeff n (PowerSeries.derivative K f) = PowerSeries.coeff (n + 1) f * (n + 1) := by
    first
      | exact PowerSeries.coeff_derivativeFun f n
      | (rw [PowerSeries.derivative_coe, PowerSeries.coeff_derivativeFun])
      | simp [PowerSeries.derivative]
  rw [h]
  have hn : ((n : K) + 1) ∈ R := R.add_mem (by simpa using R.natCast_mem n) R.one_mem
  exact R.mul_mem (hf (n + 1)) hn

/- English proof (translation)
Take `⟨h0, hI⟩` from `hu`. Establish `hmul : u * u⁻¹ = 1` using `PowerSeries.mul_inv_cancel u (by rw [h0]; exact one_ne_zero)`. Establish `h0' : PowerSeries.coeff 0 u = 1` using `by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`.

Consider the case `_ n ih`. Establish `hc` using `congrArg (PowerSeries.coeff n) hmul`. Establish `hs` using `Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)) (fun p : ℕ × ℕ => PowerSeries.coeff p.1 u * PowerSeries.coeff p.2 u⁻¹) (show ((0 : ℕ), n) ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)) from Finset.HasAntidiagonal.mem_antidiagonal.mpr (zer …`. Use `beta_reduce at hs`. Rewrite `hc` using `[PowerSeries.coeff_mul, ← hs, h0', one_mul]`.

Rewrite using `[eq_sub_of_add_eq hc]`. Use `R.sub_mem ?_ (R.sum_mem fun p hp => R.mul_mem (hI p.1) (ih p.2 ?_))` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_one] split_ifs exacts [R.one_mem, R.zero_mem]`. Establish `h1` using `Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_of_mem_erase hp)`. Establish `h2` using `Finset.ne_of_mem_erase hp`.

Break down `p with ⟨a, b⟩` into its components or cases. Simplify using `only at h1 ⊢`. Assume the negation of the conclusion as `hb`. Establish `ha : a = 0` using `by omega`. Establish `hb' : b = n` using `by omega`.

Conclude with `h2 (by rw [ha, hb'])`.
-/
private theorem intPS_inv_of_isOneUnit {K : Type} [Field K] {R : Subring K} {u : PowerSeries K}
    (hu : Formalism.L2.Th1.C.IsOneUnit R u) : Formalism.L2.Th1.C.IntPS R u⁻¹ := by
  obtain ⟨h0, hI⟩ := hu
  have hmul : u * u⁻¹ = 1 := PowerSeries.mul_inv_cancel u (by rw [h0]; exact one_ne_zero)
  have h0' : PowerSeries.coeff 0 u = 1 := by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (PowerSeries.coeff n) hmul
    have hs := Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ))
      (fun p : ℕ × ℕ => PowerSeries.coeff p.1 u * PowerSeries.coeff p.2 u⁻¹)
      (show ((0 : ℕ), n) ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)) from
        Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add n))
    beta_reduce at hs
    rw [PowerSeries.coeff_mul, ← hs, h0', one_mul] at hc
    rw [eq_sub_of_add_eq hc]
    refine R.sub_mem ?_ (R.sum_mem fun p hp => R.mul_mem (hI p.1) (ih p.2 ?_))
    · rw [PowerSeries.coeff_one]
      split_ifs
      exacts [R.one_mem, R.zero_mem]
    · have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_of_mem_erase hp)
      have h2 := Finset.ne_of_mem_erase hp
      rcases p with ⟨a, b⟩
      simp only at h1 ⊢
      by_contra hb
      have ha : a = 0 := by omega
      have hb' : b = n := by omega
      exact h2 (by rw [ha, hb'])

/- English proof (translation)
Introduce `K _ R l f hl hf i`. Establish `hu` using `intPS_inv_of_isOneUnit hl`. Establish `hit : ∀ j, Formalism.L2.Th1.C.IntPS R ((Formalism.L2.Th1.C.Dinv l)^[j] f)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => exact hf`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `intPS_mul_paired_square_jets hu (intPS_derivative' ih)`. Establish `h` using `hit i 0`.

Rewrite `h` using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `h`.
-/
theorem integral_dist_jets_holds : IntDJets := by
  intro K _ R l f hl hf i
  have hu := intPS_inv_of_isOneUnit hl
  have hit : ∀ j, Formalism.L2.Th1.C.IntPS R ((Formalism.L2.Th1.C.Dinv l)^[j] f) := by
    intro j
    induction j with
    | zero => exact hf
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact intPS_mul_paired_square_jets hu (intPS_derivative' ih)
  have h := hit i 0
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  exact h

/- English proof (translation)
Introduce `K _ _ R l linv hl hu n _ G hG`. Establish `hX : Formalism.L2.Th1.C.IntPS R (PowerSeries.X : PowerSeries K)`. Introduce `m`. Rewrite using `[PowerSeries.coeff_X]`. Use `split_ifs`.

Use `exacts [R.one_mem, R.zero_mem]`. Establish `hsl : PowerSeries.HasSubst linv` using `by first`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero hl.2.2.1`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero' hl.2.2.1`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero (by simpa using hl.2.2.1)`.

Establish `hlinv : JetsIn1 R linv`. Establish `h` using `(jets_of_dist_jets_holds K R l linv PowerSeries.X hl).mp (integral_dist_jets_holds K R l PowerSeries.X hu hX)`. Rewrite `h` using `[PowerSeries.subst_X hsl]`. Then use the resulting hypothesis. Establish `hXi : ∀ i : n, JetsIn R (MvPowerSeries.X i : MvPowerSeries n K)`. Introduce `i κ`.

Rewrite using `[MvPowerSeries.coeff_X]`. Use `split_ifs`. Rewrite using `[mul_one]`. Simplify using `using R.natCast_mem (mfact κ)`. Rewrite using `[mul_zero]`.

Conclude with `R.zero_mem`. Establish `hsX : ∀ i : n, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries n K)`. Introduce `i`. Use `first`. Consider the case `exact PowerSeries.HasSubst.X i`.

Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`. Consider the case `exact PowerSeries.HasSubst.of_constantCoeff_zero (by simp)`. Use `h1 K R n n G _ (h2 K R n G hG) (fun i => ?_) (fun i => ?_)` and prove the remaining obligations. Rewrite using `[PowerSeries.constantCoeff_subst (hsX i)]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `d`. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Simplify using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hl.2.2.1]`. Simplify using `[zero_pow hd.ne']`. Conclude with `h3 K R n linv (MvPowerSeries.X i) hlinv (MvPowerSeries.constantCoeff_X i) (hXi i)`.
-/
theorem IntMvZ_of (h1 : JetsSubst) (h2 : IntJets) (h3 : JetsSubstOne) (h4 : JetsRing) : IntMvZ := by
  intro K _ _ R l linv hl hu n _ G hG
  classical
  have hX : Formalism.L2.Th1.C.IntPS R (PowerSeries.X : PowerSeries K) := by
    intro m
    rw [PowerSeries.coeff_X]
    split_ifs
    exacts [R.one_mem, R.zero_mem]
  have hsl : PowerSeries.HasSubst linv := by
    first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero hl.2.2.1
      | exact PowerSeries.HasSubst.of_constantCoeff_zero' hl.2.2.1
      | exact PowerSeries.HasSubst.of_constantCoeff_zero (by simpa using hl.2.2.1)
  have hlinv : JetsIn1 R linv := by
    have h := (jets_of_dist_jets_holds K R l linv PowerSeries.X hl).mp (integral_dist_jets_holds K R l PowerSeries.X hu hX)
    rwa [PowerSeries.subst_X hsl] at h
  have hXi : ∀ i : n, JetsIn R (MvPowerSeries.X i : MvPowerSeries n K) := by
    intro i κ
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · rw [mul_one]
      simpa using R.natCast_mem (mfact κ)
    · rw [mul_zero]
      exact R.zero_mem
  have hsX : ∀ i : n, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries n K) := by
    intro i
    first
      | exact PowerSeries.HasSubst.X i
      | exact PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
      | exact PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  refine h1 K R n n G _ (h2 K R n G hG) (fun i => ?_) (fun i => ?_)
  · rw [PowerSeries.constantCoeff_subst (hsX i)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl.2.2.1]
    · simp [zero_pow hd.ne']
  · exact h3 K R n linv (MvPowerSeries.X i) hlinv (MvPowerSeries.constantCoeff_X i) (hXi i)

end Formalism.L2.Th1.G
