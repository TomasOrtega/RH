import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LatticeSumDilateHaarAsymptoticStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.IdealSum

/- English proof (translation)
Establish `hco : IsCoprime b m` using `Ideal.isCoprime_iff_sup_eq.2 hbm`. Establish `hl : ∀ x ∈ b * m, x ∈ b` using `fun x hx => (Ideal.mul_le_inf hx).1`. Establish `hr : ∀ x ∈ b * m, x ∈ m` using `fun x hx => (Ideal.mul_le_inf hx).2`. Take `⟨φ, hval⟩ : ∃ φ : (R ⧸ m) × ↥(b * m) → b, ∀ p, (φ p).1 = p.2.1 + s p.1` from `⟨fun p => ⟨p.2.1 + s p.1, b.add_mem (hl _ p.2.2) (hsb _)⟩, fun _ => rfl⟩`. Establish `hφ : Function.Bijective φ`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, β⟩ ⟨r', β'⟩ h`. Establish `h1 : (β : R) + s r = β' + s r'`. Establish `h0` using `congrArg Subtype.val h`. Rewrite `h0` using `[hval, hval]`. Then use the resulting hypothesis.

Establish `h2` using `congrArg (Ideal.Quotient.mk m) h1`. Establish `hβ : Ideal.Quotient.mk m (β : R) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (hr _ β.2)`. Establish `hβ' : Ideal.Quotient.mk m (β' : R) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (hr _ β'.2)`. Rewrite `h2` using `[map_add, map_add, hs, hs, hβ, hβ', zero_add, zero_add]`. Substitute `h2` using the available equality.

Rewrite using `[Subtype.ext (add_right_cancel h1)]`. Introduce and unpack `⟨a, ha⟩`. Establish `hmem : a - s (Ideal.Quotient.mk m a) ∈ b * m`. Rewrite using `[Ideal.mul_eq_inf_of_isCoprime hco]`. Conclude with `Ideal.mem_inf.2 ⟨b.sub_mem ha (hsb _), Ideal.Quotient.eq.1 (hs _).symm⟩`.

Use `⟨(Ideal.Quotient.mk m a, ⟨a - s (Ideal.Quotient.mk m a), hmem⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Conclude with `sub_add_cancel _ _`. Establish `h1 : ∑' p, ψ (φ p) * g (φ p) = ∑' α : b, ψ α * g α` using `(Equiv.ofBijective φ hφ).tsum_eq (fun α : b => ψ α * g α)`. Establish `h2 : Summable fun p => ψ (φ p) * g (φ p)` using `hg.comp_injective hφ.1`.

Establish `h3 : ∑' p, ψ (φ p) * g (φ p) = ∑' r, ∑' β, ψ (φ (r, β)) * g (φ (r, β))` using `h2.tsum_prod`. Rewrite using `[← h1, h3, tsum_fintype]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun β => ?_` and prove the remaining obligations.

Rewrite using `[hval]`. Rewrite using `[hψ ((β : R) + s r) (s r) (by rw [add_sub_cancel_right]; exact hr _ β.2)]`.
-/
theorem tsum_ideal_eq_sum_classes {R : Type} [CommRing R] (m b : Ideal R) [Fintype (R ⧸ m)]
    (hbm : b ⊔ m = ⊤) (s : R ⧸ m → R) (hsb : ∀ r, s r ∈ b)
    (hs : ∀ r, Ideal.Quotient.mk m (s r) = r) (ψ g : R → ℂ)
    (hψ : ∀ a b, a - b ∈ m → ψ a = ψ b) (hg : Summable fun α : b => ψ α * g α) :
    ∑' α : b, ψ α * g α = ∑ r : R ⧸ m, ψ (s r) * ∑' β : ↥(b * m), g ((β : R) + s r) := by
  have hco : IsCoprime b m := Ideal.isCoprime_iff_sup_eq.2 hbm
  have hl : ∀ x ∈ b * m, x ∈ b := fun x hx => (Ideal.mul_le_inf hx).1
  have hr : ∀ x ∈ b * m, x ∈ m := fun x hx => (Ideal.mul_le_inf hx).2
  obtain ⟨φ, hval⟩ : ∃ φ : (R ⧸ m) × ↥(b * m) → b, ∀ p, (φ p).1 = p.2.1 + s p.1 :=
    ⟨fun p => ⟨p.2.1 + s p.1, b.add_mem (hl _ p.2.2) (hsb _)⟩, fun _ => rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨r, β⟩ ⟨r', β'⟩ h
      have h1 : (β : R) + s r = β' + s r' := by
        have h0 := congrArg Subtype.val h
        rwa [hval, hval] at h0
      have h2 := congrArg (Ideal.Quotient.mk m) h1
      have hβ : Ideal.Quotient.mk m (β : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hr _ β.2)
      have hβ' : Ideal.Quotient.mk m (β' : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hr _ β'.2)
      rw [map_add, map_add, hs, hs, hβ, hβ', zero_add, zero_add] at h2
      subst h2
      rw [Subtype.ext (add_right_cancel h1)]
    · rintro ⟨a, ha⟩
      have hmem : a - s (Ideal.Quotient.mk m a) ∈ b * m := by
        rw [Ideal.mul_eq_inf_of_isCoprime hco]
        exact Ideal.mem_inf.2 ⟨b.sub_mem ha (hsb _), Ideal.Quotient.eq.1 (hs _).symm⟩
      refine ⟨(Ideal.Quotient.mk m a, ⟨a - s (Ideal.Quotient.mk m a), hmem⟩), Subtype.ext ?_⟩
      rw [hval]
      exact sub_add_cancel _ _
  have h1 : ∑' p, ψ (φ p) * g (φ p) = ∑' α : b, ψ α * g α :=
    (Equiv.ofBijective φ hφ).tsum_eq (fun α : b => ψ α * g α)
  have h2 : Summable fun p => ψ (φ p) * g (φ p) := hg.comp_injective hφ.1
  have h3 : ∑' p, ψ (φ p) * g (φ p) = ∑' r, ∑' β, ψ (φ (r, β)) * g (φ (r, β)) :=
    h2.tsum_prod
  rw [← h1, h3, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun β => ?_
  rw [hval]
  rw [hψ ((β : R) + s r) (s r) (by rw [add_sub_cancel_right]; exact hr _ β.2)]

/- English proof (translation)
Take `⟨r, hr⟩` from `(Metric.isBounded_iff_subset_closedBall (0 : mixedSpace K)).1 hf.isCompact.isBounded`. Set `I` to `FractionalIdeal.mk0 K (1 : (Ideal (𝓞 K))⁰)`. Establish `hd : DiscreteTopology (idealLattice K I).toAddSubgroup` using `inferInstanceAs (DiscreteTopology (idealLattice K I))`. Establish `hfin : (Metric.closedBall (0 : mixedSpace K) (r / t) ∩ (idealLattice K I : Set (mixedSpace K))).Finite` using `Metric.finite_isBounded_inter_isClosed (isDiscrete_iff_discreteTopology.2 hd) Metric.isBounded_closedBall (AddSubgroup.isClosed_of_discrete (H := (idealLattice K I).toAddSubgroup))`. Establish `hinj : Function.Injective fun α : 𝓞 K => mixedEmbedding K (α : K)` using `(mixedEmbedding_injective K).comp RingOfIntegers.coe_injective`.

Use `(hfin.preimage hinj.injOn).subset fun α hα => ⟨?_, ?_⟩` and prove the remaining obligations. Use `hr (subset_tsupport f hα)` as an intermediate fact. Rewrite `this` using `[mem_closedBall_zero_iff, _root_.norm_smul, Real.norm_of_nonneg ht.le]`. Rewrite using `[mem_closedBall_zero_iff, le_div_iff₀ ht, mul_comm]`. Conclude with `this`.

Use `(mem_idealLattice K I).2 ⟨(α : K), ?_, rfl⟩` and prove the remaining obligations. Simplify using `[I]`.
-/
theorem finite_support_dilate (K : Type) [Field K] [NumberField K] (f : mixedSpace K → ℂ)
    (hf : HasCompactSupport f) (t : ℝ) (ht : 0 < t) :
    {α : 𝓞 K | f (t • mixedEmbedding K (α : K)) ≠ 0}.Finite := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : mixedSpace K)).1
    hf.isCompact.isBounded
  let I := FractionalIdeal.mk0 K (1 : (Ideal (𝓞 K))⁰)
  have hd : DiscreteTopology (idealLattice K I).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (idealLattice K I))
  have hfin : (Metric.closedBall (0 : mixedSpace K) (r / t) ∩
      (idealLattice K I : Set (mixedSpace K))).Finite :=
    Metric.finite_isBounded_inter_isClosed
      (isDiscrete_iff_discreteTopology.2 hd)
      Metric.isBounded_closedBall
      (AddSubgroup.isClosed_of_discrete (H := (idealLattice K I).toAddSubgroup))
  have hinj : Function.Injective fun α : 𝓞 K => mixedEmbedding K (α : K) :=
    (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective
  refine (hfin.preimage hinj.injOn).subset fun α hα => ⟨?_, ?_⟩
  · have := hr (subset_tsupport f hα)
    rw [mem_closedBall_zero_iff, _root_.norm_smul, Real.norm_of_nonneg ht.le] at this
    rw [mem_closedBall_zero_iff, le_div_iff₀ ht, mul_comm]
    exact this
  · refine (mem_idealLattice K I).2 ⟨(α : K), ?_, rfl⟩
    simp [I]

/- English proof (translation)
Set `φ : ↥(J.1) → idealLattice K (FractionalIdeal.mk0 K J)` to `fun β => ⟨mixedEmbedding K ((β : 𝓞 K) : K), (mem_idealLattice K _).2 ⟨((β : 𝓞 K) : K), by`. Rewrite using `[FractionalIdeal.coe_mk0]`. Conclude with `FractionalIdeal.mem_coeIdeal_of_mem _ β.2, rfl⟩⟩`. Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion.

Introduce `a b h`. Conclude with `Subtype.ext (RingOfIntegers.coe_injective (mixedEmbedding_injective K (congrArg Subtype.val h)))`. Introduce and unpack `⟨l, hl⟩`. Take `⟨y, hy, rfl⟩` from `(mem_idealLattice K _).1 hl`. Rewrite `hy` using `[FractionalIdeal.coe_mk0]`.

Take `⟨x, hx, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hy`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Conclude with `((Equiv.ofBijective φ hφ).tsum_eq (fun l => F l)).symm`.
-/
theorem tsum_idealLattice (K : Type) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰)
    (F : mixedSpace K → ℂ) :
    ∑' l : idealLattice K (FractionalIdeal.mk0 K J), F l =
      ∑' β : ↥(J.1), F (mixedEmbedding K ((β : 𝓞 K) : K)) := by
  let φ : ↥(J.1) → idealLattice K (FractionalIdeal.mk0 K J) := fun β =>
    ⟨mixedEmbedding K ((β : 𝓞 K) : K), (mem_idealLattice K _).2 ⟨((β : 𝓞 K) : K), by
      rw [FractionalIdeal.coe_mk0]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ β.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      exact Subtype.ext (RingOfIntegers.coe_injective
        (mixedEmbedding_injective K (congrArg Subtype.val h)))
    · rintro ⟨l, hl⟩
      obtain ⟨y, hy, rfl⟩ := (mem_idealLattice K _).1 hl
      rw [FractionalIdeal.coe_mk0] at hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      exact ⟨⟨x, hx⟩, rfl⟩
  exact ((Equiv.ofBijective φ hφ).tsum_eq (fun l => F l)).symm

/- English proof (translation)
Introduce `K _ _ m ψ f hm hψ hf hfc`. Use `haveI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm`. Use `haveI : Fintype (𝓞 K ⧸ m) := Fintype.ofFinite _`. Use `set D : ℝ := 2⁻¹ ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)| with hD`. Use `⟨(∑ r : 𝓞 K ⧸ m, ψ (Quotient.out r)) * (∫ x, f x) / (((Ideal.absNorm m : ℝ) * D : ℝ) : ℂ), fun b hb hbm A => ?_⟩` and prove the remaining obligations.

Establish `hrep : ∀ r : 𝓞 K ⧸ m, ∃ x ∈ b, Ideal.Quotient.mk m x = r`. Introduce `r`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 (hbm ▸ Submodule.mem_top : a ∈ b ⊔ m)`. Conclude with `⟨x, hx, by rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hy, add_zero]⟩`.

Use `choose s hsb hs using hrep`. Set `J : (Ideal (𝓞 K))⁰` to `⟨b * m, mem_nonZeroDivisors_iff_ne_zero.2 (mul_ne_zero hb hm)⟩`. Take `⟨C, hC⟩` from `GlobalTheory.T.lattice_sum_dilate_haar_asymptotic (mixedSpace K) volume (idealLattice K (FractionalIdeal.mk0 K J)) f hf hfc A`. Use `⟨(∑ r : 𝓞 K ⧸ m, ‖ψ (s r)‖) * C, fun t ht ht1 => ?_⟩` and prove the remaining obligations. Establish `hsum : Summable fun α : b => ψ α * f (t • mixedEmbedding K ((α : 𝓞 K) : K))`.

Use `summable_of_finite_support ?_` and prove the remaining obligations. Use `((finite_support_dilate K f hfc t ht).preimage (Subtype.val_injective (p := fun x => x ∈ b)).injOn).subset fun α hα => ?_` and prove the remaining obligations. Conclude with `right_ne_zero_of_mul hα`. Rewrite using `[tsum_ideal_eq_sum_classes m b hbm s hsb hs ψ (fun α => f (t • mixedEmbedding K (α : K))) hψ hsum]`. Establish `hout : ∀ r : 𝓞 K ⧸ m, ψ (Quotient.out r) = ψ (s r)` using `fun r => hψ _ _ (Ideal.Quotient.eq.1 ((Ideal.Quotient.mk_out r).trans (hs r).symm))`.

Establish `hcov : ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume = (Ideal.absNorm b : ℝ) * ((Ideal.absNorm m : ℝ) * D)`. Rewrite using `[covolume_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, hD]`. Simplify using `only [J, map_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : (∑ r : 𝓞 K ⧸ m, ψ (Quotient.out r)) * (∫ x, f x) / (((Ideal.absNorm m : ℝ) * D : ℝ) : ℂ) / (((Ideal.absNorm b : ℝ) * t ^ Module.finrank ℚ K : ℝ) : ℂ) = ∑ r : 𝓞 K ⧸ m, ψ (s r) * ((∫ x, f x) / ((ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume * t ^ Module. …`. Rewrite using `[← Finset.sum_mul, hcov, mixedEmbedding.finrank, div_div, mul_div_assoc]`. Simplify using `only [hout]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]`. Use `norm_sum_le_of_le _ fun r _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub, norm_mul, mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations.

Establish `h` using `hC (mixedEmbedding K (s r : K)) t ht ht1`. Rewrite `h` using `[tsum_idealLattice K J (fun l => f (t • (l + mixedEmbedding K (s r : K))))]`. Establish `hβ : ∀ β : ↥(b * m), mixedEmbedding K (((β : 𝓞 K) + s r : 𝓞 K) : K) = mixedEmbedding K ((β : 𝓞 K) : K) + mixedEmbedding K (s r : K)` using `fun β => by`. Rewrite using `[← map_add]`. Both sides reduce to the same expression.

Simplify using `only [hβ]`. Conclude with `h`.
-/
theorem ideal_sum_periodic_dilate : ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (ψ : 𝓞 K → ℂ) (f : mixedSpace K → ℂ), m ≠ ⊥ → (∀ a b, a - b ∈ m → ψ a = ψ b) → ContDiff ℝ ∞ f → HasCompactSupport f → ∃ κ : ℂ, ∀ b : Ideal (𝓞 K), b ≠ ⊥ → b ⊔ m = ⊤ → ∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' α : b, ψ α * f (t • mixedEmbedding K ((α : 𝓞 K) : K)) - κ / (((Ideal.absNorm b : ℝ) * t ^ Module.finrank ℚ K : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  intro K _ _ m ψ f hm hψ hf hfc
  haveI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm
  haveI : Fintype (𝓞 K ⧸ m) := Fintype.ofFinite _
  set D : ℝ := 2⁻¹ ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)| with hD
  refine ⟨(∑ r : 𝓞 K ⧸ m, ψ (Quotient.out r)) * (∫ x, f x) /
    (((Ideal.absNorm m : ℝ) * D : ℝ) : ℂ), fun b hb hbm A => ?_⟩
  have hrep : ∀ r : 𝓞 K ⧸ m, ∃ x ∈ b, Ideal.Quotient.mk m x = r := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (hbm ▸ Submodule.mem_top : a ∈ b ⊔ m)
    exact ⟨x, hx, by rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hy, add_zero]⟩
  choose s hsb hs using hrep
  let J : (Ideal (𝓞 K))⁰ := ⟨b * m, mem_nonZeroDivisors_iff_ne_zero.2 (mul_ne_zero hb hm)⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.lattice_sum_dilate_haar_asymptotic (mixedSpace K) volume
    (idealLattice K (FractionalIdeal.mk0 K J)) f hf hfc A
  refine ⟨(∑ r : 𝓞 K ⧸ m, ‖ψ (s r)‖) * C, fun t ht ht1 => ?_⟩
  have hsum : Summable fun α : b => ψ α * f (t • mixedEmbedding K ((α : 𝓞 K) : K)) := by
    refine summable_of_finite_support ?_
    refine ((finite_support_dilate K f hfc t ht).preimage
      (Subtype.val_injective (p := fun x => x ∈ b)).injOn).subset fun α hα => ?_
    exact right_ne_zero_of_mul hα
  rw [tsum_ideal_eq_sum_classes m b hbm s hsb hs ψ
    (fun α => f (t • mixedEmbedding K (α : K))) hψ hsum]
  have hout : ∀ r : 𝓞 K ⧸ m, ψ (Quotient.out r) = ψ (s r) := fun r =>
    hψ _ _ (Ideal.Quotient.eq.1 ((Ideal.Quotient.mk_out r).trans (hs r).symm))
  have hcov : ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume =
      (Ideal.absNorm b : ℝ) * ((Ideal.absNorm m : ℝ) * D) := by
    rw [covolume_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, hD]
    simp only [J, map_mul]
    push_cast
    ring
  have key : (∑ r : 𝓞 K ⧸ m, ψ (Quotient.out r)) * (∫ x, f x) /
      (((Ideal.absNorm m : ℝ) * D : ℝ) : ℂ) /
      (((Ideal.absNorm b : ℝ) * t ^ Module.finrank ℚ K : ℝ) : ℂ) =
      ∑ r : 𝓞 K ⧸ m, ψ (s r) * ((∫ x, f x) /
        ((ZLattice.covolume (idealLattice K (FractionalIdeal.mk0 K J)) volume *
          t ^ Module.finrank ℝ (mixedSpace K) : ℝ) : ℂ)) := by
    rw [← Finset.sum_mul, hcov, mixedEmbedding.finrank, div_div, mul_div_assoc]
    simp only [hout]
    congr 2
    push_cast
    ring
  rw [key, ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun r _ => ?_
  rw [← mul_sub, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := hC (mixedEmbedding K (s r : K)) t ht ht1
  rw [tsum_idealLattice K J (fun l => f (t • (l + mixedEmbedding K (s r : K))))] at h
  have hβ : ∀ β : ↥(b * m), mixedEmbedding K (((β : 𝓞 K) + s r : 𝓞 K) : K) =
      mixedEmbedding K ((β : 𝓞 K) : K) + mixedEmbedding K (s r : K) := fun β => by
    rw [← map_add]
    rfl
  simp only [hβ]
  exact h

end GlobalTheory.IdealSum
