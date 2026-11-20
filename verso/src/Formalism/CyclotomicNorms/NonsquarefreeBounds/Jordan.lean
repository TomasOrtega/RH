import Formalism.CyclotomicNorms.StatementI
import Formalism.GaloisIrreducibility.NoSolvableTransitive

open Finset

namespace Formalism.CyclotomicNorms

/- English proof (translation)
Unfold `BlocksCycle`. Introduce `G Ω _ _ _ _ B m p g₀ hsize hdisj hcover hinv hp hlt hcyc hsupp`. Establish `hpow : ∀ (i : ℕ) (y : Ω), ((MulAction.toPerm g₀ : Equiv.Perm Ω) ^ i) y = g₀ ^ i • y`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro y`. Simplify using the standard rewrite rules. Consider the case `succ i ih => intro y`. Simplify using `[pow_succ, mul_smul, ih]`. Establish `hord : orderOf (MulAction.toPerm g₀ : Equiv.Perm Ω) = p`.

Rewrite using `[hcyc.orderOf, hsupp]`. Establish `hfix : ∀ y : Ω, g₀ ^ p • y = y`. Introduce `y`. Establish `h1` using `pow_orderOf_eq_one (MulAction.toPerm g₀ : Equiv.Perm Ω)`. Rewrite `h1` using `[hord]`.

Rewrite using `[← hpow]`. Simplify using `[h1]`. Take `⟨φ, hφdef⟩ : ∃ φ : Finset Ω → Finset Ω, ∀ s, φ s = s.image (fun x => g₀ • x)` from `⟨fun s => s.image (fun x => g₀ • x), fun _ => rfl⟩`. Establish `hφ : ∀ (i : ℕ) (s : Finset Ω), φ^[i] s = s.image (fun x => g₀ ^ i • x)`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => intro s`. Simplify using the standard rewrite rules. Consider the case `succ i ih`. Introduce `s`.

Rewrite using `[Function.iterate_succ_apply', ih, hφdef, Finset.image_image]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [Function.comp_apply, pow_succ', mul_smul]`. Establish `hφB : ∀ (i : ℕ), ∀ s ∈ B, φ^[i] s ∈ B`.

Introduce `i s hs`. Rewrite using `[hφ]`. Conclude with `hinv (g₀ ^ i) s hs`. Establish `hper : ∀ s : Finset Ω, φ^[p] s = s`. Introduce `s`.

Rewrite using `[hφ]`. Simplify using `[hfix]`. Establish `hp2` using `hp.two_le`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : (MulAction.toPerm g₀ : Equiv.Perm Ω).support.Nonempty := by`. Rewrite using `[← Finset.card_pos, hsupp]`.

Use linear arithmetic over natural numbers and integers. Take `⟨b, hbB, hxb⟩` from `hcover x`. Establish `hcard : Fintype.card Ω = B.card * m`. Establish `hU : B.biUnion (fun c => c) = Finset.univ`. Use extensionality with `y`.

Simplify using `only [Finset.mem_biUnion, Finset.mem_univ, iff_true]`. Take `⟨c, hc, hyc⟩` from `hcover y`. Conclude with `⟨c, hc, hyc⟩`. Rewrite using `[← Finset.card_univ, ← hU, Finset.card_biUnion (fun c hc c' hc' hne => hdisj c hc c' hc' hne)]`. Conclude with `Finset.sum_const_nat hsize`.

Establish `hmp : Function.minimalPeriod φ b ∣ p` using `Function.IsPeriodicPt.minimalPeriod_dvd (hper b)`. Break down `(Nat.dvd_prime hp).1 hmp with h1 | hpp` into its components or cases. Use `left`. Establish `hfixb : φ b = b` using `Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1`. Establish `hsub : (MulAction.toPerm g₀ : Equiv.Perm Ω).support ⊆ b`.

Introduce `y hy`. Take `⟨i, hi⟩` from `hcyc.exists_pow_eq (Equiv.Perm.mem_support.1 hx) (Equiv.Perm.mem_support.1 hy)`. Establish `hib : φ^[i] b = b` using `Function.iterate_fixed hfixb i`. Rewrite using `[← hi, hpow, ← hib, hφ]`. Conclude with `Finset.mem_image_of_mem _ hxb`.

Establish `hpm : p ≤ m`. Rewrite using `[← hsupp, ← hsize b hbB]`. Conclude with `Finset.card_le_card hsub`. Establish `hk1 : 1 ≤ B.card` using `Finset.card_pos.2 ⟨b, hbB⟩`. Assume the negation of the conclusion as `hne`.

Establish `hk2 : 2 ≤ B.card` using `by omega`. Establish `h2` using `Nat.mul_le_mul hk2 hpm`. Combine the linear equalities and inequalities to obtain the conclusion. Use `right`. Establish `hinj : Set.InjOn (fun n => φ^[n] b) (Finset.range p : Set ℕ)`.

Rewrite using `[Finset.coe_range, ← hpp]`. Conclude with `Function.iterate_injOn_Iio_minimalPeriod`. Establish `hkp : p ≤ B.card`. Establish `h1 : ((Finset.range p).image (fun n => φ^[n] b)) ⊆ B`. Introduce `c hc`.

Take `⟨n, -, rfl⟩` from `Finset.mem_image.1 hc`. Conclude with `hφB n b hbB`. Establish `h2` using `Finset.card_le_card h1`. Rewrite `h2` using `[Finset.card_image_of_injOn hinj, Finset.card_range]`. Then use the resulting hypothesis. Establish `hm1 : 1 ≤ m`.

Rewrite using `[← hsize b hbB]`. Conclude with `Finset.card_pos.2 ⟨x, hxb⟩`. Establish `hm : m = 1`. Assume the negation of the conclusion as `hne`. Establish `hm2 : 2 ≤ m` using `by omega`.

Establish `h3` using `Nat.mul_le_mul hkp hm2`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hcard, hm, mul_one]`.
-/
theorem blocks_form_cycle : BlocksCycle := by
  unfold BlocksCycle
  intro G Ω _ _ _ _ B m p g₀ hsize hdisj hcover hinv hp hlt hcyc hsupp
  have hpow : ∀ (i : ℕ) (y : Ω), ((MulAction.toPerm g₀ : Equiv.Perm Ω) ^ i) y = g₀ ^ i • y := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih => intro y; simp [pow_succ, mul_smul, ih]
  have hord : orderOf (MulAction.toPerm g₀ : Equiv.Perm Ω) = p := by
    rw [hcyc.orderOf, hsupp]
  have hfix : ∀ y : Ω, g₀ ^ p • y = y := by
    intro y
    have h1 := pow_orderOf_eq_one (MulAction.toPerm g₀ : Equiv.Perm Ω)
    rw [hord] at h1
    rw [← hpow]
    simp [h1]
  obtain ⟨φ, hφdef⟩ : ∃ φ : Finset Ω → Finset Ω, ∀ s, φ s = s.image (fun x => g₀ • x) :=
    ⟨fun s => s.image (fun x => g₀ • x), fun _ => rfl⟩
  have hφ : ∀ (i : ℕ) (s : Finset Ω), φ^[i] s = s.image (fun x => g₀ ^ i • x) := by
    intro i
    induction i with
    | zero => intro s; simp
    | succ i ih =>
      intro s
      rw [Function.iterate_succ_apply', ih, hφdef, Finset.image_image]
      congr 1
      funext y
      simp only [Function.comp_apply, pow_succ', mul_smul]
  have hφB : ∀ (i : ℕ), ∀ s ∈ B, φ^[i] s ∈ B := by
    intro i s hs
    rw [hφ]
    exact hinv (g₀ ^ i) s hs
  have hper : ∀ s : Finset Ω, φ^[p] s = s := by
    intro s
    rw [hφ]
    simp [hfix]
  have hp2 := hp.two_le
  obtain ⟨x, hx⟩ : (MulAction.toPerm g₀ : Equiv.Perm Ω).support.Nonempty := by
    rw [← Finset.card_pos, hsupp]
    omega
  obtain ⟨b, hbB, hxb⟩ := hcover x
  have hcard : Fintype.card Ω = B.card * m := by
    have hU : B.biUnion (fun c => c) = Finset.univ := by
      ext y
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
      obtain ⟨c, hc, hyc⟩ := hcover y
      exact ⟨c, hc, hyc⟩
    rw [← Finset.card_univ, ← hU, Finset.card_biUnion (fun c hc c' hc' hne => hdisj c hc c' hc' hne)]
    exact Finset.sum_const_nat hsize
  have hmp : Function.minimalPeriod φ b ∣ p :=
    Function.IsPeriodicPt.minimalPeriod_dvd (hper b)
  rcases (Nat.dvd_prime hp).1 hmp with h1 | hpp
  · left
    have hfixb : φ b = b := Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1
    have hsub : (MulAction.toPerm g₀ : Equiv.Perm Ω).support ⊆ b := by
      intro y hy
      obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (Equiv.Perm.mem_support.1 hx) (Equiv.Perm.mem_support.1 hy)
      have hib : φ^[i] b = b := Function.iterate_fixed hfixb i
      rw [← hi, hpow, ← hib, hφ]
      exact Finset.mem_image_of_mem _ hxb
    have hpm : p ≤ m := by
      rw [← hsupp, ← hsize b hbB]
      exact Finset.card_le_card hsub
    have hk1 : 1 ≤ B.card := Finset.card_pos.2 ⟨b, hbB⟩
    by_contra hne
    have hk2 : 2 ≤ B.card := by omega
    have h2 := Nat.mul_le_mul hk2 hpm
    linarith
  · right
    have hinj : Set.InjOn (fun n => φ^[n] b) (Finset.range p : Set ℕ) := by
      rw [Finset.coe_range, ← hpp]
      exact Function.iterate_injOn_Iio_minimalPeriod
    have hkp : p ≤ B.card := by
      have h1 : ((Finset.range p).image (fun n => φ^[n] b)) ⊆ B := by
        intro c hc
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hc
        exact hφB n b hbB
      have h2 := Finset.card_le_card h1
      rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at h2
    have hm1 : 1 ≤ m := by
      rw [← hsize b hbB]
      exact Finset.card_pos.2 ⟨x, hxb⟩
    have hm : m = 1 := by
      by_contra hne
      have hm2 : 2 ≤ m := by omega
      have h3 := Nat.mul_le_mul hkp hm2
      linarith
    rw [hcard, hm, mul_one]

/- English proof (translation)
Introduce `G Ω _ _ _ _ p g₀ htr hp hlt hle hcyc hsupp`. Use `set K : Subgroup (Equiv.Perm Ω) := (MulAction.toPermHom G Ω).range with hK`. Use `set σ : Equiv.Perm Ω := MulAction.toPerm g₀ with hσ`. Establish `hσK : σ ∈ K` using `⟨g₀, rfl⟩`. Establish `htrK : MulAction.IsPretransitive K Ω`.

Prove the components needed by the constructor for the conclusion. Introduce `x y`. Take `⟨g, hg⟩` from `htr.exists_smul_eq x y`. Conclude with `⟨⟨MulAction.toPermHom G Ω g, ⟨g, rfl⟩⟩, hg⟩`. Establish `hprim : MulAction.IsPreprimitive K Ω` using `Formalism.GaloisIrreducibility.primitiveOfPCycle Ω K σ p hp hσK hcyc hsupp hlt htrK`.

Establish `halt : alternatingGroup Ω ≤ K` using `Formalism.GaloisIrreducibility.jordanPrime Ω K σ p hp hσK hcyc hsupp hle hprim`. Use `⟨halt, ?_⟩` and prove the remaining obligations. Establish `hpc : p ∈ σ.cycleType`. Rewrite using `[hcyc.cycleType, hsupp]`. Simplify using the standard rewrite rules.

Establish `hns : ¬ Group.IsSolvable K` using `Formalism.GaloisIrreducibility.noSolvableTransitive Ω K σ p hp hσK hpc hlt hle htrK`. Introduce `hG`. Conclude with `hns (Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (MulAction.toPermHom G Ω)))`.
-/
theorem jordan_transitivity : JordanTransitive := by
  intro G Ω _ _ _ _ p g₀ htr hp hlt hle hcyc hsupp
  set K : Subgroup (Equiv.Perm Ω) := (MulAction.toPermHom G Ω).range with hK
  set σ : Equiv.Perm Ω := MulAction.toPerm g₀ with hσ
  have hσK : σ ∈ K := ⟨g₀, rfl⟩
  have htrK : MulAction.IsPretransitive K Ω := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := htr.exists_smul_eq x y
    exact ⟨⟨MulAction.toPermHom G Ω g, ⟨g, rfl⟩⟩, hg⟩
  have hprim : MulAction.IsPreprimitive K Ω :=
    Formalism.GaloisIrreducibility.primitiveOfPCycle Ω K σ p hp hσK hcyc hsupp hlt htrK
  have halt : alternatingGroup Ω ≤ K :=
    Formalism.GaloisIrreducibility.jordanPrime Ω K σ p hp hσK hcyc hsupp hle hprim
  refine ⟨halt, ?_⟩
  have hpc : p ∈ σ.cycleType := by
    rw [hcyc.cycleType, hsupp]
    simp
  have hns : ¬ Group.IsSolvable K :=
    Formalism.GaloisIrreducibility.noSolvableTransitive Ω K σ p hp hσK hpc hlt hle htrK
  intro hG
  exact hns (Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (MulAction.toPermHom G Ω)))

end Formalism.CyclotomicNorms
