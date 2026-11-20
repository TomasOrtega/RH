import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing UpperTheory.V UpperTheory.V.Alg

/- English proof (translation)
Use `haveI := Fintype.ofFinite (ResidueField O)`. Use `set q := Nat.card (ResidueField O) with hq`. Establish `hq2 : 2 ≤ q`. Rewrite using `[hq, Nat.card_eq_fintype_card]`. Conclude with `Fintype.one_lt_card`.

Establish `hk : (q : ResidueField O) = 0`. Rewrite using `[hq, Nat.card_eq_fintype_card]`. Conclude with `FiniteField.cast_card_eq_zero _`. Use `set s := ∑ i ∈ Finset.range (q - 1), a ^ i * c ^ (q - 1 - 1 - i) with hs`. Establish `hmul : s * (a - c) = a ^ (q - 1) - c ^ (q - 1)` using `geom_sum₂_mul a c (q - 1)`.

Establish `hterm : ∀ i ∈ Finset.range (q - 1), res O R a ^ i * res O R a ^ (q - 1 - 1 - i) = res O R a ^ (q - 1 - 1)`. Introduce `i hi`. Rewrite using `[← pow_add]`. Use `congr 1`. Use `Finset.mem_range.1 hi` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hres : res O R s = ((q - 1 : ℕ) : ResidueField O) * res O R a ^ (q - 1 - 1)`. Rewrite using `[hs, map_sum]`. Simplify using `only [map_mul, map_pow, ← h]`. Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`.

Establish `hcast : ((q - 1 : ℕ) : ResidueField O) = -1`. Rewrite using `[Nat.cast_sub (by omega), hk]`. Simplify using the standard rewrite rules. Establish `hua : res O R a ≠ 0`. Introduce `h0`.

Rewrite `h0` using `[res_eq_zero_iff]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h0 ha`. Establish `hsu : IsUnit s`. Assume the negation of the conclusion as `hn`. Establish `hm : s ∈ maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal _).2 hn`.

Rewrite `hm` using `[← res_eq_zero_iff O R, hres, hcast, neg_one_mul, neg_eq_zero]`. Conclude with `pow_ne_zero _ hua hm`. Take `⟨u, hu⟩` from `hsu`. Establish `he : a - c = ((u⁻¹ : Rˣ) : R) * (a ^ (q - 1) - c ^ (q - 1))`. Rewrite using `[← hmul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]`.

Rewrite using `[he]`. Conclude with `P.mul_mem_left _ hp`.
-/
private theorem flo_sub_mem {O R : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R]
    [Algebra O R] [IsCO O R] (P : Ideal R) (a c : R) (h : res O R a = res O R c) (ha : IsUnit a)
    (hp : a ^ (Nat.card (ResidueField O) - 1) - c ^ (Nat.card (ResidueField O) - 1) ∈ P) : a - c ∈ P := by
  classical
  haveI := Fintype.ofFinite (ResidueField O)
  set q := Nat.card (ResidueField O) with hq
  have hq2 : 2 ≤ q := by
    rw [hq, Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hk : (q : ResidueField O) = 0 := by
    rw [hq, Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  set s := ∑ i ∈ Finset.range (q - 1), a ^ i * c ^ (q - 1 - 1 - i) with hs
  have hmul : s * (a - c) = a ^ (q - 1) - c ^ (q - 1) := geom_sum₂_mul a c (q - 1)
  have hterm : ∀ i ∈ Finset.range (q - 1),
      res O R a ^ i * res O R a ^ (q - 1 - 1 - i) = res O R a ^ (q - 1 - 1) := by
    intro i hi
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.1 hi
    omega
  have hres : res O R s = ((q - 1 : ℕ) : ResidueField O) * res O R a ^ (q - 1 - 1) := by
    rw [hs, map_sum]
    simp only [map_mul, map_pow, ← h]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcast : ((q - 1 : ℕ) : ResidueField O) = -1 := by
    rw [Nat.cast_sub (by omega), hk]
    simp
  have hua : res O R a ≠ 0 := by
    intro h0
    rw [res_eq_zero_iff] at h0
    exact (IsLocalRing.mem_maximalIdeal _).1 h0 ha
  have hsu : IsUnit s := by
    by_contra hn
    have hm : s ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [← res_eq_zero_iff O R, hres, hcast, neg_one_mul, neg_eq_zero] at hm
    exact pow_ne_zero _ hua hm
  obtain ⟨u, hu⟩ := hsu
  have he : a - c = ((u⁻¹ : Rˣ) : R) * (a ^ (q - 1) - c ^ (q - 1)) := by
    rw [← hmul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [he]
  exact P.mul_mem_left _ hp

/- English proof (translation)
Introduce `N`. Establish `hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R')`. Use `le_trans (Ideal.pow_right_mono (J := (maximalIdeal R').comap (f : R →+* R')) ?_ N) (Ideal.le_comap_pow _ N)` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, ← res_eq_zero_iff O R']`.

Conclude with `(res_map f x).trans ((res_eq_zero_iff O R x).2 hx)`. Conclude with `(h N).comp (Ideal.quotientMap _ (f : R →+* R') hle)`.
-/
private theorem flo_cont {Γ O R R' : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing R]
    [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {a : Γ → R}
    (h : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (J := (maximalIdeal R').comap (f : R →+* R')) ?_ N) (Ideal.le_comap_pow _ N)
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O R']
    exact (res_map f x).trans ((res_eq_zero_iff O R x).2 hx)
  exact (h N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

/- English proof (translation)
Introduce `x hx`. Use `haveI hnt : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP`. Use `haveI hco : IsCO O (R ⧸ P) := co_quot O R (R ⧸ P) (Ideal.Quotient.mkₐ O P) (Ideal.Quotient.mkₐ_surjective O P)`. Establish `hu : ∀ z : ResidueField O, z ≠ 0 → z ^ (Nat.card (ResidueField O) - 1) = 1`. Introduce `z hz`.

Use `haveI := Fintype.ofFinite (ResidueField O)`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `FiniteField.pow_card_sub_one_eq_one z hz`. Establish `hzero : ∀ a ∈ maximalIdeal O, (Algebra.ofId O (R ⧸ P)) a = 0`. Introduce `a ha`.

Rewrite using `[Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hO a ha`. Set `iota : ResidueField O →ₐ[O] R ⧸ P` to `Ideal.Quotient.liftₐ (maximalIdeal O) (Algebra.ofId O (R ⧸ P)) hzero`. Set `φ : Λ.Λ →ₐ[O] R ⧸ P` to `(Ideal.Quotient.mkₐ O P).comp (Λ.toPair p)`. Set `ε : Λ.Λ →ₐ[O] R ⧸ P` to `iota.comp (res O Λ.Λ)`.

Establish `hiota : ∀ a : O, iota (algebraMap O (ResidueField O) a) = Ideal.Quotient.mk P (algebraMap O R a)`. Introduce `a`. Rewrite using `[AlgHom.commutes, Ideal.Quotient.mk_algebraMap]`. Establish `key : ∀ y : R, IsUnit y → y ^ (Nat.card (ResidueField O) - 1) - 1 ∈ P → iota (res O R y) = Ideal.Quotient.mk P y`. Introduce `y hy hyp`.

Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) y`. Establish `hr : res O R y = res O R (algebraMap O R a)`. Rewrite using `[← sub_eq_zero, ← map_sub, res_eq_zero_iff]`. Conclude with `ha`. Establish `hra : res O R (algebraMap O R a) = algebraMap O (ResidueField O) a` using `AlgHom.commutes _ a`.

Rewrite using `[hr, hra, hiota]`. Use `symm`. Rewrite using `[Ideal.Quotient.eq]`. Apply `flo_sub_mem P y (algebraMap O R a) hr hy` to reduce the goal to its premises. Establish `hres_a : algebraMap O (ResidueField O) a ≠ 0`.

Rewrite using `[← hra, ← hr]`. Introduce `h0`. Rewrite `h0` using `[res_eq_zero_iff]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h0 hy`. Establish `hm : a ^ (Nat.card (ResidueField O) - 1) - 1 ∈ maximalIdeal O`.

Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_one, sub_eq_zero]`. Conclude with `hu _ hres_a`. Establish `hc : (algebraMap O R a) ^ (Nat.card (ResidueField O) - 1) - 1 ∈ P`. Rewrite using `[← map_pow, ← map_one (algebraMap O R), ← map_sub]`. Conclude with `hO _ hm`.

Establish `hsplit : y ^ (Nat.card (ResidueField O) - 1) - (algebraMap O R a) ^ (Nat.card (ResidueField O) - 1) = (y ^ (Nat.card (ResidueField O) - 1) - 1) - ((algebraMap O R a) ^ (Nat.card (ResidueField O) - 1) - 1)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Conclude with `P.sub_mem hyp hc`. Establish `hκ' : W.IsInert r (fun v i => W.pushCh (φ : Λ.Λ →+* R ⧸ P) (Λ.κ v i))`.

Introduce `v i`. Take `⟨ψ0, hψ0, heq⟩` from `Λ.inert v i`. Use `⟨W.pushCh (φ : Λ.Λ →+* R ⧸ P) ψ0, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `flo_cont φ hψ0.cont`. Introduce `g show res O (R ⧸ P) (φ (ψ0 g : Λ.Λ)) = _`.

Rewrite using `[res_map]`. Conclude with `hψ0.red g`. Introduce `g show φ (ψ0 g : Λ.Λ) = _`. Rewrite using `[hψ0.mu g, AlgHom.commutes]`. Use `show W.pushCh (φ : Λ.Λ →+* R ⧸ P) (Λ.κ v i) = _`.

Rewrite using `[heq]`. Both sides reduce to the same expression. Establish `hφε : φ = ε`. Use `(Λ.univ (R ⧸ P) _ hκ').unique (fun v i => rfl) (fun v i => ?_)` and prove the remaining obligations. Apply `MonoidHom.ext` to reduce the goal to its premises.

Introduce `g`. Apply `Units.ext` to reduce the goal to its premises. Establish `hs` using `congrArg (fun χ => ((χ g : Rˣ) : R)) (W.LamObj.toPair_spec r Λ p v i)`. Express the relevant statement in the definitionally equal form `Λ.toPair p (Λ.κ v i g : Λ.Λ) = ((p.ψ v i (g : F.Gv v)) : R) at hs`. Use `show iota (res O Λ.Λ (Λ.κ v i g : Λ.Λ)) = Ideal.Quotient.mk P (Λ.toPair p (Λ.κ v i g : Λ.Λ))`.

Rewrite using `[← res_map (Λ.toPair p), hs]`. Conclude with `key _ (Units.isUnit _) (hψ v i g g.2)`. Establish `hx' : Ideal.Quotient.mk P (Λ.toPair p x) = 0` using `by show φ x = 0`. Rewrite using `[hφε]`. Use `show iota (res O Λ.Λ x) = 0`.

Rewrite using `[(res_eq_zero_iff O Λ.Λ x).2 hx, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 hx'`.
-/
private theorem flo_lam {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Finite (ResidueField O)] [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ : W.LamObj r) {R : Type} [CommRing R]
    [Algebra O R] [IsCO O R] (p : W.Pair r R) (P : Ideal R) (hP : P ≠ ⊤)
    (hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ P)
    (hψ : ∀ v i, ∀ g ∈ F.Iv v, ((p.ψ v i g : Rˣ) : R) ^ (Nat.card (ResidueField O) - 1) - 1 ∈ P) :
    ∀ x ∈ maximalIdeal Λ.Λ, Λ.toPair p x ∈ P := by
  intro x hx
  haveI hnt : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP
  haveI hco : IsCO O (R ⧸ P) :=
    co_quot O R (R ⧸ P) (Ideal.Quotient.mkₐ O P) (Ideal.Quotient.mkₐ_surjective O P)
  have hu : ∀ z : ResidueField O, z ≠ 0 → z ^ (Nat.card (ResidueField O) - 1) = 1 := by
    intro z hz
    haveI := Fintype.ofFinite (ResidueField O)
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one z hz
  have hzero : ∀ a ∈ maximalIdeal O, (Algebra.ofId O (R ⧸ P)) a = 0 := by
    intro a ha
    rw [Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    exact hO a ha
  let iota : ResidueField O →ₐ[O] R ⧸ P :=
    Ideal.Quotient.liftₐ (maximalIdeal O) (Algebra.ofId O (R ⧸ P)) hzero
  let φ : Λ.Λ →ₐ[O] R ⧸ P := (Ideal.Quotient.mkₐ O P).comp (Λ.toPair p)
  let ε : Λ.Λ →ₐ[O] R ⧸ P := iota.comp (res O Λ.Λ)
  have hiota : ∀ a : O, iota (algebraMap O (ResidueField O) a) =
      Ideal.Quotient.mk P (algebraMap O R a) := by
    intro a
    rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]
  have key : ∀ y : R, IsUnit y → y ^ (Nat.card (ResidueField O) - 1) - 1 ∈ P →
      iota (res O R y) = Ideal.Quotient.mk P y := by
    intro y hy hyp
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
    have hr : res O R y = res O R (algebraMap O R a) := by
      rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
      exact ha
    have hra : res O R (algebraMap O R a) = algebraMap O (ResidueField O) a := AlgHom.commutes _ a
    rw [hr, hra, hiota]
    symm
    rw [Ideal.Quotient.eq]
    apply flo_sub_mem P y (algebraMap O R a) hr hy
    have hres_a : algebraMap O (ResidueField O) a ≠ 0 := by
      rw [← hra, ← hr]
      intro h0
      rw [res_eq_zero_iff] at h0
      exact (IsLocalRing.mem_maximalIdeal _).1 h0 hy
    have hm : a ^ (Nat.card (ResidueField O) - 1) - 1 ∈ maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_one, sub_eq_zero]
      exact hu _ hres_a
    have hc : (algebraMap O R a) ^ (Nat.card (ResidueField O) - 1) - 1 ∈ P := by
      rw [← map_pow, ← map_one (algebraMap O R), ← map_sub]
      exact hO _ hm
    have hsplit : y ^ (Nat.card (ResidueField O) - 1) - (algebraMap O R a) ^ (Nat.card (ResidueField O) - 1) =
        (y ^ (Nat.card (ResidueField O) - 1) - 1) - ((algebraMap O R a) ^ (Nat.card (ResidueField O) - 1) - 1) := by
      ring
    rw [hsplit]
    exact P.sub_mem hyp hc
  have hκ' : W.IsInert r (fun v i => W.pushCh (φ : Λ.Λ →+* R ⧸ P) (Λ.κ v i)) := by
    intro v i
    obtain ⟨ψ0, hψ0, heq⟩ := Λ.inert v i
    refine ⟨W.pushCh (φ : Λ.Λ →+* R ⧸ P) ψ0, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact flo_cont φ hψ0.cont
    · intro g
      show res O (R ⧸ P) (φ (ψ0 g : Λ.Λ)) = _
      rw [res_map]
      exact hψ0.red g
    · intro g
      show φ (ψ0 g : Λ.Λ) = _
      rw [hψ0.mu g, AlgHom.commutes]
    · show W.pushCh (φ : Λ.Λ →+* R ⧸ P) (Λ.κ v i) = _
      rw [heq]
      rfl
  have hφε : φ = ε := by
    refine (Λ.univ (R ⧸ P) _ hκ').unique (fun v i => rfl) (fun v i => ?_)
    apply MonoidHom.ext
    intro g
    apply Units.ext
    have hs := congrArg (fun χ => ((χ g : Rˣ) : R)) (W.LamObj.toPair_spec r Λ p v i)
    change Λ.toPair p (Λ.κ v i g : Λ.Λ) = ((p.ψ v i (g : F.Gv v)) : R) at hs
    show iota (res O Λ.Λ (Λ.κ v i g : Λ.Λ)) = Ideal.Quotient.mk P (Λ.toPair p (Λ.κ v i g : Λ.Λ))
    rw [← res_map (Λ.toPair p), hs]
    exact key _ (Units.isUnit _) (hψ v i g g.2)
  have hx' : Ideal.Quotient.mk P (Λ.toPair p x) = 0 := by
    show φ x = 0
    rw [hφε]
    show iota (res O Λ.Λ x) = 0
    rw [(res_eq_zero_iff O Λ.Λ x).2 hx, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.1 hx'

/- English proof (translation)
Establish `hfin : ((Ideal.Quotient.mk P).comp f).Finite`. Establish `e : (Ideal.Quotient.mk P).comp f = (Ideal.Quotient.factor hJ).comp ((Ideal.Quotient.mk J).comp f)`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `(RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJ)).comp hf`. Use `haveI hnt : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 ‹P.IsPrime›.ne_top`. Use `haveI hdom : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P`. Use `haveI : (⊥ : Ideal (R ⧸ P)).IsPrime := Ideal.isPrime_bot`. Establish `hc : Ideal.comap ((Ideal.Quotient.mk P).comp f) ⊥ = maximalIdeal A`.

Establish `h1 : Ideal.comap ((Ideal.Quotient.mk P).comp f) ⊥ = Ideal.comap f P`. Rewrite using `[← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Rewrite using `[h1]`. Apply `le_antisymm` to reduce the goal to its premises. Apply `IsLocalRing.le_maximalIdeal` to reduce the goal to its premises.

Introduce `htop`. Establish `h1' : (1 : A) ∈ Ideal.comap f P` using `htop ▸ Submodule.mem_top`. Rewrite `h1'` using `[Ideal.mem_comap, map_one]`. Conclude with `‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).2 h1')`. Conclude with `h`.

Establish `hb` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ hfin.to_isIntegral (⊥ : Ideal (R ⧸ P)) (by rw [hc]; exact IsLocalRing.maximalIdeal.isMaximal A)`. Establish `hm` using `Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective (K := ⊥)`. Rewrite `hm` using `[← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Then use the resulting hypothesis.
-/
private theorem flo_max {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] (f : A →+* R) (J P : Ideal R)
    [P.IsPrime] (hJ : J ≤ P) (hf : ((Ideal.Quotient.mk J).comp f).Finite) (h : ∀ x ∈ maximalIdeal A, f x ∈ P) :
    P.IsMaximal := by
  have hfin : ((Ideal.Quotient.mk P).comp f).Finite := by
    have e : (Ideal.Quotient.mk P).comp f =
        (Ideal.Quotient.factor hJ).comp ((Ideal.Quotient.mk J).comp f) := by
      ext x
      rfl
    rw [e]
    exact (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJ)).comp hf
  haveI hnt : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 ‹P.IsPrime›.ne_top
  haveI hdom : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  haveI : (⊥ : Ideal (R ⧸ P)).IsPrime := Ideal.isPrime_bot
  have hc : Ideal.comap ((Ideal.Quotient.mk P).comp f) ⊥ = maximalIdeal A := by
    have h1 : Ideal.comap ((Ideal.Quotient.mk P).comp f) ⊥ = Ideal.comap f P := by
      rw [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [h1]
    apply le_antisymm
    · apply IsLocalRing.le_maximalIdeal
      intro htop
      have h1' : (1 : A) ∈ Ideal.comap f P := htop ▸ Submodule.mem_top
      rw [Ideal.mem_comap, map_one] at h1'
      exact ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).2 h1')
    · exact h
  have hb := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ hfin.to_isIntegral
    (⊥ : Ideal (R ⧸ P)) (by rw [hc]; exact IsLocalRing.maximalIdeal.isMaximal A)
  have hm := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective (K := ⊥)
  rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hm

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ F n T Φ hΦ hsurj Λ J hfin`. Use `haveI : Finite (ResidueField O) := Fr.IsCoef.fin (l := l)`. Use `haveI : IsLocalRing ↥T.S.B := IsLocalRing.of_surjective' (Φ : T.B.B →+* ↥T.S.B) hsurj`. Use `show T.S.mB ≤ (Ideal.map Φ J ⊔ T.S.lamId).radical`. Rewrite using `[Ideal.radical_eq_sInf]`.

Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `Q ⟨hIQ, hQ⟩`. Establish `hJQ : Ideal.map Φ J ≤ Q` using `le_trans le_sup_left hIQ`. Establish `hLQ : T.S.lamId ≤ Q` using `le_trans le_sup_right hIQ`. Establish `hOQ : Ideal.map (algebraMap O ↥T.S.B) (maximalIdeal O) ≤ Q` using `le_trans le_sup_left hLQ`.

Establish `hJP : J ≤ Ideal.comap Φ Q` using `Ideal.map_le_iff_le_comap.1 hJQ`. Establish `hO : ∀ a ∈ maximalIdeal O, algebraMap O T.B.B a ∈ Ideal.comap Φ Q`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, AlgHom.commutes]`. Conclude with `hOQ (Ideal.mem_map_of_mem _ ha)`.

Establish `hu : ∀ u : (ResidueField O)ˣ, u ^ (Nat.card (ResidueField O) - 1) = 1`. Introduce `u`. Use `haveI := Fintype.ofFinite (ResidueField O)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]`.

Conclude with `FiniteField.pow_card_sub_one_eq_one _ u.ne_zero`. Establish `hψ : ∀ v i, ∀ g ∈ T.G.Iv v, ((T.B.u.ψ v i g : T.B.Bˣ) : T.B.B) ^ (Nat.card (ResidueField O) - 1) - 1 ∈ Ideal.comap Φ Q`. Introduce `v i g hg`. Establish `h2` using `congrArg (fun χ => ((χ g : (T.S.R)ˣ) : T.S.R)) (hΦ.2 v i)`. Simplify using `[W.pushCh, Pr.TwLink.twψ, Pr.TwLink.κA] at h2`.

Establish `hg' : T.K.lam v g ∈ F.Iv (T.K.e v)` using `(T.K.lam_I v g).2 hg`. Establish `hx : Φ ((T.B.u.ψ v i g : T.B.Bˣ) : T.B.B) = T.S.ψB (T.K.e v) i (T.K.lam v g) * algebraMap O ↥T.S.B (T.K.κ ((T.G.φ v) g) : O)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[h2]`. Both sides reduce to the same expression.

Establish `e1 : T.S.ψB (T.K.e v) i (T.K.lam v g) ^ (Nat.card (ResidueField O) - 1) = T.S.ψB (T.K.e v) i (T.K.lam v g ^ (Nat.card (ResidueField O) - 1))`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Fr.Space.ψB]`. Establish `hΨ : F.Ψ ((F.loc (T.K.e v)) (T.K.lam v g ^ (Nat.card (ResidueField O) - 1))) = 1`. Rewrite using `[map_pow, map_pow]`.

Conclude with `hu _`. Establish `hA : T.S.ψB (T.K.e v) i (T.K.lam v g ^ (Nat.card (ResidueField O) - 1)) - 1 ∈ Q` using `hLQ (Ideal.mem_sup_right (Ideal.subset_span ⟨T.K.e v, i, _, pow_mem hg' _, hΨ, rfl⟩))`. Establish `hB : algebraMap O ↥T.S.B (T.K.κ ((T.G.φ v) g) : O) ^ (Nat.card (ResidueField O) - 1) - 1 ∈ Q`. Rewrite using `[← map_pow, ← map_one (algebraMap O ↥T.S.B), ← map_sub]`. Apply `hOQ` to reduce the goal to its premises.

Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_one, sub_eq_zero]`. Establish `hne : IsLocalRing.residue O (T.K.κ ((T.G.φ v) g) : O) ≠ 0` using `((T.K.κ ((T.G.φ v) g)).isUnit.map (IsLocalRing.residue O)).ne_zero`. Use `haveI := Fintype.ofFinite (ResidueField O)`. Rewrite using `[Nat.card_eq_fintype_card]`.

Conclude with `FiniteField.pow_card_sub_one_eq_one _ hne`. Rewrite using `[Ideal.mem_comap, map_sub, map_pow, map_one, hx, mul_pow, e1]`. Establish `hr : ∀ x y : ↥T.S.B, x * y - 1 = (x - 1) * y + (y - 1)` using `fun x y => by ring`. Rewrite using `[hr]`. Conclude with `Q.add_mem (Q.mul_mem_right _ hA) hB`.

Establish `hPt : Ideal.comap Φ Q ≠ ⊤` using `(Ideal.comap_isPrime Φ Q).ne_top`. Establish `hlam` using `flo_lam Λ T.B.u (Ideal.comap Φ Q) hPt hO hψ`. Use `haveI : (Ideal.comap Φ Q).IsPrime := Ideal.comap_isPrime Φ Q`. Establish `hPmax : (Ideal.comap Φ Q).IsMaximal` using `flo_max (Λ.toPair T.B.u : Λ.Λ →+* T.B.B) J (Ideal.comap Φ Q) hJP hfin (fun x hx => hlam x hx)`. Establish `hQle : Q ≤ maximalIdeal ↥T.S.B` using `IsLocalRing.le_maximalIdeal hQ.ne_top`.

Establish `hM : Ideal.comap Φ (maximalIdeal ↥T.S.B) = Ideal.comap Φ Q`. Use `symm`. Apply `hPmax.eq_of_le` to reduce the goal to its premises. Introduce `h1`. Apply `(IsLocalRing.maximalIdeal.isMaximal ↥T.S.B).ne_top` to reduce the goal to its premises.

Rewrite `h1`, the goal using `[Ideal.eq_top_iff_one]`. Rewrite `h1` using `[Ideal.mem_comap, map_one]`. Conclude with `h1`. Conclude with `Ideal.comap_mono hQle`. Establish `hQmax : Q = maximalIdeal ↥T.S.B`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hQmax]`. Apply `IsLocalRing.le_maximalIdeal` to reduce the goal to its premises. Introduce `h`. Establish `h1 : (1 : ↥T.S.B) ∈ T.S.mB` using `h ▸ Submodule.mem_top`.

Rewrite `h1` using `[Fr.Space.mB, Ideal.mem_comap, map_one]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal T.S.R).ne_top ((Ideal.eq_top_iff_one _).2 h1)`.
-/
theorem UpperTheory.V.Pr.finLamOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.FinLamOf := by
  intro l _ O _ _ _ _ _ F n T Φ hΦ hsurj Λ J hfin
  haveI : Finite (ResidueField O) := Fr.IsCoef.fin (l := l)
  haveI : IsLocalRing ↥T.S.B := IsLocalRing.of_surjective' (Φ : T.B.B →+* ↥T.S.B) hsurj
  show T.S.mB ≤ (Ideal.map Φ J ⊔ T.S.lamId).radical
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro Q ⟨hIQ, hQ⟩
  have hJQ : Ideal.map Φ J ≤ Q := le_trans le_sup_left hIQ
  have hLQ : T.S.lamId ≤ Q := le_trans le_sup_right hIQ
  have hOQ : Ideal.map (algebraMap O ↥T.S.B) (maximalIdeal O) ≤ Q := le_trans le_sup_left hLQ
  have hJP : J ≤ Ideal.comap Φ Q := Ideal.map_le_iff_le_comap.1 hJQ
  have hO : ∀ a ∈ maximalIdeal O, algebraMap O T.B.B a ∈ Ideal.comap Φ Q := by
    intro a ha
    rw [Ideal.mem_comap, AlgHom.commutes]
    exact hOQ (Ideal.mem_map_of_mem _ ha)
  have hu : ∀ u : (ResidueField O)ˣ, u ^ (Nat.card (ResidueField O) - 1) = 1 := by
    intro u
    haveI := Fintype.ofFinite (ResidueField O)
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ u.ne_zero
  have hψ : ∀ v i, ∀ g ∈ T.G.Iv v, ((T.B.u.ψ v i g : T.B.Bˣ) : T.B.B) ^ (Nat.card (ResidueField O) - 1) - 1 ∈ Ideal.comap Φ Q := by
    intro v i g hg
    have h2 := congrArg (fun χ => ((χ g : (T.S.R)ˣ) : T.S.R)) (hΦ.2 v i)
    simp [W.pushCh, Pr.TwLink.twψ, Pr.TwLink.κA] at h2
    have hg' : T.K.lam v g ∈ F.Iv (T.K.e v) := (T.K.lam_I v g).2 hg
    have hx : Φ ((T.B.u.ψ v i g : T.B.Bˣ) : T.B.B) =
        T.S.ψB (T.K.e v) i (T.K.lam v g) * algebraMap O ↥T.S.B (T.K.κ ((T.G.φ v) g) : O) := by
      apply Subtype.ext
      rw [h2]
      rfl
    have e1 : T.S.ψB (T.K.e v) i (T.K.lam v g) ^ (Nat.card (ResidueField O) - 1) =
        T.S.ψB (T.K.e v) i (T.K.lam v g ^ (Nat.card (ResidueField O) - 1)) := by
      apply Subtype.ext
      simp [Fr.Space.ψB]
    have hΨ : F.Ψ ((F.loc (T.K.e v)) (T.K.lam v g ^ (Nat.card (ResidueField O) - 1))) = 1 := by
      rw [map_pow, map_pow]
      exact hu _
    have hA : T.S.ψB (T.K.e v) i (T.K.lam v g ^ (Nat.card (ResidueField O) - 1)) - 1 ∈ Q :=
      hLQ (Ideal.mem_sup_right (Ideal.subset_span
        ⟨T.K.e v, i, _, pow_mem hg' _, hΨ, rfl⟩))
    have hB : algebraMap O ↥T.S.B (T.K.κ ((T.G.φ v) g) : O) ^ (Nat.card (ResidueField O) - 1) - 1 ∈ Q := by
      rw [← map_pow, ← map_one (algebraMap O ↥T.S.B), ← map_sub]
      apply hOQ
      apply Ideal.mem_map_of_mem
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_one, sub_eq_zero]
      have hne : IsLocalRing.residue O (T.K.κ ((T.G.φ v) g) : O) ≠ 0 :=
        ((T.K.κ ((T.G.φ v) g)).isUnit.map (IsLocalRing.residue O)).ne_zero
      haveI := Fintype.ofFinite (ResidueField O)
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ hne
    rw [Ideal.mem_comap, map_sub, map_pow, map_one, hx, mul_pow, e1]
    have hr : ∀ x y : ↥T.S.B, x * y - 1 = (x - 1) * y + (y - 1) := fun x y => by ring
    rw [hr]
    exact Q.add_mem (Q.mul_mem_right _ hA) hB
  have hPt : Ideal.comap Φ Q ≠ ⊤ := (Ideal.comap_isPrime Φ Q).ne_top
  have hlam := flo_lam Λ T.B.u (Ideal.comap Φ Q) hPt hO hψ
  haveI : (Ideal.comap Φ Q).IsPrime := Ideal.comap_isPrime Φ Q
  have hPmax : (Ideal.comap Φ Q).IsMaximal :=
    flo_max (Λ.toPair T.B.u : Λ.Λ →+* T.B.B) J (Ideal.comap Φ Q) hJP hfin (fun x hx => hlam x hx)
  have hQle : Q ≤ maximalIdeal ↥T.S.B := IsLocalRing.le_maximalIdeal hQ.ne_top
  have hM : Ideal.comap Φ (maximalIdeal ↥T.S.B) = Ideal.comap Φ Q := by
    symm
    apply hPmax.eq_of_le
    · intro h1
      apply (IsLocalRing.maximalIdeal.isMaximal ↥T.S.B).ne_top
      rw [Ideal.eq_top_iff_one] at h1 ⊢
      rw [Ideal.mem_comap, map_one] at h1
      exact h1
    · exact Ideal.comap_mono hQle
  have hQmax : Q = maximalIdeal ↥T.S.B :=
    calc Q = Ideal.map Φ (Ideal.comap Φ Q) := (Ideal.map_comap_of_surjective Φ hsurj Q).symm
      _ = Ideal.map Φ (Ideal.comap Φ (maximalIdeal ↥T.S.B)) := by rw [hM]
      _ = maximalIdeal ↥T.S.B := Ideal.map_comap_of_surjective Φ hsurj _
  rw [hQmax]
  apply IsLocalRing.le_maximalIdeal
  intro h
  have h1 : (1 : ↥T.S.B) ∈ T.S.mB := h ▸ Submodule.mem_top
  rw [Fr.Space.mB, Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal T.S.R).ne_top ((Ideal.eq_top_iff_one _).2 h1)
