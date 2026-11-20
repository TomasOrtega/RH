import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GmLawCharsMul
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem

set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.ChF

namespace GlobalTheory.ChF

/- English proof (translation)
Set `χ : (σ → Fin N) → (Multiplicative (σ → ℕ) →* O)` to `fun a => { toFun := fun b => ∏ i, (ζ ^ (Multiplicative.toAdd b) i) ^ (a i : ℕ) map_one' := by simp map_mul' := fun b b' => by`. Simplify using `[pow_add, mul_pow, Finset.prod_mul_distrib] }`. Establish `hinj : Function.Injective χ`. Introduce `a a' haa`. Use function extensionality and compare the values at `j`.

Establish `h1` using `DFunLike.congr_fun haa (Multiplicative.ofAdd (Pi.single j 1))`. Establish `key : ∀ e : σ → Fin N, χ e (Multiplicative.ofAdd (Pi.single j 1)) = ζ ^ (e j : ℕ)`. Introduce `e`. Use `show ∏ i, (ζ ^ (Pi.single j 1 : σ → ℕ) i) ^ (e i : ℕ) = _`. Rewrite using `[Finset.prod_eq_single j]`.

Simplify using the standard rewrite rules. Introduce `i _ hij`. Simplify using `[Pi.single_eq_of_ne hij]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[key, key]`.

Conclude with `Fin.ext (hζ.pow_inj (a j).2 (a' j).2 h1)`. Establish `hli` using `(linearIndependent_monoidHom (Multiplicative (σ → ℕ)) O).comp χ hinj`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Apply `hli c` to reduce the goal to its premises. Use function extensionality and compare the values at `b`.

Use `h (Multiplicative.toAdd b)` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, χ]`.
-/
private theorem coeff_eq_zero_of_roots {O : Type} [CommRing O] [IsDomain O] {σ : Type} [Fintype σ]
    [DecidableEq σ] {N : ℕ} {ζ : O} (hζ : IsPrimitiveRoot ζ N) (c : (σ → Fin N) → O)
    (h : ∀ b : σ → ℕ, ∑ a : σ → Fin N, c a * ∏ i, (ζ ^ b i) ^ (a i : ℕ) = 0) : ∀ a, c a = 0 := by
  let χ : (σ → Fin N) → (Multiplicative (σ → ℕ) →* O) := fun a =>
    { toFun := fun b => ∏ i, (ζ ^ (Multiplicative.toAdd b) i) ^ (a i : ℕ)
      map_one' := by simp
      map_mul' := fun b b' => by
        simp [pow_add, mul_pow, Finset.prod_mul_distrib] }
  have hinj : Function.Injective χ := by
    intro a a' haa
    funext j
    have h1 := DFunLike.congr_fun haa (Multiplicative.ofAdd (Pi.single j 1))
    have key : ∀ e : σ → Fin N, χ e (Multiplicative.ofAdd (Pi.single j 1)) = ζ ^ (e j : ℕ) := by
      intro e
      show ∏ i, (ζ ^ (Pi.single j 1 : σ → ℕ) i) ^ (e i : ℕ) = _
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · simp
    rw [key, key] at h1
    exact Fin.ext (hζ.pow_inj (a j).2 (a' j).2 h1)
  have hli := (linearIndependent_monoidHom (Multiplicative (σ → ℕ)) O).comp χ hinj
  rw [Fintype.linearIndependent_iff] at hli
  apply hli c
  funext b
  have := h (Multiplicative.toAdd b)
  simpa [Finset.sum_apply, χ] using this

/- English proof (translation)
Use `set S := Submodule.span O (Set.range fun a : σ → Fin N => ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (a i : ℕ)) with hS`. Establish `hmon : ∀ e : σ → ℕ, ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (e i) ∈ S`. Introduce `e`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun i => ⟨e i % N, Nat.mod_lt _ hN⟩, ?_⟩` and prove the remaining obligations.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `(pow_eq_pow_mod (e i) (hy i)).symm`. Establish `hmul : ∀ j, ∀ q ∈ S, q * (1 + ψ (MvPowerSeries.X j)) ∈ S`. Introduce `j q hq`. Proceed by induction on `hq using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Use `hmon (fun i => (a i : ℕ) + (Pi.single j 1 : σ → ℕ) i)` as an intermediate fact. Simplify using `only [pow_add, Finset.prod_mul_distrib] at this`. Rewrite `this` using `[Finset.prod_eq_single j (f := fun i => (1 + ψ (MvPowerSeries.X i)) ^ (Pi.single j 1 : σ → ℕ) i) (fun i _ hij => by simp [Pi.single_eq_of_ne hij]) (by simp), Pi.single_eq_same, pow_one]`. Then use the resulting hypothesis.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `S.add_mem hx hy`. Consider the case `smul a x _ hx => rw [smul_mul_assoc]`. Conclude with `S.smul_mem a hx`.

Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h1 : (1 : Q) ∈ S` using `by simpa using hmon 0`. Establish `: ψ ((MvPolynomial.C a : MvPolynomial σ O) : MvPowerSeries σ O) = a • (1 : Q)`. Rewrite using `[MvPolynomial.coe_C, ← Algebra.algebraMap_eq_smul_one]`.

Conclude with `ψ.commutes a`. Rewrite using `[this]`. Conclude with `S.smul_mem a h1`. Consider the case `add f g hf hg => rw [MvPolynomial.coe_add, map_add]`. Conclude with `S.add_mem hf hg`.

Consider the case `mul_X f j hf`. Rewrite using `[MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul]`. Use `S.sub_mem (hmul j _ hf) hf` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem map_coe_mem_span {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {σ : Type}
    [Fintype σ] [DecidableEq σ] {N : ℕ} (hN : 0 < N) (ψ : MvPowerSeries σ O →ₐ[O] Q)
    (hy : ∀ i, (1 + ψ (MvPowerSeries.X i)) ^ N = 1) (P : MvPolynomial σ O) :
    ψ (P : MvPowerSeries σ O) ∈ Submodule.span O
      (Set.range fun a : σ → Fin N => ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (a i : ℕ)) := by
  set S := Submodule.span O
      (Set.range fun a : σ → Fin N => ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (a i : ℕ)) with hS
  have hmon : ∀ e : σ → ℕ, ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (e i) ∈ S := by
    intro e
    apply Submodule.subset_span
    refine ⟨fun i => ⟨e i % N, Nat.mod_lt _ hN⟩, ?_⟩
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (pow_eq_pow_mod (e i) (hy i)).symm
  have hmul : ∀ j, ∀ q ∈ S, q * (1 + ψ (MvPowerSeries.X j)) ∈ S := by
    intro j q hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have := hmon (fun i => (a i : ℕ) + (Pi.single j 1 : σ → ℕ) i)
      simp only [pow_add, Finset.prod_mul_distrib] at this
      rwa [Finset.prod_eq_single j (f := fun i =>
        (1 + ψ (MvPowerSeries.X i)) ^ (Pi.single j 1 : σ → ℕ) i)
        (fun i _ hij => by simp [Pi.single_eq_of_ne hij]) (by simp), Pi.single_eq_same, pow_one] at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact S.smul_mem a hx
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h1 : (1 : Q) ∈ S := by simpa using hmon 0
    have : ψ ((MvPolynomial.C a : MvPolynomial σ O) : MvPowerSeries σ O) = a • (1 : Q) := by
      rw [MvPolynomial.coe_C, ← Algebra.algebraMap_eq_smul_one]
      exact ψ.commutes a
    rw [this]
    exact S.smul_mem a h1
  | add f g hf hg => rw [MvPolynomial.coe_add, map_add]; exact S.add_mem hf hg
  | mul_X f j hf =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul]
    have := S.sub_mem (hmul j _ hf) hf
    convert this using 1
    ring

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_add_pow_prime_pow_eq hp (1 : A) x k`. Use `⟨-(x * s), ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_pow_eq {A : Type} [CommRing A] {p : ℕ} (hp : p.Prime) (k : ℕ) (x : A) :
    ∃ s : A, x ^ p ^ k = ((1 + x) ^ p ^ k - 1) + (p : A) * s := by
  obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq hp (1 : A) x k
  refine ⟨-(x * s), ?_⟩
  rw [hs]
  ring

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Take `⟨z, hz⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot C N`. Establish `hvz : v z ≤ 1`. Establish `: v z ^ N = 1` using `by rw [← map_pow, hz.pow_eq_one, map_one]`. Conclude with `((pow_eq_one_iff_of_nonneg zero_le hN.ne').1 this).le`.

Take `⟨ζ, rfl⟩` from `hv.exists_of_le_one hvz`. Conclude with `⟨ζ, hz.of_map_of_injective hv.hom_inj⟩`.
-/
private theorem exists_primitiveRoot_integers {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {N : ℕ}
    (hN : 0 < N) : ∃ ζ : O, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C N
  have hvz : v z ≤ 1 := by
    have : v z ^ N = 1 := by rw [← map_pow, hz.pow_eq_one, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le hN.ne').1 this).le
  obtain ⟨ζ, rfl⟩ := hv.exists_of_le_one hvz
  exact ⟨ζ, hz.of_map_of_injective hv.hom_inj⟩

/- English proof (translation)
Introduce `p hp C _ _ _ v O _ _ hv _ hc r k`. Use `haveI : IsDomain O := hv.hom_inj.isDomain _`. Establish `hN : 0 < p ^ k` using `pow_pos hp.out.pos k`. Take `⟨ζ, hζ⟩` from `exists_primitiveRoot_integers hv hN`. Establish `hmul` using `(gmLaw_chars_mul O r).2.2 (p ^ k)`.

Use `set I : Ideal (PS O 1 r) := Ideal.span (Set.range (mulF (gmF O r) (p ^ k))) with hI`. Establish `hrel : ∀ i : Fin 1 × Fin r, (1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1 ∈ I`. Introduce and unpack `⟨i0, i⟩`. Take `rfl : i0 = 0` from `Subsingleton.elim _ _`. Conclude with `Ideal.subset_span ⟨i, hmul i⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨M, hM⟩ : ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin r → PS O 1 r)) ^ M ≤ I ⊔ Ideal.map (MvPowerSeries.C : O →+* PS O 1 r) (Ideal.span {(p : O)}) := by`. Apply `Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨s, hs⟩` from `exists_pow_eq hp.out k (MvPowerSeries.X i : PS O 1 r)`.

Use `⟨p ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`. Use `Ideal.add_mem _ (Ideal.mem_sup_left (hrel i)) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ ?_))` and prove the remaining obligations. Rewrite using `[← map_natCast (MvPowerSeries.C : O →+* PS O 1 r) p]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)`.

Set `π : PS O 1 r →ₐ[O] (PS O 1 r ⧸ I)` to `Ideal.Quotient.mkₐ O I`. Set `m : (Fin 1 × Fin r → Fin (p ^ k)) → (PS O 1 r ⧸ I)` to `fun a => ∏ i, (1 + π (MvPowerSeries.X i)) ^ (a i : ℕ)`. Establish `hspan : ∀ q : PS O 1 r ⧸ I, q ∈ Submodule.span O (Set.range m)`. Introduce `q`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective q`.

Take `⟨P, -, hP⟩` from `GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem O (Ideal.span {(p : O)}) (Submodule.fg_span (Set.finite_singleton _)) hc (Fin 1 × Fin r) (Fin r) (mulF (gmF O r) (p ^ k)) M hM g`. Rewrite using `[Ideal.Quotient.eq.2 hP]`. Use `map_coe_mem_span hN π (fun i => ?_) P` and prove the remaining obligations. Establish `h0 : π ((1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (hrel i)`. Rewrite `h0` using `[map_sub, map_pow, map_add, map_one]`.

Conclude with `sub_eq_zero.1 h0`. Establish `hpt : ∀ b : Fin 1 × Fin r → ℕ, ∃ φ : (PS O 1 r ⧸ I) →ₐ[O] O, ∀ i, φ (π (MvPowerSeries.X i)) = ζ ^ b i - 1`. Introduce `b`. Establish `hone : ∀ i, (1 + (ζ ^ b i - 1)) ^ p ^ k - 1 = 0`. Introduce `i`.

Rewrite using `[add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self]`. Take `⟨ψ, hψ⟩` from `(GlobalTheory.mvPowerSeries_eval_of_pow_mem O (Ideal.span {(p : O)}) (Fin 1 × Fin r) (fun i => ζ ^ b i - 1) (fun i => by`. Take `⟨s, hs⟩` from `exists_pow_eq hp.out k (ζ ^ b i - 1)`. Use `⟨p ^ k, ?_⟩` and prove the remaining obligations. Rewrite using `[hs, hone, zero_add]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hc O`. Establish `hker : I ≤ RingHom.ker ψ`. Rewrite using `[hI, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `show ψ _ = 0`.

Rewrite using `[hmul, map_sub, map_pow, map_add, map_one, hψ]`. Conclude with `hone _`. Conclude with `⟨Ideal.Quotient.liftₐ I ψ (fun a ha => hker ha), fun i => hψ i⟩`. Establish `hsep : ∀ c : (Fin 1 × Fin r → Fin (p ^ k)) → O, (∀ φ : (PS O 1 r ⧸ I) →ₐ[O] O, φ (∑ a, c a • m a) = 0) → ∀ a, c a = 0`. Introduce `c hcφ`.

Use `coeff_eq_zero_of_roots hζ c fun b => ?_` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `hpt b`. Use `hcφ φ` as an intermediate fact. Simplify `this` using `only [map_sum, map_smul, m, map_prod, map_pow, map_add, map_one, hφ, add_sub_cancel, smul_eq_mul]`. Establish `hli : LinearIndependent O m`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c h0`. Conclude with `hsep c fun φ => by rw [h0, map_zero]`. Set `B` to `Module.Basis.mk hli (fun q _ => hspan q)`. Use `⟨Module.Free.of_basis B, Module.Finite.of_basis B, fun q hq => ?_⟩` and prove the remaining obligations.

Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 (hspan q)`. Simplify using `[hsep c hq]`.
-/
theorem fh_gmF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (r : ℕ), FH p (gmF O r) := by
  intro p hp C _ _ _ v O _ _ hv _ hc r k
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain _
  have hN : 0 < p ^ k := pow_pos hp.out.pos k
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_integers hv hN
  have hmul := (gmLaw_chars_mul O r).2.2 (p ^ k)
  set I : Ideal (PS O 1 r) := Ideal.span (Set.range (mulF (gmF O r) (p ^ k))) with hI
  have hrel : ∀ i : Fin 1 × Fin r, (1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1 ∈ I := by
    rintro ⟨i0, i⟩
    obtain rfl : i0 = 0 := Subsingleton.elim _ _
    exact Ideal.subset_span ⟨i, hmul i⟩

  obtain ⟨M, hM⟩ : ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin r → PS O 1 r)) ^ M ≤
      I ⊔ Ideal.map (MvPowerSeries.C : O →+* PS O 1 r) (Ideal.span {(p : O)}) := by
    apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs⟩ := exists_pow_eq hp.out k (MvPowerSeries.X i : PS O 1 r)
    refine ⟨p ^ k, ?_⟩
    rw [hs]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (hrel i)) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ ?_))
    rw [← map_natCast (MvPowerSeries.C : O →+* PS O 1 r) p]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  let π : PS O 1 r →ₐ[O] (PS O 1 r ⧸ I) := Ideal.Quotient.mkₐ O I
  let m : (Fin 1 × Fin r → Fin (p ^ k)) → (PS O 1 r ⧸ I) :=
    fun a => ∏ i, (1 + π (MvPowerSeries.X i)) ^ (a i : ℕ)
  have hspan : ∀ q : PS O 1 r ⧸ I, q ∈ Submodule.span O (Set.range m) := by
    intro q
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨P, -, hP⟩ := GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem O
      (Ideal.span {(p : O)}) (Submodule.fg_span (Set.finite_singleton _)) hc (Fin 1 × Fin r) (Fin r)
      (mulF (gmF O r) (p ^ k)) M hM g
    rw [Ideal.Quotient.eq.2 hP]
    refine map_coe_mem_span hN π (fun i => ?_) P
    have h0 : π ((1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (hrel i)
    rw [map_sub, map_pow, map_add, map_one] at h0
    exact sub_eq_zero.1 h0

  have hpt : ∀ b : Fin 1 × Fin r → ℕ, ∃ φ : (PS O 1 r ⧸ I) →ₐ[O] O,
      ∀ i, φ (π (MvPowerSeries.X i)) = ζ ^ b i - 1 := by
    intro b
    have hone : ∀ i, (1 + (ζ ^ b i - 1)) ^ p ^ k - 1 = 0 := by
      intro i
      rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self]
    obtain ⟨ψ, hψ⟩ := (GlobalTheory.mvPowerSeries_eval_of_pow_mem O (Ideal.span {(p : O)}) (Fin 1 × Fin r)
      (fun i => ζ ^ b i - 1) (fun i => by
        obtain ⟨s, hs⟩ := exists_pow_eq hp.out k (ζ ^ b i - 1)
        refine ⟨p ^ k, ?_⟩
        rw [hs, hone, zero_add]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hc O
    have hker : I ≤ RingHom.ker ψ := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      show ψ _ = 0
      rw [hmul, map_sub, map_pow, map_add, map_one, hψ]
      exact hone _
    exact ⟨Ideal.Quotient.liftₐ I ψ (fun a ha => hker ha), fun i => hψ i⟩
  have hsep : ∀ c : (Fin 1 × Fin r → Fin (p ^ k)) → O,
      (∀ φ : (PS O 1 r ⧸ I) →ₐ[O] O, φ (∑ a, c a • m a) = 0) → ∀ a, c a = 0 := by
    intro c hcφ
    refine coeff_eq_zero_of_roots hζ c fun b => ?_
    obtain ⟨φ, hφ⟩ := hpt b
    have := hcφ φ
    simpa only [map_sum, map_smul, m, map_prod, map_pow, map_add, map_one, hφ, add_sub_cancel,
      smul_eq_mul] using this
  have hli : LinearIndependent O m := by
    rw [Fintype.linearIndependent_iff]
    intro c h0
    exact hsep c fun φ => by rw [h0, map_zero]
  let B := Module.Basis.mk hli (fun q _ => hspan q)
  refine ⟨Module.Free.of_basis B, Module.Finite.of_basis B, fun q hq => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hspan q)
  simp [hsep c hq]

end GlobalTheory.ChF
