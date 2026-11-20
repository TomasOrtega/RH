import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FiniteAlgIdem

open Polynomial

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => exact isCoprime_one_left`. Consider the case `cons a s ih`. Rewrite using `[Multiset.prod_cons]`. Conclude with `(h a (Multiset.mem_cons_self a s)).mul_left (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))`.
-/
theorem isCoprime_multiset_prod_left {R : Type} [CommRing R] (s : Multiset R) (y : R)
    (h : ∀ x ∈ s, IsCoprime x y) : IsCoprime s.prod y := by
  induction s using Multiset.induction_on with
  | empty => exact isCoprime_one_left
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a s)).mul_left
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O L)` using `hv.hom_inj`. Establish `hs : (f.map (algebraMap O L)).Splits` using `IsAlgClosed.splits _`. Establish `hm : (f.map (algebraMap O L)).Monic` using `hf.map _`. Establish `hroot : ∀ x ∈ (f.map (algebraMap O L)).roots, ∃ y, algebraMap O L y = x`. Introduce `x hx`.

Establish `hint : IsIntegral O x` using `⟨f, hf, by`. Rewrite using `[← Polynomial.eval_map]`. Conclude with `(Polynomial.mem_roots hm.ne_zero).1 hx⟩`. Conclude with `hv.exists_of_le_one ((Valuation.mem_integer_iff _ _).1 (hv.mem_of_integral hint))`. Use `⟨(f.map (algebraMap O L)).roots.map (Function.invFun (algebraMap O L)), ?_⟩` and prove the remaining obligations.

Apply `Polynomial.map_injective _ hinj` to reduce the goal to its premises. Use `conv_lhs => rw [hs.eq_prod_roots_of_monic hm]`. Rewrite using `[Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises.

Introduce `x hx`. Simplify using `[Function.invFun_eq (hroot x hx)]`.
-/
theorem monic_eq_prod_X_sub_C {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] (hv : v.Integers O) (f : O[X]) (hf : f.Monic) :
    ∃ r : Multiset O, f = (r.map fun x => X - C x).prod := by
  classical
  have hinj : Function.Injective (algebraMap O L) := hv.hom_inj
  have hs : (f.map (algebraMap O L)).Splits := IsAlgClosed.splits _
  have hm : (f.map (algebraMap O L)).Monic := hf.map _
  have hroot : ∀ x ∈ (f.map (algebraMap O L)).roots, ∃ y, algebraMap O L y = x := by
    intro x hx
    have hint : IsIntegral O x := ⟨f, hf, by
      rw [← Polynomial.eval_map]
      exact (Polynomial.mem_roots hm.ne_zero).1 hx⟩
    exact hv.exists_of_le_one ((Valuation.mem_integer_iff _ _).1 (hv.mem_of_integral hint))
  refine ⟨(f.map (algebraMap O L)).roots.map (Function.invFun (algebraMap O L)), ?_⟩
  apply Polynomial.map_injective _ hinj
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm]
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  simp [Function.invFun_eq (hroot x hx)]

/- English proof (translation)
Take `⟨f, hf, hfa⟩` from `Algebra.IsIntegral.isIntegral (R := O) a`. Take `⟨r, hr⟩` from `monic_eq_prod_X_sub_C hv f hf`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `h : aeval a f = 0` using `hfa`. Rewrite `h` using `[hr, map_multiset_prod, Multiset.map_map]`.

Simplify `h` using `[Function.comp_def]`.
-/
theorem exists_prod_sub_eq_zero {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] (hv : v.Integers O) {A : Type} [CommRing A]
    [Algebra O A] [Algebra.IsIntegral O A] (a : A) :
    ∃ r : Multiset O, (r.map fun x => a - algebraMap O A x).prod = 0 := by
  obtain ⟨f, hf, hfa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
  obtain ⟨r, hr⟩ := monic_eq_prod_X_sub_C hv f hf
  refine ⟨r, ?_⟩
  have h : aeval a f = 0 := hfa
  rw [hr, map_multiset_prod, Multiset.map_map] at h
  simpa [Function.comp_def] using h

/- English proof (translation)
Establish `h` using `congrArg c hr`. Rewrite `h` using `[map_multiset_prod, Multiset.map_map, map_zero, Multiset.prod_eq_zero_iff]`. Take `⟨x, hx, hx0⟩` from `Multiset.mem_map.1 h`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, map_sub, AlgHom.commutes] at hx0`.

Conclude with `sub_eq_zero.1 hx0`.
-/
theorem exists_mem_eq {O : Type} [CommRing O] {A K : Type} [CommRing A] [Algebra O A]
    [CommRing K] [IsDomain K] [Algebra O K] (c : A →ₐ[O] K) {a : A} {r : Multiset O}
    (hr : (r.map fun x => a - algebraMap O A x).prod = 0) :
    ∃ x ∈ r, c a = algebraMap O K x := by
  have h := congrArg c hr
  rw [map_multiset_prod, Multiset.map_map, map_zero, Multiset.prod_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.1 h
  refine ⟨x, hx, ?_⟩
  simp only [Function.comp_apply, map_sub, AlgHom.commutes] at hx0
  exact sub_eq_zero.1 hx0

open Classical in

/- English proof (translation)
Take `⟨g, hg⟩ : ∃ g : O[X], g = ((r.filter fun x => IsLocalRing.residue O x = ρ).map fun x => X - C x).prod` from `⟨_, rfl⟩`. Take `⟨h, hh⟩ : ∃ h : O[X], h = ((r.filter fun x => ¬ IsLocalRing.residue O x = ρ).map fun x => X - C x).prod` from `⟨_, rfl⟩`. Establish `hgh : g * h = (r.map fun x => X - C x).prod`. Rewrite using `[hg, hh, ← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]`. Establish `hcop : IsCoprime g h`.

Rewrite using `[hg]`. Apply `isCoprime_multiset_prod_left` to reduce the goal to its premises. Introduce `p hp`. Take `⟨x, hx, rfl⟩` from `Multiset.mem_map.1 hp`. Rewrite using `[hh]`.

Apply `IsCoprime.symm` to reduce the goal to its premises. Apply `isCoprime_multiset_prod_left` to reduce the goal to its premises. Introduce `q hq`. Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hq`. Apply `Polynomial.isCoprime_X_sub_C_of_isUnit_sub` to reduce the goal to its premises.

Apply `(IsLocalRing.residue_ne_zero_iff_isUnit _).1` to reduce the goal to its premises. Rewrite using `[map_sub, (Multiset.mem_filter.1 hx).2, sub_ne_zero]`. Conclude with `(Multiset.mem_filter.1 hy).2`. Take `⟨u, w, huw⟩` from `hcop`. Establish `hF : aeval a (g * h) = 0`.

Rewrite using `[hgh, map_multiset_prod, Multiset.map_map]`. Simplify `hr` using `[Function.comp_def]`. Use `⟨aeval a (w * h), ?_, ?_⟩` and prove the remaining obligations. Establish `key : w * h * (w * h) = w * h - u * w * (g * h)`. Take the linear combination `(w * h) * huw`.

Use `show aeval a (w * h) * aeval a (w * h) = aeval a (w * h)`. Rewrite using `[← map_mul, key, map_sub, map_mul (aeval a) (u * w), hF, mul_zero, sub_zero]`. Introduce `c`. Rewrite using `[← Polynomial.aeval_algHom_apply]`. Take `⟨x, hx, hcx⟩` from `exists_mem_eq c hr`.

Rewrite `hcx` using `[IsLocalRing.ResidueField.algebraMap_eq]`. Establish `h1` using `congrArg (aeval (c a)) huw`. Rewrite `h1` using `[map_add, map_mul, map_mul, map_one]`. Distinguish the cases in `hρ : IsLocalRing.residue O x = ρ`. Establish `hg0 : aeval (c a) g = 0`.

Rewrite using `[hg, map_multiset_prod, Multiset.map_map]`. Apply `Multiset.prod_eq_zero` to reduce the goal to its premises. Use `Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩` and prove the remaining obligations. Simplify using `[hcx]`. Rewrite using `[if_pos (hcx.trans hρ), map_mul]`.

Rewrite `h1` using `[hg0, mul_zero, zero_add]`. Conclude with `h1`. Establish `hh0 : aeval (c a) h = 0`. Rewrite using `[hh, map_multiset_prod, Multiset.map_map]`. Apply `Multiset.prod_eq_zero` to reduce the goal to its premises.

Use `Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩` and prove the remaining obligations. Simplify using `[hcx]`. Rewrite using `[if_neg (show ¬ c a = ρ by rwa [hcx]), map_mul, hh0, mul_zero]`.
-/
theorem exists_idempotent {O : Type} [CommRing O] [IsLocalRing O] {A : Type} [CommRing A]
    [Algebra O A] {a : A} {r : Multiset O} (hr : (r.map fun x => a - algebraMap O A x).prod = 0)
    (ρ : IsLocalRing.ResidueField O) :
    ∃ e : A, IsIdempotentElem e ∧ ∀ c : A →ₐ[O] IsLocalRing.ResidueField O,
      c e = if c a = ρ then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : O[X],
      g = ((r.filter fun x => IsLocalRing.residue O x = ρ).map fun x => X - C x).prod := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : O[X],
      h = ((r.filter fun x => ¬ IsLocalRing.residue O x = ρ).map fun x => X - C x).prod :=
    ⟨_, rfl⟩
  have hgh : g * h = (r.map fun x => X - C x).prod := by
    rw [hg, hh, ← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
  have hcop : IsCoprime g h := by
    rw [hg]
    apply isCoprime_multiset_prod_left
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hp
    rw [hh]
    apply IsCoprime.symm
    apply isCoprime_multiset_prod_left
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hq
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    rw [map_sub, (Multiset.mem_filter.1 hx).2, sub_ne_zero]
    exact (Multiset.mem_filter.1 hy).2
  obtain ⟨u, w, huw⟩ := hcop
  have hF : aeval a (g * h) = 0 := by
    rw [hgh, map_multiset_prod, Multiset.map_map]
    simpa [Function.comp_def] using hr
  refine ⟨aeval a (w * h), ?_, ?_⟩
  · have key : w * h * (w * h) = w * h - u * w * (g * h) := by
      linear_combination (w * h) * huw
    show aeval a (w * h) * aeval a (w * h) = aeval a (w * h)
    rw [← map_mul, key, map_sub, map_mul (aeval a) (u * w), hF, mul_zero, sub_zero]
  · intro c
    rw [← Polynomial.aeval_algHom_apply]
    obtain ⟨x, hx, hcx⟩ := exists_mem_eq c hr
    rw [IsLocalRing.ResidueField.algebraMap_eq] at hcx
    have h1 := congrArg (aeval (c a)) huw
    rw [map_add, map_mul, map_mul, map_one] at h1
    by_cases hρ : IsLocalRing.residue O x = ρ
    · have hg0 : aeval (c a) g = 0 := by
        rw [hg, map_multiset_prod, Multiset.map_map]
        apply Multiset.prod_eq_zero
        refine Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩
        simp [hcx]
      rw [if_pos (hcx.trans hρ), map_mul]
      rw [hg0, mul_zero, zero_add] at h1
      exact h1
    · have hh0 : aeval (c a) h = 0 := by
        rw [hh, map_multiset_prod, Multiset.map_map]
        apply Multiset.prod_eq_zero
        refine Multiset.mem_map.2 ⟨x, Multiset.mem_filter.2 ⟨hx, hρ⟩, ?_⟩
        simp [hcx]
      rw [if_neg (show ¬ c a = ρ by rwa [hcx]), map_mul, hh0, mul_zero]

end GlobalTheory.FiniteAlgIdem

namespace GlobalTheory.FiniteAlgIdem

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hI : Ideal.span {1 - s} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Introduce `hu`. Apply `hne` to reduce the goal to its premises.

Establish `h0 : (1 - s) * s = 0` using `by rw [sub_mul, one_mul, hs.eq, sub_self]`. Conclude with `hu.mul_right_eq_zero.1 h0`. Take `⟨M, hM, hsM⟩` from `Ideal.exists_le_maximal _ hI`. Set `ψ : O →ₐ[O] A ⧸ M` to `Algebra.ofId O (A ⧸ M)`. Establish `hψ : Function.Surjective ψ`.

Introduce `b`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Take `⟨r, hr⟩` from `exists_prod_sub_eq_zero hv b`. Take `⟨x, -, hbx⟩` from `exists_mem_eq (Ideal.Quotient.mkₐ O M) hr`. Conclude with `⟨x, by rw [Algebra.ofId_apply, ← hbx]; rfl⟩`.

Establish `hker : ∀ y ∈ RingHom.ker ψ, (Algebra.ofId O (IsLocalRing.ResidueField O)) y = 0`. Introduce `y hy`. Establish `hne : RingHom.ker ψ ≠ ⊤`. Rewrite using `[Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]`. Conclude with `one_ne_zero`.

Rewrite using `[Algebra.ofId_apply, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]`. Conclude with `IsLocalRing.le_maximalIdeal hne hy`. Set `c : A →ₐ[O] IsLocalRing.ResidueField O` to `(Ideal.Quotient.liftₐ (RingHom.ker ψ) (Algebra.ofId O _) hker).comp ((Ideal.quotientKerAlgEquivOfSurjective hψ).symm.toAlgHom.comp (Ideal.Quotient.mkₐ O M))`. Establish `hm : Ideal.Quotient.mkₐ O M (1 - s) = 0`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hsM (Ideal.mem_span_singleton_self _)`. Establish `h1 : c (1 - s) = 0`. Simplify using `only [c, AlgHom.comp_apply, hm, map_zero]`. Rewrite `h1` using `[map_sub, map_one, h c, sub_zero]`. Conclude with `one_ne_zero h1`.
-/
theorem idempotent_eq_zero {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] [IsLocalRing O] (hv : v.Integers O) {A : Type}
    [CommRing A] [Algebra O A] [Algebra.IsIntegral O A] {s : A} (hs : IsIdempotentElem s)
    (h : ∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c s = 0) : s = 0 := by
  by_contra hne
  have hI : Ideal.span {1 - s} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    apply hne
    have h0 : (1 - s) * s = 0 := by rw [sub_mul, one_mul, hs.eq, sub_self]
    exact hu.mul_right_eq_zero.1 h0
  obtain ⟨M, hM, hsM⟩ := Ideal.exists_le_maximal _ hI
  let ψ : O →ₐ[O] A ⧸ M := Algebra.ofId O (A ⧸ M)
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨r, hr⟩ := exists_prod_sub_eq_zero hv b
    obtain ⟨x, -, hbx⟩ := exists_mem_eq (Ideal.Quotient.mkₐ O M) hr
    exact ⟨x, by rw [Algebra.ofId_apply, ← hbx]; rfl⟩
  have hker : ∀ y ∈ RingHom.ker ψ, (Algebra.ofId O (IsLocalRing.ResidueField O)) y = 0 := by
    intro y hy
    have hne : RingHom.ker ψ ≠ ⊤ := by
      rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
      exact one_ne_zero
    rw [Algebra.ofId_apply, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact IsLocalRing.le_maximalIdeal hne hy
  let c : A →ₐ[O] IsLocalRing.ResidueField O :=
    (Ideal.Quotient.liftₐ (RingHom.ker ψ) (Algebra.ofId O _) hker).comp
      ((Ideal.quotientKerAlgEquivOfSurjective hψ).symm.toAlgHom.comp (Ideal.Quotient.mkₐ O M))
  have hm : Ideal.Quotient.mkₐ O M (1 - s) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hsM (Ideal.mem_span_singleton_self _)
  have h1 : c (1 - s) = 0 := by
    simp only [c, AlgHom.comp_apply, hm, map_zero]
  rw [map_sub, map_one, h c, sub_zero] at h1
  exact one_ne_zero h1

/- English proof (translation)
Use `haveI : Algebra.IsIntegral O A := Algebra.IsIntegral.of_finite O A`. Take `⟨S, hS⟩` from `Module.Finite.fg_top (R := O) (M := A)`. Use `choose r hr using fun a : A => exists_prod_sub_eq_zero hv a`. Use `choose E hEi hEc using fun (a : A) (ρ : IsLocalRing.ResidueField O) => exists_idempotent (hr a) ρ`. Establish `hsep : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, (∀ j ∈ S, c' j = c j) → c' = c`.

Introduce `c c' hcc`. Apply `AlgHom.toLinearMap_injective` to reduce the goal to its premises. Conclude with `LinearMap.ext_on hS fun x hx => hcc x hx`. Set `e : (A →ₐ[O] IsLocalRing.ResidueField O) → A` to `fun c => ∏ j ∈ S, E j (c j)`. Establish `hec : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = if c = c' then 1 else 0`.

Introduce `c c'`. Simplify using `only [e, map_prod, hEc]`. Distinguish the cases in `hcc : c = c'`. Substitute `hcc` using the available equality. Rewrite using `[if_pos rfl, Finset.prod_boole, if_pos (fun j _ => rfl)]`.

Rewrite using `[if_neg hcc, Finset.prod_boole, if_neg (fun hh => hcc (hsep c c' hh).symm)]`. Establish `hei : ∀ c, IsIdempotentElem (e c)` using `fun c => Finset.prod_induction _ IsIdempotentElem (fun _ _ ha hb => ha.mul hb) IsIdempotentElem.one (fun j _ => hEi _ _)`. Establish `hort : ∀ c c', c ≠ c' → e c * e c' = 0`. Introduce `c c' hne`. Apply `idempotent_eq_zero hv ((hei c).mul (hei c'))` to reduce the goal to its premises.

Introduce `c''`. Rewrite using `[map_mul, hec, hec]`. Apply the tactic sequence `split_ifs with h1 h2 <;> simp_all`. Establish `hfin : Finite (A →ₐ[O] IsLocalRing.ResidueField O)`. Set `T : S → Finset (IsLocalRing.ResidueField O)` to `fun j => ((r j).map (algebraMap O (IsLocalRing.ResidueField O))).toFinset`.

Set `F : (A →ₐ[O] IsLocalRing.ResidueField O) → (∀ j : S, T j)` to `fun c j => ⟨c j, by`. Take `⟨x, hx, hcx⟩` from `exists_mem_eq c (hr j)`. Simplify using `only [T, Multiset.mem_toFinset, Multiset.mem_map]`. Conclude with `⟨x, hx, hcx.symm⟩⟩`. Use `Finite.of_injective F ?_` and prove the remaining obligations.

Introduce `c c' hcc`. Conclude with `hsep c' c fun j hj => congrArg Subtype.val (congrFun hcc ⟨j, hj⟩)`. Use `⟨hfin, e, hei, hort, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hfin`. Use `letI := Fintype.ofFinite (A →ₐ[O] IsLocalRing.ResidueField O)`.

Rewrite using `[finsum_eq_sum_of_fintype]`. Establish `horth : OrthogonalIdempotents e` using `⟨hei, fun c c' h => hort c c' h⟩`. Establish `hsum` using `horth.isIdempotentElem_sum (s := Finset.univ)`. Establish `h0` using `idempotent_eq_zero hv hsum.one_sub (fun c'' => by`. Rewrite using `[map_sub, map_one, map_sum]`.

Simplify using `[hec])`. Conclude with `(sub_eq_zero.1 h0).symm`. Introduce `c c'`. Rewrite using `[hec]`. Apply the tactic sequence `split_ifs with h <;> simp [h]`.
-/
theorem finite_and_idempotents {L : Type} [Field L] [IsAlgClosed L] {v : Valuation L NNReal}
    {O : Type} [CommRing O] [Algebra O L] [IsLocalRing O] (hv : v.Integers O) (A : Type)
    [CommRing A] [Algebra O A] [Module.Finite O A] :
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
      ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧
        (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
        ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  classical
  haveI : Algebra.IsIntegral O A := Algebra.IsIntegral.of_finite O A
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := O) (M := A)
  choose r hr using fun a : A => exists_prod_sub_eq_zero hv a
  choose E hEi hEc using fun (a : A) (ρ : IsLocalRing.ResidueField O) =>
    exists_idempotent (hr a) ρ
  have hsep : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O,
      (∀ j ∈ S, c' j = c j) → c' = c := by
    intro c c' hcc
    apply AlgHom.toLinearMap_injective
    exact LinearMap.ext_on hS fun x hx => hcc x hx
  let e : (A →ₐ[O] IsLocalRing.ResidueField O) → A := fun c => ∏ j ∈ S, E j (c j)
  have hec : ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O,
      c' (e c) = if c = c' then 1 else 0 := by
    intro c c'
    simp only [e, map_prod, hEc]
    by_cases hcc : c = c'
    · subst hcc
      rw [if_pos rfl, Finset.prod_boole, if_pos (fun j _ => rfl)]
    · rw [if_neg hcc, Finset.prod_boole, if_neg (fun hh => hcc (hsep c c' hh).symm)]
  have hei : ∀ c, IsIdempotentElem (e c) := fun c =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ ha hb => ha.mul hb)
      IsIdempotentElem.one (fun j _ => hEi _ _)
  have hort : ∀ c c', c ≠ c' → e c * e c' = 0 := by
    intro c c' hne
    apply idempotent_eq_zero hv ((hei c).mul (hei c'))
    intro c''
    rw [map_mul, hec, hec]
    split_ifs with h1 h2 <;> simp_all
  have hfin : Finite (A →ₐ[O] IsLocalRing.ResidueField O) := by
    let T : S → Finset (IsLocalRing.ResidueField O) := fun j =>
      ((r j).map (algebraMap O (IsLocalRing.ResidueField O))).toFinset
    let F : (A →ₐ[O] IsLocalRing.ResidueField O) → (∀ j : S, T j) := fun c j =>
      ⟨c j, by
        obtain ⟨x, hx, hcx⟩ := exists_mem_eq c (hr j)
        simp only [T, Multiset.mem_toFinset, Multiset.mem_map]
        exact ⟨x, hx, hcx.symm⟩⟩
    refine Finite.of_injective F ?_
    intro c c' hcc
    exact hsep c' c fun j hj => congrArg Subtype.val (congrFun hcc ⟨j, hj⟩)
  refine ⟨hfin, e, hei, hort, ?_, ?_⟩
  · haveI := hfin
    letI := Fintype.ofFinite (A →ₐ[O] IsLocalRing.ResidueField O)
    rw [finsum_eq_sum_of_fintype]
    have horth : OrthogonalIdempotents e := ⟨hei, fun c c' h => hort c c' h⟩
    have hsum := horth.isIdempotentElem_sum (s := Finset.univ)
    have h0 := idempotent_eq_zero hv hsum.one_sub (fun c'' => by
      rw [map_sub, map_one, map_sum]
      simp [hec])
    exact (sub_eq_zero.1 h0).symm
  · intro c c'
    rw [hec]
    split_ifs with h <;> simp [h]

end GlobalTheory.FiniteAlgIdem

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ hv A _ _ _`. Conclude with `GlobalTheory.FiniteAlgIdem.finite_and_idempotents hv A`.
-/
theorem GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
    ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A],
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
    ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧
    (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
    ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv A _ _ _
  exact GlobalTheory.FiniteAlgIdem.finite_and_idempotents hv A
