import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitTraceUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntOfIsIntegral

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResMult

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

/- English proof (translation)
Introduce `K K' d φ hU s hgen p r c hp hr hrbar hdeg heq`. Use `set φO := intMap hU with hφO`. Establish `hspec : (algebraMap K'.O K'.E).comp φO = φ.comp (algebraMap K.O K.E)` using `RingHom.ext fun a => intMap_spec hU a`. Establish `hmax : ∀ a ∈ IsLocalRing.maximalIdeal K.O, φO a ∈ IsLocalRing.maximalIdeal K'.O`. Introduce `a ha`.

Rewrite using `[← map_maximalIdeal hU]`. Conclude with `Ideal.mem_map_of_mem _ ha`. Use `haveI : IsLocalHom φO := ⟨fun a ha => by`. Assume the negation of the conclusion as `h`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 (hmax a ((IsLocalRing.mem_maximalIdeal _).2 h)) ha⟩`.

Set `k` to `IsLocalRing.ResidueField K.O`. Set `k'` to `IsLocalRing.ResidueField K'.O`. Set `ψ : k →+* k'` to `IsLocalRing.ResidueField.map φO`. Establish `hψ : ∀ a : K.O, ψ (IsLocalRing.residue K.O a) = IsLocalRing.residue K'.O (φO a)` using `fun a => IsLocalRing.ResidueField.map_residue φO a`. Use `letI : Algebra k k' := ψ.toAlgebra`.

Use `letI : Fintype k := Fintype.ofFinite k`. Use `letI : Fintype k' := Fintype.ofFinite k'`. Use `set Q := Fintype.card k with hQdef`. Establish `hQ : Q = K.q ^ 2` using `by rw [hQdef, ← Nat.card_eq_fintype_card]; exact K.card_res`. Establish `hQ' : Fintype.card k' = Q ^ d`.

Rewrite using `[← Nat.card_eq_fintype_card]`. Express the relevant statement in the definitionally equal form `Nat.card (IsLocalRing.ResidueField K'.O) = _`. Rewrite using `[K'.card_res, hU.1, hQ, ← pow_mul, ← pow_mul, mul_comm]`. Establish `hQ1 : 1 < Q` using `Fintype.one_lt_card`. Establish `hd : d ≠ 0` using `hU.ne_zero`.

Use `set F := FiniteField.frobeniusAlgHom k k' with hF`. Establish `hFpow : ∀ (i : ℕ) (x : k'), (F ^ i) x = x ^ (Q ^ i)`. Introduce `i x`. Proceed by induction on `i with`. Consider the case `zero => simp`.

Consider the case `succ i ih`. Rewrite using `[pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom]`. Use `show (x ^ Q ^ i) ^ Q = x ^ Q ^ (i + 1)`. Rewrite using `[← pow_mul, ← pow_succ]`. Establish `hrc : r * c = p.map φO`.

Apply `Polynomial.map_injective _ (IsFractionRing.injective K'.O K'.E)` to reduce the goal to its premises. Rewrite using `[← heq, Polynomial.map_map, hspec]`. Use `set sb := IsLocalRing.residue K'.O s with hsb`. Use `set P := (r * c).map (IsLocalRing.residue K'.O) with hP`. Establish `hP2 : P = (p.map (IsLocalRing.residue K.O)).map ψ`.

Rewrite using `[hP, hrc, Polynomial.map_map, Polynomial.map_map]`. Use `congr 1`. Establish `hPmon : P.Monic` using `by rw [hP2]; exact (hp.map _).map _`. Establish `hP0 : P ≠ 0` using `hPmon.ne_zero`. Establish `hPdeg : P.natDegree = d * r.natDegree`.

Rewrite using `[hP2, (hp.map _).natDegree_map, hp.natDegree_map, hdeg]`. Establish `hPmul : P = r.map (IsLocalRing.residue K'.O) * c.map (IsLocalRing.residue K'.O)`. Rewrite using `[hP, Polynomial.map_mul]`. Establish `hmu : rootMultiplicity sb P = r.natDegree + rootMultiplicity sb (c.map (IsLocalRing.residue K'.O))`. Rewrite using `[hPmul, rootMultiplicity_mul (hPmul ▸ hP0), hrbar, rootMultiplicity_X_sub_C_pow]`.

Establish `hconj : ∀ i : ℕ, rootMultiplicity sb P ≤ rootMultiplicity (sb ^ (Q ^ i)) P`. Introduce `i`. Establish `h` using `le_rootMultiplicity_map (f := ((F ^ i : k' →ₐ[k] k') : k' →+* k')) (p := P) ?_ sb`. Establish `hPFi : P.map ((F ^ i : k' →ₐ[k] k') : k' →+* k') = P`. Rewrite using `[hP2, Polynomial.map_map]`.

Use `congr 1`. Conclude with `RingHom.ext fun x => (F ^ i).commutes x`. Rewrite `h` using `[hPFi]`. Simplify `h` using `[hFpow]`. Rewrite using `[hP2, Polynomial.map_map]`.

Establish `: ((F ^ i : k' →ₐ[k] k') : k' →+* k').comp ψ = ψ` using `RingHom.ext fun x => (F ^ i).commutes x`. Rewrite using `[this, ← hP2]`. Conclude with `hP0`. Establish `hinj : ∀ i j, i < j → j < d → sb ^ (Q ^ i) ≠ sb ^ (Q ^ j)`. Introduce `i j hij hjd h`.

Take `⟨m, rfl⟩ : ∃ m, j = i + m` from `⟨j - i, by omega⟩`. Establish `hm : 0 < m` using `by omega`. Establish `hfix : sb ^ (Q ^ m) = sb`. Apply `RingHom.injective ((F ^ i : k' →ₐ[k] k') : k' →+* k')` to reduce the goal to its premises. Rewrite using `[AlgHom.coe_toRingHom, hFpow, hFpow, h, ← pow_mul, pow_add, mul_comm]`.

Establish `hall : ∀ y : k', y ^ (Q ^ m) = y`. Introduce `y`. Take `⟨y', rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨f, z, hz, hy⟩` from `hgen y'`. Establish `hy' : y' = f.eval₂ φO s + z`.

Apply `IsFractionRing.injective K'.O K'.E` to reduce the goal to its premises. Rewrite using `[hy, map_add, Polynomial.hom_eval₂, hspec]`. Establish `hres : IsLocalRing.residue K'.O y' = f.eval₂ (ψ.comp (IsLocalRing.residue K.O)) sb`. Rewrite using `[hy', map_add, (IsLocalRing.residue_eq_zero_iff z).2 hz, add_zero, Polynomial.hom_eval₂]`. Use `congr 1`.

Establish `hev` using `Polynomial.hom_eval₂ f (ψ.comp (IsLocalRing.residue K.O)) ((F ^ m : k' →ₐ[k] k') : k' →+* k') sb`. Establish `hc : ((F ^ m : k' →ₐ[k] k') : k' →+* k').comp (ψ.comp (IsLocalRing.residue K.O)) = ψ.comp (IsLocalRing.residue K.O)` using `RingHom.ext fun a => (F ^ m).commutes (IsLocalRing.residue K.O a)`. Rewrite `hev` using `[hc, AlgHom.coe_toRingHom, hFpow m sb, hfix, hFpow]`. Rewrite using `[hres]`. Conclude with `hev`.

Establish `hQm : 1 < Q ^ m` using `Nat.one_lt_pow hm.ne' hQ1`. Establish `hcard : Fintype.card k' ≤ Q ^ m`. Establish `h1` using `card_le_degree_of_subset_roots (p := (X ^ (Q ^ m) - X : k'[X])) (Z := Finset.univ) (by`. Introduce `y _`. Rewrite using `[mem_roots (FiniteField.X_pow_card_sub_X_ne_zero (K' := k') hQm)]`.

Simplify using `[IsRoot, hall y])`. Rewrite `h1` using `[FiniteField.X_pow_card_sub_X_natDegree_eq (K' := k') hQm, Finset.card_univ]`. Then use the resulting hypothesis. Rewrite `hcard` using `[hQ']`. Conclude with `absurd hcard (not_le.2 (Nat.pow_lt_pow_right hQ1 (by omega)))`. Set `t : ℕ → k'` to `fun i => sb ^ (Q ^ i)`.

Establish `htinj : Set.InjOn t (Finset.range d)`. Introduce `i hi j hj h`. Break down `lt_trichotomy i j with h' | h' | h'` into its components or cases. Conclude with `absurd h (hinj i j h' (by simpa using hj))`. Conclude with `h'`.

Conclude with `absurd h.symm (hinj j i h' (by simpa using hi))`. Use `set S := (Finset.range d).image t with hSdef`. Establish `hS : S.card = d` using `by rw [Finset.card_image_of_injOn htinj, Finset.card_range]`. Establish `hsum1 : d * rootMultiplicity sb P ≤ ∑ x ∈ S, P.roots.count x`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_const, hS, smul_eq_mul]`. Use `_ ≤ ∑ x ∈ S, P.roots.count x := Finset.sum_le_sum fun x hx => by`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hx`. Rewrite using `[count_roots]`. Conclude with `hconj i`.

Establish `hsum2 : ∑ x ∈ S, P.roots.count x ≤ Multiset.card P.roots`. Combine the equalities or inequalities in the displayed calculation. Establish `hle : d * rootMultiplicity sb P ≤ d * r.natDegree` using `hsum1.trans (hsum2.trans ((card_roots' P).trans hPdeg.le))`. Establish `hle'` using `Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hd)`. Establish `hc0 : c.map (IsLocalRing.residue K'.O) ≠ 0` using `right_ne_zero_of_mul (hPmul ▸ hP0)`.

Introduce `hroot`. Use `(rootMultiplicity_pos hc0).2 hroot` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem not_isRoot_cofactor : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O,
    (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y =
      f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z) →
    ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic →
      r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree →
      p.natDegree = d * r.natDegree →
      p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) →
      ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := by
  intro K K' d φ hU s hgen p r c hp hr hrbar hdeg heq
  classical
  set φO := intMap hU with hφO
  have hspec : (algebraMap K'.O K'.E).comp φO = φ.comp (algebraMap K.O K.E) :=
    RingHom.ext fun a => intMap_spec hU a
  have hmax : ∀ a ∈ IsLocalRing.maximalIdeal K.O, φO a ∈ IsLocalRing.maximalIdeal K'.O := by
    intro a ha
    rw [← map_maximalIdeal hU]
    exact Ideal.mem_map_of_mem _ ha
  haveI : IsLocalHom φO := ⟨fun a ha => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).1 (hmax a ((IsLocalRing.mem_maximalIdeal _).2 h)) ha⟩
  let k := IsLocalRing.ResidueField K.O
  let k' := IsLocalRing.ResidueField K'.O
  let ψ : k →+* k' := IsLocalRing.ResidueField.map φO
  have hψ : ∀ a : K.O, ψ (IsLocalRing.residue K.O a) = IsLocalRing.residue K'.O (φO a) :=
    fun a => IsLocalRing.ResidueField.map_residue φO a
  letI : Algebra k k' := ψ.toAlgebra
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype k' := Fintype.ofFinite k'
  set Q := Fintype.card k with hQdef
  have hQ : Q = K.q ^ 2 := by rw [hQdef, ← Nat.card_eq_fintype_card]; exact K.card_res
  have hQ' : Fintype.card k' = Q ^ d := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (IsLocalRing.ResidueField K'.O) = _
    rw [K'.card_res, hU.1, hQ, ← pow_mul, ← pow_mul, mul_comm]
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hd : d ≠ 0 := hU.ne_zero
  set F := FiniteField.frobeniusAlgHom k k' with hF
  have hFpow : ∀ (i : ℕ) (x : k'), (F ^ i) x = x ^ (Q ^ i) := by
    intro i x
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom]
      show (x ^ Q ^ i) ^ Q = x ^ Q ^ (i + 1)
      rw [← pow_mul, ← pow_succ]

  have hrc : r * c = p.map φO := by
    apply Polynomial.map_injective _ (IsFractionRing.injective K'.O K'.E)
    rw [← heq, Polynomial.map_map, hspec]
  set sb := IsLocalRing.residue K'.O s with hsb
  set P := (r * c).map (IsLocalRing.residue K'.O) with hP
  have hP2 : P = (p.map (IsLocalRing.residue K.O)).map ψ := by
    rw [hP, hrc, Polynomial.map_map, Polynomial.map_map]
    congr 1
  have hPmon : P.Monic := by rw [hP2]; exact (hp.map _).map _
  have hP0 : P ≠ 0 := hPmon.ne_zero
  have hPdeg : P.natDegree = d * r.natDegree := by
    rw [hP2, (hp.map _).natDegree_map, hp.natDegree_map, hdeg]
  have hPmul : P = r.map (IsLocalRing.residue K'.O) * c.map (IsLocalRing.residue K'.O) := by
    rw [hP, Polynomial.map_mul]
  have hmu : rootMultiplicity sb P = r.natDegree + rootMultiplicity sb (c.map (IsLocalRing.residue K'.O)) := by
    rw [hPmul, rootMultiplicity_mul (hPmul ▸ hP0), hrbar, rootMultiplicity_X_sub_C_pow]

  have hconj : ∀ i : ℕ, rootMultiplicity sb P ≤ rootMultiplicity (sb ^ (Q ^ i)) P := by
    intro i
    have h := le_rootMultiplicity_map (f := ((F ^ i : k' →ₐ[k] k') : k' →+* k')) (p := P) ?_ sb
    · have hPFi : P.map ((F ^ i : k' →ₐ[k] k') : k' →+* k') = P := by
        rw [hP2, Polynomial.map_map]
        congr 1
        exact RingHom.ext fun x => (F ^ i).commutes x
      rw [hPFi] at h
      simpa [hFpow] using h
    · rw [hP2, Polynomial.map_map]
      have : ((F ^ i : k' →ₐ[k] k') : k' →+* k').comp ψ = ψ := RingHom.ext fun x => (F ^ i).commutes x
      rw [this, ← hP2]; exact hP0

  have hinj : ∀ i j, i < j → j < d → sb ^ (Q ^ i) ≠ sb ^ (Q ^ j) := by
    intro i j hij hjd h
    obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
    have hm : 0 < m := by omega
    have hfix : sb ^ (Q ^ m) = sb := by
      apply RingHom.injective ((F ^ i : k' →ₐ[k] k') : k' →+* k')
      rw [AlgHom.coe_toRingHom, hFpow, hFpow, h, ← pow_mul, pow_add, mul_comm]
    have hall : ∀ y : k', y ^ (Q ^ m) = y := by
      intro y
      obtain ⟨y', rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨f, z, hz, hy⟩ := hgen y'
      have hy' : y' = f.eval₂ φO s + z := by
        apply IsFractionRing.injective K'.O K'.E
        rw [hy, map_add, Polynomial.hom_eval₂, hspec]
      have hres : IsLocalRing.residue K'.O y' = f.eval₂ (ψ.comp (IsLocalRing.residue K.O)) sb := by
        rw [hy', map_add, (IsLocalRing.residue_eq_zero_iff z).2 hz, add_zero, Polynomial.hom_eval₂]
        congr 1
      have hev := Polynomial.hom_eval₂ f (ψ.comp (IsLocalRing.residue K.O))
        ((F ^ m : k' →ₐ[k] k') : k' →+* k') sb
      have hc : ((F ^ m : k' →ₐ[k] k') : k' →+* k').comp (ψ.comp (IsLocalRing.residue K.O)) =
          ψ.comp (IsLocalRing.residue K.O) := RingHom.ext fun a => (F ^ m).commutes (IsLocalRing.residue K.O a)
      rw [hc, AlgHom.coe_toRingHom, hFpow m sb, hfix, hFpow] at hev
      rw [hres]; exact hev
    have hQm : 1 < Q ^ m := Nat.one_lt_pow hm.ne' hQ1
    have hcard : Fintype.card k' ≤ Q ^ m := by
      have h1 := card_le_degree_of_subset_roots (p := (X ^ (Q ^ m) - X : k'[X])) (Z := Finset.univ) (by
        intro y _
        rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero (K' := k') hQm)]
        simp [IsRoot, hall y])
      rwa [FiniteField.X_pow_card_sub_X_natDegree_eq (K' := k') hQm, Finset.card_univ] at h1
    rw [hQ'] at hcard
    exact absurd hcard (not_le.2 (Nat.pow_lt_pow_right hQ1 (by omega)))

  let t : ℕ → k' := fun i => sb ^ (Q ^ i)
  have htinj : Set.InjOn t (Finset.range d) := by
    intro i hi j hj h
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (hinj i j h' (by simpa using hj))
    · exact h'
    · exact absurd h.symm (hinj j i h' (by simpa using hi))
  set S := (Finset.range d).image t with hSdef
  have hS : S.card = d := by rw [Finset.card_image_of_injOn htinj, Finset.card_range]
  have hsum1 : d * rootMultiplicity sb P ≤ ∑ x ∈ S, P.roots.count x := by
    calc d * rootMultiplicity sb P = ∑ _x ∈ S, rootMultiplicity sb P := by
          rw [Finset.sum_const, hS, smul_eq_mul]
      _ ≤ ∑ x ∈ S, P.roots.count x := Finset.sum_le_sum fun x hx => by
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
          rw [count_roots]; exact hconj i
  have hsum2 : ∑ x ∈ S, P.roots.count x ≤ Multiset.card P.roots := by
    calc ∑ x ∈ S, P.roots.count x ≤ ∑ x ∈ S ∪ P.roots.toFinset, P.roots.count x :=
          Finset.sum_le_sum_of_subset Finset.subset_union_left
      _ = ∑ x ∈ P.roots.toFinset, P.roots.count x :=
          (Finset.sum_subset Finset.subset_union_right fun x _ hx =>
            Multiset.count_eq_zero.2 (by simpa using hx)).symm
      _ = Multiset.card P.roots := Multiset.toFinset_sum_count_eq _
  have hle : d * rootMultiplicity sb P ≤ d * r.natDegree :=
    hsum1.trans (hsum2.trans ((card_roots' P).trans hPdeg.le))
  have hle' := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hd)
  have hc0 : c.map (IsLocalRing.residue K'.O) ≠ 0 := right_ne_zero_of_mul (hPmul ▸ hP0)
  intro hroot
  have := (rootMultiplicity_pos hc0).2 hroot
  omega

end GlobalTheory.UnitLemma.Unr.ResMult
