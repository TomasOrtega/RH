import ReciprocityTheory.AnalyticForms.RegularLocalRings.PreMemIrreducibleComponents

namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {W : Scheme.{0}}

def IsBranchH (T : Set W) {U : W.Opens} (f : Γ(W, U)) (y : W) (C : Set W) : Prop :=
  C ∈ compsH T ∧ y ∈ C ∧ ∃ h : IsIrreducible C, h.genericPoint ∈ U ∧ h.genericPoint ∈ W.zeroLocus {f}

/- English proof (translation)
Establish `hs : closure {h.genericPoint} = closure ({x} : Set W)` using `h.isGenericPoint_genericPoint isClosed_closure`. Conclude with `(inseparable_iff_closure_eq.2 hs).eq`.
-/
theorem gp_closure_singleton {x : W} (h : IsIrreducible (closure ({x} : Set W))) :
    h.genericPoint = x := by
  have hs : closure {h.genericPoint} = closure ({x} : Set W) :=
    h.isGenericPoint_genericPoint isClosed_closure
  exact (inseparable_iff_closure_eq.2 hs).eq

/- English proof (translation)
Conclude with `(inseparable_iff_closure_eq.2 h).eq`.
-/
theorem eq_of_closure_singleton_eq {x x' : W} (h : closure ({x} : Set W) = closure {x'}) : x = x' := by
  exact (inseparable_iff_closure_eq.2 h).eq

def ParPrimes {U : W.Opens} (hU : IsAffineOpen U) {y : W} (hy : y ∈ U) {n : ℕ} (f : Fin n → Γ(W, U))
    (q : Fin n → PrimeSpectrum Γ(W, U)) : Prop :=
  (∀ i, q i ≤ hU.primeIdealOf ⟨y, hy⟩) ∧ (∀ i, f i ∈ (q i).asIdeal) ∧
  (∀ i (Q : PrimeSpectrum Γ(W, U)), Q ≤ hU.primeIdealOf ⟨y, hy⟩ → (f i ∈ Q.asIdeal ↔ q i ≤ Q)) ∧
  (∀ i j, f j ∈ (q i).asIdeal → j = i)

/- English proof (translation)
Use `letI : Algebra Γ(W, U) (W.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨y, hy⟩`. Use `haveI : IsLocalization.AtPrime (W.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal := hU.isLocalization_stalk ⟨y, hy⟩`. Establish `hrsp' : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => algebraMap Γ(W, U) (W.presheaf.stalk y) (f i))` using `hrsp`. Establish `hsp` using `fun i => parPrime_spec (A := Γ(W, U)) (S := W.presheaf.stalk y) (p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal) hrsp' i`. Use `⟨fun i => ⟨parPrime (S := W.presheaf.stalk y) f i, (hsp i).1⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Conclude with `(hsp i).2.1`. Introduce `i`. Conclude with `(hsp i).2.2`. Introduce `i Q hQ haveI := Q.isPrime`.

Conclude with `mem_iff_parPrime_le (A := Γ(W, U)) (S := W.presheaf.stalk y) (p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal) hrsp' i hQ`. Introduce `i j h`. Conclude with `eq_of_mem_parPrime (A := Γ(W, U)) (S := W.presheaf.stalk y) hrsp' h`.
-/
theorem exists_parPrimes {U : W.Opens} (hU : IsAffineOpen U) {y : W} (hy : y ∈ U) {n : ℕ}
    (f : Fin n → Γ(W, U)) [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U y hy (f i))) :
    ∃ q, ParPrimes hU hy f q := by
  letI : Algebra Γ(W, U) (W.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨y, hy⟩
  haveI : IsLocalization.AtPrime (W.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  have hrsp' : FinalTheorems.Rsp (W.presheaf.stalk y) n
      (fun i => algebraMap Γ(W, U) (W.presheaf.stalk y) (f i)) := hrsp
  have hsp := fun i => parPrime_spec (A := Γ(W, U)) (S := W.presheaf.stalk y)
    (p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal) hrsp' i
  refine ⟨fun i => ⟨parPrime (S := W.presheaf.stalk y) f i, (hsp i).1⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hsp i).2.1
  · intro i
    exact (hsp i).2.2
  · intro i Q hQ
    haveI := Q.isPrime
    exact mem_iff_parPrime_le (A := Γ(W, U)) (S := W.presheaf.stalk y)
      (p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal) hrsp' i hQ
  · intro i j h
    exact eq_of_mem_parPrime (A := Γ(W, U)) (S := W.presheaf.stalk y) hrsp' h

section Br

variable {Z : W.IdealSheafData} {U : W.Opens} {hU : IsAffineOpen U} {y : W} {hy : y ∈ U} {n : ℕ}
  {f : Fin n → Γ(W, U)} {J : Finset (Fin n)} {q : Fin n → PrimeSpectrum Γ(W, U)}

/- English proof (translation)
Use `show P ∈ hV.fromSpec ⁻¹' W.zeroLocus s ↔ _`. Rewrite using `[hV.fromSpec_preimage_zeroLocus]`. Conclude with `Iff.rfl`.
-/
private lemma fromSpec_mem_zeroLocus_iff_subset {V : W.Opens} (hV : IsAffineOpen V) (s : Set Γ(W, V))
    (P : PrimeSpectrum Γ(W, V)) : hV.fromSpec P ∈ W.zeroLocus s ↔ s ⊆ P.asIdeal := by
  show P ∈ hV.fromSpec ⁻¹' W.zeroLocus s ↔ _
  rw [hV.fromSpec_preimage_zeroLocus]
  exact Iff.rfl

/- English proof (translation)
Conclude with `hV.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.trans (PrimeSpectrum.le_iff_specializes P Q).symm`.
-/
private lemma fromSpec_specializes_iff_le {V : W.Opens} (hV : IsAffineOpen V) (P Q : PrimeSpectrum Γ(W, V)) :
    hV.fromSpec P ⤳ hV.fromSpec Q ↔ P ≤ Q := by
  exact hV.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.trans
    (PrimeSpectrum.le_iff_specializes P Q).symm

/- English proof (translation)
Use `show _ ∈ (V : Set W)`. Rewrite using `[← hV.range_fromSpec]`. Conclude with `Set.mem_range_self P`.
-/
private lemma fromSpec_mem_of_isAffineOpen' {V : W.Opens} (hV : IsAffineOpen V) (P : PrimeSpectrum Γ(W, V)) :
    hV.fromSpec P ∈ V := by
  show _ ∈ (V : Set W)
  rw [← hV.range_fromSpec]
  exact Set.mem_range_self P

/- English proof (translation)
Rewrite `hz` using `[← SetLike.mem_coe, ← hV.range_fromSpec]`. Conclude with `hz`.
-/
private lemma exists_fromSpec_eq_of_mem {V : W.Opens} (hV : IsAffineOpen V) {z : W} (hz : z ∈ V) :
    ∃ P : PrimeSpectrum Γ(W, V), hV.fromSpec P = z := by
  rw [← SetLike.mem_coe, ← hV.range_fromSpec] at hz
  exact hz

/- English proof (translation)
Rewrite using `[SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) (fromSpec_mem_of_isAffineOpen' hU P), hZU, fromSpec_mem_zeroLocus_iff_subset, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]`. Use `haveI := P.isPrime`. Conclude with `Ideal.IsPrime.prod_mem_iff`.
-/
private lemma supp_lemma_5 (hZU : Z.ideal ⟨U, hU⟩ = Ideal.span {∏ i ∈ J, f i})
    (P : PrimeSpectrum Γ(W, U)) :
    hU.fromSpec P ∈ (Z.support : Set W) ↔ ∃ i ∈ J, f i ∈ P.asIdeal := by
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) (fromSpec_mem_of_isAffineOpen' hU P),
    hZU, fromSpec_mem_zeroLocus_iff_subset, SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
  haveI := P.isPrime
  exact Ideal.IsPrime.prod_mem_iff

/- English proof (translation)
Conclude with `(fromSpec_mem_zeroLocus_iff_subset hU {f i} (q i)).2 (Set.singleton_subset_iff.2 (hq.2.1 i))`.
-/
theorem fromSpec_mem_zeroLocus (hq : ParPrimes hU hy f q) (i : Fin n) :
    hU.fromSpec (q i) ∈ W.zeroLocus {f i} := by
  exact (fromSpec_mem_zeroLocus_iff_subset hU {f i} (q i)).2 (Set.singleton_subset_iff.2 (hq.2.1 i))

/- English proof (translation)
Establish `h` using `(fromSpec_specializes_iff_le hU (q i) (hU.primeIdealOf ⟨y, hy⟩)).2 (hq.1 i)`. Rewrite `h` using `[hU.fromSpec_primeIdealOf]`. Then use the resulting hypothesis.
-/
theorem fromSpec_specializes (hq : ParPrimes hU hy f q) (i : Fin n) : hU.fromSpec (q i) ⤳ y := by
  have h := (fromSpec_specializes_iff_le hU (q i) (hU.primeIdealOf ⟨y, hy⟩)).2 (hq.1 i)
  rwa [hU.fromSpec_primeIdealOf] at h

/- English proof (translation)
Establish `hxs : hU.fromSpec (q i) ∈ (Z.support : Set W)` using `(supp_lemma_5 hZU (q i)).2 ⟨i, hi, hq.2.1 i⟩`. Establish `hsub : closure {hU.fromSpec (q i)} ⊆ (Z.support : Set W)` using `Z.support.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hxs)`. Use `⟨⟨isIrreducible_singleton.closure, hsub⟩, fun C hC hle => ?_⟩` and prove the remaining obligations. Take `⟨hCirr, hCsub⟩` from `hC`. Establish `hK` using `hCirr.closure.isGenericPoint_genericPoint isClosed_closure`.

Generalize the expression as in `hCirr.closure.genericPoint = η at hK`. Establish `hxK : hU.fromSpec (q i) ∈ closure C` using `subset_closure (hle (subset_closure (Set.mem_singleton _)))`. Establish `hηx : η ⤳ hU.fromSpec (q i)` using `hK.specializes hxK`. Take `⟨P, hP⟩` from `exists_fromSpec_eq_of_mem hU (hηx.mem_open U.isOpen (fromSpec_mem_of_isAffineOpen' hU (q i)))`. Establish `hPq : P ≤ q i`.

Rewrite using `[← fromSpec_specializes_iff_le hU, hP]`. Conclude with `hηx`. Establish `hηs : hU.fromSpec P ∈ (Z.support : Set W)`. Rewrite using `[hP]`. Conclude with `Z.support.isClosed.closure_subset_iff.2 hCsub hK.mem`.

Take `⟨j, hj, hfj⟩` from `(supp_lemma_5 hZU P).1 hηs`. Establish `hqj : q j ≤ P` using `(hq.2.2.1 j P (le_trans hPq (hq.1 i))).1 hfj`. Establish `hji : j = i` using `hq.2.2.2 i j ((hqj.trans hPq) (hq.2.1 j))`. Rewrite `hqj` using `[hji]`. Establish `hPe : P = q i` using `le_antisymm hPq hqj`.

Establish `hK' : closure {η} = closure C` using `hK`. Rewrite `hK'` using `[← hP, hPe]`. Rewrite using `[hK']`. Conclude with `subset_closure`.
-/
theorem closure_fromSpec_mem_compsH (hq : ParPrimes hU hy f q)
    (hZU : Z.ideal ⟨U, hU⟩ = Ideal.span {∏ i ∈ J, f i}) {i : Fin n} (hi : i ∈ J) :
    closure {hU.fromSpec (q i)} ∈ compsH (Z.support : Set W) := by
  have hxs : hU.fromSpec (q i) ∈ (Z.support : Set W) := (supp_lemma_5 hZU (q i)).2 ⟨i, hi, hq.2.1 i⟩
  have hsub : closure {hU.fromSpec (q i)} ⊆ (Z.support : Set W) :=
    Z.support.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hxs)
  refine ⟨⟨isIrreducible_singleton.closure, hsub⟩, fun C hC hle => ?_⟩
  obtain ⟨hCirr, hCsub⟩ := hC
  have hK := hCirr.closure.isGenericPoint_genericPoint isClosed_closure
  generalize hCirr.closure.genericPoint = η at hK
  have hxK : hU.fromSpec (q i) ∈ closure C := subset_closure (hle (subset_closure (Set.mem_singleton _)))
  have hηx : η ⤳ hU.fromSpec (q i) := hK.specializes hxK
  obtain ⟨P, hP⟩ := exists_fromSpec_eq_of_mem hU (hηx.mem_open U.isOpen (fromSpec_mem_of_isAffineOpen' hU (q i)))
  have hPq : P ≤ q i := by
    rw [← fromSpec_specializes_iff_le hU, hP]
    exact hηx

  have hηs : hU.fromSpec P ∈ (Z.support : Set W) := by
    rw [hP]
    exact Z.support.isClosed.closure_subset_iff.2 hCsub hK.mem
  obtain ⟨j, hj, hfj⟩ := (supp_lemma_5 hZU P).1 hηs
  have hqj : q j ≤ P := (hq.2.2.1 j P (le_trans hPq (hq.1 i))).1 hfj
  have hji : j = i := hq.2.2.2 i j ((hqj.trans hPq) (hq.2.1 j))
  rw [hji] at hqj
  have hPe : P = q i := le_antisymm hPq hqj
  have hK' : closure {η} = closure C := hK
  rw [← hP, hPe] at hK'
  rw [hK']
  exact subset_closure

/- English proof (translation)
Establish `hCcl` using `isClosed_of_mem_compsH Z.support.isClosed hC`. Establish `hK` using `hC.1.1.isGenericPoint_genericPoint hCcl`. Generalize the expression as in `hC.1.1.genericPoint = η at hK`. Establish `hηy : η ⤳ y` using `hK.specializes hyC`. Take `⟨P, hP⟩` from `exists_fromSpec_eq_of_mem hU (hηy.mem_open U.isOpen hy)`.

Establish `hPy : P ≤ hU.primeIdealOf ⟨y, hy⟩`. Rewrite using `[← fromSpec_specializes_iff_le hU, hP, hU.fromSpec_primeIdealOf]`. Conclude with `hηy`. Establish `hηs : hU.fromSpec P ∈ (Z.support : Set W)`. Rewrite using `[hP]`.

Conclude with `hC.1.2 hK.mem`. Take `⟨i, hi, hfi⟩` from `(supp_lemma_5 hZU P).1 hηs`. Establish `hqi : q i ≤ P` using `(hq.2.2.1 i P hPy).1 hfi`. Use `⟨i, hi, ?_⟩` and prove the remaining obligations. Establish `hmem` using `closure_fromSpec_mem_compsH hq hZU hi`.

Establish `hsub : C ⊆ closure {hU.fromSpec (q i)}`. Establish `hK' : closure {η} = C` using `hK`. Rewrite using `[← hK']`. Use `closure_minimal ?_ isClosed_closure` and prove the remaining obligations. Rewrite using `[Set.singleton_subset_iff, ← hP, ← specializes_iff_mem_closure]`.

Conclude with `(fromSpec_specializes_iff_le hU _ _).2 hqi`. Conclude with `le_antisymm hsub (hC.2 hmem.1 hsub)`.
-/
theorem comp_eq_closure (hq : ParPrimes hU hy f q)
    (hZU : Z.ideal ⟨U, hU⟩ = Ideal.span {∏ i ∈ J, f i}) {C : Set W}
    (hC : C ∈ compsH (Z.support : Set W)) (hyC : y ∈ C) :
    ∃ i ∈ J, C = closure {hU.fromSpec (q i)} := by
  have hCcl := isClosed_of_mem_compsH Z.support.isClosed hC
  have hK := hC.1.1.isGenericPoint_genericPoint hCcl
  generalize hC.1.1.genericPoint = η at hK
  have hηy : η ⤳ y := hK.specializes hyC
  obtain ⟨P, hP⟩ := exists_fromSpec_eq_of_mem hU (hηy.mem_open U.isOpen hy)
  have hPy : P ≤ hU.primeIdealOf ⟨y, hy⟩ := by
    rw [← fromSpec_specializes_iff_le hU, hP, hU.fromSpec_primeIdealOf]
    exact hηy
  have hηs : hU.fromSpec P ∈ (Z.support : Set W) := by
    rw [hP]
    exact hC.1.2 hK.mem
  obtain ⟨i, hi, hfi⟩ := (supp_lemma_5 hZU P).1 hηs
  have hqi : q i ≤ P := (hq.2.2.1 i P hPy).1 hfi
  refine ⟨i, hi, ?_⟩
  have hmem := closure_fromSpec_mem_compsH hq hZU hi
  have hsub : C ⊆ closure {hU.fromSpec (q i)} := by
    have hK' : closure {η} = C := hK
    rw [← hK']
    refine closure_minimal ?_ isClosed_closure
    rw [Set.singleton_subset_iff, ← hP, ← specializes_iff_mem_closure]
    exact (fromSpec_specializes_iff_le hU _ _).2 hqi
  exact le_antisymm hsub (hC.2 hmem.1 hsub)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hC, hyC, hirr, -, hgz⟩`. Take `⟨j, -, rfl⟩` from `comp_eq_closure hq hZU hC hyC`. Rewrite `hgz` using `[gp_closure_singleton hirr]`. Establish `hfi : f i ∈ (q j).asIdeal` using `Set.singleton_subset_iff.1 ((fromSpec_mem_zeroLocus_iff_subset hU {f i} (q j)).1 hgz)`.

Rewrite using `[hq.2.2.2 j i hfi]`. Introduce and unpack `rfl`. Use `⟨closure_fromSpec_mem_compsH hq hZU hi, specializes_iff_mem_closure.1 (fromSpec_specializes hq i), isIrreducible_singleton.closure, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[gp_closure_singleton]`. Conclude with `fromSpec_mem_of_isAffineOpen' hU _`.

Rewrite using `[gp_closure_singleton]`. Conclude with `fromSpec_mem_zeroLocus hq i`.
-/
theorem isBranch_iff (hq : ParPrimes hU hy f q)
    (hZU : Z.ideal ⟨U, hU⟩ = Ideal.span {∏ i ∈ J, f i}) {i : Fin n} (hi : i ∈ J) (C : Set W) :
    IsBranchH (Z.support : Set W) (f i) y C ↔ C = closure {hU.fromSpec (q i)} := by
  constructor
  · rintro ⟨hC, hyC, hirr, -, hgz⟩
    obtain ⟨j, -, rfl⟩ := comp_eq_closure hq hZU hC hyC
    rw [gp_closure_singleton hirr] at hgz
    have hfi : f i ∈ (q j).asIdeal := Set.singleton_subset_iff.1 ((fromSpec_mem_zeroLocus_iff_subset hU {f i} (q j)).1 hgz)
    rw [hq.2.2.2 j i hfi]
  · rintro rfl
    refine ⟨closure_fromSpec_mem_compsH hq hZU hi,
      specializes_iff_mem_closure.1 (fromSpec_specializes hq i), isIrreducible_singleton.closure, ?_, ?_⟩
    · rw [gp_closure_singleton]
      exact fromSpec_mem_of_isAffineOpen' hU _
    · rw [gp_closure_singleton]
      exact fromSpec_mem_zeroLocus hq i

end Br

/- English proof (translation)
Rewrite using `[Set.sUnion_eq_biUnion]`. Conclude with `Set.Finite.isClosed_biUnion ((compsH_finite T).subset fun D hD => hD.1) fun D hD => isClosed_of_mem_compsH hT hD.1`.
-/
theorem isClosed_sUnion_compsH_not [IsNoetherian W] {T : Set W} (hT : IsClosed T) (y : W) :
    IsClosed (⋃₀ {D | D ∈ compsH T ∧ y ∉ D}) := by
  rw [Set.sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion ((compsH_finite T).subset fun D hD => hD.1)
    fun D hD => isClosed_of_mem_compsH hT hD.1

/- English proof (translation)
Take `⟨q, hq⟩` from `exists_parPrimes U.2 hy f hrsp`. Conclude with `⟨closure {U.2.fromSpec (q i)}, (isBranch_iff hq hZU hi _).2 rfl, fun C hC => (isBranch_iff hq hZU hi C).1 hC⟩`.
-/
theorem existsUnique_branchH [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) (i : Fin n) (hi : i ∈ J) :
    ∃! C, IsBranchH (Z.support : Set W) (f i) y C := by
  obtain ⟨q, hq⟩ := exists_parPrimes U.2 hy f hrsp
  exact ⟨closure {U.2.fromSpec (q i)}, (isBranch_iff hq hZU hi _).2 rfl,
    fun C hC => (isBranch_iff hq hZU hi C).1 hC⟩

/- English proof (translation)
Take `⟨q, hq⟩` from `exists_parPrimes U.2 hy f hrsp`. Rewrite using `[(isBranch_iff hq hZU hi C).1 hC, (isBranch_iff hq hZU hj C').1 hC']`. Introduce `heq`. Establish `hx` using `eq_of_closure_singleton_eq heq`. Establish `h2` using `fromSpec_mem_zeroLocus hq j`.

Rewrite `h2` using `[← hx]`. Establish `hfj : f j ∈ (q i).asIdeal` using `Set.singleton_subset_iff.1 ((fromSpec_mem_zeroLocus_iff_subset U.2 {f j} (q i)).1 h2)`. Conclude with `hij (hq.2.2.2 i j hfj).symm`.
-/
theorem branch_neH [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) {i j : Fin n} (hi : i ∈ J) (hj : j ∈ J)
    (hij : i ≠ j) {C C' : Set W} (hC : IsBranchH (Z.support : Set W) (f i) y C)
    (hC' : IsBranchH (Z.support : Set W) (f j) y C') : C ≠ C' := by
  obtain ⟨q, hq⟩ := exists_parPrimes U.2 hy f hrsp
  rw [(isBranch_iff hq hZU hi C).1 hC, (isBranch_iff hq hZU hj C').1 hC']
  intro heq
  have hx := eq_of_closure_singleton_eq heq
  have h2 := fromSpec_mem_zeroLocus hq j
  rw [← hx] at h2
  have hfj : f j ∈ (q i).asIdeal := Set.singleton_subset_iff.1 ((fromSpec_mem_zeroLocus_iff_subset U.2 {f j} (q i)).1 h2)
  exact hij (hq.2.2.2 i j hfj).symm

/- English proof (translation)
Take `⟨q, hq⟩` from `exists_parPrimes U.2 hy f hrsp`. Establish `hB : IsClosed (⋃₀ {D | D ∈ compsH (Z.support : Set W) ∧ y ∉ D})` using `isClosed_sUnion_compsH_not Z.support.isClosed y`. Establish `hBf : IsClosed (⋃ i, ⋃₀ {D | D ∈ compsH (W.zeroLocus {f i}) ∧ y ∉ D})` using `isClosed_iUnion_of_finite (fun i => isClosed_sUnion_compsH_not (W.zeroLocus_isClosed _) y)`. Set `O : W.Opens` to `⟨(U.1 : Set W) ∩ (⋃₀ {D | D ∈ compsH (Z.support : Set W) ∧ y ∉ D})ᶜ ∩ (⋃ i, ⋃₀ {D | D ∈ compsH (W.zeroLocus {f i}) ∧ y ∉ D})ᶜ, (U.1.isOpen.inter hB.isOpen_compl).inter hBf.isOpen_compl⟩`. Establish `hyB : y ∉ ⋃₀ {D | D ∈ compsH (Z.support : Set W) ∧ y ∉ D}`.

Introduce and unpack `⟨D, ⟨-, hyD⟩, hyD'⟩`. Conclude with `hyD hyD'`. Establish `hyBf : y ∉ ⋃ i, ⋃₀ {D | D ∈ compsH (W.zeroLocus {f i}) ∧ y ∉ D}`. Rewrite using `[Set.mem_iUnion]`. Introduce and unpack `⟨i, D, ⟨-, hyD⟩, hyD'⟩`.

Conclude with `hyD hyD'`. Use `⟨O, ⟨⟨hy, hyB⟩, hyBf⟩, fun z hz => hz.1.1, ?_⟩` and prove the remaining obligations. Introduce `C hC`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hzC, hzO⟩`. Establish `hyC : y ∈ C`. Assume the negation of the conclusion as `hyC`. Conclude with `hzO.1.2 ⟨C, ⟨hC, hyC⟩, hzC⟩`. Take `⟨i, hi, rfl⟩` from `comp_eq_closure hq hZU hC hyC`.

Use `⟨hzO, i, hi, (isBranch_iff hq hZU hi _).2 rfl, ?_⟩` and prove the remaining obligations. Conclude with `closure_minimal (Set.singleton_subset_iff.2 (fromSpec_mem_zeroLocus hq i)) (W.zeroLocus_isClosed _) hzC`. Introduce and unpack `⟨hzO, i, hi, hbr, hzf⟩`. Use `⟨?_, hzO⟩` and prove the remaining obligations. Rewrite using `[(isBranch_iff hq hZU hi C).1 hbr]`.

Establish `hzE : z ∈ ⋃₀ compsH (W.zeroLocus {f i})`. Rewrite using `[sUnion_compsH]`. Conclude with `hzf`. Take `⟨E, hE, hzE⟩` from `hzE`. Establish `hyE : y ∈ E`.

Assume the negation of the conclusion as `hyE`. Conclude with `hzO.2 (Set.mem_iUnion.2 ⟨i, E, ⟨hE, hyE⟩, hzE⟩)`. Establish `hK` using `hE.1.1.isGenericPoint_genericPoint (isClosed_of_mem_compsH (W.zeroLocus_isClosed _) hE)`. Generalize the expression as in `hE.1.1.genericPoint = ζ at hK`. Establish `hζy : ζ ⤳ y` using `hK.specializes hyE`.

Take `⟨P, hP⟩` from `exists_fromSpec_eq_of_mem U.2 (hζy.mem_open U.1.isOpen hy)`. Establish `hPy : P ≤ U.2.primeIdealOf ⟨y, hy⟩`. Rewrite using `[← fromSpec_specializes_iff_le U.2, hP, U.2.fromSpec_primeIdealOf]`. Conclude with `hζy`. Establish `hζf : U.2.fromSpec P ∈ W.zeroLocus {f i}`.

Rewrite using `[hP]`. Conclude with `hE.1.2 hK.mem`. Establish `hfP : f i ∈ P.asIdeal` using `Set.singleton_subset_iff.1 ((fromSpec_mem_zeroLocus_iff_subset U.2 {f i} P).1 hζf)`. Establish `h1 : U.2.fromSpec (q i) ⤳ ζ`. Rewrite using `[← hP]`.

Conclude with `(fromSpec_specializes_iff_le U.2 _ _).2 ((hq.2.2.1 i P hPy).1 hfP)`. Conclude with `specializes_iff_mem_closure.1 (h1.trans (hK.specializes hzE))`.
-/
theorem exists_open_compsH [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) :
    ∃ O : W.Opens, y ∈ O ∧ O ≤ U.1 ∧ ∀ C ∈ compsH (Z.support : Set W),
      C ∩ O = {z ∈ (O : Set W) | ∃ i ∈ J, IsBranchH (Z.support : Set W) (f i) y C ∧
        z ∈ W.zeroLocus {f i}} := by
  obtain ⟨q, hq⟩ := exists_parPrimes U.2 hy f hrsp

  have hB : IsClosed (⋃₀ {D | D ∈ compsH (Z.support : Set W) ∧ y ∉ D}) :=
    isClosed_sUnion_compsH_not Z.support.isClosed y
  have hBf : IsClosed (⋃ i, ⋃₀ {D | D ∈ compsH (W.zeroLocus {f i}) ∧ y ∉ D}) :=
    isClosed_iUnion_of_finite (fun i => isClosed_sUnion_compsH_not (W.zeroLocus_isClosed _) y)
  let O : W.Opens := ⟨(U.1 : Set W) ∩ (⋃₀ {D | D ∈ compsH (Z.support : Set W) ∧ y ∉ D})ᶜ ∩
      (⋃ i, ⋃₀ {D | D ∈ compsH (W.zeroLocus {f i}) ∧ y ∉ D})ᶜ,
    (U.1.isOpen.inter hB.isOpen_compl).inter hBf.isOpen_compl⟩
  have hyB : y ∉ ⋃₀ {D | D ∈ compsH (Z.support : Set W) ∧ y ∉ D} := by
    rintro ⟨D, ⟨-, hyD⟩, hyD'⟩
    exact hyD hyD'
  have hyBf : y ∉ ⋃ i, ⋃₀ {D | D ∈ compsH (W.zeroLocus {f i}) ∧ y ∉ D} := by
    rw [Set.mem_iUnion]
    rintro ⟨i, D, ⟨-, hyD⟩, hyD'⟩
    exact hyD hyD'
  refine ⟨O, ⟨⟨hy, hyB⟩, hyBf⟩, fun z hz => hz.1.1, ?_⟩
  intro C hC
  ext z
  constructor
  · rintro ⟨hzC, hzO⟩
    have hyC : y ∈ C := by
      by_contra hyC
      exact hzO.1.2 ⟨C, ⟨hC, hyC⟩, hzC⟩
    obtain ⟨i, hi, rfl⟩ := comp_eq_closure hq hZU hC hyC
    refine ⟨hzO, i, hi, (isBranch_iff hq hZU hi _).2 rfl, ?_⟩
    exact closure_minimal (Set.singleton_subset_iff.2 (fromSpec_mem_zeroLocus hq i))
      (W.zeroLocus_isClosed _) hzC
  · rintro ⟨hzO, i, hi, hbr, hzf⟩
    refine ⟨?_, hzO⟩
    rw [(isBranch_iff hq hZU hi C).1 hbr]
    have hzE : z ∈ ⋃₀ compsH (W.zeroLocus {f i}) := by
      rw [sUnion_compsH]
      exact hzf
    obtain ⟨E, hE, hzE⟩ := hzE
    have hyE : y ∈ E := by
      by_contra hyE
      exact hzO.2 (Set.mem_iUnion.2 ⟨i, E, ⟨hE, hyE⟩, hzE⟩)
    have hK := hE.1.1.isGenericPoint_genericPoint (isClosed_of_mem_compsH (W.zeroLocus_isClosed _) hE)
    generalize hE.1.1.genericPoint = ζ at hK
    have hζy : ζ ⤳ y := hK.specializes hyE
    obtain ⟨P, hP⟩ := exists_fromSpec_eq_of_mem U.2 (hζy.mem_open U.1.isOpen hy)
    have hPy : P ≤ U.2.primeIdealOf ⟨y, hy⟩ := by
      rw [← fromSpec_specializes_iff_le U.2, hP, U.2.fromSpec_primeIdealOf]
      exact hζy
    have hζf : U.2.fromSpec P ∈ W.zeroLocus {f i} := by
      rw [hP]
      exact hE.1.2 hK.mem
    have hfP : f i ∈ P.asIdeal := Set.singleton_subset_iff.1 ((fromSpec_mem_zeroLocus_iff_subset U.2 {f i} P).1 hζf)
    have h1 : U.2.fromSpec (q i) ⤳ ζ := by
      rw [← hP]
      exact (fromSpec_specializes_iff_le U.2 _ _).2 ((hq.2.2.1 i P hPy).1 hfP)
    exact specializes_iff_mem_closure.1 (h1.trans (hK.specializes hzE))

end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
