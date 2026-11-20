import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.RestValBdG

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

/- English proof (translation)
Proceed by induction on `x using WithTop.recTopCoe with`. Consider the case `top => exact le_top`. Consider the case `coe k => exact WithTop.coe_le_coe.2 (Int.ceil_le.2 (h k rfl))`.
-/
theorem ceil_le_of_geZ {x : WithTop ℤ} {t : ℝ} (h : geZ x t) : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe k => exact WithTop.coe_le_coe.2 (Int.ceil_le.2 (h k rfl))

section Tr

variable {O : Type} [CommRing O] {J : ℕ} {n : ℕ}

/- English proof (translation)
Rewrite `hX` using `[MvPolynomial.supported_eq_range_rename]`. Take `⟨Y, hY⟩` from `hX`. Rewrite using `[← hY]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_rename]`. Use `congrArg (fun f => (rename (R := O) f) Y) ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `v`. Take `⟨⟨⟨a, b⟩, c⟩, hv⟩` from `v`. Simplify using `only [Set.mem_setOf_eq] at hv`. Substitute `hv` using the available equality. Both sides reduce to the same expression.
-/
theorem back_rename (j : ZMod J) (X : MvPolynomial ((ZMod J × ℤ) × Fin n) O)
    (hX : X ∈ supported O {v : (ZMod J × ℤ) × Fin n | v.1.1 = j}) :
    rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) (rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) X) = X := by
  rw [MvPolynomial.supported_eq_range_rename] at hX
  obtain ⟨Y, hY⟩ := hX
  rw [← hY]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_rename]
  refine congrArg (fun f => (rename (R := O) f) Y) ?_
  funext v
  obtain ⟨⟨⟨a, b⟩, c⟩, hv⟩ := v
  simp only [Set.mem_setOf_eq] at hv
  subst hv
  rfl

/- English proof (translation)
Establish `h : (twistSub LL S k).comp (rename (R` using `R) (fun v : κ × Fin n => (g v.1, v.2))).toRingHom = (rename (R := GLLaurent R n) (fun v : κ × Fin n => (g v.1, v.2))).toRingHom.comp (twistSub LK T k) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[twistSub]`. Introduce `v`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, twistSub, eval₂Hom_X', hS, hvec]`. Apply the tactic sequence `split_ifs <;> simp [map_sum]`. Conclude with `congrArg (fun φ => φ X') h`.
-/
private theorem twistSub_rename_eq {R : Type} [CommRing R] {ι κ : Type} {n : ℕ} (LL : Letters ι) (LK : Letters κ)
    (S : Set ι) (T : Set κ) (g : κ → ι) (hvec : ∀ y, LL.vec (g y) = LK.vec y) (hS : ∀ y, g y ∈ S ↔ y ∈ T)
    (k : Fin n) (X' : MvPolynomial (κ × Fin n) R) :
    twistSub LL S k (rename (R := R) (fun v : κ × Fin n => (g v.1, v.2)) X') =
      rename (R := GLLaurent R n) (fun v : κ × Fin n => (g v.1, v.2)) (twistSub LK T k X') := by
  have h : (twistSub LL S k).comp (rename (R := R) (fun v : κ × Fin n => (g v.1, v.2))).toRingHom =
      (rename (R := GLLaurent R n) (fun v : κ × Fin n => (g v.1, v.2))).toRingHom.comp (twistSub LK T k) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [twistSub]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, twistSub,
        eval₂Hom_X', hS, hvec]
      split_ifs <;> simp [map_sum]
  exact congrArg (fun φ => φ X') h

/- English proof (translation)
Establish `hinj : Function.Injective (fun v : κ × Fin n => (g v.1, v.2))` using `fun a b h => by`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext (hg h.1) h.2`. Unfold `sDegs`. Rewrite using `[twistSub_rename_eq LL LK S T g hvec hS k X', MvPolynomial.support_rename_of_injective hinj, Finset.image_biUnion]`.

Simplify using `only [MvPolynomial.coeff_rename_mapDomain _ hinj]`.
-/
private theorem sDegs_rename_eq_of_injective {R : Type} [CommRing R] {ι κ : Type} {n : ℕ} (LL : Letters ι) (LK : Letters κ)
    (S : Set ι) (T : Set κ) (g : κ → ι) (hg : Function.Injective g) (hvec : ∀ y, LL.vec (g y) = LK.vec y)
    (hS : ∀ y, g y ∈ S ↔ y ∈ T) (k : Fin n) (X' : MvPolynomial (κ × Fin n) R) :
    sDegs LL S k (rename (fun v : κ × Fin n => (g v.1, v.2)) X') = sDegs LK T k X' := by
  have hinj : Function.Injective (fun v : κ × Fin n => (g v.1, v.2)) := fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hg h.1) h.2
  unfold sDegs
  rw [twistSub_rename_eq LL LK S T g hvec hS k X', MvPolynomial.support_rename_of_injective hinj,
    Finset.image_biUnion]
  simp only [MvPolynomial.coeff_rename_mapDomain _ hinj]

/- English proof (translation)
Establish `h1 : ∀ k, sDegs (LSeg J) {i | i.1 = j ∧ P i.2} k (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') = sDegs LZ {y | P y} k X'` using `fun k => sDegs_rename_eq_of_injective (LSeg J) LZ _ _ (fun y : ℤ => (j, y)) (fun a b h => (Prod.mk.inj h).2) (fun y => rfl) (fun y => by simp) k X'`. Conclude with `⟨by simp only [valS, h1], by simp only [lam1S, h1]⟩`.
-/
theorem seg_val [NeZero n] (j : ZMod J) (X' : MvPolynomial (ℤ × Fin n) O) (P : ℤ → Prop) :
    valS (LSeg J) {i | i.1 = j ∧ P i.2} (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') = valS LZ {y | P y} X' ∧
    lam1S (LSeg J) {i | i.1 = j ∧ P i.2} (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') = lam1S LZ {y | P y} X' := by
  have h1 : ∀ k, sDegs (LSeg J) {i | i.1 = j ∧ P i.2} k (rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) X') =
      sDegs LZ {y | P y} k X' := fun k =>
    sDegs_rename_eq_of_injective (LSeg J) LZ _ _ (fun y : ℤ => (j, y)) (fun a b h => (Prod.mk.inj h).2) (fun y => rfl)
      (fun y => by simp) k X'
  exact ⟨by simp only [valS, h1], by simp only [lam1S, h1]⟩

end Tr

section XGs

variable {O : Type} [CommRing O] [IsDomain O] {ι G : Type} (π : ι → G) {n : ℕ} [NeZero n] (LL : Letters ι)
  (Cv Cl : G → Set (Set ι × ℤ)) (F : MvPolynomial (ι × Fin n) O)

/- English proof (translation)
Rewrite using `[MvPolynomial.mem_supported]`. Introduce `v hv`. Take `⟨d, hd, hvd⟩` from `(MvPolynomial.mem_vars v).mp (Finset.mem_coe.mp hv)`. Take `⟨mo', -, rfl⟩` from `Finset.mem_image.mp (hx.1 d hd)`. Rewrite `hvd` using `[Finsupp.mem_support_iff]`.

Use `show π v.1 = j`. Assume the negation of the conclusion as `hne`. Conclude with `hvd (by simp [partOf, Finsupp.filter_apply, hne])`.
-/
theorem XG_supported (j : G) (x : MvPolynomial (ι × Fin n) O) (hx : x ∈ XG π LL Cv Cl F j) :
    x ∈ supported O {v : ι × Fin n | π v.1 = j} := by
  rw [MvPolynomial.mem_supported]
  intro v hv
  obtain ⟨d, hd, hvd⟩ := (MvPolynomial.mem_vars v).mp (Finset.mem_coe.mp hv)
  obtain ⟨mo', -, rfl⟩ := Finset.mem_image.mp (hx.1 d hd)
  rw [Finsupp.mem_support_iff] at hvd
  show π v.1 = j
  by_contra hne
  exact hvd (by simp [partOf, Finsupp.filter_apply, hne])

/- English proof (translation)
The claim follows from `Finset.mem_image.1 (hx.1 mo hmo)`.
-/
theorem XG_part (j : G) (x : MvPolynomial (ι × Fin n) O) (hx : x ∈ XG π LL Cv Cl F j) (mo : ι × Fin n →₀ ℕ)
    (hmo : mo ∈ x.support) : ∃ mo' ∈ F.support, partOf π j mo' = mo :=
  Finset.mem_image.1 (hx.1 mo hmo)

/- English proof (translation)
Unfold `partOf`. Conclude with `Finsupp.filter_apply_pos _ _ hv`.
-/
theorem partOf_apply_pos (j : G) (mo : ι × Fin n →₀ ℕ) (v : ι × Fin n) (hv : π v.1 = j) : partOf π j mo v = mo v := by
  unfold partOf
  exact Finsupp.filter_apply_pos _ _ hv

end XGs

/- English proof (translation)
Establish `hc` using `MvPolynomial.mem_support_iff.mp h`. Simplify using `only [homComp, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter] at hc`. Use `split_ifs at hc with hm`. Conclude with `hm`. Conclude with `absurd rfl hc`.
-/
theorem support_homComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} (δ : ι → ℕ) (F : MvPolynomial (ι × Fin n) R)
    (mo : ι × Fin n →₀ ℕ) (h : mo ∈ (homComp δ F).support) : mo ∈ F.support ∧ ∀ i, multideg mo i = δ i := by
  have hc := MvPolynomial.mem_support_iff.mp h
  simp only [homComp, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter] at hc
  split_ifs at hc with hm
  · exact hm
  · exact absurd rfl hc

section Ph

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] (K : ℕ) {J : ℕ}

/- English proof (translation)
Simplify using `only [PhiPl, phSeg, plEmb, MvPolynomial.aeval_rename, Function.comp_def]`.
-/
theorem PhiPl_seg (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) :
    PhiPl Fr p O K J (rename (fun v : ℤ × Fin r => ((j, v.1), v.2)) A) = phSeg O K p Fr (segZ j) (plEmb O r K A) := by
  simp only [PhiPl, phSeg, plEmb, MvPolynomial.aeval_rename, Function.comp_def]

/- English proof (translation)
Simplify using `only [PhiNo, phSeg, nmEmb, MvPolynomial.aeval_rename, Function.comp_def]`.
-/
theorem PhiNo_seg (j : ZMod J) (B : MvPolynomial (ℤ × Fin K) O) :
    PhiNo Fr p O K J (rename (fun v : ℤ × Fin K => ((j, v.1), v.2)) B) = phSeg O K p Fr (segZ j) (nmEmb O r K B) := by
  simp only [PhiNo, phSeg, nmEmb, MvPolynomial.aeval_rename, Function.comp_def]

end Ph

/- English proof (translation)
Simplify using `only [segZ, Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht]`.
-/
theorem segZ_cast {J : ℕ} [NeZero J] (t : ℕ) (ht : t < J) : segZ (((t : ℤ) : ZMod J)) = (t : ℤ) := by
  simp only [segZ, Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht]

/- English proof (translation)
Simplify using `only [segZ, Int.cast_natCast, ZMod.natCast_zmod_val]`.
-/
theorem cast_segZ {J : ℕ} [NeZero J] (j : ZMod J) : ((segZ j : ℤ) : ZMod J) = j := by
  simp only [segZ, Int.cast_natCast, ZMod.natCast_zmod_val]

/- English proof (translation)
Use `symm`. Use `Finset.prod_nbij' (fun j => j.val) (fun t => (t : ZMod J)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `j _`. Simplify using `[ZMod.val_lt]`. Introduce `t _`.

Simplify using the standard rewrite rules. Introduce `j _`. Simplify using `[ZMod.natCast_zmod_val]`. Introduce `t ht`. Simplify using `only [Finset.mem_coe, Finset.mem_range] at ht`.

Simplify using `[ZMod.val_natCast, Nat.mod_eq_of_lt ht]`. Introduce `j _`. Both sides reduce to the same expression.
-/
theorem prod_range_zmod {M : Type} [CommMonoid M] {J : ℕ} [NeZero J] (g : ℤ → M) :
    ∏ t ∈ Finset.range J, g (t : ℤ) = ∏ j : ZMod J, g (segZ j) := by
  symm
  refine Finset.prod_nbij' (fun j => j.val) (fun t => (t : ZMod J)) ?_ ?_ ?_ ?_ ?_
  · intro j _
    simp [ZMod.val_lt]
  · intro t _
    simp
  · intro j _
    simp [ZMod.natCast_zmod_val]
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_range] at ht
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt ht]
  · intro j _
    rfl

/- English proof (translation)
Rewrite using `[Finset.sum_mul_sum, ← Fintype.sum_prod_type']`. Use `Fintype.sum_equiv finProdFinEquiv _ _ (fun p => ?_)` and prove the remaining obligations. Simplify using `[Finset.prod_mul_distrib]`.
-/
theorem sum_mul_sum_prod {M : Type} [CommRing M] {G : Type} [Fintype G] {N1 N2 : ℕ} (a : Fin N1 → G → M)
    (b : Fin N2 → G → M) :
    (∑ i, ∏ j, a i j) * (∑ i, ∏ j, b i j) =
      ∑ q : Fin (N1 * N2), ∏ j, (a (finProdFinEquiv.symm q).1 j * b (finProdFinEquiv.symm q).2 j) := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv finProdFinEquiv _ _ (fun p => ?_)
  simp [Finset.prod_mul_distrib]

section SegDec

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {J : ℕ} [NeZero J] {n : ℕ} [NeZero n]

/- English proof (translation)
Set `Cv' : ZMod J → Set (Set (ZMod J × ℤ) × ℤ)` to `fun j => (fun q : (ℤ → Prop) × ℤ => ({i : ZMod J × ℤ | i.1 = j ∧ q.1 i.2}, q.2)) '' Cv j`. Set `Cl' : ZMod J → Set (Set (ZMod J × ℤ) × ℤ)` to `fun j => (fun q : (ℤ → Prop) × ℤ => ({i : ZMod J × ℤ | i.1 = j ∧ q.1 i.2}, q.2)) '' Cl j`. Take `⟨N, A, hA', hF⟩` from `decGen (O := O) (Prod.fst : ZMod J × ℤ → ZMod J) (LSeg J) Cv' Cl' F hA hS (by`. Introduce and unpack `j q ⟨q0, -, rfl⟩ i hi`. Conclude with `hi.1)`.

Use the proof step `(by`. Introduce and unpack `j q ⟨q0, -, rfl⟩ i hi`. Conclude with `hi.1)`. Use the proof step `(by`. Introduce and unpack `j q ⟨q0, hq0, rfl⟩`.

Conclude with `hv j q0 hq0)`. Use the proof step `(by`. Introduce and unpack `j q ⟨q0, hq0, rfl⟩`. Conclude with `hl j q0 hq0)`. Establish `hback : ∀ i j, rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) (rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) (A i j)) = A i j` using `fun i j => back_rename j (A i j) (XG_supported Prod.fst (LSeg J) Cv' Cl' F j (A i j) (hA' i j))`.

Use `⟨N, fun i j => rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) (A i j), fun i j => ?_, ?_⟩` and prove the remaining obligations. Establish `hmem : A i j ∈ XG Prod.fst (LSeg J) Cv' Cl' F j` using `hA' i j`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `mo hmo`. Establish `hinj : Function.Injective (fun v : ℤ × Fin n => ((j, v.1), v.2))` using `fun a b h => by`.

Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext h.1.2 h.2`. Establish `h2 : Finsupp.mapDomain (fun v : ℤ × Fin n => ((j, v.1), v.2)) mo ∈ (A i j).support`. Rewrite using `[← hback i j, MvPolynomial.support_rename_of_injective hinj]`. Conclude with `Finset.mem_image_of_mem _ hmo`.

Take `⟨mo', hmo', he⟩` from `XG_part Prod.fst (LSeg J) Cv' Cl' F j (A i j) hmem _ h2`. Use `⟨mo', hmo', fun x c => ?_⟩` and prove the remaining obligations. Establish `h4 : partOf Prod.fst j mo' ((j, x), c) = Finsupp.mapDomain (fun v : ℤ × Fin n => ((j, v.1), v.2)) mo ((j, x), c)`. Rewrite using `[he]`. Rewrite `h4` using `[partOf_apply_pos Prod.fst j mo' ((j, x), c) rfl, Finsupp.mapDomain_apply hinj mo (x, c)]`.

Conclude with `h4.symm`. Introduce `q hq`. Establish `h3` using `hmem.2.1 _ ⟨q, hq, rfl⟩`. Simplify using `only at h3`. Rewrite `h3` using `[← hback i j, (seg_val j _ q.1).1]`.

Conclude with `h3`. Introduce `q hq`. Establish `h3` using `hmem.2.2 _ ⟨q, hq, rfl⟩`. Simplify using `only at h3`. Rewrite `h3` using `[← hback i j, (seg_val j _ q.1).2]`.

Conclude with `h3`. Use `conv_lhs => rw [hF]`. Use `Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `(hback i j).symm`.
-/
theorem seg_dec (hA : ATL) (hS : ValSlice) (F : MvPolynomial ((ZMod J × ℤ) × Fin n) O)
    (Cv Cl : ZMod J → Set ((ℤ → Prop) × ℤ))
    (hv : ∀ j, ∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤ valS (LSeg J) {i | i.1 = j ∧ q.1 i.2} F)
    (hl : ∀ j, ∀ q ∈ Cl j, lam1S (LSeg J) {i | i.1 = j ∧ q.1 i.2} F ≤ ((q.2 : ℤ) : WithBot ℤ)) :
    ∃ (N : ℕ) (A' : Fin N → ZMod J → MvPolynomial (ℤ × Fin n) O),
      (∀ i j, (∀ mo ∈ (A' i j).support, ∃ mo' ∈ F.support, ∀ x c, mo (x, c) = mo' ((j, x), c)) ∧
        (∀ q ∈ Cv j, ((q.2 : ℤ) : WithTop ℤ) ≤ valS LZ {y | q.1 y} (A' i j)) ∧
        (∀ q ∈ Cl j, lam1S LZ {y | q.1 y} (A' i j) ≤ ((q.2 : ℤ) : WithBot ℤ))) ∧
      F = ∑ i, ∏ j, rename (fun v : ℤ × Fin n => ((j, v.1), v.2)) (A' i j) := by
  classical
  let Cv' : ZMod J → Set (Set (ZMod J × ℤ) × ℤ) := fun j =>
    (fun q : (ℤ → Prop) × ℤ => ({i : ZMod J × ℤ | i.1 = j ∧ q.1 i.2}, q.2)) '' Cv j
  let Cl' : ZMod J → Set (Set (ZMod J × ℤ) × ℤ) := fun j =>
    (fun q : (ℤ → Prop) × ℤ => ({i : ZMod J × ℤ | i.1 = j ∧ q.1 i.2}, q.2)) '' Cl j
  obtain ⟨N, A, hA', hF⟩ := decGen (O := O) (Prod.fst : ZMod J × ℤ → ZMod J) (LSeg J) Cv' Cl' F hA hS
    (by
      rintro j q ⟨q0, -, rfl⟩ i hi
      exact hi.1)
    (by
      rintro j q ⟨q0, -, rfl⟩ i hi
      exact hi.1)
    (by
      rintro j q ⟨q0, hq0, rfl⟩
      exact hv j q0 hq0)
    (by
      rintro j q ⟨q0, hq0, rfl⟩
      exact hl j q0 hq0)
  have hback : ∀ i j, rename (fun v : ℤ × Fin n => ((j, v.1), v.2))
      (rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) (A i j)) = A i j := fun i j =>
    back_rename j (A i j) (XG_supported Prod.fst (LSeg J) Cv' Cl' F j (A i j) (hA' i j))
  refine ⟨N, fun i j => rename (fun v : (ZMod J × ℤ) × Fin n => (v.1.2, v.2)) (A i j), fun i j => ?_, ?_⟩
  · have hmem : A i j ∈ XG Prod.fst (LSeg J) Cv' Cl' F j := hA' i j
    refine ⟨?_, ?_, ?_⟩
    · intro mo hmo
      have hinj : Function.Injective (fun v : ℤ × Fin n => ((j, v.1), v.2)) := fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.2 h.2
      have h2 : Finsupp.mapDomain (fun v : ℤ × Fin n => ((j, v.1), v.2)) mo ∈ (A i j).support := by
        rw [← hback i j, MvPolynomial.support_rename_of_injective hinj]
        exact Finset.mem_image_of_mem _ hmo
      obtain ⟨mo', hmo', he⟩ := XG_part Prod.fst (LSeg J) Cv' Cl' F j (A i j) hmem _ h2
      refine ⟨mo', hmo', fun x c => ?_⟩
      have h4 : partOf Prod.fst j mo' ((j, x), c) =
          Finsupp.mapDomain (fun v : ℤ × Fin n => ((j, v.1), v.2)) mo ((j, x), c) := by
        rw [he]
      rw [partOf_apply_pos Prod.fst j mo' ((j, x), c) rfl,
        Finsupp.mapDomain_apply hinj mo (x, c)] at h4
      exact h4.symm
    · intro q hq
      have h3 := hmem.2.1 _ ⟨q, hq, rfl⟩
      dsimp only at h3
      rw [← hback i j, (seg_val j _ q.1).1] at h3
      exact h3
    · intro q hq
      have h3 := hmem.2.2 _ ⟨q, hq, rfl⟩
      dsimp only at h3
      rw [← hback i j, (seg_val j _ q.1).2] at h3
      exact h3
  · conv_lhs => rw [hF]
    refine Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    exact (hback i j).symm

end SegDec

end Formalism.MainNotions.Proposition5Numerics
