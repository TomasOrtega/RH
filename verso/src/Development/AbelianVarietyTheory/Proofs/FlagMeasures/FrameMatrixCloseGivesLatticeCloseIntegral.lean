import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularCloseToOneInverseCloseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingConjInverseAdjointCloseToOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPairingMatrixInvMulSelfStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFramesJointGramInvMulSelfStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCommonDenominatorForHermitianLatticeDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CloseOnCompletedLatticeOfCloseOnFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntCastIsUnitCompletionAlmostAllPlacesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameClose

section Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Rewrite using `[L.O_def]`. Conclude with `isIntegral_algebraMap (R := 𝒪[F]) (x := (⟨a, ha⟩ : 𝒪[F]))`.
-/
theorem algebraMap_mem (L : LocE F E) {a : F} (ha : a ∈ 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.O_def]
  exact isIntegral_algebraMap (R := 𝒪[F]) (x := (⟨a, ha⟩ : 𝒪[F]))

/- English proof (translation)
Establish `h' : ¬ valuation F a ≤ 1` using `h`. Use `show valuation F a⁻¹ ≤ 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h'))`.
-/
theorem inv_mem {a : F} (h : a ∉ 𝒪[F]) : a⁻¹ ∈ 𝒪[F] := by
  have h' : ¬ valuation F a ≤ 1 := h
  show valuation F a⁻¹ ≤ 1
  rw [map_inv₀]
  exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h'))

/- English proof (translation)
Introduce `i j`. Establish `h1 : ∑ i, (M i j * la i - la j * s i j) • g i = 0`. Establish `e1 : ∑ i, M i j • (la i • g i) = ∑ i, (M i j * la i) • g i` using `Finset.sum_congr rfl fun i _ => (smul_smul _ _ _)`. Establish `e2 : h (la j • g j) = ∑ i, (la j * s i j) • g i`. Rewrite using `[map_smul, hs j, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => (smul_smul _ _ _)`. Use `hM j` as an intermediate fact. Rewrite `this` using `[e1, e2]`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[this, sub_self]`.

Use `Fintype.linearIndependent_iff.1 hg _ h1 i` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem coord_scale {n r : ℕ} (g : Fin (r + 1) → Fin n → E) (hg : LinearIndependent E g)
    (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) (la : Fin (r + 1) → E) (s M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : ∀ j, h (g j) = ∑ i, s i j • g i) (hM : ∀ j, h (la j • g j) = ∑ i, M i j • (la i • g i)) :
    ∀ i j, M i j * la i = la j * s i j := by
  intro i j
  have h1 : ∑ i, (M i j * la i - la j * s i j) • g i = 0 := by
    have e1 : ∑ i, M i j • (la i • g i) = ∑ i, (M i j * la i) • g i :=
      Finset.sum_congr rfl fun i _ => (smul_smul _ _ _)
    have e2 : h (la j • g j) = ∑ i, (la j * s i j) • g i := by
      rw [map_smul, hs j, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (smul_smul _ _ _)
    have := hM j
    rw [e1, e2] at this
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [this, sub_self]
  have := Fintype.linearIndependent_iff.1 hg _ h1 i
  exact sub_eq_zero.1 this

end Loc
end GlobalTheory.HL.FrameClose

namespace GlobalTheory.HL.FrameClose
section Loc2
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.of_apply, ← hi, hM', hM, GlobalTheory.HL.FrameStab.hf_sum]`. Simplify using `only [Matrix.mul_apply, Finset.sum_mul, cT, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem pair_fix (L : LocE F E) {r n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (u u' : Fin (r + 1) → Fin n → E)
    (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hi : ∀ x y, hf L Hm (h x) (h y) = hf L Hm x y)
    (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hM : ∀ j, h (u j) = ∑ i, M i j • u i)
    (hM' : ∀ j, h (u' j) = ∑ i, M' i j • u' i) :
    cT L M * Matrix.of (fun i j => hf L Hm (u' j) (u i)) * M' = Matrix.of (fun i j => hf L Hm (u' j) (u i)) := by
  ext a b
  rw [Matrix.of_apply, ← hi, hM', hM, GlobalTheory.HL.FrameStab.hf_sum]
  simp only [Matrix.mul_apply, Finset.sum_mul, cT, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Take `⟨o, ho, rfl⟩` from `hx`. Establish `hij' : (i : ℕ) < j` using `hij`. Establish `hj : (j : ℕ) ≤ r` using `Nat.lt_succ_iff.1 j.2`. Establish `hr : r - (i : ℕ) = (r - (j : ℕ)) + ((j : ℕ) - i)` using `by omega`. Establish `hr2 : r = (r - ((j : ℕ) - i)) + ((j : ℕ) - i)` using `by omega`.

Establish `hu : IsUnit (algebraMap F E (c ^ (r - (j : ℕ))))` using `(IsUnit.mk0 _ (pow_ne_zero _ hc)).map (algebraMap F E)`. Establish `hy : y = algebraMap F E (q * (a ^ (r - ((j : ℕ) - i)) * (a * c) ^ ((j : ℕ) - i))) * o`. Establish `p1 : c ^ (r - (i : ℕ)) = c ^ (r - (j : ℕ)) * c ^ ((j : ℕ) - i)` using `by rw [← pow_add, ← hr]`. Establish `p2 : a ^ r = a ^ (r - ((j : ℕ) - i)) * a ^ ((j : ℕ) - i)` using `by rw [← pow_add, ← hr2]`. Apply `hu.mul_right_injective` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[← hrel, p1, p2]`. Simplify using `only [map_mul, map_pow, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy]`.

Conclude with `L.O.mul_mem (algebraMap_mem L (mul_mem hq (mul_mem (pow_mem ha _) (pow_mem hac _)))) ho`.
-/
theorem scale_int (L : LocE F E) {r : ℕ} (c a q : F) (hc : c ≠ 0) (ha : a ∈ 𝒪[F]) (hac : a * c ∈ 𝒪[F])
    (hq : q ∈ 𝒪[F]) (i j : Fin (r + 1)) (hij : i < j) (x y : E)
    (hx : ∃ o ∈ L.O, x = algebraMap F E (q * a ^ r) * o)
    (hrel : x * algebraMap F E (c ^ (r - (i : ℕ))) = algebraMap F E (c ^ (r - (j : ℕ))) * y) : y ∈ L.O := by
  obtain ⟨o, ho, rfl⟩ := hx
  have hij' : (i : ℕ) < j := hij
  have hj : (j : ℕ) ≤ r := Nat.lt_succ_iff.1 j.2
  have hr : r - (i : ℕ) = (r - (j : ℕ)) + ((j : ℕ) - i) := by omega
  have hr2 : r = (r - ((j : ℕ) - i)) + ((j : ℕ) - i) := by omega
  have hu : IsUnit (algebraMap F E (c ^ (r - (j : ℕ)))) := (IsUnit.mk0 _ (pow_ne_zero _ hc)).map (algebraMap F E)
  have hy : y = algebraMap F E (q * (a ^ (r - ((j : ℕ) - i)) * (a * c) ^ ((j : ℕ) - i))) * o := by
    have p1 : c ^ (r - (i : ℕ)) = c ^ (r - (j : ℕ)) * c ^ ((j : ℕ) - i) := by rw [← pow_add, ← hr]
    have p2 : a ^ r = a ^ (r - ((j : ℕ) - i)) * a ^ ((j : ℕ) - i) := by rw [← pow_add, ← hr2]
    apply hu.mul_right_injective
    dsimp only
    rw [← hrel, p1, p2]
    simp only [map_mul, map_pow, mul_pow]
    ring
  rw [hy]
  exact L.O.mul_mem (algebraMap_mem L (mul_mem hq (mul_mem (pow_mem ha _) (pow_mem hac _)))) ho

/- English proof (translation)
Establish `h1O : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j ∈ L.O`. Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `L.O.one_mem`.

Conclude with `L.O.zero_mem`. Take `⟨si, -, h2, h3⟩` from `GlobalTheory.T.unitriangular_close_to_one_inverse_close L n s 1 L.O.one_mem hlow hdiag (fun i j => ⟨(s - 1) i j, L.O.sub_mem (hO i j) (h1O i j), (one_mul _).symm⟩)`. Use `⟨si, h2, fun i j => ?_⟩` and prove the remaining obligations. Take `⟨o, ho, he⟩` from `h3 i j`. Establish `: si i j = o + (1 : Matrix (Fin n) (Fin n) E) i j`.

Rewrite `he` using `[one_mul, Matrix.sub_apply]`. Rewrite using `[← he]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.O.add_mem ho (h1O i j)`.
-/
theorem int_inv (L : LocE F E) {n : ℕ} (s : Matrix (Fin n) (Fin n) E) (hlow : ∀ i j, j < i → s i j = 0)
    (hdiag : ∀ i, s i i = 1) (hO : ∀ i j, s i j ∈ L.O) :
    ∃ si : Matrix (Fin n) (Fin n) E, s * si = 1 ∧ ∀ i j, si i j ∈ L.O := by
  have h1O : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j ∈ L.O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
  obtain ⟨si, -, h2, h3⟩ := GlobalTheory.T.unitriangular_close_to_one_inverse_close L n s 1 L.O.one_mem hlow hdiag
    (fun i j => ⟨(s - 1) i j, L.O.sub_mem (hO i j) (h1O i j), (one_mul _).symm⟩)
  refine ⟨si, h2, fun i j => ?_⟩
  obtain ⟨o, ho, he⟩ := h3 i j
  have : si i j = o + (1 : Matrix (Fin n) (Fin n) E) i j := by
    rw [one_mul, Matrix.sub_apply] at he
    rw [← he]; ring
  rw [this]
  exact L.O.add_mem ho (h1O i j)

variable [IsNonarchimedeanLocalField F] [CharZero F]

/- English proof (translation)
Use `L.free` as an intermediate fact. Establish `hnt : Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)`. Establish `hinj : Function.Injective (algebraMap F E)` using `(algebraMap F E).injective`. Take `⟨hli, -⟩` from `GlobalTheory.FrameBasic.main L r k S`. Establish `hli1 : LinearIndependent E S.f` using `(linearIndependent_sum.1 hli).1`.

Take `⟨hN, hN', -⟩` from `GlobalTheory.HL.FrameOnto.unipotent_onto L r k S`. Establish `hhN : h ∈ S.N` using `(Subgroup.mem_inf.1 hh).1`. Establish `hhN' : h ∈ S.N'` using `(Subgroup.mem_inf.1 hh).2`. Take `⟨s, hs, hsf⟩` from `hN h hhN`. Take `⟨s', hs', hsf'⟩` from `hN' h hhN'`.

Establish `hiso : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y` using `hhN.1.1`. Use `set cp : Fin (r + 1) → E := fun j => algebraMap F E (c ^ (r - (j : ℕ))) with hcp`. Establish `hcpu : ∀ j, IsUnit (cp j)` using `fun j => (IsUnit.mk0 _ (pow_ne_zero _ hc)).map (algebraMap F E)`. Establish `hMs` using `coord_scale S.f hli1 h cp s M hsf hM`. Establish `hMlow : ∀ i j, j < i → M i j = 0`.

Introduce `i j hij`. Use `hMs i j` as an intermediate fact. Rewrite `this` using `[hs.1 i j hij, mul_zero]`. Conclude with `(hcpu i).mul_left_eq_zero.1 this`. Establish `hMdiag : ∀ i, M i i = 1`.

Introduce `i`. Use `hMs i i` as an intermediate fact. Rewrite `this` using `[hs.2 i, mul_one]`. Conclude with `(hcpu i).mul_left_inj.1 (this.trans (one_mul _).symm)`. Use `set M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun i j => algebraMap F E (c ^ (r - (j : ℕ)) / c ^ (r - (i : ℕ))) * s' i j with hM'def`.

Establish `hM' : ∀ j, h (cp j • S.f' j) = ∑ i, M' i j • (cp i • S.f' i)`. Introduce `j`. Rewrite using `[map_smul, hsf' j, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul]`.

Use `congr 1`. Establish `e1 : algebraMap F E (c ^ (r - (j : ℕ)) / c ^ (r - (i : ℕ))) * algebraMap F E (c ^ (r - (i : ℕ))) = algebraMap F E (c ^ (r - (j : ℕ)))`. Rewrite using `[← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc)]`. Simplify using `only [hM'def, hcp, Matrix.of_apply]`. Take the linear combination `(-(s' i j)) * e1`.

Establish `hpair` using `pair_fix L S.Hm (fun j => cp j • S.f j) (fun j => cp j • S.f' j) h hiso M M' hM hM'`. Establish `htO : algebraMap F E (t * e ^ 2 * a ^ r) ∈ L.O` using `algebraMap_mem L (mul_mem (mul_mem ht (pow_mem he _)) (pow_mem ha _))`. Take `⟨Mi, hMi1, hMi2, hMi⟩` from `GlobalTheory.T.unitriangular_close_to_one_inverse_close L (r + 1) M _ htO hMlow hMdiag hcl`. Establish `hcl'` using `GlobalTheory.T.pairing_conj_inverseAdjoint_close_to_one L (r + 1) _ Zi M Mi M' _ (algebraMap F E e) htO (by rw [L.cj_fix]; exact ⟨_, rfl⟩) hZi hZ hZi' hMi1 hMi2 hMi hpair`. Establish `heu : IsUnit (algebraMap F E e)` using `(IsUnit.mk0 _ he0).map (algebraMap F E)`.

Establish `hM'cl : ∀ i j, ∃ o ∈ L.O, (M' - 1) i j = algebraMap F E (t * a ^ r) * o`. Introduce `i j`. Take `⟨o, ho, hoe⟩` from `hcl' i j`. Use `⟨o, ho, ?_⟩` and prove the remaining obligations. Establish `: algebraMap F E e * algebraMap F E e * ((M' - 1) i j - algebraMap F E (t * a ^ r) * o) = 0`.

Rewrite using `[mul_sub, hoe]`. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 ((heu.mul heu).mul_right_eq_zero.1 this)`. Use `⟨?_, M', hM', hM'cl⟩` and prove the remaining obligations.

Establish `hsO : ∀ i j, s i j ∈ L.O`. Introduce `i j`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Use `scale_int L c a (t * e ^ 2) hc ha hac (mul_mem ht (pow_mem he _)) i j hij (M i j) (s i j) ?_ (hMs i j)` and prove the remaining obligations. Take `⟨o, ho, hoe⟩` from `hcl i j`.

Use `⟨o, ho, ?_⟩` and prove the remaining obligations. Rewrite `hoe` using `[Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero]`. Rewrite using `[hoe]`. Rewrite using `[hs.2 i]`. Conclude with `L.O.one_mem`.

Rewrite using `[hs.1 i j hij]`. Conclude with `L.O.zero_mem`. Establish `hs'O : ∀ i j, s' i j ∈ L.O`. Introduce `i j`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases.

Use `scale_int L c a t hc ha hac ht i j hij (M' i j) (s' i j) ?_ ?_` and prove the remaining obligations. Take `⟨o, ho, hoe⟩` from `hM'cl i j`. Use `⟨o, ho, ?_⟩` and prove the remaining obligations. Rewrite `hoe` using `[Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero]`. Rewrite using `[hoe]`.

Simplify using `only [hM'def, Matrix.of_apply]`. Rewrite using `[mul_comm _ (s' i j), mul_assoc, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc), mul_comm]`. Rewrite using `[hs'.2 i]`. Conclude with `L.O.one_mem`. Rewrite using `[hs'.1 i j hij]`.

Conclude with `L.O.zero_mem`. Take `⟨si, hsi, hsiO⟩` from `int_inv L s hs.1 hs.2 hsO`. Take `⟨si', hsi', hsi'O⟩` from `int_inv L s' hs'.1 hs'.2 hs'O`. Conclude with `GlobalTheory.T.mem_maximal_compact_of_integral L r k S h s si s' si' hh hsO hsiO hsi hs'O hsi'O hsi' hsf hsf'`.
-/
theorem loc_close (L : LocE F E) (r k : ℕ) (S : Frames L r k) (c a t e : F)
    (Zi : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (h : S.GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hc : c ≠ 0) (ha : a ∈ 𝒪[F]) (hac : a * c ∈ 𝒪[F]) (ht : t ∈ 𝒪[F]) (he : e ∈ 𝒪[F]) (he0 : e ≠ 0)
    (hZi : Zi * Matrix.of (fun i j : Fin (r + 1) => hf L S.Hm (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j)
      (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i)) = 1)
    (hZ : ∀ i j : Fin (r + 1), algebraMap F E e * hf L S.Hm (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j)
      (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i) ∈ L.O)
    (hZi' : ∀ i j, algebraMap F E e * Zi i j ∈ L.O) (hh : h ∈ S.St)
    (hM : ∀ j : Fin (r + 1), h (algebraMap F E (c ^ (r - (j : ℕ))) • S.f j) =
      ∑ i, M i j • (algebraMap F E (c ^ (r - (i : ℕ))) • S.f i))
    (hcl : ∀ i j, ∃ o ∈ L.O, (M - 1) i j = algebraMap F E (t * e ^ 2 * a ^ r) * o) :
    h ∈ S.K0 ∧ ∃ M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ j : Fin (r + 1), h (algebraMap F E (c ^ (r - (j : ℕ))) • S.f' j) =
        ∑ i, M' i j • (algebraMap F E (c ^ (r - (i : ℕ))) • S.f' i)) ∧
      ∀ i j, ∃ o ∈ L.O, (M' - 1) i j = algebraMap F E (t * a ^ r) * o := by
  have := L.free
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  obtain ⟨hli, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hli1 : LinearIndependent E S.f := (linearIndependent_sum.1 hli).1
  obtain ⟨hN, hN', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  have hhN : h ∈ S.N := (Subgroup.mem_inf.1 hh).1
  have hhN' : h ∈ S.N' := (Subgroup.mem_inf.1 hh).2
  obtain ⟨s, hs, hsf⟩ := hN h hhN
  obtain ⟨s', hs', hsf'⟩ := hN' h hhN'
  have hiso : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hhN.1.1
  set cp : Fin (r + 1) → E := fun j => algebraMap F E (c ^ (r - (j : ℕ))) with hcp
  have hcpu : ∀ j, IsUnit (cp j) := fun j => (IsUnit.mk0 _ (pow_ne_zero _ hc)).map (algebraMap F E)

  have hMs := coord_scale S.f hli1 h cp s M hsf hM
  have hMlow : ∀ i j, j < i → M i j = 0 := by
    intro i j hij
    have := hMs i j
    rw [hs.1 i j hij, mul_zero] at this
    exact (hcpu i).mul_left_eq_zero.1 this
  have hMdiag : ∀ i, M i i = 1 := by
    intro i
    have := hMs i i
    rw [hs.2 i, mul_one] at this
    exact (hcpu i).mul_left_inj.1 (this.trans (one_mul _).symm)

  set M' : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
    Matrix.of fun i j => algebraMap F E (c ^ (r - (j : ℕ)) / c ^ (r - (i : ℕ))) * s' i j with hM'def
  have hM' : ∀ j, h (cp j • S.f' j) = ∑ i, M' i j • (cp i • S.f' i) := by
    intro j
    rw [map_smul, hsf' j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    have e1 : algebraMap F E (c ^ (r - (j : ℕ)) / c ^ (r - (i : ℕ))) * algebraMap F E (c ^ (r - (i : ℕ))) =
        algebraMap F E (c ^ (r - (j : ℕ))) := by
      rw [← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc)]
    simp only [hM'def, hcp, Matrix.of_apply]
    linear_combination (-(s' i j)) * e1

  have hpair := pair_fix L S.Hm (fun j => cp j • S.f j) (fun j => cp j • S.f' j) h hiso M M' hM hM'
  have htO : algebraMap F E (t * e ^ 2 * a ^ r) ∈ L.O :=
    algebraMap_mem L (mul_mem (mul_mem ht (pow_mem he _)) (pow_mem ha _))
  obtain ⟨Mi, hMi1, hMi2, hMi⟩ := GlobalTheory.T.unitriangular_close_to_one_inverse_close L (r + 1) M _ htO hMlow hMdiag hcl
  have hcl' := GlobalTheory.T.pairing_conj_inverseAdjoint_close_to_one L (r + 1) _ Zi M Mi M' _ (algebraMap F E e) htO
    (by rw [L.cj_fix]; exact ⟨_, rfl⟩) hZi hZ hZi' hMi1 hMi2 hMi hpair
  have heu : IsUnit (algebraMap F E e) := (IsUnit.mk0 _ he0).map (algebraMap F E)
  have hM'cl : ∀ i j, ∃ o ∈ L.O, (M' - 1) i j = algebraMap F E (t * a ^ r) * o := by
    intro i j
    obtain ⟨o, ho, hoe⟩ := hcl' i j
    refine ⟨o, ho, ?_⟩
    have : algebraMap F E e * algebraMap F E e * ((M' - 1) i j - algebraMap F E (t * a ^ r) * o) = 0 := by
      rw [mul_sub, hoe]
      simp only [map_mul, map_pow]
      ring
    exact sub_eq_zero.1 ((heu.mul heu).mul_right_eq_zero.1 this)
  refine ⟨?_, M', hM', hM'cl⟩
  have hsO : ∀ i j, s i j ∈ L.O := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · refine scale_int L c a (t * e ^ 2) hc ha hac (mul_mem ht (pow_mem he _)) i j hij (M i j) (s i j) ?_ (hMs i j)
      obtain ⟨o, ho, hoe⟩ := hcl i j
      refine ⟨o, ho, ?_⟩
      rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero] at hoe
      rw [hoe]
    · rw [hs.2 i]; exact L.O.one_mem
    · rw [hs.1 i j hij]; exact L.O.zero_mem
  have hs'O : ∀ i j, s' i j ∈ L.O := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · refine scale_int L c a t hc ha hac ht i j hij (M' i j) (s' i j) ?_ ?_
      · obtain ⟨o, ho, hoe⟩ := hM'cl i j
        refine ⟨o, ho, ?_⟩
        rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt hij), sub_zero] at hoe
        rw [hoe]
      · simp only [hM'def, Matrix.of_apply]
        rw [mul_comm _ (s' i j), mul_assoc, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc), mul_comm]
    · rw [hs'.2 i]; exact L.O.one_mem
    · rw [hs'.1 i j hij]; exact L.O.zero_mem
  obtain ⟨si, hsi, hsiO⟩ := int_inv L s hs.1 hs.2 hsO
  obtain ⟨si', hsi', hsi'O⟩ := int_inv L s' hs'.1 hs'.2 hs'O
  exact GlobalTheory.T.mem_maximal_compact_of_integral L r k S h s si s' si' hh hsO hsiO hsi hs'O hsi'O hsi' hsf hsf'

end Loc2
end GlobalTheory.HL.FrameClose

namespace GlobalTheory.HL.FrameClose

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A r k G Λ hΛ`. Establish `hZinv` using `GlobalTheory.T.rationalPairingMatrix_inv_mul_self A r k G`. Establish `hΓinv` using `GlobalTheory.T.globalFrames_joint_gram_inv_mul_self A r k G`. Take `⟨D, hD0, hDv, hDpair, hDg⟩` from `GlobalTheory.T.exists_common_denominator_for_hermitian_lattice_data (Sum.elim (fun ab : Fin (r + 1) × Fin (r + 1) => G.Zh ab.1 ab.2) (Sum.elim (fun ab : Fin (r + 1) × Fin (r + 1) => G.Zh⁻¹ ab.1 ab.2) (fun kl : (Fin (r + 1) ⊕ Fin (r + 1)) × (Fin (r + 1) ⊕ Fin (r + 1)) => (Matrix.o …`. Set `a : ∀ p, (A.loc p).Fp` to `fun p => if ((G.c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) then 1 else (G.c p : (A.loc p).Fp)⁻¹`.

Establish `ha : ∀ p, a p ∈ 𝒪[(A.loc p).Fp] ∧ a p * G.c p ∈ 𝒪[(A.loc p).Fp] ∧ a p ≠ 0`. Introduce `p`. Distinguish the cases in `hc : ((G.c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])`. Simplify using `only [a, if_pos hc, one_mul]`. Conclude with `⟨one_mem _, hc, one_ne_zero⟩`.

Simplify using `only [a, if_neg hc]`. Conclude with `⟨inv_mem hc, by rw [inv_mul_cancel₀ (Units.ne_zero _)]; exact one_mem _, inv_ne_zero (Units.ne_zero _)⟩`. Use `⟨fun p => (D : (A.loc p).Fp) ^ 5 * a p ^ r, fun p => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: (D : (A.loc p).Fp) ≠ 0` using `by haveI := (A.loc p).char0`. Conclude with `hD0` after adjusting the coercions.

Conclude with `mul_ne_zero (pow_ne_zero _ this) (pow_ne_zero _ (ha p).2.2)`. Use `((GlobalTheory.T.intCast_isUnit_completion_almost_all_places A D hD0).union G.c_unit).subset fun p hp => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hq`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hq`. Take `⟨⟨u, hu⟩, ⟨v, hv⟩⟩` from `hq`.

Apply `hp` to reduce the goal to its premises. Establish `hcO : ((G.c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])` using `hv ▸ (v : 𝒪[(A.loc p).Fp]).2`. Use `⟨u ^ 5, ?_⟩` and prove the remaining obligations. Simplify using `only [a, if_pos hcO, one_pow, mul_one]`. Rewrite using `[← hu]`.

Use `push_cast`. Both sides reduce to the same expression. Introduce `p c0 h M hc0 hc0O hh hM hcl haveI := (A.loc p).lf haveI := (A.loc p).char0`. Take `⟨haO, hacO, ha0⟩` from `ha p`. Establish `hform` using `(GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1`.

Establish `hZloc : ∀ i j : Fin (r + 1), hf (A.L p) (G.S p).Hm (A.bc p (G.f' j)) (A.bc p (G.f i)) = (A.loc p).ιE (G.Zh i j)`. Introduce `i j`. Rewrite using `[G.Hm_eq p, hform]`. Both sides reduce to the same expression. Establish `hint : ∀ x : E, (∃ o : 𝓞 E, (D : E) * x = o) → (A.loc p).ιE ((D : E) * x) ∈ (A.L p).O`.

Introduce and unpack `x ⟨o, ho⟩`. Conclude with `((GlobalTheory.HL.PlacesInt.integers_local A).1 _).2 ⟨o, ho.symm⟩ p`. Establish `hDE : algebraMap (A.loc p).Fp (A.loc p).Ep (D : (A.loc p).Fp) = (A.loc p).ιE (D : E)`. Rewrite using `[map_intCast, map_intCast]`. Establish `hDO : (D : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]` using `intCast_mem _ D`.

Establish `hD0' : (D : (A.loc p).Fp) ≠ 0` using `by exact_mod_cast hD0`. Establish `hZm : (Matrix.of fun i j : Fin (r + 1) => hf (A.L p) (G.S p).Hm (A.bc p (G.f' j)) (A.bc p (G.f i))) = G.Zh.map (A.loc p).ιE`. Use extensionality with `i j`. Rewrite using `[Matrix.of_apply, hZloc]`. Both sides reduce to the same expression.

Take `⟨hK0, M', hM', hcl'⟩` from `loc_close (A.L p) r k (G.S p) (G.c p) (a p) (c0 * (D : (A.loc p).Fp) ^ 3) (D : (A.loc p).Fp) ((G.Zh⁻¹).map (A.loc p).ιE) h M (Units.ne_zero _) haO hacO (mul_mem hc0O (pow_mem hDO _)) hDO hD0' (by`. Simplify using `only [G.f_eq p, G.f'_eq p]`. Rewrite using `[hZm, ← Matrix.map_mul, hZinv, Matrix.map_one _ (map_zero _) (map_one _)])`. Use the proof step `(by`. Introduce `i j`.

Simplify using `only [G.f_eq p, G.f'_eq p]`. Rewrite using `[hZloc, hDE, ← map_mul]`. Conclude with `hint _ (hDv (Sum.inl (i, j))))`. Use the proof step `(by`. Introduce `i j`.

Rewrite using `[Matrix.map_apply, hDE, ← map_mul]`. Conclude with `hint _ (hDv (Sum.inr (Sum.inl (i, j)))))`. Use `hh (by simpa only [G.f_eq p] using hM)`. Use the proof step `(by`. Introduce `i j`.

Take `⟨o, ho, hoe⟩` from `hcl i j`. Use `⟨o, ho, ?_⟩` and prove the remaining obligations. Rewrite using `[hoe]`. Use `congr 2`. Use the proof step `ring)`.

Use `⟨hK0, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.close_on_completed_lattice_of_close_on_frames A r k G Λ D p h M M' c0 hΓinv (fun k l => hDv (Sum.inr (Sum.inr (k, l)))) (fun x hx l => hDpair x hx l) hDg hh hM (by simpa only [G.f'_eq p] using hM') ?_ ?_` and prove the remaining obligations. Introduce `i j`. Take `⟨o, ho, hoe⟩` from `hcl i j`. Use `⟨algebraMap _ _ ((D : (A.loc p).Fp) ^ 2 * a p ^ r) * o, (A.L p).O.mul_mem (algebraMap_mem (A.L p) (mul_mem (pow_mem hDO _) (pow_mem haO _))) ho, ?_⟩` and prove the remaining obligations.

Rewrite using `[hoe]`. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i j`. Take `⟨o, ho, hoe⟩` from `hcl' i j`.

Use `⟨algebraMap _ _ (a p ^ r) * o, (A.L p).O.mul_mem (algebraMap_mem (A.L p) (pow_mem haO _)) ho, ?_⟩` and prove the remaining obligations. Rewrite using `[hoe]`. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem close_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsLattice E Λ → ∃ d : ∀ p, (A.loc p).Fp, (∀ p, d p ≠ 0) ∧ {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = d p}.Finite ∧ ∀ p (c0 : (A.loc p).Fp) (h : (G.S p).GLV) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), c0 ≠ 0 → c0 ∈ 𝒪[(A.loc p).Fp] → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c0 * d p) * o) → h ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep c0 • y := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ
  have hZinv := GlobalTheory.T.rationalPairingMatrix_inv_mul_self A r k G
  have hΓinv := GlobalTheory.T.globalFrames_joint_gram_inv_mul_self A r k G
  obtain ⟨D, hD0, hDv, hDpair, hDg⟩ := GlobalTheory.T.exists_common_denominator_for_hermitian_lattice_data
    (Sum.elim (fun ab : Fin (r + 1) × Fin (r + 1) => G.Zh ab.1 ab.2)
      (Sum.elim (fun ab : Fin (r + 1) × Fin (r + 1) => G.Zh⁻¹ ab.1 ab.2)
        (fun kl : (Fin (r + 1) ⊕ Fin (r + 1)) × (Fin (r + 1) ⊕ Fin (r + 1)) =>
          (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j *
            sig (Sum.elim G.f G.f' l j))⁻¹ kl.1 kl.2)))
    (Sum.elim G.f G.f') G.Hm (sig : E →+* E) Λ hΛ
  let a : ∀ p, (A.loc p).Fp := fun p =>
    if ((G.c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) then 1 else (G.c p : (A.loc p).Fp)⁻¹
  have ha : ∀ p, a p ∈ 𝒪[(A.loc p).Fp] ∧ a p * G.c p ∈ 𝒪[(A.loc p).Fp] ∧ a p ≠ 0 := by
    intro p
    by_cases hc : ((G.c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])
    · simp only [a, if_pos hc, one_mul]
      exact ⟨one_mem _, hc, one_ne_zero⟩
    · simp only [a, if_neg hc]
      exact ⟨inv_mem hc, by rw [inv_mul_cancel₀ (Units.ne_zero _)]; exact one_mem _,
        inv_ne_zero (Units.ne_zero _)⟩
  refine ⟨fun p => (D : (A.loc p).Fp) ^ 5 * a p ^ r, fun p => ?_, ?_, ?_⟩
  · have : (D : (A.loc p).Fp) ≠ 0 := by
      haveI := (A.loc p).char0
      exact_mod_cast hD0
    exact mul_ne_zero (pow_ne_zero _ this) (pow_ne_zero _ (ha p).2.2)
  · refine ((GlobalTheory.T.intCast_isUnit_completion_almost_all_places A D hD0).union G.c_unit).subset fun p hp => ?_
    by_contra hq
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hq
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hq
    apply hp
    have hcO : ((G.c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) := hv ▸ (v : 𝒪[(A.loc p).Fp]).2
    refine ⟨u ^ 5, ?_⟩
    simp only [a, if_pos hcO, one_pow, mul_one]
    rw [← hu]
    push_cast
    rfl
  · intro p c0 h M hc0 hc0O hh hM hcl
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨haO, hacO, ha0⟩ := ha p
    have hform := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1
    have hZloc : ∀ i j : Fin (r + 1), hf (A.L p) (G.S p).Hm (A.bc p (G.f' j)) (A.bc p (G.f i)) =
        (A.loc p).ιE (G.Zh i j) := by
      intro i j
      rw [G.Hm_eq p, hform]
      rfl
    have hint : ∀ x : E, (∃ o : 𝓞 E, (D : E) * x = o) → (A.loc p).ιE ((D : E) * x) ∈ (A.L p).O := by
      rintro x ⟨o, ho⟩
      exact ((GlobalTheory.HL.PlacesInt.integers_local A).1 _).2 ⟨o, ho.symm⟩ p
    have hDE : algebraMap (A.loc p).Fp (A.loc p).Ep (D : (A.loc p).Fp) = (A.loc p).ιE (D : E) := by
      rw [map_intCast, map_intCast]
    have hDO : (D : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp] := intCast_mem _ D
    have hD0' : (D : (A.loc p).Fp) ≠ 0 := by exact_mod_cast hD0
    have hZm : (Matrix.of fun i j : Fin (r + 1) => hf (A.L p) (G.S p).Hm (A.bc p (G.f' j)) (A.bc p (G.f i))) =
        G.Zh.map (A.loc p).ιE := by
      ext i j
      rw [Matrix.of_apply, hZloc]
      rfl
    obtain ⟨hK0, M', hM', hcl'⟩ := loc_close (A.L p) r k (G.S p) (G.c p) (a p)
      (c0 * (D : (A.loc p).Fp) ^ 3) (D : (A.loc p).Fp) ((G.Zh⁻¹).map (A.loc p).ιE) h M (Units.ne_zero _) haO hacO
      (mul_mem hc0O (pow_mem hDO _)) hDO hD0'
      (by
        simp only [G.f_eq p, G.f'_eq p]
        rw [hZm, ← Matrix.map_mul, hZinv, Matrix.map_one _ (map_zero _) (map_one _)])
      (by
        intro i j
        simp only [G.f_eq p, G.f'_eq p]
        rw [hZloc, hDE, ← map_mul]
        exact hint _ (hDv (Sum.inl (i, j))))
      (by
        intro i j
        rw [Matrix.map_apply, hDE, ← map_mul]
        exact hint _ (hDv (Sum.inr (Sum.inl (i, j)))))
      hh (by simpa only [G.f_eq p] using hM)
      (by
        intro i j
        obtain ⟨o, ho, hoe⟩ := hcl i j
        refine ⟨o, ho, ?_⟩
        rw [hoe]
        congr 2
        ring)
    refine ⟨hK0, ?_⟩
    refine GlobalTheory.T.close_on_completed_lattice_of_close_on_frames A r k G Λ D p h M M' c0 hΓinv (fun k l => hDv (Sum.inr (Sum.inr (k, l))))
      (fun x hx l => hDpair x hx l) hDg hh hM (by simpa only [G.f'_eq p] using hM') ?_ ?_
    · intro i j
      obtain ⟨o, ho, hoe⟩ := hcl i j
      refine ⟨algebraMap _ _ ((D : (A.loc p).Fp) ^ 2 * a p ^ r) * o,
        (A.L p).O.mul_mem (algebraMap_mem (A.L p) (mul_mem (pow_mem hDO _) (pow_mem haO _))) ho, ?_⟩
      rw [hoe]
      simp only [map_mul, map_pow]
      ring
    · intro i j
      obtain ⟨o, ho, hoe⟩ := hcl' i j
      refine ⟨algebraMap _ _ (a p ^ r) * o, (A.L p).O.mul_mem (algebraMap_mem (A.L p) (pow_mem haO _)) ho, ?_⟩
      rw [hoe]
      simp only [map_mul, map_pow]
      ring

end GlobalTheory.HL.FrameClose
