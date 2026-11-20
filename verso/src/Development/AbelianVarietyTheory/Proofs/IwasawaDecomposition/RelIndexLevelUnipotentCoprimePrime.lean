import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)

noncomputable section

namespace GlobalTheory.UniLevelIndex

open IsDedekindDomain.HeightOneSpectrum

section Count

/- English proof (translation)
Set `e : {p : Fin n × Fin n // p.1 < p.2} ≃ Σ j : Fin n, Fin j.val` to `{ toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩ invFun := fun x => ⟨(⟨x.2.val, lt_trans x.2.2 x.1.2⟩, x.1), x.2.2⟩ left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl right_inv := by rintro ⟨j, i⟩; rfl }`. Rewrite using `[Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]`. Simplify using the standard rewrite rules.
-/
theorem card_pairs_lt (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = ∑ i : Fin n, (i : ℕ) := by
  let e : {p : Fin n × Fin n // p.1 < p.2} ≃ Σ j : Fin n, Fin j.val :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
      invFun := fun x => ⟨(⟨x.2.val, lt_trans x.2.2 x.1.2⟩, x.1), x.2.2⟩
      left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
      right_inv := by rintro ⟨j, i⟩; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp

/- English proof (translation)
Use `Nat.Coprime.prod_left fun i _ => ?_` and prove the remaining obligations. Establish `hm : n - (i : ℕ) ≠ 0` using `by have := i.2; omega`. Rewrite using `[Nat.coprime_comm, hp.coprime_iff_not_dvd]`. Introduce `hd`. Establish `h2 : p ∣ q ^ (n - i)` using `dvd_pow hpq hm`.

Establish `h1 : 1 ≤ q ^ (n - i)` using `Nat.one_le_pow _ _ hq`. Establish `h3` using `Nat.dvd_sub h2 hd`. Rewrite `h3` using `[Nat.sub_sub_self h1]`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 h3)`.
-/
theorem coprime_prod_pow_sub_one {q p : ℕ} (n : ℕ) (hp : p.Prime) (hpq : p ∣ q) (hq : 0 < q) :
    Nat.Coprime (∏ i : Fin n, (q ^ (n - i) - 1)) p := by
  refine Nat.Coprime.prod_left fun i _ => ?_
  have hm : n - (i : ℕ) ≠ 0 := by have := i.2; omega
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hd
  have h2 : p ∣ q ^ (n - i) := dvd_pow hpq hm
  have h1 : 1 ≤ q ^ (n - i) := Nat.one_le_pow _ _ hq
  have h3 := Nat.dvd_sub h2 hd
  rw [Nat.sub_sub_self h1] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

variable (κ : Type) [Field κ] [Finite κ]

/- English proof (translation)
Use `letI := Fintype.ofFinite κ`. Establish `h1` using `Subgroup.card_mul_index (Formalism.L2.DIV.unip κ n)`. Rewrite `h1` using `[GlobalTheory.Mem.GrpCount.card_unip, card_pairs_lt, Matrix.card_GL_field, ← Nat.card_eq_fintype_card]`. Establish `h2 : ∏ i : Fin n, (Nat.card κ ^ n - Nat.card κ ^ (i : ℕ)) = Nat.card κ ^ (∑ i : Fin n, (i : ℕ)) * ∏ i : Fin n, (Nat.card κ ^ (n - i) - 1)`. Rewrite using `[← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' i.2.le]`. Rewrite `h1` using `[h2]`. Establish `hq : 0 < Nat.card κ ^ (∑ i : Fin n, (i : ℕ))` using `pow_pos Nat.card_pos _`. Conclude with `Nat.eq_of_mul_eq_mul_left hq h1`.
-/
theorem unip_index (n : ℕ) : (Formalism.L2.DIV.unip κ n).index = ∏ i : Fin n, (Nat.card κ ^ (n - i) - 1) := by
  classical
  letI := Fintype.ofFinite κ
  have h1 := Subgroup.card_mul_index (Formalism.L2.DIV.unip κ n)
  rw [GlobalTheory.Mem.GrpCount.card_unip, card_pairs_lt, Matrix.card_GL_field, ← Nat.card_eq_fintype_card] at h1
  have h2 : ∏ i : Fin n, (Nat.card κ ^ n - Nat.card κ ^ (i : ℕ)) =
      Nat.card κ ^ (∑ i : Fin n, (i : ℕ)) * ∏ i : Fin n, (Nat.card κ ^ (n - i) - 1) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' i.2.le]
  rw [h2] at h1
  have hq : 0 < Nat.card κ ^ (∑ i : Fin n, (i : ℕ)) := pow_pos Nat.card_pos _
  exact Nat.eq_of_mul_eq_mul_left hq h1

end Count

section Loc

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

variable (v : HeightOneSpectrum (𝓞 (NumberField.maximalRealSubfield L)))

def toVS : (v.adicCompletionIntegers L⁺).toSubring →+* v.adicCompletionIntegers L⁺ where
  toFun x := ⟨x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def ofVS : v.adicCompletionIntegers L⁺ →+* (v.adicCompletionIntegers L⁺).toSubring where
  toFun x := ⟨x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def redGL (n : ℕ) : GL (Fin n) (v.adicCompletionIntegers L⁺).toSubring →*
    GL (Fin n) (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) :=
  Matrix.GeneralLinearGroup.map ((IsLocalRing.residue (v.adicCompletionIntegers L⁺)).comp (toVS v))

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff]`. Conclude with `Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L⁺) (WithZero (Multiplicative ℤ))))`.
-/
theorem residue_eq_zero_iff' (x : v.adicCompletionIntegers L⁺) :
    IsLocalRing.residue (v.adicCompletionIntegers L⁺) x = 0 ↔ Valued.v (x : v.adicCompletion L⁺) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L⁺) (WithZero (Multiplicative ℤ))))

/- English proof (translation)
The claim follows from `residue_eq_zero_iff' v (toVS v x)`.
-/
theorem res_toVS_eq_zero_iff (x : (v.adicCompletionIntegers L⁺).toSubring) :
    IsLocalRing.residue (v.adicCompletionIntegers L⁺) (toVS v x) = 0 ↔ Valued.v (x : v.adicCompletion L⁺) < 1 :=
  residue_eq_zero_iff' v (toVS v x)

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← map_one (IsLocalRing.residue (v.adicCompletionIntegers L⁺)), ← map_sub, residue_eq_zero_iff']`. Conclude with `Iff.rfl`.
-/
theorem res_toVS_eq_one_iff (x : (v.adicCompletionIntegers L⁺).toSubring) :
    IsLocalRing.residue (v.adicCompletionIntegers L⁺) (toVS v x) = 1 ↔ Valued.v ((x : v.adicCompletion L⁺) - 1) < 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (v.adicCompletionIntegers L⁺)), ← map_sub, residue_eq_zero_iff']
  exact Iff.rfl

/- English proof (translation)
Introduce `M`. Use `choose A hA using fun i j => (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers L⁺)) ((M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺))) i j)`. Set `B : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L⁺).toSubring` to `fun i j => ofVS v (A i j)`. Establish `hB : ((IsLocalRing.residue (v.adicCompletionIntegers L⁺)).comp (toVS v)).mapMatrix B = M`. Use extensionality with `i j`.

Conclude with `hA i j`. Establish `hu : IsUnit ((toVS v).mapMatrix B).det`. Establish `e : (IsLocalRing.residue (v.adicCompletionIntegers L⁺)).mapMatrix ((toVS v).mapMatrix B) = (M : Matrix (Fin n) (Fin n) _)`. Rewrite using `[← hB]`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, e]`. Conclude with `(Matrix.isUnits_det_units M).ne_zero`. Establish `hBB : (ofVS v).mapMatrix ((toVS v).mapMatrix B) = B`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `hdet : IsUnit B.det`. Rewrite using `[← hBB, ← RingHom.map_det]`. Conclude with `hu.map (ofVS v)`. Conclude with `⟨Matrix.nonsingInvUnit B hdet, Units.ext hB⟩`.
-/
theorem redGL_surjective (n : ℕ) : Function.Surjective (redGL v n) := by
  intro M
  choose A hA using fun i j => (IsLocalRing.residue_surjective (R := v.adicCompletionIntegers L⁺))
    ((M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺))) i j)
  let B : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers L⁺).toSubring := fun i j => ofVS v (A i j)
  have hB : ((IsLocalRing.residue (v.adicCompletionIntegers L⁺)).comp (toVS v)).mapMatrix B = M := by
    ext i j
    exact hA i j
  have hu : IsUnit ((toVS v).mapMatrix B).det := by
    have e : (IsLocalRing.residue (v.adicCompletionIntegers L⁺)).mapMatrix ((toVS v).mapMatrix B) =
        (M : Matrix (Fin n) (Fin n) _) := by
      rw [← hB]; ext i j; rfl
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, e]
    exact (Matrix.isUnits_det_units M).ne_zero
  have hBB : (ofVS v).mapMatrix ((toVS v).mapMatrix B) = B := by
    ext i j
    rfl
  have hdet : IsUnit B.det := by
    rw [← hBB, ← RingHom.map_det]
    exact hu.map (ofVS v)
  exact ⟨Matrix.nonsingInvUnit B hdet, Units.ext hB⟩

end Loc

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

/- English proof (translation)
Use `letI := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺))`. Establish `h0 : ((p : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) = 0`. Establish `: (IsLocalRing.residue (v.adicCompletionIntegers L⁺)) (algebraMap (𝓞 L⁺) (v.adicCompletionIntegers L⁺) ((p : ℕ) : 𝓞 L⁺)) = 0`. Rewrite using `[residue_eq_zero_iff', algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := L⁺) (v := v), valuation_of_algebraMap]`. Conclude with `(intValuation_lt_one_iff_mem v _).2 hv`.

Simplify using `using this`. Establish `h1 : ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) = p` using `(hp.eq_one_or_self_of_dvd _ (ringChar.dvd h0)).resolve_left CharP.ringChar_ne_one`. Establish `h2` using `ringChar.dvd (FiniteField.cast_card_eq_zero (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)))`. Rewrite `h2` using `[h1, ← Nat.card_eq_fintype_card]`. Conclude with `h2`.
-/
theorem prime_dvd_card_residue (v : HeightOneSpectrum (𝓞 (NumberField.maximalRealSubfield L))) {p : ℕ} (hp : p.Prime)
    (hv : ((p : ℕ) : 𝓞 L⁺) ∈ v.asIdeal) [Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺))] :
    p ∣ Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) := by
  classical
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺))
  have h0 : ((p : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) = 0 := by
    have : (IsLocalRing.residue (v.adicCompletionIntegers L⁺))
        (algebraMap (𝓞 L⁺) (v.adicCompletionIntegers L⁺) ((p : ℕ) : 𝓞 L⁺)) = 0 := by
      rw [residue_eq_zero_iff', algebraMap_adicCompletionIntegers_apply,
        adicCompletion.valued_coe (K := L⁺) (v := v), valuation_of_algebraMap]
      exact (intValuation_lt_one_iff_mem v _).2 hv
    simpa using this
  have h1 : ringChar (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)) = p :=
    (hp.eq_one_or_self_of_dvd _ (ringChar.dvd h0)).resolve_left CharP.ringChar_ne_one
  have h2 := ringChar.dvd (FiniteField.cast_card_eq_zero (IsLocalRing.ResidueField (v.adicCompletionIntegers L⁺)))
  rw [h1, ← Nat.card_eq_fintype_card] at h2
  exact h2

end Main

/- English proof (translation)
Introduce `L _ _ _ n s r p H hp hA _ hH`. Use `haveI : Finite (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L))) := Formalism.UG.P.glint_finite_residueField s.v`. Set `ι` to `Formalism.UG.bc (n := Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.subtype`. Establish `hG : Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring = ι.range` using `rfl`. Rewrite using `[hG, MonoidHom.range_eq_map, ← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]`.

Establish `hmem : ∀ g, g ∈ H.comap ι ↔ NG.UniRT s r (ι g)` using `fun g => hH (ι g)`. Establish `hker : (redGL s.v n).ker ≤ H.comap ι`. Introduce `g hg`. Rewrite `hg` using `[MonoidHom.mem_ker]`. Establish `he : ∀ a b, IsLocalRing.residue _ (toVS s.v ((g : Matrix (Fin n) (Fin n) _) a b)) = (1 : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L)))) a b` using `fun a b => by`.

Use `congrArg (fun M : GL (Fin n) (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L))) => (M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L)))) a b) hg` as an intermediate fact. Conclude with `this`. Establish `hoff : ∀ a b : Fin n, a ≠ b → Valued.v (((ι g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1`. Introduce `a b hab`. Establish `h2` using `he a b`.

Rewrite `h2` using `[Matrix.one_apply_ne hab]`. Conclude with `(res_toVS_eq_zero_iff s.v _).1 h2`. Use `(hmem g).2 ⟨⟨⟨g, rfl⟩, fun a b ha hb => hoff a b ?_⟩, fun a b _ _ => ⟨fun hba => hoff a b ?_, fun hab => ?_⟩⟩` and prove the remaining obligations. Introduce `h`. Substitute `h` using the available equality.

Use linear arithmetic over natural numbers and integers. Introduce `h`. Substitute `h` using the available equality. Conclude with `lt_irrefl _ hba`. Substitute `hab` using the available equality.

Establish `h2` using `he a a`. Rewrite `h2` using `[Matrix.one_apply_eq]`. Conclude with `(res_toVS_eq_one_iff s.v _).1 h2`. Rewrite using `[← Subgroup.index_map_eq (H.comap ι) (redGL_surjective s.v n) hker]`. Establish `hU : Formalism.L2.DIV.unip (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L))) n ≤ (H.comap ι).map (redGL s.v n)`.

Introduce `M hM`. Take `⟨h0, h1⟩` from `hM`. Set `lift` to `Function.surjInv (IsLocalRing.residue_surjective (R := s.v.adicCompletionIntegers (maximalRealSubfield L)))`. Set `B : Matrix (Fin n) (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring` to `fun i j => if j < i then 0 else if i = j then 1 else ofVS s.v (lift ((M : Matrix (Fin n) (Fin n) _) i j))`. Establish `hlow : ∀ i j, j < i → B i j = 0` using `by intro i j h; simp [B, h]`.

Establish `hdiag : ∀ i, B i i = 1` using `by intro i; simp [B]`. Establish `hdet : B.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular hlow]`. Simplify using `[hdiag]`. Set `g` to `Matrix.nonsingInvUnit B (by rw [hdet]; exact isUnit_one)`.

Establish `hgB : ((ι g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) = fun i j => ((B i j : _) : s.v.adicCompletion (maximalRealSubfield L))` using `rfl`. Establish `hlowK : ∀ a b : Fin n, b < a → Valued.v (((ι g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1`. Introduce `a b h`. Rewrite using `[hgB]`. Simplify using `only [hlow a b h, ZeroMemClass.coe_zero, map_zero]`.

Conclude with `zero_lt_one`. Use `⟨g, (hmem g).2 ⟨⟨⟨g, rfl⟩, fun a b ha hb => hlowK a b ?_⟩, fun a b _ _ => ⟨fun hba => hlowK a b hba, fun hab => ?_⟩⟩, ?_⟩` and prove the remaining obligations. Conclude with `Fin.lt_def.2 (by omega)`. Substitute `hab` using the available equality. Rewrite using `[hgB]`.

Simplify using `only [hdiag, OneMemClass.coe_one, sub_self, map_zero]`. Conclude with `zero_lt_one`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `show IsLocalRing.residue _ (toVS s.v (B i j)) = (M : Matrix (Fin n) (Fin n) _) i j`.

Distinguish the cases in `hji : j < i`. Rewrite using `[hlow i j hji, map_zero, map_zero]`. Conclude with `(h0 hji).symm`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Rewrite using `[hdiag, map_one, map_one, h1]`. Simplify using `only [B, if_neg hji, if_neg hij]`. Conclude with `Function.surjInv_eq _ _`. Use `Nat.Coprime.coprime_dvd_left (Subgroup.index_dvd_of_le hU) ?_` and prove the remaining obligations. Rewrite using `[unip_index]`.

Conclude with `coprime_prod_pow_sub_one n hp (prime_dvd_card_residue s.v hp hA) Nat.card_pos`.
-/
theorem relIndex_coprime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r p : ℕ)
    (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), p.Prime → s.Above p → r ≤ n →
    (∀ g, g ∈ H ↔ NG.UniRT s r g) →
    Nat.Coprime (H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring)) p := by
  intro L _ _ _ n s r p H hp hA _ hH
  classical
  haveI : Finite (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L))) :=
    Formalism.UG.P.glint_finite_residueField s.v
  let ι := Formalism.UG.bc (n := Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.subtype
  have hG : Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring = ι.range := rfl
  rw [hG, MonoidHom.range_eq_map, ← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
  have hmem : ∀ g, g ∈ H.comap ι ↔ NG.UniRT s r (ι g) := fun g => hH (ι g)
  have hker : (redGL s.v n).ker ≤ H.comap ι := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have he : ∀ a b, IsLocalRing.residue _ (toVS s.v ((g : Matrix (Fin n) (Fin n) _) a b)) =
        (1 : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L)))) a b :=
      fun a b => by
        have := congrArg (fun M : GL (Fin n) (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L))) => (M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L)))) a b) hg
        exact this
    have hoff : ∀ a b : Fin n, a ≠ b → Valued.v (((ι g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
      intro a b hab
      have h2 := he a b
      rw [Matrix.one_apply_ne hab] at h2
      exact (res_toVS_eq_zero_iff s.v _).1 h2
    refine (hmem g).2 ⟨⟨⟨g, rfl⟩, fun a b ha hb => hoff a b ?_⟩, fun a b _ _ => ⟨fun hba => hoff a b ?_, fun hab => ?_⟩⟩
    · intro h; subst h; omega
    · intro h; subst h; exact lt_irrefl _ hba
    · subst hab
      have h2 := he a a
      rw [Matrix.one_apply_eq] at h2
      exact (res_toVS_eq_one_iff s.v _).1 h2
  rw [← Subgroup.index_map_eq (H.comap ι) (redGL_surjective s.v n) hker]
  have hU : Formalism.L2.DIV.unip (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield L))) n ≤
      (H.comap ι).map (redGL s.v n) := by
    intro M hM
    obtain ⟨h0, h1⟩ := hM
    let lift := Function.surjInv (IsLocalRing.residue_surjective (R := s.v.adicCompletionIntegers (maximalRealSubfield L)))
    let B : Matrix (Fin n) (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun i j =>
      if j < i then 0 else if i = j then 1 else ofVS s.v (lift ((M : Matrix (Fin n) (Fin n) _) i j))
    have hlow : ∀ i j, j < i → B i j = 0 := by intro i j h; simp [B, h]
    have hdiag : ∀ i, B i i = 1 := by intro i; simp [B]
    have hdet : B.det = 1 := by
      rw [Matrix.det_of_upperTriangular hlow]
      simp [hdiag]
    let g := Matrix.nonsingInvUnit B (by rw [hdet]; exact isUnit_one)
    have hgB : ((ι g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) = fun i j => ((B i j : _) : s.v.adicCompletion (maximalRealSubfield L)) := rfl
    have hlowK : ∀ a b : Fin n, b < a → Valued.v (((ι g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
      intro a b h
      rw [hgB]
      simp only [hlow a b h, ZeroMemClass.coe_zero, map_zero]
      exact zero_lt_one
    refine ⟨g, (hmem g).2 ⟨⟨⟨g, rfl⟩, fun a b ha hb => hlowK a b ?_⟩, fun a b _ _ => ⟨fun hba => hlowK a b hba, fun hab => ?_⟩⟩, ?_⟩
    · exact Fin.lt_def.2 (by omega)
    · subst hab
      rw [hgB]
      simp only [hdiag, OneMemClass.coe_one, sub_self, map_zero]
      exact zero_lt_one
    · apply Units.ext
      ext i j
      show IsLocalRing.residue _ (toVS s.v (B i j)) = (M : Matrix (Fin n) (Fin n) _) i j
      by_cases hji : j < i
      · rw [hlow i j hji, map_zero, map_zero]
        exact (h0 hji).symm
      · by_cases hij : i = j
        · subst hij
          rw [hdiag, map_one, map_one, h1]
        · simp only [B, if_neg hji, if_neg hij]
          exact Function.surjInv_eq _ _
  refine Nat.Coprime.coprime_dvd_left (Subgroup.index_dvd_of_le hU) ?_
  rw [unip_index]
  exact coprime_prod_pow_sub_one n hp (prime_dvd_card_residue s.v hp hA) Nat.card_pos

end GlobalTheory.UniLevelIndex
