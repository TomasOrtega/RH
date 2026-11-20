import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

namespace GlobalTheory.CechOne

/- English proof (translation)
Introduce `R _ F E s hs`. Take `⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩` from `GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F`. Take `⟨z, hz0, hz⟩` from `hs`. Rewrite `hz0` using `[CohomologyClass.mk_eq_zero_iff]`. Take `⟨m, hm, β, hβ⟩` from `hz0`.

Take `rfl : m = 0` from `by push_cast at hm; omega`. Establish `hzv : ∀ (p q : ℤ) (hpq : p + ((1 : ℕ) : ℤ) = q), (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)).v p q hpq = (Cochain.single (p` using `-((1 : ℕ) : ℤ)) (q := 0) ((chainsXIso R E 1).hom ≫ s ≫ resι R F) ((1 : ℕ) : ℤ)).v p q hpq := by`. Introduce `p q hpq`. Rewrite using `[show (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)) = z.1 from rfl, hz]`. Set `b` to `β.v 0 0 (by omega)`.

Establish `hb : b ≫ (res R F).d 0 1 = 0`. Establish `e` using `Cochain.congr_v hβ 0 1 (by norm_num)`. Rewrite `e` using `[δ_v 0 _ (by norm_num) β 0 1 _ 0 1 (by omega) rfl, (hpos E 1 (by norm_num)).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero, hzv, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]`. Conclude with `e`. Use `haveI : Mono (ShortComplex.mk _ _ w).f := hmono`.

Set `t' : ((chains R).obj E).X 0 ⟶ F` to `hex.lift b hb`. Establish `ht' : t' ≫ resι R F = b` using `hex.lift_f b hb`. Establish `e` using `Cochain.congr_v hβ (-((1 : ℕ) : ℤ)) 0 (by omega)`. Establish `h1 : β.v (-((1 : ℕ) : ℤ)) (-1) (by omega) = 0` using `(hneg (-1) (by norm_num)).eq_of_tgt _ _`. Rewrite `e` using `[δ_v 0 _ (by norm_num) β _ 0 _ (-1) 0 (by omega) (by norm_num), h1, zero_comp, zero_add, hzv, Cochain.single_v]`.

Rewrite `e` using `[show β.v 0 0 (by omega) = b from rfl, ← ht']`. Set `D : (free R).obj (E.obj (op ⦋1⦌)) ⟶ (free R).obj (E.obj (op ⦋0⦌))` to `∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)`. Establish `hd : ((chains R).obj E).d (-((1 : ℕ) : ℤ)) 0 = (chainsXIso R E 1).hom ≫ D ≫ (chainsXIso R E 0).inv` using `GlobalTheory.EtC.ClsBasic.chains_d (R := R) E 0`. Rewrite `e` using `[hd]`. Establish `hs : s = (((1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E 0).inv ≫ t')`.

Apply `(cancel_epi (chainsXIso R E 1).hom).1` to reduce the goal to its premises. Apply `(cancel_mono (resι R F)).1` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← e]`. Simplify using `only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]`. Use `⟨(((1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E 0).inv ≫ t'), ?_⟩` and prove the remaining obligations.

Rewrite using `[hs]`. Simplify using `only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum, smul_smul, Category.assoc]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem cobd_of_isCls_zero : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (s : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F), IsCls s (0 : H R E F ((1 : ℕ) : ℤ)) → ∃ t : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, s = cobd t := by
  intro R _ F E s hs
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, hz0, hz⟩ := hs
  rw [CohomologyClass.mk_eq_zero_iff] at hz0
  obtain ⟨m, hm, β, hβ⟩ := hz0
  obtain rfl : m = 0 := by push_cast at hm; omega
  have hzv : ∀ (p q : ℤ) (hpq : p + ((1 : ℕ) : ℤ) = q),
      (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)).v p q hpq =
        (Cochain.single (p := -((1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E 1).hom ≫ s ≫ resι R F) ((1 : ℕ) : ℤ)).v p q hpq := by
    intro p q hpq
    rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)) = z.1 from rfl, hz]
  let b := β.v 0 0 (by omega)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v hβ 0 1 (by norm_num)
    rw [δ_v 0 _ (by norm_num) β 0 1 _ 0 1 (by omega) rfl,
      (hpos E 1 (by norm_num)).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero, hzv,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
    exact e
  haveI : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  have e := Cochain.congr_v hβ (-((1 : ℕ) : ℤ)) 0 (by omega)
  have h1 : β.v (-((1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
  rw [δ_v 0 _ (by norm_num) β _ 0 _ (-1) 0 (by omega) (by norm_num), h1,
    zero_comp, zero_add, hzv, Cochain.single_v] at e
  rw [show β.v 0 0 (by omega) = b from rfl, ← ht'] at e
  let D : (free R).obj (E.obj (op ⦋1⦌)) ⟶ (free R).obj (E.obj (op ⦋0⦌)) :=
    ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
  have hd : ((chains R).obj E).d (-((1 : ℕ) : ℤ)) 0 = (chainsXIso R E 1).hom ≫ D ≫ (chainsXIso R E 0).inv :=
    GlobalTheory.EtC.ClsBasic.chains_d (R := R) E 0
  rw [hd] at e
  have hs : s = (((1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E 0).inv ≫ t') := by
    apply (cancel_epi (chainsXIso R E 1).hom).1
    apply (cancel_mono (resι R F)).1
    rw [Category.assoc, ← e]
    simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  refine ⟨(((1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E 0).inv ≫ t'), ?_⟩
  rw [hs]
  simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
    smul_smul, Category.assoc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

end GlobalTheory.CechOne
