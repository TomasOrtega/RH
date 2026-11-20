import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharExistsOfGreen
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumUnipotentRadicalEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement

noncomputable section

namespace GlobalTheory.ParamLabel

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.GLq GlobalTheory.GoodCharsCompare GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Take `⟨hch, hip⟩` from `GlobalTheory.T.isCharacter_cuspidal_rootSum_regular (ZMod p) θ hθ d k hd hk`. Establish `hadd` using `(GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod p) θ k).1`. Use `⟨hd, ?_, fun a ha had => ?_⟩` and prove the remaining obligations. Establish `hs` using `GlobalTheory.T.star_virtualCharacter_eq_apply_inv _ _ (AddSubgroup.subset_closure (k := {χ | BI.IsChar ℂ ℂ χ}) hch)`. Take `⟨n, ρ, hρ⟩` from `hch`.

Establish `hρ' : ∀ x, (FDRep.of ρ).character x = (-1) ^ (d - 1) * psi (rootSum θ k) (Fin d → ZMod p) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod p)))` using `fun x => (hρ x).symm`. Use `⟨FDRep.of ρ, ?_, hρ'⟩` and prove the remaining obligations. Rewrite using `[FDRep.simple_iff_char_is_norm_one]`. Rewrite `hip` using `[(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties (ZMod p) d (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype, glCard]`. Rewrite using `[← hip]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Establish `h1 : ((-1 : ℂ) ^ (d - 1)) * ((-1 : ℂ) ^ (d - 1)) = 1`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Rewrite using `[hρ', hρ', ← hs x, star_mul', star_pow, star_neg, star_one, mul_mul_mul_comm, h1, one_mul]`.

Establish `h` using `GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive (ZMod p) d _ (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse (ZMod p) (Fin d → ZMod p) _ hadd) a ha had`. Rewrite `h` using `[finsum_mem_def, finsum_eq_sum_of_fintype]`. Establish `h2` using `congrArg (fun z : ℂ => (-1 : ℂ) ^ (d - 1) * z) h`. Simplify using `only [mul_zero, Finset.mul_sum] at h2`. Unfold `res`.

Use `mul_eq_zero_of_right _ (Eq.trans ?_ h2)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Distinguish the cases in `hu : u ∈ (Formalism.D.Classical.grUnipBlock d a : Set (GL (Fin d) (ZMod p)))`. Rewrite using `[if_pos ((GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).1 hu), Set.indicator_of_mem (by exact hu)]`. Rewrite using `[if_neg (mt (GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).2 hu), Set.indicator_of_notMem (by exact hu), mul_zero]`.
-/
theorem isCusp_psi (θ : Fbar p →* ℂ) (hθ : ∀ x y : Fbar p, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) {d k : ℕ} (hd : 0 < d)
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card (ZMod p) ^ i ≡ k [MOD Nat.card (ZMod p) ^ d - 1]) :
    IsCusp (fun x : Gn p d => (-1) ^ (d - 1) *
      psi (rootSum θ k) (Fin d → ZMod p) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod p)))) := by
  classical
  obtain ⟨hch, hip⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular (ZMod p) θ hθ d k hd hk
  have hadd := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod p) θ k).1
  refine ⟨hd, ?_, fun a ha had => ?_⟩
  · have hs := GlobalTheory.T.star_virtualCharacter_eq_apply_inv _ _ (AddSubgroup.subset_closure (k := {χ | BI.IsChar ℂ ℂ χ}) hch)
    obtain ⟨n, ρ, hρ⟩ := hch
    have hρ' : ∀ x, (FDRep.of ρ).character x = (-1) ^ (d - 1) *
      psi (rootSum θ k) (Fin d → ZMod p) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod p))) :=
      fun x => (hρ x).symm
    refine ⟨FDRep.of ρ, ?_, hρ'⟩
    rw [FDRep.simple_iff_char_is_norm_one]
    rw [(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties (ZMod p) d (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype, glCard] at hip
    rw [← hip]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : ((-1 : ℂ) ^ (d - 1)) * ((-1 : ℂ) ^ (d - 1)) = 1 := by
      rw [← mul_pow]; simp
    rw [hρ', hρ', ← hs x, star_mul', star_pow, star_neg, star_one, mul_mul_mul_comm, h1, one_mul]
  · have h := GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive (ZMod p) d _ (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse (ZMod p) (Fin d → ZMod p) _ hadd) a ha had
    rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
    have h2 := congrArg (fun z : ℂ => (-1 : ℂ) ^ (d - 1) * z) h
    simp only [mul_zero, Finset.mul_sum] at h2
    unfold res
    refine mul_eq_zero_of_right _ (Eq.trans ?_ h2)
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ (Formalism.D.Classical.grUnipBlock d a : Set (GL (Fin d) (ZMod p)))
    · rw [if_pos ((GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).1 hu), Set.indicator_of_mem (by exact hu)]
    · rw [if_neg (mt (GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).2 hu), Set.indicator_of_notMem (by exact hu), mul_zero]

/- English proof (translation)
Establish `hp : IsPrimitiveRoot (L.gen d) (p ^ d - 1)` using `L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _`. Use `haveI : NeZero (p ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩`. Take `⟨n, -, rfl⟩` from `hp.eq_pow_of_pow_eq_one hz`. Rewrite using `[Model.thetaOf_gen_pow L hd (by rw [← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow]), ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm]`.
-/
theorem thetaOf_gen (L : LabelDatum p) {d : ℕ} (hd : 0 < d) (k : ℕ) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    thetaOf L d (L.gen d ^ k) z = L.teich z ^ k := by
  have hp : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  haveI : NeZero (p ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨n, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hz
  rw [Model.thetaOf_gen_pow L hd (by rw [← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow]),
    ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm]

/- English proof (translation)
Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow (g_pow_sub_pos hd).ne']`. Conclude with `zero_ne_one hz`. Set `u : Tor p d` to `⟨Units.mk0 z hz0, (mem_rootsOfUnity _ _).2 (Units.ext (by simpa using hz))⟩`.

Establish `hinj : Function.Injective (fun u : Tor p d => ((u : (Fbar p)ˣ) : Fbar p))` using `fun a b e => Subtype.ext (Units.ext e)`. Conclude with `(hinj.extend_apply (fun u => ((θ u : ℂˣ) : ℂ)) 0 u).trans (h u)`.
-/
theorem torVal_eq {d : ℕ} (hd : 0 < d) (θ : Tor p d →* ℂˣ) (F : Fbar p → ℂ)
    (h : ∀ u : Tor p d, ((θ u : ℂˣ) : ℂ) = F ((u : (Fbar p)ˣ) : Fbar p)) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    torVal θ z = F z := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (g_pow_sub_pos hd).ne'] at hz
    exact zero_ne_one hz
  let u : Tor p d := ⟨Units.mk0 z hz0, (mem_rootsOfUnity _ _).2 (Units.ext (by simpa using hz))⟩
  have hinj : Function.Injective (fun u : Tor p d => ((u : (Fbar p)ˣ) : Fbar p)) :=
    fun a b e => Subtype.ext (Units.ext e)
  exact (hinj.extend_apply (fun u => ((θ u : ℂˣ) : ℂ)) 0 u).trans (h u)

/- English proof (translation)
Use function extensionality and compare the values at `y`. Take `⟨x, hx, hx'⟩` from `exists_preimage hω hd (z := rootC (p ^ Fintype.card ι - 1) ^ k) (by rw [← pow_mul, mul_comm, pow_mul, (rootC_prim (g := p) hd).pow_eq_one, one_pow])`. Establish `hM : (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι)).det ≠ 0`. Rewrite using `[Matrix.det_submatrix_equiv_self]`. Conclude with `y.det_ne_zero`.

Establish `e1 : cuspOn θ y = cuspVal ω x (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι))`. Unfold `cuspOn cuspChar cuspVal`. Use `split_ifs with hh`. Take `⟨q, m, hq, hm⟩` from `hh`. Use `congr 1`.

Use `Finset.sum_congr rfl fun z hz => ?_` and prove the remaining obligations. Establish `hz1` using `root_pow hM hq hm (y := z) (Multiset.mem_toFinset.1 hz)`. Take `⟨a, ha⟩` from `exists_log ω hd hz1`. Rewrite using `[torVal_eq hd θ (fun z => ω z ^ k) h hz1, labelChar_eq ω hd hx ha, hx', ha, ← pow_mul, ← pow_mul, mul_comm a k]`. Both sides reduce to the same expression.

Both sides reduce to the same expression. Rewrite using `[e1, GlobalTheory.CuspFormula.cuspVal_eq_psi ω hd hx hx' _ hM, ← GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj _ _ _ _ (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (Fintype.equivFin ι)) (Matrix.toLin' y.val)]`. Use `congr 2`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Use `show Matrix.toLin' (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm y.val) v = _`.

Rewrite using `[Matrix.toLin'_reindex]`. Both sides reduce to the same expression.
-/
theorem cuspOn_eq_psi {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι) {ω : Fbar p →*₀ ℂ}
    (hω : Function.Injective ω) (θ : Tor p (Fintype.card ι) →* ℂˣ) (k : ℕ)
    (h : ∀ u : Tor p (Fintype.card ι), ((θ u : ℂˣ) : ℂ) = ω ((u : (Fbar p)ˣ) : Fbar p) ^ k) :
    cuspOn θ = fun y : Gn p (Fintype.card ι) => (-1) ^ (Fintype.card ι - 1) *
      psi (rootSum (ω : Fbar p →* ℂ) k) (Fin (Fintype.card ι) → ZMod p) (Matrix.toLin' y.val) := by
  classical
  funext y
  obtain ⟨x, hx, hx'⟩ := exists_preimage hω hd (z := rootC (p ^ Fintype.card ι - 1) ^ k)
    (by rw [← pow_mul, mul_comm, pow_mul, (rootC_prim (g := p) hd).pow_eq_one, one_pow])
  have hM : (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι)).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self]
    exact y.det_ne_zero
  have e1 : cuspOn θ y = cuspVal ω x (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι)) := by
    unfold cuspOn cuspChar cuspVal
    split_ifs with hh
    · obtain ⟨q, m, hq, hm⟩ := hh
      congr 1
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz1 := root_pow hM hq hm (y := z) (Multiset.mem_toFinset.1 hz)
      obtain ⟨a, ha⟩ := exists_log ω hd hz1
      rw [torVal_eq hd θ (fun z => ω z ^ k) h hz1, labelChar_eq ω hd hx ha, hx', ha, ← pow_mul, ← pow_mul,
        mul_comm a k]
      rfl
    · rfl
  rw [e1, GlobalTheory.CuspFormula.cuspVal_eq_psi ω hd hx hx' _ hM,
    ← GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj _ _ _ _ (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (Fintype.equivFin ι)) (Matrix.toLin' y.val)]
  congr 2
  refine LinearMap.ext fun v => ?_
  show Matrix.toLin' (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm y.val) v = _
  rw [Matrix.toLin'_reindex]
  rfl

/- English proof (translation)
Take `⟨hx1, hθ⟩` from `hL`. Establish `hp : IsPrimitiveRoot (L.gen (Fintype.card ι)) (p ^ Fintype.card ι - 1)` using `L.gen_order _ hd ▸ IsPrimitiveRoot.orderOf _`. Use `haveI : NeZero (p ^ Fintype.card ι - 1) := ⟨(g_pow_sub_pos hd).ne'⟩`. Take `⟨k, -, rfl⟩` from `hp.eq_pow_of_pow_eq_one hx1`. Take `⟨ω, hω, he⟩` from `exists_ext (ι := Units.map L.teich) fun a b e => Units.ext (L.teich_inj _ _ a.ne_zero b.ne_zero (congrArg Units.val e))`.

Establish `he' : ∀ z : Fbar p, z ^ (p ^ Fintype.card ι - 1) = 1 → L.teich z = ω z`. Introduce `z hz`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow (g_pow_sub_pos hd).ne']`.

Conclude with `zero_ne_one hz`. Conclude with `he (Units.mk0 z hz0)`. Establish `e` using `cuspOn_eq_psi hd hω θ k fun u => by`. Establish `hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ Fintype.card ι - 1) = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]`.

Rewrite using `[hθ, thetaOf_gen L hd k hu, he' _ hu]`. Establish `hc : Nat.card (ZMod p) = p` using `Nat.card_zmod p`. Use `⟨⟨minpoly.monic (isInt _), minpoly.irreducible (isInt _), minpoly.coeff_zero_ne_zero (isInt _) (pow_ne_zero _ (hp.ne_zero (g_pow_sub_pos hd).ne')), hx⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `isCusp_psi _ (fun _ _ _ _ h => hω h) hd (GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow (ZMod p) _ k (L.gen _) hd (by rw [hc]; exact L.gen_order _ hd) hx)`.

Introduce `x₀ hx₀ y hy z hz`. Take `⟨j, rfl⟩` from `mem_roots_minpoly.1 hx₀`. Establish `hz1` using `root_pow y.det_ne_zero hy (pow_one _).symm hz`. Rewrite `hz1` using `[Fintype.card_fin]`. Establish `h` using `GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible (ZMod p) _ _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod p) (ω : Fbar p →* ℂ) k).1 (Matrix.toLin' y.val) (by rw [Matrix.charpoly_toLin']; exact hy)`.

Rewrite `h` using `[Matrix.charpoly_toLin']`. Rewrite using `[e]`. Use `show _ * _ = _`. Rewrite using `[h]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `((Formalism.CyclotomicNorms.rootsBar _).map _).sum = _`. Establish `hnd : y.val.charpoly.natDegree = Fintype.card ι` using `by simp`. Rewrite using `[GlobalTheory.GreenExists.rootsBar_eq hy ((mem_rootsBar hy.ne_zero).1 hz), hnd, Multiset.map_map]`. Establish `hs` using `sum_shift (g := p) (z := ω z) (m := k) (e := Fintype.card ι) (by rw [mul_comm, pow_mul, ← map_pow, pow_g_of hz1]) j`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hs.symm.trans (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations.

Simplify using `only [Function.comp, MonoidHom.coe_coe, map_pow, ← pow_mul, mul_comm]`. Establish `hzi : (z ^ p ^ i) ^ (p ^ Fintype.card ι - 1) = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hz1, one_pow]`. Rewrite using `[← pow_mul (L.gen _), thetaOf_gen L hd _ hzi, he' _ hzi, map_pow, ← pow_mul, ← pow_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isCuspOf_cuspOn (L : LabelDatum p) {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p) (hd : 0 < Fintype.card ι) (hL : LabelsChar L θ x)
    (hx : (minpoly (ZMod p) x).natDegree = Fintype.card ι) : IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) := by
  classical
  obtain ⟨hx1, hθ⟩ := hL
  have hp : IsPrimitiveRoot (L.gen (Fintype.card ι)) (p ^ Fintype.card ι - 1) :=
    L.gen_order _ hd ▸ IsPrimitiveRoot.orderOf _
  haveI : NeZero (p ^ Fintype.card ι - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨k, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx1
  obtain ⟨ω, hω, he⟩ := exists_ext (ι := Units.map L.teich) fun a b e =>
    Units.ext (L.teich_inj _ _ a.ne_zero b.ne_zero (congrArg Units.val e))
  have he' : ∀ z : Fbar p, z ^ (p ^ Fintype.card ι - 1) = 1 → L.teich z = ω z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (g_pow_sub_pos hd).ne'] at hz
      exact zero_ne_one hz
    exact he (Units.mk0 z hz0)
  have e := cuspOn_eq_psi hd hω θ k fun u => by
    have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ Fintype.card ι - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
    rw [hθ, thetaOf_gen L hd k hu, he' _ hu]
  have hc : Nat.card (ZMod p) = p := Nat.card_zmod p
  refine ⟨⟨minpoly.monic (isInt _), minpoly.irreducible (isInt _),
    minpoly.coeff_zero_ne_zero (isInt _) (pow_ne_zero _ (hp.ne_zero (g_pow_sub_pos hd).ne')), hx⟩, ?_, ?_⟩
  · rw [e]
    exact isCusp_psi _ (fun _ _ _ _ h => hω h) hd
      (GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow (ZMod p) _ k (L.gen _) hd (by rw [hc]; exact L.gen_order _ hd) hx)
  · intro x₀ hx₀ y hy z hz
    obtain ⟨j, rfl⟩ := mem_roots_minpoly.1 hx₀
    have hz1 := root_pow y.det_ne_zero hy (pow_one _).symm hz
    rw [Fintype.card_fin] at hz1
    have h := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible (ZMod p) _ _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod p) (ω : Fbar p →* ℂ) k).1
      (Matrix.toLin' y.val) (by rw [Matrix.charpoly_toLin']; exact hy)
    rw [Matrix.charpoly_toLin'] at h
    rw [e]
    show _ * _ = _
    rw [h]
    congr 1
    change ((Formalism.CyclotomicNorms.rootsBar _).map _).sum = _
    have hnd : y.val.charpoly.natDegree = Fintype.card ι := by simp
    rw [GlobalTheory.GreenExists.rootsBar_eq hy ((mem_rootsBar hy.ne_zero).1 hz), hnd, Multiset.map_map]
    have hs := sum_shift (g := p) (z := ω z) (m := k) (e := Fintype.card ι)
      (by rw [mul_comm, pow_mul, ← map_pow, pow_g_of hz1]) j
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hs.symm.trans (Finset.sum_congr rfl fun i _ => ?_))
    · simp only [Function.comp, MonoidHom.coe_coe, map_pow, ← pow_mul, mul_comm]
    · have hzi : (z ^ p ^ i) ^ (p ^ Fintype.card ι - 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
      rw [← pow_mul (L.gen _), thetaOf_gen L hd _ hzi, he' _ hzi, map_pow, ← pow_mul, ← pow_mul]
      congr 1
      ring

/- English proof (translation)
Introduce `_ _ _ L _ _ _ _ θ x hd hL hx` and use `isCuspOf_cuspOn L θ x hd hL hx`.
-/
theorem isCuspOf_cuspOn_of_green : GlobalTheory.GLq.Green → ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p), 5 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p), 0 < Fintype.card ι → LabelsChar L θ x → (minpoly (ZMod p) x).natDegree = Fintype.card ι → GlobalTheory.GLq.IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) :=
  fun _ _ _ L _ _ _ _ θ x hd hL hx => isCuspOf_cuspOn L θ x hd hL hx

end GlobalTheory.ParamLabel
