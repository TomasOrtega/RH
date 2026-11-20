import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.ZeroGrp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

def autOf (A : GL (Fin n) (𝓞 E)) : Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinear (Matrix.toLin' (A.1.map (algebraMap (𝓞 E) E))) (Matrix.toLin' ((A⁻¹).1.map (algebraMap (𝓞 E) E)))
    (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one])

omit [StarRing E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem autOf_apply (A : GL (Fin n) (𝓞 E)) (x : Sp E n) (i : Fin n) :
    autOf A x i = ∑ j, algebraMap (𝓞 E) E (A.1 i j) * x j := rfl

omit [StarRing E] in
/- English proof (translation)
The claim follows from `LinearEquiv.ext fun _ => rfl`.
-/
theorem autOf_inv (A : GL (Fin n) (𝓞 E)) : (autOf A)⁻¹ = autOf A⁻¹ := LinearEquiv.ext fun _ => rfl

omit [StarRing E] in
/- English proof (translation)
Rewrite using `[CongLevel.extE_apply, Pi.add_apply, CongLevel.inX_apply]`. Use `split_ifs with h`. Establish `: CongLevel.resX c v ⟨l.1, h⟩ = v l` using `rfl`. Rewrite using `[Pi.sub_apply, this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[add_zero]`.
-/
theorem extE_lt (c : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) (l : Fin (n + c)) :
    CongLevel.extE c g v l = if h : l.1 < n then g (CongLevel.resX c v) ⟨l.1, h⟩ else v l := by
  rw [CongLevel.extE_apply, Pi.add_apply, CongLevel.inX_apply]
  split_ifs with h
  · have : CongLevel.resX c v ⟨l.1, h⟩ = v l := rfl
    rw [Pi.sub_apply, this]
    ring
  · rw [add_zero]

/- English proof (translation)
Rewrite `hv`, the goal using `[CongLevel.mem_sclLat]`. Introduce `l`. Rewrite using `[extE_lt]`. Use `split_ifs with h`. Rewrite using `[autOf_apply, Finset.mul_sum]`.

Use `TopStep.intAt_sum _ fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j.1 < l.1`. Rewrite using `[hA ⟨l.1, h⟩ j hj]`. Simplify using `using TopStep.intAt_zero`. Take `⟨d, hd⟩` from `Int.le.dest (he l.1 j.1 (by omega) j.2)`.

Establish `h1` using `((IntAt.coe P (A.1 ⟨l.1, h⟩ j)).mul (TopStep.intAt_pow (TopStep.intAt_nat q) d)).mul (hv (Fin.castAdd c j))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Establish `: CongLevel.resX c v j = v (Fin.castAdd c j)` using `rfl`. Rewrite using `[this, Fin.val_castAdd, ← hd, zpow_add₀ hq, zpow_natCast]`. Use `zpow_ne_zero (e l.1) hq` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Conclude with `hv l`.
-/
theorem extE_maps_scl {q c : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (he : ∀ i j, i ≤ j → j < n → e i ≤ e j)
    (A : GL (Fin n) (𝓞 E)) (hA : ∀ i j : Fin n, j.1 < i.1 → A.1 i j = 0) (v : Sp E (n + c))
    (hv : v ∈ LocE.sclLat P q (n + c) e) : CongLevel.extE c (autOf A) v ∈ LocE.sclLat P q (n + c) e := by
  rw [CongLevel.mem_sclLat] at hv ⊢
  intro l
  rw [extE_lt]
  split_ifs with h
  · rw [autOf_apply, Finset.mul_sum]
    refine TopStep.intAt_sum _ fun j _ => ?_
    by_cases hj : j.1 < l.1
    · rw [hA ⟨l.1, h⟩ j hj]
      simpa using TopStep.intAt_zero
    · obtain ⟨d, hd⟩ := Int.le.dest (he l.1 j.1 (by omega) j.2)
      have h1 := ((IntAt.coe P (A.1 ⟨l.1, h⟩ j)).mul (TopStep.intAt_pow (TopStep.intAt_nat q) d)).mul
        (hv (Fin.castAdd c j))
      convert h1 using 1
      have : CongLevel.resX c v j = v (Fin.castAdd c j) := rfl
      rw [this, Fin.val_castAdd, ← hd, zpow_add₀ hq, zpow_natCast]
      have := zpow_ne_zero (e l.1) hq
      field_simp
  · exact hv l

/- English proof (translation)
Substitute `ha` using the available equality. Rewrite using `[mem_uniUT]`. Use `⟨fun h => ⟨fun i j => h.2.1 i j i.2, fun i => h.2.2 i i.2⟩, fun h => ⟨fun i j hij => ?_, fun i j _ => h.1 i j, fun i _ => h.2 i⟩⟩` and prove the remaining obligations. Establish `: coarse n [] j.1 < coarse n [] i.1` using `hij`. Rewrite `this` using `[coarse_of_lt i.2]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem uni_iff {κ : Type} [CommRing κ] {a : ℕ} (ha : n = a) {M : GL (Fin n) κ} :
    M ∈ uniUT n κ a [] ↔ (∀ i j : Fin n, j.1 < i.1 → M.1 i j = 0) ∧ ∀ i, M.1 i i = 1 := by
  subst ha
  rw [mem_uniUT]
  refine ⟨fun h => ⟨fun i j => h.2.1 i j i.2, fun i => h.2.2 i i.2⟩, fun h => ⟨fun i j hij => ?_, fun i j _ => h.1 i j,
    fun i _ => h.2 i⟩⟩
  have : coarse n [] j.1 < coarse n [] i.1 := hij
  rw [coarse_of_lt i.2] at this
  omega

/- English proof (translation)
Introduce `v`. Use `⟨fun hv => ?_, extE_maps_scl hq e he A ((uni_iff rfl).1 hA).1 v⟩` and prove the remaining obligations. Establish `h` using `extE_maps_scl hq e he A⁻¹ ((uni_iff rfl).1 (inv_mem hA)).1 _ hv`. Rewrite `h` using `[← autOf_inv, ← CongLevel.extE_inv]`. Rewrite `h` using `[show (CongLevel.extE c (autOf A))⁻¹ (CongLevel.extE c (autOf A) v) = v from LinearEquiv.symm_apply_apply _ v]`. Then use the resulting hypothesis.
-/
theorem extE_stab_scl {q c : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (he : ∀ i j, i ≤ j → j < n → e i ≤ e j)
    (A : GL (Fin n) (𝓞 E)) (hA : A ∈ uniUT n (𝓞 E) n []) :
    CongLevel.extE c (autOf A) ∈ stabL E (n + c) (LocE.sclLat P q (n + c) e) := by
  intro v
  refine ⟨fun hv => ?_, extE_maps_scl hq e he A ((uni_iff rfl).1 hA).1 v⟩
  have h := extE_maps_scl hq e he A⁻¹ ((uni_iff rfl).1 (inv_mem hA)).1 _ hv
  rw [← autOf_inv, ← CongLevel.extE_inv] at h
  rwa [show (CongLevel.extE c (autOf A))⁻¹ (CongLevel.extE c (autOf A) v) = v from LinearEquiv.symm_apply_apply _ v] at h

omit [NumberField E] [StarRing E] in
/- English proof (translation)
Establish `h1 : LocE.fIdx n c n (symIdxInv n rS (f.1 + rS)) = f.1`. Use `f.2` as an intermediate fact. Unfold `LocE.fIdx symIdxInv`. Apply the tactic sequence `split_ifs <;> omega`. Unfold `LocE.bvecS LocE.bvecG`.

Rewrite using `[h1]`. Unfold `LocE.scE`. Rewrite using `[if_pos f.2, zpow_zero, one_smul]`. Use function extensionality and compare the values at `l`. Rewrite using `[CongLevel.inX_apply]`.

Unfold `Loc.eN`. Use `f.2` as an intermediate fact. Distinguish the cases in `h : l.1 < n`. Rewrite using `[dif_pos h, Pi.single_apply]`. Simplify using `[Fin.ext_iff]`.

Rewrite using `[dif_neg h, if_neg (by omega)]`.
-/
theorem bvecS_eq (q rS c : ℕ) (f : Fin n) :
    LocE.bvecS E q n rS n c (f.1 + rS) = Loc.inX E n c (Pi.single f 1) := by
  have h1 : LocE.fIdx n c n (symIdxInv n rS (f.1 + rS)) = f.1 := by
    have := f.2
    unfold LocE.fIdx symIdxInv
    split_ifs <;> omega
  unfold LocE.bvecS LocE.bvecG
  rw [h1]
  unfold LocE.scE
  rw [if_pos f.2, zpow_zero, one_smul]
  funext l
  rw [CongLevel.inX_apply]
  unfold Loc.eN
  have := f.2
  by_cases h : l.1 < n
  · rw [dif_pos h, Pi.single_apply]
    simp [Fin.ext_iff]
  · rw [dif_neg h, if_neg (by omega)]

/- English proof (translation)
Unfold `LocE.flagS`. Rewrite using `[CongLevel.mem_sclLat]`. Establish `key : ∀ l, l < n → (LocE.scE n (fun i => i + 1) l + if LocE.bd5 n rS (f.1 + rS) ≤ symIdx n rS (LocE.fPos n c n l) then (1 : ℤ) else 0) = if f.1 ≤ l then 1 else 0`. Introduce `l hl`. Use `f.2` as an intermediate fact.

Unfold `LocE.scE LocE.bd5 LocE.fPos symIdx`. Rewrite using `[if_pos hl, if_pos hl, if_pos hl, if_neg (by omega : ¬ f.1 + rS = rS + n), zero_add]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce `h l`.

Establish `h1` using `h (Fin.castAdd c l)`. Rewrite `h1` using `[key _ (by simp), CongLevel.inX_apply, dif_pos (by simp)]`. Conclude with `h1`. Introduce `h l`. Rewrite using `[CongLevel.inX_apply]`.

Distinguish the cases in `hl : l.1 < n`. Rewrite using `[dif_pos hl, key _ hl]`. Conclude with `h ⟨l.1, hl⟩`. Rewrite using `[dif_neg hl, mul_zero]`. Conclude with `TopStep.intAt_zero`.
-/
theorem inX_mem_flagS (q rS c : ℕ) (f : Fin n) (x : Sp E n) :
    Loc.inX E n c x ∈ LocE.flagS P q n rS n c (f.1 + rS) ↔
      ∀ l : Fin n, IntAt P (((q : E) ^ (if f.1 ≤ l.1 then (1 : ℤ) else 0))⁻¹ * x l) := by
  unfold LocE.flagS
  rw [CongLevel.mem_sclLat]
  have key : ∀ l, l < n → (LocE.scE n (fun i => i + 1) l +
      if LocE.bd5 n rS (f.1 + rS) ≤ symIdx n rS (LocE.fPos n c n l) then (1 : ℤ) else 0) = if f.1 ≤ l then 1 else 0 := by
    intro l hl
    have := f.2
    unfold LocE.scE LocE.bd5 LocE.fPos symIdx
    rw [if_pos hl, if_pos hl, if_pos hl, if_neg (by omega : ¬ f.1 + rS = rS + n), zero_add]
    simp
  constructor
  · intro h l
    have h1 := h (Fin.castAdd c l)
    rw [key _ (by simp), CongLevel.inX_apply, dif_pos (by simp)] at h1
    exact h1
  · intro h l
    rw [CongLevel.inX_apply]
    by_cases hl : l.1 < n
    · rw [dif_pos hl, key _ hl]
      exact h ⟨l.1, hl⟩
    · rw [dif_neg hl, mul_zero]
      exact TopStep.intAt_zero

/- English proof (translation)
Establish `hs : ∀ s, CongLevel.extE c (autOf A) ∈ stabL E (n + c) (LocE.flagS P q n rS n c s)`. Introduce `s`. Use `extE_stab_scl hq _ (fun i j hij hj => ?_) A hA` and prove the remaining obligations. Establish `hi : i < n` using `by omega`. Unfold `LocE.scE LocE.fPos symIdx`.

Simplify using `only [if_pos hi, if_pos hj]`. Apply the tactic sequence `split_ifs <;> omega`. Use `⟨extE_stab_scl hq _ (fun i j hij hj => ?_) A hA, fun s _ => hs s, fun s _ => ⟨hs s, ?_⟩⟩` and prove the remaining obligations. Unfold `LocE.scE`. Rewrite using `[if_pos hj, if_pos (by omega)]`.

Distinguish the cases in `h : rS ≤ s ∧ s < rS + n`. Take `⟨f, rfl⟩ : ∃ f : Fin n, s = f.1 + rS` from `⟨⟨s - rS, by omega⟩, by simp only; omega⟩`. Rewrite using `[bvecS_eq, CongLevel.extE_inX, ← map_sub, inX_mem_flagS]`. Introduce `l`. Take `⟨h1, h2⟩` from `(uni_iff rfl).1 hA`.

Establish `e : (autOf A (Pi.single f 1) - (Pi.single f 1 : Sp E n)) l = algebraMap (𝓞 E) E (A.1 l f) - (Pi.single f 1 : Sp E n) l`. Rewrite using `[Pi.sub_apply, autOf_apply]`. Simplify using `[Pi.single_apply]`. Rewrite using `[e]`. Use `split_ifs with hl`.

Distinguish the cases in `hlf : l = f`. Substitute `hlf` using the available equality. Simplify `TopStep.intAt_zero` using `[h2]`. Establish `: f.1 < l.1` using `lt_of_le_of_ne hl fun h => hlf (Fin.ext h.symm)`. Simplify `TopStep.intAt_zero` using `[h1 l f this, hlf]`.

Establish `hlf : l ≠ f` using `fun h => hl (h ▸ le_rfl)`. Simplify `IntAt.coe P (A.1 l f)` using `[hlf]`. Apply the tactic sequence `obtain ⟨i, hi⟩ : ∃ i, LocE.fIdx n c n (symIdxInv n rS s) = n + i := ⟨LocE.fIdx n c n (symIdxInv n rS s) - n, by unfold LocE.fIdx symIdxInv; split_ifs <;> omega⟩`. Unfold `LocE.bvecS LocE.bvecG`. Rewrite using `[hi, map_smul, CongLevel.extE_apply, CongLevel.resX_eN]`.

Simplify using the standard rewrite rules.
-/
theorem extE_mem_JGsym {q : ℕ} (hq : (q : E) ≠ 0) (rS r t c : ℕ) (A : GL (Fin n) (𝓞 E)) (hA : A ∈ uniUT n (𝓞 E) n []) :
    CongLevel.extE c (autOf A) ∈ LocE.JGsym P q n rS r t n c := by
  have hs : ∀ s, CongLevel.extE c (autOf A) ∈ stabL E (n + c) (LocE.flagS P q n rS n c s) := by
    intro s
    refine extE_stab_scl hq _ (fun i j hij hj => ?_) A hA
    have hi : i < n := by omega
    unfold LocE.scE LocE.fPos symIdx
    simp only [if_pos hi, if_pos hj]
    split_ifs <;> omega
  refine ⟨extE_stab_scl hq _ (fun i j hij hj => ?_) A hA, fun s _ => hs s, fun s _ => ⟨hs s, ?_⟩⟩
  · unfold LocE.scE
    rw [if_pos hj, if_pos (by omega)]
  · by_cases h : rS ≤ s ∧ s < rS + n
    · obtain ⟨f, rfl⟩ : ∃ f : Fin n, s = f.1 + rS := ⟨⟨s - rS, by omega⟩, by simp only; omega⟩
      rw [bvecS_eq, CongLevel.extE_inX, ← map_sub, inX_mem_flagS]
      intro l
      obtain ⟨h1, h2⟩ := (uni_iff rfl).1 hA
      have e : (autOf A (Pi.single f 1) - (Pi.single f 1 : Sp E n)) l =
          algebraMap (𝓞 E) E (A.1 l f) - (Pi.single f 1 : Sp E n) l := by
        rw [Pi.sub_apply, autOf_apply]
        simp [Pi.single_apply]
      rw [e]
      split_ifs with hl
      · by_cases hlf : l = f
        · subst hlf
          simpa [h2] using TopStep.intAt_zero
        · have : f.1 < l.1 := lt_of_le_of_ne hl fun h => hlf (Fin.ext h.symm)
          simpa [h1 l f this, hlf] using TopStep.intAt_zero
      · have hlf : l ≠ f := fun h => hl (h ▸ le_rfl)
        simpa [hlf] using IntAt.coe P (A.1 l f)
    · obtain ⟨i, hi⟩ : ∃ i, LocE.fIdx n c n (symIdxInv n rS s) = n + i :=
        ⟨LocE.fIdx n c n (symIdxInv n rS s) - n, by unfold LocE.fIdx symIdxInv; split_ifs <;> omega⟩
      unfold LocE.bvecS LocE.bvecG
      rw [hi, map_smul, CongLevel.extE_apply, CongLevel.resX_eN]
      simp

omit [StarRing E] in
/- English proof (translation)
Take `⟨h1, h2⟩` from `(uni_iff rfl).1 hM`. Use `choose a ha using fun i j => Ideal.Quotient.mk_surjective (M.1 i j)`. Set `B : Matrix (Fin n) (Fin n) (𝓞 E)` to `Matrix.of fun i j => if j.1 < i.1 then 0 else if i = j then 1 else a i j`. Establish `hB : B.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (M := B) (fun i j hij => if_pos (show j.1 < i.1 from hij))]`.

Simplify using `[B]`. Use `⟨Matrix.GeneralLinearGroup.mk'' B (by rw [hB]; exact isUnit_one), (uni_iff rfl).2 ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j => ?_⟩` and prove the remaining obligations. Conclude with `if_pos hij`. Use `show B i i = 1`. Simplify using `[B]`.

Use `show Ideal.Quotient.mk P.asIdeal (if j.1 < i.1 then 0 else if i = j then 1 else a i j) = _ split_ifs with c1 c2`. Rewrite using `[h1 i j c1, map_zero]`. Rewrite using `[c2, h2, map_one]`. Conclude with `ha i j`.
-/
theorem exists_lift (M : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) (hM : M ∈ uniUT n _ n []) :
    ∃ A ∈ uniUT n (𝓞 E) n [], ∀ i j, Ideal.Quotient.mk P.asIdeal (A.1 i j) = M.1 i j := by
  obtain ⟨h1, h2⟩ := (uni_iff rfl).1 hM
  choose a ha using fun i j => Ideal.Quotient.mk_surjective (M.1 i j)
  let B : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun i j => if j.1 < i.1 then 0 else if i = j then 1 else a i j
  have hB : B.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := B) (fun i j hij => if_pos (show j.1 < i.1 from hij))]
    simp [B]
  refine ⟨Matrix.GeneralLinearGroup.mk'' B (by rw [hB]; exact isUnit_one), (uni_iff rfl).2 ⟨fun i j hij => ?_, fun i => ?_⟩,
    fun i j => ?_⟩
  · exact if_pos hij
  · show B i i = 1
    simp [B]
  · show Ideal.Quotient.mk P.asIdeal (if j.1 < i.1 then 0 else if i = j then 1 else a i j) = _
    split_ifs with c1 c2
    · rw [h1 i j c1, map_zero]
    · rw [c2, h2, map_one]
    · exact ha i j

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hq` using `TopStep.qOf_ne_zero (P := P)`. Establish `hc : ∀ ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c), ρ ∈ Loc.Cbe (LocE.JGsym P (qOf P) n rS r t n c) 1 ↔ ρ ∈ Loc.R1 E n c ∧ ρ ∈ LocE.JGsym P (qOf P) n rS r t n c`. Introduce `ρ`. Simplify using `[Loc.Cbe]`.

Prove the components needed by the constructor for the conclusion. Introduce `hM`. Take `⟨A, hA, hAM⟩` from `exists_lift M hM`. Use `⟨autOf A, ⟨CongLevel.extE c (autOf A), (hc _).2 ⟨CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ _, extE_mem_JGsym hq _ _ _ _ A hA⟩, CongLevel.extE_inX _ _⟩, fun x hx => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `hx'` using `TopStep.mem_stdAt.1 hx`. Use `show redP P (autOf A x i) = ∑ j, M.1 i j * redP P (x j)`. Rewrite using `[autOf_apply, TopStep.reduction_sum₂ _ fun j _ => (IntAt.coe P _).mul (hx' j)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[reduction_mul (IntAt.coe P _) (hx' j), reduction_coe, hAM]`.

Introduce and unpack `⟨g, ⟨ρ, hρ, hg⟩, hM⟩`. Establish `key : ∀ f l : Fin n, f.1 ≤ l.1 → M.1 l f = (Pi.single f 1 : Fin n → 𝓞 E ⧸ P.asIdeal) l`. Introduce `f l hl`. Establish `h1` using `(((hc ρ).1 hρ).2.2.2 (f.1 + rS) (by have := f.2; omega)).2`. Rewrite `h1` using `[bvecS_eq, hg, ← map_sub, inX_mem_flagS]`.

Establish `h2` using `h1 l`. Rewrite `h2` using `[if_pos hl, zpow_one, mul_comm, ← div_eq_mul_inv, Pi.sub_apply]`. Establish `h3` using `TopStep.redP_eq_zero_of_div h2`. Establish `h4 : IntAt P (g (Pi.single f 1) l - (Pi.single f 1 : Sp E n) l)`. Use `(TopStep.intAt_nat (qOf P)).mul h2` as an intermediate fact.

Rewrite `this` using `[mul_div_cancel₀ _ hq]`. Then use the resulting hypothesis. Establish `h5` using `reduction_add h4 (TopStep.mem_stdAt.1 (TopStep.single_mem_stdAt (P := P) f) l)`. Rewrite `h5` using `[sub_add_cancel, h3, zero_add]`. Establish `h6` using `congrFun (hM _ (TopStep.single_mem_stdAt f)) l`. Rewrite `h6` using `[TopStep.redV_single, Matrix.mulVec_single_one]`.

Rewrite using `[← TopStep.redV_single]`. Conclude with `h6.symm.trans h5`. Use `(uni_iff rfl).2 ⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[key j i hij.le, Pi.single_eq_of_ne fun h => by rw [h] at hij; omega]`. Rewrite using `[key i i le_rfl, Pi.single_eq_same]`.
-/
theorem uni_iff_prX {k : ℕ} (hn : n = k) (rS r t c : ℕ) (hr : k + rS ≤ r) (M : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) :
    M ∈ uniUT n _ k [] ↔ ∃ g ∈ Loc.prX (Loc.Cbe (LocE.JGsym P (qOf P) k rS r t n c) 1),
      ∀ x ∈ stdAt E n P, redV P (g x) = M.1.mulVec (redV P x) := by
  subst hn
  have hq := TopStep.qOf_ne_zero (P := P)
  have hc : ∀ ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c), ρ ∈ Loc.Cbe (LocE.JGsym P (qOf P) n rS r t n c) 1 ↔
      ρ ∈ Loc.R1 E n c ∧ ρ ∈ LocE.JGsym P (qOf P) n rS r t n c := by
    intro ρ
    simp [Loc.Cbe]
  constructor
  · intro hM
    obtain ⟨A, hA, hAM⟩ := exists_lift M hM
    refine ⟨autOf A, ⟨CongLevel.extE c (autOf A), (hc _).2 ⟨CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ _, extE_mem_JGsym hq _ _ _ _ A hA⟩,
      CongLevel.extE_inX _ _⟩, fun x hx => ?_⟩
    funext i
    have hx' := TopStep.mem_stdAt.1 hx
    show redP P (autOf A x i) = ∑ j, M.1 i j * redP P (x j)
    rw [autOf_apply, TopStep.reduction_sum₂ _ fun j _ => (IntAt.coe P _).mul (hx' j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [reduction_mul (IntAt.coe P _) (hx' j), reduction_coe, hAM]
  · rintro ⟨g, ⟨ρ, hρ, hg⟩, hM⟩
    have key : ∀ f l : Fin n, f.1 ≤ l.1 → M.1 l f = (Pi.single f 1 : Fin n → 𝓞 E ⧸ P.asIdeal) l := by
      intro f l hl
      have h1 := (((hc ρ).1 hρ).2.2.2 (f.1 + rS) (by have := f.2; omega)).2
      rw [bvecS_eq, hg, ← map_sub, inX_mem_flagS] at h1
      have h2 := h1 l
      rw [if_pos hl, zpow_one, mul_comm, ← div_eq_mul_inv, Pi.sub_apply] at h2
      have h3 := TopStep.redP_eq_zero_of_div h2
      have h4 : IntAt P (g (Pi.single f 1) l - (Pi.single f 1 : Sp E n) l) := by
        have := (TopStep.intAt_nat (qOf P)).mul h2
        rwa [mul_div_cancel₀ _ hq] at this
      have h5 := reduction_add h4 (TopStep.mem_stdAt.1 (TopStep.single_mem_stdAt (P := P) f) l)
      rw [sub_add_cancel, h3, zero_add] at h5
      have h6 := congrFun (hM _ (TopStep.single_mem_stdAt f)) l
      rw [TopStep.redV_single, Matrix.mulVec_single_one] at h6
      rw [← TopStep.redV_single]
      exact h6.symm.trans h5
    refine (uni_iff rfl).2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [key j i hij.le, Pi.single_eq_of_ne fun h => by rw [h] at hij; omega]
    · rw [key i i le_rfl, Pi.single_eq_same]

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst P hP hs _ M`. Establish `hm` using `R.two_le_m`. Establish `e1 : (colLev Ch 0 ⟨P.1, hP⟩).H = uniUT (R.N 0) _ R.k []`. Unfold `colLev`. Rewrite using `[if_pos (by omega)]`.

Both sides reduce to the same expression. Establish `e2 : Jat (Pr` using `Pr) cst.sharp 0 P.1 = LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N 0) (cOf R 0) := by`. Unfold `Jat`. Rewrite using `[if_pos hP, if_pos hs]`. Unfold `prCat`.

Rewrite using `[e1, e2]`. Conclude with `uni_iff_prX (by simp [Ranks.N]) _ _ _ _ (by unfold Ranks.rS Ranks.r; omega) M`.
-/
theorem grpG_zero : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), cst.sharp = true → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → GrpG sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  intro X Pr R Ch sel S mu cst P hP hs _ M
  have hm := R.two_le_m
  have e1 : (colLev Ch 0 ⟨P.1, hP⟩).H = uniUT (R.N 0) _ R.k [] := by
    unfold colLev
    rw [if_pos (by omega)]
    rfl
  have e2 : Jat (Pr := Pr) cst.sharp 0 P.1 = LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N 0) (cOf R 0) := by
    unfold Jat
    rw [if_pos hP, if_pos hs]
  unfold prCat
  rw [e1, e2]
  exact uni_iff_prX (by simp [Ranks.N]) _ _ _ _ (by unfold Ranks.rS Ranks.r; omega) M

end GlobalTheory.Mem.ZeroGrp

end
