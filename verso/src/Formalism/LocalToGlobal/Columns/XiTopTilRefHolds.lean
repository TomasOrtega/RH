import Formalism.LocalToGlobal.Columns.XtIntAtQpow

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Mid

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
The claim follows from `yIntAt_inv (IntAt.coe w pi) (by rw [reduction_coe]; exact mk_ne_zero h)`.
-/
theorem xtIntAt_piInv {w : HeightOneSpectrum (𝓞 E)} {pi : 𝓞 E} (h : pi ∉ w.asIdeal) : IntAt w ((algebraMap (𝓞 E) E pi)⁻¹) :=
  yIntAt_inv (IntAt.coe w pi) (by rw [reduction_coe]; exact mk_ne_zero h)

/- English proof (translation)
Use `set v0 : Sp E n := fun i : Fin n => v ⟨i.1, by omega⟩ with hv0def`. Establish `hpi0 : algebraMap (𝓞 E) E pi ≠ 0`. Introduce `h`. Establish `: pi = 0` using `(FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h, map_zero])`. Conclude with `hG w (this ▸ zero_mem _)`.

Establish `hv1 : (∀ i, IntAt w.1 (F'.symm v i)) ↔ v ∈ (DecoSet.tilH (ST` using `ST) hN pi d).1.at w.1 := by`. Rewrite using `[← ciMem_stdAt, ← hF'.1 (F'.symm v), LinearEquiv.apply_symm_apply]`. Establish `hv2 : (∀ i, IntAt w.1 (f0.symm v0 i)) ↔ v0 ∈ d.1.at w.1`. Rewrite using `[← ciMem_stdAt, ← hf0.1 (f0.symm v0), LinearEquiv.apply_symm_apply]`. Establish `hv3 : IntAt w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩) ↔ IntAt w.1 (v ⟨n, by omega⟩)`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(IntAt.coe w.1 pi).mul h` as an intermediate fact. Rewrite `this` using `[← mul_assoc, mul_inv_cancel₀ hpi0, one_mul]`. Then use the resulting hypothesis. Introduce `h`.

Conclude with `(xtIntAt_piInv (hG w)).mul h`. Use `⟨by rw [hv1, xtTilH_mem hN d hT hG w.1 v, hv2, hv3], fun hall => ?_⟩` and prove the remaining obligations. Establish `hvD` using `hv1.1 hall`. Establish `hbe : (DecoSet.tilH (ST` using `ST) hN pi d).1.be w v = redV w.1 (F'.symm v) := by`. Use `hF'.2 (F'.symm v) ((ciMem_stdAt _ _).2 hall)` as an intermediate fact.

Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hv0 : v0 ∈ d.1.at w.1` using `((xtTilH_mem hN d hT hG w.1 v).1 hvD).1`. Establish `hbe0 : d.1.be w v0 = redV w.1 (f0.symm v0)`. Use `hf0.2 (f0.symm v0) ((ciMem_stdAt _ _).2 (hv2.2 hv0))` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.

Prove the components needed by the constructor for the conclusion. Introduce `i`. Establish `h1` using `xtTilH_be hN d hT hG w v hvD ⟨i.1, by omega⟩`. Rewrite `h1` using `[dif_pos i.2, hbe]`. Establish `h2` using `congrFun hbe0 i`.

Conclude with `h1.trans h2`. Establish `h1` using `xtTilH_be hN d hT hG w v hvD ⟨n, by omega⟩`. Rewrite `h1` using `[dif_neg (lt_irrefl n), hbe]`. Rewrite using `[inv_mul_eq_div]`. Conclude with `h1`.
-/
theorem xtMid (hN : N = n + 1) (d : DecoSet E n ∅ SG) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (w : SG) (F' : Sp E N ≃ₗ[E] Sp E N) (hF' : (DecoSet.tilH (ST := ST) hN pi d).1.IsLift w F')
    (f0 : Sp E n ≃ₗ[E] Sp E n) (hf0 : d.1.IsLift w f0) (v : Sp E N) :
    ((∀ i, IntAt w.1 (F'.symm v i)) ↔
      (∀ i, IntAt w.1 (f0.symm (fun i : Fin n => v ⟨i.1, by omega⟩) i)) ∧ IntAt w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩)) ∧
    ((∀ i, IntAt w.1 (F'.symm v i)) →
      (∀ i : Fin n, redP w.1 (F'.symm v ⟨i.1, by omega⟩) = redP w.1 (f0.symm (fun i : Fin n => v ⟨i.1, by omega⟩) i)) ∧
        redP w.1 (F'.symm v ⟨n, by omega⟩) = redP w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩)) := by
  set v0 : Sp E n := fun i : Fin n => v ⟨i.1, by omega⟩ with hv0def
  have hpi0 : algebraMap (𝓞 E) E pi ≠ 0 := by
    intro h
    have : pi = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h, map_zero])
    exact hG w (this ▸ zero_mem _)
  have hv1 : (∀ i, IntAt w.1 (F'.symm v i)) ↔ v ∈ (DecoSet.tilH (ST := ST) hN pi d).1.at w.1 := by
    rw [← ciMem_stdAt, ← hF'.1 (F'.symm v), LinearEquiv.apply_symm_apply]
  have hv2 : (∀ i, IntAt w.1 (f0.symm v0 i)) ↔ v0 ∈ d.1.at w.1 := by
    rw [← ciMem_stdAt, ← hf0.1 (f0.symm v0), LinearEquiv.apply_symm_apply]
  have hv3 : IntAt w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩) ↔ IntAt w.1 (v ⟨n, by omega⟩) := by
    constructor
    · intro h
      have := (IntAt.coe w.1 pi).mul h
      rwa [← mul_assoc, mul_inv_cancel₀ hpi0, one_mul] at this
    · intro h
      exact (xtIntAt_piInv (hG w)).mul h
  refine ⟨by rw [hv1, xtTilH_mem hN d hT hG w.1 v, hv2, hv3], fun hall => ?_⟩
  have hvD := hv1.1 hall
  have hbe : (DecoSet.tilH (ST := ST) hN pi d).1.be w v = redV w.1 (F'.symm v) := by
    have := hF'.2 (F'.symm v) ((ciMem_stdAt _ _).2 hall)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hv0 : v0 ∈ d.1.at w.1 := ((xtTilH_mem hN d hT hG w.1 v).1 hvD).1
  have hbe0 : d.1.be w v0 = redV w.1 (f0.symm v0) := by
    have := hf0.2 (f0.symm v0) ((ciMem_stdAt _ _).2 (hv2.2 hv0))
    rwa [LinearEquiv.apply_symm_apply] at this
  constructor
  · intro i
    have h1 := xtTilH_be hN d hT hG w v hvD ⟨i.1, by omega⟩
    rw [dif_pos i.2, hbe] at h1
    have h2 := congrFun hbe0 i
    exact h1.trans h2
  · have h1 := xtTilH_be hN d hT hG w v hvD ⟨n, by omega⟩
    rw [dif_neg (lt_irrefl n), hbe] at h1
    rw [inv_mul_eq_div]
    exact h1

end Mid

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks}

/- English proof (translation)
Unfold `Ranks.r Ranks.N`. Establish `h1 : R.m - 1 = m2 + 1` using `by omega`. Establish `h2 : R.k + R.m - 1 = R.k + (m2 + 1)` using `by omega`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xt_a_eq {m2 : ℕ} (hm : R.m = m2 + 2) : R.r + (R.m - 1) * R.t = R.N (m2 + 1) := by
  unfold Ranks.r Ranks.N
  have h1 : R.m - 1 = m2 + 1 := by omega
  have h2 : R.k + R.m - 1 = R.k + (m2 + 1) := by omega
  rw [h1, h2]
  ring

/- English proof (translation)
Rewrite using `[xt_a_eq hm]`. Unfold `Ranks.N`. Rewrite using `[hm]`. Establish `e : (m2 + 2) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1)` using `by ring`. Use linear arithmetic over natural numbers and integers.
-/
theorem xt_a_le {m2 : ℕ} (hm : R.m = m2 + 2) : R.r + (R.m - 1) * R.t ≤ (R.N R.m - 1) + 0 := by
  rw [xt_a_eq hm]
  unfold Ranks.N
  rw [hm]
  have e : (m2 + 2) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1) := by ring
  omega

/- English proof (translation)
Unfold `cOf`. Use linear arithmetic over natural numbers and integers.
-/
theorem xt_cOf {m2 : ℕ} (hm : R.m = m2 + 2) : cOf R (m2 + 1) = 0 := by
  unfold cOf
  omega

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

/- English proof (translation)
Establish `hu` using `ciQ_notMem_sq hX hPr hP`. Establish `hq` using `ciQ_mem P`. Establish `hq0 : ((qOf P : ℕ) : X.E) ≠ 0` using `ciQ_ne_zero hu`. Establish `ha` using `xt_a_eq (R := R) hm`. Establish `hle` using `xt_a_le (R := R) hm`.

Establish `hkr : R.k ≤ R.r` using `by unfold Ranks.r; have := R.two_le_m; omega`. Unfold `PhiTop`. Rewrite using `[if_pos hP]`. Consider the cases of `sharp`. Simplify using `only [Bool.false_eq_true, if_false]`.

Use `ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hle fun p p' hp hp' => hD p p' hp (ha ▸ hp')` and prove the remaining obligations. Unfold `Ranks.r`. Use `R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Unfold `Ranks.r`.

Use `R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [if_true]`. Conclude with `xtPhiGS_congr hq hq0 _ _ x x' hkr hle fun p p' hp hp' => hD p p' hp (ha ▸ hp')`.
-/
theorem xtPhiTop_congr (hX : X.Ok) (hPr : Pr.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x x' : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0))
    (hD : ∀ p p', p < (R.N R.m - 1) + 0 → p' < R.N (m2 + 1) → ∃ d, IntAt P d ∧
      LocE.entB (qOf P) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB (qOf P) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1) x p p' + (qOf P : X.E) * d) :
    PhiTop Ch mu sharp m2 P x' = PhiTop Ch mu sharp m2 P x := by
  have hu := ciQ_notMem_sq hX hPr hP
  have hq := ciQ_mem P
  have hq0 : ((qOf P : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have ha := xt_a_eq (R := R) hm
  have hle := xt_a_le (R := R) hm
  have hkr : R.k ≤ R.r := by unfold Ranks.r; have := R.two_le_m; omega
  unfold PhiTop
  rw [if_pos hP]
  cases sharp
  · simp only [Bool.false_eq_true, if_false]
    refine ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hle fun p p' hp hp' => hD p p' hp (ha ▸ hp')
    · unfold Ranks.r; have := R.two_le_m; omega
    · unfold Ranks.r; have := R.two_le_m; omega
  · simp only [if_true]
    exact xtPhiGS_congr hq hq0 _ _ x x' hkr hle fun p p' hp hp' => hD p p' hp (ha ▸ hp')

/- English proof (translation)
Establish `ha` using `xt_a_eq (R := R) hm`. Unfold `PhiTop at h`. Rewrite `h` using `[if_pos hP]`. Introduce `p p' hp hp'`. Consider the cases of `sharp`.

Simplify using `only [Bool.false_eq_true, if_false] at h`. Conclude with `ciPhiG_int _ _ false x h p p' hp (ha.symm ▸ hp')`. Simplify using `only [if_true] at h`. Conclude with `xtPhiGS_int _ _ x h p p' hp (ha.symm ▸ hp')`.
-/
theorem xtPhiTop_int {m2 : ℕ} (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) (h : PhiTop Ch mu sharp m2 P x ≠ 0) :
    ∀ p p', p < (R.N R.m - 1) + 0 → p' < R.N (m2 + 1) →
      IntAt P (LocE.entB (qOf P) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1) x p p') := by
  have ha := xt_a_eq (R := R) hm
  unfold PhiTop at h
  rw [if_pos hP] at h
  intro p p' hp hp'
  cases sharp
  · simp only [Bool.false_eq_true, if_false] at h
    exact ciPhiG_int _ _ false x h p p' hp (ha.symm ▸ hp')
  · simp only [if_true] at h
    exact xtPhiGS_int _ _ x h p p' hp (ha.symm ▸ hp')

open Classical in

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hY`. Establish `hrep : repY {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))} ∈ {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}` using `Classical.epsilon_spec (p := fun z => z ∈ {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}) ⟨y, by show y - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))`. Rewrite using `[sub_self]`. Conclude with `zero_mem _⟩`. Use `set ρ := repY {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}`.

Establish `h1` using `(mem_locLat _ _ _ _).1 hy P`. Establish `h2` using `(mem_locLat _ _ _ _).1 hrep P`. Simplify using `only [if_pos hP, _root_.zpow_neg, zpow_one, inv_inv, zpow_zero, inv_one, one_smul] at h1 h2`. Establish `h3 : (qOf P.1 : X.E) • ρ ∈ d.1.at P.1`. Establish `e : (qOf P.1 : X.E) • ρ = (qOf P.1 : X.E) • (ρ - y) + (qOf P.1 : X.E) • y` using `by rw [← smul_add, sub_add_cancel]`.

Rewrite using `[e]`. Conclude with `add_mem (yInt_smul_mem ciIntAt_q h2) h1`. Establish `hl` using `Deco.liftFr_spec (d.2.hasLift ⟨P.1, hP⟩)`. Establish `h4` using `(hl.1 ((d.1.liftFr ⟨P.1, hP⟩).symm ((qOf P.1 : X.E) • ρ))).1 (by rw [LinearEquiv.apply_symm_apply]; exact h3)`. Establish `h5` using `(ciMem_stdAt _ _).1 h4 j`.

Rewrite `h5` using `[map_smul, Pi.smul_apply, smul_eq_mul]`. Then use the resulting hypothesis.
-/
theorem xtRepY_int {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST Pr.vGs) (Y : Set (Sp X.E n))
    (hY : Y ∈ ybSet sel mu cst d.1.N) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (j : Fin n) :
    IntAt P.1 ((qOf P.1 : X.E) * (d.1.liftFr ⟨P.1, hP⟩).symm (repY Y) j) := by
  obtain ⟨y, hy, rfl⟩ := hY
  have hrep : repY {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))} ∈
      {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))} :=
    Classical.epsilon_spec (p := fun z => z ∈ {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))})
      ⟨y, by
        show y - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))
        rw [sub_self]
        exact zero_mem _⟩
  set ρ := repY {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 hrep P
  simp only [if_pos hP, _root_.zpow_neg, zpow_one, inv_inv, zpow_zero, inv_one, one_smul] at h1 h2
  have h3 : (qOf P.1 : X.E) • ρ ∈ d.1.at P.1 := by
    have e : (qOf P.1 : X.E) • ρ = (qOf P.1 : X.E) • (ρ - y) + (qOf P.1 : X.E) • y := by rw [← smul_add, sub_add_cancel]
    rw [e]
    exact add_mem (yInt_smul_mem ciIntAt_q h2) h1
  have hl := Deco.liftFr_spec (d.2.hasLift ⟨P.1, hP⟩)
  have h4 := (hl.1 ((d.1.liftFr ⟨P.1, hP⟩).symm ((qOf P.1 : X.E) • ρ))).1 (by rw [LinearEquiv.apply_symm_apply]; exact h3)
  have h5 := (ciMem_stdAt _ _).1 h4 j
  rwa [map_smul, Pi.smul_apply, smul_eq_mul] at h5

end Fin

end Formalism.L2.Col
