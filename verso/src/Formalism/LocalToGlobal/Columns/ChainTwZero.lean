import Formalism.LocalToGlobal.Columns.ChainTwMain

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwZr

variable {k : Type} [Field k] {n c : ℕ}

def twZrPr : (Fin (n + c) → k) →ₗ[k] (Fin n → k) := LinearMap.funLeft k k (Fin.castAdd c)

/- English proof (translation)
Use function extensionality and compare the values at `l`. Use `show Loc.inX k n c x (Fin.castAdd c l) = x l`. Unfold `Loc.inX`. Simplify using `[LinearMap.pi_apply, l.2]`.
-/
theorem twZrPr_inX (x : Fin n → k) : twZrPr (c := c) (Loc.inX k n c x) = x := by
  funext l
  show Loc.inX k n c x (Fin.castAdd c l) = x l
  unfold Loc.inX
  simp [LinearMap.pi_apply, l.2]

def twZrMap (g : (Fin n → k) →ₗ[k] (Fin n → k)) : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k) :=
  Loc.inX k n c ∘ₗ g ∘ₗ twZrPr + (LinearMap.id - Loc.inX k n c ∘ₗ twZrPr)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twZrMap_apply (g : (Fin n → k) →ₗ[k] (Fin n → k)) (v : Fin (n + c) → k) :
    twZrMap g v = Loc.inX k n c (g (twZrPr v)) + (v - Loc.inX k n c (twZrPr v)) := rfl

/- English proof (translation)
Rewrite using `[twZrMap_apply, map_add, map_sub, twZrPr_inX, twZrPr_inX, sub_self, add_zero]`.
-/
theorem twZrPr_map (g : (Fin n → k) →ₗ[k] (Fin n → k)) (v : Fin (n + c) → k) : twZrPr (twZrMap g v) = g (twZrPr v) := by
  rw [twZrMap_apply, map_add, map_sub, twZrPr_inX, twZrPr_inX, sub_self, add_zero]

/- English proof (translation)
Rewrite using `[twZrMap_apply, twZrPr_map, twZrMap_apply, twZrMap_apply]`. Use `show _ = Loc.inX k n c (g (g' (twZrPr v))) + _`. Normalize the expressions using the abelian group laws.
-/
theorem twZrMap_comp (g g' : (Fin n → k) →ₗ[k] (Fin n → k)) (v : Fin (n + c) → k) :
    twZrMap g (twZrMap g' v) = twZrMap (g ∘ₗ g') v := by
  rw [twZrMap_apply, twZrPr_map, twZrMap_apply, twZrMap_apply]
  show _ = Loc.inX k n c (g (g' (twZrPr v))) + _
  abel

/- English proof (translation)
Rewrite using `[twZrMap_apply]`. Simplify using the standard rewrite rules.
-/
theorem twZrMap_id (v : Fin (n + c) → k) : twZrMap LinearMap.id v = v := by
  rw [twZrMap_apply]
  simp

def twZrExt (g : (Fin n → k) ≃ₗ[k] (Fin n → k)) : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k) :=
  LinearEquiv.ofLinear (twZrMap g.toLinearMap) (twZrMap g.symm.toLinearMap)
    (LinearMap.ext fun v => by
      show twZrMap g.toLinearMap (twZrMap g.symm.toLinearMap v) = v
      rw [twZrMap_comp]
      have : g.toLinearMap ∘ₗ g.symm.toLinearMap = LinearMap.id := by ext; simp
      rw [this, twZrMap_id])
    (LinearMap.ext fun v => by
      show twZrMap g.symm.toLinearMap (twZrMap g.toLinearMap v) = v
      rw [twZrMap_comp]
      have : g.symm.toLinearMap ∘ₗ g.toLinearMap = LinearMap.id := by ext; simp
      rw [this, twZrMap_id])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twZrExt_apply (g : (Fin n → k) ≃ₗ[k] (Fin n → k)) (v : Fin (n + c) → k) :
    twZrExt (c := c) g v = twZrMap g.toLinearMap v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twZrExt_inv_apply (g : (Fin n → k) ≃ₗ[k] (Fin n → k)) (v : Fin (n + c) → k) :
    (twZrExt (c := c) g)⁻¹ v = twZrMap g.symm.toLinearMap v := rfl

/- English proof (translation)
Rewrite using `[twZrExt_apply, twZrMap_apply, twZrPr_inX, sub_self, add_zero]`. Both sides reduce to the same expression.
-/
theorem twZrExt_inX (g : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → k) :
    twZrExt (c := c) g (Loc.inX k n c x) = Loc.inX k n c (g x) := by
  rw [twZrExt_apply, twZrMap_apply, twZrPr_inX, sub_self, add_zero]
  rfl

/- English proof (translation)
Introduce `l hl`. Establish `hl' : ¬ l.1 < n` using `fun h => hl (by show l.1 < n + i; omega)`. Unfold `Loc.inX`. Simplify using `[LinearMap.pi_apply, hl']`.
-/
theorem twZr_inX_mem_Ufl (x : Fin n → k) (i : ℕ) : Loc.inX k n c x ∈ Loc.Ufl k n c i := by
  intro l hl
  have hl' : ¬ l.1 < n := fun h => hl (by show l.1 < n + i; omega)
  unfold Loc.inX
  simp [LinearMap.pi_apply, hl']

/- English proof (translation)
Use function extensionality and compare the values at `l`. Use `show Loc.eN k (n + c) i (Fin.castAdd c l) = 0`. Unfold `Loc.eN`. Establish `: ¬ (l : ℕ) = i` using `by have := l.2; omega`. Simplify using `[this]`.
-/
theorem twZrPr_eN (i : ℕ) (hi : n ≤ i) : twZrPr (c := c) (Loc.eN k (n + c) i) = 0 := by
  funext l
  show Loc.eN k (n + c) i (Fin.castAdd c l) = 0
  unfold Loc.eN
  have : ¬ (l : ℕ) = i := by have := l.2; omega
  simp [this]

/- English proof (translation)
Use `⟨fun i v hv => ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hr, twZrMap_apply]`. Conclude with `add_mem (twZr_inX_mem_Ufl _ i) (sub_mem hv (twZr_inX_mem_Ufl _ i))`. Rewrite using `[hr, twZrMap_apply, twZrPr_eN n le_rfl, map_zero, map_zero, sub_zero, zero_add]`. Rewrite using `[hr, twZrMap_apply, twZrPr_eN (n + i) (by omega), map_zero, map_zero, sub_zero, zero_add, sub_self]`.

Conclude with `zero_mem _`.
-/
theorem twZrMap_R1cond (g : (Fin n → k) →ₗ[k] (Fin n → k)) (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (hr : ∀ v, r v = twZrMap g v) : Loc.R1cond k n c r := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [hr, twZrMap_apply]
    exact add_mem (twZr_inX_mem_Ufl _ i) (sub_mem hv (twZr_inX_mem_Ufl _ i))
  · rw [hr, twZrMap_apply, twZrPr_eN n le_rfl, map_zero, map_zero, sub_zero, zero_add]
  · rw [hr, twZrMap_apply, twZrPr_eN (n + i) (by omega), map_zero, map_zero, sub_zero, zero_add, sub_self]
    exact zero_mem _

/- English proof (translation)
Assemble the required witnesses or components as `⟨twZrMap_R1cond _ _ (twZrExt_apply g), twZrMap_R1cond _ _ (twZrExt_inv_apply g)⟩`.
-/
theorem zeroExtension_mem_R1 (g : (Fin n → k) ≃ₗ[k] (Fin n → k)) : twZrExt (c := c) g ∈ Loc.R1 k n c :=
  ⟨twZrMap_R1cond _ _ (twZrExt_apply g), twZrMap_R1cond _ _ (twZrExt_inv_apply g)⟩

end TwZr

section TwZrLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n c : ℕ}

/- English proof (translation)
Rewrite using `[twZrMap_apply]`. Use `show Loc.inX E n c _ l + (v l - Loc.inX E n c _ l) = _`. Rewrite using `[ciInX_apply, ciInX_apply]`. Use `split_ifs with h`. Establish `: twZrPr (c` using `c) v ⟨l.1, h⟩ = v l := by show v (Fin.castAdd c ⟨l.1, h⟩) = v l`.

Both sides reduce to the same expression. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twZrMap_coord (g : (Fin n → E) →ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) (l : Fin (n + c)) :
    twZrMap g v l = if h : l.1 < n then g (twZrPr v) ⟨l.1, h⟩ else v l := by
  rw [twZrMap_apply]
  show Loc.inX E n c _ l + (v l - Loc.inX E n c _ l) = _
  rw [ciInX_apply, ciInX_apply]
  split_ifs with h
  · have : twZrPr (c := c) v ⟨l.1, h⟩ = v l := by
      show v (Fin.castAdd c ⟨l.1, h⟩) = v l
      rfl
    rw [this]
    ring
  · ring

/- English proof (translation)
Introduce `v`. Rewrite using `[hM, hM]`. Establish `hgv` using `hg (twZrPr v)`. Rewrite `hgv` using `[ciMem_stdAt, ciMem_stdAt]`. Prove the components needed by the constructor for the conclusion.

Introduce `h l`. Distinguish the cases in `hl : l.1 < n`. Use `(hgv.1 fun i => by` as an intermediate fact. Establish `h1` using `h (Fin.castAdd c i)`. Rewrite `h1` using `[twZrExt_apply, twZrMap_coord, dif_pos (by simp)]`.

Conclude with `h1) ⟨l.1, hl⟩`. Conclude with `this`. Establish `h1` using `h l`. Rewrite `h1` using `[twZrExt_apply, twZrMap_coord, dif_neg hl]`. Then use the resulting hypothesis. Introduce `h l`.

Rewrite using `[twZrExt_apply, twZrMap_coord]`. Use `split_ifs with hl`. Conclude with `hgv.2 (fun i => h (Fin.castAdd c i)) ⟨l.1, hl⟩`. Conclude with `h l`.
-/
theorem twZrExt_stab (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E (n + c)))
    (hM : ∀ v, v ∈ M ↔ ∀ l, IntAt P (v l)) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ GLint E n P) :
    twZrExt (c := c) g ∈ stabL E (n + c) M := by
  intro v
  rw [hM, hM]
  have hgv := hg (twZrPr v)
  rw [ciMem_stdAt, ciMem_stdAt] at hgv
  constructor
  · intro h l
    by_cases hl : l.1 < n
    · have := (hgv.1 fun i => by
        have h1 := h (Fin.castAdd c i)
        rw [twZrExt_apply, twZrMap_coord, dif_pos (by simp)] at h1
        exact h1) ⟨l.1, hl⟩
      exact this
    · have h1 := h l
      rwa [twZrExt_apply, twZrMap_coord, dif_neg hl] at h1
  · intro h l
    rw [twZrExt_apply, twZrMap_coord]
    split_ifs with hl
    · exact hgv.2 (fun i => h (Fin.castAdd c i)) ⟨l.1, hl⟩
    · exact h l

end TwZrLat

section TwZrQ

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

/- English proof (translation)
Unfold `Ranks.N`. Simplify using the standard rewrite rules.
-/
theorem rank_zero_eq_k : R.N 0 = R.k := by unfold Ranks.N; simp

/- English proof (translation)
Unfold `LocE.parL`. Rewrite using `[ciMem_sclLat]`. Establish `hN` using `rank_zero_eq_k (R := R)`. Use `forall_congr' fun l => ?_` and prove the remaining obligations. Rewrite using `[if_neg (by omega), zpow_zero, inv_one, one_mul]`.
-/
theorem twZr_parL (P : HeightOneSpectrum (𝓞 X.E)) (v : Sp X.E (R.N 0 + cOf R 0)) :
    v ∈ LocE.parL P (qOf P) (R.k + 0) (R.N 0) (cOf R 0) ↔ ∀ l, IntAt P (v l) := by
  unfold LocE.parL
  rw [ciMem_sclLat]
  have hN := rank_zero_eq_k (R := R)
  refine forall_congr' fun l => ?_
  rw [if_neg (by omega), zpow_zero, inv_one, one_mul]

/- English proof (translation)
Rewrite using `[twJat_Q sharp 0 hP]`. Conclude with `⟨twZrExt_stab P _ (fun v => ciMem_stdAt P v) hg, twZrExt_stab P _ (twZr_parL P) hg⟩`.
-/
theorem zeroExtension_mem_parahoric_zero {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (sharp : Bool) {g : Sp X.E (R.N 0) ≃ₗ[X.E] Sp X.E (R.N 0)}
    (hg : g ∈ GLint X.E (R.N 0) P) : twZrExt (c := cOf R 0) g ∈ Jat (Pr := Pr) (R := R) sharp 0 P := by
  rw [twJat_Q sharp 0 hP]
  exact ⟨twZrExt_stab P _ (fun v => ciMem_stdAt P v) hg, twZrExt_stab P _ (twZr_parL P) hg⟩

/- English proof (translation)
Introduce `g hg`. Use `⟨twZrExt (c := cOf R 0) g, ⟨zeroExtension_mem_R1 g, ?_⟩, twZrExt_inX g⟩` and prove the remaining obligations. Use `show (MulAut.conj (1 : AutY X R 0)⁻¹) (twZrExt (c := cOf R 0) g) ∈ Jat (Pr := Pr) (R := R) sharp 0 P`. Simplify `zeroExtension_mem_parahoric_zero hP sharp hg` using `[MulAut.conj_apply]`.
-/
theorem twZr_grp {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (sharp : Bool) :
    GLint X.E (R.N 0) P ≤ prCat (Pr := Pr) (R := R) sharp 0 P 1 := by
  intro g hg
  refine ⟨twZrExt (c := cOf R 0) g, ⟨zeroExtension_mem_R1 g, ?_⟩, twZrExt_inX g⟩
  show (MulAut.conj (1 : AutY X R 0)⁻¹) (twZrExt (c := cOf R 0) g) ∈ Jat (Pr := Pr) (R := R) sharp 0 P
  simpa [MulAut.conj_apply] using zeroExtension_mem_parahoric_zero hP sharp hg

/- English proof (translation)
Rewrite using `[ciMem_stdAt]`. Introduce `l`. Unfold `Loc.eN`. Use `split_ifs`. Conclude with `ciIntAt_one`.

Conclude with `ciIntAt_zero`.
-/
theorem twZr_eN_mem (P : HeightOneSpectrum (𝓞 X.E)) (N i : ℕ) : Loc.eN X.E N i ∈ stdAt X.E N P := by
  rw [ciMem_stdAt]
  intro l
  unfold Loc.eN
  split_ifs
  · exact ciIntAt_one
  · exact ciIntAt_zero

/- English proof (translation)
Establish `hrJ : r ∈ Jat (Pr` using `Pr) (R := R) cst.sharp 0 P.1 := by`. Use `hr.2` as an intermediate fact. Simplify `this` using `[MulAut.conj_apply]`. Rewrite `hrJ` using `[twJat_Q _ 0 hP]`. Establish `hstd` using `hrJ.1`.

Establish `hint : IntAt P.1 (Loc.n1Arg r)`. Unfold `Loc.n1Arg`. Use `ciIntAt_sum _ _ fun i _ => ?_` and prove the remaining obligations. Establish `hv : r (Loc.eN X.E (R.N 0 + cOf R 0) (R.N 0 + i + 1)) ∈ stdAt X.E (R.N 0 + cOf R 0) P.1` using `(hstd _).2 (twZr_eN_mem P.1 _ _)`. Rewrite `hv` using `[ciMem_stdAt]`.

Unfold `Loc.atN`. Use `split_ifs`. Conclude with `hv _`. Conclude with `ciIntAt_zero`. Unfold `chiInv`.

Rewrite using `[hc.psi_int P _ hint, inv_one, one_mul]`. Unfold `lamRow`. Rewrite using `[if_neg hP]`. Unfold `LocE.lamQB`. Establish `hN` using `rank_zero_eq_k (R := R)`.

Establish `: IsEmpty (Fin (R.N 0 - (R.k + 0)))` using `⟨fun i => by have := i.2; omega⟩`. Rewrite using `[Matrix.det_isEmpty]`. Unfold `LocE.unitV`. Establish `hu : IsUnit (redP P.1 (1 : X.E))` using `by rw [redP_one]; exact isUnit_one`. Rewrite using `[dif_pos hu]`.

Establish `: hu.unit = 1` using `Units.ext (by rw [IsUnit.unit_spec, redP_one]; rfl)`. Rewrite using `[this, map_one, Units.val_one, inv_one]`.
-/
theorem twZr_chr (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (r : AutY X R 0)
    (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp 0 P.1) 1) : chiInv Ch sel mu cst 0 P 1 r = 1 := by
  have hrJ : r ∈ Jat (Pr := Pr) (R := R) cst.sharp 0 P.1 := by
    have := hr.2
    simpa [MulAut.conj_apply] using this
  rw [twJat_Q _ 0 hP] at hrJ
  have hstd := hrJ.1
  have hint : IntAt P.1 (Loc.n1Arg r) := by
    unfold Loc.n1Arg
    refine ciIntAt_sum _ _ fun i _ => ?_
    have hv : r (Loc.eN X.E (R.N 0 + cOf R 0) (R.N 0 + i + 1)) ∈ stdAt X.E (R.N 0 + cOf R 0) P.1 :=
      (hstd _).2 (twZr_eN_mem P.1 _ _)
    rw [ciMem_stdAt] at hv
    unfold Loc.atN
    split_ifs
    · exact hv _
    · exact ciIntAt_zero
  unfold chiInv
  rw [hc.psi_int P _ hint, inv_one, one_mul]
  unfold lamRow
  rw [if_neg hP]
  unfold LocE.lamQB
  have hN := rank_zero_eq_k (R := R)
  have : IsEmpty (Fin (R.N 0 - (R.k + 0))) := ⟨fun i => by have := i.2; omega⟩
  rw [Matrix.det_isEmpty]
  unfold LocE.unitV
  have hu : IsUnit (redP P.1 (1 : X.E)) := by rw [redP_one]; exact isUnit_one
  rw [dif_pos hu]
  have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, redP_one]; rfl)
  rw [this, map_one, Units.val_one, inv_one]

/- English proof (translation)
Introduce `P hP` and use `⟨twZr_grp hP cst.sharp, fun r hr => twZr_chr hc P hP r hr⟩`.
-/
theorem twZeroQ_of (hc : cst.Ok) : TwZeroQ Ch sel mu cst := fun P hP =>
  ⟨twZr_grp hP cst.sharp, fun r hr => twZr_chr hc P hP r hr⟩

end TwZrQ

end Formalism.L2.Col
