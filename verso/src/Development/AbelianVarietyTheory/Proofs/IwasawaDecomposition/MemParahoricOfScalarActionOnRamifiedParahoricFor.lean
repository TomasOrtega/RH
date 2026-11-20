import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ParaRigid

/- English proof (translation)
Establish `e : M = (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O)).map O.subtype` using `by ext i j; rfl`. Establish `h` using `RingHom.map_det O.subtype (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O))`. Rewrite `h` using `[RingHom.mapMatrix_apply]`. Rewrite using `[e, ← h]`. Conclude with `SetLike.coe_mem _`.
-/
theorem det_mem_of {K : Type} [Field K] (O : Subring K) {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (hM : ∀ i j, M i j ∈ O) : M.det ∈ O := by
  have e : M = (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O)).map O.subtype := by ext i j; rfl
  have h := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨M i j, hM i j⟩ : O))
  rw [RingHom.mapMatrix_apply] at h
  rw [e, ← h]
  exact SetLike.coe_mem _

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]`. Use `O.mul_mem ?_ (det_mem_of O _ ?_)` and prove the remaining obligations. Rewrite using `[Ring.inverse_eq_inv']`. Conclude with `hd`.

Introduce `k l`. Rewrite using `[Matrix.updateRow_apply]`. Use `split_ifs`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`.

Conclude with `O.one_mem`. Conclude with `O.zero_mem`. Conclude with `h1 k l`.
-/
theorem inv_entry_mem {K : Type} [Field K] (O : Subring K) {m : ℕ} (x : GL (Fin m) K)
    (h1 : ∀ i j, x.1 i j ∈ O) (hd : (x.1.det)⁻¹ ∈ O) : ∀ i j, (x⁻¹).1 i j ∈ O := by
  intro i j
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine O.mul_mem ?_ (det_mem_of O _ ?_)
  · rw [Ring.inverse_eq_inv']; exact hd
  · intro k l
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    · exact h1 k l

/- English proof (translation)
The claim follows from `GlobalTheory.HeckeScalarSph.mem_GLint_iff.2 ⟨h1, inv_entry_mem O x h1 hd⟩`.
-/
theorem mem_GLint_of {K : Type} [Field K] (O : Subring K) {m : ℕ} (x : GL (Fin m) K)
    (h1 : ∀ i j, x.1 i j ∈ O) (hd : (x.1.det)⁻¹ ∈ O) : x ∈ Formalism.UG.GLint (Fin m) O :=
  GlobalTheory.HeckeScalarSph.mem_GLint_iff.2 ⟨h1, inv_entry_mem O x h1 hd⟩

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

variable {K : Type} [Field K] {m : ℕ}

def colVecAt (j : Fin m) (t : K) : Matrix (Fin m) Unit K := Matrix.of fun i _ => if i = j then t else 0

def rowVecAt (K : Type) [Field K] (i : Fin m) : Matrix Unit (Fin m) K := Matrix.of fun _ j => if j = i then 1 else 0

def Gmat (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) : Matrix (Fin m) (Fin m) K :=
  1 + (h * colVecAt j0 t) * rowVecAt K i0

def Pmat (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) : Matrix (Fin m) (Fin m) K :=
  1 + colVecAt j0 t * (rowVecAt K i0 * h)

/- English proof (translation)
Rewrite using `[Gmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]`. Simplify using `[colVecAt, rowVecAt, Matrix.mul_apply]`. Use `done`.
-/
theorem det_G (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) :
    (Gmat h i0 j0 t).det = 1 + h i0 j0 * t := by
  rw [Gmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [colVecAt, rowVecAt, Matrix.mul_apply]
  done

/- English proof (translation)
Rewrite using `[Pmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]`. Simplify using `[colVecAt, rowVecAt, Matrix.mul_apply]`. Use `done`.
-/
theorem det_P (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) :
    (Pmat h i0 j0 t).det = 1 + h i0 j0 * t := by
  rw [Pmat, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [colVecAt, rowVecAt, Matrix.mul_apply]
  done

/- English proof (translation)
Simplify using `[Gmat, colVecAt, rowVecAt, Matrix.mul_apply]`. Use `done`.
-/
theorem G_apply (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (i j : Fin m) :
    Gmat h i0 j0 t i j = (1 : Matrix (Fin m) (Fin m) K) i j + if j = i0 then h i j0 * t else 0 := by
  simp [Gmat, colVecAt, rowVecAt, Matrix.mul_apply]
  done

/- English proof (translation)
Simplify using `[Pmat, colVecAt, rowVecAt, Matrix.mul_apply]`. Use `done`.
-/
theorem P_apply (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (i j : Fin m) :
    Pmat h i0 j0 t i j = (1 : Matrix (Fin m) (Fin m) K) i j + if i = j0 then t * h i0 j else 0 := by
  simp [Pmat, colVecAt, rowVecAt, Matrix.mul_apply]
  done

/- English proof (translation)
Simplify using `only [Gmat, Pmat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hh, Matrix.one_mul]`.
-/
theorem conj_G (h h' : Matrix (Fin m) (Fin m) K) (hh : h' * h = 1) (i0 j0 : Fin m) (t : K) :
    h' * Gmat h i0 j0 t * h = Pmat h i0 j0 t := by
  simp only [Gmat, Pmat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hh, Matrix.one_mul]

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

variable {K : Type} [Field K] {m : ℕ}

/- English proof (translation)
Establish `e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Gmat h i0 j0 t a.1 b.1) = 1 + ((Matrix.of fun a (_ : Unit) => h a.1 j0 * t : Matrix {x : Fin m // r ≤ x.val} Unit K) * (Matrix.of fun (_ : Unit) b => if b = ⟨i0, hi0⟩ then 1 else 0 : Matrix Unit {x : Fin m // r ≤ x.val} K))`. Use extensionality with `a b`. Simplify using `[G_apply, Matrix.one_apply, Matrix.mul_apply, Subtype.ext_iff]`. Rewrite using `[e, Matrix.det_one_add_mul_comm, Matrix.det_unique]`. Simplify using `[Matrix.mul_apply]`.
-/
theorem detDD_G (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (r : ℕ) (hi0 : r ≤ i0.val) :
    (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Gmat h i0 j0 t a.1 b.1).det = 1 + h i0 j0 * t := by
  have e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Gmat h i0 j0 t a.1 b.1) =
      1 + ((Matrix.of fun a (_ : Unit) => h a.1 j0 * t : Matrix {x : Fin m // r ≤ x.val} Unit K) *
        (Matrix.of fun (_ : Unit) b => if b = ⟨i0, hi0⟩ then 1 else 0 : Matrix Unit {x : Fin m // r ≤ x.val} K)) := by
    ext a b
    simp [G_apply, Matrix.one_apply, Matrix.mul_apply, Subtype.ext_iff]
  rw [e, Matrix.det_one_add_mul_comm, Matrix.det_unique]
  simp [Matrix.mul_apply]

/- English proof (translation)
Establish `e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Pmat h i0 j0 t a.1 b.1) = 1`. Use extensionality with `a b`. Establish `ha : (a.1 : Fin m) ≠ j0` using `fun e => by have := a.2; rw [e] at this; omega`. Simplify using `[P_apply, Matrix.one_apply, Subtype.ext_iff, ha]`. Rewrite using `[e, Matrix.det_one]`.
-/
theorem detDD_P (h : Matrix (Fin m) (Fin m) K) (i0 j0 : Fin m) (t : K) (r : ℕ) (hj0 : j0.val < r) :
    (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Pmat h i0 j0 t a.1 b.1).det = 1 := by
  have e : (Matrix.of fun a b : {x : Fin m // r ≤ x.val} => Pmat h i0 j0 t a.1 b.1) = 1 := by
    ext a b
    have ha : (a.1 : Fin m) ≠ j0 := fun e => by have := a.2; rw [e] at this; omega
    simp [P_apply, Matrix.one_apply, Subtype.ext_iff, ha]
  rw [e, Matrix.det_one]

end GlobalTheory.ParaRigid

namespace GlobalTheory.ParaRigid

/- English proof (translation)
Introduce `L _ _ _ n r s V _ _ F J χ a hF ha hJ hEig h1 ha' κ hκU hκT hc`. Take `⟨c, hc⟩` from `hc`. Use `set O := (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring with hO`. Establish `hOv : ∀ x, x ∈ O ↔ Valued.v x ≤ 1` using `fun x => by`. Rewrite using `[hO, ValuationSubring.mem_toSubring, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`.

Establish `hint` using `(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκT).2 hκU`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨i0, j0, hi0, hj0, hv⟩` from `hcon`.

Use `set h := s.loc n κ with hh`. Establish `hent : ∀ i j, Valued.v (h.val i j) ≤ 1` using `fun i j => (hOv _).1 ((GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hint).1 i j)`. Establish `hv1 : Valued.v (h.val i0 j0) = 1` using `le_antisymm (hent i0 j0) hv`. Establish `hne : h.val i0 j0 ≠ 0`. Introduce `e`.

Rewrite `hv1` using `[e, map_zero]`. Conclude with `zero_ne_one hv1`. Establish `ha0 : a ≠ 0`. Introduce `e`. Rewrite `ha` using `[e, map_zero]`.

Conclude with `zero_ne_one ha`. Use `set t := (a - 1) / h.val i0 j0 with ht`. Establish `htv : Valued.v t ≤ 1`. Rewrite using `[ht, map_div₀, hv1, div_one]`. Use `(Valuation.map_sub _ _ _).trans (max_le ha.le (by rw [map_one]))` and prove the remaining obligations.

Establish `hth : 1 + h.val i0 j0 * t = a` using `by rw [ht]; field_simp; ring`. Establish `hdinv : a⁻¹ ∈ O` using `by rw [hOv, map_inv₀, ha, inv_one]`. Establish `hone : ∀ i j, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) ≤ 1`. Introduce `i j`. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Rewrite using `[map_one]`. Rewrite using `[map_zero]`. Conclude with `zero_le'`. Establish `hGint : ∀ i j, Gmat h.val i0 j0 t i j ∈ O`.

Introduce `i j`. Rewrite using `[hOv, G_apply]`. Use `(Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[map_mul]`.

Conclude with `mul_le_one' (hent _ _) htv`. Rewrite using `[map_zero]`. Conclude with `zero_le'`. Establish `hPint : ∀ i j, Pmat h.val i0 j0 t i j ∈ O`. Introduce `i j`.

Rewrite using `[hOv, P_apply]`. Use `(Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[map_mul]`. Conclude with `mul_le_one' htv (hent _ _)`.

Rewrite using `[map_zero]`. Conclude with `zero_le'`. Establish `hdG : (Gmat h.val i0 j0 t).det = a` using `by rw [det_G, hth]`. Establish `hdP : (Pmat h.val i0 j0 t).det = a` using `by rw [det_P, hth]`. Set `Gg` to `Matrix.GeneralLinearGroup.mkOfDetNeZero (Gmat h.val i0 j0 t) (by rw [hdG]; exact ha0)`.

Establish `hGg : Gg.val = Gmat h.val i0 j0 t` using `rfl`. Take `⟨g, ⟨hgT, hgl⟩, -⟩` from `(GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s).2.2 Gg`. Use `set p := κ⁻¹ * g * κ with hp`. Establish `hpT : TrivOutside {s.v} p` using `GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv hκT) hgT) hκT`. Establish `hinv : (h⁻¹).val * h.val = 1` using `by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Establish `hpl : (s.loc n p).val = Pmat h.val i0 j0 t`. Rewrite using `[hp, map_mul, map_mul, map_inv, hgl, ← hh, Units.val_mul, Units.val_mul, hGg]`. Conclude with `conj_G h.val (h⁻¹).val hinv i0 j0 t`. Establish `hgl' : (s.loc n g).val = Gmat h.val i0 j0 t` using `by rw [hgl]; exact hGg`. Establish `hgP : NG.ParaRT s r (s.loc n g)`.

Use `⟨mem_GLint_of O _ (fun i j => by rw [hgl']; exact hGint i j) (by rw [hgl', hdG]; exact hdinv), ?_⟩` and prove the remaining obligations. Introduce `i j hi hj`. Establish `hji : j ≠ i0` using `fun e => by rw [e] at hj; omega`. Establish `hij : i ≠ j` using `fun e => by rw [e] at hi; omega`. Rewrite using `[hgl', G_apply, if_neg hji, Matrix.one_apply_ne hij, add_zero, map_zero]`.

Conclude with `zero_lt_one`. Establish `hpP : NG.ParaRT s r (s.loc n p)`. Use `⟨mem_GLint_of O _ (fun i j => by rw [hpl]; exact hPint i j) (by rw [hpl, hdP]; exact hdinv), ?_⟩` and prove the remaining obligations. Introduce `i j hi hj`. Establish `hij0 : i ≠ j0` using `fun e => by rw [e] at hi; omega`.

Establish `hij : i ≠ j` using `fun e => by rw [e] at hi; omega`. Rewrite using `[hpl, P_apply, if_neg hij0, Matrix.one_apply_ne hij, add_zero, map_zero]`. Conclude with `zero_lt_one`. Establish `hgJ : g ∈ J` using `(hJ g hgT).2 hgP`. Establish `hpJ : p ∈ J` using `(hJ p hpT).2 hpP`.

Establish `hχg : χ ⟨g, hgJ⟩ ≠ 1` using `ha' g hgJ hgT (by unfold NG.detDD; simp only [hgl']; rw [detDD_G _ _ _ _ r hi0, hth])`. Establish `hχp : χ ⟨p, hpJ⟩ = 1` using `h1 p hpJ hpT (by unfold NG.detDD; simp only [hpl]; rw [detDD_P _ _ _ _ r hj0])`. Establish `eg` using `hEig ⟨g, hgJ⟩`. Establish `ep` using `hEig ⟨p, hpJ⟩`. Rewrite `ep` using `[hχp]`.

Establish `hkp : κ * p = g * κ` using `by rw [hp]; group`. Choose the witnesses or unpack the hypotheses as in `⟨x0, hx0⟩ : ∃ x, F x ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Conclude with `hF (funext hn)`.

Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Apply `hx0` to reduce the goal to its premises. Use `hc (x0 * κ⁻¹)` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right, zero_smul]`. Then use the resulting hypothesis.

Establish `key : ∀ x, c • ((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) • F x = c • F x`. Introduce `x`. Establish `e1` using `hc (x * g)`. Establish `e2` using `ep (x * κ)`. Rewrite `e1` using `[eg x]`.

Rewrite `e2` using `[mul_assoc, hkp, ← mul_assoc, e1, hc x]`. Simplify using `using e2`. Apply `hχg` to reduce the goal to its premises. Establish `k0` using `key x0`. Rewrite `k0` using `[smul_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero]`.

Break down `k0 with k0 | k0` into its components or cases. Apply `Units.ext` to reduce the goal to its premises. Establish `: c * (((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) - 1) = 0` using `by rw [mul_sub, mul_one]; exact k0`. Break down `mul_eq_zero.1 this with h' | h'` into its components or cases. Conclude with `absurd h' hc0`.

Simplify `h'` using `[sub_eq_zero]`. Conclude with `absurd k0 hx0`.
-/
theorem mem_para_of_eig : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (V : Type) [AddCommGroup V] [Module ℂ V] (F : GAf L n → V) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (a : s.v.adicCompletion (maximalRealSubfield L)), F ≠ 0 → Valued.v a = 1 → (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ NG.ParaRT s r (s.loc n κ))) → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = 1 → χ ⟨κ, h⟩ = 1) → (∀ κ (h : κ ∈ J), TrivOutside {s.v} κ → NG.detDD s r (s.loc n κ) = a → χ ⟨κ, h⟩ ≠ 1) → ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  intro L _ _ _ n r s V _ _ F J χ a hF ha hJ hEig h1 ha' κ hκU hκT hc
  obtain ⟨c, hc⟩ := hc
  classical
  set O := (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring with hO
  have hOv : ∀ x, x ∈ O ↔ Valued.v x ≤ 1 := fun x => by
    rw [hO, ValuationSubring.mem_toSubring, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hint := (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκT).2 hκU
  refine ⟨hint, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, j0, hi0, hj0, hv⟩ := hcon
  set h := s.loc n κ with hh
  have hent : ∀ i j, Valued.v (h.val i j) ≤ 1 := fun i j =>
    (hOv _).1 ((GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hint).1 i j)
  have hv1 : Valued.v (h.val i0 j0) = 1 := le_antisymm (hent i0 j0) hv
  have hne : h.val i0 j0 ≠ 0 := by
    intro e; rw [e, map_zero] at hv1; exact zero_ne_one hv1
  have ha0 : a ≠ 0 := by
    intro e; rw [e, map_zero] at ha; exact zero_ne_one ha
  set t := (a - 1) / h.val i0 j0 with ht
  have htv : Valued.v t ≤ 1 := by
    rw [ht, map_div₀, hv1, div_one]
    refine (Valuation.map_sub _ _ _).trans (max_le ha.le (by rw [map_one]))
  have hth : 1 + h.val i0 j0 * t = a := by rw [ht]; field_simp; ring
  have hdinv : a⁻¹ ∈ O := by rw [hOv, map_inv₀, ha, inv_one]
  have hone : ∀ i j, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) ≤ 1 := by
    intro i j
    rw [Matrix.one_apply]; split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  have hGint : ∀ i j, Gmat h.val i0 j0 t i j ∈ O := by
    intro i j
    rw [hOv, G_apply]
    refine (Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)
    split_ifs
    · rw [map_mul]; exact mul_le_one' (hent _ _) htv
    · rw [map_zero]; exact zero_le'
  have hPint : ∀ i j, Pmat h.val i0 j0 t i j ∈ O := by
    intro i j
    rw [hOv, P_apply]
    refine (Valuation.map_add _ _ _).trans (max_le (hone i j) ?_)
    split_ifs
    · rw [map_mul]; exact mul_le_one' htv (hent _ _)
    · rw [map_zero]; exact zero_le'
  have hdG : (Gmat h.val i0 j0 t).det = a := by rw [det_G, hth]
  have hdP : (Pmat h.val i0 j0 t).det = a := by rw [det_P, hth]
  let Gg := Matrix.GeneralLinearGroup.mkOfDetNeZero (Gmat h.val i0 j0 t) (by rw [hdG]; exact ha0)
  have hGg : Gg.val = Gmat h.val i0 j0 t := rfl
  obtain ⟨g, ⟨hgT, hgl⟩, -⟩ := (GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s).2.2 Gg
  set p := κ⁻¹ * g * κ with hp
  have hpT : TrivOutside {s.v} p :=
    GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv hκT) hgT) hκT
  have hinv : (h⁻¹).val * h.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpl : (s.loc n p).val = Pmat h.val i0 j0 t := by
    rw [hp, map_mul, map_mul, map_inv, hgl, ← hh, Units.val_mul, Units.val_mul, hGg]
    exact conj_G h.val (h⁻¹).val hinv i0 j0 t
  have hgl' : (s.loc n g).val = Gmat h.val i0 j0 t := by rw [hgl]; exact hGg
  have hgP : NG.ParaRT s r (s.loc n g) := by
    refine ⟨mem_GLint_of O _ (fun i j => by rw [hgl']; exact hGint i j) (by rw [hgl', hdG]; exact hdinv), ?_⟩
    intro i j hi hj
    have hji : j ≠ i0 := fun e => by rw [e] at hj; omega
    have hij : i ≠ j := fun e => by rw [e] at hi; omega
    rw [hgl', G_apply, if_neg hji, Matrix.one_apply_ne hij, add_zero, map_zero]
    exact zero_lt_one
  have hpP : NG.ParaRT s r (s.loc n p) := by
    refine ⟨mem_GLint_of O _ (fun i j => by rw [hpl]; exact hPint i j) (by rw [hpl, hdP]; exact hdinv), ?_⟩
    intro i j hi hj
    have hij0 : i ≠ j0 := fun e => by rw [e] at hi; omega
    have hij : i ≠ j := fun e => by rw [e] at hi; omega
    rw [hpl, P_apply, if_neg hij0, Matrix.one_apply_ne hij, add_zero, map_zero]
    exact zero_lt_one
  have hgJ : g ∈ J := (hJ g hgT).2 hgP
  have hpJ : p ∈ J := (hJ p hpT).2 hpP
  have hχg : χ ⟨g, hgJ⟩ ≠ 1 := ha' g hgJ hgT (by unfold NG.detDD; simp only [hgl']; rw [detDD_G _ _ _ _ r hi0, hth])
  have hχp : χ ⟨p, hpJ⟩ = 1 := h1 p hpJ hpT (by unfold NG.detDD; simp only [hpl]; rw [detDD_P _ _ _ _ r hj0])
  have eg := hEig ⟨g, hgJ⟩
  have ep := hEig ⟨p, hpJ⟩
  rw [hχp] at ep
  have hkp : κ * p = g * κ := by rw [hp]; group
  obtain ⟨x0, hx0⟩ : ∃ x, F x ≠ 0 := by
    by_contra hn; push_neg at hn; exact hF (funext hn)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx0
    have := hc (x0 * κ⁻¹)
    rwa [inv_mul_cancel_right, zero_smul] at this
  have key : ∀ x, c • ((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) • F x = c • F x := by
    intro x
    have e1 := hc (x * g)
    have e2 := ep (x * κ)
    rw [eg x] at e1
    rw [mul_assoc, hkp, ← mul_assoc, e1, hc x] at e2
    simpa using e2
  apply hχg
  have k0 := key x0
  rw [smul_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at k0
  rcases k0 with k0 | k0
  · apply Units.ext
    have : c * (((χ ⟨g, hgJ⟩ : ℂˣ) : ℂ) - 1) = 0 := by rw [mul_sub, mul_one]; exact k0
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hc0
    · simpa [sub_eq_zero] using h'
  · exact absurd k0 hx0

end GlobalTheory.ParaRigid
