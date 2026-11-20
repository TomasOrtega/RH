import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

open Formalism.UG (cT)

noncomputable section

namespace GlobalTheory.EisMidParam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)`.
-/
theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem sig_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, RingHom.coe_coe, map_sum, map_mul, hσ, hJ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_swap' (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (hE σ J y x) = hE σ J x y := by
  simp only [hE, Formalism.UG.hform, RingHom.coe_coe, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, hE, Formalism.UG.hform, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem cT_mul_apply {m m' : ℕ} (A : Matrix (Fin n) (Fin m) E) (B : Matrix (Fin n) (Fin m') E) (i : Fin m)
    (j : Fin m') : (cT (σ : E →+* E) A * J * B) i j = hE σ J (fun k => A k i) (fun k => B k j) := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, hE, Formalism.UG.hform, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_sub_smul_right (a b d : Fin n → E) (c : E) :
    hE σ J a (b - c • d) = hE σ J a b - c * hE σ J a d := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.coe_coe, map_sub, map_mul]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_sub_smul_left (a b d : Fin n → E) (c : E) :
    hE σ J (b - c • d) a = hE σ J b a - σ c * hE σ J d a := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.coe_coe, map_sub, map_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
theorem col_mul (q : Matrix (Fin n) (Fin n) E) (a : Fin n → E) (k : Fin n) :
    (q * Matrix.of (fun k (_ : Fin 1) => a k)) k 0 = (q *ᵥ a) k := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/- English proof (translation)
Set `A : Matrix (Fin n) (Fin 1) E` to `Matrix.of fun k _ => a k`. Set `B : Matrix (Fin n) (Fin 1) E` to `Matrix.of fun k _ => b k`. Establish `hm : cT (σ : E →+* E) (q * A) * J * (q * B) = cT (σ : E →+* E) A * J * B`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Formalism.UG.cT_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hq]`. Establish `e` using `congrFun (congrFun hm 0) 0`. Rewrite `e` using `[cT_mul_apply, cT_mul_apply]`. Establish `e1 : (fun k => (q * A) k 0) = q *ᵥ a` using `funext fun k => col_mul q a k`.

Establish `e2 : (fun k => (q * B) k 0) = q *ᵥ b` using `funext fun k => col_mul q b k`. Rewrite `e` using `[e1, e2]`. Conclude with `e`.
-/
theorem hE_unitary {q : Matrix (Fin n) (Fin n) E} (hq : cT (σ : E →+* E) q * J * q = J) (a b : Fin n → E) :
    hE σ J (q *ᵥ a) (q *ᵥ b) = hE σ J a b := by
  let A : Matrix (Fin n) (Fin 1) E := Matrix.of fun k _ => a k
  let B : Matrix (Fin n) (Fin 1) E := Matrix.of fun k _ => b k
  have hm : cT (σ : E →+* E) (q * A) * J * (q * B) = cT (σ : E →+* E) A * J * B := by
    calc cT (σ : E →+* E) (q * A) * J * (q * B) = cT (σ : E →+* E) A * (cT (σ : E →+* E) q * J * q) * B := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hq]
  have e := congrFun (congrFun hm 0) 0
  rw [cT_mul_apply, cT_mul_apply] at e
  have e1 : (fun k => (q * A) k 0) = q *ᵥ a := funext fun k => col_mul q a k
  have e2 : (fun k => (q * B) k 0) = q *ᵥ b := funext fun k => col_mul q b k
  rw [e1, e2] at e
  exact e

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [GlobalTheory.EisMidHt.adVec, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`.
-/
theorem adMat_mulVec (N : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    adMat F N *ᵥ GlobalTheory.EisMidHt.adVec F v = GlobalTheory.EisMidHt.adVec F (N *ᵥ v) := by
  funext i
  simp only [GlobalTheory.EisMidHt.adVec, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, col0, GlobalTheory.EisMidHt.firstColumn, GlobalTheory.EisMidHt.adVec]`.
-/
theorem mul_first_column_of_unit_column {r : ℕ} (M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (X : Matrix (Fin n) (Fin (r + 1)) E)
    (i : Fin n) (j : Fin 1) :
    (M * adMat F (col0 X)) i j = (M *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, col0, GlobalTheory.EisMidHt.firstColumn, GlobalTheory.EisMidHt.adVec]

/- English proof (translation)
Use `⟨l, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[mul_first_column_of_unit_column, h]`. Simplify using `[col0, GlobalTheory.EisMidHt.firstColumn, GlobalTheory.EisMidHt.adVec]`.
-/
theorem stabL_of_vec {r : ℕ} {X : Matrix (Fin n) (Fin (r + 1)) E} {g : GAd σ J} {l : (AF F ⊗[F] E)ˣ}
    (h : (matHom _ σ J g).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) =
      l.1 • GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) : GlobalTheory.EisCT.StabL σ J (col0 X) g := by
  refine ⟨l, ?_⟩
  ext i j
  rw [mul_first_column_of_unit_column, h]
  simp [col0, GlobalTheory.EisMidHt.firstColumn, GlobalTheory.EisMidHt.adVec]

/- English proof (translation)
Take `⟨q, hqU, hq⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hr)`. Use `⟨q, hqU, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `(change ((show HR (AF F) σ J from p) : GL (Fin n) (AF F ⊗[F] E)).1 = _; rw [← hq]; rfl)`. Consider the case `(rw [matHom_apply]; unfold HA.mat; rw [← hq]; rfl)`.
-/
theorem rat_mat {p : GAd σ J} (hr : p ∈ ratPts σ J) :
    ∃ q : GL (Fin n) E, cT (σ : E →+* E) q.1 * J * q.1 = J ∧ (matHom _ σ J p).1 = adMat F q.1 := by
  obtain ⟨q, hqU, hq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hr)
  refine ⟨q, hqU, ?_⟩
  first
    | (change ((show HR (AF F) σ J from p) : GL (Fin n) (AF F ⊗[F] E)).1 = _; rw [← hq]; rfl)
    | (rw [matHom_apply]; unfold HA.mat; rw [← hq]; rfl)

end GlobalTheory.EisMidParam

namespace GlobalTheory.EisMidParam

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in
/- English proof (translation)
Set `S` to `{z : Fin n → E // z ≠ 0 ∧ hE σ J z z = 0 ∧ hE σ J x z = 0 ∧ hE σ J y z = 0}`. Set `s : Setoid S` to `{ r := fun a b => ∃ c : E, a.1 = c • b.1 iseqv := { refl := fun a => ⟨1, (one_smul _ _).symm⟩`. Use symmetry as in `:= fun {a b} h => by`. Take `⟨c, hc⟩` from `h`. Establish `hc0 : c ≠ 0`.

Introduce `h0`. Apply `a.2.1` to reduce the goal to its premises. Rewrite using `[hc, h0, zero_smul]`. Conclude with `⟨c⁻¹, by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩`. Use `trans := fun {a b d} h1 h2 => by`.

Take `⟨c, hc⟩` from `h1`. Take `⟨c', hc'⟩` from `h2`. Conclude with `⟨c * c', by rw [hc, hc', smul_smul]⟩ } }`. Use `⟨Set.range (fun q : Quotient s => (Quotient.out q).1), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨q, rfl⟩`.

Conclude with `(Quotient.out q).2`. Introduce and unpack `z ⟨q, rfl⟩ z' ⟨q', rfl⟩ c hc`. Establish `: q = q'`. Rewrite using `[← Quotient.out_eq q, ← Quotient.out_eq q']`. Conclude with `Quotient.sound ⟨c, hc⟩`.

Rewrite using `[this]`. Introduce `z hz0 hzz hxz hyz`. Set `a : S` to `⟨z, hz0, hzz, hxz, hyz⟩`. Take `⟨c, hc⟩` from `s.symm (Quotient.mk_out (s := s) a)`. Conclude with `⟨_, ⟨Quotient.mk s a, rfl⟩, c, hc⟩`.
-/
theorem exists_lineReps (x y : Fin n → E) : ∃ Yr : Set (Fin n → E), GlobalTheory.EisMidHt.IsLineReps σ J x y Yr := by
  let S := {z : Fin n → E // z ≠ 0 ∧ hE σ J z z = 0 ∧ hE σ J x z = 0 ∧ hE σ J y z = 0}
  let s : Setoid S :=
    { r := fun a b => ∃ c : E, a.1 = c • b.1
      iseqv :=
        { refl := fun a => ⟨1, (one_smul _ _).symm⟩
          symm := fun {a b} h => by
            obtain ⟨c, hc⟩ := h
            have hc0 : c ≠ 0 := by
              intro h0; apply a.2.1; rw [hc, h0, zero_smul]
            exact ⟨c⁻¹, by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
          trans := fun {a b d} h1 h2 => by
            obtain ⟨c, hc⟩ := h1
            obtain ⟨c', hc'⟩ := h2
            exact ⟨c * c', by rw [hc, hc', smul_smul]⟩ } }
  refine ⟨Set.range (fun q : Quotient s => (Quotient.out q).1), ?_, ?_, ?_⟩
  · rintro z ⟨q, rfl⟩
    exact (Quotient.out q).2
  · rintro z ⟨q, rfl⟩ z' ⟨q', rfl⟩ c hc
    have : q = q' := by
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      exact Quotient.sound ⟨c, hc⟩
    rw [this]
  · intro z hz0 hzz hxz hyz
    let a : S := ⟨z, hz0, hzz, hxz, hyz⟩
    obtain ⟨c, hc⟩ := s.symm (Quotient.mk_out (s := s) a)
    exact ⟨_, ⟨Quotient.mk s a, rfl⟩, c, hc⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `hg`. Use `⟨a⁻¹, ?_⟩` and prove the remaining obligations. Establish `h1 : (matHom _ σ J g⁻¹).1 * ((matHom _ σ J g).1 * adMat F x) = adMat F x`. Rewrite using `[← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]`. Rewrite `h1` using `[ha, Matrix.mul_smul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, Units.inv_mul, one_smul]`. Use `_ = _ := by rw [h1]`.
-/
theorem stabL_inv' {x : Matrix (Fin n) (Fin 1) E} {g : GAd σ J} (hg : GlobalTheory.EisCT.StabL σ J x g) :
    GlobalTheory.EisCT.StabL σ J x g⁻¹ := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨a⁻¹, ?_⟩
  have h1 : (matHom _ σ J g⁻¹).1 * ((matHom _ σ J g).1 * adMat F x) = adMat F x := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]
  rw [ha, Matrix.mul_smul] at h1
  calc (matHom _ σ J g⁻¹).1 * adMat F x
      = (a⁻¹).1 • (a.1 • ((matHom _ σ J g⁻¹).1 * adMat F x)) := by
        rw [smul_smul, Units.inv_mul, one_smul]
    _ = _ := by rw [h1]

/- English proof (translation)
Take `⟨q, hqU, hq⟩` from `rat_mat (σ := σ) (J := J) (inv_mem t.2)`. Establish `hxx : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn X) = 0`. Use `congrFun (congrFun hW.xx 0) 0` as an intermediate fact. Rewrite `this` using `[cT_mul_apply]`. Conclude with `this`.

Establish `hxy : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) = 1`. Use `congrFun (congrFun hW.xy 0) 0` as an intermediate fact. Rewrite `this` using `[cT_mul_apply, Matrix.one_apply_eq]`. Conclude with `this`. Establish `hx0 : GlobalTheory.EisMidHt.firstColumn X ≠ 0`.

Introduce `h0`. Establish `: hE σ J (0 : Fin n → E) (GlobalTheory.EisMidHt.firstColumn Y) = 0` using `by simp [hE, Formalism.UG.hform]`. Rewrite `this` using `[← h0, hxy]`. Conclude with `one_ne_zero this`. Use `⟨q.1 *ᵥ GlobalTheory.EisMidHt.firstColumn X, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hq, adMat_mulVec]`. Rewrite using `[hE_unitary hqU]`. Conclude with `hxx`. Establish `h0` using `ho`. Unfold `GlobalTheory.EisCT.OrthL at h0`.

Rewrite `h0` using `[hq, ← Matrix.map_mul, ← Matrix.map_mul]`. Establish `h1 : cT (σ : E →+* E) (col0 X) * J * (q.1 * col0 X) = 0`. Rewrite using `[← Matrix.mul_assoc]`. Conclude with `Matrix.map_injective (inclR_inj (F := F)) (h0.trans (Matrix.map_zero _ (map_zero _)).symm)`. Use `congrFun (congrFun h1 0) 0` as an intermediate fact.

Rewrite `this` using `[cT_mul_apply]`. Establish `e1 : (fun k => (col0 X) k 0) = GlobalTheory.EisMidHt.firstColumn X` using `rfl`. Establish `e2 : (fun k => (q.1 * col0 X) k 0) = q.1 *ᵥ GlobalTheory.EisMidHt.firstColumn X`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, col0, GlobalTheory.EisMidHt.firstColumn]`.

Rewrite `this` using `[e1, e2]`. Conclude with `this`. Introduce `l hl`. Establish `hl0 : l ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hl` using `[zero_smul]`. Apply `hx0` to reduce the goal to its premises. Use `congrArg (fun v => (q⁻¹ : GL (Fin n) E).1 *ᵥ v) hl` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec]`. Apply `hs` to reduce the goal to its premises.

Establish `hst : GlobalTheory.EisCT.StabL σ J (col0 X) (t.1⁻¹)`. Use `stabL_of_vec (l := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 l hl0)) ?_` and prove the remaining obligations. Rewrite using `[hq, adMat_mulVec, hl]`. Use function extensionality and compare the values at `i`. Simplify using `[GlobalTheory.EisMidHt.adVec]`.

Simplify using `using stabL_inv' hst`.
-/
theorem mid_vec (hσ : ∀ x, σ (σ x) = x) {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}
    (hW : IsWittFrame σ J X Y) (t : ratPts σ J) (hs : ¬ GlobalTheory.EisCT.StabL σ J (col0 X) t.1)
    (ho : GlobalTheory.EisCT.OrthL σ J (col0 X) t.1) :
    ∃ z : Fin n → E, (matHom _ σ J t.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) =
      GlobalTheory.EisMidHt.adVec F z ∧ hE σ J z z = 0 ∧ hE σ J (GlobalTheory.EisMidHt.firstColumn X) z = 0 ∧
      ∀ l : E, z ≠ l • GlobalTheory.EisMidHt.firstColumn X := by
  obtain ⟨q, hqU, hq⟩ := rat_mat (σ := σ) (J := J) (inv_mem t.2)
  have hxx : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn X) = 0 := by
    have := congrFun (congrFun hW.xx 0) 0
    rw [cT_mul_apply] at this; exact this
  have hxy : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) = 1 := by
    have := congrFun (congrFun hW.xy 0) 0
    rw [cT_mul_apply, Matrix.one_apply_eq] at this; exact this
  have hx0 : GlobalTheory.EisMidHt.firstColumn X ≠ 0 := by
    intro h0
    have : hE σ J (0 : Fin n → E) (GlobalTheory.EisMidHt.firstColumn Y) = 0 := by simp [hE, Formalism.UG.hform]
    rw [← h0, hxy] at this; exact one_ne_zero this
  refine ⟨q.1 *ᵥ GlobalTheory.EisMidHt.firstColumn X, ?_, ?_, ?_, ?_⟩
  · rw [hq, adMat_mulVec]
  · rw [hE_unitary hqU]; exact hxx
  · have h0 := ho
    unfold GlobalTheory.EisCT.OrthL at h0
    rw [hq, ← Matrix.map_mul, ← Matrix.map_mul] at h0
    have h1 : cT (σ : E →+* E) (col0 X) * J * (q.1 * col0 X) = 0 := by
      rw [← Matrix.mul_assoc]
      exact Matrix.map_injective (inclR_inj (F := F)) (h0.trans (Matrix.map_zero _ (map_zero _)).symm)
    have := congrFun (congrFun h1 0) 0
    rw [cT_mul_apply] at this
    have e1 : (fun k => (col0 X) k 0) = GlobalTheory.EisMidHt.firstColumn X := rfl
    have e2 : (fun k => (q.1 * col0 X) k 0) = q.1 *ᵥ GlobalTheory.EisMidHt.firstColumn X := by
      funext k; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, col0, GlobalTheory.EisMidHt.firstColumn]
    rw [e1, e2] at this; exact this
  · intro l hl
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hl
      apply hx0
      have := congrArg (fun v => (q⁻¹ : GL (Fin n) E).1 *ᵥ v) hl
      simpa [Matrix.mulVec_mulVec] using this
    apply hs
    have hst : GlobalTheory.EisCT.StabL σ J (col0 X) (t.1⁻¹) := by
      refine stabL_of_vec (l := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 l hl0)) ?_
      rw [hq, adMat_mulVec, hl]
      funext i
      simp [GlobalTheory.EisMidHt.adVec]
    simpa using stabL_inv' hst

end GlobalTheory.EisMidParam

open GlobalTheory.EisMidParam in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a h hS T hT`. Establish `hσ` using `sig_invol hS.1`. Establish `hJ` using `hS.2.2.1`. Establish `hW` using `hS.2.2.2.2.1`. Establish `hxx : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn X) = 0`.

Use `congrFun (congrFun hW.xx 0) 0` as an intermediate fact. Rewrite `this` using `[cT_mul_apply]`. Conclude with `this`. Establish `hxy : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) = 1`. Use `congrFun (congrFun hW.xy 0) 0` as an intermediate fact.

Rewrite `this` using `[cT_mul_apply, Matrix.one_apply_eq]`. Conclude with `this`. Establish `hyx : hE σ J (GlobalTheory.EisMidHt.firstColumn Y) (GlobalTheory.EisMidHt.firstColumn X) = 1`. Rewrite using `[← hE_swap' hσ hJ.1, hxy, map_one]`. Take `⟨Yr, hYr⟩` from `exists_lineReps σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y)`.

Use `⟨Yr, hYr, ?_⟩` and prove the remaining obligations. Establish `key : ∀ t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ∃ p : Yr × E, ∃ μ : E, μ ≠ 0 ∧ (matHom _ σ J t.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) = GlobalTheory.EisMidHt.adVec F (μ • (p.1.1 + p.2 • GlobalTheory.EisMidHt.firstColumn X))`. Introduce `t`. Take `⟨z, hz, hzz, hxz, hzl⟩` from `mid_vec (F := F) hσ hW t.1 t.2.2.1 t.2.2.2`. Use `set x := GlobalTheory.EisMidHt.firstColumn X`.

Use `set y₀ := GlobalTheory.EisMidHt.firstColumn Y`. Use `set c := hE σ J y₀ z`. Establish `hzx : hE σ J z x = 0` using `by rw [← hE_swap' hσ hJ.1, hxz, map_zero]`. Establish `h1 : hE σ J x (z - c • x) = 0` using `by rw [hE_sub_smul_right, hxz, hxx, mul_zero, sub_zero]`. Establish `h2 : hE σ J y₀ (z - c • x) = 0` using `by rw [hE_sub_smul_right, hyx, mul_one, sub_self]`.

Establish `h3 : hE σ J (z - c • x) (z - c • x) = 0`. Rewrite using `[hE_sub_smul_left, h1, mul_zero, sub_zero, hE_sub_smul_right, hzz, hzx, mul_zero, sub_zero]`. Establish `h0 : z - c • x ≠ 0`. Introduce `h`. Conclude with `hzl c (sub_eq_zero.1 h)`.

Take `⟨y, hy, μ, hμ⟩` from `hYr.2.2 _ h0 h3 h1 h2`. Establish `hμ0 : μ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hμ` using `[zero_smul]`. Conclude with `h0 hμ`.

Use `⟨(⟨y, hy⟩, c / μ), μ, hμ0, ?_⟩` and prove the remaining obligations. Rewrite using `[hz]`. Use `congr 1`. Rewrite using `[smul_add, smul_smul, mul_div_cancel₀ _ hμ0, ← hμ, sub_add_cancel]`. Use `choose f μ hμ0 hμ using key`.

Use `⟨f, ?_, fun t => ⟨μ t, hμ0 t, hμ t⟩⟩` and prove the remaining obligations. Introduce `t₁ t₂ e`. Use `set x := GlobalTheory.EisMidHt.firstColumn X`. Establish `e1 : (matHom _ σ J t₁.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F x = GlobalTheory.EisMidHt.adVec F (μ t₁ • ((f t₂).1.1 + (f t₂).2 • x))`. Rewrite using `[hμ t₁, e]`.

Establish `e2` using `hμ t₂`. Establish `e3 : (matHom _ σ J t₁.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F x = inclR (F` using `F) (AF F) (μ t₁ / μ t₂) • ((matHom _ σ J t₂.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F x) := by`. Rewrite using `[e1, e2]`. Use function extensionality and compare the values at `i`. Simplify using `only [GlobalTheory.EisMidHt.adVec, Pi.smul_apply, smul_eq_mul, ← map_mul, smul_smul]`.

Rewrite using `[← mul_assoc, div_mul_cancel₀ _ (hμ0 t₂)]`. Establish `hst : GlobalTheory.EisCT.StabL σ J (col0 X) (t₂.1 * t₁.1⁻¹ : ratPts σ J).1`. Use `stabL_of_vec (l := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (μ t₁ / μ t₂) (div_ne_zero (hμ0 t₁) (hμ0 t₂)))) ?_` and prove the remaining obligations. Establish `: ((t₂.1 * t₁.1⁻¹ : ratPts σ J) : GAd σ J) = t₂.1.1 * t₁.1.1⁻¹` using `rfl`. Rewrite using `[this, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, e3, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]`.

Both sides reduce to the same expression. Establish `hst2 : GlobalTheory.EisCT.StabL σ J (col0 X) (t₂.1 * t₂.1⁻¹ : ratPts σ J).1`. Rewrite using `[mul_inv_cancel]; exact ⟨1, by simp⟩`. Conclude with `Subtype.ext ((hT t₂.1).unique ⟨t₁.2.1, hst⟩ ⟨t₂.2.1, hst2⟩)`.
-/
theorem GlobalTheory.EisMidParam.midSet_param : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
      ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T →
      ∃ Yr : Set (Fin n → E), GlobalTheory.EisMidHt.IsLineReps σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) Yr ∧
        ∃ f : GlobalTheory.EisCT.midSet σ J (col0 X) T → Yr × E, Function.Injective f ∧
          ∀ t, ∃ μ : E, μ ≠ 0 ∧ (matHom _ σ J t.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) =
            GlobalTheory.EisMidHt.adVec F (μ • ((f t).1.1 + (f t).2 • GlobalTheory.EisMidHt.firstColumn X)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS T hT
  have hσ := sig_invol hS.1
  have hJ := hS.2.2.1
  have hW := hS.2.2.2.2.1
  have hxx : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn X) = 0 := by
    have := congrFun (congrFun hW.xx 0) 0
    rw [cT_mul_apply] at this; exact this
  have hxy : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) = 1 := by
    have := congrFun (congrFun hW.xy 0) 0
    rw [cT_mul_apply, Matrix.one_apply_eq] at this; exact this
  have hyx : hE σ J (GlobalTheory.EisMidHt.firstColumn Y) (GlobalTheory.EisMidHt.firstColumn X) = 1 := by
    rw [← hE_swap' hσ hJ.1, hxy, map_one]
  obtain ⟨Yr, hYr⟩ := exists_lineReps σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y)
  refine ⟨Yr, hYr, ?_⟩
  have key : ∀ t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ∃ p : Yr × E, ∃ μ : E, μ ≠ 0 ∧
      (matHom _ σ J t.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) =
        GlobalTheory.EisMidHt.adVec F (μ • (p.1.1 + p.2 • GlobalTheory.EisMidHt.firstColumn X)) := by
    intro t
    obtain ⟨z, hz, hzz, hxz, hzl⟩ := mid_vec (F := F) hσ hW t.1 t.2.2.1 t.2.2.2
    set x := GlobalTheory.EisMidHt.firstColumn X
    set y₀ := GlobalTheory.EisMidHt.firstColumn Y
    set c := hE σ J y₀ z
    have hzx : hE σ J z x = 0 := by rw [← hE_swap' hσ hJ.1, hxz, map_zero]
    have h1 : hE σ J x (z - c • x) = 0 := by rw [hE_sub_smul_right, hxz, hxx, mul_zero, sub_zero]
    have h2 : hE σ J y₀ (z - c • x) = 0 := by rw [hE_sub_smul_right, hyx, mul_one, sub_self]
    have h3 : hE σ J (z - c • x) (z - c • x) = 0 := by
      rw [hE_sub_smul_left, h1, mul_zero, sub_zero, hE_sub_smul_right, hzz, hzx, mul_zero, sub_zero]
    have h0 : z - c • x ≠ 0 := by
      intro h; exact hzl c (sub_eq_zero.1 h)
    obtain ⟨y, hy, μ, hμ⟩ := hYr.2.2 _ h0 h3 h1 h2
    have hμ0 : μ ≠ 0 := by
      rintro rfl; rw [zero_smul] at hμ; exact h0 hμ
    refine ⟨(⟨y, hy⟩, c / μ), μ, hμ0, ?_⟩
    rw [hz]
    congr 1
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hμ0, ← hμ, sub_add_cancel]
  choose f μ hμ0 hμ using key
  refine ⟨f, ?_, fun t => ⟨μ t, hμ0 t, hμ t⟩⟩
  intro t₁ t₂ e
  set x := GlobalTheory.EisMidHt.firstColumn X
  have e1 : (matHom _ σ J t₁.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F x = GlobalTheory.EisMidHt.adVec F (μ t₁ • ((f t₂).1.1 + (f t₂).2 • x)) := by
    rw [hμ t₁, e]
  have e2 := hμ t₂
  have e3 : (matHom _ σ J t₁.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F x =
      inclR (F := F) (AF F) (μ t₁ / μ t₂) • ((matHom _ σ J t₂.1.1⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F x) := by
    rw [e1, e2]
    funext i
    simp only [GlobalTheory.EisMidHt.adVec, Pi.smul_apply, smul_eq_mul, ← map_mul, smul_smul]
    rw [← mul_assoc, div_mul_cancel₀ _ (hμ0 t₂)]
  have hst : GlobalTheory.EisCT.StabL σ J (col0 X) (t₂.1 * t₁.1⁻¹ : ratPts σ J).1 := by
    refine stabL_of_vec (l := Units.map (inclR (F := F) (AF F)).toMonoidHom
      (Units.mk0 (μ t₁ / μ t₂) (div_ne_zero (hμ0 t₁) (hμ0 t₂)))) ?_
    have : ((t₂.1 * t₁.1⁻¹ : ratPts σ J) : GAd σ J) = t₂.1.1 * t₁.1.1⁻¹ := rfl
    rw [this, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, e3, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
    rfl
  have hst2 : GlobalTheory.EisCT.StabL σ J (col0 X) (t₂.1 * t₂.1⁻¹ : ratPts σ J).1 := by
    rw [mul_inv_cancel]; exact ⟨1, by simp⟩
  exact Subtype.ext ((hT t₂.1).unique ⟨t₁.2.1, hst⟩ ⟨t₂.2.1, hst2⟩)
